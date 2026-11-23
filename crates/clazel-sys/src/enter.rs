//! [`enter`]: run a validated blob (jit.md item J.0(a), decision E1).
//!
//! This is the only place the crate calls generated code, and the only call
//! through a function pointer built from an address. It is exactly one
//! function, [`enter`], whose safe part checks the entry against the region
//! and whose one `unsafe` block per ABI turns the region's **stub** address
//! into a function and calls it with the context and the blob's address. The
//! stub (`crate::code::STUB`, written at offset 0 of every region) is the only
//! code that meets the platform ABI: it saves the callee-saved registers, sets
//! the context register, calls the blob, and returns when the blob's exit
//! sequence executes `ret`. On A64 on Linux it first does the instruction-cache
//! maintenance over the region, which is why it also takes the region's length;
//! on Windows ARM64 `enter` itself calls `FlushInstructionCache` first (the
//! writer may be another process), and on macOS `CodeRegion::write` has already
//! invalidated. On x86-64 the stub starts with a serializing `cpuid`. The full
//! argument, per platform, is in `crate::code`.
//!
//! The ABIs: `sysv64` (x86-64 on Linux and macOS), `win64` (x86-64 on
//! Windows) and `C` (AArch64, whose `C` is AAPCS64 on Linux, macOS and
//! Windows). `cargo xtask check` accepts the call only in exactly the form of
//! [`run`] below (see `xtask/src/sys.rs`, rule 10).
//!
//! What makes this sound, in the order a reviewer should check it:
//!
//! 1. The region's memory is read-execute, so nothing in this process can
//!    change it, and it was mapped by `crate::linux::code`,
//!    `crate::macos::code` or `crate::windows::code`, which checked the stub
//!    is the expected bytes.
//! 2. What the writer put after the stub was accepted by
//!    `clazel-codecheck`; [`Validated`] carries that verdict. The writer is
//!    trusted (jit.md J.0(b)); this crate does not read the blob.
//! 3. The entry is inside the region and past the stub, and on A64 a multiple
//!    of 4. A validated entry is the first byte of a unit, so it is an
//!    instruction boundary.
//! 4. The context is a live `&mut Context` of the ABI's 512 bytes, and the
//!    blob reaches memory only through the regions the context lists, which
//!    the caller (`clazel-jit`) filled with memory it owns.

use crate::{CODE_START, CodeError, CodeRegion, Context, Exit, Validated};

/// Run the blob that `entry` names in `region`, with `ctx` as its context,
/// and return the exit code its exit sequence stored.
///
/// The call returns when the blob executes its exit sequence, and the
/// caller reads the operands of the exit from `ctx`. A blob that never exits
/// (a loop, which the validator does not forbid) never returns: preemption is
/// not this crate's business.
///
/// # Errors
///
/// [`CodeError::OutOfRange`] if `entry` is before [`CODE_START`] or not
/// inside the region; [`CodeError::Misaligned`] on AArch64 if it is not a
/// multiple of 4.
pub fn enter(region: &CodeRegion, entry: Validated, ctx: &mut Context) -> Result<Exit, CodeError> {
    let offset = entry.from_start();
    if offset < CODE_START || offset >= region.len() {
        return Err(CodeError::OutOfRange);
    }
    #[cfg(target_arch = "aarch64")]
    if !offset.is_multiple_of(4) {
        return Err(CodeError::Misaligned);
    }
    // Windows ARM64: the writer may be another process and cannot be trusted
    // to flush, so the executing process makes its own instruction cache
    // coherent with what was written, before every entry. (Linux ARM64 does it
    // in the stub, macOS in `CodeRegion::write`, x86-64 needs none: see
    // `crate::code`.)
    #[cfg(all(windows, target_arch = "aarch64"))]
    region.flush()?;
    let stub = region.base();
    let entry = stub.checked_add(offset).ok_or(CodeError::OutOfRange)?;
    let raw: *mut u8 = std::ptr::from_mut(&mut *ctx).cast();
    run(stub, raw, entry, region.len());
    // The blob stored the exit code through `raw`, which was derived from
    // this reference and is not used again, so reading through `ctx` is fine.
    Ok(Exit(ctx.exit_code()))
}

/// The one block for x86-64 System V (Linux and macOS).
#[cfg(all(target_arch = "x86_64", not(windows)))]
fn run(stub: usize, ctx: *mut u8, entry: usize, len: usize) {
    // SAFETY: man 2 mmap and man 2 mprotect (W^X): `stub` is the base address
    // of a mapping this crate made read-execute and whose first bytes it
    // checked to be `crate::code::STUB`, a function with the System V x86-64
    // ABI (System V psABI, "Function Calling Sequence"): `void (*)(void *ctx,
    // uintptr_t entry, size_t len)`, arguments in rdi, rsi and rdx (the third
    // is not used by this stub), which preserves every callee-saved register
    // and returns once. `transmute::<usize, unsafe extern "sysv64" fn(*mut u8,
    // usize, usize)>` has the size of a function pointer; `ctx` points to the
    // caller's live 512-byte `Context`, `entry` is the address of a blob
    // `clazel-codecheck` accepted (`Validated`), inside the same mapping,
    // whose `ret` returns to the stub, and `len` is the mapping's length.
    unsafe {
        (std::mem::transmute::<usize, unsafe extern "sysv64" fn(*mut u8, usize, usize)>(stub))(
            ctx, entry, len,
        )
    }
}

/// The one block for x86-64 on Windows.
#[cfg(all(target_arch = "x86_64", windows))]
fn run(stub: usize, ctx: *mut u8, entry: usize, len: usize) {
    // SAFETY: docs MapViewOfFile3 (the view is mapped PAGE_EXECUTE_READ and its
    // first bytes were checked to be `crate::code::STUB`) and docs
    // VirtualProtect (W^X): `stub` is the base of that view, a function with the
    // Windows x64 calling convention (Microsoft Learn, "x64 calling
    // convention"): `void (*)(void *ctx, uintptr_t entry, size_t len)`,
    // arguments in rcx, rdx and r8 (the third is not used by this stub), which
    // preserves rbx, rbp, rdi, rsi, r12-r15 and xmm6-xmm15, reserves the 32
    // bytes of shadow space and returns once. `transmute::<usize, unsafe
    // extern "win64" fn(*mut u8, usize, usize)>` has the size of a function
    // pointer; `ctx` points to the caller's live 512-byte `Context`, `entry` is
    // the address of a blob `clazel-codecheck` accepted (`Validated`), inside
    // the same view, whose `ret` returns to the stub, and `len` is the view's
    // length.
    unsafe {
        (std::mem::transmute::<usize, unsafe extern "win64" fn(*mut u8, usize, usize)>(stub))(
            ctx, entry, len,
        )
    }
}

/// The one block for AArch64 (AAPCS64 on Linux, macOS and Windows).
#[cfg(target_arch = "aarch64")]
fn run(stub: usize, ctx: *mut u8, entry: usize, len: usize) {
    // SAFETY: man 2 mmap and man 2 mprotect (W^X; on macOS man 3
    // pthread_jit_write_protect_np): `stub` is the base address of a mapping
    // this crate made executable and whose first bytes it checked to be
    // `crate::code::STUB`, a function with the AAPCS64 ABI (Arm "Procedure Call
    // Standard for the Arm 64-bit Architecture"): `void (*)(void *ctx,
    // uintptr_t entry, size_t len)`, arguments in x0, x1 and x2, which
    // preserves x19-x30, x18 and d8-d15 (and clobbers only x9-x16, the
    // temporaries it uses for cache maintenance) and returns once through x30.
    // `transmute::<usize, unsafe extern "C" fn(*mut u8, usize, usize)>` has the
    // size of a function pointer; `ctx` points to the caller's live 512-byte
    // `Context`, `entry` is the address of a blob `clazel-codecheck` accepted
    // (`Validated`), inside the same mapping, a multiple of 4, whose `ret`
    // returns to the stub through x30, and `len` is the mapping's length.
    unsafe {
        (std::mem::transmute::<usize, unsafe extern "C" fn(*mut u8, usize, usize)>(stub))(
            ctx, entry, len,
        )
    }
}
