//! Executable code regions (jit.md item J.7): the target-independent half.
//!
//! What lives here is data and checks, no foreign call: the layout of a
//! region (a fixed **enter stub** at its start, validated blobs after it),
//! the [`Context`] block that generated code reaches through its context
//! register, the [`Exit`] it leaves through, the [`Validated`] entry point
//! that [`crate::enter`] takes, and the [`CodeError`] every call reports. The
//! OS halves ([`crate::linux::code`], [`crate::macos::code`],
//! [`crate::windows::code`]) make and map the memory; [`crate::enter`]
//! calls the stub.
//!
//! None of it decides anything. Sizes, when to map and what is written come
//! from the caller (`clazel-jit`, later), and *whether bytes may run at all*
//! is `clazel-codecheck`'s verdict, which arrives here only as a
//! [`Validated`].
//!
//! # The ABI (jit.md J.0(a); `clazel-codecheck`'s `spec` and `a64::spec`)
//!
//! - The **context** is a 512-byte block, reached by the blob only through
//!   the context register (`r15` on x86-64, `x28` on A64): bytes `0..256`
//!   are a table of 16 regions (`base` at `16k`, `bound` at `16k + 8`) that
//!   the blob may read but never write, and bytes `256..512` are the exit
//!   area (the exit code at 256, operands after it). [`Context`] is exactly
//!   that block.
//! - The **stub** is the only code that meets the platform ABI. It takes the
//!   context, the blob's address and the region's length. It saves the
//!   platform's callee-saved registers (everything but the context register
//!   and the stack pointer is the blob's, so it saves them all), sets the
//!   context register from its first argument, calls its second argument
//!   (the blob's address), and on the blob's `ret` restores the registers and
//!   returns. The blob has no prologue or epilogue: its exit sequence is
//!   `mov t, code; mov [ctx + 256], t; ret`, and the `ret` returns here.
//! - **Instruction-cache maintenance** is the stub's first instructions on
//!   A64 **on Linux**: `dc cvau` over every data cache line of `[base + 256,
//!   base + len)`, `dsb ish`, `ic ivau` over every instruction cache line of
//!   the same range, `dsb ish`, `isb`, with the line sizes read from
//!   `CTR_EL0`. It runs on every [`crate::enter`] (the renderer cannot know
//!   what the writer changed, and `CodeWriter::write` may replace bytes), so
//!   it costs a few instructions per cache line of the region; an embedder
//!   that wants less makes the region smaller. They are not system calls
//!   (legal at EL0), so the sandboxed renderer needs no system call. On
//!   macOS and Windows A64 `CTR_EL0` cannot be read, so the maintenance is
//!   an OS call, and the stub only does `dsb ish; isb`.
//! - **Why no safe caller can run stale code** (audit finding 3 of PR 272),
//!   per platform. The rule is that *every path from a write to an entry
//!   passes through maintenance that this crate makes, not that the caller
//!   makes*:
//!   - **Linux A64:** the stub's maintenance runs on every entry and covers
//!     the whole blob area, so it covers every write, whoever made it and
//!     whenever. No call of the caller's is involved.
//!   - **macOS (A64 and Intel):** the only writes are `CodeRegion::write` and
//!     the stub install in `create`, and both end in `sys_icache_invalidate`
//!     (`copy_in`) before they return, so no write is without its
//!     invalidation. The writer and the executor are the same process.
//!   - **Windows A64:** the writer is another process with no handle to the
//!     executor, so a flush in `CodeWriter::write` cannot reach it, and a flush
//!     the caller must remember is one safe code can omit. So `enter`
//!     itself calls `FlushInstructionCache` in the executing process before
//!     every entry (`crate::enter`): there is no entry without a flush made
//!     after the last write. `RemoteView::flush` is optional.
//!   - **x86-64 (all):** see the next item.
//! - **x86-64 serialization** (audit finding 3 of the second audit of PR 272;
//!   recalled from the Intel SDM, Vol. 3A, "Handling Self- and Cross-Modifying
//!   Code", not re-read for this change). Stores and instruction fetch are
//!   coherent, by *physical* address, in the caches, so no cache maintenance
//!   is needed. But the SDM says the check of what the core has already
//!   *prefetched* is by *linear* address, and that a core executing code that
//!   another core modified (cross-modifying code) must execute a serializing
//!   instruction before it runs the new bytes. Here the writer's read-write
//!   view and the executor's read-execute view are different linear addresses
//!   (other processes on Linux and Windows, one mapping on macOS but another
//!   thread), so the architecture's own sequence is needed, and the plan (jit.md J.0
//!   decisions, "a serializing jump after the mapping changes") asks for it.
//!   The stub therefore starts with `xor eax, eax; cpuid` on every entry,
//!   before it calls the blob. `cpuid` is the SDM's example of a serializing
//!   instruction, available at every privilege level, and is the only one
//!   that needs no feature test (`SERIALIZE` needs a CPUID flag; `iretq` to
//!   the next instruction needs a stack frame and segment selectors; `lfence`
//!   is not architecturally serializing for instruction fetch). It clobbers
//!   `rax`, `rbx`, `rcx` and `rdx`: the stub has saved `rbx` and it passes no
//!   argument in `rax`/`rcx`/`rdx` (System V: `rdi` and `rsi` are the
//!   arguments, which `cpuid` does not touch; Windows: the stub moves its
//!   `rcx` and `rdx` into `r15` and `r14`, which it has saved, first). The
//!   cost is one `cpuid` per entry (a few tens of cycles; a trap to the
//!   hypervisor, about a microsecond, in a virtual machine). The writer must
//!   still not replace bytes a thread may be executing (the stub only makes the
//!   *next* entry see the new bytes).
//! - A region is [`CODE_START`] bytes of stub (zero padded), then blobs. A
//!   [`Validated`] offset is from the region's start, so at least
//!   [`CODE_START`].

use std::fmt;

use crate::Errno;

/// Where a blob may start: the offset of the first byte after the stub, and
/// a multiple of 16 so a blob is aligned. The stub is below it and no write
/// reaches it.
pub const CODE_START: usize = 256;

/// The size of [`Context`] in bytes (jit.md J.6: the context register
/// points at a table of 16 `(base, bound)` pairs and an exit area).
pub const CONTEXT_BYTES: usize = 512;

/// [`CONTEXT_BYTES`] as 64-bit words.
pub const CONTEXT_WORDS: usize = 64;

/// The word of [`Context`] that holds the exit code (byte offset 256).
pub const EXIT_CODE_WORD: usize = 32;

/// The block a blob reaches through its context register: a region table in
/// words `0..32` (`base` at word `2k`, `bound` at `2k + 1`), which blobs read
/// and never write, and the exit area in words `32..64`, where word 32 is the
/// exit code. Which values go in is the caller's business.
#[derive(Clone, PartialEq, Eq)]
#[repr(C, align(16))]
pub struct Context {
    words: [u64; CONTEXT_WORDS],
}

impl Context {
    /// An all-zero context.
    pub const fn new() -> Context {
        Context {
            words: [0; CONTEXT_WORDS],
        }
    }

    /// The 64 words, read-only.
    pub fn words(&self) -> &[u64; CONTEXT_WORDS] {
        &self.words
    }

    /// The 64 words, to fill the region table and the exit area's operands
    /// before [`crate::enter`] and to read the operands after.
    pub fn words_mut(&mut self) -> &mut [u64; CONTEXT_WORDS] {
        &mut self.words
    }

    /// The exit code the blob stored (word [`EXIT_CODE_WORD`]).
    pub fn exit_code(&self) -> u64 {
        self.words.get(EXIT_CODE_WORD).copied().unwrap_or(0)
    }
}

impl Default for Context {
    fn default() -> Context {
        Context::new()
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("exit_code", &self.exit_code())
            .finish_non_exhaustive()
    }
}

/// How a blob left: the exit code its exit sequence stored in the context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exit(pub u64);

/// An entry point into a region that `clazel-codecheck` accepted: a byte
/// offset from the region's start.
///
/// **Only `clazel-codecheck` (and, later, `clazel-jit`) may build one**, from
/// the offset of an entry it validated in the blob it checked. This crate
/// cannot depend on it (its only dependency is `libc`), so the constructor is
/// public and the rule is kept by `cargo xtask check` (rule 11 in
/// `xtask/src/sys.rs`): no crate but those listed there may name
/// [`Validated::new`], [`crate::enter`] or the writers.
/// [`crate::enter`] still refuses an offset that is outside the region, inside
/// the stub, or (A64) not a multiple of 4, so a wrong value can fail but
/// cannot reach the stub or run past the region.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Validated {
    offset: usize,
}

impl Validated {
    /// The entry at `offset` bytes from the region's start. See the type's
    /// documentation: only `clazel-codecheck` calls this.
    pub const fn new(offset: usize) -> Validated {
        Validated { offset }
    }

    /// The offset from the region's start.
    pub const fn from_start(self) -> usize {
        self.offset
    }
}

/// Why a code-region call failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodeError {
    /// A foreign call failed with this error number (`GetLastError` on
    /// Windows).
    Os {
        /// The call that failed.
        call: &'static str,
        /// What it left in `errno`.
        errno: Errno,
    },
    /// A region must be larger than [`CODE_START`] and at most `isize::MAX`.
    BadSize,
    /// An offset or length reaches outside the region, or into the stub.
    OutOfRange,
    /// An entry offset that the architecture cannot enter (A64: not a
    /// multiple of 4).
    Misaligned,
    /// The memory is not what this crate makes: wrong seals or size, not
    /// mapped read-execute, or the stub is not the expected bytes.
    NotACodeRegion,
}

impl fmt::Display for CodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CodeError::Os { call, errno } => write!(f, "{call} failed: {errno}"),
            CodeError::BadSize => f.write_str("a code region must be larger than the stub"),
            CodeError::OutOfRange => {
                f.write_str("offset outside the code region or inside the stub")
            }
            CodeError::Misaligned => f.write_str("entry offset is not a multiple of 4"),
            CodeError::NotACodeRegion => {
                f.write_str("memory is not a code region made by clazel-sys")
            }
        }
    }
}

impl std::error::Error for CodeError {}

impl CodeError {
    /// The error of the foreign call `call`, reading the thread's error
    /// number now (so call it straight after the failing call).
    pub(crate) fn os(call: &'static str) -> CodeError {
        CodeError::Os {
            call,
            errno: Errno::last(),
        }
    }
}

/// Check that `bytes` placed at `offset` fit in a region of `len` bytes and
/// do not touch the stub; the end of the write as an offset.
pub(crate) fn write_range(len: usize, offset: usize, bytes: &[u8]) -> Result<usize, CodeError> {
    let end = offset
        .checked_add(bytes.len())
        .ok_or(CodeError::OutOfRange)?;
    if offset < CODE_START || end > len {
        return Err(CodeError::OutOfRange);
    }
    Ok(end)
}

/// Check a region's size at creation: room for the stub and at least one
/// byte of code, and addressable.
pub(crate) fn check_size(len: usize) -> Result<(), CodeError> {
    if len <= CODE_START || isize::try_from(len).is_err() {
        return Err(CodeError::BadSize);
    }
    Ok(())
}

/// The enter stub for this target: the bytes at the start of every region.
/// Calling convention (the stub's own): first argument the context, second
/// the blob's address, third the region's length in bytes; no result. (Only
/// the A64 stub uses the length.) One comment per instruction group, on the
/// line above its bytes; the bytes were assembled with `clang` from the
/// instructions in the comments and are checked in as arrays.
#[cfg(all(target_arch = "x86_64", not(windows)))]
#[rustfmt::skip]
pub(crate) const STUB: &[u8] = &[
    // push rbx; push rbp; push r12; push r13; push r14; push r15
    0x53, 0x55, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57,
    // sub rsp, 8   (the stack is 16-aligned at the call below)
    0x48, 0x83, 0xec, 0x08,
    // xor eax, eax; cpuid   (a serializing instruction: the core refetches what the
    // writer wrote through another linear address; clobbers rax, rbx (saved), rcx,
    // rdx; rdi and rsi, the arguments, are not touched)
    0x31, 0xc0, 0x0f, 0xa2,
    // mov r15, rdi   (the context register)
    0x49, 0x89, 0xff,
    // call rsi   (the blob; its `ret` returns here; rdx, the length, is not used)
    0xff, 0xd6,
    // add rsp, 8
    0x48, 0x83, 0xc4, 0x08,
    // pop r15; pop r14; pop r13; pop r12; pop rbp; pop rbx
    0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5d, 0x5b,
    // ret
    0xc3,
];

/// The enter stub for this target (Windows x64: arguments in `rcx`, `rdx`,
/// `r8`; `rbx rbp rdi rsi r12-r15` and `xmm6-xmm15` are callee-saved; 32 bytes
/// of shadow space).
#[cfg(all(target_arch = "x86_64", windows))]
#[rustfmt::skip]
pub(crate) const STUB: &[u8] = &[
    // push rbx; push rbp; push rdi; push rsi; push r12; push r13; push r14; push r15
    0x53, 0x55, 0x57, 0x56, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57,
    // sub rsp, 200   (32 shadow + 160 for xmm6-15 + 8 alignment)
    0x48, 0x81, 0xec, 0xc8, 0x00, 0x00, 0x00,
    // movaps [rsp+32+16i], xmm(6+i), i = 0..10
    0x0f, 0x29, 0x74, 0x24, 0x20, 0x0f, 0x29, 0x7c, 0x24, 0x30, 0x44, 0x0f,
    0x29, 0x44, 0x24, 0x40, 0x44, 0x0f, 0x29, 0x4c, 0x24, 0x50, 0x44, 0x0f,
    0x29, 0x54, 0x24, 0x60, 0x44, 0x0f, 0x29, 0x5c, 0x24, 0x70, 0x44, 0x0f,
    0x29, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x29, 0xac, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x29, 0xb4, 0x24, 0xa0, 0x00, 0x00,
    0x00, 0x44, 0x0f, 0x29, 0xbc, 0x24, 0xb0, 0x00, 0x00, 0x00,
    // mov r15, rcx   (the context register); mov r14, rdx   (the blob's address; r14 is
    // saved above, and cpuid below clobbers rcx and rdx)
    0x49, 0x89, 0xcf, 0x49, 0x89, 0xd6,
    // xor eax, eax; cpuid   (a serializing instruction: the core refetches what the
    // writer wrote through another linear address; clobbers rax, rbx (saved), rcx, rdx)
    0x31, 0xc0, 0x0f, 0xa2,
    // call r14   (the blob; r8, the length, is not used)
    0x41, 0xff, 0xd6,
    // movaps xmm(6+i), [rsp+32+16i], i = 0..10
    0x0f, 0x28, 0x74, 0x24, 0x20, 0x0f, 0x28, 0x7c, 0x24, 0x30, 0x44, 0x0f,
    0x28, 0x44, 0x24, 0x40, 0x44, 0x0f, 0x28, 0x4c, 0x24, 0x50, 0x44, 0x0f,
    0x28, 0x54, 0x24, 0x60, 0x44, 0x0f, 0x28, 0x5c, 0x24, 0x70, 0x44, 0x0f,
    0x28, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x28, 0xac, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x28, 0xb4, 0x24, 0xa0, 0x00, 0x00,
    0x00, 0x44, 0x0f, 0x28, 0xbc, 0x24, 0xb0, 0x00, 0x00, 0x00,
    // add rsp, 200
    0x48, 0x81, 0xc4, 0xc8, 0x00, 0x00, 0x00,
    // pop r15; pop r14; pop r13; pop r12; pop rsi; pop rdi; pop rbp; pop rbx
    0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5e, 0x5f, 0x5d, 0x5b,
    // ret
    0xc3,
];

/// The enter stub for this target (AAPCS64: arguments in `x0`, `x1`, `x2`;
/// `x19-x30` and `d8-d15` are callee-saved, and `x18`, the platform register
/// on Apple and Windows, is saved too, since the blob may write it).
///
/// **Linux.** It first makes the region's code visible to instruction fetch,
/// by the architecture's own sequence (Arm ARM, "Synchronization and
/// coherency issues between data and instruction accesses"): clean the data
/// cache to the point of unification (`dc cvau`) over `[base + 256, base +
/// len)`, one instruction per line of the size `CTR_EL0.DminLine` gives,
/// `dsb ish`, invalidate the instruction cache to the point of unification
/// (`ic ivau`) over the same range by `CTR_EL0.IminLine`, `dsb ish`, `isb`.
/// Those instructions and the read of `CTR_EL0` are legal at EL0 on Linux
/// (`SCTLR_EL1.UCI` and `UCT`). It uses only `x9-x16`, which the caller does
/// not expect preserved.
#[cfg(all(target_arch = "aarch64", target_os = "linux"))]
#[rustfmt::skip]
pub(crate) const STUB: &[u8] = &[
    // adr x9, stub   (x9 = the region base: the stub is at offset 0)
    0x09, 0x00, 0x00, 0x10,
    // add x10, x9, #256   (x10 = the first byte after the stub)
    0x2a, 0x01, 0x04, 0x91,
    // add x11, x9, x2   (x11 = the region end; x2 is the length)
    0x2b, 0x01, 0x02, 0x8b,
    // mrs x12, ctr_el0   (cache line sizes)
    0x2c, 0x00, 0x3b, 0xd5,
    // ubfx x13, x12, #16, #4; mov x14, #4; lsl x13, x14, x13   (x13 = data line bytes, 4 << DminLine)
    0x8d, 0x4d, 0x50, 0xd3, 0x8e, 0x00, 0x80, 0xd2, 0xcd, 0x21, 0xcd, 0x9a,
    // and x15, x12, #0xf; lsl x15, x14, x15   (x15 = instruction line bytes, 4 << IminLine)
    0x8f, 0x0d, 0x40, 0x92, 0xcf, 0x21, 0xcf, 0x9a,
    // sub x16, x13, #1; bic x16, x10, x16   (x16 = x10 rounded down to a data line)
    0xb0, 0x05, 0x00, 0xd1, 0x50, 0x01, 0x30, 0x8a,
    // dc cvau, x16; add x16, x16, x13; cmp x16, x11; b.lo (back to the dc)   (clean every data line to the point of unification)
    0x30, 0x7b, 0x0b, 0xd5, 0x10, 0x02, 0x0d, 0x8b, 0x1f, 0x02, 0x0b, 0xeb,
    0xa3, 0xff, 0xff, 0x54,
    // dsb ish   (the cleans are complete before the invalidates)
    0x9f, 0x3b, 0x03, 0xd5,
    // sub x16, x15, #1; bic x16, x10, x16   (x16 = x10 rounded down to an instruction line)
    0xf0, 0x05, 0x00, 0xd1, 0x50, 0x01, 0x30, 0x8a,
    // ic ivau, x16; add x16, x16, x15; cmp x16, x11; b.lo (back to the ic)   (invalidate every instruction line to the point of unification)
    0x30, 0x75, 0x0b, 0xd5, 0x10, 0x02, 0x0f, 0x8b, 0x1f, 0x02, 0x0b, 0xeb,
    0xa3, 0xff, 0xff, 0x54,
    // dsb ish; isb   (the invalidates are complete; refetch from here)
    0x9f, 0x3b, 0x03, 0xd5, 0xdf, 0x3f, 0x03, 0xd5,
    // stp x29, x30, [sp, #-176]!
    0xfd, 0x7b, 0xb5, 0xa9,
    // stp x19, x20, [sp, #16]; stp x21, x22, [sp, #32]; stp x23, x24, [sp, #48]
    0xf3, 0x53, 0x01, 0xa9, 0xf5, 0x5b, 0x02, 0xa9, 0xf7, 0x63, 0x03, 0xa9,
    // stp x25, x26, [sp, #64]; stp x27, x28, [sp, #80]
    0xf9, 0x6b, 0x04, 0xa9, 0xfb, 0x73, 0x05, 0xa9,
    // stp d8, d9, [sp, #96]; stp d10, d11, [sp, #112]; stp d12, d13, [sp, #128]; stp d14, d15, [sp, #144]
    0xe8, 0x27, 0x06, 0x6d, 0xea, 0x2f, 0x07, 0x6d, 0xec, 0x37, 0x08, 0x6d,
    0xee, 0x3f, 0x09, 0x6d,
    // str x18, [sp, #160]
    0xf2, 0x53, 0x00, 0xf9,
    // mov x28, x0   (the context register)
    0xfc, 0x03, 0x00, 0xaa,
    // blr x1   (the blob; x30 is the return address)
    0x20, 0x00, 0x3f, 0xd6,
    // ldr x18, [sp, #160]
    0xf2, 0x53, 0x40, 0xf9,
    // ldp d14, d15, [sp, #144]; ldp d12, d13, [sp, #128]; ldp d10, d11, [sp, #112]; ldp d8, d9, [sp, #96]
    0xee, 0x3f, 0x49, 0x6d, 0xec, 0x37, 0x48, 0x6d, 0xea, 0x2f, 0x47, 0x6d,
    0xe8, 0x27, 0x46, 0x6d,
    // ldp x27, x28, [sp, #80]; ldp x25, x26, [sp, #64]; ldp x23, x24, [sp, #48]
    0xfb, 0x73, 0x45, 0xa9, 0xf9, 0x6b, 0x44, 0xa9, 0xf7, 0x63, 0x43, 0xa9,
    // ldp x21, x22, [sp, #32]; ldp x19, x20, [sp, #16]
    0xf5, 0x5b, 0x42, 0xa9, 0xf3, 0x53, 0x41, 0xa9,
    // ldp x29, x30, [sp], #176
    0xfd, 0x7b, 0xcb, 0xa8,
    // ret
    0xc0, 0x03, 0x5f, 0xd6,
];

/// The enter stub for this target (AAPCS64, macOS and Windows: arguments in
/// `x0`, `x1`; `x2` is not used; `x19-x30` and `d8-d15` are callee-saved, and
/// `x18`, the platform register, is saved too, since the blob may write it).
///
/// It does **no cache maintenance of its own**: reading `CTR_EL0` at EL0 is
/// not allowed on macOS (it raises SIGILL) and Windows does not document it.
/// There the instruction cache is made coherent by an OS call that this crate
/// makes, not the caller: on macOS `sys_icache_invalidate`, which
/// `CodeRegion::write` calls on every write; on Windows
/// `FlushInstructionCache`, which `crate::enter` calls in the executing
/// process before every entry (the writer is another process). The stub only
/// issues `dsb ish; isb`, so that this thread refetches.
#[cfg(all(target_arch = "aarch64", not(target_os = "linux")))]
#[rustfmt::skip]
pub(crate) const STUB: &[u8] = &[
    // dsb ish; isb   (the invalidates are complete; refetch from here)
    0x9f, 0x3b, 0x03, 0xd5, 0xdf, 0x3f, 0x03, 0xd5,
    // stp x29, x30, [sp, #-176]!
    0xfd, 0x7b, 0xb5, 0xa9,
    // stp x19, x20, [sp, #16]; stp x21, x22, [sp, #32]; stp x23, x24, [sp, #48]
    0xf3, 0x53, 0x01, 0xa9, 0xf5, 0x5b, 0x02, 0xa9, 0xf7, 0x63, 0x03, 0xa9,
    // stp x25, x26, [sp, #64]; stp x27, x28, [sp, #80]
    0xf9, 0x6b, 0x04, 0xa9, 0xfb, 0x73, 0x05, 0xa9,
    // stp d8, d9, [sp, #96]; stp d10, d11, [sp, #112]; stp d12, d13, [sp, #128]; stp d14, d15, [sp, #144]
    0xe8, 0x27, 0x06, 0x6d, 0xea, 0x2f, 0x07, 0x6d, 0xec, 0x37, 0x08, 0x6d,
    0xee, 0x3f, 0x09, 0x6d,
    // str x18, [sp, #160]
    0xf2, 0x53, 0x00, 0xf9,
    // mov x28, x0   (the context register)
    0xfc, 0x03, 0x00, 0xaa,
    // blr x1   (the blob; x30 is the return address)
    0x20, 0x00, 0x3f, 0xd6,
    // ldr x18, [sp, #160]
    0xf2, 0x53, 0x40, 0xf9,
    // ldp d14, d15, [sp, #144]; ldp d12, d13, [sp, #128]; ldp d10, d11, [sp, #112]; ldp d8, d9, [sp, #96]
    0xee, 0x3f, 0x49, 0x6d, 0xec, 0x37, 0x48, 0x6d, 0xea, 0x2f, 0x47, 0x6d,
    0xe8, 0x27, 0x46, 0x6d,
    // ldp x27, x28, [sp, #80]; ldp x25, x26, [sp, #64]; ldp x23, x24, [sp, #48]
    0xfb, 0x73, 0x45, 0xa9, 0xf9, 0x6b, 0x44, 0xa9, 0xf7, 0x63, 0x43, 0xa9,
    // ldp x21, x22, [sp, #32]; ldp x19, x20, [sp, #16]
    0xf5, 0x5b, 0x42, 0xa9, 0xf3, 0x53, 0x41, 0xa9,
    // ldp x29, x30, [sp], #176
    0xfd, 0x7b, 0xcb, 0xa8,
    // ret
    0xc0, 0x03, 0x5f, 0xd6,
];

/// A blob that is just the exit sequence with code 42, for tests: x86-64
/// `mov eax, 42; mov [r15 + 256], rax; ret`.
#[cfg(all(test, target_arch = "x86_64"))]
pub(crate) const EXIT_42: &[u8] = &[
    0xb8, 0x2a, 0x00, 0x00, 0x00, 0x49, 0x89, 0x87, 0x00, 0x01, 0x00, 0x00, 0xc3,
];

/// A blob that is just the exit sequence with code 42, for tests: A64
/// `movz x0, #42; str x0, [x28, #256]; ret`.
#[cfg(all(test, target_arch = "aarch64"))]
pub(crate) const EXIT_42: &[u8] = &[
    0x40, 0x05, 0x80, 0xd2, 0x80, 0x83, 0x00, 0xf9, 0xc0, 0x03, 0x5f, 0xd6,
];

/// [`EXIT_42`] with the code replaced by `code` (below 8, for the test
/// that rewrites a blob in place): x86-64 `mov eax, imm32` and A64
/// `movz x0, #imm16`.
#[cfg(test)]
pub(crate) fn exit_with(code: u8) -> Vec<u8> {
    let mut blob = EXIT_42.to_vec();
    #[cfg(target_arch = "x86_64")]
    if let Some(b) = blob.get_mut(1) {
        *b = code;
    }
    #[cfg(target_arch = "aarch64")]
    {
        // `movz x0, #imm16` is 0xd280_0000 | imm16 << 5.
        let word = 0xd280_0000u32 | (u32::from(code) << 5);
        for (dst, src) in blob.iter_mut().zip(word.to_le_bytes()) {
            *dst = src;
        }
    }
    blob
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_stub_fits_before_the_code() {
        assert!(STUB.len() < CODE_START);
        assert_eq!(CODE_START % 16, 0);
    }

    #[test]
    fn context_is_the_abis_512_bytes() {
        assert_eq!(size_of::<Context>(), CONTEXT_BYTES);
        assert_eq!(CONTEXT_WORDS.saturating_mul(8), CONTEXT_BYTES);
        assert_eq!(EXIT_CODE_WORD.saturating_mul(8), 256);
        let mut c = Context::new();
        assert_eq!(c.exit_code(), 0);
        if let Some(w) = c.words_mut().get_mut(EXIT_CODE_WORD) {
            *w = 7;
        }
        assert_eq!(c.exit_code(), 7);
    }

    #[test]
    fn writes_stay_out_of_the_stub_and_inside_the_region() {
        let len = 4096;
        assert_eq!(
            write_range(len, CODE_START, &[0; 4]),
            Ok(CODE_START.saturating_add(4))
        );
        assert_eq!(write_range(len, 0, &[0; 4]), Err(CodeError::OutOfRange));
        assert_eq!(
            write_range(len, CODE_START.saturating_sub(1), &[0]),
            Err(CodeError::OutOfRange)
        );
        assert_eq!(write_range(len, len, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(write_range(len, len, &[]), Ok(len));
        assert_eq!(
            write_range(len, usize::MAX, &[0, 0]),
            Err(CodeError::OutOfRange)
        );
    }

    #[test]
    fn sizes_need_room_for_the_stub() {
        assert_eq!(check_size(CODE_START), Err(CodeError::BadSize));
        assert_eq!(check_size(CODE_START.saturating_add(1)), Ok(()));
        assert_eq!(check_size(usize::MAX), Err(CodeError::BadSize));
    }
}
