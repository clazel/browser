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
//! - The **stub** is the only code that meets the platform ABI. It saves the
//!   platform's callee-saved registers (everything but the context register
//!   and the stack pointer is the blob's, so it saves them all), sets the
//!   context register from its first argument, calls its second argument
//!   (the blob's address), and on the blob's `ret` restores the registers and
//!   returns. The blob has no prologue or epilogue: its exit sequence is
//!   `mov t, code; mov [ctx + 256], t; ret`, and the `ret` returns here.
//! - **Instruction-cache maintenance** is the stub's first instructions on
//!   A64 (`dsb ish; isb`, serializing the instruction stream), and nothing on
//!   x86-64, whose instruction fetch is coherent with stores. It is not a
//!   system call, so the renderer needs none (jit.md J.7). On Windows the
//!   writer also calls `FlushInstructionCache`, and on macOS the writer calls
//!   `sys_icache_invalidate`.
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
/// **Only `clazel-codecheck` may build one**, from the offset of an entry
/// it validated in the blob it checked. This crate cannot depend on it (its
/// only dependency is `libc`), so the constructor is public and the rule is
/// kept by review: nothing but `clazel-codecheck` may call
/// [`Validated::new`]. A later `cargo xtask check` rule should enforce it.
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
/// the blob's address; no result.
#[cfg(all(target_arch = "x86_64", not(windows)))]
pub(crate) const STUB: &[u8] = &[
    // push rbx; push rbp; push r12; push r13; push r14; push r15
    0x53, 0x55, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57,
    // sub rsp, 8   (the stack is 16-aligned at the call below)
    0x48, 0x83, 0xec, 0x08, // mov r15, rdi   (the context register)
    0x49, 0x89, 0xff, // call rsi   (the blob; its `ret` returns here)
    0xff, 0xd6, // add rsp, 8
    0x48, 0x83, 0xc4, 0x08, // pop r15; pop r14; pop r13; pop r12; pop rbp; pop rbx
    0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5d, 0x5b, // ret
    0xc3,
];

/// The enter stub for this target (Windows x64: arguments in `rcx`, `rdx`;
/// `rbx rbp rdi rsi r12-r15` and `xmm6-xmm15` are callee-saved; 32 bytes of
/// shadow space).
#[cfg(all(target_arch = "x86_64", windows))]
pub(crate) const STUB: &[u8] = &[
    // push rbx; push rbp; push rdi; push rsi; push r12; push r13; push r14; push r15
    0x53, 0x55, 0x57, 0x56, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57,
    // sub rsp, 200   (32 shadow + 160 for xmm6-15 + 8 alignment)
    0x48, 0x81, 0xec, 0xc8, 0x00, 0x00, 0x00, // movaps [rsp+32+16i], xmm(6+i), i = 0..10
    0x0f, 0x29, 0x74, 0x24, 0x20, 0x0f, 0x29, 0x7c, 0x24, 0x30, 0x44, 0x0f, 0x29, 0x44, 0x24, 0x40,
    0x44, 0x0f, 0x29, 0x4c, 0x24, 0x50, 0x44, 0x0f, 0x29, 0x54, 0x24, 0x60, 0x44, 0x0f, 0x29, 0x5c,
    0x24, 0x70, 0x44, 0x0f, 0x29, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x29, 0xac, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x29, 0xb4, 0x24, 0xa0, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x29,
    0xbc, 0x24, 0xb0, 0x00, 0x00, 0x00, // mov r15, rcx   (the context register)
    0x49, 0x89, 0xcf, // call rdx   (the blob)
    0xff, 0xd2, // movaps xmm(6+i), [rsp+32+16i], i = 0..10
    0x0f, 0x28, 0x74, 0x24, 0x20, 0x0f, 0x28, 0x7c, 0x24, 0x30, 0x44, 0x0f, 0x28, 0x44, 0x24, 0x40,
    0x44, 0x0f, 0x28, 0x4c, 0x24, 0x50, 0x44, 0x0f, 0x28, 0x54, 0x24, 0x60, 0x44, 0x0f, 0x28, 0x5c,
    0x24, 0x70, 0x44, 0x0f, 0x28, 0xa4, 0x24, 0x80, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x28, 0xac, 0x24,
    0x90, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x28, 0xb4, 0x24, 0xa0, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x28,
    0xbc, 0x24, 0xb0, 0x00, 0x00, 0x00, // add rsp, 200
    0x48, 0x81, 0xc4, 0xc8, 0x00, 0x00, 0x00,
    // pop r15; pop r14; pop r13; pop r12; pop rsi; pop rdi; pop rbp; pop rbx
    0x41, 0x5f, 0x41, 0x5e, 0x41, 0x5d, 0x41, 0x5c, 0x5e, 0x5f, 0x5d, 0x5b, // ret
    0xc3,
];

/// The enter stub for this target (AAPCS64: arguments in `x0`, `x1`; `x19-x30`
/// and `d8-d15` are callee-saved, and `x18`, the platform register on Apple
/// and Windows, is saved too, since the blob may write it).
#[cfg(target_arch = "aarch64")]
pub(crate) const STUB: &[u8] = &[
    // dsb ish; isb
    0x9f, 0x3b, 0x03, 0xd5, 0xdf, 0x3f, 0x03, 0xd5, // stp x29, x30, [sp, #-176]!
    0xfd, 0x7b, 0xb5, 0xa9,
    // stp x19, x20, [sp, #16]; stp x21, x22, [sp, #32]; stp x23, x24, [sp, #48]
    0xf3, 0x53, 0x01, 0xa9, 0xf5, 0x5b, 0x02, 0xa9, 0xf7, 0x63, 0x03, 0xa9,
    // stp x25, x26, [sp, #64]; stp x27, x28, [sp, #80]
    0xf9, 0x6b, 0x04, 0xa9, 0xfb, 0x73, 0x05, 0xa9,
    // stp d8, d9, [sp, #96]; stp d10, d11, [sp, #112]; stp d12, d13, [sp, #128]; stp d14, d15, [sp, #144]
    0xe8, 0x27, 0x06, 0x6d, 0xea, 0x2f, 0x07, 0x6d, 0xec, 0x37, 0x08, 0x6d, 0xee, 0x3f, 0x09, 0x6d,
    // str x18, [sp, #160]
    0xf2, 0x53, 0x00, 0xf9, // mov x28, x0   (the context register)
    0xfc, 0x03, 0x00, 0xaa, // blr x1   (the blob; x30 is the return address)
    0x20, 0x00, 0x3f, 0xd6, // ldr x18, [sp, #160]
    0xf2, 0x53, 0x40, 0xf9,
    // ldp d14, d15, [sp, #144]; ldp d12, d13, [sp, #128]; ldp d10, d11, [sp, #112]; ldp d8, d9, [sp, #96]
    0xee, 0x3f, 0x49, 0x6d, 0xec, 0x37, 0x48, 0x6d, 0xea, 0x2f, 0x47, 0x6d, 0xe8, 0x27, 0x46, 0x6d,
    // ldp x27, x28, [sp, #80]; ldp x25, x26, [sp, #64]; ldp x23, x24, [sp, #48]
    0xfb, 0x73, 0x45, 0xa9, 0xf9, 0x6b, 0x44, 0xa9, 0xf7, 0x63, 0x43, 0xa9,
    // ldp x21, x22, [sp, #32]; ldp x19, x20, [sp, #16]
    0xf5, 0x5b, 0x42, 0xa9, 0xf3, 0x53, 0x41, 0xa9, // ldp x29, x30, [sp], #176
    0xfd, 0x7b, 0xcb, 0xa8, // ret
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
