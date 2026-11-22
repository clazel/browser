//! macOS code regions (jit.md item J.7): `MAP_JIT` in the process itself.
//!
//! No other process can map code into a hardened-runtime process on macOS, so
//! unlike Linux and Windows the renderer validates and writes its own code
//! (jit.md J.0(b): "macOS uses `MAP_JIT` in the renderer"). A [`CodeRegion`]
//! is one anonymous `MAP_JIT` mapping, with the enter stub written at offset 0.
//! The process needs the `com.apple.security.cs.allow-jit` entitlement under
//! the hardened runtime (jit.md J.8); an unsigned test binary needs none.
//!
//! On Apple silicon a `MAP_JIT` page is writable or executable *for a
//! thread*, not both: [`CodeRegion::write`] flips the calling thread to
//! writable with `pthread_jit_write_protect_np(0)`, copies, flips it back with
//! `pthread_jit_write_protect_np(1)` (nothing else runs in between) and calls
//! `sys_icache_invalidate` on the bytes it wrote. On Intel there is no such
//! switch and the mapping is read-write-execute, and the same calls are made
//! except the switch. `libc` is not a dependency on macOS, so the calls are
//! declared here.

use std::ffi::{c_int, c_void};

use crate::CodeError;
use crate::code::{STUB, check_size, write_range};

// SAFETY: man 2 mmap and <sys/mman.h>: `void *mmap(void *addr, size_t len, int
// prot, int flags, int fd, off_t offset)` (`off_t` is `i64` on every macOS
// target), and man 2 munmap: `int munmap(void *addr, size_t len)`; man 3 memcpy
// and <string.h>: `void *memcpy(void *dst, const void *src, size_t n)`; man 3
// pthread_jit_write_protect_np and <pthread.h>: `void
// pthread_jit_write_protect_np(int enabled)` (Apple silicon only, so it is
// declared only there); man 3 sys_icache_invalidate and <libkern/OSCacheControl.h>:
// `void sys_icache_invalidate(void *start, size_t len)`. The declarations below
// match those prototypes (`int` is `c_int`, `size_t` is `usize`); the functions
// are in libSystem, which Rust's standard library links; none is `pub` or
// declared `safe`, so every call needs its own `unsafe` block.
unsafe extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        off: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> c_int;
    fn memcpy(dst: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
    #[cfg(target_arch = "aarch64")]
    fn pthread_jit_write_protect_np(enabled: c_int);
    fn sys_icache_invalidate(start: *mut c_void, len: usize);
}

/// `PROT_READ`, `PROT_WRITE`, `PROT_EXEC` of `<sys/mman.h>`.
const PROT_RWX: c_int = 0x1 | 0x2 | 0x4;
/// `MAP_PRIVATE`, `MAP_ANON` and `MAP_JIT` of `<sys/mman.h>`.
const MAP_JIT_ANON: c_int = 0x0002 | 0x1000 | 0x0800;

/// An executable `MAP_JIT` mapping with the enter stub at its start. Unmapped
/// on drop. [`crate::enter`] runs code in it.
#[derive(Debug)]
pub struct CodeRegion {
    base: usize,
    len: usize,
}

impl CodeRegion {
    /// A new region of `len` bytes (larger than [`crate::CODE_START`]; the OS rounds
    /// it up to whole pages), zero-filled, with the enter stub written.
    ///
    /// # Errors
    ///
    /// [`CodeError::BadSize`], or the failing `mmap`'s `errno` (without the
    /// entitlement under the hardened runtime that is `EPERM`).
    pub fn new(len: usize) -> Result<CodeRegion, CodeError> {
        check_size(len)?;
        let any_address: *mut c_void = std::ptr::null_mut();
        let no_file: c_int = -1;
        // SAFETY: man 2 mmap: with a null `addr`, `mmap` maps `len` bytes of
        // fresh zero-filled memory at a kernel-chosen address and returns it, or
        // MAP_FAILED (-1) and sets errno. `MAP_ANON` takes `fd` -1 and offset
        // 0; MAP_JIT (with MAP_PRIVATE | MAP_ANON, and PROT_READ | PROT_WRITE |
        // PROT_EXEC) asks for a region the thread can switch between writable
        // and executable, and needs the allow-jit entitlement under the hardened
        // runtime. The declaration above matches the prototype. `any_address`
        // is null, `len` was checked to fit an `isize`, and the mapping is new,
        // so it aliases nothing the program holds.
        let p = unsafe { mmap(any_address, len, PROT_RWX, MAP_JIT_ANON, no_file, 0) };
        if p as isize == -1 {
            return Err(CodeError::os("mmap"));
        }
        let mut region = CodeRegion {
            base: p as usize,
            len,
        };
        region.copy_in(0, STUB)?;
        Ok(region)
    }

    /// The region's size in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Always false: a region is larger than the stub.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Write `bytes` at `offset` from the region's start. The stub is not
    /// writable: `offset` must be at least [`crate::CODE_START`], and the write must
    /// end inside the region. The instruction cache is invalidated for the
    /// bytes written.
    ///
    /// # Errors
    ///
    /// [`CodeError::OutOfRange`].
    pub fn write(&mut self, offset: usize, bytes: &[u8]) -> Result<(), CodeError> {
        write_range(self.len, offset, bytes)?;
        self.copy_in(offset, bytes)
    }

    /// The address of the region's first byte (the stub).
    pub(crate) fn base(&self) -> usize {
        self.base
    }

    /// Copy `bytes` to `offset` with this thread writable, then executable,
    /// and invalidate the instruction cache for them.
    fn copy_in(&mut self, offset: usize, bytes: &[u8]) -> Result<(), CodeError> {
        let end = offset
            .checked_add(bytes.len())
            .ok_or(CodeError::OutOfRange)?;
        if end > self.len {
            return Err(CodeError::OutOfRange);
        }
        if bytes.is_empty() {
            return Ok(());
        }
        let at = self.base.checked_add(offset).ok_or(CodeError::OutOfRange)?;
        let dst = at as *mut c_void;
        let src: *const c_void = bytes.as_ptr().cast();
        let n = bytes.len();
        jit_write_protect(false);
        // SAFETY: man 3 memcpy: copies `n` bytes from `src` to `dst`, which must
        // not overlap. The declaration above matches the prototype. `dst` is `n`
        // bytes inside this value's MAP_JIT mapping (`at + n` was checked against
        // `len`, and the mapping lasts as long as `self`), which this thread has
        // just made writable; `src` is the live slice `bytes`, a different
        // allocation, and `n` is its length.
        let _ = unsafe { memcpy(dst, src, n) };
        jit_write_protect(true);
        // SAFETY: man 3 sys_icache_invalidate: invalidates the instruction cache
        // for `len` bytes from `start`, so that code just written there can be
        // executed; it returns nothing. The declaration above matches the
        // prototype. `dst` and the length are the bytes just written, inside the
        // mapping.
        unsafe { sys_icache_invalidate(dst, n) };
        Ok(())
    }
}

/// Switch the calling thread's `MAP_JIT` pages to read-only-executable
/// (`protect` true) or writable (false). Apple silicon only; on Intel the
/// pages are always both and this does nothing.
#[cfg(target_arch = "aarch64")]
fn jit_write_protect(protect: bool) {
    let enabled: c_int = c_int::from(protect);
    // SAFETY: man 3 pthread_jit_write_protect_np: `pthread_jit_write_protect_np(enabled)`
    // makes `MAP_JIT` pages executable and not writable for the calling thread
    // when `enabled` is nonzero, and writable and not executable when it is 0;
    // it returns nothing and affects only this thread. The declaration above
    // matches the prototype. The caller makes no other call and touches no
    // other memory while the thread is writable.
    unsafe { pthread_jit_write_protect_np(enabled) };
}

/// Intel: `MAP_JIT` pages are always writable and executable.
#[cfg(not(target_arch = "aarch64"))]
fn jit_write_protect(_protect: bool) {}

impl Drop for CodeRegion {
    fn drop(&mut self) {
        // SAFETY: man 2 munmap: removes the mapping and returns 0, or -1 and sets
        // errno. The declaration above matches the prototype. `base` and `len` are
        // the address and length of the mapping `new` made and this value owns,
        // unmapped once here, and no reference into it exists. The result is
        // ignored: nothing can be done about a failed unmap.
        let _ = unsafe { munmap(self.base as *mut c_void, self.len) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::EXIT_42;
    use crate::{CODE_START, Context, Exit, Validated, enter};

    #[test]
    #[cfg_attr(
        miri,
        ignore = "foreign calls and generated code cannot run under Miri"
    )]
    fn an_exit_blob_runs_and_returns_its_code() -> Result<(), CodeError> {
        let mut region = CodeRegion::new(16_384)?;
        region.write(CODE_START, EXIT_42)?;
        let mut ctx = Context::new();
        assert_eq!(ctx.exit_code(), 0);
        let exit = enter(&region, Validated::new(CODE_START), &mut ctx)?;
        assert_eq!(exit, Exit(42));
        assert_eq!(ctx.exit_code(), 42);
        // Again, with a fresh context, and after writing a second blob.
        let second = CODE_START.saturating_add(64);
        region.write(second, EXIT_42)?;
        let mut again = Context::new();
        assert_eq!(
            enter(&region, Validated::new(second), &mut again)?,
            Exit(42)
        );
        assert_eq!(
            enter(&region, Validated::new(CODE_START), &mut again)?,
            Exit(42)
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn another_thread_can_enter_and_write() -> Result<(), CodeError> {
        // The write-protect switch is per thread: a thread that never wrote
        // still executes, and a different thread can write.
        let mut region = CodeRegion::new(16_384)?;
        region.write(CODE_START, EXIT_42)?;
        let handle = std::thread::spawn(move || {
            let mut ctx = Context::new();
            let first = enter(&region, Validated::new(CODE_START), &mut ctx);
            let wrote = region.write(CODE_START.saturating_add(32), EXIT_42);
            (first, wrote)
        });
        let (first, wrote) = handle.join().map_err(|_| CodeError::NotACodeRegion)?;
        assert_eq!(first, Ok(Exit(42)));
        assert_eq!(wrote, Ok(()));
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn enter_and_write_refuse_what_is_outside_the_blob_area() -> Result<(), CodeError> {
        let mut region = CodeRegion::new(16_384)?;
        let mut ctx = Context::new();
        for offset in [0, 1, CODE_START.saturating_sub(1), 16_384, usize::MAX] {
            assert_eq!(
                enter(&region, Validated::new(offset), &mut ctx),
                Err(CodeError::OutOfRange),
                "offset {offset}"
            );
        }
        #[cfg(target_arch = "aarch64")]
        assert_eq!(
            enter(
                &region,
                Validated::new(CODE_START.saturating_add(2)),
                &mut ctx
            ),
            Err(CodeError::Misaligned)
        );
        assert_eq!(region.write(0, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(
            region.write(CODE_START.saturating_sub(1), &[0]),
            Err(CodeError::OutOfRange)
        );
        assert_eq!(region.write(16_384, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(CodeRegion::new(CODE_START).err(), Some(CodeError::BadSize));
        Ok(())
    }
}
