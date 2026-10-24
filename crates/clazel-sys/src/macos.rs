//! macOS: the Seatbelt sandbox (`sandbox_init`), and the two escape attempts
//! the sandbox tests make (`fork`, `ptrace`).
//!
//! `sandbox_init` is deprecated, but it is what Chromium and Firefox still
//! use, and no replacement exists for a process that is not an App Sandbox
//! application. `libc` does not declare it, so it is declared here.

use std::ffi::{CString, c_char, c_int};
use std::fmt;

use crate::Errno;

// SAFETY: man 3 sandbox_init and <sandbox.h>: `int sandbox_init(const char
// *profile, uint64_t flags, char **errorbuf)` and `void
// sandbox_free_error(char *errorbuf)`; man 2 fork: `pid_t fork(void)`; man 2
// _exit: `void _exit(int status)`; man 2 ptrace and <sys/ptrace.h>: `int
// ptrace(int request, pid_t pid, caddr_t addr, int data)`. The declarations
// below match those prototypes (`c_char`, `c_int` and `u64` have the C sizes
// on every macOS target, `pid_t` is `int` and `caddr_t` is `char *`), the
// functions live in libSystem, which Rust's standard library
// links, and neither is `pub` or declared `safe`, so every call needs its own
// `unsafe` block.
unsafe extern "C" {
    fn sandbox_init(profile: *const c_char, flags: u64, errorbuf: *mut *mut c_char) -> c_int;
    fn sandbox_free_error(errorbuf: *mut c_char);
    fn fork() -> c_int;
    fn _exit(status: c_int) -> !;
    fn ptrace(request: c_int, pid: c_int, addr: *mut c_char, data: c_int) -> c_int;
}

/// `PT_ATTACHEXC` of `<sys/ptrace.h>`: attach to a process and take its
/// exceptions as Mach messages instead of signals (what debuggers use).
const PT_ATTACHEXC: c_int = 14;

/// `EINVAL` of `<sys/errno.h>` (`libc` is not a dependency on macOS).
const EINVAL: i32 = 22;

/// Why a Seatbelt profile was not applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SandboxError {
    /// The profile text contains a NUL byte, so it cannot be a C string.
    InteriorNul,
    /// `sandbox_init` refused the profile (a syntax error, or the process is
    /// already sandboxed in a way that forbids it). The message it returns is
    /// freed, not read: reading it would need a second kind of `unsafe` call.
    Rejected,
}

impl fmt::Display for SandboxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SandboxError::InteriorNul => f.write_str("sandbox profile contains a NUL byte"),
            SandboxError::Rejected => f.write_str("sandbox_init rejected the profile"),
        }
    }
}

impl std::error::Error for SandboxError {}

/// `sandbox_init(profile, 0, ..)`: parse `profile`, written in the Seatbelt
/// profile language (SBPL), and confine this process to it, for good. A
/// process cannot leave or loosen a sandbox once it is in one.
pub fn sandbox_init_profile(profile: &str) -> Result<(), SandboxError> {
    let text = CString::new(profile).map_err(|_| SandboxError::InteriorNul)?;
    let text_ptr: *const c_char = text.as_ptr();
    let mut error: *mut c_char = std::ptr::null_mut();
    let error_slot: *mut *mut c_char = &raw mut error;
    // SAFETY: man 3 sandbox_init: `profile` must be a NUL-terminated string
    // and, with `flags` 0, it is SBPL source (SANDBOX_NAMED is not set);
    // `errorbuf` must be writable and receives a heap string on failure. The
    // arguments have the types of the declaration above: `text_ptr` points to
    // the NUL-terminated buffer of `text`, which lives to the end of this
    // function, and `error_slot` points to the live local `error`.
    let rc = unsafe { sandbox_init(text_ptr, 0, error_slot) };
    if rc == 0 {
        return Ok(());
    }
    if !error.is_null() {
        // SAFETY: man 3 sandbox_init: a non-NULL `*errorbuf` set by a failed
        // sandbox_init was allocated by it and must be released with
        // sandbox_free_error, once. `error` was set by that call and is not
        // used again, nor copied anywhere.
        unsafe { sandbox_free_error(error) };
    }
    Err(SandboxError::Rejected)
}

/// `fork(2)`, as an *attempt* for the sandbox tests: `Ok` means the OS
/// created a child, which is an escape. The child, if there is one, calls
/// `_exit(0)` at once and does nothing else, so it touches no lock or
/// allocator of this (possibly multithreaded) process. The parent does not
/// wait for it: a child that was created is reparented and reaped when this
/// process exits. Seatbelt's `(deny default)` refuses the call (`EPERM`).
pub fn attempt_fork() -> Result<(), Errno> {
    // SAFETY: man 2 fork: `fork` takes no argument and returns the child's pid
    // in the parent, 0 in the child, or -1 and sets errno; the declaration
    // above matches `pid_t fork(void)`. No pointer is passed. In a
    // multithreaded process the child may only call async-signal-safe
    // functions, and the only thing it does (below) is `_exit`.
    let pid = unsafe { fork() };
    if pid < 0 {
        return Err(Errno::last());
    }
    if pid == 0 {
        // SAFETY: man 2 _exit: `_exit(status)` ends the calling process at
        // once, runs no atexit handler or destructor, and is
        // async-signal-safe, so it is the one call a fork child may make in
        // a multithreaded process. The declaration above matches `void
        // _exit(int)`; no pointer is involved.
        unsafe { _exit(0) }
    }
    Ok(())
}

/// `ptrace(PT_ATTACHEXC, pid, 0, 0)`, as an *attempt* for the sandbox tests:
/// `Ok` means the OS let this process attach to `pid` as a debugger, which is
/// an escape. The tracee is left attached; the test kills it. A `pid` that is
/// not positive is refused here with `EINVAL`, before the OS is asked.
/// Without a sandbox the OS may still refuse (`EPERM`: a platform binary, a
/// hardened-runtime process, or another user's), so a test must first attach
/// to a plain binary unsandboxed to show that a denial is the sandbox's.
pub fn attempt_ptrace_attach(pid: i32) -> Result<(), Errno> {
    if pid <= 0 {
        return Err(Errno(EINVAL));
    }
    let addr: *mut c_char = std::ptr::null_mut();
    // SAFETY: man 2 ptrace: `ptrace(request, pid, addr, data)`; with
    // PT_ATTACHEXC, `pid` is the process to attach to and `addr` and `data`
    // are ignored. The arguments have the types of the declaration above
    // (`int`, `pid_t`, `caddr_t`, `int`): `PT_ATTACHEXC` is a constant, `pid`
    // is positive, and `addr` is a null pointer, which the kernel never reads
    // for this request, so nothing can dangle.
    let rc = unsafe { ptrace(PT_ATTACHEXC, pid, addr, 0) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

#[cfg(test)]
mod tests {
    use super::{SandboxError, attempt_ptrace_attach, sandbox_init_profile};
    use crate::Errno;

    #[test]
    fn a_profile_with_a_nul_never_reaches_the_os() {
        assert_eq!(
            sandbox_init_profile("(version 1)\0(deny default)"),
            Err(SandboxError::InteriorNul)
        );
    }

    // Miri cannot run foreign calls. An unparsable profile is refused before
    // any sandbox is entered, so this does not confine the test process.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn an_unparsable_profile_is_rejected() {
        assert_eq!(
            sandbox_init_profile("(version 1"),
            Err(SandboxError::Rejected)
        );
    }

    #[test]
    fn a_pid_that_is_not_positive_never_reaches_the_os() {
        assert_eq!(attempt_ptrace_attach(0), Err(Errno(22)));
        assert_eq!(attempt_ptrace_attach(-1), Err(Errno(22)));
    }
}
