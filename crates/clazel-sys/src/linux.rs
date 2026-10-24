//! Linux: `prctl`, `seccomp`, Landlock and `unshare`, and the two escape
//! attempts the sandbox tests make (`fork`, `ptrace`).
//!
//! None of these takes a decision: each hands a value to the kernel. The
//! kernel's rules (a filter needs `no_new_privs` or `CAP_SYS_ADMIN`; Landlock
//! needs 5.13; `unshare(USER)` fails in a multithreaded process) show up as an
//! [`Errno`], and the caller fails closed.

use std::fmt;

use crate::Errno;

/// One classic BPF instruction: `struct sock_filter` of `<linux/filter.h>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SockFilter {
    /// Opcode.
    pub code: u16,
    /// Jump offset if the test is true.
    pub jt: u8,
    /// Jump offset if the test is false.
    pub jf: u8,
    /// Operand.
    pub k: u32,
}

/// The kernel's limit on the length of a classic BPF program
/// (`BPF_MAXINSNS`, `<linux/bpf_common.h>`).
pub const MAX_BPF_INSNS: usize = 4096;

/// `prctl(PR_SET_NO_NEW_PRIVS, 1)`: this process and its descendants can never
/// gain privileges through `execve` (setuid and file capabilities stop
/// working). The kernel requires it before an unprivileged seccomp filter.
/// It cannot be undone.
pub fn set_no_new_privs() -> Result<(), Errno> {
    // `prctl` is variadic and reads each argument as an `unsigned long`.
    let one: libc::c_ulong = 1;
    let zero: libc::c_ulong = 0;
    // SAFETY: man 2 prctl: PR_SET_NO_NEW_PRIVS takes arg2 = 1 and requires
    // arg3, arg4 and arg5 to be 0. All four are plain integers passed as
    // `unsigned long`, as the variadic `libc::prctl(c_int, ...) -> c_int`
    // declaration needs; no pointer is passed, so nothing can dangle.
    let rc = unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, one, zero, zero, zero) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

/// `seccomp(SECCOMP_SET_MODE_FILTER, 0, program)`: install a BPF filter that
/// the kernel runs on every system call from now on, from every thread
/// created afterwards. `program` must have 1 to [`MAX_BPF_INSNS`]
/// instructions; the kernel validates it further. Call
/// [`set_no_new_privs`] first, or the kernel refuses with `EACCES`.
pub fn seccomp_set_mode_filter(program: &[SockFilter]) -> Result<(), Errno> {
    let invalid = Errno(libc::EINVAL);
    if program.is_empty() || program.len() > MAX_BPF_INSNS {
        return Err(invalid);
    }
    let insns: Vec<libc::sock_filter> = program
        .iter()
        .map(|i| libc::sock_filter {
            code: i.code,
            jt: i.jt,
            jf: i.jf,
            k: i.k,
        })
        .collect();
    let len = u16::try_from(insns.len()).map_err(|_| invalid)?;
    let prog = libc::sock_fprog {
        len,
        filter: insns.as_ptr().cast_mut(),
    };
    let prog_ptr: *const libc::sock_fprog = &raw const prog;
    // `syscall` is variadic and reads each argument as an `unsigned long`.
    let operation = libc::c_ulong::from(libc::SECCOMP_SET_MODE_FILTER);
    let flags: libc::c_ulong = 0;
    // SAFETY: man 2 seccomp: with SECCOMP_SET_MODE_FILTER, `args` points to a
    // `struct sock_fprog` (the `libc::sock_fprog` declaration: a u16 length
    // and a pointer to that many `sock_filter`s) and `flags` may be 0. `prog`
    // is a live local, so `prog_ptr` is valid and aligned; `prog.filter`
    // points to the `len` initialised elements of `insns`, which is not
    // dropped before the end of this function; the kernel only reads them and
    // copies the program before returning. The syscall number is
    // `libc::SYS_seccomp` for this target, and the call returns 0 or -1.
    let rc = unsafe { libc::syscall(libc::SYS_seccomp, operation, flags, prog_ptr) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

/// `landlock_create_ruleset` with `handled_access_fs` as the set of
/// filesystem accesses the ruleset governs (the `LANDLOCK_ACCESS_FS_*` bits),
/// then `landlock_restrict_self` on the new ruleset. With no rule added, every
/// governed access is denied everywhere, for this thread and everything it
/// creates later. Pass the bits of the kernel's ABI version; unknown bits make
/// the kernel refuse (`EINVAL`), which the caller treats as "no Landlock".
///
/// The ruleset's descriptor stays open for the life of the process. The
/// kernel creates it close-on-exec, and once enforced it gives no power: the
/// restriction is a snapshot, and a process can only add more restrictions.
/// (Closing it would need `close`, which is not on the list of foreign
/// functions this crate may call.)
pub fn landlock_deny_filesystem(handled_access_fs: u64) -> Result<(), Errno> {
    let invalid = Errno(libc::EINVAL);
    // `struct landlock_ruleset_attr`, ABI version 1 (`<linux/landlock.h>`).
    #[repr(C)]
    struct RulesetAttr {
        handled_access_fs: u64,
    }
    let attr = RulesetAttr { handled_access_fs };
    let attr_ptr: *const RulesetAttr = &raw const attr;
    // `syscall` is variadic and reads each argument as an `unsigned long`.
    let size = libc::c_ulong::try_from(size_of::<RulesetAttr>()).map_err(|_| invalid)?;
    let no_flags: libc::c_ulong = 0;
    // SAFETY: man 7 landlock and man 2 landlock_create_ruleset: `attr` points
    // to a `struct landlock_ruleset_attr` of `size` bytes (ABI 1, one u64,
    // mirrored by `RulesetAttr`, which is `repr(C)`), `flags` is 0 and the
    // call returns a new descriptor or -1. `attr` is a live local, so the
    // pointer is valid and aligned for the call, which only reads it. The
    // number is `libc::SYS_landlock_create_ruleset`.
    let fd = unsafe { libc::syscall(libc::SYS_landlock_create_ruleset, attr_ptr, size, no_flags) };
    if fd < 0 {
        return Err(Errno::last());
    }
    let ruleset = libc::c_ulong::try_from(fd).map_err(|_| invalid)?;
    // SAFETY: man 7 landlock and man 2 landlock_restrict_self: the arguments
    // are a ruleset descriptor, just returned by landlock_create_ruleset and
    // still open, and `flags`, which must be 0. Both are integers passed as
    // `unsigned long` to the variadic `libc::syscall`; no pointer is involved.
    // The number is `libc::SYS_landlock_restrict_self`.
    let rc = unsafe { libc::syscall(libc::SYS_landlock_restrict_self, ruleset, no_flags) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

/// A set of namespaces for [`unshare`].
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Namespaces(libc::c_int);

impl Namespaces {
    /// No namespace.
    pub const NONE: Namespaces = Namespaces(0);
    /// A new user namespace (`CLONE_NEWUSER`).
    pub const USER: Namespaces = Namespaces(libc::CLONE_NEWUSER);
    /// A new mount namespace (`CLONE_NEWNS`).
    pub const MOUNT: Namespaces = Namespaces(libc::CLONE_NEWNS);
    /// A new PID namespace for children (`CLONE_NEWPID`).
    pub const PID: Namespaces = Namespaces(libc::CLONE_NEWPID);
    /// A new network namespace (`CLONE_NEWNET`).
    pub const NETWORK: Namespaces = Namespaces(libc::CLONE_NEWNET);
    /// A new IPC namespace (`CLONE_NEWIPC`).
    pub const IPC: Namespaces = Namespaces(libc::CLONE_NEWIPC);

    /// Both sets together.
    #[must_use]
    pub const fn union(self, other: Namespaces) -> Namespaces {
        Namespaces(self.0 | other.0)
    }

    /// The `CLONE_NEW*` bits.
    #[must_use]
    pub const fn bits(self) -> i32 {
        self.0
    }
}

impl fmt::Debug for Namespaces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Namespaces({:#x})", self.0)
    }
}

/// `unshare(2)` for the namespaces in `namespaces`. The kernel refuses
/// `USER` in a process with more than one thread (`EINVAL`) and the other
/// kinds without `CAP_SYS_ADMIN` unless `USER` comes with them; a distribution
/// may disable unprivileged user namespaces. All of these are an [`Errno`].
pub fn unshare(namespaces: Namespaces) -> Result<(), Errno> {
    let flags = namespaces.bits();
    // SAFETY: man 2 unshare: the only argument is an integer set of CLONE_NEW*
    // flags, which `Namespaces` builds only from the `libc::CLONE_NEW*`
    // constants; `libc::unshare(c_int) -> c_int` takes no pointer, so nothing
    // can dangle.
    let rc = unsafe { libc::unshare(flags) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

/// `fork(2)`, as an *attempt* for the sandbox tests: `Ok` means the kernel
/// created a child, which is an escape. The child, if there is one, calls
/// `_exit(0)` at once and does nothing else, so it touches no lock or
/// allocator of this (possibly multithreaded) process. The parent does not
/// wait for it: a child that was created is reparented and reaped when this
/// process exits. Under the renderer's seccomp filter the call ends the
/// process with `SIGSYS` instead of returning.
pub fn attempt_fork() -> Result<(), Errno> {
    // SAFETY: man 2 fork: `fork` takes no argument and returns the child's pid
    // in the parent, 0 in the child, or -1 and sets errno; the
    // `libc::fork() -> pid_t` declaration matches. No pointer is passed. In a
    // multithreaded process the child may only call async-signal-safe
    // functions, and the only thing it does (below) is `_exit`.
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        return Err(Errno::last());
    }
    if pid == 0 {
        // SAFETY: man 2 _exit: `_exit(status)` ends the calling process at
        // once, runs no atexit handler or destructor, and is
        // async-signal-safe, so it is the one call a fork child may make in
        // a multithreaded process. The `libc::_exit(c_int) -> !` declaration
        // takes an integer; no pointer is involved.
        unsafe { libc::_exit(0) }
    }
    Ok(())
}

/// `ptrace(PTRACE_ATTACH, pid, 0, 0)`, as an *attempt* for the sandbox tests:
/// `Ok` means the kernel let this process attach to `pid`, which is an
/// escape. The tracee is left attached and stopped; the test kills it. A
/// `pid` that is not positive is refused here with `EINVAL`, before the
/// kernel is asked. Without a sandbox the kernel may still refuse (`EPERM`:
/// Yama's `ptrace_scope`, or no common user); under the renderer's seccomp
/// filter the call ends the process with `SIGSYS`.
pub fn attempt_ptrace_attach(pid: i32) -> Result<(), Errno> {
    let invalid = Errno(libc::EINVAL);
    if pid <= 0 {
        return Err(invalid);
    }
    // `syscall` is variadic and reads each argument as an `unsigned long`;
    // the request constant is a `c_uint` or a `c_int` depending on the libc.
    let request = libc::c_ulong::try_from(i64::from(libc::PTRACE_ATTACH)).map_err(|_| invalid)?;
    let target = libc::c_ulong::try_from(pid).map_err(|_| invalid)?;
    let zero: libc::c_ulong = 0;
    // SAFETY: man 2 ptrace: `ptrace(request, pid, addr, data)`; with
    // PTRACE_ATTACH, `pid` is the tracee and `addr` and `data` are ignored
    // (0). All four are integers passed as `unsigned long` to the variadic
    // `libc::syscall`, which calls the raw system call (glibc's `ptrace`
    // wrapper is variadic too and its request type differs by libc); no
    // pointer is passed, so nothing can dangle. The number is
    // `libc::SYS_ptrace`, and the call returns 0 or -1.
    let rc = unsafe { libc::syscall(libc::SYS_ptrace, request, target, zero, zero) };
    if rc == 0 { Ok(()) } else { Err(Errno::last()) }
}

#[cfg(test)]
mod tests {
    use super::{
        MAX_BPF_INSNS, Namespaces, SockFilter, attempt_ptrace_attach, seccomp_set_mode_filter,
    };
    use crate::Errno;

    const RET_KILL: SockFilter = SockFilter {
        code: 0x06,
        jt: 0,
        jf: 0,
        k: 0,
    };

    #[test]
    fn program_length_is_checked_before_the_kernel_is_asked() {
        let einval = Err(Errno(libc::EINVAL));
        assert_eq!(seccomp_set_mode_filter(&[]), einval);
        let too_long = vec![RET_KILL; MAX_BPF_INSNS.saturating_add(1)];
        assert_eq!(seccomp_set_mode_filter(&too_long), einval);
    }

    #[test]
    fn namespaces_combine() {
        let both = Namespaces::USER.union(Namespaces::NETWORK);
        assert_eq!(both.bits(), libc::CLONE_NEWUSER | libc::CLONE_NEWNET);
        assert_eq!(Namespaces::NONE.union(Namespaces::IPC), Namespaces::IPC);
    }

    #[test]
    fn a_pid_that_is_not_positive_never_reaches_the_kernel() {
        assert_eq!(attempt_ptrace_attach(0), Err(Errno(libc::EINVAL)));
        assert_eq!(attempt_ptrace_attach(-1), Err(Errno(libc::EINVAL)));
    }
}
