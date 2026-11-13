//! The renderer's syscall allowlist, per architecture.
//!
//! A renderer is started with one end of a socket pair as its stdin and is
//! sandboxed *after* start-up (item 2.15), so the list holds only what the
//! steady state needs: byte I/O on file descriptors it already has, memory
//! management, futexes, time, signal-mask housekeeping and exit. It holds
//! nothing that opens, connects, forks or executes, and nothing that creates
//! a descriptor or maps a file by name: `open`, `openat`, `socket`,
//! `connect`, `accept`, `bind`, `clone`, `clone3`, `fork`, `vfork`, `execve`,
//! `ptrace`, `prctl`, `ioctl`, `mount`, `unshare`, `setns`, `kill`, `tgkill`,
//! `seccomp`, `landlock_*`, `bpf`, `io_uring_*` and `perf_event_open` are all
//! absent, and so is every syscall that is merely absent from this table.
//!
//! Modelling choices (the list is deliberately conservative; widening it is
//! a reviewed change to this file):
//!
//! - Selection is by syscall number only. Arguments are not inspected, so
//!   `read`/`write`/`close` apply to every descriptor the process holds, and
//!   `mprotect`/`mmap` may request `PROT_EXEC`. Argument filters (for
//!   instance `mmap` without `PROT_EXEC` once there is no JIT) are future
//!   work, not claimed here.
//! - `sendmsg` and `recvmsg` are left out on purpose: they carry
//!   `SCM_RIGHTS`, which would let a renderer receive descriptors. Plain
//!   `read` and `write` are enough for a byte-stream socket.
//! - No thread creation: `clone` is absent, so a renderer is single-threaded
//!   after sandboxing. Threads need an argument-filtered `clone3` rule.
//! - `rt_sigaction` is absent: handlers are installed during start-up, and
//!   the sandboxed process may not install new ones.
//!
//! Syscall numbers come from the kernel's own tables, vendored in
//! `vendor/linux/` (Linux v6.12): `arch/x86/entry/syscalls/syscall_64.tbl`
//! for x86-64 and `include/uapi/asm-generic/unistd.h` for aarch64 (which
//! uses the generic table). `tests/vendored.rs` re-derives every number
//! below from those files, so none is from memory.

/// A CPU architecture whose syscall ABI the sandbox covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arch {
    /// x86-64 (`AUDIT_ARCH_X86_64`).
    X86_64,
    /// aarch64 (`AUDIT_ARCH_AARCH64`).
    Aarch64,
}

/// `__AUDIT_ARCH_64BIT` (`include/uapi/linux/audit.h`).
pub const AUDIT_ARCH_64BIT: u32 = 0x8000_0000;
/// `__AUDIT_ARCH_LE` (`include/uapi/linux/audit.h`).
pub const AUDIT_ARCH_LE: u32 = 0x4000_0000;
/// `EM_X86_64` (`include/uapi/linux/elf-em.h`).
pub const EM_X86_64: u32 = 62;
/// `EM_AARCH64` (`include/uapi/linux/elf-em.h`).
pub const EM_AARCH64: u32 = 183;
/// `AUDIT_ARCH_X86_64 = EM_X86_64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`.
pub const AUDIT_ARCH_X86_64: u32 = EM_X86_64 | AUDIT_ARCH_64BIT | AUDIT_ARCH_LE;
/// `AUDIT_ARCH_AARCH64 = EM_AARCH64 | __AUDIT_ARCH_64BIT | __AUDIT_ARCH_LE`.
pub const AUDIT_ARCH_AARCH64: u32 = EM_AARCH64 | AUDIT_ARCH_64BIT | AUDIT_ARCH_LE;

impl Arch {
    /// Both architectures.
    pub const ALL: [Arch; 2] = [Arch::X86_64, Arch::Aarch64];

    /// The `seccomp_data.arch` value for this architecture.
    pub const fn audit_arch(self) -> u32 {
        match self {
            Arch::X86_64 => AUDIT_ARCH_X86_64,
            Arch::Aarch64 => AUDIT_ARCH_AARCH64,
        }
    }
}

/// One allowlist entry.
#[derive(Clone, Copy, Debug)]
pub struct Syscall {
    /// The kernel's name for the syscall (`sys_<name>`).
    pub name: &'static str,
    /// Its number on x86-64.
    pub x86_64: u32,
    /// Its number on aarch64.
    pub aarch64: u32,
    /// What the renderer needs it for.
    pub reason: &'static str,
}

impl Syscall {
    /// The number of this syscall on `arch`.
    pub const fn number(&self, arch: Arch) -> u32 {
        match arch {
            Arch::X86_64 => self.x86_64,
            Arch::Aarch64 => self.aarch64,
        }
    }
}

/// The allowlist. Every entry exists on both architectures.
pub const ALLOWLIST: &[Syscall] = &[
    Syscall {
        name: "read",
        x86_64: 0,
        aarch64: 63,
        reason: "read IPC frames from the inherited socket (stdin)",
    },
    Syscall {
        name: "write",
        x86_64: 1,
        aarch64: 64,
        reason: "write IPC frames to the inherited socket; stderr diagnostics",
    },
    Syscall {
        name: "close",
        x86_64: 3,
        aarch64: 57,
        reason: "close descriptors the renderer already holds",
    },
    Syscall {
        name: "mmap",
        x86_64: 9,
        aarch64: 222,
        reason: "allocator arenas and stacks (anonymous memory)",
    },
    Syscall {
        name: "mprotect",
        x86_64: 10,
        aarch64: 226,
        reason: "allocator guard pages and arena growth",
    },
    Syscall {
        name: "munmap",
        x86_64: 11,
        aarch64: 215,
        reason: "allocator returning arenas",
    },
    Syscall {
        name: "brk",
        x86_64: 12,
        aarch64: 214,
        reason: "allocator heap growth (glibc and musl malloc)",
    },
    Syscall {
        name: "rt_sigprocmask",
        x86_64: 14,
        aarch64: 135,
        reason: "libc and the Rust runtime save and restore the signal mask",
    },
    Syscall {
        name: "rt_sigreturn",
        x86_64: 15,
        aarch64: 139,
        reason: "return from a signal handler installed before sandboxing",
    },
    Syscall {
        name: "sched_yield",
        x86_64: 24,
        aarch64: 124,
        reason: "spin-lock back-off in std::sync",
    },
    Syscall {
        name: "mremap",
        x86_64: 25,
        aarch64: 216,
        reason: "allocator growing a large block in place (realloc)",
    },
    Syscall {
        name: "madvise",
        x86_64: 28,
        aarch64: 233,
        reason: "allocator releasing pages (MADV_DONTNEED, MADV_FREE)",
    },
    Syscall {
        name: "nanosleep",
        x86_64: 35,
        aarch64: 101,
        reason: "std::thread::sleep",
    },
    Syscall {
        name: "exit",
        x86_64: 60,
        aarch64: 93,
        reason: "terminate the thread",
    },
    Syscall {
        name: "sigaltstack",
        x86_64: 131,
        aarch64: 132,
        reason: "Rust's stack-overflow handler alternate stack",
    },
    Syscall {
        name: "gettid",
        x86_64: 186,
        aarch64: 178,
        reason: "thread id for locks and diagnostics",
    },
    Syscall {
        name: "futex",
        x86_64: 202,
        aarch64: 98,
        reason: "Mutex, Condvar, Once and parking in std::sync",
    },
    Syscall {
        name: "clock_gettime",
        x86_64: 228,
        aarch64: 113,
        reason: "Instant::now and SystemTime::now (when the vDSO is not used)",
    },
    Syscall {
        name: "clock_nanosleep",
        x86_64: 230,
        aarch64: 115,
        reason: "timed sleeps",
    },
    Syscall {
        name: "exit_group",
        x86_64: 231,
        aarch64: 94,
        reason: "terminate the process (std::process::exit, abort paths)",
    },
    Syscall {
        name: "ppoll",
        x86_64: 271,
        aarch64: 73,
        reason: "wait for the IPC socket to become readable",
    },
    Syscall {
        name: "getrandom",
        x86_64: 318,
        aarch64: 278,
        reason: "HashMap's random seeds",
    },
];

/// The allowlisted syscall numbers for `arch`, in table order.
pub fn numbers(arch: Arch) -> Vec<u32> {
    ALLOWLIST.iter().map(|s| s.number(arch)).collect()
}

/// Whether syscall number `nr` is on the allowlist for `arch`. This is the
/// reference the harnesses compare the generated program against.
pub fn is_allowed(arch: Arch, nr: u32) -> bool {
    ALLOWLIST.iter().any(|s| s.number(arch) == nr)
}

/// Item 5.21a: the GPU process's additions to [`ALLOWLIST`] on Linux.
///
/// **Not measured.** Every entry here is reasoned from what a Vulkan driver is
/// documented or known to do, on a Mac where no Linux GPU process can run; none has
/// been checked against lavapipe or a hardware driver. Each `reason` starts "not
/// measured", and `tests/vendored.rs` checks that it does, until a Linux machine
/// measures the list (draw every scene with lavapipe and with each real driver,
/// read the pixels back, and narrow until removing any entry breaks it).
///
/// Modelling choices:
/// - **Warm up, then enter.** The GPU process loads the Vulkan loader and driver,
///   opens its device node (none for lavapipe), makes its device and compiles its
///   fixed pipelines (our shaders, never a page's) *before* installing the filter,
///   as the plan says ("the device paths opened before entering it") and as the
///   macOS GPU process does. So there is still no `open`, `openat`, `socket` or
///   `connect`: no new file, no X server, no network.
/// - **The renderer's list, plus what a driver needs at run time**: `sendmsg` and
///   `recvmsg` for passing buffer descriptors with the host (which the renderer's
///   list deliberately lacks), threads (`clone`, `clone3`, and what a new thread
///   does first), and `ioctl` for a hardware driver's commands.
/// - **No argument filtering**, as for the renderer: the generator selects by
///   number only. So `ioctl` reaches every ioctl of every descriptor the process
///   holds (the plan: "`ioctl` argument filtering is stated per driver or stated
///   as absent": it is absent); `clone` and `clone3` can make a process as well as
///   a thread, which then runs under the same filter; and `mmap` and `mprotect` can
///   make executable memory, which lavapipe needs for its compiled shaders (ours).
/// - **Weaker than the renderer's**, by exactly these additions; the crate README
///   says so.
pub const GPU_EXTRA: &[Syscall] = &[
    Syscall {
        name: "ioctl",
        x86_64: 16,
        aarch64: 29,
        reason: "not measured: a hardware driver's commands on its device node (DRM); \
                 no argument filtering",
    },
    Syscall {
        name: "getpid",
        x86_64: 39,
        aarch64: 172,
        reason: "not measured: drivers and the Vulkan loader read their own process id",
    },
    Syscall {
        name: "sendmsg",
        x86_64: 46,
        aarch64: 211,
        reason: "not measured: send buffer descriptors to the host (SCM_RIGHTS)",
    },
    Syscall {
        name: "recvmsg",
        x86_64: 47,
        aarch64: 212,
        reason: "not measured: receive buffer descriptors from the host (SCM_RIGHTS)",
    },
    Syscall {
        name: "clone",
        x86_64: 56,
        aarch64: 220,
        reason: "not measured: lavapipe's and drivers' worker threads (older libc); \
                 no argument filtering",
    },
    Syscall {
        name: "sched_getaffinity",
        x86_64: 204,
        aarch64: 123,
        reason: "not measured: lavapipe sizes its thread pool from the usable CPUs",
    },
    Syscall {
        name: "set_robust_list",
        x86_64: 273,
        aarch64: 99,
        reason: "not measured: the C library registers each new thread's robust futexes",
    },
    Syscall {
        name: "rseq",
        x86_64: 334,
        aarch64: 293,
        reason: "not measured: the C library registers each new thread's restartable \
                 sequences",
    },
    Syscall {
        name: "clone3",
        x86_64: 435,
        aarch64: 435,
        reason: "not measured: worker threads (newer libc tries clone3 first); no \
                 argument filtering",
    },
];

/// The GPU process's allowlisted numbers for `arch`: [`ALLOWLIST`] then
/// [`GPU_EXTRA`], in table order.
pub fn gpu_numbers(arch: Arch) -> Vec<u32> {
    ALLOWLIST
        .iter()
        .chain(GPU_EXTRA)
        .map(|s| s.number(arch))
        .collect()
}

/// Whether syscall number `nr` is on the GPU process's allowlist for `arch`.
pub fn is_gpu_allowed(arch: Arch, nr: u32) -> bool {
    is_allowed(arch, nr) || GPU_EXTRA.iter().any(|s| s.number(arch) == nr)
}
