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

/// Item 5.21a: the GPU process's additions to [`ALLOWLIST`] on Linux, for a
/// software driver (lavapipe), which has no device.
///
/// **Measured on one configuration**: `clazel-gpu` on lavapipe (Mesa 25.2.8, LLVM
/// 20.1.2) with glibc 2.39 on aarch64 Linux (Ubuntu 24.04 in a container), under
/// `strace -f`, over the 14 GPU processes that `clazel`'s `tests/browse_gpu.rs`
/// starts (hand-built lists, real pages at several viewports, scrolls, a
/// navigation). The calls made after the filter was installed were exactly
/// `futex`, `mmap`, `write`, `mprotect`, `rt_sigprocmask`, `read`, `munmap`,
/// `sigaltstack`, `brk`, `gettid` (all the renderer's) and the five below; each
/// `reason` says who made it. The list was narrowed to those: the plan's other
/// candidates (`getpid`, `sendmsg`, `recvmsg`, `clone`) were not called and are
/// not allowed. **Not measured**: x86-64, another Mesa or C library, a process
/// running for long or under memory pressure.
///
/// Modelling choices:
/// - **Warm up, then enter.** The GPU process loads the Vulkan loader and driver,
///   makes its device and its fixed pipeline, and draws one frame of its own
///   *before* installing the filter (`clazel_gpu::sandbox`), as the plan says
///   ("the device paths opened before entering it") and as the macOS GPU process
///   does. So lavapipe has started its worker threads and compiled our shaders
///   by then: no executable mapping was made after the filter in the
///   measurement. There is no `open`, `openat`, `socket` or `connect`: no new
///   file, no X server, no network.
/// - **Every thread at once.** The driver's workers exist when the filter is
///   installed, so it is installed with `SECCOMP_FILTER_FLAG_TSYNC`
///   (`clazel_sys::linux::seccomp_set_mode_filter_all_threads`); a filter on the
///   calling thread alone would leave them unfiltered.
/// - **No descriptor passing.** Pixels leave the GPU process as bytes on a pipe
///   (`clazel_gpu::channel`), so `sendmsg` and `recvmsg`, which the plan lists
///   for passing buffer descriptors, are not needed and not allowed. They return
///   with the `memfd` route.
/// - **No argument filtering**, as for the renderer: the generator selects by
///   number only. So `clone3` can make a process as well as a thread, which then
///   runs under the same filter, and `mmap` and `mprotect` (the renderer's) can
///   make executable memory.
/// - **Weaker than the renderer's**, by exactly these additions; the crate README
///   says so.
pub const GPU_EXTRA: &[Syscall] = &[
    Syscall {
        name: "ftruncate",
        x86_64: 77,
        aarch64: 46,
        reason: "measured: lavapipe grows the memory file behind its device memory \
                 when a target or buffer is allocated (a descriptor it already holds)",
    },
    Syscall {
        name: "sched_getaffinity",
        x86_64: 204,
        aarch64: 123,
        reason: "measured: called once on each new thread of the GPU process's own \
                 (its two readers), by the C library's thread start",
    },
    Syscall {
        name: "set_robust_list",
        x86_64: 273,
        aarch64: 99,
        reason: "measured: the C library registers each new thread's robust futexes",
    },
    Syscall {
        name: "rseq",
        x86_64: 334,
        aarch64: 293,
        reason: "measured: the C library registers each new thread's restartable \
                 sequences",
    },
    Syscall {
        name: "clone3",
        x86_64: 435,
        aarch64: 435,
        reason: "measured: the GPU process's two reader threads (`clazel_gpu::process`), \
                 started after the filter; no argument filtering",
    },
];

/// Item 5.21a: what a hardware driver's GPU process is allowed on top of
/// [`GPU_EXTRA`].
///
/// **Not measured.** No hardware Vulkan driver has run in this sandbox; the one
/// entry is reasoned from what a DRM driver is known to do, and its `reason`
/// starts "not measured", which `tests/vendored.rs` checks. A driver that needs
/// another call is killed, and the crash policy (item 5.17c) counts that as a
/// refusal; the list is never widened at run time.
pub const GPU_HARDWARE_EXTRA: &[Syscall] = &[Syscall {
    name: "ioctl",
    x86_64: 16,
    aarch64: 29,
    reason: "not measured: a hardware driver's commands on its device node (DRM); \
             no argument filtering, so every ioctl of every descriptor the process holds",
}];

/// The GPU process's allowlisted numbers for `arch` on a software driver:
/// [`ALLOWLIST`] then [`GPU_EXTRA`], in table order.
pub fn gpu_numbers(arch: Arch) -> Vec<u32> {
    ALLOWLIST
        .iter()
        .chain(GPU_EXTRA)
        .map(|s| s.number(arch))
        .collect()
}

/// The GPU process's allowlisted numbers for `arch` on a hardware driver:
/// [`gpu_numbers`] then [`GPU_HARDWARE_EXTRA`].
pub fn gpu_hardware_numbers(arch: Arch) -> Vec<u32> {
    ALLOWLIST
        .iter()
        .chain(GPU_EXTRA)
        .chain(GPU_HARDWARE_EXTRA)
        .map(|s| s.number(arch))
        .collect()
}

/// Whether syscall number `nr` is on the GPU process's allowlist for `arch` on a
/// software driver.
pub fn is_gpu_allowed(arch: Arch, nr: u32) -> bool {
    is_allowed(arch, nr) || GPU_EXTRA.iter().any(|s| s.number(arch) == nr)
}

/// Whether syscall number `nr` is on the GPU process's allowlist for `arch` on a
/// hardware driver.
pub fn is_gpu_hardware_allowed(arch: Arch, nr: u32) -> bool {
    is_gpu_allowed(arch, nr) || GPU_HARDWARE_EXTRA.iter().any(|s| s.number(arch) == nr)
}
