//! The namespace set.
//!
//! Source: `include/uapi/linux/sched.h` (Linux v6.12, vendored under
//! `vendor/linux/`), the `CLONE_NEW*` flags. The set is the one item 2.14
//! names: user, mount, PID, network and IPC. The user namespace comes first
//! because an unprivileged process needs it to be allowed the others; the
//! applier (item 2.15) unshares them and then, in the new mount namespace,
//! pivots to an empty root. Applying them is not done here.
//!
//! Not in the set, by choice: UTS (nothing in a renderer reads or writes the
//! hostname, and the seccomp program excludes `sethostname`), cgroup and
//! time.

/// A namespace to unshare.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Namespace {
    /// `CLONE_NEWUSER`.
    User,
    /// `CLONE_NEWNS`.
    Mount,
    /// `CLONE_NEWPID`.
    Pid,
    /// `CLONE_NEWNET`: with no interface but a down loopback, no network.
    Net,
    /// `CLONE_NEWIPC`.
    Ipc,
}

/// The renderer's namespaces, in the order they are unshared.
pub const RENDERER: [Namespace; 5] = [
    Namespace::User,
    Namespace::Mount,
    Namespace::Pid,
    Namespace::Net,
    Namespace::Ipc,
];

/// The GPU process's namespaces on Linux (phase-5.md item 5.21a), in the order
/// they are unshared: the renderer's without the PID namespace. A process that
/// has unshared its PID namespace can create no more threads (the kernel
/// refuses `clone` with `CLONE_THREAD` once `pid_ns_for_children` differs from
/// the caller's own, `kernel/fork.c`, `copy_process`), and a Vulkan driver
/// starts its worker threads after this point. What the PID namespace gave the
/// renderer (no other process's id means anything) is covered for the GPU
/// process by its seccomp list having no call that takes a process id.
pub const GPU: [Namespace; 4] = [
    Namespace::User,
    Namespace::Mount,
    Namespace::Net,
    Namespace::Ipc,
];

/// `CLONE_NEWNS`.
pub const CLONE_NEWNS: u32 = 0x0002_0000;
/// `CLONE_NEWIPC`.
pub const CLONE_NEWIPC: u32 = 0x0800_0000;
/// `CLONE_NEWUSER`.
pub const CLONE_NEWUSER: u32 = 0x1000_0000;
/// `CLONE_NEWPID`.
pub const CLONE_NEWPID: u32 = 0x2000_0000;
/// `CLONE_NEWNET`.
pub const CLONE_NEWNET: u32 = 0x4000_0000;

impl Namespace {
    /// The `CLONE_NEW*` flag for `unshare(2)`.
    pub const fn clone_flag(self) -> u32 {
        match self {
            Namespace::User => CLONE_NEWUSER,
            Namespace::Mount => CLONE_NEWNS,
            Namespace::Pid => CLONE_NEWPID,
            Namespace::Net => CLONE_NEWNET,
            Namespace::Ipc => CLONE_NEWIPC,
        }
    }
}

/// All the flags of [`GPU`], for a single `unshare` call.
pub fn gpu_unshare_flags() -> u32 {
    GPU.iter().fold(0, |acc, n| acc | n.clone_flag())
}

/// All the flags of [`RENDERER`], for a single `unshare` call.
pub fn renderer_unshare_flags() -> u32 {
    RENDERER.iter().fold(0, |acc, n| acc | n.clone_flag())
}
