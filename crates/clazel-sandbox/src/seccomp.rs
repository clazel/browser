//! The seccomp-BPF program generator.
//!
//! Sources (Linux v6.12, vendored under `vendor/linux/`):
//! - `Documentation/userspace-api/seccomp_filter.rst`, "Usage" (the program
//!   runs over `struct seccomp_data`), "Return values" (precedence of
//!   actions) and "Pitfalls" ("Always check the arch value!").
//! - `include/uapi/linux/seccomp.h`: `struct seccomp_data`, `SECCOMP_RET_*`.
//! - `include/uapi/linux/audit.h`: `AUDIT_ARCH_*` (see [`crate::syscalls`]).
//!
//! The program has this shape, for allowlist numbers `n_0 .. n_{N-1}`:
//!
//! ```text
//!  0        ld   [arch]                     ; seccomp_data.arch
//!  1        jeq  AUDIT_ARCH, +1, +0         ; right architecture: skip the kill
//!  2        ret  SECCOMP_RET_KILL_PROCESS   ; wrong architecture
//!  3        ld   [nr]                       ; seccomp_data.nr
//!  4+i      jeq  n_i, (N - i), +0           ; allowed: jump to the final ret
//!  4+N      ret  SECCOMP_RET_KILL_PROCESS   ; not on the list
//!  5+N      ret  SECCOMP_RET_ALLOW
//! ```
//!
//! Modelling choices:
//! - The architecture is checked first, before the syscall number is read
//!   (`seccomp_filter.rst`, "Pitfalls"). Because syscall numbers are
//!   compared for equality over the full 32 bits, an x32 call (number with
//!   bit 30 set) matches nothing on the list and is killed.
//! - Everything not allowed is `SECCOMP_RET_KILL_PROCESS` (the highest
//!   precedence action, so no later filter can soften it) rather than an
//!   errno: a renderer that attempts a forbidden call is compromised or
//!   broken, and should not continue.

use crate::bpf::SockFilter;
use crate::bpf::{BPF_ABS, BPF_JEQ, BPF_JMP, BPF_K, BPF_LD, BPF_MAXINSNS, BPF_RET, BPF_W};
use crate::syscalls::{self, Arch};

/// `SECCOMP_RET_KILL_PROCESS` (`seccomp.h`).
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
/// `SECCOMP_RET_KILL_THREAD` (`seccomp.h`).
pub const SECCOMP_RET_KILL_THREAD: u32 = 0x0000_0000;
/// `SECCOMP_RET_TRAP` (`seccomp.h`).
pub const SECCOMP_RET_TRAP: u32 = 0x0003_0000;
/// `SECCOMP_RET_ERRNO` (`seccomp.h`).
pub const SECCOMP_RET_ERRNO: u32 = 0x0005_0000;
/// `SECCOMP_RET_USER_NOTIF` (`seccomp.h`).
pub const SECCOMP_RET_USER_NOTIF: u32 = 0x7fc0_0000;
/// `SECCOMP_RET_TRACE` (`seccomp.h`).
pub const SECCOMP_RET_TRACE: u32 = 0x7ff0_0000;
/// `SECCOMP_RET_LOG` (`seccomp.h`).
pub const SECCOMP_RET_LOG: u32 = 0x7ffc_0000;
/// `SECCOMP_RET_ALLOW` (`seccomp.h`).
pub const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;
/// `SECCOMP_RET_ACTION_FULL` (`seccomp.h`): the bits that select the action.
pub const SECCOMP_RET_ACTION_FULL: u32 = 0xffff_0000;

/// Byte offset of `seccomp_data.nr` (`struct seccomp_data`, `seccomp.h`).
pub const OFFSET_NR: u32 = 0;
/// Byte offset of `seccomp_data.arch`.
pub const OFFSET_ARCH: u32 = 4;
/// `sizeof(struct seccomp_data)`: `int nr; __u32 arch; __u64 ip; __u64 args[6]`.
pub const SECCOMP_DATA_LEN: u32 = 64;

/// Why a program could not be generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenError {
    /// A conditional jump offset is 8 bits, so at most 255 syscall numbers
    /// fit in this straight-line layout.
    TooManySyscalls,
}

/// Number of instructions in the program for `n` allowlisted numbers.
pub fn program_len(n: usize) -> Result<usize, GenError> {
    // The jump from entry `i` to the final `ret ALLOW` is `n - i` <= n.
    if n > usize::from(u8::MAX) {
        return Err(GenError::TooManySyscalls);
    }
    n.checked_add(6).ok_or(GenError::TooManySyscalls)
}

/// Instruction `i` of the program for `numbers` (the layout in the module
/// documentation), or `None` past its end or if `numbers` is too long.
///
/// The program is defined pointwise so that the Kani harnesses can build it
/// in a fixed-size array without going through `Vec`; [`generate`] is this
/// function collected.
pub fn insn_at(audit_arch: u32, numbers: &[u32], i: usize) -> Option<SockFilter> {
    let n = numbers.len();
    program_len(n).ok()?;
    let ld_w_abs = BPF_LD | BPF_W | BPF_ABS;
    let jeq_k = BPF_JMP | BPF_JEQ | BPF_K;
    let ret_k = BPF_RET | BPF_K;
    match i {
        // 0-2: the architecture check comes first.
        0 => Some(SockFilter::stmt(ld_w_abs, OFFSET_ARCH)),
        1 => Some(SockFilter::jump(jeq_k, audit_arch, 1, 0)),
        2 => Some(SockFilter::stmt(ret_k, SECCOMP_RET_KILL_PROCESS)),
        // 3: then the syscall number.
        3 => Some(SockFilter::stmt(ld_w_abs, OFFSET_NR)),
        _ => {
            // 4+j: one comparison per allowed number.
            let j = i.checked_sub(4)?;
            if let Some(nr) = numbers.get(j) {
                let to_allow = u8::try_from(n.checked_sub(j)?).ok()?;
                Some(SockFilter::jump(jeq_k, *nr, to_allow, 0))
            } else if j == n {
                Some(SockFilter::stmt(ret_k, SECCOMP_RET_KILL_PROCESS))
            } else if j == n.checked_add(1)? {
                Some(SockFilter::stmt(ret_k, SECCOMP_RET_ALLOW))
            } else {
                None
            }
        }
    }
}

/// Generate the program that allows exactly the syscalls `numbers` when
/// `seccomp_data.arch` is `audit_arch`, and kills the process otherwise.
pub fn generate(audit_arch: u32, numbers: &[u32]) -> Result<Vec<SockFilter>, GenError> {
    let len = program_len(numbers.len())?;
    debug_assert!(len <= BPF_MAXINSNS);
    (0..len)
        .map(|i| insn_at(audit_arch, numbers, i))
        .collect::<Option<Vec<_>>>()
        .ok_or(GenError::TooManySyscalls)
}

/// The renderer's seccomp program for `arch`, from [`syscalls::ALLOWLIST`].
pub fn renderer_program(arch: Arch) -> Result<Vec<SockFilter>, GenError> {
    generate(arch.audit_arch(), &syscalls::numbers(arch))
}

/// The GPU process's seccomp program for `arch` on a software driver (item
/// 5.21a), from [`syscalls::gpu_numbers`]: the same layout, over the renderer's
/// list and [`syscalls::GPU_EXTRA`], measured on one configuration (see
/// `GPU_EXTRA`).
pub fn gpu_program(arch: Arch) -> Result<Vec<SockFilter>, GenError> {
    generate(arch.audit_arch(), &syscalls::gpu_numbers(arch))
}

/// The GPU process's seccomp program for `arch` on a hardware driver, from
/// [`syscalls::gpu_hardware_numbers`]: [`gpu_program`]'s list and
/// [`syscalls::GPU_HARDWARE_EXTRA`]. **Not measured** (see `GPU_HARDWARE_EXTRA`).
pub fn gpu_hardware_program(arch: Arch) -> Result<Vec<SockFilter>, GenError> {
    generate(arch.audit_arch(), &syscalls::gpu_hardware_numbers(arch))
}
