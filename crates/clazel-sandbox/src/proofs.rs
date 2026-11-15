//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! What they establish, with the interpreter in [`crate::interp`] as the model
//! of the kernel:
//!
//! - [`insn_at`] (the generator, defined pointwise) never panics, and the
//!   program it describes validates, for any architecture value and any
//!   allowlist of 0 to 3 symbolic numbers ([`list_0`] to [`list_3`]); the
//!   program for 255 numbers validates and 256 is refused ([`limits`]).
//! - For each such allowlist, any syscall number, architecture and
//!   arguments: the program returns `SECCOMP_RET_ALLOW` exactly when the
//!   architecture matches and the number is in the list, and
//!   `SECCOMP_RET_KILL_PROCESS` otherwise.
//! - For the real allowlist, on x86-64 and on aarch64: the same, for **every**
//!   32-bit syscall number (so, in particular, every number below 1024) with
//!   the right architecture, and for every other architecture value (so, in
//!   particular, the other supported architecture).
//! - For the GPU process's program (item 5.21a: the renderer's list and
//!   `GPU_EXTRA`, 37 instructions), on x86-64 and on aarch64: every other
//!   architecture value is killed, whatever the syscall number. That the program
//!   allows exactly its list for every 32-bit number under the right architecture
//!   is **not** proven: a harness for it exceeded the machine's 8 GB cap during
//!   symbolic execution (4.4 million steps), so it was removed. `tests/policies.rs`
//!   sweeps every number below 1024 on both architectures instead. Neither says
//!   whether the list is right, which is not measured.
//! - The validator and interpreter never panic, on any program of up to two
//!   instructions with any field values, over any data.
//!
//! Not proven here: the `Vec` plumbing of [`generate`] (it collects
//! `insn_at`; `tests/policies.rs` checks the collected program equals the one
//! the harnesses use). The harnesses build programs in fixed-size arrays
//! because modelling `Vec` growth made CBMC run out of memory.

use crate::bpf::SockFilter;
use crate::interp::{SeccompData, run, validate};
use crate::seccomp::{GenError, SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, insn_at, program_len};
use crate::syscalls::{self, ALLOWLIST, Arch, GPU_EXTRA};

const FILLER: SockFilter = SockFilter::stmt(0, 0);

/// The program for `numbers` as a fixed array of `N = numbers.len() + 6`.
fn build<const N: usize>(audit_arch: u32, numbers: &[u32]) -> [SockFilter; N] {
    core::array::from_fn(|i| insn_at(audit_arch, numbers, i).unwrap_or(FILLER))
}

/// For symbolic `L` numbers: the program is complete, valid, and allows
/// exactly the list under exactly the right architecture.
fn check_list<const L: usize, const N: usize>() {
    let arch: u32 = kani::any();
    let nums: [u32; L] = kani::any();
    assert!(program_len(L) == Ok(N));
    let mut i = 0;
    while i < N {
        assert!(insn_at(arch, &nums, i).is_some());
        i += 1;
    }
    assert!(insn_at(arch, &nums, N).is_none());
    let prog: [SockFilter; N] = build(arch, &nums);
    assert!(validate(&prog).is_ok());
    let data = SeccompData {
        nr: kani::any(),
        arch: kani::any(),
        instruction_pointer: kani::any(),
        args: kani::any(),
    };
    let expected = if data.arch == arch && nums.contains(&data.nr) {
        SECCOMP_RET_ALLOW
    } else {
        SECCOMP_RET_KILL_PROCESS
    };
    assert!(run(&prog, &data) == Ok(expected));
}

#[kani::proof]
#[kani::unwind(12)]
fn list_0() {
    check_list::<0, 6>();
}

#[kani::proof]
#[kani::unwind(12)]
fn list_1() {
    check_list::<1, 7>();
}

#[kani::proof]
#[kani::unwind(12)]
fn list_2() {
    check_list::<2, 8>();
}

#[kani::proof]
#[kani::unwind(12)]
fn list_3() {
    check_list::<3, 9>();
}

#[kani::proof]
fn limits() {
    assert!(program_len(255) == Ok(261));
    assert!(program_len(256) == Err(GenError::TooManySyscalls));
    let big = [0u32; 256];
    assert!(insn_at(0, &big, 0).is_none());
    // The largest accepted list: every instruction exists, the one after the
    // last does not, and every conditional jump stays inside the program.
    let max = [0u32; 255];
    let i: usize = kani::any();
    kani::assume(i <= 261);
    match insn_at(0, &max, i) {
        Some(insn) => {
            assert!(i < 261);
            if insn.code & 0x07 == crate::bpf::BPF_JMP {
                assert!(i + 1 + usize::from(insn.jt) < 261);
                assert!(i + 1 + usize::from(insn.jf) < 261);
            }
        }
        None => assert!(i == 261),
    }
}

const REAL: usize = 22;

/// The real allowlist for `arch`: every syscall number, right architecture.
fn check_real_allowlist(arch: Arch) {
    assert!(ALLOWLIST.len() == REAL);
    let nums: [u32; REAL] =
        core::array::from_fn(|i| ALLOWLIST.get(i).map_or(0, |s| s.number(arch)));
    let prog: [SockFilter; 28] = build(arch.audit_arch(), &nums);
    assert!(validate(&prog).is_ok());
    let nr: u32 = kani::any();
    let got = run(&prog, &SeccompData::new(nr, arch.audit_arch()));
    if syscalls::is_allowed(arch, nr) {
        assert!(got == Ok(SECCOMP_RET_ALLOW));
    } else {
        assert!(got == Ok(SECCOMP_RET_KILL_PROCESS));
    }
    // Any other architecture value, whatever the syscall number.
    let other: u32 = kani::any();
    kani::assume(other != arch.audit_arch());
    assert!(run(&prog, &SeccompData::new(nr, other)) == Ok(SECCOMP_RET_KILL_PROCESS));
}

#[kani::proof]
#[kani::unwind(40)]
fn real_allowlist_x86_64() {
    check_real_allowlist(Arch::X86_64);
}

#[kani::proof]
#[kani::unwind(40)]
fn real_allowlist_aarch64() {
    check_real_allowlist(Arch::Aarch64);
}

const GPU: usize = 31;

/// The GPU process's list for `arch` as an array: the renderer's, then
/// `GPU_EXTRA`.
fn gpu_nums(arch: Arch) -> [u32; GPU] {
    core::array::from_fn(|i| {
        ALLOWLIST
            .get(i)
            .or_else(|| i.checked_sub(REAL).and_then(|j| GPU_EXTRA.get(j)))
            .map_or(0, |s| s.number(arch))
    })
}

/// The GPU process's program for `arch` kills every other architecture value,
/// whatever the syscall number.
fn check_gpu_other_arch(arch: Arch) {
    let nums = gpu_nums(arch);
    let prog: [SockFilter; 37] = build(arch.audit_arch(), &nums);
    let nr: u32 = kani::any();
    let other: u32 = kani::any();
    kani::assume(other != arch.audit_arch());
    assert!(run(&prog, &SeccompData::new(nr, other)) == Ok(SECCOMP_RET_KILL_PROCESS));
}

#[kani::proof]
#[kani::unwind(45)]
fn gpu_other_arch_x86_64() {
    check_gpu_other_arch(Arch::X86_64);
}

#[kani::proof]
#[kani::unwind(45)]
fn gpu_other_arch_aarch64() {
    check_gpu_other_arch(Arch::Aarch64);
}

#[kani::proof]
#[kani::unwind(6)]
fn interpreter_never_panics() {
    let insns: [SockFilter; 2] = [
        SockFilter {
            code: kani::any(),
            jt: kani::any(),
            jf: kani::any(),
            k: kani::any(),
        },
        SockFilter {
            code: kani::any(),
            jt: kani::any(),
            jf: kani::any(),
            k: kani::any(),
        },
    ];
    let len: usize = kani::any();
    kani::assume(len <= 2);
    let prog = insns.get(..len).unwrap_or(&[]);
    let data = SeccompData {
        nr: kani::any(),
        arch: kani::any(),
        instruction_pointer: kani::any(),
        args: kani::any(),
    };
    let _ = validate(prog);
    let _ = run(prog, &data);
}
