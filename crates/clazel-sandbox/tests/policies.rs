//! Behaviour of the generated policies. The exhaustive run over every
//! syscall number below 1024 is repeated here as a plain test (the Kani
//! harnesses in `src/proofs.rs` prove it for all 2^32 numbers).

use clazel_sandbox::bpf::{
    BPF_ABS, BPF_ALU, BPF_DIV, BPF_JMP, BPF_K, BPF_LD, BPF_RET, BPF_W, SockFilter,
};
use clazel_sandbox::interp::{BpfError, SeccompData, run, validate};
use clazel_sandbox::seccomp::{
    GenError, SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, generate, renderer_program,
};
use clazel_sandbox::syscalls::{self, AUDIT_ARCH_AARCH64, AUDIT_ARCH_X86_64, Arch};
use clazel_sandbox::{landlock, namespaces, seatbelt};

/// Every syscall number normally; under Miri, every seventeenth (Miri runs
/// the interpreter slowly, and Kani covers all numbers anyway).
fn miri_step() -> usize {
    if cfg!(miri) { 17 } else { 1 }
}

#[test]
fn programs_allow_exactly_the_allowlist_below_1024() -> Result<(), String> {
    for arch in Arch::ALL {
        let prog = renderer_program(arch).map_err(|e| format!("{e:?}"))?;
        validate(&prog).map_err(|e| format!("{e:?}"))?;
        for nr in (0..1024u32).step_by(miri_step()) {
            let got = run(&prog, &SeccompData::new(nr, arch.audit_arch()));
            let want = if syscalls::is_allowed(arch, nr) {
                SECCOMP_RET_ALLOW
            } else {
                SECCOMP_RET_KILL_PROCESS
            };
            assert_eq!(got, Ok(want), "{arch:?} syscall {nr}");
        }
    }
    Ok(())
}

#[test]
fn wrong_architecture_is_killed_for_every_number() -> Result<(), String> {
    let wrong = [
        0,
        1,
        0x4000_003e,         // x86-64 without __AUDIT_ARCH_64BIT
        0xc000_003e ^ 1,     // one bit off
        0xc000_00b7 ^ 0x100, // one bit off
        u32::MAX,
        // The other supported architecture, and 32-bit x86 (EM_386 = 3, LE).
        AUDIT_ARCH_AARCH64,
        AUDIT_ARCH_X86_64,
        0x4000_0003,
    ];
    for arch in Arch::ALL {
        let prog = renderer_program(arch).map_err(|e| format!("{e:?}"))?;
        for other in wrong.iter().filter(|a| **a != arch.audit_arch()) {
            for nr in (0..1024u32).step_by(miri_step()) {
                let got = run(&prog, &SeccompData::new(nr, *other));
                assert_eq!(
                    got,
                    Ok(SECCOMP_RET_KILL_PROCESS),
                    "{arch:?} arch {other:#x} nr {nr}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn x86_64_x32_numbers_are_killed() -> Result<(), String> {
    // x32 calls arrive with arch X86_64 and bit 30 set in the number.
    let prog = renderer_program(Arch::X86_64).map_err(|e| format!("{e:?}"))?;
    for s in syscalls::ALLOWLIST {
        let nr = s.x86_64 | 0x4000_0000;
        let got = run(&prog, &SeccompData::new(nr, AUDIT_ARCH_X86_64));
        assert_eq!(got, Ok(SECCOMP_RET_KILL_PROCESS), "{}", s.name);
    }
    Ok(())
}

#[test]
fn architecture_is_checked_first() -> Result<(), String> {
    for arch in Arch::ALL {
        let prog = renderer_program(arch).map_err(|e| format!("{e:?}"))?;
        let first = prog.first().ok_or("empty program")?;
        assert_eq!(first.code, BPF_LD | BPF_W | BPF_ABS);
        assert_eq!(first.k, 4, "first instruction must load seccomp_data.arch");
        let second = prog.get(1).ok_or("short program")?;
        assert_eq!(second.code, BPF_JMP | clazel_sandbox::bpf::BPF_JEQ | BPF_K);
        assert_eq!(second.k, arch.audit_arch());
        // The instruction after the comparison kills.
        let third = prog.get(2).ok_or("short program")?;
        assert_eq!(third.code, BPF_RET | BPF_K);
        assert_eq!(third.k, SECCOMP_RET_KILL_PROCESS);
    }
    Ok(())
}

#[test]
fn generator_edges() -> Result<(), String> {
    // Empty list: nothing allowed.
    let p = generate(7, &[]).map_err(|e| format!("{e:?}"))?;
    assert_eq!(p.len(), 6);
    validate(&p).map_err(|e| format!("{e:?}"))?;
    assert_eq!(
        run(&p, &SeccompData::new(0, 7)),
        Ok(SECCOMP_RET_KILL_PROCESS)
    );
    // 255 numbers fit; 256 do not.
    let nums: Vec<u32> = (0..255).collect();
    let p = generate(7, &nums).map_err(|e| format!("{e:?}"))?;
    validate(&p).map_err(|e| format!("{e:?}"))?;
    assert_eq!(run(&p, &SeccompData::new(0, 7)), Ok(SECCOMP_RET_ALLOW));
    assert_eq!(run(&p, &SeccompData::new(254, 7)), Ok(SECCOMP_RET_ALLOW));
    assert_eq!(
        run(&p, &SeccompData::new(255, 7)),
        Ok(SECCOMP_RET_KILL_PROCESS)
    );
    let nums: Vec<u32> = (0..256).collect();
    assert_eq!(generate(7, &nums), Err(GenError::TooManySyscalls));
    Ok(())
}

#[test]
fn validator_rejects_what_the_kernel_would() {
    let ret0 = SockFilter::stmt(BPF_RET | BPF_K, 0);
    assert_eq!(validate(&[]), Err(BpfError::BadLength));
    assert_eq!(validate(&vec![ret0; 4097]), Err(BpfError::BadLength));
    assert_eq!(
        validate(&[SockFilter::stmt(0xffff, 0)]),
        Err(BpfError::BadOpcode)
    );
    // Unaligned and out-of-range absolute loads.
    for k in [1, 2, 3, 5, 64, 68, u32::MAX] {
        let ld = SockFilter::stmt(BPF_LD | BPF_W | BPF_ABS, k);
        assert_eq!(validate(&[ld, ret0]), Err(BpfError::BadLoad), "k = {k}");
    }
    // Half-word load.
    let ldh = SockFilter::stmt(BPF_LD | clazel_sandbox::bpf::BPF_H | BPF_ABS, 0);
    assert_eq!(validate(&[ldh, ret0]), Err(BpfError::BadOpcode));
    // Jump past the end; fall off the end.
    let jmp = SockFilter::jump(BPF_JMP | clazel_sandbox::bpf::BPF_JEQ | BPF_K, 0, 2, 0);
    assert_eq!(validate(&[jmp, ret0]), Err(BpfError::BadJump));
    let ld = SockFilter::stmt(BPF_LD | BPF_W | BPF_ABS, 0);
    assert_eq!(validate(&[ret0, ld]), Err(BpfError::NoReturn));
    // Constant division by zero.
    let div0 = SockFilter::stmt(BPF_ALU | BPF_DIV | BPF_K, 0);
    assert_eq!(validate(&[div0, ret0]), Err(BpfError::BadArithmetic));
}

#[test]
fn interpreter_semantics() -> Result<(), String> {
    use clazel_sandbox::bpf::*;
    let data = SeccompData {
        nr: 5,
        arch: 9,
        instruction_pointer: 0x1111_2222_3333_4444,
        args: [0xaaaa_bbbb_cccc_dddd, 0, 0, 0, 0, 7],
    };
    let ld = |k| SockFilter::stmt(BPF_LD | BPF_W | BPF_ABS, k);
    let ret_a = SockFilter::stmt(BPF_RET | BPF_A, 0);
    // The data layout: nr, arch, ip (low, high), args (low, high).
    for (off, want) in [
        (0, 5),
        (4, 9),
        (8, 0x3333_4444),
        (12, 0x1111_2222),
        (16, 0xcccc_dddd),
        (20, 0xaaaa_bbbb),
        (56, 7),
        (60, 0),
    ] {
        assert_eq!(run(&[ld(off), ret_a], &data), Ok(want), "offset {off}");
    }
    // ld #7; add #3; mul #2; st M[1]; ldx M[1]; sub x; ret a  -> 0
    // then: ld #20; tax; ld #3; or x ... exercise TAX/TXA, ALU, scratch.
    let p = [
        SockFilter::stmt(BPF_LD | BPF_IMM, 7),
        SockFilter::stmt(BPF_ALU | BPF_ADD | BPF_K, 3),
        SockFilter::stmt(BPF_ALU | BPF_MUL | BPF_K, 2),
        SockFilter::stmt(BPF_ST, 1),
        SockFilter::stmt(BPF_LDX | BPF_MEM, 1),
        SockFilter::stmt(BPF_ALU | BPF_SUB | BPF_X, 0),
        SockFilter::stmt(BPF_RET | BPF_A, 0),
    ];
    validate(&p).map_err(|e| format!("{e:?}"))?;
    assert_eq!(run(&p, &data), Ok(0));
    let p = [
        SockFilter::stmt(BPF_LD | BPF_IMM, 20),
        SockFilter::stmt(BPF_MISC | BPF_TAX, 0),
        SockFilter::stmt(BPF_LD | BPF_LEN, 0),
        SockFilter::stmt(BPF_ALU | BPF_DIV | BPF_X, 0),
        SockFilter::stmt(BPF_MISC | BPF_TXA, 0),
        SockFilter::stmt(BPF_RET | BPF_A, 0),
    ];
    validate(&p).map_err(|e| format!("{e:?}"))?;
    assert_eq!(run(&p, &data), Ok(20));
    // Division by X = 0 faults at run time.
    let p = [
        SockFilter::stmt(BPF_LD | BPF_IMM, 20),
        SockFilter::stmt(BPF_ALU | BPF_DIV | BPF_X, 0),
        SockFilter::stmt(BPF_RET | BPF_A, 0),
    ];
    assert_eq!(run(&p, &data), Err(BpfError::BadArithmetic));
    // Conditional jumps: jgt, jge, jset with both branches.
    let jump = |op, k| {
        [
            SockFilter::stmt(BPF_LD | BPF_IMM, 8),
            SockFilter::jump(BPF_JMP | op | BPF_K, k, 1, 0),
            SockFilter::stmt(BPF_RET | BPF_K, 0),
            SockFilter::stmt(BPF_RET | BPF_K, 1),
        ]
    };
    for (op, k, taken) in [
        (BPF_JGT, 7, 1),
        (BPF_JGT, 8, 0),
        (BPF_JGE, 8, 1),
        (BPF_JGE, 9, 0),
        (BPF_JSET, 8, 1),
        (BPF_JSET, 7, 0),
        (BPF_JEQ, 8, 1),
        (BPF_JEQ, 9, 0),
    ] {
        assert_eq!(run(&jump(op, k), &data), Ok(taken), "op {op:#x} k {k}");
    }
    Ok(())
}

#[test]
fn landlock_policy_denies_everything() {
    let r = landlock::RENDERER;
    assert!(r.allows_nothing());
    assert!(r.path_rules.is_empty());
    assert_eq!(r.handled_access_fs, landlock::FS_ABI_5);
    // Every right is handled: no filesystem right is left unrestricted.
    for bit in 0..16 {
        assert_ne!(r.handled_access_fs & (1 << bit), 0, "fs bit {bit}");
    }
    // Older kernels: only the rights they know, still with no rules.
    assert_eq!(r.for_abi(0).handled_access_fs, 0);
    assert_eq!(r.for_abi(1).handled_access_fs, (1 << 13) - 1);
    assert_eq!(r.for_abi(2).handled_access_fs, (1 << 14) - 1);
    assert_eq!(r.for_abi(3).handled_access_fs, (1 << 15) - 1);
    assert_eq!(r.for_abi(4).handled_access_fs, (1 << 15) - 1);
    assert_eq!(r.for_abi(4).handled_access_net, 0b11);
    assert_eq!(r.for_abi(5).handled_access_fs, (1 << 16) - 1);
    assert_eq!(r.for_abi(5).scoped, 0);
    assert_eq!(r.for_abi(6), r);
    assert_eq!(r.for_abi(99), r);
    for abi in 0..8 {
        assert!(r.for_abi(abi).allows_nothing());
    }
}

#[test]
fn namespace_set_is_user_mount_pid_net_ipc() {
    use namespaces::Namespace::*;
    assert_eq!(namespaces::RENDERER, [User, Mount, Pid, Net, Ipc]);
    assert_eq!(namespaces::renderer_unshare_flags(), 0x7802_0000);
}

#[test]
fn seatbelt_profile_shape() {
    let p = seatbelt::renderer_profile();
    assert!(p.starts_with("(version 1)\n(deny default)\n"), "{p}");
    for rule in seatbelt::RENDERER {
        for banned in [
            "file", "network", "process", "mach", "ipc", "iokit", "system",
        ] {
            assert!(!rule.operation.contains(banned), "{}", rule.operation);
        }
        assert!(!rule.reason.is_empty());
    }
    // Balanced parentheses, every line a complete form.
    for line in p.lines() {
        assert!(line.starts_with('(') && line.ends_with(')'), "{line}");
        let open = line.matches('(').count();
        let close = line.matches(')').count();
        assert_eq!(open, close, "{line}");
    }
    assert_eq!(p.matches("(deny default)").count(), 1);
    assert!(!p.contains("(allow default)"));
}

// Item 5.21a: the GPU process's policies.

#[test]
fn gpu_programs_allow_exactly_the_gpu_list_below_1024() -> Result<(), String> {
    use clazel_sandbox::seccomp::gpu_program;
    for arch in Arch::ALL {
        let prog = gpu_program(arch).map_err(|e| format!("{e:?}"))?;
        validate(&prog).map_err(|e| format!("{e:?}"))?;
        assert_eq!(
            prog.len(),
            syscalls::ALLOWLIST.len() + syscalls::GPU_EXTRA.len() + 6
        );
        for nr in (0..1024u32).step_by(miri_step()) {
            let got = run(&prog, &SeccompData::new(nr, arch.audit_arch()));
            let want = if syscalls::is_gpu_allowed(arch, nr) {
                SECCOMP_RET_ALLOW
            } else {
                SECCOMP_RET_KILL_PROCESS
            };
            assert_eq!(got, Ok(want), "{arch:?} syscall {nr}");
            let other = match arch {
                Arch::X86_64 => AUDIT_ARCH_AARCH64,
                Arch::Aarch64 => AUDIT_ARCH_X86_64,
            };
            assert_eq!(
                run(&prog, &SeccompData::new(nr, other)),
                Ok(SECCOMP_RET_KILL_PROCESS)
            );
        }
    }
    Ok(())
}

/// The GPU list is the renderer's plus its additions: everything the renderer may
/// call, the GPU process may too, and the additions are exactly the plan's.
#[test]
fn gpu_list_is_the_renderers_plus_the_additions() {
    for arch in Arch::ALL {
        for s in syscalls::ALLOWLIST {
            assert!(syscalls::is_gpu_allowed(arch, s.number(arch)), "{}", s.name);
        }
        for s in syscalls::GPU_EXTRA {
            assert!(!syscalls::is_allowed(arch, s.number(arch)), "{}", s.name);
            assert!(syscalls::is_gpu_allowed(arch, s.number(arch)), "{}", s.name);
        }
    }
    let names: Vec<&str> = syscalls::GPU_EXTRA.iter().map(|s| s.name).collect();
    assert_eq!(
        names,
        [
            "ioctl",
            "getpid",
            "sendmsg",
            "recvmsg",
            "clone",
            "sched_getaffinity",
            "set_robust_list",
            "rseq",
            "clone3"
        ]
    );
}

/// The GPU profile is `(deny default)` and nothing else: the measured profile
/// after the warm-up (`seatbelt.rs`).
#[test]
fn gpu_seatbelt_profile_is_deny_default_alone() {
    assert!(seatbelt::GPU.is_empty());
    assert_eq!(seatbelt::gpu_profile(), "(version 1)\n(deny default)\n");
}

/// The Windows GPU policy is the renderer's less `win32k`, plus `registryRead`,
/// under its own name (the plan's measured decision).
#[test]
fn gpu_appcontainer_policy_is_the_renderers_less_win32k() {
    use clazel_sandbox::appcontainer as ac;
    let win32k = ac::MITIGATIONS
        .iter()
        .find(|m| m.name == "WIN32K_SYSTEM_CALL_DISABLE_ALWAYS_ON")
        .map(|m| m.mask);
    assert_eq!(win32k, Some(1 << 28));
    assert_eq!(
        ac::gpu_mitigation_mask(),
        ac::mitigation_mask() & !(1u64 << 28)
    );
    assert_eq!(ac::GPU_CAPABILITIES, ["registryRead"]);
    assert!(ac::CAPABILITIES.is_empty());
    assert_ne!(ac::GPU_CONTAINER_NAME, ac::CONTAINER_NAME);
    assert_eq!(ac::GPU_JOB, ac::RENDERER_JOB);
    for name in ac::GPU_WITHOUT {
        assert!(ac::MITIGATIONS.iter().any(|m| m.name == *name), "{name}");
    }
}

/// The array the Kani harnesses build for the GPU list (`proofs.rs`'s
/// `gpu_nums`: the renderer's list, then `GPU_EXTRA`) is `gpu_numbers`, and
/// `is_gpu_allowed` holds exactly for its entries.
#[test]
fn gpu_numbers_are_the_two_lists_in_order() {
    for arch in Arch::ALL {
        let want: Vec<u32> = syscalls::ALLOWLIST
            .iter()
            .chain(syscalls::GPU_EXTRA)
            .map(|s| s.number(arch))
            .collect();
        assert_eq!(syscalls::gpu_numbers(arch), want);
        assert_eq!(want.len(), 31);
        for nr in (0..1024u32).step_by(miri_step()) {
            assert_eq!(syscalls::is_gpu_allowed(arch, nr), want.contains(&nr));
        }
    }
}
