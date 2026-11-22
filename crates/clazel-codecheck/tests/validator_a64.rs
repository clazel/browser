//! Tests of the executable A64 validator: accepted programs, a hostile corpus
//! (jit.md exit criterion 6, the hand-assembled part), and a deterministic
//! mutation fuzz. The programs are the ones of `src/a64/examples.rs`, whose
//! branch offsets (in words) are worked out there.

use clazel_a64::decoder::decode_instr;
use clazel_a64::encoder::encode_instr;
use clazel_a64::spec::{Instr, MoveWideOp, ShiftType, Width};
use clazel_codecheck::a64::validate::validate;

fn bytes(ins: &[Instr]) -> Vec<u8> {
    ins.iter()
        .flat_map(|i| encode_instr(i).to_le_bytes())
        .collect()
}

fn exit_seq(t: u8, code: u16) -> Vec<Instr> {
    vec![
        Instr::MoveWide {
            sf: Width::W32,
            opcode: MoveWideOp::Z,
            d: t,
            imm16: code,
            hw: 0,
        },
        Instr::LoadStoreImm {
            sf: Width::W64,
            load: false,
            t,
            n: 28,
            imm12: 32,
        },
        Instr::Ret,
    ]
}

fn base_load(dst: u8, k: u16) -> Instr {
    Instr::LoadStoreImm {
        sf: Width::W64,
        load: true,
        t: dst,
        n: 28,
        imm12: k.wrapping_mul(2),
    }
}

fn region_load(dst: u8, base: u8, idx: u8) -> Instr {
    Instr::LoadStoreReg {
        sf: Width::W64,
        load: true,
        t: dst,
        n: base,
        m: idx,
        s: false,
    }
}

fn cmp(n: u8, m: u8) -> Instr {
    Instr::AddSubShiftedReg {
        sf: Width::W64,
        sub_op: true,
        setflags: true,
        d: 31,
        n,
        m,
        shift_type: ShiftType::Lsl,
        shift_amount: 0,
    }
}

/// The bounds check of region `k` for `n` bytes: index `x1`, scratch `x5`,
/// `x6`, the branches `r1` and `r2` words on.
fn check_seq(k: u16, n: u16, r1: i32, r2: i32) -> Vec<Instr> {
    vec![
        Instr::LoadStoreImm {
            sf: Width::W64,
            load: true,
            t: 6,
            n: 28,
            imm12: k.wrapping_mul(2).wrapping_add(1),
        },
        Instr::AddSubImm {
            sf: Width::W64,
            sub_op: false,
            setflags: true,
            d: 5,
            n: 1,
            imm12: n,
            sh: false,
        },
        Instr::BCond { cond: 2, imm19: r1 },
        cmp(5, 6),
        Instr::BCond { cond: 8, imm19: r2 },
        cmp(1, 6),
        Instr::CondSelect {
            sf: Width::W64,
            else_inv: false,
            else_inc: false,
            d: 1,
            n: 1,
            m: 31,
            cond: 3,
        },
    ]
}

fn checked_load(k: u16, n: u16) -> Vec<Instr> {
    checked_load_of(3, k, n)
}

/// The base of region `base_k`, a check of region `k` for `n` bytes, and an
/// 8-byte load.
fn checked_load_of(base_k: u16, k: u16, n: u16) -> Vec<Instr> {
    let mut p = vec![base_load(2, base_k)];
    p.extend(check_seq(k, n, 6, 4));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    p
}

fn ok(ins: &[Instr]) -> bool {
    validate(&bytes(ins), &[0])
}

fn add_rr(d: u8, n: u8, m: u8) -> Instr {
    Instr::AddSubShiftedReg {
        sf: Width::W64,
        sub_op: false,
        setflags: false,
        d,
        n,
        m,
        shift_type: ShiftType::Lsl,
        shift_amount: 0,
    }
}

#[test]
fn exit_sequence_bytes_are_accepted() {
    let blob = [
        0xE0, 0x00, 0x80, 0x52, 0x80, 0x83, 0x00, 0xF9, 0xC0, 0x03, 0x5F, 0xD6,
    ];
    assert!(validate(&blob, &[0]));
    assert_eq!(bytes(&exit_seq(0, 7)), blob);
}

#[test]
fn accepted_programs() {
    assert!(ok(&checked_load(3, 8)));
    // A second entry at the exit sequence (instruction 9, byte 36).
    assert!(validate(&bytes(&checked_load(3, 8)), &[0, 36]));
    // A loop.
    assert!(ok(&[add_rr(0, 0, 3), Instr::B { imm26: -1 }]));
    // A store to an exit operand.
    let mut p = vec![Instr::LoadStoreImm {
        sf: Width::W64,
        load: false,
        t: 0,
        n: 28,
        imm12: 33,
    }];
    p.extend(exit_seq(7, 1));
    assert!(ok(&p));
    // A compare writes the zero register, not the stack pointer.
    let mut p = vec![cmp(0, 1)];
    p.extend(exit_seq(7, 1));
    assert!(ok(&p));
    // The check must cover the 8-byte load, in each of the 16 regions; a
    // check of fewer bytes does not, and one of more than 8 is no check.
    for k in 0..16 {
        for n in 0..=9 {
            assert_eq!(
                ok(&checked_load_of(k, k, n)),
                n == 8,
                "region {k}, {n} bytes"
            );
        }
    }
    // A region outside the table is no check either.
    assert!(!ok(&checked_load_of(15, 16, 8)));
}

#[test]
fn unchecked_index_is_refused() {
    let mut p = vec![base_load(2, 3), region_load(0, 2, 1)];
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn check_for_too_few_bytes_or_the_wrong_region_is_refused() {
    assert!(!ok(&checked_load(3, 4)));
    assert!(!ok(&checked_load(2, 8)));
}

#[test]
fn a_shifted_index_is_refused() {
    let mut p = vec![base_load(2, 3)];
    p.extend(check_seq(3, 8, 6, 4));
    p.push(Instr::LoadStoreReg {
        sf: Width::W64,
        load: true,
        t: 0,
        n: 2,
        m: 1,
        s: true,
    });
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn writes_to_reserved_registers_are_refused() {
    let writes = |d: u8| -> Vec<Instr> {
        vec![
            Instr::MoveWide {
                sf: Width::W64,
                opcode: MoveWideOp::Z,
                d,
                imm16: 0,
                hw: 0,
            },
            add_rr(d, 0, 1),
            Instr::LoadStoreImm {
                sf: Width::W64,
                load: true,
                t: d,
                n: 28,
                imm12: 33,
            },
            Instr::AddSubImm {
                sf: Width::W64,
                sub_op: false,
                setflags: false,
                d,
                n: 0,
                imm12: 8,
                sh: false,
            },
        ]
    };
    for d in [28u8, 30] {
        for (n, i) in writes(d).into_iter().enumerate() {
            let mut p = vec![i];
            p.extend(exit_seq(7, 1));
            assert!(!ok(&p), "write to x{d}: form {n}");
        }
    }
    // The stack pointer: `add sp, x0, #8` and `sub sp, sp, #16`.
    for sub_op in [false, true] {
        let mut p = vec![Instr::AddSubImm {
            sf: Width::W64,
            sub_op,
            setflags: false,
            d: 31,
            n: if sub_op { 31 } else { 0 },
            imm12: 16,
            sh: false,
        }];
        p.extend(exit_seq(7, 1));
        assert!(!ok(&p), "write to sp");
    }
    // With flags, register 31 is the zero register: `cmn sp, #16`.
    let mut p = vec![Instr::AddSubImm {
        sf: Width::W64,
        sub_op: false,
        setflags: true,
        d: 31,
        n: 31,
        imm12: 16,
        sh: false,
    }];
    p.extend(exit_seq(7, 1));
    assert!(ok(&p));
}

#[test]
fn branch_into_a_bounds_check_is_refused() {
    let mut p = vec![Instr::B { imm26: 2 }];
    p.extend(check_seq(3, 8, 5, 3));
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn branch_over_a_bounds_check_to_the_access_is_refused() {
    let mut p = vec![Instr::B { imm26: 9 }, base_load(2, 3)];
    p.extend(check_seq(3, 8, 6, 4));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn context_accesses_outside_the_exit_area_are_refused() {
    let st = |imm12: u16| -> Vec<Instr> {
        let mut p = vec![Instr::LoadStoreImm {
            sf: Width::W64,
            load: false,
            t: 0,
            n: 28,
            imm12,
        }];
        p.extend(exit_seq(7, 1));
        p
    };
    assert!(!ok(&st(0)), "store to the region table");
    assert!(!ok(&st(31)), "store to the last bound");
    assert!(ok(&st(33)));
    assert!(ok(&st(63)), "last exit operand");
    assert!(!ok(&st(64)), "past the context");
    let ld = |imm12: u16| -> Vec<Instr> {
        let mut p = vec![Instr::LoadStoreImm {
            sf: Width::W64,
            load: true,
            t: 0,
            n: 28,
            imm12,
        }];
        p.extend(exit_seq(7, 1));
        p
    };
    assert!(ok(&ld(0)), "load from the table");
    assert!(ok(&ld(63)));
    assert!(!ok(&ld(64)), "load past the context");
    // A register offset on the context register.
    let mut p = vec![Instr::LoadStoreReg {
        sf: Width::W64,
        load: true,
        t: 0,
        n: 28,
        m: 1,
        s: false,
    }];
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn running_off_the_end_is_refused() {
    assert!(!ok(&[add_rr(0, 0, 3)]));
    // A conditional branch last: its fall-through leaves the blob.
    let mut p = exit_seq(7, 1);
    p.push(Instr::CompareBranch {
        sf: Width::W64,
        iszero: true,
        t: 0,
        imm19: -3,
    });
    assert!(!ok(&p));
    p.pop();
    p.push(Instr::BCond { cond: 0, imm19: -3 });
    assert!(!ok(&p));
}

#[test]
fn bare_ret_and_other_exits_are_refused() {
    assert!(!ok(&[Instr::Ret]));
    // An exit sequence that stores through the wrong operand.
    let p = vec![
        Instr::MoveWide {
            sf: Width::W32,
            opcode: MoveWideOp::Z,
            d: 7,
            imm16: 1,
            hw: 0,
        },
        Instr::LoadStoreImm {
            sf: Width::W64,
            load: false,
            t: 7,
            n: 28,
            imm12: 33,
        },
        Instr::Ret,
    ];
    assert!(!ok(&p));
}

#[test]
fn entries_and_branches_must_hit_unit_starts() {
    let blob = bytes(&checked_load(3, 8));
    assert!(!validate(&blob, &[12]), "entry inside the check");
    assert!(!validate(&blob, &[2]), "unaligned entry");
    assert!(!validate(&blob, &[blob.len()]), "entry at the end");
    assert!(!validate(&blob, &[usize::MAX]), "entry out of range");
    assert!(!ok(&[Instr::B { imm26: 100 }]), "branch out");
    assert!(!ok(&[Instr::B { imm26: -100 }]), "branch before the start");
    assert!(!ok(&[Instr::B { imm26: 0x01FF_FFFF }]), "farthest branch");
    assert!(
        !ok(&[Instr::B {
            imm26: -0x0200_0000
        }]),
        "farthest back"
    );
}

#[test]
fn truncated_empty_and_unaligned_blobs_are_refused() {
    assert!(!validate(&[], &[]));
    let blob = bytes(&checked_load(3, 8));
    for n in 0..blob.len() {
        assert!(
            !validate(blob.get(..n).unwrap_or(&[]), &[0]),
            "prefix of {n} bytes"
        );
    }
    let mut longer = blob.clone();
    longer.push(0);
    assert!(!validate(&longer, &[0]));
}

#[test]
fn forbidden_and_non_canonical_words_are_refused() {
    let tail = bytes(&exit_seq(7, 1));
    let cases: &[(&str, u32)] = &[
        ("nop", 0xD503_201F),
        ("svc #0", 0xD400_0001),
        ("brk #0", 0xD420_0000),
        ("br x0", 0xD61F_0000),
        ("blr x0", 0xD63F_0000),
        ("bl +0", 0x9400_0000),
        ("ret x1", 0xD65F_0020),
        ("msr nzcv, x0", 0xD51B_4200),
        ("mrs x0, nzcv", 0xD53B_4200),
        ("ldr x0, [sp]", 0xF940_03E0),
        ("ldp x0, x1, [x2]", 0xA940_0440),
        ("ldr x0, [x2, x1, sxtw]", 0xF861_C840),
        ("ldrb w0, [x2]", 0x3940_0040),
        ("ldr x0, [x2], #8", 0xF840_8440),
        ("ldr x0, [x2, #8]!", 0xF840_8C40),
        ("add x0, x1, x2, ror #1", 0x8BC2_0420),
        ("udf #0", 0x0000_0000),
        ("all ones", 0xFFFF_FFFF),
    ];
    for (name, w) in cases {
        let mut blob = w.to_le_bytes().to_vec();
        blob.extend(&tail);
        assert!(!validate(&blob, &[0]), "{name}");
    }
}

#[test]
fn encoder_and_decoder_agree_with_the_validator() {
    // Every instruction word of a valid program decodes.
    for i in checked_load(3, 8) {
        let w = encode_instr(&i);
        assert_eq!(decode_instr(w).map(|d| encode_instr(&d)), Some(w));
    }
}

/// A deterministic xorshift generator, so that the fuzz is reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: usize) -> usize {
        let m = u64::try_from(n.max(1)).unwrap_or(1);
        usize::try_from(self.next().checked_rem(m).unwrap_or(0)).unwrap_or(0)
    }
}

#[test]
fn mutation_fuzz_never_panics_and_accepts_only_canonical_blobs() {
    let seeds: Vec<Vec<u8>> = vec![
        bytes(&checked_load(3, 8)),
        bytes(&exit_seq(0, 7)),
        bytes(&[add_rr(0, 0, 3), Instr::B { imm26: -1 }]),
    ];
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut accepted = 0usize;
    for round in 0..20_000usize {
        let seed = seeds
            .get(rng.below(seeds.len()))
            .cloned()
            .unwrap_or_default();
        let mut blob = seed;
        for _ in 0..=rng.below(3) {
            let len = blob.len();
            let at = rng.below(len);
            let byte = u8::try_from(rng.next() & 0xFF).unwrap_or(0);
            match rng.below(4) {
                0 => {
                    if let Some(b) = blob.get_mut(at) {
                        *b ^= byte | 1;
                    }
                }
                1 => {
                    if let Some(b) = blob.get_mut(at) {
                        *b = byte;
                    }
                }
                2 => {
                    blob.truncate(at);
                }
                _ => {
                    blob.insert(at.min(blob.len()), byte);
                }
            }
        }
        let entries: Vec<usize> = match round % 3 {
            0 => vec![0],
            1 => vec![0, rng.below(blob.len() + 8)],
            _ => vec![],
        };
        if validate(&blob, &entries) {
            accepted += 1;
            // An accepted blob is whole words, each a canonical encoding.
            assert_eq!(blob.len() % 4, 0);
            for w in blob.chunks(4) {
                let word = u32::from_le_bytes([
                    w.first().copied().unwrap_or(0),
                    w.get(1).copied().unwrap_or(0),
                    w.get(2).copied().unwrap_or(0),
                    w.get(3).copied().unwrap_or(0),
                ]);
                let i = decode_instr(word);
                assert!(i.is_some(), "accepted blob has non-subset word {word:#x}");
                if let Some(i) = i {
                    assert_eq!(encode_instr(&i), word);
                }
            }
        }
    }
    // The fuzz does reach accepted blobs (unmutated-looking ones, mostly).
    assert!(accepted > 0);
}
