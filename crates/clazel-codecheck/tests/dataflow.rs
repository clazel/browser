//! Tests of the second x86-64 validator (the dataflow analysis): it must never
//! accept what the first validator refuses (the proven contract, checked here
//! on the hostile corpus of `validator.rs` and on a deterministic mutation
//! fuzz), and it agrees with the first on every case of the corpus. The
//! contract promises only the first direction; agreement is observed.

use clazel_codecheck::dataflow::validate::validate as second;
use clazel_codecheck::validate::validate as first;
use clazel_x64::encoder::encode_exec as encode;
use clazel_x64::spec::{AluOp, Index, Instr, Mem, Size};

fn ctxm(disp: i32) -> Mem {
    Mem {
        base: 15,
        index: None,
        disp,
    }
}

fn exit_seq(t: u8, code: u32) -> Vec<Instr> {
    vec![
        Instr::MovImm32 {
            dst: t,
            imm_u32: code,
        },
        Instr::MovStore {
            sz: Size::W64,
            mem: ctxm(256),
            src: t,
        },
        Instr::Ret,
    ]
}

fn base_load(dst: u8, k: i32) -> Instr {
    Instr::MovLoad {
        sz: Size::W64,
        dst,
        mem: ctxm(k.wrapping_mul(16)),
    }
}

fn region_load(dst: u8, base: u8, idx: u8) -> Instr {
    Instr::MovLoad {
        sz: Size::W64,
        dst,
        mem: Mem {
            base,
            index: Some(Index { reg: idx, scale: 0 }),
            disp: 0,
        },
    }
}

/// The bounds check of region `k` for `n` bytes: index `r1`, scratch `r5`,
/// `r6`.
fn check_seq(k: i32, n: i32, r1: i32, r2: i32) -> Vec<Instr> {
    let bound = k.wrapping_mul(16).wrapping_add(8);
    vec![
        Instr::MovRR {
            sz: Size::W64,
            dst: 5,
            src: 1,
        },
        Instr::AluRI {
            alu: AluOp::Add,
            sz: Size::W64,
            dst: 5,
            imm: n,
        },
        Instr::Jcc { cc: 2, rel: r1 },
        Instr::AluRM {
            alu: AluOp::Cmp,
            sz: Size::W64,
            dst: 5,
            mem: ctxm(bound),
        },
        Instr::Jcc { cc: 7, rel: r2 },
        Instr::MovImm32 { dst: 6, imm_u32: 0 },
        Instr::AluRM {
            alu: AluOp::Cmp,
            sz: Size::W64,
            dst: 1,
            mem: ctxm(bound),
        },
        Instr::Cmovcc {
            cc: 3,
            sz: Size::W64,
            dst: 1,
            src: 6,
        },
    ]
}

fn bytes(ins: &[Instr]) -> Vec<u8> {
    ins.iter().flat_map(encode).collect()
}

fn checked_load(k: i32, n: i32) -> Vec<Instr> {
    let mut p = vec![base_load(2, 3)];
    p.extend(check_seq(k, n, 39, 25));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    p
}

fn add(dst: u8) -> Instr {
    Instr::AluRR {
        alu: AluOp::Add,
        sz: Size::W64,
        dst,
        src: 3,
    }
}

/// A program, its entries, and whether both validators must accept it.
type Case = (&'static str, Vec<Instr>, Vec<usize>, bool);

fn with_exit(mut p: Vec<Instr>) -> Vec<Instr> {
    p.extend(exit_seq(7, 1));
    p
}

fn corpus() -> Vec<Case> {
    let mut v: Vec<Case> = vec![("checked load", checked_load(3, 8), vec![0], true)];
    v.push((
        "checked load, second entry",
        checked_load(3, 8),
        vec![0, 63],
        true,
    ));
    v.push(("loop", vec![add(0), Instr::Jmp { rel: -8 }], vec![0], true));
    v.push((
        "store to an exit operand",
        with_exit(vec![Instr::MovStore {
            sz: Size::W64,
            mem: ctxm(264),
            src: 0,
        }]),
        vec![0],
        true,
    ));
    v.push((
        "cmp rsp is not a write",
        with_exit(vec![Instr::AluRI {
            alu: AluOp::Cmp,
            sz: Size::W64,
            dst: 4,
            imm: 8,
        }]),
        vec![0],
        true,
    ));
    let mut p = vec![base_load(2, 3), region_load(0, 2, 1)];
    p.extend(exit_seq(7, 1));
    v.push(("unchecked index", p, vec![0], false));
    v.push((
        "check for too few bytes",
        checked_load(3, 4),
        vec![0],
        false,
    ));
    v.push((
        "check of the wrong region",
        checked_load(2, 8),
        vec![0],
        false,
    ));
    for dst in [4u8, 15] {
        v.push((
            "mov to a reserved register",
            with_exit(vec![Instr::MovRR {
                sz: Size::W64,
                dst,
                src: 0,
            }]),
            vec![0],
            false,
        ));
        v.push((
            "mov imm to a reserved register",
            with_exit(vec![Instr::MovImm32 { dst, imm_u32: 0 }]),
            vec![0],
            false,
        ));
        v.push((
            "add to a reserved register",
            with_exit(vec![Instr::AluRI {
                alu: AluOp::Add,
                sz: Size::W64,
                dst,
                imm: 8,
            }]),
            vec![0],
            false,
        ));
    }
    let mut p = vec![Instr::Jmp { rel: 3 }];
    p.extend(check_seq(3, 8, 31, 17));
    p.extend(exit_seq(7, 1));
    v.push(("jump into a bounds check", p, vec![0], false));
    let mut p = vec![Instr::Jmp { rel: 55 }, base_load(2, 3)];
    p.extend(check_seq(3, 8, 39, 25));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    v.push(("jump over a check to the access", p, vec![0], false));
    v.push((
        "store to the region table",
        with_exit(vec![Instr::MovStore {
            sz: Size::W64,
            mem: ctxm(0),
            src: 0,
        }]),
        vec![0],
        false,
    ));
    for d in [508, -8] {
        v.push((
            "load outside the context",
            with_exit(vec![Instr::MovLoad {
                sz: Size::W64,
                dst: 0,
                mem: ctxm(d),
            }]),
            vec![0],
            false,
        ));
    }
    v.push(("runs off the end", vec![add(0)], vec![0], false));
    let mut p = exit_seq(7, 1);
    p.push(Instr::Jcc { cc: 4, rel: -14 });
    v.push(("jcc last", p, vec![0], false));
    v.push(("bare ret", vec![Instr::Ret], vec![0], false));
    v.push((
        "exit through the wrong operand",
        vec![
            Instr::MovImm32 { dst: 7, imm_u32: 1 },
            Instr::MovStore {
                sz: Size::W64,
                mem: ctxm(264),
                src: 7,
            },
            Instr::Ret,
        ],
        vec![0],
        false,
    ));
    v.push(("jump out", vec![Instr::Jmp { rel: 100 }], vec![0], false));
    v.push((
        "jump before the start",
        vec![Instr::Jmp { rel: -100 }],
        vec![0],
        false,
    ));
    // A fact must not survive a jump target: the access after the loop head
    // lands where the base register is unknown.
    let mut p = vec![base_load(2, 3)];
    p.extend(check_seq(3, 8, 54, 40));
    p.push(add(9));
    p.push(region_load(0, 2, 1));
    p.push(Instr::Jmp { rel: -16 });
    v.push(("fact kept past a target", p, vec![0], false));
    // The base is overwritten between the check and the access.
    let mut p = vec![base_load(2, 3)];
    p.extend(check_seq(3, 8, 39, 25));
    p.push(Instr::MovRR {
        sz: Size::W64,
        dst: 2,
        src: 8,
    });
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    v.push(("base overwritten", p, vec![0], false));
    // The index is overwritten between the check and the access.
    let mut p = vec![base_load(2, 3)];
    p.extend(check_seq(3, 8, 39, 25));
    p.push(add(1));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    v.push(("index overwritten", p, vec![0], false));
    v
}

#[test]
fn both_validators_agree_on_the_corpus() {
    for (name, p, entries, want) in corpus() {
        let blob = bytes(&p);
        let a = first(&blob, &entries);
        let b = second(&blob, &entries);
        assert_eq!(a, want, "first validator, {name}");
        assert_eq!(b, want, "second validator, {name}");
    }
}

#[test]
fn entries_and_truncations() {
    let blob = bytes(&checked_load(3, 8));
    for entries in [
        vec![9],
        vec![blob.len()],
        vec![usize::MAX],
        vec![0, 9],
        vec![],
    ] {
        assert_eq!(
            first(&blob, &entries),
            second(&blob, &entries),
            "{entries:?}"
        );
    }
    assert!(!second(&[], &[]));
    for n in 0..blob.len() {
        let t = blob.get(..n).unwrap_or(&[]);
        assert!(!second(t, &[0]), "prefix of {n} bytes");
    }
}

#[test]
fn forbidden_bytes_are_refused() {
    let tail = bytes(&exit_seq(7, 1));
    let cases: &[&[u8]] = &[
        &[0x90],
        &[0x0F, 0x05],
        &[0xCD, 0x80],
        &[0xFF, 0xE0],
        &[0xE8, 0, 0, 0, 0],
        &[0xC2, 0, 0],
        &[0x50],
        &[0x5C],
        &[0xF4],
        &[0x48, 0x03, 0xC3],
        &[0x40, 0x01, 0xD8],
        &[0x66, 0x48, 0x01, 0xD8],
        &[0x64, 0x48, 0x8B, 0x84, 0x23, 0, 0, 0, 0],
        &[0xF0, 0x48, 0x01, 0xD8],
        &[0x48, 0x8B, 0x05, 0, 0, 0, 0],
        &[0xC5, 0xF8, 0x77],
        &[0xEB, 0x00],
    ];
    for bad in cases {
        let mut blob = bad.to_vec();
        blob.extend(&tail);
        assert!(!second(&blob, &[0]), "{bad:02X?}");
    }
}

/// A deterministic generator (xorshift64).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
}

/// Runs both validators and checks the proven direction.
fn check(blob: &[u8], entries: &[usize], second_accepted: &mut usize, first_accepted: &mut usize) {
    let a = first(blob, entries);
    let b = second(blob, entries);
    assert!(
        !b || a,
        "the second validator accepted what the first refused: {blob:02X?} at {entries:?}"
    );
    *second_accepted = second_accepted.saturating_add(usize::from(b));
    *first_accepted = first_accepted.saturating_add(usize::from(a));
}

#[test]
fn mutation_fuzz_never_accepts_what_the_first_refuses() {
    // Seeds are the accepted programs of the corpus. Under Miri, which
    // interprets every step, a tenth of the rounds run (about a minute); the
    // full count runs in the normal test job.
    let rounds: usize = if cfg!(miri) { 300 } else { 6_000 };
    let seeds: Vec<(Vec<u8>, Vec<usize>)> = corpus()
        .into_iter()
        .map(|(_, p, e, _)| (bytes(&p), e))
        .collect();
    let pool: Vec<Vec<u8>> = corpus()
        .into_iter()
        .flat_map(|(_, p, _, _)| p)
        .map(|i| encode(&i))
        .collect();
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let (mut sa, mut fa) = (0usize, 0usize);
    for round in 0..rounds {
        let (seed, entries) = seeds
            .get(rng.below(seeds.len()))
            .cloned()
            .unwrap_or_default();
        let mut blob = seed;
        let mut entries = entries;
        match round % 4 {
            // Replace one to three bytes.
            0 => {
                for _ in 0..=rng.below(3) {
                    let pos = rng.below(blob.len());
                    if let Some(b) = blob.get_mut(pos) {
                        *b = rng.next().to_le_bytes()[0];
                    }
                }
            }
            // A random list of whole instructions from the corpus, so most
            // results still decode.
            1 => {
                blob = (0..2 + rng.below(8))
                    .filter_map(|_| pool.get(rng.below(pool.len())))
                    .flatten()
                    .copied()
                    .collect();
                if rng.below(2) == 0 {
                    blob.extend(bytes(&exit_seq(7, 1)));
                }
                entries = vec![0];
            }
            // Perturb a jump displacement or an entry.
            2 => {
                let pos = rng.below(blob.len());
                if let Some(b) = blob.get_mut(pos) {
                    *b = b.wrapping_add(1 + u8::try_from(rng.below(7)).unwrap_or(0));
                }
                entries = (0..rng.below(3))
                    .map(|_| rng.below(blob.len() + 2))
                    .collect();
            }
            // Truncate or extend.
            _ => {
                let cut = rng.below(blob.len() + 1);
                blob.truncate(cut);
                if rng.below(2) == 0 {
                    blob.extend(bytes(&exit_seq(7, 1)));
                }
            }
        }
        check(&blob, &entries, &mut sa, &mut fa);
    }
    // The fuzz must reach accepted blobs, or it tests nothing.
    assert!(fa > 0, "no mutant was accepted by the first validator");
    assert!(sa > 0, "no mutant was accepted by the second validator");
}

#[test]
fn single_byte_mutations_of_accepted_blobs() {
    let (mut sa, mut fa) = (0usize, 0usize);
    let step: usize = if cfg!(miri) { 7 } else { 1 };
    for (_, p, entries, want) in corpus() {
        if !want {
            continue;
        }
        let blob = bytes(&p);
        for pos in (0..blob.len()).step_by(step) {
            for v in [
                0u8, 0x0F, 0x40, 0x49, 0x66, 0x80, 0xC3, 0xE9, 0xFF, 7, 8, 16,
            ] {
                let mut m = blob.clone();
                if let Some(b) = m.get_mut(pos) {
                    *b = v;
                }
                check(&m, &entries, &mut sa, &mut fa);
            }
        }
    }
    assert!(sa > 0 && fa > 0);
}

#[test]
fn random_bytes_never_panic_and_never_disagree_unsafely() {
    let rounds: usize = if cfg!(miri) { 300 } else { 10_000 };
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    let (mut sa, mut fa) = (0usize, 0usize);
    for round in 0..rounds {
        let n = rng.below(64);
        let blob: Vec<u8> = (0..n).map(|_| rng.next().to_le_bytes()[0]).collect();
        let entries: Vec<usize> = (0..round % 3).map(|_| rng.below(70)).collect();
        check(&blob, &entries, &mut sa, &mut fa);
    }
    assert!(sa <= fa);
}
