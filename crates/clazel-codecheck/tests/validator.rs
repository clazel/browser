//! Tests of the executable validator and decoder: accepted programs, a
//! hostile corpus (jit.md exit criterion 6, the hand-assembled part), and
//! decoder checks. The programs are the ones of `src/examples.rs`, whose
//! jump displacements are worked out there.

use clazel_codecheck::validate::validate;
use clazel_x64::decoder_exec::decode_exec as decode;
use clazel_x64::encoder::encode_exec as encode;
use clazel_x64::spec::{AluOp, Index, Instr, Mem, Size};

fn ctxm(disp: i32) -> Mem {
    Mem { base: 15, index: None, disp }
}

fn exit_seq(t: u8, code: u32) -> Vec<Instr> {
    vec![
        Instr::MovImm32 { dst: t, imm_u32: code },
        Instr::MovStore { sz: Size::W64, mem: ctxm(256), src: t },
        Instr::Ret,
    ]
}

fn base_load(dst: u8, k: i32) -> Instr {
    Instr::MovLoad { sz: Size::W64, dst, mem: ctxm(k.wrapping_mul(16)) }
}

fn region_load(dst: u8, base: u8, idx: u8) -> Instr {
    Instr::MovLoad {
        sz: Size::W64,
        dst,
        mem: Mem { base, index: Some(Index { reg: idx, scale: 0 }), disp: 0 },
    }
}

/// The bounds check of region `k` for `n` bytes: index `r1`, scratch `r5`,
/// `r6`.
fn check_seq(k: i32, n: i32, r1: i32, r2: i32) -> Vec<Instr> {
    let bound = Mem { base: 15, index: None, disp: k.wrapping_mul(16).wrapping_add(8) };
    vec![
        Instr::MovRR { sz: Size::W64, dst: 5, src: 1 },
        Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: 5, imm: n },
        Instr::Jcc { cc: 2, rel: r1 },
        Instr::AluRM {
            alu: AluOp::Cmp,
            sz: Size::W64,
            dst: 5,
            mem: Mem { base: 15, index: None, disp: bound.disp },
        },
        Instr::Jcc { cc: 7, rel: r2 },
        Instr::MovImm32 { dst: 6, imm_u32: 0 },
        Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: 1, mem: bound },
        Instr::Cmovcc { cc: 3, sz: Size::W64, dst: 1, src: 6 },
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

fn ok(ins: &[Instr]) -> bool {
    validate(&bytes(ins), &[0])
}

#[test]
fn exit_sequence_bytes_are_accepted() {
    let blob = [0xB8, 7, 0, 0, 0, 0x49, 0x89, 0x84, 0x27, 0, 1, 0, 0, 0xC3];
    assert!(validate(&blob, &[0]));
    assert_eq!(bytes(&exit_seq(0, 7)), blob);
}

#[test]
fn accepted_programs() {
    assert!(ok(&checked_load(3, 8)));
    // A second entry at the exit sequence (offset 63).
    assert!(validate(&bytes(&checked_load(3, 8)), &[0, 63]));
    // A loop.
    let l = [
        Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 },
        Instr::Jmp { rel: -8 },
    ];
    assert!(ok(&l));
    // A store to an exit operand.
    let mut p = vec![Instr::MovStore { sz: Size::W64, mem: ctxm(264), src: 0 }];
    p.extend(exit_seq(7, 1));
    assert!(ok(&p));
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
fn writes_to_reserved_registers_are_refused() {
    for dst in [4u8, 15] {
        let mut p = vec![Instr::MovRR { sz: Size::W64, dst, src: 0 }];
        p.extend(exit_seq(7, 1));
        assert!(!ok(&p), "mov r{dst}, rax");
        let mut p = vec![Instr::MovImm32 { dst, imm_u32: 0 }];
        p.extend(exit_seq(7, 1));
        assert!(!ok(&p), "mov r{dst}d, 0");
        let mut p = vec![Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst, imm: 8 }];
        p.extend(exit_seq(7, 1));
        assert!(!ok(&p), "add r{dst}, 8");
    }
    // `cmp rsp, 8` writes nothing.
    let mut p = vec![Instr::AluRI { alu: AluOp::Cmp, sz: Size::W64, dst: 4, imm: 8 }];
    p.extend(exit_seq(7, 1));
    assert!(ok(&p));
}

#[test]
fn jump_into_a_bounds_check_is_refused() {
    let mut p = vec![Instr::Jmp { rel: 3 }];
    p.extend(check_seq(3, 8, 31, 17));
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn jump_over_a_bounds_check_to_the_access_is_refused() {
    let mut p = vec![Instr::Jmp { rel: 55 }, base_load(2, 3)];
    p.extend(check_seq(3, 8, 39, 25));
    p.push(region_load(0, 2, 1));
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn store_to_the_region_table_is_refused() {
    let mut p = vec![Instr::MovStore { sz: Size::W64, mem: ctxm(0), src: 0 }];
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
    // Out of the context altogether.
    let mut p = vec![Instr::MovLoad { sz: Size::W64, dst: 0, mem: ctxm(508) }];
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
    let mut p = vec![Instr::MovLoad { sz: Size::W64, dst: 0, mem: ctxm(-8) }];
    p.extend(exit_seq(7, 1));
    assert!(!ok(&p));
}

#[test]
fn running_off_the_end_is_refused() {
    assert!(!ok(&[Instr::AluRR { alu: AluOp::Add, sz: Size::W64, dst: 0, src: 3 }]));
    // A conditional jump last: its fall-through leaves the blob.
    let mut p = exit_seq(7, 1);
    p.push(Instr::Jcc { cc: 4, rel: -14 });
    assert!(!ok(&p));
}

#[test]
fn bare_ret_and_other_exits_are_refused() {
    assert!(!ok(&[Instr::Ret]));
    // An exit sequence that stores through the wrong operand.
    let p = vec![
        Instr::MovImm32 { dst: 7, imm_u32: 1 },
        Instr::MovStore { sz: Size::W64, mem: ctxm(264), src: 7 },
        Instr::Ret,
    ];
    assert!(!ok(&p));
}

#[test]
fn entries_and_jumps_must_hit_unit_starts() {
    let blob = bytes(&checked_load(3, 8));
    assert!(!validate(&blob, &[9]), "entry inside the check");
    assert!(!validate(&blob, &[blob.len()]), "entry at the end");
    assert!(!validate(&blob, &[usize::MAX]), "entry out of range");
    assert!(!ok(&[Instr::Jmp { rel: 100 }]), "jump out");
    assert!(!ok(&[Instr::Jmp { rel: -100 }]), "jump before the start");
}

#[test]
fn truncated_and_empty_blobs_are_refused() {
    assert!(!validate(&[], &[]));
    let blob = bytes(&checked_load(3, 8));
    for n in 0..blob.len() {
        assert!(!validate(blob.get(..n).unwrap_or(&[]), &[0]), "prefix of {n} bytes");
    }
}

#[test]
fn non_canonical_and_forbidden_bytes_are_refused() {
    let tails = exit_seq(7, 1);
    let tail = bytes(&tails);
    let cases: &[(&str, &[u8])] = &[
        ("nop", &[0x90]),
        ("syscall", &[0x0F, 0x05]),
        ("int 0x80", &[0xCD, 0x80]),
        ("jmp rax", &[0xFF, 0xE0]),
        ("call rel32", &[0xE8, 0, 0, 0, 0]),
        ("ret imm16", &[0xC2, 0, 0]),
        ("push rax", &[0x50]),
        ("pop rsp", &[0x5C]),
        ("hlt", &[0xF4]),
        ("add rax, rbx, direction 03", &[0x48, 0x03, 0xC3]),
        ("add eax, ebx with a redundant REX", &[0x40, 0x01, 0xD8]),
        ("add rax, rbx with a 66 prefix", &[0x66, 0x48, 0x01, 0xD8]),
        ("add rax, imm8", &[0x48, 0x83, 0xC0, 0x01]),
        ("mov rax, [rbx] (mod 00)", &[0x48, 0x8B, 0x03]),
        ("mov rax, fs:[rbx]", &[0x64, 0x48, 0x8B, 0x84, 0x23, 0, 0, 0, 0]),
        ("lock add", &[0xF0, 0x48, 0x01, 0xD8]),
        ("rep movsb", &[0xF3, 0xA4]),
        ("rip-relative load", &[0x48, 0x8B, 0x05, 0, 0, 0, 0]),
        ("address-size override", &[0x67, 0x48, 0x8B, 0x84, 0x23, 0, 0, 0, 0]),
        ("VEX", &[0xC5, 0xF8, 0x77]),
        ("jmp rel8", &[0xEB, 0x00]),
    ];
    for (name, bad) in cases {
        let mut blob = bad.to_vec();
        blob.extend(&tail);
        assert!(!validate(&blob, &[0]), "{name}");
        assert!(decode(bad).is_none(), "{name} decodes");
    }
}

#[test]
fn the_decoder_reads_back_what_the_encoder_writes() {
    let samples = [
        Instr::MovRR { sz: Size::W64, dst: 9, src: 3 },
        Instr::MovLoad { sz: Size::W32, dst: 12, mem: Mem { base: 13, index: Some(Index { reg: 12, scale: 3 }), disp: -5 } },
        Instr::MovImm64 { dst: 11, imm_u64: 0x0123_4567_89AB_CDEF },
        Instr::MovImm32S { dst: 2, imm: -1 },
        Instr::ShiftImm { shift: clazel_x64::spec::ShiftOp::Sar, sz: Size::W64, r: 14, count: 63 },
        Instr::Setcc { cc: 4, dst: 6 },
        Instr::Jcc { cc: 15, rel: i32::MIN },
        Instr::Ret,
    ];
    for i in &samples {
        let e = encode(i);
        let mut padded = e.clone();
        padded.extend([0xAA, 0xBB]);
        let got = decode(&padded);
        assert_eq!(got.as_ref().map(|(g, n)| (encode(g), *n)), Some((e.clone(), e.len())));
        for n in 0..e.len() {
            assert!(decode(e.get(..n).unwrap_or(&[])).is_none(), "{n}-byte prefix of {e:02X?}");
        }
    }
}

#[test]
fn shift_counts_out_of_range_are_refused() {
    use clazel_x64::spec::ShiftOp;
    for (sz, count) in [(Size::W64, 0u8), (Size::W64, 64), (Size::W32, 32), (Size::W32, 0)] {
        let i = Instr::ShiftImm { shift: ShiftOp::Shl, sz, r: 0, count };
        assert!(decode(&encode(&i)).is_none());
    }
}

#[test]
fn random_bytes_never_panic() {
    let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let mut accepted = 0usize;
    for round in 0..20_000usize {
        let n = usize::try_from(next() % 64).unwrap_or(0);
        let blob: Vec<u8> = (0..n).map(|_| next().to_le_bytes()[0]).collect();
        let entries: Vec<usize> = (0..round % 3).map(|_| usize::try_from(next() % 70).unwrap_or(0)).collect();
        accepted += usize::from(validate(&blob, &entries));
    }
    assert!(accepted < 20_000);
}

#[test]
fn single_byte_mutations_of_an_accepted_blob_are_decided_without_panic() {
    let blob = bytes(&checked_load(3, 8));
    let mut still_ok = 0usize;
    for pos in 0..blob.len() {
        for v in [0u8, 0x0F, 0x40, 0x49, 0x66, 0x80, 0xC3, 0xE9, 0xFF] {
            let mut m = blob.clone();
            if let Some(b) = m.get_mut(pos) {
                *b = v;
            }
            still_ok += usize::from(validate(&m, &[0]));
        }
    }
    // Some mutations are harmless (a new exit code); most are not.
    assert!(still_ok < blob.len() * 9);
}
