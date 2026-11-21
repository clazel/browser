//! The back end never produces a blob the validator refuses (docs/phases/jit.md
//! J.9: "a test checks that the back end never produces a blob the validator
//! refuses").
//!
//! The blob is `emit_blob`'s output: the encoded templates and the exit
//! sequence. The validator is `clazel-codecheck`'s executable one
//! ([`clazel_codecheck::validate::validate`], proven sound and complete for
//! its spec), entered at offset 0.
//!
//! 1. **Every template.** For each instruction of the first slice, with every
//!    operator and comparison, a program that sets up the operands and runs it.
//! 2. **Generated programs.** A few thousand small random well-formed
//!    programs (a fixed seed), each of which must have a blob that is
//!    accepted.
//! 3. **What has no template is refused by the back end, not emitted**: the
//!    `f64` arithmetic, the rotates, a bad local, a short stack, a frame of
//!    more than 31 slots.
//! 4. **Controls.** The validator does refuse the blob when its last byte is
//!    changed or cut off, so a `true` above is not the validator saying yes
//!    to everything.
//!
//! This test is evidence, not proof: the proofs are in the `verus!` modules
//! (`compose::lemma_prog_refines` for the meaning of the code,
//! `emit::emit_blob_impl` for the bytes). That every blob is accepted is not
//! yet a theorem.

use clazel_codecheck::validate::validate;
use clazel_jit::api::Backend;
use clazel_jit::emit::X64Backend;
use clazel_jit::spec::Op;
use clazel_lir::spec::{BinOp, FBin, FCmp, IBin, ICmp, UnOp, Val};

// The spec's types are not `Copy`, so each use builds a fresh value.

const IBINS: [fn() -> IBin; 9] = [
    || IBin::Add,
    || IBin::Sub,
    || IBin::Mul,
    || IBin::And,
    || IBin::Or,
    || IBin::Xor,
    || IBin::Shl,
    || IBin::ShrU,
    || IBin::ShrS,
];

const ICMPS: [fn() -> ICmp; 10] = [
    || ICmp::Eq,
    || ICmp::Ne,
    || ICmp::LtS,
    || ICmp::LtU,
    || ICmp::GtS,
    || ICmp::GtU,
    || ICmp::LeS,
    || ICmp::LeU,
    || ICmp::GeS,
    || ICmp::GeU,
];

const UNS: [fn() -> UnOp; 8] = [
    || UnOp::I32Eqz,
    || UnOp::I64Eqz,
    || UnOp::F64Neg,
    || UnOp::F64Abs,
    || UnOp::I32WrapI64,
    || UnOp::I64ExtendI32S,
    || UnOp::I64ExtendI32U,
    || UnOp::F64ReinterpretI64,
];

/// Every operation of the slice that is one constructor away, with the
/// number of operands it takes.
fn all_ops() -> Vec<(Op, usize)> {
    let mut v = vec![
        (Op::Nop, 0),
        (Op::Drop, 1),
        (Op::Select, 3),
        (Op::LocalGet(0), 0),
        (Op::LocalGet(1), 0),
        (Op::LocalSet(0), 1),
        (Op::LocalSet(1), 1),
        (Op::LocalTee(0), 1),
        (Op::LocalTee(1), 1),
        (Op::Const(Val::I32(0)), 0),
        (Op::Const(Val::I32(u32::MAX)), 0),
        (Op::Const(Val::I64(0x1234_5678_9abc_def0)), 0),
        (Op::Const(Val::F64(0x7ff8_0000_0000_0001)), 0),
        (Op::Un(UnOp::I64ReinterpretF64), 1),
    ];
    for u in UNS {
        v.push((Op::Un(u()), 1));
    }
    for o in IBINS {
        v.push((Op::Bin(BinOp::I32(o())), 2));
        v.push((Op::Bin(BinOp::I64(o())), 2));
    }
    for c in ICMPS {
        v.push((Op::Bin(BinOp::I32Cmp(c())), 2));
        v.push((Op::Bin(BinOp::I64Cmp(c())), 2));
    }
    v
}

/// A program that pushes `n` constants, then runs `op`.
fn with_operands(op: Op, n: usize) -> Vec<Op> {
    let mut p: Vec<Op> = (0..n).map(|k| Op::Const(Val::I64(k as u64))).collect();
    p.push(op);
    p
}

fn blob(ops: &[Op], nl: usize) -> Option<Vec<u8>> {
    X64Backend::emit_blob(ops, nl, 7)
}

fn accepted(b: &[u8]) -> bool {
    validate(b, &[0])
}

#[test]
fn every_template_is_accepted() {
    let mut count = 0usize;
    for (op, n) in all_ops() {
        let prog = with_operands(op, n);
        let b = blob(&prog, 2);
        assert!(
            b.is_some(),
            "no blob for template {count} ({} ops)",
            prog.len()
        );
        let b = b.unwrap_or_default();
        assert!(
            accepted(&b),
            "the validator refuses template {count}: {b:02x?}"
        );
        count = count.saturating_add(1);
    }
    // 14 fixed + 8 unary + 18 integer + 20 comparisons
    assert_eq!(count, 60);
}

#[test]
fn the_body_alone_is_not_a_blob_but_the_blob_is() {
    // The blob is the body plus the exit sequence: cut the `ret` off and the
    // validator refuses (every path must end in an exit sequence or a
    // branch).
    let prog = with_operands(Op::Bin(BinOp::I32(IBin::Add)), 2);
    let body = X64Backend::emit_body(&prog, 0).unwrap_or_default();
    assert!(!body.is_empty());
    let b = blob(&prog, 0).unwrap_or_default();
    assert!(accepted(&b));
    // The exit sequence is `mov eax, 7` (5 bytes), `mov [r15+256], rax`
    // (8) and `ret` (1).
    assert_eq!(b.last().copied(), Some(0xc3));
    assert!(!accepted(b.get(..b.len().saturating_sub(1)).unwrap_or(&[])));
}

#[test]
fn an_empty_program_is_just_the_exit_sequence() {
    let b = blob(&[], 0).unwrap_or_default();
    assert_eq!(b.len(), 14);
    assert!(accepted(&b));
}

/// xorshift64: a fixed pseudo-random sequence.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x.wrapping_shl(13);
        x ^= x.wrapping_shr(7);
        x ^= x.wrapping_shl(17);
        self.0 = x;
        x
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

/// A random well-formed program for `nl` locals: each instruction has the
/// operands it needs, local indices are in range, the frame fits. Returns the
/// program.
fn random_program(rng: &mut Rng, nl: usize, len: usize) -> Vec<Op> {
    let ops = all_ops();
    let mut prog = Vec::new();
    let mut h = 0usize;
    for _ in 0..len {
        let pick = rng.below(ops.len());
        let Some((op, pops)) = ops.get(pick) else {
            continue;
        };
        let pops = *pops;
        // keep the frame inside 31 slots and the operands available
        if h < pops {
            let c = match rng.below(3) {
                0 => Val::I32(u32::try_from(rng.next() & 0xffff_ffff).unwrap_or(0)),
                1 => Val::I64(rng.next()),
                _ => Val::F64(rng.next()),
            };
            if nl.saturating_add(h) < 31 {
                prog.push(Op::Const(c));
                h = h.saturating_add(1);
            }
            continue;
        }
        let pushes = match op {
            Op::Nop | Op::Drop | Op::LocalSet(_) => 0,
            _ => 1,
        };
        let after = h.saturating_sub(pops).saturating_add(pushes);
        if nl.saturating_add(after) > 31 {
            continue;
        }
        // local indices 0 and 1 need two locals
        if matches!(op, Op::LocalGet(_) | Op::LocalSet(_) | Op::LocalTee(_)) && nl < 2 {
            continue;
        }
        prog.push(clone_op(op));
        h = after;
    }
    prog
}

fn clone_op(op: &Op) -> Op {
    match op {
        Op::Nop => Op::Nop,
        Op::Const(Val::I32(c)) => Op::Const(Val::I32(*c)),
        Op::Const(Val::I64(c)) => Op::Const(Val::I64(*c)),
        Op::Const(Val::F64(c)) => Op::Const(Val::F64(*c)),
        Op::LocalGet(x) => Op::LocalGet(*x),
        Op::LocalSet(x) => Op::LocalSet(*x),
        Op::LocalTee(x) => Op::LocalTee(*x),
        Op::Drop => Op::Drop,
        Op::Select => Op::Select,
        Op::Bin(b) => Op::Bin(match b {
            BinOp::I32(o) => BinOp::I32(clone_ibin(o)),
            BinOp::I64(o) => BinOp::I64(clone_ibin(o)),
            BinOp::I32Cmp(c) => BinOp::I32Cmp(clone_icmp(c)),
            BinOp::I64Cmp(c) => BinOp::I64Cmp(clone_icmp(c)),
            BinOp::F64(_) => BinOp::F64(FBin::Add),
            BinOp::F64Cmp(_) => BinOp::F64Cmp(FCmp::Eq),
        }),
        Op::Un(u) => Op::Un(clone_un(u)),
    }
}

fn clone_ibin(o: &IBin) -> IBin {
    match o {
        IBin::Add => IBin::Add,
        IBin::Sub => IBin::Sub,
        IBin::Mul => IBin::Mul,
        IBin::And => IBin::And,
        IBin::Or => IBin::Or,
        IBin::Xor => IBin::Xor,
        IBin::Shl => IBin::Shl,
        IBin::ShrS => IBin::ShrS,
        IBin::ShrU => IBin::ShrU,
        IBin::Rotl => IBin::Rotl,
        IBin::Rotr => IBin::Rotr,
    }
}

fn clone_icmp(c: &ICmp) -> ICmp {
    match c {
        ICmp::Eq => ICmp::Eq,
        ICmp::Ne => ICmp::Ne,
        ICmp::LtS => ICmp::LtS,
        ICmp::LtU => ICmp::LtU,
        ICmp::GtS => ICmp::GtS,
        ICmp::GtU => ICmp::GtU,
        ICmp::LeS => ICmp::LeS,
        ICmp::LeU => ICmp::LeU,
        ICmp::GeS => ICmp::GeS,
        ICmp::GeU => ICmp::GeU,
    }
}

fn clone_un(u: &UnOp) -> UnOp {
    match u {
        UnOp::I32Eqz => UnOp::I32Eqz,
        UnOp::I64Eqz => UnOp::I64Eqz,
        UnOp::F64Neg => UnOp::F64Neg,
        UnOp::F64Abs => UnOp::F64Abs,
        UnOp::F64Sqrt => UnOp::F64Sqrt,
        UnOp::I32WrapI64 => UnOp::I32WrapI64,
        UnOp::I64ExtendI32S => UnOp::I64ExtendI32S,
        UnOp::I64ExtendI32U => UnOp::I64ExtendI32U,
        UnOp::F64ConvertI32S => UnOp::F64ConvertI32S,
        UnOp::F64ConvertI32U => UnOp::F64ConvertI32U,
        UnOp::F64ConvertI64S => UnOp::F64ConvertI64S,
        UnOp::F64ConvertI64U => UnOp::F64ConvertI64U,
        UnOp::F64ReinterpretI64 => UnOp::F64ReinterpretI64,
        UnOp::I64ReinterpretF64 => UnOp::I64ReinterpretF64,
    }
}

#[test]
fn generated_programs_are_accepted() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut longest = 0usize;
    // Miri interprets every step: 3000 programs took 4772 s there, over
    // xtask's 300 s limit, so it checks the first 40 of the same sequence
    // (about a minute). The normal test job checks all 3000.
    let rounds = if cfg!(miri) { 40usize } else { 3000usize };
    for round in 0..rounds {
        let nl = rng.below(6);
        let len = rng.below(60);
        let prog = random_program(&mut rng, nl, len);
        let b = blob(&prog, nl);
        assert!(
            b.is_some(),
            "round {round}: no blob ({} ops, {nl} locals)",
            prog.len()
        );
        let b = b.unwrap_or_default();
        assert!(
            accepted(&b),
            "round {round}: refused ({} ops, {nl} locals): {b:02x?}",
            prog.len()
        );
        longest = longest.max(b.len());
    }
    // the programs are not all tiny
    assert!(
        longest > if cfg!(miri) { 100 } else { 300 },
        "longest blob {longest}"
    );
}

#[test]
fn no_template_means_no_blob() {
    // `f64` arithmetic, comparisons and conversions: LIR's are uninterpreted.
    let none = |op: Op, n: usize| {
        let prog = with_operands(op, n);
        assert!(
            blob(&prog, 2).is_none(),
            "unexpected blob for a program of {} ops",
            prog.len()
        );
        assert!(X64Backend::emit_body(&prog, 2).is_none());
    };
    none(Op::Bin(BinOp::F64(FBin::Add)), 2);
    none(Op::Bin(BinOp::F64(FBin::Div)), 2);
    none(Op::Bin(BinOp::F64Cmp(FCmp::Lt)), 2);
    none(Op::Un(UnOp::F64Sqrt), 1);
    none(Op::Un(UnOp::F64ConvertI32S), 1);
    none(Op::Un(UnOp::F64ConvertI64U), 1);
    // rotates
    none(Op::Bin(BinOp::I32(IBin::Rotl)), 2);
    none(Op::Bin(BinOp::I64(IBin::Rotr)), 2);
    // a local that does not exist
    none(Op::LocalGet(2), 0);
    none(Op::LocalSet(5), 1);
    // a short stack
    none(Op::Bin(BinOp::I32(IBin::Add)), 1);
    none(Op::Select, 2);
    none(Op::Drop, 0);
}

#[test]
fn the_frame_has_31_slots() {
    // 31 constants fit with no locals; the 32nd does not.
    let consts = |n: usize| -> Vec<Op> { (0..n).map(|_| Op::Const(Val::I32(1))).collect() };
    let b = blob(&consts(31), 0);
    assert!(b.as_deref().map(accepted).unwrap_or(false));
    assert!(blob(&consts(32), 0).is_none());
    // locals and stack share the 31
    assert!(blob(&consts(21), 10).is_some());
    assert!(blob(&consts(22), 10).is_none());
    assert!(blob(&[], 31).is_some());
    assert!(blob(&[], 32).is_none());
}

#[test]
fn the_validator_refuses_what_is_not_a_blob() {
    let prog = with_operands(Op::Bin(BinOp::I64(IBin::Xor)), 2);
    let b = blob(&prog, 0).unwrap_or_default();
    assert!(accepted(&b));
    // cut off
    assert!(!accepted(b.get(..b.len().saturating_sub(1)).unwrap_or(&[])));
    // the `ret` replaced by a byte that is no instruction of the subset
    let mut bad = b.clone();
    if let Some(last) = bad.last_mut() {
        *last = 0xf4; // hlt
    }
    assert!(!accepted(&bad));
    // entered in the middle of an instruction
    assert!(!validate(&b, &[1]));
}
