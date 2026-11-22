//! The control-flow back end never produces a blob the validator refuses
//! (docs/phases/jit.md J.9: "a test checks that the back end never produces a
//! blob the validator refuses"), for **structured control flow, memory
//! instructions and `br_table`**.
//!
//! The blob is [`clazel_jit::cfemit::emit_cf_blob`]'s output, the encoded body
//! and the exit sequence, and the validator is `clazel-codecheck`'s executable
//! one, entered at offset 0.
//!
//! 1. **Every memory template**: every region, every access type, every check
//!    size, with its operands set up.
//! 2. **`br_table`** with every position of the index, nested in blocks.
//! 3. **Generated programs** with blocks, loops, `if`, branches, memory
//!    accesses, `br_table` and `exit` (a fixed seed), each of which must
//!    have a blob that is accepted.
//! 4. **Refusals**: what has no translation is not emitted.
//! 5. **Controls**: the validator does refuse a blob whose bounds check is
//!    broken, whose jump lands inside the check, or whose last byte is cut.
//!
//! That the validator accepts the blobs is evidence, not proof; that the emitter returns the templates is proven (`clazel_jit::cfemit`).

use clazel_codecheck::validate::validate;
use clazel_jit::cfemit::emit_cf_blob;
use clazel_jit::cfspec::{MTy, MemOp, Node};
use clazel_jit::spec::Op;
use clazel_lir::spec::{BinOp, IBin, Val};

fn nop() -> Node {
    Node::Op(Op::Nop)
}

fn then(a: Node, b: Node) -> Node {
    Node::Then(Box::new(a), Box::new(b))
}

fn seq(nodes: Vec<Node>) -> Node {
    nodes.into_iter().fold(nop(), then)
}

fn c64(x: u64) -> Node {
    Node::Op(Op::Const(Val::I64(x)))
}

fn c32(x: u32) -> Node {
    Node::Op(Op::Const(Val::I32(x)))
}

fn accepted(b: &[u8]) -> bool {
    validate(b, &[0])
}

fn blob(n: &Node, nl: usize) -> Option<Vec<u8>> {
    emit_cf_blob(n, nl, 7)
}

const TYS: [fn() -> MTy; 3] = [|| MTy::I32, || MTy::I64, || MTy::F64];

fn const_of(ty: &MTy) -> Node {
    match ty {
        MTy::I32 => c32(5),
        MTy::I64 => c64(5),
        MTy::F64 => Node::Op(Op::Const(Val::F64(5))),
    }
}

#[test]
fn every_memory_template_is_accepted() {
    let regions: Vec<usize> = if cfg!(miri) {
        vec![0, 15]
    } else {
        (0..16).collect()
    };
    let mut count = 0usize;
    for region in regions {
        for ty in TYS {
            let load = seq(vec![c64(3), Node::Mem(MemOp::Load { region, ty: ty() })]);
            let store = seq(vec![
                c64(3),
                const_of(&ty()),
                Node::Mem(MemOp::Store { region, ty: ty() }),
            ]);
            for (name, p) in [("load", load), ("store", store)] {
                let b = blob(&p, 2).unwrap_or_default();
                assert!(!b.is_empty(), "no blob for {name} region {region}");
                assert!(accepted(&b), "refused: {name} region {region}: {b:02x?}");
                count = count.saturating_add(1);
            }
        }
        let sizes: Vec<usize> = if cfg!(miri) {
            vec![1, 8]
        } else {
            (1..=8).collect()
        };
        for size in sizes {
            let p = seq(vec![
                c64(3),
                Node::Mem(MemOp::BoundsCheck {
                    region,
                    size,
                    code: 99,
                }),
            ]);
            let b = blob(&p, 0).unwrap_or_default();
            assert!(!b.is_empty(), "no blob for bounds_check {region} {size}");
            assert!(accepted(&b), "refused: bounds_check {region} {size}");
            count = count.saturating_add(1);
        }
    }
    assert!(count >= if cfg!(miri) { 14 } else { 224 });
}

#[test]
fn br_table_is_accepted() {
    // block 2 { block 1 { block 0 { index; br_table [0 1 2 1] 2 } } }
    for pos in 0..6u32 {
        let table = Node::BrTable(vec![0, 1, 2, 1], 2);
        let inner = Node::Block(Box::new(seq(vec![c32(pos), table])));
        let mid = Node::Block(Box::new(then(inner, nop())));
        let outer = Node::Block(Box::new(then(mid, nop())));
        let b = blob(&outer, 0).unwrap_or_default();
        assert!(!b.is_empty(), "no blob for br_table {pos}");
        assert!(accepted(&b), "refused: br_table {pos}: {b:02x?}");
    }
    // a table with no targets is a `jmp` to the default
    let p = Node::Block(Box::new(seq(vec![c32(0), Node::BrTable(vec![], 0)])));
    assert!(accepted(&blob(&p, 0).unwrap_or_default()));
    // and one with many
    let many: Vec<usize> = (0..300usize)
        .map(|i| i.checked_rem(2).unwrap_or(0))
        .collect();
    let p = Node::Block(Box::new(Node::Block(Box::new(seq(vec![
        c32(1),
        Node::BrTable(many, 1),
    ])))));
    let b = blob(&p, 0).unwrap_or_default();
    assert!(b.len() > 3900);
    assert!(accepted(&b));
}

#[test]
fn a_loop_with_memory_is_accepted() {
    // loop { local.get 0; i64.const 8; i64.add; local.tee 0; load; drop; br_if 0 }
    let body = seq(vec![
        Node::Op(Op::LocalGet(0)),
        c64(8),
        Node::Op(Op::Bin(BinOp::I64(IBin::Add))),
        Node::Op(Op::LocalTee(0)),
        Node::Mem(MemOp::Load {
            region: 1,
            ty: MTy::I32,
        }),
        Node::BrIf(0),
    ]);
    let p = seq(vec![
        c64(0),
        Node::Op(Op::LocalSet(0)),
        Node::Loop(Box::new(body)),
    ]);
    let b = blob(&p, 1).unwrap_or_default();
    assert!(!b.is_empty());
    assert!(accepted(&b), "refused: {b:02x?}");
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

/// The generator's context: locals, and the most height it uses.
const MAX_H: usize = 8;

/// One random instruction valid at height `h` with `depth` labels in scope,
/// with `nest` more levels of nesting allowed; the height after it, or
/// `None` if it never falls through.
fn gen_one(rng: &mut Rng, nl: usize, h: usize, depth: usize, nest: usize) -> (Node, Option<usize>) {
    loop {
        let pick = rng.below(18);
        let room = h < MAX_H;
        match pick {
            0 if room => {
                return (
                    c32(u32::try_from(rng.below(5)).unwrap_or(0)),
                    Some(h.saturating_add(1)),
                );
            }
            1 if room => {
                return (
                    c64(rng.next().checked_rem(40).unwrap_or(0)),
                    Some(h.saturating_add(1)),
                );
            }
            2 if h >= 1 => return (Node::Op(Op::Drop), Some(h.saturating_sub(1))),
            3 if nl >= 1 && room => {
                return (
                    Node::Op(Op::LocalGet(rng.below(nl))),
                    Some(h.saturating_add(1)),
                );
            }
            4 if nl >= 1 && h >= 1 => {
                return (
                    Node::Op(Op::LocalSet(rng.below(nl))),
                    Some(h.saturating_sub(1)),
                );
            }
            5 => return (nop(), Some(h)),
            6 if h >= 2 => {
                return (
                    Node::Op(Op::Bin(BinOp::I64(IBin::Add))),
                    Some(h.saturating_sub(1)),
                );
            }
            7 if h >= 1 => {
                let ty = TYS.get(rng.below(3)).map_or(MTy::I64, |f| f());
                return (
                    Node::Mem(MemOp::Load {
                        region: rng.below(16),
                        ty,
                    }),
                    Some(h),
                );
            }
            8 if h >= 2 => {
                let ty = TYS.get(rng.below(3)).map_or(MTy::I64, |f| f());
                return (
                    Node::Mem(MemOp::Store {
                        region: rng.below(16),
                        ty,
                    }),
                    Some(h.saturating_sub(2)),
                );
            }
            9 if h >= 1 => {
                return (
                    Node::Mem(MemOp::BoundsCheck {
                        region: rng.below(16),
                        size: rng.below(8).saturating_add(1),
                        code: u32::try_from(rng.below(1000)).unwrap_or(0),
                    }),
                    Some(h),
                );
            }
            10 if nest > 0 => {
                let (b, _) = gen_body(
                    rng,
                    nl,
                    h,
                    depth.saturating_add(1),
                    nest.saturating_sub(1),
                    h,
                );
                return (Node::Block(Box::new(b)), Some(h));
            }
            11 if nest > 0 => {
                let (b, _) = gen_body(
                    rng,
                    nl,
                    h,
                    depth.saturating_add(1),
                    nest.saturating_sub(1),
                    h,
                );
                return (Node::Loop(Box::new(b)), Some(h));
            }
            12 if nest > 0 && h >= 1 => {
                let (t, _) = gen_body(
                    rng,
                    nl,
                    h.saturating_sub(1),
                    depth.saturating_add(1),
                    nest.saturating_sub(1),
                    h.saturating_sub(1),
                );
                let (e, _) = gen_body(
                    rng,
                    nl,
                    h.saturating_sub(1),
                    depth.saturating_add(1),
                    nest.saturating_sub(1),
                    h.saturating_sub(1),
                );
                return (
                    Node::If(Box::new(t), Box::new(e)),
                    Some(h.saturating_sub(1)),
                );
            }
            13 if depth >= 1 => return (Node::Br(rng.below(depth)), None),
            14 if depth >= 1 && h >= 1 => {
                return (Node::BrIf(rng.below(depth)), Some(h.saturating_sub(1)));
            }
            15 if depth >= 1 && h >= 1 => {
                let len = rng.below(6);
                let ls: Vec<usize> = (0..len).map(|_| rng.below(depth)).collect();
                return (Node::BrTable(ls, rng.below(depth)), None);
            }
            16 if rng.below(8) == 0 => {
                let k = rng.below(h.saturating_add(1));
                return (
                    Node::Exit(u32::try_from(rng.below(100)).unwrap_or(0), k),
                    None,
                );
            }
            _ => {}
        }
    }
}

/// A random body at height `h` that ends at height `target` (or never falls
/// through): up to a few instructions, then drops or constants to reach the
/// target.
fn gen_body(
    rng: &mut Rng,
    nl: usize,
    h: usize,
    depth: usize,
    nest: usize,
    target: usize,
) -> (Node, Option<usize>) {
    let steps = rng.below(7);
    let mut acc = nop();
    let mut cur = h;
    for _ in 0..steps {
        let (n, next) = gen_one(rng, nl, cur, depth, nest);
        acc = then(acc, n);
        match next {
            Some(x) => cur = x,
            None => return (acc, None),
        }
    }
    while cur > target {
        acc = then(acc, Node::Op(Op::Drop));
        cur = cur.saturating_sub(1);
    }
    while cur < target {
        acc = then(acc, c32(1));
        cur = cur.saturating_add(1);
    }
    (acc, Some(target))
}

#[test]
fn generated_programs_are_accepted() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    // Miri interprets every step, so it checks the first few programs of the
    // same sequence; the normal test job checks all of them.
    let rounds = if cfg!(miri) { 5usize } else { 1500usize };
    let mut longest = 0usize;
    let mut with_jumps = 0usize;
    for round in 0..rounds {
        let nl = rng.below(4);
        let (p, _) = gen_body(&mut rng, nl, 0, 1, 3, 0);
        let b = blob(&p, nl);
        assert!(b.is_some(), "round {round}: no blob ({nl} locals)");
        let b = b.unwrap_or_default();
        assert!(
            accepted(&b),
            "round {round}: refused ({nl} locals): {b:02x?}"
        );
        longest = longest.max(b.len());
        // a `jmp` or a `jcc` is in the blob (a crude count, but the programs
        // are not only straight-line code)
        if b.iter().any(|x| *x == 0xE9 || *x == 0x0F) {
            with_jumps = with_jumps.saturating_add(1);
        }
    }
    assert!(
        longest > if cfg!(miri) { 40 } else { 400 },
        "longest {longest}"
    );
    assert!(with_jumps > rounds / 4, "only {with_jumps} with jumps");
}

#[test]
fn no_translation_means_no_blob() {
    let load = |region| {
        Node::Mem(MemOp::Load {
            region,
            ty: MTy::I32,
        })
    };
    // region 16 is not in the table
    assert!(blob(&seq(vec![c64(0), load(16)]), 0).is_none());
    // no index to load
    assert!(blob(&load(0), 0).is_none());
    // a check of 0 or 9 bytes
    for size in [0usize, 9] {
        let p = seq(vec![
            c64(0),
            Node::Mem(MemOp::BoundsCheck {
                region: 0,
                size,
                code: 1,
            }),
        ]);
        assert!(blob(&p, 0).is_none(), "size {size}");
    }
    // store needs two operands
    let p = seq(vec![
        c64(0),
        Node::Mem(MemOp::Store {
            region: 0,
            ty: MTy::I64,
        }),
    ]);
    assert!(blob(&p, 0).is_none());
    // a branch past the outermost label
    assert!(blob(&Node::Br(1), 0).is_none());
    assert!(blob(&Node::Br(0), 0).is_some());
    // br_table: a label out of scope, a missing index
    assert!(blob(&seq(vec![c32(0), Node::BrTable(vec![0, 1], 0)]), 0).is_none());
    assert!(blob(&Node::BrTable(vec![], 0), 0).is_none());
    // too many targets
    let many: Vec<usize> = vec![0; 0x10001];
    assert!(blob(&seq(vec![c32(0), Node::BrTable(many, 0)]), 0).is_none());
    // `if` arms that leave different heights
    let p = seq(vec![c32(1), Node::If(Box::new(c32(1)), Box::new(nop()))]);
    assert!(blob(&p, 0).is_none());
    // a block that leaves a value
    assert!(blob(&Node::Block(Box::new(c32(1))), 0).is_none());
    // code after a branch
    assert!(blob(&then(Node::Br(0), c32(1)), 0).is_none());
    // a frame beyond 31 slots
    assert!(blob(&nop(), 32).is_none());
    assert!(blob(&nop(), 31).is_some());
}

#[test]
fn exit_with_operands_is_accepted() {
    let p = seq(vec![c64(1), c64(2), Node::Exit(42, 2)]);
    assert!(accepted(&blob(&p, 0).unwrap_or_default()));
}

#[test]
fn the_validator_refuses_a_broken_check() {
    let p = seq(vec![
        c64(3),
        Node::Mem(MemOp::Load {
            region: 0,
            ty: MTy::I64,
        }),
    ]);
    let b = blob(&p, 0).unwrap_or_default();
    assert!(accepted(&b));
    // the check begins `mov rdx, rcx` (3 bytes), `add rdx, 8` (7); then comes
    // `jb rel32` (`0f 82`), whose displacement follows
    let at = b
        .windows(2)
        .position(|w| w == [0x0f, 0x82])
        .unwrap_or(usize::MAX);
    assert_ne!(at, usize::MAX);
    // jump one byte further: into the middle of an instruction
    let mut moved = b.clone();
    if let Some(x) = moved.get_mut(at.saturating_add(2)) {
        *x = x.wrapping_add(1);
    }
    assert!(!accepted(&moved));
    // the check's second compare is the one that bounds the access: turn
    // `cmovae` (`0f 43`) into `cmovb` (`0f 42`) and the sequence is no
    // longer the check
    let mut broken = b.clone();
    let cm = b
        .windows(2)
        .position(|w| w == [0x0f, 0x43])
        .unwrap_or(usize::MAX);
    assert_ne!(cm, usize::MAX);
    if let Some(x) = broken.get_mut(cm.saturating_add(1)) {
        *x = 0x42;
    }
    assert!(!accepted(&broken));
    // cut the last byte
    assert!(!accepted(b.get(..b.len().saturating_sub(1)).unwrap_or(&[])));
}
