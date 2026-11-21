//! The control-flow back end never produces a blob the validator refuses
//! (docs/phases/jit.md J.9). Like `validator.rs` for the straight-line slice:
//! the blob is the encoded code of `emit_cf_blob` and the exit sequence, the
//! validator is `clazel-codecheck`'s executable one, entered at offset 0.
//!
//! 1. **Each form.** `block`, `loop`, `if`, `br`, `br_if`, `exit` with and
//!    without operands, nested, branching to outer labels.
//! 2. **Generated programs.** Random well-typed programs of nested control
//!    flow (a fixed seed), each of which must have an accepted blob.
//! 3. **What has no template is refused by the back end, not emitted**: the
//!    memory instructions, `br_table`, a label out of scope, code after a
//!    `br`, a block that leaves its height changed.
//! 4. **Controls.** The validator does refuse a blob whose last byte is
//!    cut off, and one whose first jump is moved off an instruction boundary.
//!
//! This is evidence, not proof (see `validator.rs`): the meaning of the code
//! is `cfproofs::lemma_ctmpl_refines`, and `emit_cf_body` is proven to return
//! the code that lemma is about.

use clazel_codecheck::validate::validate;
use clazel_jit::cfemit::emit_cf_blob;
use clazel_jit::cfspec::{MTy, MemOp, Node};
use clazel_jit::spec::Op;
use clazel_lir::spec::{BinOp, IBin, Val};

fn then(a: Node, b: Node) -> Node {
    Node::Then(Box::new(a), Box::new(b))
}

/// The instructions one after the other: `((nop; i0); i1); ...`.
fn seq(items: Vec<Node>) -> Node {
    items.into_iter().fold(Node::Op(Op::Nop), then)
}

fn block(b: Node) -> Node {
    Node::Block(Box::new(b))
}

fn lp(b: Node) -> Node {
    Node::Loop(Box::new(b))
}

fn iff(t: Node, e: Node) -> Node {
    Node::If(Box::new(t), Box::new(e))
}

fn c32(c: u32) -> Node {
    Node::Op(Op::Const(Val::I32(c)))
}

fn drop_() -> Node {
    Node::Op(Op::Drop)
}

fn blob(n: &Node, nl: usize) -> Option<Vec<u8>> {
    emit_cf_blob(n, nl, 7)
}

fn accepted(b: &[u8]) -> bool {
    validate(b, &[0])
}

fn assert_accepted(n: &Node, nl: usize, what: &str) {
    let b = blob(n, nl);
    assert!(b.is_some(), "no blob for {what}");
    let b = b.unwrap_or_default();
    assert!(accepted(&b), "the validator refuses {what}: {b:02x?}");
}

#[test]
fn each_form_is_accepted() {
    // a block that is branched out of, and falls out of
    assert_accepted(&block(seq(vec![Node::Br(0)])), 0, "block; br 0");
    assert_accepted(&block(seq(vec![c32(1), drop_()])), 0, "block with a body");
    // a loop that is branched back to on a condition
    assert_accepted(
        &lp(seq(vec![c32(1), drop_(), c32(0), Node::BrIf(0)])),
        0,
        "loop; br_if 0",
    );
    // an infinite loop
    assert_accepted(&lp(seq(vec![Node::Br(0)])), 0, "loop; br 0");
    // if and else
    assert_accepted(
        &seq(vec![
            c32(5),
            iff(seq(vec![c32(1), drop_()]), seq(vec![c32(2), drop_()])),
        ]),
        0,
        "if/else",
    );
    // an if whose arms branch out of it, and past it
    assert_accepted(
        &block(seq(vec![
            c32(5),
            iff(seq(vec![Node::Br(1)]), seq(vec![Node::Br(0)])),
        ])),
        0,
        "if with branches",
    );
    // branches to the return label, from inside nested blocks
    assert_accepted(
        &block(block(seq(vec![c32(1), Node::BrIf(2), Node::Br(1)]))),
        0,
        "br_if to return",
    );
    // exit with and without operands
    assert_accepted(&seq(vec![Node::Exit(9, 0)]), 0, "exit");
    assert_accepted(&seq(vec![c32(3), c32(4), Node::Exit(9, 2)]), 0, "exit 2");
    assert_accepted(
        &block(seq(vec![c32(3), Node::Exit(9, 1)])),
        0,
        "exit inside a block",
    );
    // locals and arithmetic inside
    assert_accepted(
        &lp(seq(vec![
            Node::Op(Op::LocalGet(0)),
            Node::Op(Op::Const(Val::I32(1))),
            Node::Op(Op::Bin(BinOp::I32(IBin::Add))),
            Node::Op(Op::LocalTee(0)),
            Node::BrIf(0),
        ])),
        1,
        "a counting loop",
    );
}

#[test]
fn what_has_no_template_is_refused() {
    // a label out of scope (only the return label, 0, exists at the top)
    assert!(blob(&Node::Br(1), 0).is_none());
    assert!(blob(&seq(vec![c32(1), Node::BrIf(1)]), 0).is_none());
    // code after a branch
    assert!(blob(&seq(vec![Node::Br(0), c32(1)]), 0).is_none());
    assert!(blob(&seq(vec![Node::Exit(1, 0), Node::Br(0)]), 0).is_none());
    // br_if without a condition
    assert!(blob(&Node::BrIf(0), 0).is_none());
    // a block that leaves the stack higher than it found it
    assert!(blob(&block(seq(vec![c32(1)])), 0).is_none());
    // an if with the wrong arms
    assert!(blob(&iff(seq(vec![]), seq(vec![])), 0).is_none());
    // the memory instructions and br_table have no template yet
    assert!(
        blob(
            &Node::Mem(MemOp::Load {
                region: 0,
                ty: MTy::I32
            }),
            0
        )
        .is_none()
    );
    assert!(blob(&Node::BrTable(vec![0], 0), 0).is_none());
    // an exit with more operands than the stack has
    assert!(blob(&Node::Exit(1, 1), 0).is_none());
    // a frame of more than 31 slots
    assert!(blob(&Node::Op(Op::Nop), 32).is_none());
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

/// A random body, at stack height 0 and with `labels` labels in scope, that
/// leaves the height as it found it or ends in a branch or an exit: a list of
/// height-neutral statements, ended early by a terminator.
fn gen_body(rng: &mut Rng, labels: usize, nest: usize, nl: usize) -> Node {
    let n = rng.below(5).saturating_add(1);
    let mut items: Vec<Node> = Vec::new();
    for _ in 0..n {
        let kinds = if nest == 0 { 5 } else { 9 };
        match rng.below(kinds) {
            0 => {
                items.push(c32(u32::try_from(rng.next() & 0xffff).unwrap_or(0)));
                items.push(drop_());
            }
            1 => {
                items.push(c32(1));
                items.push(c32(2));
                items.push(Node::Op(Op::Bin(BinOp::I32(IBin::Add))));
                items.push(drop_());
            }
            2 => {
                if nl >= 2 {
                    items.push(Node::Op(Op::LocalGet(0)));
                    items.push(Node::Op(Op::LocalSet(1)));
                }
            }
            3 => {
                // a conditional branch to any label in scope
                items.push(c32(u32::try_from(rng.next() & 3).unwrap_or(0)));
                items.push(Node::BrIf(rng.below(labels)));
            }
            4 => {
                // an unconditional branch, or an exit: ends the body
                if rng.below(2) == 0 {
                    items.push(Node::Br(rng.below(labels)));
                } else {
                    items.push(Node::Exit(u32::try_from(rng.below(100)).unwrap_or(0), 0));
                }
                break;
            }
            5 => items.push(block(gen_body(
                rng,
                labels.saturating_add(1),
                nest.saturating_sub(1),
                nl,
            ))),
            6 => items.push(lp(gen_body(
                rng,
                labels.saturating_add(1),
                nest.saturating_sub(1),
                nl,
            ))),
            7 => {
                items.push(c32(u32::try_from(rng.next() & 1).unwrap_or(0)));
                items.push(iff(
                    gen_body(rng, labels.saturating_add(1), nest.saturating_sub(1), nl),
                    gen_body(rng, labels.saturating_add(1), nest.saturating_sub(1), nl),
                ));
            }
            _ => {
                // an exit with an operand
                items.push(c32(3));
                items.push(Node::Exit(u32::try_from(rng.below(100)).unwrap_or(0), 1));
                break;
            }
        }
    }
    seq(items)
}

#[test]
fn generated_programs_are_accepted() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let count = if cfg!(miri) { 12usize } else { 1500usize };
    let mut accepted_count = 0usize;
    for k in 0..count {
        let nl = rng.below(4);
        let prog = gen_body(&mut rng, 1, 3, nl);
        let b = blob(&prog, nl);
        assert!(b.is_some(), "no blob for generated program {k}");
        let b = b.unwrap_or_default();
        assert!(
            accepted(&b),
            "the validator refuses generated program {k}: {b:02x?}"
        );
        accepted_count = accepted_count.saturating_add(1);
    }
    assert_eq!(accepted_count, count);
}

#[test]
fn the_validator_refuses_a_cut_blob() {
    let n = block(seq(vec![c32(1), Node::BrIf(0), Node::Br(1)]));
    let b = blob(&n, 0).unwrap_or_default();
    assert!(accepted(&b));
    // cut off the `ret`
    assert!(!accepted(b.get(..b.len().saturating_sub(1)).unwrap_or(&[])));
    // a conditional jump whose displacement is changed to land inside an
    // instruction: find the `jne rel32` (0f 85) and bump its displacement
    let mut moved = b.clone();
    let at = moved.windows(2).position(|w| w == [0x0f, 0x85]);
    assert!(at.is_some(), "no jne in the blob");
    if let Some(i) = at {
        if let Some(byte) = moved.get_mut(i.saturating_add(2)) {
            *byte = byte.wrapping_add(1);
        }
    }
    assert!(
        !accepted(&moved),
        "a jump into the middle of an instruction is accepted"
    );
}
