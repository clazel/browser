//! The lengths of the control-flow templates: every A64 instruction is 4
//! bytes, so [`csize`] is the length of [`ctmpl`] whatever the labels' offsets
//! are. The A64 counterpart of [`crate::cflens`].

#[cfg(verus_only)]
use super::cfbrt::*;
#[cfg(verus_only)]
use super::cfif::lemma_cond_pre_len;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of `br_table`'s code does not depend on the labels.
pub proof fn lemma_brt_len(ls: Seq<usize>, d: usize, nl: nat, h: nat, offs: Seq<int>)
    ensures
        code_len(brt_code(ls, d, nl, h, offs)) == 8 + 12 * ls.len(),
{
    lemma_brt_shape(ls, d, nl, h, offs);
}

/// The length of a node's code does not depend on the values of the label
/// offsets, only on their number.
pub proof fn lemma_ctmpl_len_eq(n: Node, nl: nat, h: nat, o1: Seq<int>, o2: Seq<int>)
    requires
        o1.len() == o2.len(),
    ensures
        code_len(ctmpl(n, nl, h, o1)) == code_len(ctmpl(n, nl, h, o2)),
    decreases n,
{
    match n {
        Node::Op(o) => {},
        Node::Mem(_) => {},
        Node::Then(a, b) => {
            lemma_ctmpl_len_eq(*a, nl, h, o1, o2);
            let d = csize(*a, nl, h, o1.len()) as int;
            let h1 = flow_h(*a, nl, h, o1.len());
            assert(shift(o1, d).len() == shift(o2, d).len());
            lemma_ctmpl_len_eq(*b, nl, h1, shift(o1, d), shift(o2, d));
        },
        Node::Block(b) => {
            let s1 = seq![csize(*b, nl, h, o1.len() + 1) as int] + o1;
            let s2 = seq![csize(*b, nl, h, o2.len() + 1) as int] + o2;
            lemma_ctmpl_len_eq(*b, nl, h, s1, s2);
        },
        Node::Loop(b) => {
            lemma_ctmpl_len_eq(*b, nl, h, seq![0int] + o1, seq![0int] + o2);
        },
        Node::If(t, e) => {
            let st = csize(*t, nl, (h - 1) as nat, o1.len() + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, o1.len() + 1) as int;
            let t1 = seq![st + 4 + se] + shift(o1, 8);
            let t2 = seq![st + 4 + se] + shift(o2, 8);
            let e1 = seq![se] + shift(o1, 12 + st);
            let e2 = seq![se] + shift(o2, 12 + st);
            lemma_ctmpl_len_eq(*t, nl, (h - 1) as nat, t1, t2);
            lemma_ctmpl_len_eq(*e, nl, (h - 1) as nat, e1, e2);
        },
        Node::Br(l) => {},
        Node::BrIf(l) => {},
        Node::BrTable(ls, d) => {
            lemma_brt_len(ls@, d, nl, h, o1);
            lemma_brt_len(ls@, d, nl, h, o2);
        },
        Node::Exit(c, _) => {},
    }
}

/// [`csize`] is the length of the code, for any labels.
pub proof fn lemma_ctmpl_len(n: Node, nl: nat, h: nat, offs: Seq<int>)
    ensures
        code_len(ctmpl(n, nl, h, offs)) == csize(n, nl, h, offs.len()),
{
    lemma_ctmpl_len_eq(n, nl, h, offs, zeros(offs.len()));
}

/// `csize` of `then`: the first's, and the second's at the height the first
/// leaves.
pub proof fn lemma_csize_then(a: Node, b: Node, nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::Then(Box::new(a), Box::new(b)), nl, h, depth) == csize(a, nl, h, depth)
            + csize(b, nl, flow_h(a, nl, h, depth), depth),
{
    let z = zeros(depth);
    let d = csize(a, nl, h, depth) as int;
    let h1 = flow_h(a, nl, h, depth);
    assert(z.len() == depth);
    lemma_ctmpl_len(b, nl, h1, shift(z, d));
    assert(shift(z, d).len() == depth);
}

/// `csize` of `block`: the body's, one label deeper.
pub proof fn lemma_csize_block(b: Node, nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::Block(Box::new(b)), nl, h, depth) == csize(b, nl, h, depth + 1),
{
    let z = zeros(depth);
    lemma_ctmpl_len(b, nl, h, seq![csize(b, nl, h, depth + 1) as int] + z);
    assert((seq![csize(b, nl, h, depth + 1) as int] + z).len() == depth + 1);
}

/// `csize` of `loop`: the body's, one label deeper.
pub proof fn lemma_csize_loop(b: Node, nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::Loop(Box::new(b)), nl, h, depth) == csize(b, nl, h, depth + 1),
{
    let z = zeros(depth);
    lemma_ctmpl_len(b, nl, h, seq![0int] + z);
    assert((seq![0int] + z).len() == depth + 1);
}

/// `csize` of `br`: one `b`.
pub proof fn lemma_csize_br(l: usize, nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::Br(l), nl, h, depth) == 4,
{
}

/// `csize` of `br_if`: the condition test.
pub proof fn lemma_csize_brif(l: usize, nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::BrIf(l), nl, h, depth) == 8,
{
    let z = zeros(depth);
    lemma_cond_pre_len(
        nl,
        h,
        false,
        if l < z.len() {
            z[l as int] - 4
        } else {
            0
        },
    );
}

/// `csize` of `if`: the test, the first arm, a `b`, the second arm.
pub proof fn lemma_csize_if(t: Node, e: Node, nl: nat, h: nat, depth: nat)
    requires
        1 <= h,
    ensures
        csize(Node::If(Box::new(t), Box::new(e)), nl, h, depth) == 8 + csize(
            t,
            nl,
            (h - 1) as nat,
            depth + 1,
        ) + 4 + csize(e, nl, (h - 1) as nat, depth + 1),
{
    let z = zeros(depth);
    let st = csize(t, nl, (h - 1) as nat, depth + 1) as int;
    let se = csize(e, nl, (h - 1) as nat, depth + 1) as int;
    let ot = seq![st + 4 + se] + shift(z, 8);
    let oe = seq![se] + shift(z, 12 + st);
    lemma_ctmpl_len(t, nl, (h - 1) as nat, ot);
    lemma_ctmpl_len(e, nl, (h - 1) as nat, oe);
    assert(ot.len() == depth + 1);
    assert(oe.len() == depth + 1);
}

} // verus!
