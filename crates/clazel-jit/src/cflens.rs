//! The lengths of the control-flow templates: a jump's length does not depend
//! on its displacement, so [`csize`] is the length of [`ctmpl`] whatever the
//! labels' offsets are.

use crate::cfspec::*;
use crate::cftemplates::*;
use crate::spec::*;
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `le_bytes(v, n)` has `n` bytes.
pub proof fn lemma_le_bytes_len(v: int, n: nat)
    ensures
        x64::le_bytes(v, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_le_bytes_len(v / 256, (n - 1) as nat);
    }
}

/// `jmp rel32` is 5 bytes.
pub proof fn lemma_jmp_len(rel: int)
    ensures
        x64::instr_len(jmp_i(rel)) == 5,
{
    lemma_le_bytes_len(rel as i32 as int, 4);
    assert(x64::encode(jmp_i(rel)) == seq![0xE9u8] + x64::le_bytes(rel as i32 as int, 4));
}

/// `jcc rel32` is 6 bytes.
pub proof fn lemma_jcc_len(cc: u8, rel: int)
    ensures
        x64::instr_len(jcc_i(cc, rel)) == 6,
{
    lemma_le_bytes_len(rel as i32 as int, 4);
    assert(x64::encode(jcc_i(cc, rel)) == seq![0x0Fu8, (0x80 + cc as int) as u8] + x64::le_bytes(
        rel as i32 as int,
        4,
    ));
}

/// The condition test's length does not depend on `cc` or `rel`.
pub proof fn lemma_cond_pre_len(nl: nat, h: nat, cc: u8, rel: int)
    ensures
        code_len(cond_pre(nl, h, cc, rel)) == cond_len(nl, h),
{
    let a = load_slot(rax(), (nl + h - 1) as nat);
    let b = x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() };
    lemma_jcc_len(cc, rel);
    lemma_jcc_len(0, 0);
    super::runseq::lemma_len3(a, b, jcc_i(cc, rel));
    super::runseq::lemma_len3(a, b, jcc_i(0, 0));
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
            super::runseq::lemma_code_len_append(ctmpl(*a, nl, h, o1), ctmpl(*b, nl, h1, shift(o1, d)));
            super::runseq::lemma_code_len_append(ctmpl(*a, nl, h, o2), ctmpl(*b, nl, h1, shift(o2, d)));
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
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, o1.len() + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, o1.len() + 1) as int;
            let t1 = seq![st + 5 + se] + shift(o1, p);
            let t2 = seq![st + 5 + se] + shift(o2, p);
            let e1 = seq![se] + shift(o1, p + st + 5);
            let e2 = seq![se] + shift(o2, p + st + 5);
            lemma_ctmpl_len_eq(*t, nl, (h - 1) as nat, t1, t2);
            lemma_ctmpl_len_eq(*e, nl, (h - 1) as nat, e1, e2);
            lemma_cond_pre_len(nl, h, 4, st + 5);
            lemma_jmp_len(se);
            let cp = cond_pre(nl, h, 4, st + 5);
            let ct1 = ctmpl(*t, nl, (h - 1) as nat, t1);
            let ct2 = ctmpl(*t, nl, (h - 1) as nat, t2);
            let ce1 = ctmpl(*e, nl, (h - 1) as nat, e1);
            let ce2 = ctmpl(*e, nl, (h - 1) as nat, e2);
            super::runseq::lemma_code_len_append(cp, ct1);
            super::runseq::lemma_code_len_append(cp + ct1, seq![jmp_i(se)]);
            super::runseq::lemma_code_len_append(cp + ct1 + seq![jmp_i(se)], ce1);
            super::runseq::lemma_code_len_append(cp, ct2);
            super::runseq::lemma_code_len_append(cp + ct2, seq![jmp_i(se)]);
            super::runseq::lemma_code_len_append(cp + ct2 + seq![jmp_i(se)], ce2);
            super::runseq::lemma_code_len_one(jmp_i(se));
        },
        Node::Br(l) => {
            lemma_jmp_len(if l < o1.len() { o1[l as int] - 5 } else { 0 });
            lemma_jmp_len(if l < o2.len() { o2[l as int] - 5 } else { 0 });
            super::runseq::lemma_code_len_one(jmp_i(if l < o1.len() { o1[l as int] - 5 } else { 0 }));
            super::runseq::lemma_code_len_one(jmp_i(if l < o2.len() { o2[l as int] - 5 } else { 0 }));
        },
        Node::BrIf(l) => {
            lemma_cond_pre_len(nl, h, 5, if l < o1.len() { o1[l as int] - cond_len(nl, h) as int } else { 0 });
            lemma_cond_pre_len(nl, h, 5, if l < o2.len() { o2[l as int] - cond_len(nl, h) as int } else { 0 });
        },
        Node::BrTable(_, _) => {},
        Node::Exit(c, _) => {},
    }
}

/// [`csize`] is the length of the code, for any labels.
pub proof fn lemma_ctmpl_len(n: Node, nl: nat, h: nat, offs: Seq<int>)
    ensures
        code_len(ctmpl(n, nl, h, offs)) == csize(n, nl, h, offs.len()),
{
    lemma_ctmpl_len_eq(n, nl, h, offs, Seq::new(offs.len(), |i: int| 0int));
}

} // verus!
