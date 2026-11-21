//! Every instruction the control-flow templates use is in the x86-64 subset
//! ([`x64::valid_instr`]): the emitter's blob is decoded by the validator
//! only if it is.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Valid code followed by valid code is valid.
pub proof fn lemma_valid_cat(a: Seq<x64::Instr>, b: Seq<x64::Instr>)
    requires
        all_valid_instrs(a),
        all_valid_instrs(b),
    ensures
        all_valid_instrs(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies x64::valid_instr(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// The condition test is valid code, when its slot is in the frame.
pub proof fn lemma_cond_pre_valid(nl: nat, h: nat, cc: u8, rel: int)
    requires
        1 <= h,
        nl + h <= max_slots(),
        cc < 16,
    ensures
        all_valid_instrs(cond_pre(nl, h, cc, rel)),
{
    crate::tlemmas::lemma_ls_valid(0, (nl + h - 1) as nat);
    let c = cond_pre(nl, h, cc, rel);
    assert forall|k: int| 0 <= k < c.len() implies x64::valid_instr(#[trigger] c[k]) by {
        assert(k == 0 || k == 1 || k == 2);
    }
}

/// **The code of every templated node is in the subset.**
pub proof fn lemma_ctmpl_valid(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        templated(n),
    ensures
        all_valid_instrs(ctmpl(n, nl, h, offs)),
    decreases n,
{
    let d = offs.len();
    match n {
        Node::Op(o) => {
            crate::tlemmas::lemma_tmpl_valid(o, nl, h);
        },
        Node::Mem(_) => {},
        Node::Then(a, b) => {
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    lemma_ctmpl_valid(*a, nl, h, offs);
                    let ob = shift(offs, csize(*a, nl, h, d) as int);
                    assert(ob.len() == d);
                    lemma_ctmpl_valid(*b, nl, h1, ob);
                    lemma_valid_cat(ctmpl(*a, nl, h, offs), ctmpl(*b, nl, h1, ob));
                },
                Some(Flow::Dead) => {
                    lemma_ctmpl_valid(*a, nl, h, offs);
                    let ob = shift(offs, csize(*a, nl, h, d) as int);
                    assert(ctmpl(*b, nl, h, ob) =~= Seq::<x64::Instr>::empty());
                    lemma_valid_cat(ctmpl(*a, nl, h, offs), Seq::empty());
                    assert(ctmpl(*a, nl, h, offs) + Seq::<x64::Instr>::empty() =~= ctmpl(
                        *a,
                        nl,
                        h,
                        offs,
                    ));
                },
                None => {},
            }
        },
        Node::Block(b) => {
            lemma_ctmpl_valid(*b, nl, h, seq![csize(*b, nl, h, d + 1) as int] + offs);
        },
        Node::Loop(b) => {
            lemma_ctmpl_valid(*b, nl, h, seq![0int] + offs);
        },
        Node::If(t, e) => {
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 5 + se] + shift(offs, p);
            let oe = seq![se] + shift(offs, p + st + 5);
            assert(ot.len() == d + 1 && oe.len() == d + 1);
            lemma_ctmpl_valid(*t, nl, (h - 1) as nat, ot);
            lemma_ctmpl_valid(*e, nl, (h - 1) as nat, oe);
            lemma_cond_pre_valid(nl, h, 4, st + 5);
            let cp = cond_pre(nl, h, 4, st + 5);
            let ct = ctmpl(*t, nl, (h - 1) as nat, ot);
            let ce = ctmpl(*e, nl, (h - 1) as nat, oe);
            let jm = seq![jmp_i(se)];
            assert(all_valid_instrs(jm));
            lemma_valid_cat(cp, ct);
            lemma_valid_cat(cp + ct, jm);
            lemma_valid_cat(cp + ct + jm, ce);
        },
        Node::Br(l) => {
            let c = ctmpl(n, nl, h, offs);
            assert(all_valid_instrs(c));
        },
        Node::BrIf(l) => {
            lemma_cond_pre_valid(
                nl,
                h,
                5,
                if l < offs.len() {
                    offs[l as int] - cond_len(nl, h) as int
                } else {
                    0
                },
            );
        },
        Node::BrTable(_, _) => {},
        Node::Exit(c, _) => {
            crate::tlemmas::lemma_exit_valid(c);
        },
    }
}

} // verus!
