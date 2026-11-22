//! **The refinement of every templated node** ([`lemma_ctmpl_refines`]): by
//! induction on the node, from the leaves ([`super::cfop`], [`super::cfleaf`],
//! [`super::cfexit`], [`super::cfmemops`], [`super::cfbrt`]) and the
//! compositions ([`super::cfcompose`], [`super::cfblock`], [`super::cfif`]).
//! The induction also carries the size invariant ([`super::cffit::labels_fit`])
//! that every `b`, `b.cond`, `cbz` and `cbnz` displacement fits its field, and
//! with it that the code is in the subset. The A64 counterpart of
//! [`crate::cfproofs`].

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfblock::*;
#[cfg(verus_only)]
use super::cfbrt::*;
#[cfg(verus_only)]
use super::cfcompose::*;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cfexit::*;
#[cfg(verus_only)]
use super::cffit::*;
#[cfg(verus_only)]
use super::cfif::*;
#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cflens::*;
#[cfg(verus_only)]
use super::cfmemops::*;
#[cfg(verus_only)]
use super::cfop::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::cfvalid::*;
#[cfg(verus_only)]
use super::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The size of a node's code is a multiple of 4.
pub proof fn lemma_csize_mod4(n: Node, nl: nat, h: nat, depth: nat)
    ensures
        csize(n, nl, h, depth) % 4 == 0,
{
}

/// **Every templated node's code refines it, and is in the subset.** For a node
/// the analysis accepts and that has a template, entered at height `h` with
/// `nl` locals and the labels at the byte offsets `offs`, [`ctmpl`] refines it
/// ([`cf_refines`]), provided the code is small enough for its displacements
/// ([`labels_fit`]).
#[verifier::rlimit(1000)]
pub proof fn lemma_ctmpl_refines(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        templated(n),
        codes_ok(n),
        csize(n, nl, h, offs.len()) <= max_size(),
        labels_fit(offs, csize(n, nl, h, offs.len())),
    ensures
        cf_refines(n@, nl, h, offs, ctmpl(n, nl, h, offs)),
        all_valid_instrs(ctmpl(n, nl, h, offs)),
    decreases n,
{
    let d = offs.len();
    let size = csize(n, nl, h, d);
    lemma_ctmpl_len(n, nl, h, offs);
    super::steps::lemma_frame_agrees();
    match n {
        Node::Op(o) => {
            lemma_op_ok_agrees(o, nl, h);
            lemma_op_cf(o, nl, h, offs);
            super::tlemmas::lemma_tmpl_valid(o, nl, h);
        },
        Node::Mem(m) => {
            match m {
                MemOp::BoundsCheck { region, size, code } => {
                    lemma_bc_cf(region, size, code, nl, h, offs);
                },
                MemOp::Load { region, ty } => {
                    lemma_load_cf(region, ty, nl, h, offs);
                },
                MemOp::Store { region, ty } => {
                    lemma_store_cf(region, ty, nl, h, offs);
                },
            }
            lemma_mem_valid(m, nl, h);
        },
        Node::Then(a, b) => {
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    lemma_csize_then(*a, *b, nl, h, d);
                    assert(flow_h(*a, nl, h, d) == h1);
                    let sa = csize(*a, nl, h, d);
                    let sb = csize(*b, nl, h1, d);
                    lemma_csize_mod4(*a, nl, h, d);
                    lemma_fit_mono(offs, size, sa);
                    lemma_ctmpl_refines(*a, nl, h, offs);
                    let ob = shift(offs, sa as int);
                    lemma_fit_shift(offs, sa, size, sb);
                    assert(ob.len() == d);
                    lemma_ctmpl_refines(*b, nl, h1, ob);
                    lemma_ctmpl_len(*a, nl, h, offs);
                    lemma_then(
                        *a,
                        *b,
                        nl,
                        h,
                        h1,
                        offs,
                        ctmpl(*a, nl, h, offs),
                        ctmpl(*b, nl, h1, ob),
                    );
                    lemma_valid_cat(ctmpl(*a, nl, h, offs), ctmpl(*b, nl, h1, ob));
                },
                Some(Flow::Dead) => {
                    // the second is `nop`: no code
                    lemma_csize_then(*a, *b, nl, h, d);
                    lemma_fit_mono(offs, size, csize(*a, nl, h, d));
                    lemma_ctmpl_refines(*a, nl, h, offs);
                    lemma_then_dead(*a, nl, h, offs, ctmpl(*a, nl, h, offs));
                    assert(ctmpl(n, nl, h, offs) == ctmpl(*a, nl, h, offs) + ctmpl(
                        *b,
                        nl,
                        h,
                        shift(offs, csize(*a, nl, h, d) as int),
                    ));
                    assert(ctmpl(*b, nl, h, shift(offs, csize(*a, nl, h, d) as int)) =~= Seq::<
                        isa::Instr,
                    >::empty());
                    assert(ctmpl(*a, nl, h, offs) + Seq::<isa::Instr>::empty() =~= ctmpl(
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
            lemma_csize_block(*b, nl, h, d);
            let sb = csize(*b, nl, h, d + 1);
            let ob = seq![sb as int] + offs;
            lemma_csize_mod4(*b, nl, h, d + 1);
            lemma_fit_mono(offs, size, sb);
            lemma_fit_cons(sb as int, offs, sb);
            lemma_ctmpl_refines(*b, nl, h, ob);
            lemma_ctmpl_len(*b, nl, h, ob);
            lemma_block(*b, nl, h, offs, ctmpl(*b, nl, h, ob));
        },
        Node::Loop(b) => {
            lemma_csize_loop(*b, nl, h, d);
            let sb = csize(*b, nl, h, d + 1);
            let ob = seq![0int] + offs;
            lemma_fit_mono(offs, size, sb);
            lemma_fit_cons(0, offs, sb);
            lemma_ctmpl_refines(*b, nl, h, ob);
            lemma_loop(*b, nl, h, offs, ctmpl(*b, nl, h, ob));
        },
        Node::If(t, e) => {
            lemma_csize_if(*t, *e, nl, h, d);
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            lemma_csize_mod4(*t, nl, (h - 1) as nat, d + 1);
            lemma_csize_mod4(*e, nl, (h - 1) as nat, d + 1);
            let ot = seq![st + 4 + se] + shift(offs, 8);
            let oe = seq![se] + shift(offs, 12 + st);
            lemma_fit_shift(offs, 8, size, st as nat);
            lemma_fit_cons(st + 4 + se, shift(offs, 8), st as nat);
            lemma_fit_shift(offs, (12 + st) as nat, size, se as nat);
            lemma_fit_cons(se, shift(offs, 12 + st), se as nat);
            assert(cf_flow(*t, nl, (h - 1) as nat, d + 1) is Some);
            assert(cf_flow(*e, nl, (h - 1) as nat, d + 1) is Some);
            lemma_ctmpl_refines(*t, nl, (h - 1) as nat, ot);
            lemma_ctmpl_refines(*e, nl, (h - 1) as nat, oe);
            let ct = ctmpl(*t, nl, (h - 1) as nat, ot);
            let ce = ctmpl(*e, nl, (h - 1) as nat, oe);
            lemma_ctmpl_len(*t, nl, (h - 1) as nat, ot);
            lemma_ctmpl_len(*e, nl, (h - 1) as nat, oe);
            assert(code_len(ct) == st && code_len(ce) == se);
            assert(cond_len(nl, h) == 8) by {
                lemma_cond_pre_len(nl, h, true, 0);
            }
            assert(if_offs_t(nl, h, offs, ct, ce) == ot);
            assert(if_offs_e(nl, h, offs, ct, ce) == oe);
            lemma_if(*t, *e, nl, h, offs, ct, ce);
            assert(ctmpl(n, nl, h, offs) == if_code(nl, h, ct, ce));
            lemma_cond_pre_valid(nl, h, true, st + 8);
            lemma_b_valid(se + 4);
            let cp = cond_pre(nl, h, true, st + 8);
            let jm = seq![b_i(se + 4)];
            assert(all_valid_instrs(jm)) by {
                assert forall|j: int| 0 <= j < jm.len() implies isa::valid_instr(#[trigger] jm[j]) by {
                    assert(j == 0);
                }
            }
            lemma_valid_cat(cp, ct);
            lemma_valid_cat(cp + ct, jm);
            lemma_valid_cat(cp + ct + jm, ce);
        },
        Node::Br(l) => {
            lemma_csize_br(l, nl, h, d);
            assert(l < offs.len());
            lemma_br(nl, h, offs, l);
            lemma_b_valid(offs[l as int]);
            let c = ctmpl(n, nl, h, offs);
            assert(all_valid_instrs(c)) by {
                assert forall|j: int| 0 <= j < c.len() implies isa::valid_instr(#[trigger] c[j]) by {
                    assert(j == 0);
                }
            }
        },
        Node::BrIf(l) => {
            lemma_csize_brif(l, nl, h, d);
            lemma_brif(nl, h, offs, l);
            lemma_cond_pre_valid(nl, h, false, offs[l as int] - 4);
        },
        Node::BrTable(ls, d2) => {
            lemma_brt_len(ls@, d2, nl, h, offs);
            lemma_brt_cf(ls, d2, nl, h, offs);
            lemma_brt_valid(ls@, d2, nl, h, offs);
        },
        Node::Exit(c, k) => {
            lemma_exit_cf(c, k, nl, h, offs);
            super::tlemmas::lemma_exit_valid(c as u16);
        },
    }
}

} // verus!
