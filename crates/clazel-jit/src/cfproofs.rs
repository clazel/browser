//! **The refinement of every templated node** ([`lemma_ctmpl_refines`]): by
//! induction on the node, from the leaves ([`crate::cfop`], [`crate::cfleaf`],
//! [`crate::cfexit`]) and the compositions ([`crate::cfcompose`],
//! [`crate::cfblock`], [`crate::cfif`]). The induction also carries the size
//! invariant that every `jmp` and `jcc` displacement is a 32-bit number.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfblock::*;
#[cfg(verus_only)]
use crate::cfcompose::*;
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cfexit::*;
#[cfg(verus_only)]
use crate::cfif::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfop::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::contract::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every label offset is far enough from every place a jump in code of
/// `size` bytes can be, that the displacement is a 32-bit number: from a
/// jump ending at most `size + 5` bytes in, to a label at `o`, is `o - (size +
/// 5) >= -2^31` and `o <= 2^31 - 1`.
pub open spec fn labels_fit(offs: Seq<int>, size: nat) -> bool {
    forall|l: int|
        0 <= l < offs.len() ==> -0x8000_0000 + size + 6 <= #[trigger] offs[l] && offs[l]
            <= 0x7FFF_FFFF
}

/// Labels seen from code that starts `d` bytes in, for a smaller piece.
pub proof fn lemma_fit_shift(offs: Seq<int>, d: nat, size: nat, size2: nat)
    requires
        labels_fit(offs, size),
        d + size2 <= size,
    ensures
        labels_fit(shift(offs, d as int), size2),
{
    assert forall|l: int| 0 <= l < shift(offs, d as int).len() implies -0x8000_0000 + size2 + 6
        <= #[trigger] shift(offs, d as int)[l] && shift(offs, d as int)[l] <= 0x7FFF_FFFF by {
        lemma_shift_index(offs, d as int, l);
    }
}

/// A new label in front.
pub proof fn lemma_fit_cons(x: int, offs: Seq<int>, size: nat)
    requires
        labels_fit(offs, size),
        -0x8000_0000 + size + 6 <= x <= 0x7FFF_FFFF,
    ensures
        labels_fit(seq![x] + offs, size),
{
    let all = seq![x] + offs;
    assert forall|l: int| 0 <= l < all.len() implies -0x8000_0000 + size + 6 <= #[trigger] all[l]
        && all[l] <= 0x7FFF_FFFF by {
        if l > 0 {
            assert(all[l] == offs[l - 1]);
        }
    }
}

/// `labels_fit` for a smaller size.
pub proof fn lemma_fit_mono(offs: Seq<int>, size: nat, size2: nat)
    requires
        labels_fit(offs, size),
        size2 <= size,
    ensures
        labels_fit(offs, size2),
{
}

/// **Every templated node's code refines it.** For a node the analysis
/// accepts and that has a template, entered at height `h` with `nl` locals
/// and the labels at the byte offsets `offs`, [`ctmpl`] refines it
/// ([`cf_refines`]), provided the code is small enough for its displacements
/// ([`labels_fit`]).
#[verifier::rlimit(1000)]
pub proof fn lemma_ctmpl_refines(n: Node, nl: nat, h: nat, offs: Seq<int>)
    requires
        cf_flow(n, nl, h, offs.len()) is Some,
        templated(n),
        csize(n, nl, h, offs.len()) <= max_size(),
        labels_fit(offs, csize(n, nl, h, offs.len())),
    ensures
        cf_refines(n@, nl, h, offs, ctmpl(n, nl, h, offs)),
    decreases n,
{
    let d = offs.len();
    let size = csize(n, nl, h, d);
    lemma_ctmpl_len(n, nl, h, offs);
    match n {
        Node::Op(o) => {
            lemma_op_cf(o, nl, h, offs);
        },
        Node::Mem(_) => {},
        Node::Then(a, b) => {
            match cf_flow(*a, nl, h, d) {
                Some(Flow::Falls(h1)) => {
                    lemma_csize_then(*a, *b, nl, h, d);
                    assert(flow_h(*a, nl, h, d) == h1);
                    let sa = csize(*a, nl, h, d);
                    let sb = csize(*b, nl, h1, d);
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
                        x64::Instr,
                    >::empty());
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
            lemma_csize_block(*b, nl, h, d);
            let sb = csize(*b, nl, h, d + 1);
            let ob = seq![sb as int] + offs;
            lemma_fit_cons(sb as int, offs, sb);
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
            let p = cond_len(nl, h) as int;
            let st = csize(*t, nl, (h - 1) as nat, d + 1) as int;
            let se = csize(*e, nl, (h - 1) as nat, d + 1) as int;
            let ot = seq![st + 5 + se] + shift(offs, p);
            let oe = seq![se] + shift(offs, p + st + 5);
            lemma_fit_shift(offs, p as nat, size, st as nat);
            lemma_fit_cons(st + 5 + se, shift(offs, p), st as nat);
            lemma_fit_shift(offs, (p + st + 5) as nat, size, se as nat);
            lemma_fit_cons(se, shift(offs, p + st + 5), se as nat);
            assert(cf_flow(*t, nl, (h - 1) as nat, d + 1) is Some);
            assert(cf_flow(*e, nl, (h - 1) as nat, d + 1) is Some);
            lemma_ctmpl_refines(*t, nl, (h - 1) as nat, ot);
            lemma_ctmpl_refines(*e, nl, (h - 1) as nat, oe);
            let ct = ctmpl(*t, nl, (h - 1) as nat, ot);
            let ce = ctmpl(*e, nl, (h - 1) as nat, oe);
            lemma_ctmpl_len(*t, nl, (h - 1) as nat, ot);
            lemma_ctmpl_len(*e, nl, (h - 1) as nat, oe);
            assert(code_len(ct) == st && code_len(ce) == se);
            assert(if_offs_t(nl, h, offs, ct, ce) == ot);
            assert(if_offs_e(nl, h, offs, ct, ce) == oe);
            lemma_if(*t, *e, nl, h, offs, ct, ce);
            assert(ctmpl(n, nl, h, offs) == if_code(nl, h, ct, ce));
        },
        Node::Br(l) => {
            lemma_csize_br(l, nl, h, d);
            assert(l < offs.len());
            lemma_br(nl, h, offs, l);
        },
        Node::BrIf(l) => {
            lemma_csize_brif(l, nl, h, d);
            lemma_brif(nl, h, offs, l);
        },
        Node::BrTable(_, _) => {},
        Node::Exit(c, k) => {
            lemma_exit_cf(c, k, nl, h, offs);
        },
    }
}

} // verus!
