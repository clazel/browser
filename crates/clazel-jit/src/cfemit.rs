//! The executable emitter for structured control flow: [`emit_cf_body`]
//! returns exactly [`ctmpl`] of the program (so the refinement proof of
//! [`crate::cfproofs::lemma_ctmpl_refines`] is about what it returns), and
//! [`emit_cf_blob`] encodes it with `clazel-x64`'s proven encoder and appends
//! the exit sequence, like the straight-line emitter.
//!
//! Three recursive functions walk the program: [`ex_flow`] (the analysis,
//! [`cf_flow`]), [`ex_size`] (the code's length, [`csize`], saturating at
//! [`cap`]) and [`emit_cf`] (the code, [`ctmpl`]); the last two read the
//! labels as a vector of offsets.

use crate::cfcontract::*;
use crate::cfproofs::*;
use crate::cfspec::*;
use crate::cftemplates::*;
use crate::contract::*;
use crate::emit::*;
use crate::spec::*;
use crate::templates::*;
use clazel_x64::encoder::encode_exec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The view of an offsets vector: the labels as `int`s.
pub open spec fn ov(v: Seq<i64>) -> Seq<int> {
    v.map_values(|x: i64| x as int)
}

/// The saturation point of [`ex_size`].
pub open spec fn cap() -> nat {
    0x4000_0000
}

/// The smaller of two numbers.
pub open spec fn mn(a: nat, b: nat) -> nat {
    if a < b {
        a
    } else {
        b
    }
}

// ----------------------------------------------------------------------------
// Instructions
// ----------------------------------------------------------------------------

/// The length in bytes of an instruction in the subset.
fn ilen(i: &x64::Instr) -> (r: usize)
    requires
        x64::valid_instr(*i),
    ensures
        r == x64::instr_len(*i),
{
    let e = encode_exec(i);
    proof {
        assert(e@ =~= x64::encode(*i));
    }
    e.len()
}

/// The length of a list of valid instructions, saturating at [`cap`].
fn ex_len(v: &Vec<x64::Instr>) -> (r: usize)
    requires
        all_valid_instrs(v@),
    ensures
        r == mn(code_len(v@), cap()),
        r <= 0x4000_0000,
{
    let mut k: usize = 0;
    let mut acc: usize = 0;
    proof {
        assert(v@.take(0) =~= Seq::<x64::Instr>::empty());
    }
    while k < v.len()
        invariant
            k <= v.len(),
            all_valid_instrs(v@),
            acc == mn(code_len(v@.take(k as int)), cap()),
            acc <= 0x4000_0000,
        decreases v.len() - k,
    {
        let l = ilen(&v[k]);
        proof {
            let t = v@.take(k as int + 1);
            assert(t.drop_last() =~= v@.take(k as int));
            assert(t.last() == v@[k as int]);
            lemma_code_len_snoc(v@.take(k as int), v@[k as int]);
            assert(t =~= v@.take(k as int).push(v@[k as int]));
        }
        acc = if acc.saturating_add(l) > 0x4000_0000 {
            0x4000_0000
        } else {
            acc.saturating_add(l)
        };
        k = k + 1;
    }
    proof {
        assert(v@.take(v@.len() as int) =~= v@);
    }
    acc
}

/// `code_len` of a list with one more instruction.
pub proof fn lemma_code_len_snoc(s: Seq<x64::Instr>, i: x64::Instr)
    ensures
        code_len(s.push(i)) == code_len(s) + x64::instr_len(i),
{
    assert(s.push(i) =~= s + seq![i]);
    crate::runseq::lemma_code_len_append(s, seq![i]);
    crate::runseq::lemma_code_len_one(i);
}

/// Append `cond_pre(nl, h, cc, rel)`: the condition test.
fn ex_cond_pre(nl: usize, h: usize, cc: u8, rel: i32, out: &mut Vec<x64::Instr>)
    requires
        1 <= h,
        nl + h <= 31,
    ensures
        final(out)@ == old(out)@ + cond_pre(nl as nat, h as nat, cc, rel as int),
{
    let ghost old_out = out@;
    let j = nl + h - 1;
    out.push(ex_load(0, j));
    out.push(x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 });
    out.push(x64::Instr::Jcc { cc, rel });
    proof {
        assert(out@ =~= old_out + cond_pre(nl as nat, h as nat, cc, rel as int));
    }
}

/// The length of the condition test, as [`cond_len`].
fn ex_cond_len(nl: usize, h: usize) -> (r: usize)
    requires
        1 <= h,
        nl + h <= 31,
    ensures
        r == mn(cond_len(nl as nat, h as nat), cap()),
        r <= 0x4000_0000,
{
    let mut v: Vec<x64::Instr> = Vec::new();
    ex_cond_pre(nl, h, 0, 0, &mut v);
    proof {
        crate::cfvalid::lemma_cond_pre_valid(nl as nat, h as nat, 0, 0);
        assert(0 as i32 as int == 0);
        crate::cflens::lemma_cond_pre_len(nl as nat, h as nat, 0, 0);
        assert(v@ == cond_pre(nl as nat, h as nat, 0, 0));
    }
    ex_len(&v)
}

// ----------------------------------------------------------------------------
// Offset vectors
// ----------------------------------------------------------------------------

/// The labels, `d` bytes further on.
fn shift_vec(offs: &Vec<i64>, d: i64) -> (r: Vec<i64>)
    requires
        forall|i: int| 0 <= i < offs@.len() ==> -0x1_0000_0000 < #[trigger] offs@[i] < 0x1_0000_0000,
        0 <= d <= 0x4000_0000,
    ensures
        ov(r@) == shift(ov(offs@), d as int),
{
    let mut r: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < offs.len()
        invariant
            k <= offs.len(),
            r@.len() == k,
            forall|i: int| 0 <= i < offs@.len() ==> -0x1_0000_0000 < #[trigger] offs@[i] < 0x1_0000_0000,
            0 <= d <= 0x4000_0000,
            forall|i: int| 0 <= i < k ==> #[trigger] r@[i] == offs@[i] - d,
        decreases offs.len() - k,
    {
        r.push(offs[k] - d);
        k = k + 1;
    }
    proof {
        assert(ov(r@) =~= shift(ov(offs@), d as int));
    }
    r
}

/// A new label in front.
fn cons_vec(x: i64, offs: &Vec<i64>) -> (r: Vec<i64>)
    ensures
        ov(r@) == seq![x as int] + ov(offs@),
        r@.len() == offs@.len() + 1,
        r@[0] == x,
        forall|i: int| 0 <= i < offs@.len() ==> #[trigger] r@[i + 1] == offs@[i],
{
    let mut r: Vec<i64> = Vec::new();
    r.push(x);
    let mut k: usize = 0;
    while k < offs.len()
        invariant
            k <= offs.len(),
            r@.len() == k + 1,
            r@[0] == x,
            forall|i: int| 0 <= i < k ==> #[trigger] r@[i + 1] == offs@[i],
        decreases offs.len() - k,
    {
        r.push(offs[k]);
        k = k + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < r@.len() implies #[trigger] ov(r@)[i] == (seq![x as int]
            + ov(offs@))[i] by {
            if i > 0 {
                assert(r@[(i - 1) + 1] == offs@[i - 1]);
                assert((i - 1) + 1 == i);
            }
        }
        assert(ov(r@) =~= seq![x as int] + ov(offs@));
    }
    r
}

// ----------------------------------------------------------------------------
// The analysis
// ----------------------------------------------------------------------------

/// The nesting depth ([`nest`]), saturating at `2^28`.
fn ex_nest(n: &Node) -> (r: usize)
    ensures
        r == if nest(*n) < 0x1000_0000 {
            nest(*n)
        } else {
            0x1000_0000nat
        },
    decreases *n,
{
    match n {
        Node::Then(a, b) => {
            let x = ex_nest(a);
            let y = ex_nest(b);
            if x > y {
                x
            } else {
                y
            }
        },
        Node::Block(b) => {
            let x = ex_nest(b);
            if x >= 0x1000_0000 {
                0x1000_0000
            } else {
                x + 1
            }
        },
        Node::Loop(b) => {
            let x = ex_nest(b);
            if x >= 0x1000_0000 {
                0x1000_0000
            } else {
                x + 1
            }
        },
        Node::If(t, e) => {
            let x = ex_nest(t);
            let y = ex_nest(e);
            let m = if x > y {
                x
            } else {
                y
            };
            if m >= 0x1000_0000 {
                0x1000_0000
            } else {
                m + 1
            }
        },
        _ => 0,
    }
}

/// [`cf_flow`], executable, for the nodes that have a template: `None` if the
/// analysis refuses (or the node has no template), else whether it is dead and
/// the height it falls through at.
fn ex_flow(n: &Node, nl: usize, h: usize, depth: usize) -> (r: Option<(bool, usize)>)
    requires
        nl <= 31,
        h <= 31,
        depth + nest(*n) < 0x1000_0000,
    ensures
        match r {
            Some((_, h1)) => h1 <= 31,
            None => true,
        },
        !templated(*n) ==> r is None,
        templated(*n) ==> match r {
            None => cf_flow(*n, nl as nat, h as nat, depth as nat) is None,
            Some((dead, h1)) => if dead {
                cf_flow(*n, nl as nat, h as nat, depth as nat) == Some(Flow::Dead)
            } else {
                cf_flow(*n, nl as nat, h as nat, depth as nat) == Some(Flow::Falls(h1 as nat))
            },
        },
    decreases *n,
{
    proof {
        crate::tlemmas::lemma_abi_consts_t();
    }
    match n {
        Node::Op(o) => {
            if op_ok_exec(o, nl, h) {
                let h1 = add_u(sub_u(h, pops_exec(o)), pushes_exec(o));
                Some((false, h1))
            } else {
                None
            }
        },
        Node::Mem(_) => None,
        Node::Then(a, b) => match ex_flow(a, nl, h, depth) {
            None => None,
            Some((false, h1)) => ex_flow(b, nl, h1, depth),
            Some((true, _)) => match &**b {
                Node::Op(Op::Nop) => Some((true, h)),
                _ => None,
            },
        },
        Node::Block(b) => match ex_flow(b, nl, h, depth + 1) {
            Some((false, h1)) => if h1 == h {
                Some((false, h))
            } else {
                None
            },
            Some((true, _)) => Some((false, h)),
            None => None,
        },
        Node::Loop(b) => match ex_flow(b, nl, h, depth + 1) {
            Some((false, h1)) => if h1 == h {
                Some((false, h))
            } else {
                None
            },
            Some((true, _)) => Some((false, h)),
            None => None,
        },
        Node::If(t, e) => if 1 <= h && nl + h <= 31 {
            match (ex_flow(t, nl, h - 1, depth + 1), ex_flow(e, nl, h - 1, depth + 1)) {
                (Some((dt, ht)), Some((de, he))) => if (dt || ht == h - 1) && (de || he == h - 1) {
                    Some((false, h - 1))
                } else {
                    None
                },
                _ => None,
            }
        } else {
            None
        },
        Node::Br(l) => if *l < depth {
            Some((true, h))
        } else {
            None
        },
        Node::BrIf(l) => if *l < depth && 1 <= h && nl + h <= 31 {
            Some((false, h - 1))
        } else {
            None
        },
        Node::BrTable(_, _) => None,
        Node::Exit(c, k) => if *k <= h && nl + h <= 31 {
            Some((true, h))
        } else {
            None
        },
    }
}

// ----------------------------------------------------------------------------
// The size
// ----------------------------------------------------------------------------

/// `mn` of a sum of `mn`s.
proof fn lemma_mn_add(x: nat, y: nat)
    ensures
        mn(mn(x, cap()) + mn(y, cap()), cap()) == mn(x + y, cap()),
{
}

/// [`csize`] of `nop` is 0, at any height.
proof fn lemma_csize_nop(nl: nat, h: nat, depth: nat)
    ensures
        csize(Node::Op(Op::Nop), nl, h, depth) == 0,
{
    assert(ctmpl(Node::Op(Op::Nop), nl, h, zeros(depth)) == tmpl(Op::Nop, nl, h));
}

/// The code length of a node (saturating at [`cap`]): [`csize`].
#[verifier::rlimit(300)]
fn ex_size(n: &Node, nl: usize, h: usize, depth: usize) -> (r: usize)
    requires
        nl <= 31,
        h <= 31,
        depth + nest(*n) < 0x1000_0000,
        cf_flow(*n, nl as nat, h as nat, depth as nat) is Some,
        templated(*n),
        h as nat <= 31,
    ensures
        r == mn(csize(*n, nl as nat, h as nat, depth as nat), cap()),
        r <= 0x4000_0000,
    decreases *n,
{
    proof {
        crate::tlemmas::lemma_abi_consts_t();
    }
    match n {
        Node::Op(o) => {
            let mut t: Vec<x64::Instr> = Vec::new();
            emit_op(o, nl, h, &mut t);
            proof {
                crate::tlemmas::lemma_tmpl_valid(*o, nl as nat, h as nat);
                assert(t@ == tmpl(*o, nl as nat, h as nat));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(t@));
            }
            ex_len(&t)
        },
        Node::Mem(_) => {
            proof {
                assert(false);
            }
            0
        },
        Node::Then(a, b) => {
            match ex_flow(a, nl, h, depth) {
                Some((false, h1)) => {
                    proof {
                        crate::cflens::lemma_csize_then(**a, **b, nl as nat, h as nat, depth as nat);
                        assert(flow_h(**a, nl as nat, h as nat, depth as nat) == h1 as nat);
                    }
                    let sa = ex_size(a, nl, h, depth);
                    let sb = ex_size(b, nl, h1, depth);
                    proof {
                        lemma_mn_add(
                            csize(**a, nl as nat, h as nat, depth as nat),
                            csize(**b, nl as nat, h1 as nat, depth as nat),
                        );
                    }
                    let t = sa + sb;
                    if t > 0x4000_0000 {
                        0x4000_0000
                    } else {
                        t
                    }
                },
                Some((true, _)) => {
                    proof {
                        crate::cflens::lemma_csize_then(**a, **b, nl as nat, h as nat, depth as nat);
                        lemma_csize_nop(
                            nl as nat,
                            flow_h(**a, nl as nat, h as nat, depth as nat),
                            depth as nat,
                        );
                        match **b {
                            Node::Op(Op::Nop) => {},
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    ex_size(a, nl, h, depth)
                },
                None => {
                    proof {
                        assert(false);
                    }
                    0
                },
            }
        },
        Node::Block(b) => {
            proof {
                crate::cflens::lemma_csize_block(**b, nl as nat, h as nat, depth as nat);
            }
            ex_size(b, nl, h, depth + 1)
        },
        Node::Loop(b) => {
            proof {
                crate::cflens::lemma_csize_loop(**b, nl as nat, h as nat, depth as nat);
            }
            ex_size(b, nl, h, depth + 1)
        },
        Node::If(t, e) => {
            proof {
                crate::cflens::lemma_csize_if(**t, **e, nl as nat, h as nat, depth as nat);
            }
            let p = ex_cond_len(nl, h);
            let st = ex_size(t, nl, h - 1, depth + 1);
            let se = ex_size(e, nl, h - 1, depth + 1);
            let tot = p + st + 5 + se;
            if tot > 0x4000_0000 {
                0x4000_0000
            } else {
                tot
            }
        },
        Node::Br(l) => {
            proof {
                crate::cflens::lemma_csize_br(*l, nl as nat, h as nat, depth as nat);
            }
            5
        },
        Node::BrIf(l) => {
            proof {
                crate::cflens::lemma_csize_brif(*l, nl as nat, h as nat, depth as nat);
            }
            ex_cond_len(nl, h)
        },
        Node::BrTable(_, _) => {
            proof {
                assert(false);
            }
            0
        },
        Node::Exit(c, _) => {
            let mut t: Vec<x64::Instr> = Vec::new();
            emit_exit(&mut t, *c);
            proof {
                crate::tlemmas::lemma_exit_valid(*c);
                assert(t@ == exit_seq(*c));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(exit_seq(*c)));
            }
            ex_len(&t)
        },
    }
}

// ----------------------------------------------------------------------------
// The code
// ----------------------------------------------------------------------------

/// A label offset is below `2^32` in absolute value, from [`labels_fit`].
proof fn lemma_fit_range(offs: Seq<int>, size: nat)
    requires
        labels_fit(offs, size),
        size <= max_size(),
    ensures
        forall|i: int| 0 <= i < offs.len() ==> -0x1_0000_0000 < #[trigger] offs[i] < 0x1_0000_0000,
{
}

/// `ex_size` is exact below the saturation point.
proof fn lemma_mn_small(x: nat)
    requires
        x <= max_size(),
    ensures
        mn(x, cap()) == x,
{
}

/// The code of a node: [`ctmpl`].
#[verifier::rlimit(400)]
fn emit_cf(n: &Node, nl: usize, h: usize, offs: &Vec<i64>, out: &mut Vec<x64::Instr>)
    requires
        nl <= 31,
        h <= 31,
        offs@.len() + nest(*n) < 0x1000_0000,
        cf_flow(*n, nl as nat, h as nat, offs@.len()) is Some,
        templated(*n),
        csize(*n, nl as nat, h as nat, offs@.len()) <= max_size(),
        labels_fit(ov(offs@), csize(*n, nl as nat, h as nat, offs@.len())),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, ov(offs@)),
    decreases *n,
{
    proof {
        crate::tlemmas::lemma_abi_consts_t();
        assert(ov(offs@).len() == offs@.len());
    }
    let ghost old_out = out@;
    let depth = offs.len();
    let ghost size = csize(*n, nl as nat, h as nat, depth as nat);
    proof {
        lemma_fit_range(ov(offs@), size);
    }
    match n {
        Node::Op(o) => {
            emit_op(o, nl, h, out);
        },
        Node::Mem(_) => {
            proof {
                assert(false);
            }
        },
        Node::Then(a, b) => {
            match ex_flow(a, nl, h, depth) {
                Some((false, h1)) => {
                    proof {
                        crate::cflens::lemma_csize_then(**a, **b, nl as nat, h as nat, depth as nat);
                        assert(flow_h(**a, nl as nat, h as nat, depth as nat) == h1 as nat);
                    }
                    let ghost sa_ = csize(**a, nl as nat, h as nat, depth as nat);
                    let ghost sb_ = csize(**b, nl as nat, h1 as nat, depth as nat);
                    proof {
                        lemma_fit_mono(ov(offs@), size, sa_);
                    }
                    emit_cf(a, nl, h, offs, out);
                    let sa = ex_size(a, nl, h, depth);
                    proof {
                        lemma_mn_small(sa_);
                        assert(sa as nat == sa_);
                    }
                    proof {
                        assert forall|i: int| 0 <= i < offs@.len() implies -0x1_0000_0000
                            < #[trigger] offs@[i] < 0x1_0000_0000 by {
                            assert(ov(offs@)[i] == offs@[i] as int);
                        }
                    }
                    let shifted = shift_vec(offs, sa as i64);
                    proof {
                        lemma_fit_shift(ov(offs@), sa as nat, size, sb_);
                        assert(ov(shifted@) == shift(ov(offs@), sa as int));
                        assert(shifted@.len() == offs@.len()) by {
                            assert(ov(shifted@).len() == ov(offs@).len());
                        }
                    }
                    emit_cf(b, nl, h1, &shifted, out);
                    proof {
                        assert(ctmpl(*n, nl as nat, h as nat, ov(offs@)) == ctmpl(
                            **a,
                            nl as nat,
                            h as nat,
                            ov(offs@),
                        ) + ctmpl(**b, nl as nat, h1 as nat, shift(ov(offs@), sa_ as int)));
                        assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
                    }
                },
                Some((true, _)) => {
                    proof {
                        crate::cflens::lemma_csize_then(**a, **b, nl as nat, h as nat, depth as nat);
                        lemma_csize_nop(
                            nl as nat,
                            flow_h(**a, nl as nat, h as nat, depth as nat),
                            depth as nat,
                        );
                        lemma_fit_mono(
                            ov(offs@),
                            size,
                            csize(**a, nl as nat, h as nat, depth as nat),
                        );
                        match **b {
                            Node::Op(Op::Nop) => {},
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    emit_cf(a, nl, h, offs, out);
                    proof {
                        let ob = shift(
                            ov(offs@),
                            csize(**a, nl as nat, h as nat, depth as nat) as int,
                        );
                        assert(ctmpl(**b, nl as nat, h as nat, ob) =~= Seq::<x64::Instr>::empty());
                        assert(ctmpl(*n, nl as nat, h as nat, ov(offs@)) == ctmpl(
                            **a,
                            nl as nat,
                            h as nat,
                            ov(offs@),
                        ) + ctmpl(
                            **b,
                            nl as nat,
                            flow_h(**a, nl as nat, h as nat, depth as nat),
                            ob,
                        ));
                        assert(ctmpl(**a, nl as nat, h as nat, ov(offs@)) + Seq::<
                            x64::Instr,
                        >::empty() =~= ctmpl(**a, nl as nat, h as nat, ov(offs@)));
                        assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
                    }
                },
                None => {
                    proof {
                        assert(false);
                    }
                },
            }
        },
        Node::Block(b) => {
            proof {
                crate::cflens::lemma_csize_block(**b, nl as nat, h as nat, depth as nat);
            }
            let ghost sb_ = csize(**b, nl as nat, h as nat, depth as nat + 1);
            let sb = ex_size(b, nl, h, depth + 1);
            proof {
                lemma_mn_small(sb_);
                assert(sb as nat == sb_);
                lemma_fit_mono(ov(offs@), size, sb_);
            }
            let offs2 = cons_vec(sb as i64, offs);
            proof {
                lemma_fit_cons(sb as int, ov(offs@), sb_);
                assert(offs2@.len() == depth + 1);
            }
            emit_cf(b, nl, h, &offs2, out);
            proof {
                assert(ctmpl(*n, nl as nat, h as nat, ov(offs@)) == ctmpl(
                    **b,
                    nl as nat,
                    h as nat,
                    seq![sb_ as int] + ov(offs@),
                ));
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
            }
        },
        Node::Loop(b) => {
            proof {
                crate::cflens::lemma_csize_loop(**b, nl as nat, h as nat, depth as nat);
            }
            let ghost sb_ = csize(**b, nl as nat, h as nat, depth as nat + 1);
            proof {
                lemma_fit_mono(ov(offs@), size, sb_);
            }
            let offs2 = cons_vec(0, offs);
            proof {
                lemma_fit_cons(0, ov(offs@), sb_);
                assert(offs2@.len() == depth + 1);
            }
            emit_cf(b, nl, h, &offs2, out);
            proof {
                assert(ctmpl(*n, nl as nat, h as nat, ov(offs@)) == ctmpl(
                    **b,
                    nl as nat,
                    h as nat,
                    seq![0int] + ov(offs@),
                ));
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
            }
        },
        Node::If(t, e) => {
            proof {
                crate::cflens::lemma_csize_if(**t, **e, nl as nat, h as nat, depth as nat);
            }
            let ghost st_ = csize(**t, nl as nat, (h - 1) as nat, depth as nat + 1);
            let ghost se_ = csize(**e, nl as nat, (h - 1) as nat, depth as nat + 1);
            let p = ex_cond_len(nl, h);
            let st = ex_size(t, nl, h - 1, depth + 1);
            let se = ex_size(e, nl, h - 1, depth + 1);
            proof {
                lemma_mn_small(st_);
                lemma_mn_small(se_);
                assert(st as nat == st_ && se as nat == se_);
                lemma_mn_small(cond_len(nl as nat, h as nat));
                assert(p as nat == cond_len(nl as nat, h as nat));
            }
            ex_cond_pre(nl, h, 4, (st + 5) as i32, out);
            proof {
                assert forall|i: int| 0 <= i < offs@.len() implies -0x1_0000_0000
                    < #[trigger] offs@[i] < 0x1_0000_0000 by {
                    assert(ov(offs@)[i] == offs@[i] as int);
                }
            }
            let shifted_t = shift_vec(offs, p as i64);
            let ot = cons_vec((st + 5 + se) as i64, &shifted_t);
            proof {
                lemma_fit_shift(ov(offs@), p as nat, size, st_);
                lemma_fit_cons((st_ + 5 + se_) as int, shift(ov(offs@), p as int), st_);
                assert(ov(shifted_t@) == shift(ov(offs@), p as int));
                assert(shifted_t@.len() == offs@.len()) by {
                    assert(ov(shifted_t@).len() == ov(offs@).len());
                }
                assert(ot@.len() == depth + 1);
            }
            emit_cf(t, nl, h - 1, &ot, out);
            out.push(x64::Instr::Jmp { rel: se as i32 });
            let shifted_e = shift_vec(offs, (p + st + 5) as i64);
            let oe = cons_vec(se as i64, &shifted_e);
            proof {
                lemma_fit_shift(ov(offs@), (p + st + 5) as nat, size, se_);
                lemma_fit_cons(se_ as int, shift(ov(offs@), (p + st_ + 5) as int), se_);
                assert(ov(shifted_e@) == shift(ov(offs@), (p + st + 5) as int));
                assert(shifted_e@.len() == offs@.len()) by {
                    assert(ov(shifted_e@).len() == ov(offs@).len());
                }
                assert(oe@.len() == depth + 1);
            }
            emit_cf(e, nl, h - 1, &oe, out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
            }
        },
        Node::Br(l) => {
            proof {
                crate::cflens::lemma_csize_br(*l, nl as nat, h as nat, depth as nat);
                assert(*l < depth);
            }
            proof {
                assert(ov(offs@)[*l as int] == offs@[*l as int] as int);
                assert(-0x8000_0000 + 11 <= offs@[*l as int] <= 0x7FFF_FFFF);
            }
            out.push(x64::Instr::Jmp { rel: (offs[*l] - 5) as i32 });
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
            }
        },
        Node::BrIf(l) => {
            proof {
                crate::cflens::lemma_csize_brif(*l, nl as nat, h as nat, depth as nat);
                assert(*l < depth);
            }
            let p = ex_cond_len(nl, h);
            proof {
                assert(ov(offs@)[*l as int] == offs@[*l as int] as int);
                lemma_mn_small(cond_len(nl as nat, h as nat));
                assert(p as nat == cond_len(nl as nat, h as nat));
                assert(-0x8000_0000 + cond_len(nl as nat, h as nat) + 6 <= offs@[*l as int]);
            }
            ex_cond_pre(nl, h, 5, (offs[*l] - p as i64) as i32, out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, ov(offs@)));
            }
        },
        Node::BrTable(_, _) => {
            proof {
                assert(false);
            }
        },
        Node::Exit(c, _) => {
            emit_exit(out, *c);
        },
    }
}

// ----------------------------------------------------------------------------
// The program and the blob
// ----------------------------------------------------------------------------

/// **The code of a program**, the return label at its end: [`ctmpl`], proven
/// to refine the program ([`cf_refines`]) and to be in the subset. `None`
/// exactly when [`cf_prog_ok`] refuses.
#[verifier::rlimit(400)]
pub fn emit_cf_body(n: &Node, nl: usize) -> (r: Option<Vec<x64::Instr>>)
    ensures
        match r {
            Some(v) => cf_prog_ok(*n, nl as nat) && all_valid_instrs(v@) && cf_refines(
                n@,
                nl as nat,
                0,
                seq![code_len(v@) as int],
                v@,
            ),
            None => !cf_prog_ok(*n, nl as nat),
        },
{
    proof {
        crate::tlemmas::lemma_abi_consts_t();
    }
    if nl > 31 {
        return None;
    }
    if ex_nest(n) >= 0x0FFF_0000 {
        return None;
    }
    match ex_flow(n, nl, 0, 1) {
        None => None,
        Some(_) => {
            let size = ex_size(n, nl, 0, 1);
            if size > 0x2000_0000 {
                proof {
                    assert(csize(*n, nl as nat, 0, 1) > max_size());
                }
                return None;
            }
            proof {
                assert(csize(*n, nl as nat, 0, 1) <= max_size());
                assert(size as nat == csize(*n, nl as nat, 0, 1));
            }
            let mut offs: Vec<i64> = Vec::new();
            offs.push(size as i64);
            let mut out: Vec<x64::Instr> = Vec::new();
            proof {
                assert(ov(offs@) =~= seq![size as int]);
                assert(labels_fit(ov(offs@), size as nat));
            }
            emit_cf(n, nl, 0, &offs, &mut out);
            proof {
                crate::cfproofs::lemma_ctmpl_refines(*n, nl as nat, 0, ov(offs@));
                crate::cfvalid::lemma_ctmpl_valid(*n, nl as nat, 0, ov(offs@));
                crate::cflens::lemma_ctmpl_len(*n, nl as nat, 0, ov(offs@));
                assert(out@ =~= ctmpl(*n, nl as nat, 0, ov(offs@)));
                assert(code_len(out@) == size as nat);
            }
            Some(out)
        },
    }
}

/// **The bytes of a blob**: the encoded program and the exit sequence for
/// `exit_code` ([`emit_cf_blob_ensures`]).
#[verifier::rlimit(500)]
pub fn emit_cf_blob(n: &Node, nl: usize, exit_code: u32) -> (r: Option<Vec<u8>>)
    ensures
        emit_cf_blob_ensures(*n, nl, exit_code, match r {
            Some(v) => Some(v@),
            None => None,
        }),
{
    match emit_cf_body(n, nl) {
        None => None,
        Some(body) => {
            let ghost body_seq = body@;
            let mut code = body;
            emit_exit(&mut code, exit_code);
            proof {
                crate::tlemmas::lemma_exit_valid(exit_code);
                assert forall|k: int| 0 <= k < code@.len() implies x64::valid_instr(
                    #[trigger] code@[k],
                ) by {
                    if k < body_seq.len() {
                        assert(code@[k] == body_seq[k]);
                    } else {
                        assert(code@[k] == exit_seq(exit_code)[k - body_seq.len()]);
                    }
                }
            }
            let mut bytes: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            proof {
                assert(code@.take(0) =~= Seq::<x64::Instr>::empty());
            }
            while k < code.len()
                invariant
                    k <= code.len(),
                    bytes@ == clazel_codecheck::spec::enc_all(code@.take(k as int)),
                    forall|j: int| 0 <= j < code@.len() ==> x64::valid_instr(#[trigger] code@[j]),
                decreases code.len() - k,
            {
                let ins = match code.get(k) {
                    Some(ins) => ins,
                    None => {
                        proof {
                            assert(false);
                        }
                        return None;
                    },
                };
                let e = encode_exec(ins);
                bytes.extend_from_slice(e.as_slice());
                proof {
                    let t = code@.take(k as int + 1);
                    assert(t.drop_last() =~= code@.take(k as int));
                    assert(t.last() == code@[k as int]);
                    assert(e@ =~= x64::encode(code@[k as int]));
                }
                k = k + 1;
            }
            proof {
                assert(code@.take(code@.len() as int) =~= code@);
                assert(code@ == body_seq + exit_seq(exit_code));
            }
            Some(bytes)
        },
    }
}

} // verus!
