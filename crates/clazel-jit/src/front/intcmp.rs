//! The int32 comparisons: `Lt`, `Le`, `Gt`, `Ge`, `StrictEq`, `StrictNe`.
//!
//! The semantics compares the *doubles* two int32s stand for
//! (`num_bits`, `f64_of_int`) with `Number::lessThan` and `Number::equal`;
//! [`super::numord`] proves that this is the order and equality of the
//! integers. So the lowering is: both operands int32 (the tag test of the
//! first slice), sign-extend the two payloads to 64 bits, compare them with
//! the signed (or `eq`, `ne`) `i64` comparison, widen the `i32` flag and add
//! it to the encoding of `false` (`true` is that plus one), and store. Any
//! other operands exit to the handler, which for `StrictEq` and `StrictNe`
//! includes cases where `fast_path` holds (`undefined === undefined`, two
//! doubles, ...) and so relies on [`handler_complete`].
//!
//! `k` is the operator: 0 `Lt`, 1 `Le`, 2 `Gt`, 3 `Ge`, 4 `StrictEq`,
//! 5 `StrictNe`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `i64` comparison of operator `k`.
pub open spec fn cmp_icmp(k: nat) -> lir::ICmp {
    if k == 0 {
        lir::ICmp::LtS
    } else if k == 1 {
        lir::ICmp::LeS
    } else if k == 2 {
        lir::ICmp::GtS
    } else if k == 3 {
        lir::ICmp::GeS
    } else if k == 4 {
        lir::ICmp::Eq
    } else {
        lir::ICmp::Ne
    }
}

/// The bytecode op of operator `k`.
pub open spec fn cmp_op(k: nat, dst: nat, a: nat, b: nat) -> js::Op {
    if k == 0 {
        js::Op::Lt { dst, a, b }
    } else if k == 1 {
        js::Op::Le { dst, a, b }
    } else if k == 2 {
        js::Op::Gt { dst, a, b }
    } else if k == 3 {
        js::Op::Ge { dst, a, b }
    } else if k == 4 {
        js::Op::StrictEq { dst, a, b }
    } else {
        js::Op::StrictNe { dst, a, b }
    }
}

/// The truth value of operator `k` on two integers.
pub open spec fn cmp_truth(k: nat, ia: int, ib: int) -> bool {
    if k == 0 {
        ia < ib
    } else if k == 1 {
        ia <= ib
    } else if k == 2 {
        ia > ib
    } else if k == 3 {
        ia >= ib
    } else if k == 4 {
        ia == ib
    } else {
        ia != ib
    }
}

/// After the two sign-extended payloads: compare, widen, add `false`.
pub open spec fn cmp_tail(k: nat) -> Seq<lir::Instr> {
    seq![
        super::lower::cmp64(cmp_icmp(k)),
        lir::Instr::Un(lir::UnOp::I64ExtendI32U),
        super::lower::i64c(js::FALSE),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
    ]
}

/// The value block: the encoded boolean of the comparison of locals 1 and 2.
pub open spec fn cmp_val(k: nat) -> Seq<lir::Instr> {
    super::lower::sext_local(1) + (super::lower::sext_local(2) + cmp_tail(k))
}

/// The word the value block pushes, from the two sign-extended payloads.
pub open spec fn cmp_word(k: nat, xa: u64, xb: u64) -> u64 {
    (lir::bool_i32(lir::icmp(cmp_icmp(k), 64, xa as int, xb as int)) as u64 + js::FALSE) as u64
}

/// The lowering of operator `k` on registers `a` and `b` into `dst`.
pub open spec fn lower_cmp(k: nat, dst: nat, a: nat, b: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::lower_bin(cmp_val(k), dst, a, b, op, pc)
}

/// The value block is simple and ten instructions long.
pub proof fn lemma_cmp_val_simple(k: nat)
    ensures
        super::run::all_simple(cmp_val(k)),
        cmp_val(k).len() == 10,
{
    super::intops::lemma_literals_simple(0);
    let t = cmp_tail(k);
    assert(super::run::all_simple(t)) by {
        assert forall|i: int| 0 <= i < t.len() implies super::run::is_simple(#[trigger] t[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3);
        }
    }
    super::intops::lemma_simple_concat(super::lower::sext_local(2), t);
    super::intops::lemma_simple_concat(super::lower::sext_local(1), super::lower::sext_local(2) + t);
}

/// The value block's trace: from locals 1 and 2 holding two words, it pushes
/// the comparison of their sign-extended low halves.
pub proof fn lemma_cmp_val_trace(lay: lir::Layout, k: nat, va: u64, vb: u64)
    ensures
        super::blocks::val_computes(
            lay,
            cmp_val(k),
            va,
            vb,
            cmp_word(k, super::arith::sext(super::arith::lo32(va)), super::arith::sext(super::arith::lo32(vb))),
        ),
{
    let xa = super::arith::sext(super::arith::lo32(va));
    let xb = super::arith::sext(super::arith::lo32(vb));
    let w = cmp_word(k, xa, xb);
    let t = cmp_tail(k);
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, cmp_val(k), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) && st1.locals[2]
            == lir::Val::I64(vb) implies super::run::exec(lay, cmp_val(k), st1) == lir::Outcome::Normal(
        st1.with_stack(st1.stack.push(lir::Val::I64(w))),
    ) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        super::trace::lemma_exec_sext_local(lay, st1, 1, va);
        let s1 = st1.with_stack(st1.stack.push(lir::Val::I64(xa)));
        super::trace::lemma_exec_app(
            lay,
            super::lower::sext_local(1),
            super::lower::sext_local(2) + t,
            st1,
            s1,
        );
        super::trace::lemma_exec_sext_local(lay, s1, 2, vb);
        let s2 = s1.with_stack(s1.stack.push(lir::Val::I64(xb)));
        super::trace::lemma_exec_app(lay, super::lower::sext_local(2), t, s1, s2);
        let f = lir::bool_i32(lir::icmp(cmp_icmp(k), 64, xa as int, xb as int));
        super::frame::lemma_add_small(f as u64, js::FALSE);
        reveal_with_fuel(super::run::exec, 5);
        assert(super::run::exec(lay, t, s2) == lir::Outcome::Normal(
            st1.with_stack(st1.stack.push(lir::Val::I64(w))),
        ));
    }
}

/// The comparison's word is the encoding of the integers' comparison.
pub proof fn lemma_cmp_word(k: nat, va: u64, vb: u64)
    requires
        k <= 5,
        js::is_int32(va),
        js::is_int32(vb),
    ensures
        cmp_word(k, super::arith::sext(super::arith::lo32(va)), super::arith::sext(super::arith::lo32(vb)))
            == js::enc_bool(cmp_truth(k, js::int32_of(va) as int, js::int32_of(vb) as int)),
{
    super::arith::lemma_payload(va);
    super::arith::lemma_payload(vb);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    let xa = super::arith::sext(super::arith::lo32(va));
    let xb = super::arith::sext(super::arith::lo32(vb));
    assert(xa == (ia as i64) as u64);
    assert(xb == (ib as i64) as u64);
    super::arith::lemma_signed64(xa);
    super::arith::lemma_signed64(xb);
    assert((((ia as i64) as u64) as i64) == (ia as i64)) by (bit_vector);
    assert((((ib as i64) as u64) as i64) == (ib as i64)) by (bit_vector);
    assert((((ia as i64) as u64) == ((ib as i64) as u64)) <==> (ia == ib)) by (bit_vector);
    let t = cmp_truth(k, ia as int, ib as int);
    assert(lir::icmp(cmp_icmp(k), 64, xa as int, xb as int) == t);
    assert(js::FALSE + 1 == js::TRUE);
}

/// The semantics of an operator `k` on two int32 registers: the fast path
/// holds, and the result is the encoded comparison of the integers.
pub proof fn lemma_cmp_sem(s: js::State, k: nat, dst: nat, a: nat, b: nat)
    requires
        k <= 5,
        js::is_int32(js::reg(s, a)),
        js::is_int32(js::reg(s, b)),
    ensures
        js::fast_path(s, cmp_op(k, dst, a, b)),
        js::fast_step(s, cmp_op(k, dst, a, b)) == js::next(
            js::set_reg(
                s,
                dst,
                js::enc_bool(
                    cmp_truth(k, js::int32_of(js::reg(s, a)) as int, js::int32_of(js::reg(s, b)) as int),
                ),
            ),
        ),
{
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    super::numord::lemma_less_than_int(ia as int, ib as int);
    super::numord::lemma_less_than_int(ib as int, ia as int);
    super::numord::lemma_equal_int(ia as int, ib as int);
    assert(js::num_bits(va) == js::f64_of_int(ia as int));
    assert(js::num_bits(vb) == js::f64_of_int(ib as int));
    assert(js::is_number(va) && js::is_number(vb));
}

/// An int32 comparison op: the lowering refines `step`.
pub proof fn lemma_cmp_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    k: nat,
    dst: nat,
    a: nat,
    b: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        k <= 5,
        op == cmp_op(k, dst, a, b),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
        super::lower::lower(c, op, pc, lbl) == lower_cmp(k, dst, a, b, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_cmp_val_simple(k);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let w = js::enc_bool(cmp_truth(k, js::int32_of(va) as int, js::int32_of(vb) as int));
    if js::is_int32(va) && js::is_int32(vb) {
        lemma_cmp_sem(s, k, dst, a, b);
        lemma_cmp_val_trace(lay, k, va, vb);
        lemma_cmp_word(k, va, vb);
    }
    super::blocks::lemma_bin_op(op, pc, lbl, lay, s, st, fuel, dst, a, b, cmp_val(k), w);
}

} // verus!
