//! `UShr` (`>>>`) on int32s.
//!
//! The semantics shifts the *unsigned* reading of the left operand right by
//! the count reduced modulo 32, and the result, a `uint32`, is an int32 only
//! when it is below `2^31` (otherwise it is a double, which LIR cannot compute
//! in this slice). So there are two guards, `and`ed into one flag: both
//! operands are int32s, and the shifted value (`(a & 0xFFFF_FFFF) >>u (b & 31)`
//! on the 64-bit words) is below `2^31`. The value is that shifted value,
//! tagged. Everything else, a result of `2^31` or more included, exits to the
//! handler (which relies on [`handler_complete`] where `fast_path` holds).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The extra flag block: the shifted value is below `2^31`, `and`ed into the
/// flag on the stack.
pub open spec fn ushr_ex() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(1),
        super::lower::i64c(0xFFFF_FFFF),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        lir::Instr::LocalGet(2),
        super::lower::i64c(31),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::ShrU)),
        super::lower::i64c(0x8000_0000),
        super::lower::cmp64(lir::ICmp::LtU),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ]
}

/// The value block: the shifted value, tagged.
pub open spec fn ushr_val() -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(1),
        super::lower::i64c(0xFFFF_FFFF),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        lir::Instr::LocalGet(2),
        super::lower::i64c(31),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::ShrU)),
        super::lower::i64c(0xFFFF_FFFF),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
        super::lower::i64c(super::arith::tag_bits()),
        lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
    ]
}

/// The shifted value, from the two operand words.
pub open spec fn ushr_s(va: u64, vb: u64) -> u64 {
    lir::ibin64(lir::IBin::ShrU, va & 0xFFFF_FFFFu64, vb & 31u64)
}

/// The extra flag: the shifted value is below `2^31`.
pub open spec fn ushr_f(va: u64, vb: u64) -> u32 {
    lir::bool_i32(lir::icmp(lir::ICmp::LtU, 64, ushr_s(va, vb) as int, 0x8000_0000u64 as int))
}

/// The word the value block pushes.
pub open spec fn ushr_word(va: u64, vb: u64) -> u64 {
    super::arith::tagged(ushr_s(va, vb))
}

/// The `UShr` lowering.
pub open spec fn lower_ushr(dst: nat, a: nat, b: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::lower_bin2(ushr_ex(), ushr_val(), dst, a, b, op, pc)
}

/// The blocks are simple and short.
pub proof fn lemma_ushr_simple()
    ensures
        super::run::all_simple(ushr_ex()),
        ushr_ex().len() == 10,
        super::run::all_simple(ushr_val()),
        ushr_val().len() == 11,
{
    let e = ushr_ex();
    assert(super::run::all_simple(e)) by {
        assert forall|i: int| 0 <= i < e.len() implies super::run::is_simple(#[trigger] e[i]) by {
            assert(0 <= i < 10);
        }
    }
    let v = ushr_val();
    assert(super::run::all_simple(v)) by {
        assert forall|i: int| 0 <= i < v.len() implies super::run::is_simple(#[trigger] v[i]) by {
            assert(0 <= i < 11);
        }
    }
}

/// The extra flag block's trace.
pub proof fn lemma_ushr_ex_trace(lay: lir::Layout, va: u64, vb: u64)
    ensures
        super::blocks::flag_and_computes(lay, ushr_ex(), va, vb, ushr_f(va, vb)),
{
    assert forall|st1: lir::St, base: Seq<lir::Val>, g1: u32|
        #![trigger super::run::exec(lay, ushr_ex(), st1), base.push(lir::Val::I32(g1))]
        st1.stack == base.push(lir::Val::I32(g1)) && st1.locals.len() == nlocals() && st1.locals[1]
            == lir::Val::I64(va) && st1.locals[2] == lir::Val::I64(vb) implies super::run::exec(
        lay,
        ushr_ex(),
        st1,
    ) == lir::Outcome::Normal(
        st1.with_stack(base.push(lir::Val::I32(lir::ibin32(lir::IBin::And, g1, ushr_f(va, vb))))),
    ) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        reveal_with_fuel(super::run::exec, 11);
    }
}

/// The value block's trace.
pub proof fn lemma_ushr_val_trace(lay: lir::Layout, va: u64, vb: u64)
    ensures
        super::blocks::val_computes(lay, ushr_val(), va, vb, ushr_word(va, vb)),
{
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, ushr_val(), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) && st1.locals[2]
            == lir::Val::I64(vb) implies super::run::exec(lay, ushr_val(), st1) == lir::Outcome::Normal(
        st1.with_stack(st1.stack.push(lir::Val::I64(ushr_word(va, vb)))),
    ) by {
        broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

        reveal_with_fuel(super::run::exec, 12);
    }
}

/// The semantics' result on two int32 registers whose shifted value is below
/// `2^31`: the fast path holds and the result is the tagged shifted value.
pub proof fn lemma_ushr_sem(s: js::State, dst: nat, a: nat, b: nat)
    requires
        js::is_int32(js::reg(s, a)),
        js::is_int32(js::reg(s, b)),
        ushr_f(js::reg(s, a), js::reg(s, b)) != 0,
    ensures
        js::fast_path(s, js::Op::UShr { dst, a, b }),
        js::fast_step(s, js::Op::UShr { dst, a, b }) == js::next(
            js::set_reg(s, dst, ushr_word(js::reg(s, a), js::reg(s, b))),
        ),
{
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    super::arith::lemma_payload(va);
    super::arith::lemma_payload(vb);
    super::numord::lemma_to_uint32(ia);
    super::numord::lemma_to_uint32(ib);
    assert(js::num_bits(va) == js::f64_of_int(ia as int));
    assert(js::num_bits(vb) == js::f64_of_int(ib as int));
    assert(js::is_number(va) && js::is_number(vb));
    let c: u32 = (ib as u32) % 32u32;
    assert((vb & 31u64) == (c as u64)) by (bit_vector)
        requires
            ib == (super::arith::lo32(vb) as i32),
            c == (ib as u32) % 32u32,
    ;
    assert((va & 0xFFFF_FFFFu64) == ((ia as u32) as u64)) by (bit_vector)
        requires
            ia == (super::arith::lo32(va) as i32),
    ;
    assert(c as nat == super::bitops::shift_count(ib));
    vstd::arithmetic::power2::lemma2_to64_rest();
    assert((c as int % 64) as nat == c as nat);
    let sc = super::bitops::shift_count(ib);
    let q: int = ((ia as u32) as int) / (vstd::arithmetic::power2::pow2(sc) as int);
    let s_ = ushr_s(va, vb);
    assert(s_ == (q as u64));
    vstd::arithmetic::power2::lemma_pow2_pos(sc);
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(((ia as u32) as int), 1, vstd::arithmetic::power2::pow2(sc) as int);
    assert(0 <= q);
    assert(q < 0x8000_0000int);
    assert(js::fits_i32(q));
    let r: nat = ((ia as u32) as nat) / vstd::arithmetic::power2::pow2(sc);
    assert(r as int == q);
    assert(super::arith::tagged(s_) == js::enc_int32(s_ as i32)) by (bit_vector)
        requires
            s_ < 0x8000_0000u64,
    ;
    assert(s_ as int == q);
    assert((s_ as i32) == (q as i32));
}

/// A `UShr` op: the lowering refines `step`.
pub proof fn lemma_ushr_op(
    c: js::Code,
    op: js::Op,
    pc: nat,
    lbl: nat,
    lay: lir::Layout,
    s: js::State,
    st: lir::St,
    fuel: nat,
    dst: nat,
    a: nat,
    b: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        op == (js::Op::UShr { dst, a, b }),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
        super::lower::lower(c, op, pc, lbl) == lower_ushr(dst, a, b, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_ushr_simple();
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let f = ushr_f(va, vb);
    lemma_ushr_ex_trace(lay, va, vb);
    assert(f == 0 || f == 1);
    if js::is_int32(va) && js::is_int32(vb) && f != 0 {
        lemma_ushr_sem(s, dst, a, b);
        lemma_ushr_val_trace(lay, va, vb);
    }
    super::blocks::lemma_bin_op2(
        op,
        pc,
        lbl,
        lay,
        s,
        st,
        fuel,
        dst,
        a,
        b,
        ushr_ex(),
        ushr_val(),
        f,
        ushr_word(va, vb),
    );
}

} // verus!
