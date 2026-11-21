//! The int32 bitwise operations and shifts: `BitAnd`, `BitOr`, `BitXor`,
//! `Shl`, `Shr`.
//!
//! The semantics takes `ToInt32` of the doubles two int32s stand for, which
//! [`super::numord`] shows is the identity on an int32 (and `ToUint32` its
//! unsigned reading). So the lowering is: both operands int32, sign-extend
//! the two payloads to 64 bits, do the operation on the 64-bit words (for a
//! shift, with the count masked to its low five bits first, as the semantics
//! reduces it modulo 32), keep the low 32 bits of the result and tag them.
//! Every other pair of operands exits to the handler.
//!
//! `k` is the operation: 0 `BitAnd`, 1 `BitOr`, 2 `BitXor`, 3 `Shl`,
//! 4 `Shr`. (`UShr` is not lowered: its result is a double when the shifted
//! value has its top bit set, which needs a second guard; `BitNot` is a
//! unary op.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The 64-bit operator of operation `k`.
pub open spec fn bit_ibin(k: nat) -> lir::IBin {
    if k == 0 {
        lir::IBin::And
    } else if k == 1 {
        lir::IBin::Or
    } else if k == 2 {
        lir::IBin::Xor
    } else if k == 3 {
        lir::IBin::Shl
    } else {
        lir::IBin::ShrS
    }
}

/// The bytecode op of operation `k`.
pub open spec fn bit_op(k: nat, dst: nat, a: nat, b: nat) -> js::Op {
    if k == 0 {
        js::Op::BitAnd { dst, a, b }
    } else if k == 1 {
        js::Op::BitOr { dst, a, b }
    } else if k == 2 {
        js::Op::BitXor { dst, a, b }
    } else if k == 3 {
        js::Op::Shl { dst, a, b }
    } else {
        js::Op::Shr { dst, a, b }
    }
}

/// The shift count the semantics uses: `ToUint32` of the right operand,
/// modulo 32.
pub open spec fn shift_count(ib: i32) -> nat {
    ((ib as u32) as nat) % 32
}

/// The int32 result of operation `k` on two int32s, as the semantics writes
/// it (`Number::bitwiseAND`, `leftShift`, `signedRightShift`, ... on the
/// `ToInt32`s, which are the int32s themselves).
pub open spec fn bit_res(k: nat, ia: i32, ib: i32) -> i32 {
    if k == 0 {
        ia & ib
    } else if k == 1 {
        ia | ib
    } else if k == 2 {
        ia ^ ib
    } else if k == 3 {
        js::wrap_i32(ia as int * vstd::arithmetic::power2::pow2(shift_count(ib)) as int)
    } else {
        ((ia as int) / (vstd::arithmetic::power2::pow2(shift_count(ib)) as int)) as i32
    }
}

/// After the two sign-extended payloads: (for a shift, mask the count),
/// operate, keep the low half (`and` with `0xFFFF_FFFF`), tag (`or` with the
/// int32 tag).
pub open spec fn bit_tail(k: nat) -> Seq<lir::Instr> {
    if k <= 2 {
        seq![
            lir::Instr::Bin(lir::BinOp::I64(bit_ibin(k))),
            super::lower::i64c(0xFFFF_FFFF),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
            super::lower::i64c(super::arith::tag_bits()),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
        ]
    } else {
        seq![
            super::lower::i64c(31),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
            lir::Instr::Bin(lir::BinOp::I64(bit_ibin(k))),
            super::lower::i64c(0xFFFF_FFFF),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And)),
            super::lower::i64c(super::arith::tag_bits()),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
        ]
    }
}

/// The value block: the tagged result of operation `k` on locals 1 and 2.
pub open spec fn bit_val(k: nat) -> Seq<lir::Instr> {
    super::lower::sext_local(1) + (super::lower::sext_local(2) + bit_tail(k))
}

/// The word the value block pushes, from the sign-extended payloads.
pub open spec fn bit_word(k: nat, xa: u64, xb: u64) -> u64 {
    super::arith::tagged(
        lir::ibin64(
            bit_ibin(k),
            xa,
            if k >= 3 {
                xb & 31
            } else {
                xb
            },
        ),
    )
}

/// The lowering of operation `k` on registers `a` and `b` into `dst`.
pub open spec fn lower_bit(k: nat, dst: nat, a: nat, b: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::lower_bin(bit_val(k), dst, a, b, op, pc)
}

/// The value block is simple, and short.
pub proof fn lemma_bit_val_simple(k: nat)
    ensures
        super::run::all_simple(bit_val(k)),
        bit_val(k).len() < 40,
{
    super::intops::lemma_literals_simple(0);
    let t = bit_tail(k);
    assert(super::run::all_simple(t)) by {
        assert forall|i: int| 0 <= i < t.len() implies super::run::is_simple(#[trigger] t[i]) by {
            assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6);
        }
    }
    super::intops::lemma_simple_concat(super::lower::sext_local(2), t);
    super::intops::lemma_simple_concat(super::lower::sext_local(1), super::lower::sext_local(2) + t);
}

/// The tail's trace: from the two sign-extended payloads on the stack it
/// leaves the word.
pub proof fn lemma_bit_tail_trace(lay: lir::Layout, k: nat, st: lir::St, base: Seq<lir::Val>, xa: u64, xb: u64)
    requires
        st.stack == base.push(lir::Val::I64(xa)).push(lir::Val::I64(xb)),
    ensures
        super::run::exec(lay, bit_tail(k), st) == lir::Outcome::Normal(
            st.with_stack(base.push(lir::Val::I64(bit_word(k, xa, xb)))),
        ),
{
    broadcast use super::blocks::lemma_below_push1, super::blocks::lemma_below_push2, super::blocks::lemma_drop_last_push;

    reveal_with_fuel(super::run::exec, 8);
}

/// The value block's trace.
pub proof fn lemma_bit_val_trace(lay: lir::Layout, k: nat, va: u64, vb: u64)
    ensures
        super::blocks::val_computes(
            lay,
            bit_val(k),
            va,
            vb,
            bit_word(k, super::arith::sext(super::arith::lo32(va)), super::arith::sext(super::arith::lo32(vb))),
        ),
{
    let xa = super::arith::sext(super::arith::lo32(va));
    let xb = super::arith::sext(super::arith::lo32(vb));
    let w = bit_word(k, xa, xb);
    let t = bit_tail(k);
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, bit_val(k), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) && st1.locals[2]
            == lir::Val::I64(vb) implies super::run::exec(lay, bit_val(k), st1) == lir::Outcome::Normal(
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
        lemma_bit_tail_trace(lay, k, s2, st1.stack, xa, xb);
    }
}

/// The low half of a left shift: shifting the sign extension and keeping 32
/// bits is shifting the 32-bit value.
pub proof fn lemma_shl_low(ia: i32, c: u32)
    requires
        c < 32,
    ensures
        ((((ia as i64) as u64) << (c as u64)) & 0xFFFF_FFFFu64) == (((ia as u32) << c) as u64),
        ((ia as int) * (vstd::arithmetic::power2::pow2(c as nat) as int)) % 4294967296int == (((ia as u32) << c) as int),
{
    assert(((((ia as i64) as u64) << (c as u64)) & 0xFFFF_FFFFu64) == (((ia as u32) << c) as u64)) by (bit_vector)
        requires
            c < 32,
    ;
    assert((((ia as int) * ((1u32 << c) as int)) % 4294967296int) == (((ia as u32) << c) as int)) by (bit_vector)
        requires
            c < 32,
    ;
    vstd::bits::lemma_u32_pow2_no_overflow(c as nat);
    vstd::bits::lemma_u32_shl_is_mul(1u32, c);
    assert((1u32 << c) as int == vstd::arithmetic::power2::pow2(c as nat) as int);
}

/// LIR's `shl` of a word by a small count is the machine's.
pub proof fn lemma_shl64(x: u64, y: u64)
    requires
        y < 64,
    ensures
        lir::ibin64(lir::IBin::Shl, x, y) == (x << y),
{
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::bits::lemma_u64_pow2_no_overflow(y as nat);
    vstd::bits::lemma_u64_shl_is_mul(1u64, y);
    assert((1u64 << y) as int == vstd::arithmetic::power2::pow2(y as nat) as int);
    assert((y as int % 64) as nat == y as nat);
    assert((((x as int) * ((1u64 << y) as int)) % 0x1_0000_0000_0000_0000int) as u64 == (x << y)) by (bit_vector)
        requires
            y < 64,
    ;
}

/// `wrap_i32` reduces modulo 2^32: its low 32 bits are `n mod 2^32`.
pub proof fn lemma_wrap_i32_low(n: int)
    ensures
        ((js::wrap_i32(n) as u32) as int) == n % 4294967296int,
{
    let m: int = n % 4294967296int;
    assert(0 <= m < 4294967296int);
    let mu = m as u32;
    assert(mu as int == m);
    if m >= 2147483648int {
        assert(((((mu as int) - 4294967296int) as i32) as u32) == mu) by (bit_vector)
            requires
                mu >= 2147483648u32,
        ;
    } else {
        assert((((mu as int) as i32) as u32) == mu) by (bit_vector)
            requires
                mu < 2147483648u32,
        ;
    }
}

/// The arithmetic right shift's quotient is an int32.
pub proof fn lemma_shr_range(ia: i32, c: nat)
    requires
        c < 32,
    ensures
        -2147483648int <= (ia as int) / (vstd::arithmetic::power2::pow2(c) as int) <= 2147483647int,
{
    let d = vstd::arithmetic::power2::pow2(c) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(c);
    assert(d >= 1);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(ia as int, 2147483647int, d);
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(2147483647int, 1, d);
    assert(2147483647int / 1 == 2147483647int) by {
        vstd::arithmetic::div_mod::lemma_div_basics(2147483647int);
    }
    let q = (ia as int) / d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(ia as int, d);
    vstd::arithmetic::div_mod::lemma_mod_bound(ia as int, d);
    let r = (ia as int) % d;
    if q <= -2147483649int {
        assert(d * (q + 2147483649int) <= 0) by (nonlinear_arith)
            requires
                d >= 1,
                q + 2147483649int <= 0,
        ;
        assert(d * q + d * 2147483649int <= 0) by (nonlinear_arith)
            requires
                d * (q + 2147483649int) <= 0,
        ;
        assert(d * 2147483649int >= 2147483649int) by (nonlinear_arith)
            requires
                d >= 1,
        ;
        assert(false);
    }
}

/// LIR's arithmetic right shift of a sign-extended int32 by a small count is
/// the sign extension of the int32 shifted.
pub proof fn lemma_shrs64(ia: i32, y: u64)
    requires
        y < 32,
    ensures
        lir::ibin64(lir::IBin::ShrS, (ia as i64) as u64, y) == ((((ia as int) / (vstd::arithmetic::power2::pow2(y as nat) as int)) as i32)
            as i64) as u64,
{
    let xa = (ia as i64) as u64;
    super::arith::lemma_signed64(xa);
    assert(((ia as i64) as u64) as i64 == (ia as i64)) by (bit_vector);
    assert(lir::signed_of(64, xa as int) == ia as int);
    lemma_shr_range(ia, y as nat);
    let q: int = (ia as int) / (vstd::arithmetic::power2::pow2(y as nat) as int);
    let r: i32 = q as i32;
    assert(r as int == q);
    vstd::arithmetic::power2::lemma2_to64_rest();
    assert((y as int % 64) as nat == y as nat);
    assert((((r as int) % 0x1_0000_0000_0000_0000int) as u64) == ((r as i64) as u64)) by (bit_vector);
}

/// The word of operation `k` is the encoding of the int32 result.
pub proof fn lemma_bit_word(k: nat, va: u64, vb: u64)
    requires
        k <= 4,
        js::is_int32(va),
        js::is_int32(vb),
    ensures
        bit_word(k, super::arith::sext(super::arith::lo32(va)), super::arith::sext(super::arith::lo32(vb)))
            == js::enc_int32(bit_res(k, js::int32_of(va), js::int32_of(vb))),
{
    super::arith::lemma_payload(va);
    super::arith::lemma_payload(vb);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    let xa = super::arith::sext(super::arith::lo32(va));
    let xb = super::arith::sext(super::arith::lo32(vb));
    assert(xa == (ia as i64) as u64);
    assert(xb == (ib as i64) as u64);
    if k == 0 {
        assert(super::arith::tagged(xa & xb) == js::enc_int32(ia & ib)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
    } else if k == 1 {
        assert(super::arith::tagged(xa | xb) == js::enc_int32(ia | ib)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
    } else if k == 2 {
        assert(super::arith::tagged(xa ^ xb) == js::enc_int32(ia ^ ib)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
                xb == (ib as i64) as u64,
        ;
    } else {
        let y = xb & 31;
        assert((xb & 31) == (((ib as u32) % 32u32) as u64)) by (bit_vector)
            requires
                xb == (ib as i64) as u64,
        ;
        let c: u32 = (ib as u32) % 32u32;
        assert(y == c as u64);
        assert(c as nat == shift_count(ib));
        if k == 3 {
            lemma_shl64(xa, y);
            lemma_shl_low(ia, c);
            let n: int = ia as int * vstd::arithmetic::power2::pow2(shift_count(ib)) as int;
            lemma_wrap_i32_low(n);
            let r = js::wrap_i32(n);
            let s = xa << y;
            assert(((s & 0xFFFF_FFFFu64)) == (((ia as u32) << c) as u64));
            assert((r as u32) as int == (((ia as u32) << c) as int));
            assert((s & 0xFFFF_FFFFu64) == ((r as u32) as u64)) by (bit_vector)
                requires
                    (s & 0xFFFF_FFFFu64) == (((ia as u32) << c) as u64),
                    (r as u32) as int == (((ia as u32) << c) as int),
            ;
            assert(super::arith::tagged(s) == js::enc_int32(r)) by (bit_vector)
                requires
                    (s & 0xFFFF_FFFFu64) == ((r as u32) as u64),
            ;
        } else {
            lemma_shrs64(ia, y);
            let r: i32 = ((ia as int) / (vstd::arithmetic::power2::pow2(shift_count(ib)) as int)) as i32;
            let s = lir::ibin64(lir::IBin::ShrS, xa, y);
            assert(s == ((r as i64) as u64));
            assert(super::arith::tagged(s) == js::enc_int32(r)) by (bit_vector)
                requires
                    s == ((r as i64) as u64),
            ;
        }
    }
}

/// The semantics of operation `k` on two int32 registers.
pub proof fn lemma_bit_sem(s: js::State, k: nat, dst: nat, a: nat, b: nat)
    requires
        k <= 4,
        js::is_int32(js::reg(s, a)),
        js::is_int32(js::reg(s, b)),
    ensures
        js::fast_path(s, bit_op(k, dst, a, b)),
        js::fast_step(s, bit_op(k, dst, a, b)) == js::next(
            js::set_reg(
                s,
                dst,
                js::enc_int32(bit_res(k, js::int32_of(js::reg(s, a)), js::int32_of(js::reg(s, b)))),
            ),
        ),
{
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let ia = js::int32_of(va);
    let ib = js::int32_of(vb);
    super::numord::lemma_to_int32(ia);
    super::numord::lemma_to_int32(ib);
    super::numord::lemma_to_uint32(ib);
    assert(js::num_bits(va) == js::f64_of_int(ia as int));
    assert(js::num_bits(vb) == js::f64_of_int(ib as int));
    assert(js::is_number(va) && js::is_number(vb));
}

/// An int32 bitwise or shift op: the lowering refines `step`.
pub proof fn lemma_bit_op(
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
        k <= 4,
        op == bit_op(k, dst, a, b),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
        super::lower::lower(c, op, pc, lbl) == lower_bit(k, dst, a, b, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_bit_val_simple(k);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let w = js::enc_int32(bit_res(k, js::int32_of(va), js::int32_of(vb)));
    if js::is_int32(va) && js::is_int32(vb) {
        lemma_bit_sem(s, k, dst, a, b);
        lemma_bit_val_trace(lay, k, va, vb);
        lemma_bit_word(k, va, vb);
    }
    super::blocks::lemma_bin_op(op, pc, lbl, lay, s, st, fuel, dst, a, b, bit_val(k), w);
}

} // verus!
