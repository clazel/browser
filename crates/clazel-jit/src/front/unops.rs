//! The int32 unary ops: `Inc`, `Dec`, `Neg`, `BitNot`.
//!
//! One guard each, computed from the operand word alone: the operand is an
//! int32 and (for `Inc`) not `2^31 - 1`, (for `Dec`) not `-2^31`, (for `Neg`)
//! neither `0` (`-0` is not an int32) nor `-2^31`. Those are exactly the cases
//! where the semantics' result is an int32; the rest exit to the handler. The
//! value is the 64-bit operation on the sign-extended payload, low half,
//! tagged. (No overflow test follows the operation: the guard has already
//! ruled it out, so the result fits.)
//!
//! `k` is the op: 0 `Inc`, 1 `Dec`, 2 `Neg`, 3 `BitNot`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bytecode op of `k`.
pub open spec fn un_op(k: nat, dst: nat, src: nat) -> js::Op {
    if k == 0 {
        js::Op::Inc { dst, src }
    } else if k == 1 {
        js::Op::Dec { dst, src }
    } else if k == 2 {
        js::Op::Neg { dst, src }
    } else {
        js::Op::BitNot { dst, src }
    }
}

/// `-2^31` sign-extended to 64 bits, as a word.
pub open spec fn min32_word() -> u64 {
    0xFFFF_FFFF_8000_0000
}

/// One comparison of the sign-extended payload of local 1 with `c`
/// (`ne`), `and`ed into the flag on the stack.
pub open spec fn ne_half(c: u64) -> Seq<lir::Instr> {
    seq![
        lir::Instr::LocalGet(1),
        lir::Instr::Un(lir::UnOp::I32WrapI64),
        lir::Instr::Un(lir::UnOp::I64ExtendI32S),
        super::lower::i64c(c),
        super::lower::cmp64(lir::ICmp::Ne),
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ]
}

/// The flag block's instructions after the tag test: compare the
/// sign-extended payload with the excluded values.
pub open spec fn un_flag_tail(k: nat) -> Seq<lir::Instr> {
    if k == 0 {
        ne_half(0x7FFF_FFFF)
    } else if k == 1 {
        ne_half(min32_word())
    } else if k == 2 {
        ne_half(0) + ne_half(min32_word())
    } else {
        seq![]
    }
}

/// The flag block: the tag test of local 1, then the tail.
pub open spec fn un_flag(k: nat) -> Seq<lir::Instr> {
    super::lower::tag_test(1) + un_flag_tail(k)
}

/// `1` if the sign-extended payload `xa` differs from `c`.
pub open spec fn ne_flag(xa: u64, c: u64) -> u32 {
    lir::bool_i32(lir::icmp(lir::ICmp::Ne, 64, xa as int, c as int))
}

/// The flag's value for operand word `va`.
pub open spec fn un_g(k: nat, va: u64) -> u32 {
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    let xa = super::arith::sext(super::arith::lo32(va));
    if k == 0 {
        lir::ibin32(lir::IBin::And, isint, ne_flag(xa, 0x7FFF_FFFF))
    } else if k == 1 {
        lir::ibin32(lir::IBin::And, isint, ne_flag(xa, min32_word()))
    } else if k == 2 {
        lir::ibin32(
            lir::IBin::And,
            lir::ibin32(lir::IBin::And, isint, ne_flag(xa, 0)),
            ne_flag(xa, min32_word()),
        )
    } else {
        isint
    }
}

/// What the guard lets through, for an int32 `ia`.
pub open spec fn un_cond(k: nat, ia: i32) -> bool {
    if k == 0 {
        ia != 2147483647
    } else if k == 1 {
        ia != -2147483648
    } else if k == 2 {
        ia != 0 && ia != -2147483648
    } else {
        true
    }
}

/// The value block: the tagged result of the operation on the payload in
/// local 1.
pub open spec fn un_val(k: nat) -> Seq<lir::Instr> {
    let sx0 = lir::Instr::LocalGet(1);
    let sx1 = lir::Instr::Un(lir::UnOp::I32WrapI64);
    let sx2 = lir::Instr::Un(lir::UnOp::I64ExtendI32S);
    let mask = super::lower::i64c(0xFFFF_FFFF);
    let and64 = lir::Instr::Bin(lir::BinOp::I64(lir::IBin::And));
    let tag = super::lower::i64c(super::arith::tag_bits());
    let or64 = lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or));
    if k == 0 {
        seq![
            sx0,
            sx1,
            sx2,
            super::lower::i64c(1),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Add)),
            mask,
            and64,
            tag,
            or64,
        ]
    } else if k == 1 {
        seq![
            sx0,
            sx1,
            sx2,
            super::lower::i64c(1),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Sub)),
            mask,
            and64,
            tag,
            or64,
        ]
    } else if k == 2 {
        seq![
            super::lower::i64c(0),
            sx0,
            sx1,
            sx2,
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Sub)),
            mask,
            and64,
            tag,
            or64,
        ]
    } else {
        seq![
            sx0,
            sx1,
            sx2,
            super::lower::i64c(0xFFFF_FFFF_FFFF_FFFF),
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Xor)),
            mask,
            and64,
            tag,
            or64,
        ]
    }
}

/// The 64-bit result of the operation on the sign-extended payload.
pub open spec fn un_s(k: nat, xa: u64) -> u64 {
    if k == 0 {
        lir::ibin64(lir::IBin::Add, xa, 1)
    } else if k == 1 {
        lir::ibin64(lir::IBin::Sub, xa, 1)
    } else if k == 2 {
        lir::ibin64(lir::IBin::Sub, 0, xa)
    } else {
        lir::ibin64(lir::IBin::Xor, xa, 0xFFFF_FFFF_FFFF_FFFF)
    }
}

/// The word the value block pushes.
pub open spec fn un_word(k: nat, xa: u64) -> u64 {
    super::arith::tagged(un_s(k, xa))
}

/// The int32 result of the op on an int32, as the semantics writes it.
pub open spec fn un_res(k: nat, ia: i32) -> i32 {
    if k == 0 {
        ((ia as int) + 1) as i32
    } else if k == 1 {
        ((ia as int) - 1) as i32
    } else if k == 2 {
        (-(ia as int)) as i32
    } else {
        (-1 - (ia as int)) as i32
    }
}

/// The lowering of op `k` on register `src` into `dst`.
pub open spec fn lower_unary(k: nat, dst: nat, src: nat, op: js::Op, pc: nat) -> lir::Instr {
    super::blocks::lower_un(un_flag(k), un_val(k), dst, src, op, pc)
}

/// A comparison half is simple.
pub proof fn lemma_half_simple(c: u64)
    ensures
        super::run::all_simple(ne_half(c)),
        ne_half(c).len() == 6,
{
    let h = ne_half(c);
    assert(super::run::all_simple(h)) by {
        assert forall|i: int| 0 <= i < h.len() implies super::run::is_simple(#[trigger] h[i]) by {
            assert(0 <= i < 6);
        }
    }
}

/// The flag and value blocks are simple and short.
pub proof fn lemma_un_simple(k: nat)
    ensures
        super::run::all_simple(un_flag(k)),
        un_flag(k).len() < 40,
        super::run::all_simple(un_val(k)),
        un_val(k).len() < 40,
{
    super::intops::lemma_literals_simple(0);
    lemma_half_simple(0x7FFF_FFFF);
    lemma_half_simple(min32_word());
    lemma_half_simple(0);
    super::intops::lemma_simple_concat(ne_half(0), ne_half(min32_word()));
    let t = un_flag_tail(k);
    assert(super::run::all_simple(t)) by {
        if k > 2 {
            assert(t =~= Seq::<lir::Instr>::empty());
        }
    }
    super::intops::lemma_simple_concat(super::lower::tag_test(1), t);
    let v = un_val(k);
    assert(super::run::all_simple(v)) by {
        assert forall|i: int| 0 <= i < v.len() implies super::run::is_simple(#[trigger] v[i]) by {
            assert(0 <= i < 9);
        }
    }
}

/// One comparison half's trace: the flag `e` on the stack becomes `e & ne`.
pub proof fn lemma_half_trace(lay: lir::Layout, st: lir::St, base: Seq<lir::Val>, va: u64, e: u32, c: u64)
    requires
        st.stack == base.push(lir::Val::I32(e)),
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
    ensures
        super::run::exec(lay, ne_half(c), st) == lir::Outcome::Normal(
            st.with_stack(
                base.push(
                    lir::Val::I32(
                        lir::ibin32(
                            lir::IBin::And,
                            e,
                            ne_flag(super::arith::sext(super::arith::lo32(va)), c),
                        ),
                    ),
                ),
            ),
        ),
{
    broadcast use super::blocks::stack_shape;

    super::arith::lemma_sx(super::arith::lo32(va));
    reveal_with_fuel(super::run::exec, 7);
}

/// The flag block's trace.
pub proof fn lemma_un_flag_trace(lay: lir::Layout, k: nat, va: u64)
    ensures
        super::blocks::flag_computes(lay, un_flag(k), va, un_g(k, va)),
{
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, un_flag(k), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) implies super::run::exec(
        lay,
        un_flag(k),
        st1,
    ) == lir::Outcome::Normal(st1.with_stack(st1.stack.push(lir::Val::I32(un_g(k, va))))) by {
        super::trace::lemma_exec_tag_test(lay, st1, 1, va);
        let s1 = st1.with_stack(st1.stack.push(lir::Val::I32(isint)));
        super::trace::lemma_exec_app(lay, super::lower::tag_test(1), un_flag_tail(k), st1, s1);
        let xa = super::arith::sext(super::arith::lo32(va));
        if k == 0 {
            lemma_half_trace(lay, s1, st1.stack, va, isint, 0x7FFF_FFFF);
        } else if k == 1 {
            lemma_half_trace(lay, s1, st1.stack, va, isint, min32_word());
        } else if k == 2 {
            lemma_half_trace(lay, s1, st1.stack, va, isint, 0);
            let e1 = lir::ibin32(lir::IBin::And, isint, ne_flag(xa, 0));
            let s2 = st1.with_stack(st1.stack.push(lir::Val::I32(e1)));
            super::trace::lemma_exec_app(lay, ne_half(0), ne_half(min32_word()), s1, s2);
            lemma_half_trace(lay, s2, st1.stack, va, e1, min32_word());
        } else {
            assert(un_flag_tail(k) =~= Seq::<lir::Instr>::empty());
            reveal_with_fuel(super::run::exec, 1);
        }
    }
}

/// `1 & 1` is the only non-zero `and` of two flags.
pub proof fn lemma_and01(e1: u32, e2: u32)
    requires
        e1 == 0 || e1 == 1,
        e2 == 0 || e2 == 1,
    ensures
        ((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1),
{
    assert(((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1)) by (bit_vector)
        requires
            e1 == 0 || e1 == 1,
            e2 == 0 || e2 == 1,
    ;
}

/// The `and` of two flags is a flag.
pub proof fn lemma_and01_range(e1: u32, e2: u32)
    requires
        e1 == 0 || e1 == 1,
        e2 == 0 || e2 == 1,
    ensures
        (e1 & e2) == 0 || (e1 & e2) == 1,
{
    assert(((e1 & e2) == 0 || (e1 & e2) == 1)) by (bit_vector)
        requires
            e1 == 0 || e1 == 1,
            e2 == 0 || e2 == 1,
    ;
}

/// The flag is non-zero exactly for an int32 the semantics' fast result
/// covers.
pub proof fn lemma_un_g(k: nat, va: u64)
    requires
        k <= 3,
    ensures
        (un_g(k, va) != 0) <==> (js::is_int32(va) && un_cond(k, js::int32_of(va))),
{
    super::trace::lemma_tag_test(va);
    let isint = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    let xa = super::arith::sext(super::arith::lo32(va));
    assert(isint == 0 || isint == 1);
    if js::is_int32(va) {
        super::arith::lemma_payload(va);
        let ia = js::int32_of(va);
        assert(xa == (ia as i64) as u64);
        assert(isint == 1);
        assert(ne_flag(xa, 0x7FFF_FFFF) == 0 || ne_flag(xa, 0x7FFF_FFFF) == 1);
        assert(ne_flag(xa, min32_word()) == 0 || ne_flag(xa, min32_word()) == 1);
        assert(ne_flag(xa, 0) == 0 || ne_flag(xa, 0) == 1);
        assert((xa != 0x7FFF_FFFFu64) <==> (ia != 2147483647)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
        assert((xa != 0xFFFF_FFFF_8000_0000u64) <==> (ia != -2147483648)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
        assert((xa != 0u64) <==> (ia != 0)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
        if k == 0 {
            lemma_and01(isint, ne_flag(xa, 0x7FFF_FFFF));
        } else if k == 1 {
            lemma_and01(isint, ne_flag(xa, min32_word()));
        } else if k == 2 {
            lemma_and01(isint, ne_flag(xa, 0));
            let e = lir::ibin32(lir::IBin::And, isint, ne_flag(xa, 0));
            lemma_and01_range(isint, ne_flag(xa, 0));
            assert(e == 0 || e == 1);
            lemma_and01(e, ne_flag(xa, min32_word()));
        }
    } else {
        assert(isint == 0);
        if k == 0 {
            lemma_and01(isint, ne_flag(xa, 0x7FFF_FFFF));
        } else if k == 1 {
            lemma_and01(isint, ne_flag(xa, min32_word()));
        } else if k == 2 {
            lemma_and01(isint, ne_flag(xa, 0));
            let e = lir::ibin32(lir::IBin::And, isint, ne_flag(xa, 0));
            lemma_and01_range(isint, ne_flag(xa, 0));
            assert(e == 0 || e == 1);
            lemma_and01(e, ne_flag(xa, min32_word()));
        }
    }
}

/// The value block's trace.
pub proof fn lemma_un_val_trace(lay: lir::Layout, k: nat, va: u64)
    ensures
        super::blocks::val_computes1(lay, un_val(k), va, un_word(k, super::arith::sext(super::arith::lo32(va)))),
{
    let xa = super::arith::sext(super::arith::lo32(va));
    super::arith::lemma_sx(super::arith::lo32(va));
    assert forall|st1: lir::St|
        #![trigger super::run::exec(lay, un_val(k), st1)]
        st1.locals.len() == nlocals() && st1.locals[1] == lir::Val::I64(va) implies super::run::exec(
        lay,
        un_val(k),
        st1,
    ) == lir::Outcome::Normal(st1.with_stack(st1.stack.push(lir::Val::I64(un_word(k, xa))))) by {
        broadcast use super::blocks::stack_shape;

        reveal_with_fuel(super::run::exec, 10);
        if k == 0 {
            assert(super::run::exec(lay, un_val(0), st1) == lir::Outcome::Normal(
                st1.with_stack(st1.stack.push(lir::Val::I64(un_word(0, xa)))),
            ));
        } else if k == 1 {
            assert(super::run::exec(lay, un_val(1), st1) == lir::Outcome::Normal(
                st1.with_stack(st1.stack.push(lir::Val::I64(un_word(1, xa)))),
            ));
        } else if k == 2 {
            assert(super::run::exec(lay, un_val(2), st1) == lir::Outcome::Normal(
                st1.with_stack(st1.stack.push(lir::Val::I64(un_word(2, xa)))),
            ));
        } else {
            assert(super::run::exec(lay, un_val(k), st1) == lir::Outcome::Normal(
                st1.with_stack(st1.stack.push(lir::Val::I64(un_word(k, xa)))),
            ));
        }
    }
}

/// The value block's word is the encoding of the int32 result.
pub proof fn lemma_un_word(k: nat, va: u64)
    requires
        k <= 3,
        js::is_int32(va),
    ensures
        un_word(k, super::arith::sext(super::arith::lo32(va))) == js::enc_int32(un_res(k, js::int32_of(va))),
{
    super::arith::lemma_payload(va);
    let ia = js::int32_of(va);
    let xa = super::arith::sext(super::arith::lo32(va));
    assert(xa == (ia as i64) as u64);
    if k == 0 {
        super::arith::lemma_ibin64(0, xa, 1);
        assert(super::arith::tagged(xa.wrapping_add(1)) == js::enc_int32(((ia as int) + 1) as i32)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
    } else if k == 1 {
        super::arith::lemma_ibin64(1, xa, 1);
        assert(super::arith::tagged(xa.wrapping_sub(1)) == js::enc_int32(((ia as int) - 1) as i32)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
    } else if k == 2 {
        super::arith::lemma_ibin64(1, 0, xa);
        assert(super::arith::tagged((0u64).wrapping_sub(xa)) == js::enc_int32((-(ia as int)) as i32)) by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
    } else {
        assert(super::arith::tagged(xa ^ 0xFFFF_FFFF_FFFF_FFFFu64) == js::enc_int32((-1 - (ia as int)) as i32))
            by (bit_vector)
            requires
                xa == (ia as i64) as u64,
        ;
    }
}

/// The semantics of op `k` on an int32 register the guard lets through.
pub proof fn lemma_un_sem(s: js::State, k: nat, dst: nat, src: nat)
    requires
        k <= 3,
        js::is_int32(js::reg(s, src)),
        un_cond(k, js::int32_of(js::reg(s, src))),
    ensures
        js::fast_path(s, un_op(k, dst, src)),
        js::fast_step(s, un_op(k, dst, src)) == js::next(
            js::set_reg(s, dst, js::enc_int32(un_res(k, js::int32_of(js::reg(s, src))))),
        ),
{
    let va = js::reg(s, src);
    let ia = js::int32_of(va);
    clazel_js_vm::lemmas::lemma_decode_enc_int32(1);
    assert(js::is_int32(js::enc_int32(1)));
    assert(js::int32_of(js::enc_int32(1)) == 1);
    if k == 3 {
        super::numord::lemma_to_int32(ia);
        assert(js::num_bits(va) == js::f64_of_int(ia as int));
    }
    assert(js::is_number(va));
}

/// An int32 unary op: the lowering refines `step`.
pub proof fn lemma_un_op_k(
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
    src: nat,
)
    requires
        super::proofs::pre(c, op, pc, lay, s, st, fuel),
        k <= 3,
        op == un_op(k, dst, src),
        js::reg_ok(js::cur_code(s), dst),
        js::reg_ok(js::cur_code(s), src),
        super::lower::lower(c, op, pc, lbl) == lower_unary(k, dst, src, op, pc),
    ensures
        outcome_refines(lay, s, op, lbl, lir::eval(lay, super::lower::lower(c, op, pc, lbl), st, fuel)),
{
    lemma_un_simple(k);
    let va = js::reg(s, src);
    let g = un_g(k, va);
    let w = js::enc_int32(un_res(k, js::int32_of(va)));
    lemma_un_flag_trace(lay, k, va);
    lemma_un_g(k, va);
    if g != 0 {
        lemma_un_sem(s, k, dst, src);
        lemma_un_val_trace(lay, k, va);
        lemma_un_word(k, va);
    }
    super::blocks::lemma_un_op(op, pc, lbl, lay, s, st, fuel, dst, src, un_flag(k), un_val(k), g, w);
}

} // verus!
