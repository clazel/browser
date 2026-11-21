//! What the blocks of the small-integer lowerings do to LIR's state: the
//! tag test, the sign extension, the operation and the two guards, each as
//! [`exec`] of its instruction list from a state whose scratch locals hold
//! the operands.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// Running `a` and then `b`, when `a` ends in `s1`.
pub proof fn lemma_exec_app(
    lay: lir::Layout,
    a: Seq<lir::Instr>,
    b: Seq<lir::Instr>,
    st: lir::St,
    s1: lir::St,
)
    requires
        super::run::exec(lay, a, st) == lir::Outcome::Normal(s1),
    ensures
        super::run::exec(lay, a + b, st) == super::run::exec(lay, b, s1),
{
    super::run::lemma_exec_concat(lay, a, b, st);
}

/// Setting a scratch local to an `i64` keeps the locals related.
pub proof fn lemma_locals_set(s: js::State, l: Seq<lir::Val>, x: nat, v: u64)
    requires
        locals_rel(s, l),
        1 <= x < nlocals(),
    ensures
        locals_rel(s, l.update(x as int, lir::Val::I64(v))),
{
    let l2 = l.update(x as int, lir::Val::I64(v));
    assert(l2.len() == l.len());
    assert(l2[0] == l[0]);
    assert forall|j: int| 1 <= j < l2.len() implies #[trigger] l2[j] is I64 by {
        if j != x {
            assert(l2[j] == l[j]);
        }
    }
}

/// `i64.shr_u` by 32 is the machine shift.
pub proof fn lemma_shr32(v: u64)
    ensures
        lir::ibin64(lir::IBin::ShrU, v, 32) == (v >> 32u64),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(((v as int) / 0x1_0000_0000int) as u64 == (v >> 32u64)) by (bit_vector);
}

/// The tag word's test: a word's high half is `tag_hi` exactly when it is an
/// int32 value.
pub proof fn lemma_tag_test(v: u64)
    ensures
        ((v >> 32u64) == super::arith::tag_hi()) <==> js::is_int32(v),
{
    assert((((v >> 32u64) == 0xFFF9_0000u64) <==> ((v >> 48u64) == 0xFFF9u64 && ((v >> 32u64) & 0xFFFFu64) == 0u64)))
        by (bit_vector);
}

/// The sign extension block pushes [`sext`] of the low half.
pub proof fn lemma_exec_sext_local(lay: lir::Layout, st: lir::St, x: nat, v: u64)
    requires
        x < st.locals.len(),
        st.locals[x as int] == lir::Val::I64(v),
    ensures
        super::run::exec(lay, super::lower::sext_local(x), st) == lir::Outcome::Normal(
            st.with_stack(st.stack.push(lir::Val::I64(super::arith::sext(super::arith::lo32(v))))),
        ),
{
    super::arith::lemma_sx(super::arith::lo32(v));
    reveal_with_fuel(super::run::exec, 4);
    let s1 = st.with_stack(st.stack.push(lir::Val::I64(v)));
    let s2 = st.with_stack(st.stack.push(lir::Val::I32(super::arith::lo32(v))));
    assert(lir::below(s1.stack, 1) =~= st.stack);
    assert(lir::below(s2.stack, 1) =~= st.stack);
}

/// The tag test block pushes the result of the comparison.
pub proof fn lemma_exec_tag_test(lay: lir::Layout, st: lir::St, x: nat, v: u64)
    requires
        x < st.locals.len(),
        st.locals[x as int] == lir::Val::I64(v),
    ensures
        super::run::exec(lay, super::lower::tag_test(x), st) == lir::Outcome::Normal(
            st.with_stack(st.stack.push(lir::Val::I32(lir::bool_i32((v >> 32u64) == super::arith::tag_hi())))),
        ),
{
    lemma_shr32(v);
    reveal_with_fuel(super::run::exec, 6);
    let s1 = st.with_stack(st.stack.push(lir::Val::I64(v)));
    let s2 = s1.with_stack(s1.stack.push(lir::Val::I64(32)));
    let s3 = st.with_stack(st.stack.push(lir::Val::I64(v >> 32u64)));
    let s4 = s3.with_stack(s3.stack.push(lir::Val::I64(super::arith::tag_hi())));
    assert(lir::below(s2.stack, 2) =~= st.stack);
    assert(lir::below(s4.stack, 2) =~= st.stack);
}


/// The operand block loads both registers into scratch locals 1 and 2 and
/// leaves the stack empty and the relation intact.
pub proof fn lemma_operands_trace(lay: lir::Layout, s: js::State, st: lir::St, a: nat, b: nat)
    requires
        rel(lay, s, st),
        st.stack == Seq::<lir::Val>::empty(),
        js::state_wf(s),
        js::reg_ok(js::cur_code(s), a),
        js::reg_ok(js::cur_code(s), b),
    ensures
        ({
            let st2 = lir::St {
                stack: Seq::<lir::Val>::empty(),
                locals: st.locals.update(1, lir::Val::I64(js::reg(s, a))).update(
                    2,
                    lir::Val::I64(js::reg(s, b)),
                ),
                mem: st.mem,
            };
            &&& super::run::exec(lay, super::lower::operands_ins(a, b), st) == lir::Outcome::Normal(st2)
            &&& rel(lay, s, st2)
        }),
{
    super::proofs::lemma_reg_slot_ok(s, a);
    super::proofs::lemma_reg_slot_ok(s, b);
    let va = js::reg(s, a);
    let vb = js::reg(s, b);
    let la = super::lower::load_ins(reg_off(a));
    let lb = super::lower::load_ins(reg_off(b));
    let set1 = seq![lir::Instr::LocalSet(1)];
    let set2 = seq![lir::Instr::LocalSet(2)];
    // Load a.
    super::frame::lemma_exec_load(lay, s, st, reg_off(a));
    let s_a = st.with_stack(st.stack.push(lir::Val::I64(va)));
    // Set local 1.
    reveal_with_fuel(super::run::exec, 2);
    let loc1 = st.locals.update(1, lir::Val::I64(va));
    let s_b = lir::St { stack: Seq::<lir::Val>::empty(), locals: loc1, mem: st.mem };
    assert(s_a.stack.drop_last() =~= Seq::<lir::Val>::empty());
    assert(super::run::exec(lay, set1, s_a) == lir::Outcome::Normal(s_b));
    lemma_exec_app(lay, la, set1, st, s_a);
    assert(super::run::exec(lay, la + set1, st) == lir::Outcome::Normal(s_b));
    lemma_locals_set(s, st.locals, 1, va);
    assert(rel(lay, s, s_b));
    // Load b.
    super::frame::lemma_exec_load(lay, s, s_b, reg_off(b));
    let s_c = s_b.with_stack(s_b.stack.push(lir::Val::I64(vb)));
    lemma_exec_app(lay, la + set1, lb, st, s_b);
    assert(super::run::exec(lay, (la + set1) + lb, st) == lir::Outcome::Normal(s_c));
    // Set local 2.
    let loc2 = loc1.update(2, lir::Val::I64(vb));
    let st2 = lir::St { stack: Seq::<lir::Val>::empty(), locals: loc2, mem: st.mem };
    assert(s_c.stack.drop_last() =~= Seq::<lir::Val>::empty());
    assert(super::run::exec(lay, set2, s_c) == lir::Outcome::Normal(st2));
    lemma_exec_app(lay, (la + set1) + lb, set2, st, s_c);
    assert(super::lower::operands_ins(a, b) =~= ((la + set1) + lb) + set2);
    lemma_locals_set(s, loc1, 2, vb);
    assert(rel(lay, s, st2));
}

/// The first guard pushes whether both operands are int32 words.
pub proof fn lemma_guard1_trace(lay: lir::Layout, st: lir::St, va: u64, vb: u64)
    requires
        st.stack == Seq::<lir::Val>::empty(),
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
        st.locals[2] == lir::Val::I64(vb),
    ensures
        ({
            let g1 = lir::ibin32(
                lir::IBin::And,
                lir::bool_i32((va >> 32u64) == super::arith::tag_hi()),
                lir::bool_i32((vb >> 32u64) == super::arith::tag_hi()),
            );
            &&& super::run::exec(lay, super::lower::guard1_ins(), st) == lir::Outcome::Normal(
                st.with_stack(seq![lir::Val::I32(g1)]),
            )
            &&& (g1 != 0) <==> (js::is_int32(va) && js::is_int32(vb))
        }),
{
    let e1 = lir::bool_i32((va >> 32u64) == super::arith::tag_hi());
    let e2 = lir::bool_i32((vb >> 32u64) == super::arith::tag_hi());
    let g1 = lir::ibin32(lir::IBin::And, e1, e2);
    lemma_exec_tag_test(lay, st, 1, va);
    let s1 = st.with_stack(st.stack.push(lir::Val::I32(e1)));
    lemma_exec_app(lay, super::lower::tag_test(1), super::lower::tag_test(2), st, s1);
    lemma_exec_tag_test(lay, s1, 2, vb);
    let s2 = s1.with_stack(s1.stack.push(lir::Val::I32(e2)));
    lemma_exec_app(
        lay,
        super::lower::tag_test(1) + super::lower::tag_test(2),
        seq![lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And))],
        st,
        s2,
    );
    assert(super::lower::guard1_ins() =~= (super::lower::tag_test(1) + super::lower::tag_test(2)) + seq![
        lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
    ]);
    reveal_with_fuel(super::run::exec, 2);
    assert(s2.stack =~= seq![lir::Val::I32(e1), lir::Val::I32(e2)]);
    assert(lir::below(s2.stack, 2) =~= Seq::<lir::Val>::empty());
    assert(Seq::<lir::Val>::empty().push(lir::Val::I32(g1)) =~= seq![lir::Val::I32(g1)]);
    lemma_tag_test(va);
    lemma_tag_test(vb);
    assert(e1 == 0 || e1 == 1);
    assert(e2 == 0 || e2 == 1);
    assert(((e1 & e2) != 0) <==> (e1 == 1 && e2 == 1)) by (bit_vector)
        requires
            e1 == 0 || e1 == 1,
            e2 == 0 || e2 == 1,
    ;
}

/// The operation block computes the 64-bit result into local 3.
pub proof fn lemma_compute_trace(lay: lir::Layout, st: lir::St, k: nat, va: u64, vb: u64)
    requires
        st.stack == Seq::<lir::Val>::empty(),
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
        st.locals[2] == lir::Val::I64(vb),
    ensures
        super::run::exec(lay, super::lower::compute_ins(k), st) == lir::Outcome::Normal(
            lir::St {
                stack: Seq::<lir::Val>::empty(),
                locals: st.locals.update(3, lir::Val::I64(super::arith::s64(k, va, vb))),
                mem: st.mem,
            },
        ),
{
    let xa = super::arith::sext(super::arith::lo32(va));
    let xb = super::arith::sext(super::arith::lo32(vb));
    lemma_exec_sext_local(lay, st, 1, va);
    let s1 = st.with_stack(st.stack.push(lir::Val::I64(xa)));
    lemma_exec_app(lay, super::lower::sext_local(1), super::lower::sext_local(2), st, s1);
    lemma_exec_sext_local(lay, s1, 2, vb);
    let s2 = s1.with_stack(s1.stack.push(lir::Val::I64(xb)));
    let tail = seq![lir::Instr::Bin(lir::BinOp::I64(super::arith::ibin_of(k))), lir::Instr::LocalSet(3)];
    lemma_exec_app(lay, super::lower::sext_local(1) + super::lower::sext_local(2), tail, st, s2);
    assert(super::lower::compute_ins(k) =~= (super::lower::sext_local(1) + super::lower::sext_local(2)) + tail);
    reveal_with_fuel(super::run::exec, 3);
    assert(s2.stack =~= seq![lir::Val::I64(xa), lir::Val::I64(xb)]);
    assert(lir::below(s2.stack, 2) =~= Seq::<lir::Val>::empty());
    assert(Seq::<lir::Val>::empty().push(lir::Val::I64(super::arith::s64(k, va, vb))).drop_last()
        =~= Seq::<lir::Val>::empty());
}/// The fits test pushes whether local 3 is the sign extension of its low half.
pub proof fn lemma_fits_trace(lay: lir::Layout, st: lir::St, s: u64)
    requires
        st.locals.len() == nlocals(),
        st.locals[3] == lir::Val::I64(s),
    ensures
        super::run::exec(lay, super::lower::fits_ins(), st) == lir::Outcome::Normal(
            st.with_stack(st.stack.push(lir::Val::I32(super::arith::fits_flag(s)))),
        ),
{
    super::arith::lemma_sx(super::arith::lo32(s));
    reveal_with_fuel(super::run::exec, 6);
    let a1 = st.with_stack(st.stack.push(lir::Val::I64(s)));
    let a2 = st.with_stack(st.stack.push(lir::Val::I32(super::arith::lo32(s))));
    let a3 = st.with_stack(st.stack.push(lir::Val::I64(super::arith::sext(super::arith::lo32(s)))));
    let a4 = st.with_stack(st.stack.push(lir::Val::I64(super::arith::sext(super::arith::lo32(s)))).push(lir::Val::I64(s)));
    assert(lir::below(a1.stack, 1) =~= st.stack);
    assert(lir::below(a2.stack, 1) =~= st.stack);
    assert(lir::below(a4.stack, 2) =~= st.stack);
}

/// The first half of a product's extra test: the stack `[f]` becomes
/// `[f, s == 0, xa, xb]`.
pub proof fn lemma_mul_tail_a(lay: lir::Layout, st: lir::St, va: u64, vb: u64, s: u64, f: u32)
    requires
        st.stack == seq![lir::Val::I32(f)],
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
        st.locals[2] == lir::Val::I64(vb),
        st.locals[3] == lir::Val::I64(s),
    ensures
        ({
            let sx = seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)]
                + super::lower::sext_local(1) + super::lower::sext_local(2);
            super::run::exec(lay, sx, st) == lir::Outcome::Normal(
                st.with_stack(
                    seq![
                        lir::Val::I32(f),
                        lir::Val::I32(lir::bool_i32(s == 0)),
                        lir::Val::I64(super::arith::sext(super::arith::lo32(va))),
                        lir::Val::I64(super::arith::sext(super::arith::lo32(vb))),
                    ],
                ),
            )
        }),
{
    let t1 = seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)];
    reveal_with_fuel(super::run::exec, 3);
    let z0 = lir::bool_i32(s == 0);
    let b1 = st.with_stack(seq![lir::Val::I32(f), lir::Val::I64(s)]);
    let b2 = st.with_stack(seq![lir::Val::I32(f), lir::Val::I32(z0)]);
    assert(st.stack.push(lir::Val::I64(s)) =~= b1.stack);
    assert(lir::below(b1.stack, 1) =~= seq![lir::Val::I32(f)]);
    assert(seq![lir::Val::I32(f)].push(lir::Val::I32(z0)) =~= b2.stack);
    assert(super::run::exec(lay, t1, st) == lir::Outcome::Normal(b2));
    lemma_exec_app(lay, t1, super::lower::sext_local(1), st, b2);
    lemma_exec_sext_local(lay, b2, 1, va);
    let b3 = b2.with_stack(b2.stack.push(lir::Val::I64(super::arith::sext(super::arith::lo32(va)))));
    lemma_exec_app(lay, t1 + super::lower::sext_local(1), super::lower::sext_local(2), st, b3);
    lemma_exec_sext_local(lay, b3, 2, vb);
    let b4 = b3.with_stack(b3.stack.push(lir::Val::I64(super::arith::sext(super::arith::lo32(vb)))));
    assert(b4.stack =~= seq![
        lir::Val::I32(f),
        lir::Val::I32(z0),
        lir::Val::I64(super::arith::sext(super::arith::lo32(va))),
        lir::Val::I64(super::arith::sext(super::arith::lo32(vb))),
    ]);
}

/// The second half: `[f, z0, xa, xb]` becomes the guard's value.
pub proof fn lemma_mul_tail_b(lay: lir::Layout, st: lir::St, f: u32, z0: u32, xa: u64, xb: u64)
    requires
        st.stack == seq![
            lir::Val::I32(f),
            lir::Val::I32(z0),
            lir::Val::I64(xa),
            lir::Val::I64(xb),
        ],
    ensures
        ({
            let tail = seq![
                lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
                super::lower::i64c(0),
                super::lower::cmp64(lir::ICmp::LtS),
            ] + seq![
                lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
                lir::Instr::Un(lir::UnOp::I32Eqz),
                lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
            ];
            let lt = lir::bool_i32(
                lir::signed_of(64, (xa | xb) as int) < lir::signed_of(64, 0),
            );
            let zn = lir::ibin32(lir::IBin::And, z0, lt);
            super::run::exec(lay, tail, st) == lir::Outcome::Normal(
                st.with_stack(
                    seq![
                        lir::Val::I32(
                            lir::ibin32(lir::IBin::And, f, lir::bool_i32(zn == 0)),
                        ),
                    ],
                ),
            )
        }),
{
    reveal_with_fuel(super::run::exec, 7);
    let xo = xa | xb;
    let lt = lir::bool_i32(lir::signed_of(64, xo as int) < lir::signed_of(64, 0));
    let zn = lir::ibin32(lir::IBin::And, z0, lt);
    let zz = lir::bool_i32(zn == 0);
    assert(lir::below(st.stack, 2) =~= seq![lir::Val::I32(f), lir::Val::I32(z0)]);
    let c1 = seq![lir::Val::I32(f), lir::Val::I32(z0), lir::Val::I64(xo)];
    assert(seq![lir::Val::I32(f), lir::Val::I32(z0)].push(lir::Val::I64(xo)) =~= c1);
    let c2 = seq![lir::Val::I32(f), lir::Val::I32(z0), lir::Val::I64(xo), lir::Val::I64(0)];
    assert(c1.push(lir::Val::I64(0)) =~= c2);
    assert(lir::below(c2, 2) =~= seq![lir::Val::I32(f), lir::Val::I32(z0)]);
    let c3 = seq![lir::Val::I32(f), lir::Val::I32(z0), lir::Val::I32(lt)];
    assert(seq![lir::Val::I32(f), lir::Val::I32(z0)].push(lir::Val::I32(lt)) =~= c3);
    assert(lir::below(c3, 2) =~= seq![lir::Val::I32(f)]);
    let c4 = seq![lir::Val::I32(f), lir::Val::I32(zn)];
    assert(seq![lir::Val::I32(f)].push(lir::Val::I32(zn)) =~= c4);
    assert(lir::below(c4, 1) =~= seq![lir::Val::I32(f)]);
    let c5 = seq![lir::Val::I32(f), lir::Val::I32(zz)];
    assert(seq![lir::Val::I32(f)].push(lir::Val::I32(zz)) =~= c5);
    assert(lir::below(c5, 2) =~= Seq::<lir::Val>::empty());
    assert(Seq::<lir::Val>::empty().push(lir::Val::I32(lir::ibin32(lir::IBin::And, f, zz)))
        =~= seq![lir::Val::I32(lir::ibin32(lir::IBin::And, f, zz))]);
}

/// The second guard pushes whether the result is an int32 the semantics
/// encodes as one.
pub proof fn lemma_guard2_trace(lay: lir::Layout, st: lir::St, k: nat, va: u64, vb: u64)
    requires
        k <= 2,
        st.stack == Seq::<lir::Val>::empty(),
        st.locals.len() == nlocals(),
        st.locals[1] == lir::Val::I64(va),
        st.locals[2] == lir::Val::I64(vb),
        st.locals[3] == lir::Val::I64(super::arith::s64(k, va, vb)),
    ensures
        super::run::exec(lay, super::lower::guard2_ins(k), st) == lir::Outcome::Normal(
            st.with_stack(seq![lir::Val::I32(super::arith::guard2(k, va, vb))]),
        ),
{
    let s = super::arith::s64(k, va, vb);
    lemma_fits_trace(lay, st, s);
    let f = super::arith::fits_flag(s);
    let sf = st.with_stack(st.stack.push(lir::Val::I32(f)));
    assert(st.stack.push(lir::Val::I32(f)) =~= seq![lir::Val::I32(f)]);
    if k != 2 {
    } else {
        lemma_exec_app(lay, super::lower::fits_ins(), super::lower::mul_tail_ins(), st, sf);
        let ta = seq![lir::Instr::LocalGet(3), lir::Instr::Un(lir::UnOp::I64Eqz)]
            + super::lower::sext_local(1) + super::lower::sext_local(2);
        let tb = seq![
            lir::Instr::Bin(lir::BinOp::I64(lir::IBin::Or)),
            super::lower::i64c(0),
            super::lower::cmp64(lir::ICmp::LtS),
        ] + seq![
            lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
            lir::Instr::Un(lir::UnOp::I32Eqz),
            lir::Instr::Bin(lir::BinOp::I32(lir::IBin::And)),
        ];
        assert(super::lower::mul_tail_ins() =~= ta + tb);
        lemma_mul_tail_a(lay, sf, va, vb, s, f);
        let z0 = lir::bool_i32(s == 0);
        let xa = super::arith::sext(super::arith::lo32(va));
        let xb = super::arith::sext(super::arith::lo32(vb));
        let sg = sf.with_stack(
            seq![lir::Val::I32(f), lir::Val::I32(z0), lir::Val::I64(xa), lir::Val::I64(xb)],
        );
        lemma_exec_app(lay, ta, tb, sf, sg);
        lemma_mul_tail_b(lay, sg, f, z0, xa, xb);
        assert(super::arith::zneg_flag(va, vb, s) == lir::ibin32(
            lir::IBin::And,
            z0,
            lir::bool_i32(lir::signed_of(64, (xa | xb) as int) < lir::signed_of(64, 0)),
        ));
    }
}

} // verus!
