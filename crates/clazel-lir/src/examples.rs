//! Small LIR programs with proven properties: evidence that the typing
//! accepts what a front end would write, rejects what it must, and that the
//! soundness theorem applies to concrete code.
//!
//! - `load_at`: the bounds-checked load every JS property access lowers
//!   to. It type-checks; the typing rejects the same code with the
//!   `bounds_check` removed or with dead code after a branch; and by
//!   `tc_sound` it is never stuck, whatever the index (the bounds failure
//!   is an `exit`, `example_load_at_exits`).
//! - `countdown`: a loop with a `br_if` back edge, typed, and by
//!   `tc_sound` never stuck for any fuel.
//! - `store_then_load`: memory through a region.

#[allow(unused_imports)]
use super::spec::*;
pub use super::typing::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `a; b`.
pub open spec fn then(a: Instr, b: Instr) -> Instr {
    Instr::Then(Box::new(a), Box::new(b))
}

/// One region of 64 bytes at `0x1000`.
pub open spec fn lay1() -> Layout {
    seq![Region { base: 0x1000, bound: 64 }]
}

/// Local 0 is an `i64` index. Check it against region 0 for 8 bytes (exit
/// with code 7 if it does not fit), then load the `i64` there.
pub open spec fn load_at() -> Instr {
    then(
        Instr::LocalGet(0),
        then(
            Instr::BoundsCheck { region: 0, size: 8, code: 7 },
            Instr::Load { region: 0, ty: Ty::I64 },
        ),
    )
}

/// The context of `load_at`: one `i64` local, and the function's return
/// label taking an `i64`.
pub open spec fn ctx_load() -> Ctx {
    Ctx { locals: seq![Ty::I64], labels: seq![seq![Ty::I64]] }
}

/// `load_at` type-checks, leaving an `i64`.
pub proof fn example_load_at_types()
    ensures
        tc(lay1(), ctx_load(), load_at(), seq![]) == Some(Flow::Falls(seq![Ty::I64])),
{
    let l = lay1();
    let c = ctx_load();
    let bc = Instr::BoundsCheck { region: 0, size: 8, code: 7 };
    let ld = Instr::Load { region: 0, ty: Ty::I64 };
    assert(Seq::<Ty>::empty().push(Ty::I64) =~= seq![Ty::I64]);
    assert(below(seq![Ty::I64], 1).push(Ty::Idx(0, 8)) =~= seq![Ty::Idx(0, 8)]);
    assert(below(seq![Ty::Idx(0, 8)], 1).push(Ty::I64) =~= seq![Ty::I64]);
    assert(tc(l, c, Instr::LocalGet(0), seq![]) == Some(Flow::Falls(seq![Ty::I64])));
    assert(tc(l, c, bc, seq![Ty::I64]) == Some(Flow::Falls(seq![Ty::Idx(0, 8)])));
    assert(tc(l, c, ld, seq![Ty::Idx(0, 8)]) == Some(Flow::Falls(seq![Ty::I64])));
    assert(tc(l, c, then(bc, ld), seq![Ty::I64]) == Some(Flow::Falls(seq![Ty::I64])));
    assert(tc(l, c, load_at(), seq![]) == Some(Flow::Falls(seq![Ty::I64])));
}

/// The same code without the `bounds_check` does not type: the index is an
/// `i64`, not an `Idx`.
pub proof fn example_unchecked_load_rejected()
    ensures
        tc(
            lay1(),
            ctx_load(),
            then(Instr::LocalGet(0), Instr::Load { region: 0, ty: Ty::I64 }),
            seq![],
        ) is None,
{
    reveal_with_fuel(tc, 12);
    reveal_with_fuel(tc_blk, 3);
    assert(tc(
        lay1(),
        ctx_load(),
        then(Instr::LocalGet(0), Instr::Load { region: 0, ty: Ty::I64 }),
        seq![],
    ) is None);
}

/// A check for 4 bytes does not license an 8-byte load.
pub proof fn example_short_check_rejected()
    ensures
        tc(
            lay1(),
            ctx_load(),
            then(
                Instr::LocalGet(0),
                then(
                    Instr::BoundsCheck { region: 0, size: 4, code: 7 },
                    Instr::Load { region: 0, ty: Ty::I64 },
                ),
            ),
            seq![],
        ) is None,
{
    reveal_with_fuel(tc, 12);
    reveal_with_fuel(tc_blk, 3);
    assert(tc(
        lay1(),
        ctx_load(),
        then(
            Instr::LocalGet(0),
            then(
                Instr::BoundsCheck { region: 0, size: 4, code: 7 },
                Instr::Load { region: 0, ty: Ty::I64 },
            ),
        ),
        seq![],
    ) is None);
}

/// Dead code after `br` does not type (difference 1 of the typing).
pub proof fn example_dead_code_rejected()
    ensures
        tc(lay1(), ctx_load(), then(Instr::Br(0), Instr::Nop), seq![Ty::I64]) is None,
{
    reveal_with_fuel(tc, 12);
    reveal_with_fuel(tc_blk, 3);
    assert(tc(lay1(), ctx_load(), then(Instr::Br(0), Instr::Nop), seq![Ty::I64]) is None);
}

/// For any state with an `i64` local and an empty stack, in any amount of
/// fuel, `load_at` is not stuck: it reads inside region 0, or exits.
pub proof fn example_load_at_never_stuck(st: St, fuel: nat)
    requires
        st.stack == Seq::<Val>::empty(),
        st.locals.len() == 1,
        st.locals[0] is I64,
    ensures
        !(eval(lay1(), load_at(), st, fuel) is Stuck),
{
    example_load_at_types();
    assert(vals_conform(lay1(), st.stack, seq![]));
    assert(vals_conform(lay1(), st.locals, ctx_load().locals));
    crate::soundness::tc_sound(lay1(), ctx_load(), load_at(), seq![], st, fuel, Flow::Falls(seq![Ty::I64]));
}

/// An index past the end of the region exits with the check's code.
pub proof fn example_load_at_exits()
    ensures
        ({
            let st = St { stack: seq![], locals: seq![Val::I64(60)], mem: Map::empty() };
            match eval(lay1(), load_at(), st, 10) {
                Outcome::Exit(code, ops, _) => code == 7 && ops.len() == 0,
                _ => false,
            }
        }),
{
    reveal_with_fuel(eval, 6);
}

/// A countdown loop on local 0 (an `i32`): subtract 1, keep it, and branch
/// back to the start while it is non-zero.
pub open spec fn countdown() -> Instr {
    Instr::Loop(
        BlockType { params: seq![], results: seq![] },
        Box::new(
            then(
                Instr::LocalGet(0),
                then(
                    Instr::Const(Val::I32(1)),
                    then(
                        Instr::Bin(BinOp::I32(IBin::Sub)),
                        then(Instr::LocalTee(0), Instr::BrIf(0)),
                    ),
                ),
            ),
        ),
    )
}

/// The context of `countdown`.
pub open spec fn ctx_count() -> Ctx {
    Ctx { locals: seq![Ty::I32], labels: seq![seq![]] }
}

/// `countdown` type-checks and leaves nothing.
pub proof fn example_countdown_types()
    ensures
        tc(lay1(), ctx_count(), countdown(), seq![]) == Some(Flow::Falls(seq![])),
{
    reveal_with_fuel(tc, 12);
    reveal_with_fuel(tc_blk, 3);
    assert(tc(lay1(), ctx_count(), countdown(), seq![]) == Some(Flow::Falls(seq![])));
}

/// For any state with an `i32` local and an empty stack, in any amount of
/// fuel, `countdown` is not stuck. (It does not run for ever when it has
/// enough fuel, but that is a fact about the semantics, not the typing.)
pub proof fn example_countdown_never_stuck(st: St, fuel: nat)
    requires
        st.stack == Seq::<Val>::empty(),
        st.locals.len() == 1,
        st.locals[0] is I32,
    ensures
        !(eval(lay1(), countdown(), st, fuel) is Stuck),
{
    example_countdown_types();
    assert(vals_conform(lay1(), st.stack, seq![]));
    assert(vals_conform(lay1(), st.locals, ctx_count().locals));
    crate::soundness::tc_sound(lay1(), ctx_count(), countdown(), seq![], st, fuel, Flow::Falls(seq![]));
}

/// Store the `i32` `0x11223344` at index 4 of region 0, then load it back.
pub open spec fn store_then_load() -> Instr {
    then(
        then(
            Instr::Const(Val::I64(4)),
            then(
                Instr::BoundsCheck { region: 0, size: 4, code: 1 },
                then(
                    Instr::Const(Val::I32(0x1122_3344)),
                    Instr::Store { region: 0, ty: Ty::I32 },
                ),
            ),
        ),
        then(
            Instr::Const(Val::I64(4)),
            then(
                Instr::BoundsCheck { region: 0, size: 4, code: 1 },
                Instr::Load { region: 0, ty: Ty::I32 },
            ),
        ),
    )
}

/// It types, leaving an `i32`.
pub proof fn example_store_then_load_types()
    ensures
        tc(
            lay1(),
            Ctx { locals: seq![], labels: seq![] },
            store_then_load(),
            seq![],
        ) == Some(Flow::Falls(seq![Ty::I32])),
{
    let l = lay1();
    let c = Ctx { locals: seq![], labels: seq![] };
    let bc = Instr::BoundsCheck { region: 0, size: 4, code: 1 };
    let s0 = Seq::<Ty>::empty();
    let s1 = seq![Ty::I64];
    let s2 = seq![Ty::Idx(0, 4)];
    let s3 = seq![Ty::Idx(0, 4), Ty::I32];
    let s4 = seq![Ty::I32];
    assert(s0.push(Ty::I64) =~= s1);
    assert(below(s1, 1).push(Ty::Idx(0, 4)) =~= s2);
    assert(s2.push(Ty::I32) =~= s3);
    assert(below(s3, 2) =~= s0);
    assert(below(s2, 1).push(Ty::I32) =~= s4);
    let sto = Instr::Store { region: 0, ty: Ty::I32 };
    let ld = Instr::Load { region: 0, ty: Ty::I32 };
    let c4 = Instr::Const(Val::I32(0x1122_3344));
    let c64 = Instr::Const(Val::I64(4));
    assert(tc(l, c, c64, s0) == Some(Flow::Falls(s1)));
    assert(tc(l, c, bc, s1) == Some(Flow::Falls(s2)));
    assert(tc(l, c, c4, s2) == Some(Flow::Falls(s3)));
    assert(tc(l, c, sto, s3) == Some(Flow::Falls(s0)));
    assert(tc(l, c, ld, s2) == Some(Flow::Falls(s4)));
    assert(tc(l, c, then(c4, sto), s2) == Some(Flow::Falls(s0)));
    assert(tc(l, c, then(bc, then(c4, sto)), s1) == Some(Flow::Falls(s0)));
    assert(tc(l, c, then(c64, then(bc, then(c4, sto))), s0) == Some(Flow::Falls(s0)));
    assert(tc(l, c, then(bc, ld), s1) == Some(Flow::Falls(s4)));
    assert(tc(l, c, then(c64, then(bc, ld)), s0) == Some(Flow::Falls(s4)));
    assert(tc(l, c, store_then_load(), s0) == Some(Flow::Falls(s4)));
}

/// Run from empty memory, `store_then_load` gives back the stored `i32`.
/// (Region 0 is at `0x1000` and the index is 4, so bytes `0x1004..0x1008`
/// are written, little-endian, and read.)
pub proof fn example_store_then_load_runs()
    ensures
        ({
            let st = St { stack: seq![], locals: seq![], mem: Map::empty() };
            match eval(lay1(), store_then_load(), st, 40) {
                Outcome::Normal(s) => s.stack == seq![Val::I32(0x1122_3344)],
                _ => false,
            }
        }),
{
    reveal_with_fuel(eval, 12);
    reveal_with_fuel(read_le, 5);
    reveal_with_fuel(write_le, 5);
}

} // verus!
