//! The standard's results, evaluated on the spec with `compute_only`. Kept
//! apart from [`super::lemmas`] so that a mutant that breaks one of them does
//! not stop Verus before it checks a kill certificate there
//! (`mutations.json`).
//!
//! - [`example_multiply_zero_signs`]: the sign of a zero product (steps 4
//!   and 5 and the step 5a erratum of Number::multiply).
//! - [`example_new_ops_wf`], [`example_new_ops_classes`] and
//!   [`example_to_number`]: the ops added for the compiler's needs
//!   (`DefineProp`, `DefineElem`, `SetLiteralProto`, `GetGlobalOrUndefined`,
//!   `DeclareGlobals`, `ToNumber`): which operands `op_wf` accepts, each op's
//!   class and handler, and `ToNumber`'s fast path and result.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sign of a zero product, §6.1.6.1.4: `-0 × 5` is `-0` (step 4.b),
/// `5 × -0` is `-0` (step 5.b), `-0 × -5` is `+0` (step 4.a), and `+0 × -5`
/// is `-0` (the step 5a erratum, docs/ERRATA.md).
pub proof fn example_multiply_zero_signs()
    ensures
        number_multiply(0x8000_0000_0000_0000u64, 0x4014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
        number_multiply(0x4014_0000_0000_0000u64, 0x8000_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
        number_multiply(0x8000_0000_0000_0000u64, 0xC014_0000_0000_0000u64) == 0u64,
        number_multiply(0u64, 0xC014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
{
    assert(number_multiply(0x8000_0000_0000_0000u64, 0x4014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
    assert(number_multiply(0x4014_0000_0000_0000u64, 0x8000_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
    assert(number_multiply(0x8000_0000_0000_0000u64, 0xC014_0000_0000_0000u64) == 0u64) by (compute_only);
    assert(number_multiply(0u64, 0xC014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
}

/// A code with three registers (one parameter, two locals), three constants
/// (two `undefined` and a bit pattern that is not a value), one cache and no
/// ops, which is all `op_wf` reads of the ops it checks.
pub open spec fn example_code() -> Code {
    Code {
        ops: Seq::empty(),
        consts: seq![UNDEFINED, UNDEFINED, 0xFFFD_0000_0000_0000u64],
        nparams: 1,
        nregs: 2,
        nics: 1,
    }
}

/// A machine whose frame is at slot 0, with `v` in register 0 (slot 4, after
/// the four header slots) and `undefined` elsewhere, an empty heap and no
/// code: all that `fast_path` and `fast_step` read of a `ToNumber`.
pub open spec fn example_state(v: u64) -> State {
    State {
        region: seq![UNDEFINED, UNDEFINED, UNDEFINED, UNDEFINED, v, UNDEFINED, UNDEFINED],
        fp: 0,
        pc: 0,
        heap: Heap { cells: Map::empty() },
        codes: Seq::empty(),
        ics: Seq::empty(),
        exception: UNDEFINED,
        terminate: false,
    }
}

/// The operands `op_wf` accepts of the ops added for the compiler: every
/// register inside the frame (registers 0 to 2), every constant index inside
/// the pool (0 to 2), and a `DeclareGlobals` constant that is a value
/// (constant 2 is not).
pub proof fn example_new_ops_wf()
    ensures
        op_wf(example_code(), Op::DefineProp { obj: 0, key: 2, val: 2 }),
        !op_wf(example_code(), Op::DefineProp { obj: 3, key: 2, val: 2 }),
        !op_wf(example_code(), Op::DefineProp { obj: 0, key: 3, val: 2 }),
        !op_wf(example_code(), Op::DefineProp { obj: 0, key: 2, val: 3 }),
        op_wf(example_code(), Op::DefineElem { obj: 0, idx: 1, val: 2 }),
        !op_wf(example_code(), Op::DefineElem { obj: 3, idx: 1, val: 2 }),
        !op_wf(example_code(), Op::DefineElem { obj: 0, idx: 3, val: 2 }),
        !op_wf(example_code(), Op::DefineElem { obj: 0, idx: 1, val: 3 }),
        op_wf(example_code(), Op::SetLiteralProto { obj: 0, val: 2 }),
        !op_wf(example_code(), Op::SetLiteralProto { obj: 3, val: 2 }),
        !op_wf(example_code(), Op::SetLiteralProto { obj: 0, val: 3 }),
        op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 2, key: 2 }),
        !op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 3, key: 2 }),
        !op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 2, key: 3 }),
        op_wf(example_code(), Op::DeclareGlobals { k: 0 }),
        !op_wf(example_code(), Op::DeclareGlobals { k: 2 }),
        op_wf(example_code(), Op::ToNumber { dst: 2, src: 0 }),
        !op_wf(example_code(), Op::ToNumber { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::ToNumber { dst: 2, src: 3 }),
{
    assert(op_wf(example_code(), Op::DefineProp { obj: 0, key: 2, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineProp { obj: 3, key: 2, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineProp { obj: 0, key: 3, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineProp { obj: 0, key: 2, val: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DefineElem { obj: 0, idx: 1, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineElem { obj: 3, idx: 1, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineElem { obj: 0, idx: 3, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineElem { obj: 0, idx: 1, val: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SetLiteralProto { obj: 0, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetLiteralProto { obj: 3, val: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetLiteralProto { obj: 0, val: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 2, key: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 3, key: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetGlobalOrUndefined { dst: 2, key: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DeclareGlobals { k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DeclareGlobals { k: 2 })) by (compute_only);
    assert(op_wf(example_code(), Op::ToNumber { dst: 2, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToNumber { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToNumber { dst: 2, src: 3 })) by (compute_only);
}

/// The class and the handler of each op added for the compiler: the five
/// that always call out are handler ops (so the JIT lowers each to an exit),
/// and `ToNumber` is guarded, like `ToNumeric`, with its own handler.
pub proof fn example_new_ops_classes()
    ensures
        op_class(Op::DefineProp { obj: 0, key: 0, val: 0 }) is Handler,
        op_class(Op::DefineElem { obj: 0, idx: 0, val: 0 }) is Handler,
        op_class(Op::SetLiteralProto { obj: 0, val: 0 }) is Handler,
        op_class(Op::GetGlobalOrUndefined { dst: 0, key: 0 }) is Handler,
        op_class(Op::DeclareGlobals { k: 0 }) is Handler,
        op_class(Op::ToNumber { dst: 0, src: 0 }) is Guarded,
        op_handler(Op::DefineProp { obj: 0, key: 0, val: 0 }) == HandlerId::DefineProp,
        op_handler(Op::DefineElem { obj: 0, idx: 0, val: 0 }) == HandlerId::DefineElem,
        op_handler(Op::SetLiteralProto { obj: 0, val: 0 }) == HandlerId::SetLiteralProto,
        op_handler(Op::GetGlobalOrUndefined { dst: 0, key: 0 }) == HandlerId::GetGlobalOrUndefined,
        op_handler(Op::DeclareGlobals { k: 0 }) == HandlerId::DeclareGlobals,
        op_handler(Op::ToNumber { dst: 0, src: 0 }) == HandlerId::ToNumber,
{
    assert(op_class(Op::DefineProp { obj: 0, key: 0, val: 0 }) is Handler) by (compute_only);
    assert(op_class(Op::DefineElem { obj: 0, idx: 0, val: 0 }) is Handler) by (compute_only);
    assert(op_class(Op::SetLiteralProto { obj: 0, val: 0 }) is Handler) by (compute_only);
    assert(op_class(Op::GetGlobalOrUndefined { dst: 0, key: 0 }) is Handler) by (compute_only);
    assert(op_class(Op::DeclareGlobals { k: 0 }) is Handler) by (compute_only);
    assert(op_class(Op::ToNumber { dst: 0, src: 0 }) is Guarded) by (compute_only);
    assert(op_handler(Op::DefineProp { obj: 0, key: 0, val: 0 }) == HandlerId::DefineProp) by (compute_only);
    assert(op_handler(Op::DefineElem { obj: 0, idx: 0, val: 0 }) == HandlerId::DefineElem) by (compute_only);
    assert(op_handler(Op::SetLiteralProto { obj: 0, val: 0 }) == HandlerId::SetLiteralProto) by (compute_only);
    assert(op_handler(Op::GetGlobalOrUndefined { dst: 0, key: 0 }) == HandlerId::GetGlobalOrUndefined) by (compute_only);
    assert(op_handler(Op::DeclareGlobals { k: 0 }) == HandlerId::DeclareGlobals) by (compute_only);
    assert(op_handler(Op::ToNumber { dst: 0, src: 0 }) == HandlerId::ToNumber) by (compute_only);
}

/// `ToNumber` (§7.1.4† step 1): on a Number the fast path holds and the
/// result is the operand, in the next op; on `undefined` (which ToNumber
/// turns into `NaN`, step 4, in the handler) it does not hold.
pub proof fn example_to_number()
    ensures
        fast_path(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 }),
        fast_step(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 }).region[5]
            == 0xFFF9_0000_0000_0005u64,
        fast_step(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 }).pc == 1nat,
        !fast_path(example_state(UNDEFINED), Op::ToNumber { dst: 1, src: 0 }),
{
    assert(fast_path(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 })) by (compute_only);
    assert(fast_step(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 }).region[5]
        == 0xFFF9_0000_0000_0005u64) by (compute_only);
    assert(fast_step(example_state(0xFFF9_0000_0000_0005u64), Op::ToNumber { dst: 1, src: 0 }).pc == 1nat) by (compute_only);
    assert(!fast_path(example_state(UNDEFINED), Op::ToNumber { dst: 1, src: 0 })) by (compute_only);
}

} // verus!
