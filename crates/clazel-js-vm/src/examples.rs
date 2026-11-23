//! The standard's results, evaluated on the spec with `compute_only`. Kept
//! apart from [`super::lemmas`] so that a mutant that breaks one of them does
//! not stop Verus before it checks a kill certificate there
//! (`mutations.json`).
//!
//! - [`example_multiply_zero_signs`]: the sign of a zero product (steps 4
//!   and 5 and the step 5a erratum of Number::multiply).
//! - [`example_compiler_ops_wf`] and [`example_compiler_ops_classes`]: the ops added
//!   for the compiler's second slice (destructuring, spread, templates, classes,
//!   `for`-`in`, the `arguments` object): which operands `op_wf` accepts, and each
//!   op's class and handler.
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

/// The operands `op_wf` accepts of the ops added for the compiler's second
/// slice (`ToPropertyKey`, `ToString`, `CopyDataProperties`, `GetTemplateObject`, `NewSpread`, `SuperCall`, `SuperCallSpread`, `InitInstance`, `ClassSetup`, `DefineMethod`, `SetHomeObject`, `SetInstanceInit`, `NewPrivateName`, `GetPrivate`, `SetPrivate`, `DefinePrivate`, `HasPrivate`, `GetSuperBase`, `GetSuper`, `SetSuper`, `GetNewTarget`, `ConstructResult`, `CreateUnmappedArguments`, `CreateMappedArguments`, `CreateRestArray`, `ForInIterator`):
/// every register inside the frame (registers 0 to 2), every register range
/// inside it, every constant index inside the pool (0 to 2), a record constant
/// that is a value (constant 2 is not), and each small enumerated operand below
/// its bound.
pub proof fn example_compiler_ops_wf()
    ensures
        op_wf(example_code(), Op::ToPropertyKey { dst: 0, src: 0 }),
        !op_wf(example_code(), Op::ToPropertyKey { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::ToPropertyKey { dst: 0, src: 3 }),
        op_wf(example_code(), Op::ToString { dst: 0, src: 0 }),
        !op_wf(example_code(), Op::ToString { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::ToString { dst: 0, src: 3 }),
        op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 }),
        !op_wf(example_code(), Op::CopyDataProperties { obj: 3, src: 0, excl: 0, nexcl: 3 }),
        !op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 3, excl: 0, nexcl: 3 }),
        !op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 0, excl: 1, nexcl: 3 }),
        op_wf(example_code(), Op::GetTemplateObject { dst: 0, k: 0 }),
        !op_wf(example_code(), Op::GetTemplateObject { dst: 3, k: 0 }),
        !op_wf(example_code(), Op::GetTemplateObject { dst: 0, k: 2 }),
        op_wf(example_code(), Op::NewSpread { dst: 0, callee: 0, args: 0 }),
        !op_wf(example_code(), Op::NewSpread { dst: 3, callee: 0, args: 0 }),
        !op_wf(example_code(), Op::NewSpread { dst: 0, callee: 3, args: 0 }),
        !op_wf(example_code(), Op::NewSpread { dst: 0, callee: 0, args: 3 }),
        op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }),
        !op_wf(example_code(), Op::SuperCall { dst: 3, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }),
        !op_wf(example_code(), Op::SuperCall { dst: 0, func: 3, newtarget: 0, this: 0, args: 0, argc: 3 }),
        !op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 3, this: 0, args: 0, argc: 3 }),
        !op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 3, args: 0, argc: 3 }),
        !op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 1, argc: 3 }),
        op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 }),
        !op_wf(example_code(), Op::SuperCallSpread { dst: 3, func: 0, newtarget: 0, this: 0, args: 0 }),
        !op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 3, newtarget: 0, this: 0, args: 0 }),
        !op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 3, this: 0, args: 0 }),
        !op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 3, args: 0 }),
        !op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 3 }),
        op_wf(example_code(), Op::InitInstance { obj: 0, func: 0 }),
        !op_wf(example_code(), Op::InitInstance { obj: 3, func: 0 }),
        !op_wf(example_code(), Op::InitInstance { obj: 0, func: 3 }),
        op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true }),
        !op_wf(example_code(), Op::ClassSetup { ctor: 3, proto: 0, heritage: 0, derived: true }),
        !op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 3, heritage: 0, derived: true }),
        !op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 0, heritage: 3, derived: true }),
        op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true }),
        !op_wf(example_code(), Op::DefineMethod { obj: 3, key: 0, func: 0, form: 2, enumerable: true }),
        !op_wf(example_code(), Op::DefineMethod { obj: 0, key: 3, func: 0, form: 2, enumerable: true }),
        !op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 3, form: 2, enumerable: true }),
        !op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 0, form: 3, enumerable: true }),
        op_wf(example_code(), Op::SetHomeObject { func: 0, obj: 0 }),
        !op_wf(example_code(), Op::SetHomeObject { func: 3, obj: 0 }),
        !op_wf(example_code(), Op::SetHomeObject { func: 0, obj: 3 }),
        op_wf(example_code(), Op::SetInstanceInit { ctor: 0, init: 0 }),
        !op_wf(example_code(), Op::SetInstanceInit { ctor: 3, init: 0 }),
        !op_wf(example_code(), Op::SetInstanceInit { ctor: 0, init: 3 }),
        op_wf(example_code(), Op::NewPrivateName { dst: 0, k: 2 }),
        !op_wf(example_code(), Op::NewPrivateName { dst: 3, k: 2 }),
        !op_wf(example_code(), Op::NewPrivateName { dst: 0, k: 3 }),
        op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 0, name: 0 }),
        !op_wf(example_code(), Op::GetPrivate { dst: 3, obj: 0, name: 0 }),
        !op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 3, name: 0 }),
        !op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 0, name: 3 }),
        op_wf(example_code(), Op::SetPrivate { obj: 0, name: 0, val: 0 }),
        !op_wf(example_code(), Op::SetPrivate { obj: 3, name: 0, val: 0 }),
        !op_wf(example_code(), Op::SetPrivate { obj: 0, name: 3, val: 0 }),
        !op_wf(example_code(), Op::SetPrivate { obj: 0, name: 0, val: 3 }),
        op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 }),
        !op_wf(example_code(), Op::DefinePrivate { obj: 3, name: 0, val: 0, form: 3 }),
        !op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 3, val: 0, form: 3 }),
        !op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 3, form: 3 }),
        !op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 4 }),
        op_wf(example_code(), Op::HasPrivate { dst: 0, name: 0, obj: 0 }),
        !op_wf(example_code(), Op::HasPrivate { dst: 3, name: 0, obj: 0 }),
        !op_wf(example_code(), Op::HasPrivate { dst: 0, name: 3, obj: 0 }),
        !op_wf(example_code(), Op::HasPrivate { dst: 0, name: 0, obj: 3 }),
        op_wf(example_code(), Op::GetSuperBase { dst: 0, func: 0 }),
        !op_wf(example_code(), Op::GetSuperBase { dst: 3, func: 0 }),
        !op_wf(example_code(), Op::GetSuperBase { dst: 0, func: 3 }),
        op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 }),
        !op_wf(example_code(), Op::GetSuper { dst: 3, base: 0, key: 0, this: 0 }),
        !op_wf(example_code(), Op::GetSuper { dst: 0, base: 3, key: 0, this: 0 }),
        !op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 3, this: 0 }),
        !op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 0, this: 3 }),
        op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 0, this: 0 }),
        !op_wf(example_code(), Op::SetSuper { base: 3, key: 0, val: 0, this: 0 }),
        !op_wf(example_code(), Op::SetSuper { base: 0, key: 3, val: 0, this: 0 }),
        !op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 3, this: 0 }),
        !op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 0, this: 3 }),
        op_wf(example_code(), Op::GetNewTarget { dst: 0 }),
        !op_wf(example_code(), Op::GetNewTarget { dst: 3 }),
        op_wf(example_code(), Op::ConstructResult { dst: 0, val: 0, this: 0 }),
        !op_wf(example_code(), Op::ConstructResult { dst: 3, val: 0, this: 0 }),
        !op_wf(example_code(), Op::ConstructResult { dst: 0, val: 3, this: 0 }),
        !op_wf(example_code(), Op::ConstructResult { dst: 0, val: 0, this: 3 }),
        op_wf(example_code(), Op::CreateUnmappedArguments { dst: 0 }),
        !op_wf(example_code(), Op::CreateUnmappedArguments { dst: 3 }),
        op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 0, k: 0 }),
        !op_wf(example_code(), Op::CreateMappedArguments { dst: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 3, k: 0 }),
        !op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 0, k: 2 }),
        op_wf(example_code(), Op::CreateRestArray { dst: 0, from: 0 }),
        !op_wf(example_code(), Op::CreateRestArray { dst: 3, from: 0 }),
        op_wf(example_code(), Op::ForInIterator { dst: 0, src: 0 }),
        !op_wf(example_code(), Op::ForInIterator { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::ForInIterator { dst: 0, src: 3 }),
{
    assert(op_wf(example_code(), Op::ToPropertyKey { dst: 0, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToPropertyKey { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToPropertyKey { dst: 0, src: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::ToString { dst: 0, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToString { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToString { dst: 0, src: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CopyDataProperties { obj: 3, src: 0, excl: 0, nexcl: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 3, excl: 0, nexcl: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CopyDataProperties { obj: 0, src: 0, excl: 1, nexcl: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetTemplateObject { dst: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetTemplateObject { dst: 3, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetTemplateObject { dst: 0, k: 2 })) by (compute_only);
    assert(op_wf(example_code(), Op::NewSpread { dst: 0, callee: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewSpread { dst: 3, callee: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewSpread { dst: 0, callee: 3, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewSpread { dst: 0, callee: 0, args: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCall { dst: 3, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCall { dst: 0, func: 3, newtarget: 0, this: 0, args: 0, argc: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 3, this: 0, args: 0, argc: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 3, args: 0, argc: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 1, argc: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCallSpread { dst: 3, func: 0, newtarget: 0, this: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 3, newtarget: 0, this: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 3, this: 0, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 3, args: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::InitInstance { obj: 0, func: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::InitInstance { obj: 3, func: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::InitInstance { obj: 0, func: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::ClassSetup { ctor: 3, proto: 0, heritage: 0, derived: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 3, heritage: 0, derived: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::ClassSetup { ctor: 0, proto: 0, heritage: 3, derived: true })) by (compute_only);
    assert(op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineMethod { obj: 3, key: 0, func: 0, form: 2, enumerable: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineMethod { obj: 0, key: 3, func: 0, form: 2, enumerable: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 3, form: 2, enumerable: true })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefineMethod { obj: 0, key: 0, func: 0, form: 3, enumerable: true })) by (compute_only);
    assert(op_wf(example_code(), Op::SetHomeObject { func: 0, obj: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetHomeObject { func: 3, obj: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetHomeObject { func: 0, obj: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SetInstanceInit { ctor: 0, init: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetInstanceInit { ctor: 3, init: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetInstanceInit { ctor: 0, init: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::NewPrivateName { dst: 0, k: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewPrivateName { dst: 3, k: 2 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewPrivateName { dst: 0, k: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 0, name: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetPrivate { dst: 3, obj: 0, name: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 3, name: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetPrivate { dst: 0, obj: 0, name: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SetPrivate { obj: 0, name: 0, val: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetPrivate { obj: 3, name: 0, val: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetPrivate { obj: 0, name: 3, val: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetPrivate { obj: 0, name: 0, val: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefinePrivate { obj: 3, name: 0, val: 0, form: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 3, val: 0, form: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 3, form: 3 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 4 })) by (compute_only);
    assert(op_wf(example_code(), Op::HasPrivate { dst: 0, name: 0, obj: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::HasPrivate { dst: 3, name: 0, obj: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::HasPrivate { dst: 0, name: 3, obj: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::HasPrivate { dst: 0, name: 0, obj: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetSuperBase { dst: 0, func: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuperBase { dst: 3, func: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuperBase { dst: 0, func: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuper { dst: 3, base: 0, key: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuper { dst: 0, base: 3, key: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 3, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetSuper { dst: 0, base: 0, key: 0, this: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetSuper { base: 3, key: 0, val: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetSuper { base: 0, key: 3, val: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 3, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::SetSuper { base: 0, key: 0, val: 0, this: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetNewTarget { dst: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetNewTarget { dst: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::ConstructResult { dst: 0, val: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ConstructResult { dst: 3, val: 0, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ConstructResult { dst: 0, val: 3, this: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ConstructResult { dst: 0, val: 0, this: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::CreateUnmappedArguments { dst: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CreateUnmappedArguments { dst: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CreateMappedArguments { dst: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 3, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CreateMappedArguments { dst: 0, env: 0, k: 2 })) by (compute_only);
    assert(op_wf(example_code(), Op::CreateRestArray { dst: 0, from: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::CreateRestArray { dst: 3, from: 0 })) by (compute_only);
    assert(op_wf(example_code(), Op::ForInIterator { dst: 0, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ForInIterator { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ForInIterator { dst: 0, src: 3 })) by (compute_only);
}

/// The class and the handler of each op added for the compiler's second
/// slice: each always calls out (it can allocate, call user code or throw), so
/// each is a handler op, which the JIT lowers to an exit, with its own handler.
pub proof fn example_compiler_ops_classes()
    ensures
        op_class(Op::ToPropertyKey { dst: 0, src: 0 }) is Handler,
        op_handler(Op::ToPropertyKey { dst: 0, src: 0 }) == HandlerId::ToPropertyKey,
        op_class(Op::ToString { dst: 0, src: 0 }) is Handler,
        op_handler(Op::ToString { dst: 0, src: 0 }) == HandlerId::ToString,
        op_class(Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 }) is Handler,
        op_handler(Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 }) == HandlerId::CopyDataProperties,
        op_class(Op::GetTemplateObject { dst: 0, k: 0 }) is Handler,
        op_handler(Op::GetTemplateObject { dst: 0, k: 0 }) == HandlerId::GetTemplateObject,
        op_class(Op::NewSpread { dst: 0, callee: 0, args: 0 }) is Handler,
        op_handler(Op::NewSpread { dst: 0, callee: 0, args: 0 }) == HandlerId::NewSpread,
        op_class(Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }) is Handler,
        op_handler(Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }) == HandlerId::SuperCall,
        op_class(Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 }) is Handler,
        op_handler(Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 }) == HandlerId::SuperCallSpread,
        op_class(Op::InitInstance { obj: 0, func: 0 }) is Handler,
        op_handler(Op::InitInstance { obj: 0, func: 0 }) == HandlerId::InitInstance,
        op_class(Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true }) is Handler,
        op_handler(Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true }) == HandlerId::ClassSetup,
        op_class(Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true }) is Handler,
        op_handler(Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true }) == HandlerId::DefineMethod,
        op_class(Op::SetHomeObject { func: 0, obj: 0 }) is Handler,
        op_handler(Op::SetHomeObject { func: 0, obj: 0 }) == HandlerId::SetHomeObject,
        op_class(Op::SetInstanceInit { ctor: 0, init: 0 }) is Handler,
        op_handler(Op::SetInstanceInit { ctor: 0, init: 0 }) == HandlerId::SetInstanceInit,
        op_class(Op::NewPrivateName { dst: 0, k: 2 }) is Handler,
        op_handler(Op::NewPrivateName { dst: 0, k: 2 }) == HandlerId::NewPrivateName,
        op_class(Op::GetPrivate { dst: 0, obj: 0, name: 0 }) is Handler,
        op_handler(Op::GetPrivate { dst: 0, obj: 0, name: 0 }) == HandlerId::GetPrivate,
        op_class(Op::SetPrivate { obj: 0, name: 0, val: 0 }) is Handler,
        op_handler(Op::SetPrivate { obj: 0, name: 0, val: 0 }) == HandlerId::SetPrivate,
        op_class(Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 }) is Handler,
        op_handler(Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 }) == HandlerId::DefinePrivate,
        op_class(Op::HasPrivate { dst: 0, name: 0, obj: 0 }) is Handler,
        op_handler(Op::HasPrivate { dst: 0, name: 0, obj: 0 }) == HandlerId::HasPrivate,
        op_class(Op::GetSuperBase { dst: 0, func: 0 }) is Handler,
        op_handler(Op::GetSuperBase { dst: 0, func: 0 }) == HandlerId::GetSuperBase,
        op_class(Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 }) is Handler,
        op_handler(Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 }) == HandlerId::GetSuper,
        op_class(Op::SetSuper { base: 0, key: 0, val: 0, this: 0 }) is Handler,
        op_handler(Op::SetSuper { base: 0, key: 0, val: 0, this: 0 }) == HandlerId::SetSuper,
        op_class(Op::GetNewTarget { dst: 0 }) is Handler,
        op_handler(Op::GetNewTarget { dst: 0 }) == HandlerId::GetNewTarget,
        op_class(Op::ConstructResult { dst: 0, val: 0, this: 0 }) is Handler,
        op_handler(Op::ConstructResult { dst: 0, val: 0, this: 0 }) == HandlerId::ConstructResult,
        op_class(Op::CreateUnmappedArguments { dst: 0 }) is Handler,
        op_handler(Op::CreateUnmappedArguments { dst: 0 }) == HandlerId::CreateUnmappedArguments,
        op_class(Op::CreateMappedArguments { dst: 0, env: 0, k: 0 }) is Handler,
        op_handler(Op::CreateMappedArguments { dst: 0, env: 0, k: 0 }) == HandlerId::CreateMappedArguments,
        op_class(Op::CreateRestArray { dst: 0, from: 0 }) is Handler,
        op_handler(Op::CreateRestArray { dst: 0, from: 0 }) == HandlerId::CreateRestArray,
        op_class(Op::ForInIterator { dst: 0, src: 0 }) is Handler,
        op_handler(Op::ForInIterator { dst: 0, src: 0 }) == HandlerId::ForInIterator,
{
    assert(op_class(Op::ToPropertyKey { dst: 0, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ToPropertyKey { dst: 0, src: 0 }) == HandlerId::ToPropertyKey) by (compute_only);
    assert(op_class(Op::ToString { dst: 0, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ToString { dst: 0, src: 0 }) == HandlerId::ToString) by (compute_only);
    assert(op_class(Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 }) is Handler) by (compute_only);
    assert(op_handler(Op::CopyDataProperties { obj: 0, src: 0, excl: 0, nexcl: 3 }) == HandlerId::CopyDataProperties) by (compute_only);
    assert(op_class(Op::GetTemplateObject { dst: 0, k: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetTemplateObject { dst: 0, k: 0 }) == HandlerId::GetTemplateObject) by (compute_only);
    assert(op_class(Op::NewSpread { dst: 0, callee: 0, args: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::NewSpread { dst: 0, callee: 0, args: 0 }) == HandlerId::NewSpread) by (compute_only);
    assert(op_class(Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }) is Handler) by (compute_only);
    assert(op_handler(Op::SuperCall { dst: 0, func: 0, newtarget: 0, this: 0, args: 0, argc: 3 }) == HandlerId::SuperCall) by (compute_only);
    assert(op_class(Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::SuperCallSpread { dst: 0, func: 0, newtarget: 0, this: 0, args: 0 }) == HandlerId::SuperCallSpread) by (compute_only);
    assert(op_class(Op::InitInstance { obj: 0, func: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::InitInstance { obj: 0, func: 0 }) == HandlerId::InitInstance) by (compute_only);
    assert(op_class(Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true }) is Handler) by (compute_only);
    assert(op_handler(Op::ClassSetup { ctor: 0, proto: 0, heritage: 0, derived: true }) == HandlerId::ClassSetup) by (compute_only);
    assert(op_class(Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true }) is Handler) by (compute_only);
    assert(op_handler(Op::DefineMethod { obj: 0, key: 0, func: 0, form: 2, enumerable: true }) == HandlerId::DefineMethod) by (compute_only);
    assert(op_class(Op::SetHomeObject { func: 0, obj: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::SetHomeObject { func: 0, obj: 0 }) == HandlerId::SetHomeObject) by (compute_only);
    assert(op_class(Op::SetInstanceInit { ctor: 0, init: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::SetInstanceInit { ctor: 0, init: 0 }) == HandlerId::SetInstanceInit) by (compute_only);
    assert(op_class(Op::NewPrivateName { dst: 0, k: 2 }) is Handler) by (compute_only);
    assert(op_handler(Op::NewPrivateName { dst: 0, k: 2 }) == HandlerId::NewPrivateName) by (compute_only);
    assert(op_class(Op::GetPrivate { dst: 0, obj: 0, name: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetPrivate { dst: 0, obj: 0, name: 0 }) == HandlerId::GetPrivate) by (compute_only);
    assert(op_class(Op::SetPrivate { obj: 0, name: 0, val: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::SetPrivate { obj: 0, name: 0, val: 0 }) == HandlerId::SetPrivate) by (compute_only);
    assert(op_class(Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 }) is Handler) by (compute_only);
    assert(op_handler(Op::DefinePrivate { obj: 0, name: 0, val: 0, form: 3 }) == HandlerId::DefinePrivate) by (compute_only);
    assert(op_class(Op::HasPrivate { dst: 0, name: 0, obj: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::HasPrivate { dst: 0, name: 0, obj: 0 }) == HandlerId::HasPrivate) by (compute_only);
    assert(op_class(Op::GetSuperBase { dst: 0, func: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetSuperBase { dst: 0, func: 0 }) == HandlerId::GetSuperBase) by (compute_only);
    assert(op_class(Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetSuper { dst: 0, base: 0, key: 0, this: 0 }) == HandlerId::GetSuper) by (compute_only);
    assert(op_class(Op::SetSuper { base: 0, key: 0, val: 0, this: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::SetSuper { base: 0, key: 0, val: 0, this: 0 }) == HandlerId::SetSuper) by (compute_only);
    assert(op_class(Op::GetNewTarget { dst: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetNewTarget { dst: 0 }) == HandlerId::GetNewTarget) by (compute_only);
    assert(op_class(Op::ConstructResult { dst: 0, val: 0, this: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ConstructResult { dst: 0, val: 0, this: 0 }) == HandlerId::ConstructResult) by (compute_only);
    assert(op_class(Op::CreateUnmappedArguments { dst: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::CreateUnmappedArguments { dst: 0 }) == HandlerId::CreateUnmappedArguments) by (compute_only);
    assert(op_class(Op::CreateMappedArguments { dst: 0, env: 0, k: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::CreateMappedArguments { dst: 0, env: 0, k: 0 }) == HandlerId::CreateMappedArguments) by (compute_only);
    assert(op_class(Op::CreateRestArray { dst: 0, from: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::CreateRestArray { dst: 0, from: 0 }) == HandlerId::CreateRestArray) by (compute_only);
    assert(op_class(Op::ForInIterator { dst: 0, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ForInIterator { dst: 0, src: 0 }) == HandlerId::ForInIterator) by (compute_only);
}

/// The operands `op_wf` accepts of the ops added for top-level lexical
/// declarations (`InitGlobalLexical`):
/// every register inside the frame (registers 0 to 2), every register range
/// inside it, every constant index inside the pool (0 to 2), a record constant
/// that is a value (constant 2 is not), and each small enumerated operand below
/// its bound.
pub proof fn example_global_lexical_wf()
    ensures
        op_wf(example_code(), Op::InitGlobalLexical { key: 2, src: 0 }),
        !op_wf(example_code(), Op::InitGlobalLexical { key: 3, src: 0 }),
        !op_wf(example_code(), Op::InitGlobalLexical { key: 2, src: 3 }),
{
    assert(op_wf(example_code(), Op::InitGlobalLexical { key: 2, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::InitGlobalLexical { key: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::InitGlobalLexical { key: 2, src: 3 })) by (compute_only);
}

/// The class and the handler of each op added for the compiler's second
/// slice: each always calls out (it can allocate, call user code or throw), so
/// each is a handler op, which the JIT lowers to an exit, with its own handler.
pub proof fn example_global_lexical_classes()
    ensures
        op_class(Op::InitGlobalLexical { key: 2, src: 0 }) is Handler,
        op_handler(Op::InitGlobalLexical { key: 2, src: 0 }) == HandlerId::InitGlobalLexical,
{
    assert(op_class(Op::InitGlobalLexical { key: 2, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::InitGlobalLexical { key: 2, src: 0 }) == HandlerId::InitGlobalLexical) by (compute_only);
}

/// The operands `op_wf` accepts of the ops added for regular expression literals (`NewRegExp`):
/// every register inside the frame (registers 0 to 2), every register range inside it, every
/// constant index inside the pool (0 to 2), a record constant that is a value (constant 2 is not),
/// and each small enumerated operand below its bound.
pub proof fn example_regex_wf()
    ensures
        op_wf(example_code(), Op::NewRegExp { dst: 0, k: 0 }),
        !op_wf(example_code(), Op::NewRegExp { dst: 3, k: 0 }),
        !op_wf(example_code(), Op::NewRegExp { dst: 0, k: 2 }),
{
    assert(op_wf(example_code(), Op::NewRegExp { dst: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewRegExp { dst: 3, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::NewRegExp { dst: 0, k: 2 })) by (compute_only);
}

/// The class and the handler of each op added for regular expression literals: each always calls
/// out (it can allocate, call user code or throw), so each is a handler op, which the JIT lowers to
/// an exit, with its own handler.
pub proof fn example_regex_classes()
    ensures
        op_class(Op::NewRegExp { dst: 0, k: 0 }) is Handler,
        op_handler(Op::NewRegExp { dst: 0, k: 0 }) == HandlerId::NewRegExp,
{
    assert(op_class(Op::NewRegExp { dst: 0, k: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::NewRegExp { dst: 0, k: 0 }) == HandlerId::NewRegExp) by (compute_only);
}

/// The operands `op_wf` accepts of the ops added for generators, async functions and `for await`
/// (`GeneratorStart`, `YieldDelegate`, `GetAsyncIterator`, `IterCallMethod`, `IterComplete`,
/// `IterValue`, `ThrowIfNotObject`): every register inside the frame (registers 0 to 2), every
/// register range inside it, every constant index inside the pool (0 to 2), a record constant that
/// is a value (constant 2 is not), and each small enumerated operand below its bound.
pub proof fn example_generators_wf()
    ensures
        op_wf(example_code(), Op::GeneratorStart),
        op_wf(example_code(), Op::YieldDelegate { src: 0, value: 0, mode: 0 }),
        !op_wf(example_code(), Op::YieldDelegate { src: 3, value: 0, mode: 0 }),
        !op_wf(example_code(), Op::YieldDelegate { src: 0, value: 3, mode: 0 }),
        !op_wf(example_code(), Op::YieldDelegate { src: 0, value: 0, mode: 3 }),
        op_wf(example_code(), Op::GetAsyncIterator { dst: 0, src: 0 }),
        !op_wf(example_code(), Op::GetAsyncIterator { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::GetAsyncIterator { dst: 0, src: 3 }),
        op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 }),
        !op_wf(example_code(), Op::IterCallMethod { dst: 3, found: 0, iter: 0, arg: 0, which: 0 }),
        !op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 3, iter: 0, arg: 0, which: 0 }),
        !op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 3, arg: 0, which: 0 }),
        !op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 3, which: 0 }),
        !op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 5 }),
        op_wf(example_code(), Op::IterComplete { done: 0, result: 0 }),
        !op_wf(example_code(), Op::IterComplete { done: 3, result: 0 }),
        !op_wf(example_code(), Op::IterComplete { done: 0, result: 3 }),
        op_wf(example_code(), Op::IterValue { dst: 0, result: 0 }),
        !op_wf(example_code(), Op::IterValue { dst: 3, result: 0 }),
        !op_wf(example_code(), Op::IterValue { dst: 0, result: 3 }),
        op_wf(example_code(), Op::ThrowIfNotObject { src: 0 }),
        !op_wf(example_code(), Op::ThrowIfNotObject { src: 3 }),
{
    assert(op_wf(example_code(), Op::GeneratorStart)) by (compute_only);
    assert(op_wf(example_code(), Op::YieldDelegate { src: 0, value: 0, mode: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::YieldDelegate { src: 3, value: 0, mode: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::YieldDelegate { src: 0, value: 3, mode: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::YieldDelegate { src: 0, value: 0, mode: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::GetAsyncIterator { dst: 0, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetAsyncIterator { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetAsyncIterator { dst: 0, src: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterCallMethod { dst: 3, found: 0, iter: 0, arg: 0, which: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 3, iter: 0, arg: 0, which: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 3, arg: 0, which: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 3, which: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 5 })) by (compute_only);
    assert(op_wf(example_code(), Op::IterComplete { done: 0, result: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterComplete { done: 3, result: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterComplete { done: 0, result: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::IterValue { dst: 0, result: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterValue { dst: 3, result: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::IterValue { dst: 0, result: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::ThrowIfNotObject { src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ThrowIfNotObject { src: 3 })) by (compute_only);
}

/// The class and the handler of each op added for generators, async functions and `for await`: each
/// always calls out (it can allocate, call user code or throw), so each is a handler op, which the
/// JIT lowers to an exit, with its own handler.
pub proof fn example_generators_classes()
    ensures
        op_class(Op::GeneratorStart) is Handler,
        op_handler(Op::GeneratorStart) == HandlerId::GeneratorStart,
        op_class(Op::YieldDelegate { src: 0, value: 0, mode: 0 }) is Handler,
        op_handler(Op::YieldDelegate { src: 0, value: 0, mode: 0 }) == HandlerId::YieldDelegate,
        op_class(Op::GetAsyncIterator { dst: 0, src: 0 }) is Handler,
        op_handler(Op::GetAsyncIterator { dst: 0, src: 0 }) == HandlerId::GetAsyncIterator,
        op_class(Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 }) is Handler,
        op_handler(Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 }) == HandlerId::IterCallMethod,
        op_class(Op::IterComplete { done: 0, result: 0 }) is Handler,
        op_handler(Op::IterComplete { done: 0, result: 0 }) == HandlerId::IterComplete,
        op_class(Op::IterValue { dst: 0, result: 0 }) is Handler,
        op_handler(Op::IterValue { dst: 0, result: 0 }) == HandlerId::IterValue,
        op_class(Op::ThrowIfNotObject { src: 0 }) is Handler,
        op_handler(Op::ThrowIfNotObject { src: 0 }) == HandlerId::ThrowIfNotObject,
{
    assert(op_class(Op::GeneratorStart) is Handler) by (compute_only);
    assert(op_handler(Op::GeneratorStart) == HandlerId::GeneratorStart) by (compute_only);
    assert(op_class(Op::YieldDelegate { src: 0, value: 0, mode: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::YieldDelegate { src: 0, value: 0, mode: 0 }) == HandlerId::YieldDelegate) by (compute_only);
    assert(op_class(Op::GetAsyncIterator { dst: 0, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetAsyncIterator { dst: 0, src: 0 }) == HandlerId::GetAsyncIterator) by (compute_only);
    assert(op_class(Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::IterCallMethod { dst: 0, found: 0, iter: 0, arg: 0, which: 0 }) == HandlerId::IterCallMethod) by (compute_only);
    assert(op_class(Op::IterComplete { done: 0, result: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::IterComplete { done: 0, result: 0 }) == HandlerId::IterComplete) by (compute_only);
    assert(op_class(Op::IterValue { dst: 0, result: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::IterValue { dst: 0, result: 0 }) == HandlerId::IterValue) by (compute_only);
    assert(op_class(Op::ThrowIfNotObject { src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ThrowIfNotObject { src: 0 }) == HandlerId::ThrowIfNotObject) by (compute_only);
}

/// The operands `op_wf` accepts of the ops added for `with`, direct `eval` and `delete` of a
/// variable (`ToObject`, `WithHas`, `WithGet`, `WithSet`, `WithDelete`, `DeleteGlobal`,
/// `DirectEval`): every register inside the frame (registers 0 to 2), every register range inside
/// it, every constant index inside the pool (0 to 2), a record constant that is a value (constant 2
/// is not), and each small enumerated operand below its bound.
pub proof fn example_withs_wf()
    ensures
        op_wf(example_code(), Op::ToObject { dst: 0, src: 0 }),
        !op_wf(example_code(), Op::ToObject { dst: 3, src: 0 }),
        !op_wf(example_code(), Op::ToObject { dst: 0, src: 3 }),
        op_wf(example_code(), Op::WithHas { dst: 0, obj: 0, key: 0 }),
        !op_wf(example_code(), Op::WithHas { dst: 3, obj: 0, key: 0 }),
        !op_wf(example_code(), Op::WithHas { dst: 0, obj: 3, key: 0 }),
        !op_wf(example_code(), Op::WithHas { dst: 0, obj: 0, key: 3 }),
        op_wf(example_code(), Op::WithGet { dst: 0, obj: 0, key: 0, strict: false }),
        !op_wf(example_code(), Op::WithGet { dst: 3, obj: 0, key: 0, strict: false }),
        !op_wf(example_code(), Op::WithGet { dst: 0, obj: 3, key: 0, strict: false }),
        !op_wf(example_code(), Op::WithGet { dst: 0, obj: 0, key: 3, strict: false }),
        op_wf(example_code(), Op::WithSet { obj: 0, key: 0, val: 0, strict: false }),
        !op_wf(example_code(), Op::WithSet { obj: 3, key: 0, val: 0, strict: false }),
        !op_wf(example_code(), Op::WithSet { obj: 0, key: 3, val: 0, strict: false }),
        !op_wf(example_code(), Op::WithSet { obj: 0, key: 0, val: 3, strict: false }),
        op_wf(example_code(), Op::WithDelete { dst: 0, obj: 0, key: 0 }),
        !op_wf(example_code(), Op::WithDelete { dst: 3, obj: 0, key: 0 }),
        !op_wf(example_code(), Op::WithDelete { dst: 0, obj: 3, key: 0 }),
        !op_wf(example_code(), Op::WithDelete { dst: 0, obj: 0, key: 3 }),
        op_wf(example_code(), Op::DeleteGlobal { dst: 0, key: 0 }),
        !op_wf(example_code(), Op::DeleteGlobal { dst: 3, key: 0 }),
        !op_wf(example_code(), Op::DeleteGlobal { dst: 0, key: 3 }),
        op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 3, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 0, callee: 3, this: 0, args: 0, argc: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 3, args: 0, argc: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 2, argc: 2, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 3, k: 0 }),
        !op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 2 }),
{
    assert(op_wf(example_code(), Op::ToObject { dst: 0, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToObject { dst: 3, src: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ToObject { dst: 0, src: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::WithHas { dst: 0, obj: 0, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithHas { dst: 3, obj: 0, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithHas { dst: 0, obj: 3, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithHas { dst: 0, obj: 0, key: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::WithGet { dst: 0, obj: 0, key: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithGet { dst: 3, obj: 0, key: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithGet { dst: 0, obj: 3, key: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithGet { dst: 0, obj: 0, key: 3, strict: false })) by (compute_only);
    assert(op_wf(example_code(), Op::WithSet { obj: 0, key: 0, val: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithSet { obj: 3, key: 0, val: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithSet { obj: 0, key: 3, val: 0, strict: false })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithSet { obj: 0, key: 0, val: 3, strict: false })) by (compute_only);
    assert(op_wf(example_code(), Op::WithDelete { dst: 0, obj: 0, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithDelete { dst: 3, obj: 0, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithDelete { dst: 0, obj: 3, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::WithDelete { dst: 0, obj: 0, key: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DeleteGlobal { dst: 0, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DeleteGlobal { dst: 3, key: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DeleteGlobal { dst: 0, key: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 3, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 0, callee: 3, this: 0, args: 0, argc: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 3, args: 0, argc: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 2, argc: 2, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 3, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 2 })) by (compute_only);
}

/// The class and the handler of each op added for `with`, direct `eval` and `delete` of a variable:
/// each always calls out (it can allocate, call user code or throw), so each is a handler op, which
/// the JIT lowers to an exit, with its own handler.
pub proof fn example_withs_classes()
    ensures
        op_class(Op::ToObject { dst: 0, src: 0 }) is Handler,
        op_handler(Op::ToObject { dst: 0, src: 0 }) == HandlerId::ToObject,
        op_class(Op::WithHas { dst: 0, obj: 0, key: 0 }) is Handler,
        op_handler(Op::WithHas { dst: 0, obj: 0, key: 0 }) == HandlerId::WithHas,
        op_class(Op::WithGet { dst: 0, obj: 0, key: 0, strict: false }) is Handler,
        op_handler(Op::WithGet { dst: 0, obj: 0, key: 0, strict: false }) == HandlerId::WithGet,
        op_class(Op::WithSet { obj: 0, key: 0, val: 0, strict: false }) is Handler,
        op_handler(Op::WithSet { obj: 0, key: 0, val: 0, strict: false }) == HandlerId::WithSet,
        op_class(Op::WithDelete { dst: 0, obj: 0, key: 0 }) is Handler,
        op_handler(Op::WithDelete { dst: 0, obj: 0, key: 0 }) == HandlerId::WithDelete,
        op_class(Op::DeleteGlobal { dst: 0, key: 0 }) is Handler,
        op_handler(Op::DeleteGlobal { dst: 0, key: 0 }) == HandlerId::DeleteGlobal,
        op_class(Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }) is Handler,
        op_handler(Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }) == HandlerId::DirectEval,
{
    assert(op_class(Op::ToObject { dst: 0, src: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ToObject { dst: 0, src: 0 }) == HandlerId::ToObject) by (compute_only);
    assert(op_class(Op::WithHas { dst: 0, obj: 0, key: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::WithHas { dst: 0, obj: 0, key: 0 }) == HandlerId::WithHas) by (compute_only);
    assert(op_class(Op::WithGet { dst: 0, obj: 0, key: 0, strict: false }) is Handler) by (compute_only);
    assert(op_handler(Op::WithGet { dst: 0, obj: 0, key: 0, strict: false }) == HandlerId::WithGet) by (compute_only);
    assert(op_class(Op::WithSet { obj: 0, key: 0, val: 0, strict: false }) is Handler) by (compute_only);
    assert(op_handler(Op::WithSet { obj: 0, key: 0, val: 0, strict: false }) == HandlerId::WithSet) by (compute_only);
    assert(op_class(Op::WithDelete { dst: 0, obj: 0, key: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::WithDelete { dst: 0, obj: 0, key: 0 }) == HandlerId::WithDelete) by (compute_only);
    assert(op_class(Op::DeleteGlobal { dst: 0, key: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::DeleteGlobal { dst: 0, key: 0 }) == HandlerId::DeleteGlobal) by (compute_only);
    assert(op_class(Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::DirectEval { dst: 0, callee: 0, this: 0, args: 0, argc: 3, env: 0, k: 0 }) == HandlerId::DirectEval) by (compute_only);
}

/// The operands `op_wf` accepts of the ops added for modules and `import()` (`GetImportBinding`,
/// `ImportCall`, `ImportMeta`) and for direct `eval` with a spread argument (`DirectEvalSpread`):
/// every register inside the frame (registers 0 to 2), every constant index inside the pool (0 to
/// 2), and a record constant that is a value (constant 2 is not).
pub proof fn example_imports_wf()
    ensures
        op_wf(example_code(), Op::GetImportBinding { dst: 0, env: 0, idx: 0 }),
        !op_wf(example_code(), Op::GetImportBinding { dst: 3, env: 0, idx: 0 }),
        !op_wf(example_code(), Op::GetImportBinding { dst: 0, env: 3, idx: 0 }),
        op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 0, options: 0 }),
        !op_wf(example_code(), Op::ImportCall { dst: 3, specifier: 0, options: 0 }),
        !op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 3, options: 0 }),
        !op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 0, options: 3 }),
        op_wf(example_code(), Op::ImportMeta { dst: 0 }),
        !op_wf(example_code(), Op::ImportMeta { dst: 3 }),
        op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 3, callee: 0, this: 0, args: 0, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 3, this: 0, args: 0, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 3, args: 0, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 3, env: 0, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 3, k: 0 }),
        !op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 2 }),
{
    assert(op_wf(example_code(), Op::GetImportBinding { dst: 0, env: 0, idx: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetImportBinding { dst: 3, env: 0, idx: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::GetImportBinding { dst: 0, env: 3, idx: 0 })) by (compute_only);
    assert(op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 0, options: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ImportCall { dst: 3, specifier: 0, options: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 3, options: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ImportCall { dst: 0, specifier: 0, options: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::ImportMeta { dst: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::ImportMeta { dst: 3 })) by (compute_only);
    assert(op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 3, callee: 0, this: 0, args: 0, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 3, this: 0, args: 0, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 3, args: 0, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 3, env: 0, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 3, k: 0 })) by (compute_only);
    assert(!op_wf(example_code(), Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 2 })) by (compute_only);
}

/// The class and the handler of each op added for modules and `import()`, and for direct `eval`
/// with a spread argument: each always calls out (it can allocate, call user code, call the host
/// or throw), so each is a handler op, which the JIT lowers to an exit, with its own handler.
pub proof fn example_imports_classes()
    ensures
        op_class(Op::GetImportBinding { dst: 0, env: 0, idx: 0 }) is Handler,
        op_handler(Op::GetImportBinding { dst: 0, env: 0, idx: 0 }) == HandlerId::GetImportBinding,
        op_class(Op::ImportCall { dst: 0, specifier: 0, options: 0 }) is Handler,
        op_handler(Op::ImportCall { dst: 0, specifier: 0, options: 0 }) == HandlerId::ImportCall,
        op_class(Op::ImportMeta { dst: 0 }) is Handler,
        op_handler(Op::ImportMeta { dst: 0 }) == HandlerId::ImportMeta,
        op_class(Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 }) is Handler,
        op_handler(Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 }) == HandlerId::DirectEvalSpread,
{
    assert(op_class(Op::GetImportBinding { dst: 0, env: 0, idx: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::GetImportBinding { dst: 0, env: 0, idx: 0 }) == HandlerId::GetImportBinding) by (compute_only);
    assert(op_class(Op::ImportCall { dst: 0, specifier: 0, options: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ImportCall { dst: 0, specifier: 0, options: 0 }) == HandlerId::ImportCall) by (compute_only);
    assert(op_class(Op::ImportMeta { dst: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::ImportMeta { dst: 0 }) == HandlerId::ImportMeta) by (compute_only);
    assert(op_class(Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 }) is Handler) by (compute_only);
    assert(op_handler(Op::DirectEvalSpread { dst: 0, callee: 0, this: 0, args: 0, env: 0, k: 0 }) == HandlerId::DirectEvalSpread) by (compute_only);
}

} // verus!
