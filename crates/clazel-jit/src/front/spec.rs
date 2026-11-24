//! What the JS front end is *about* (jit.md item J.10): the state relation
//! between a bytecode machine state and a LIR state, the exit protocol, and
//! the per-op outcome a lowering must have. Nothing here runs and nothing is
//! proven; the lowerings are in `lower` and their proofs after it.
//!
//! # Source
//!
//! There is no standard to transcribe. The sources are:
//!
//! - **jit.md, "J.10 JS front end"**: "One lowering per bytecode op: fast
//!   paths inline [...]; everything else is an exit to the shared handler.
//!   Proof per op: the LIR refines `step`. This is written once and holds on
//!   both instruction sets, because it stops at LIR."
//! - **phase-7.md, "Shapes fixed here for the JIT"**: "Each frame is a window
//!   of `u64` slots in one value-stack region: header slots [...], then
//!   arguments, then registers. The interpreter and the JIT read and write
//!   the same slots." And: "Every op that can allocate, call out, or throw is
//!   distinguished, and is an exit in the JIT and a handler call in the
//!   interpreter. Handlers are plain Rust functions over the frame region and
//!   the heap, shared by both." (item 7.8 repeats it.)
//! - **`clazel-js-vm`'s `spec`** ([`js::step`], [`js::fast_path`],
//!   [`js::fast_step`], [`js::handler`]): the meaning of the source.
//! - **`clazel-lir`'s `spec`** ([`lir::eval`]): the meaning of the target.
//!
//! # Modelling choices
//!
//! 1. **The value stack is LIR region 0.** Slot `j` of the bytecode machine's
//!    `region` is the 8 bytes of LIR memory at `base(0) + 8 j`, little-endian
//!    ([`mem_rel`]), and the region's bound is `8 × region.len()`
//!    ([`layout_ok`]). A NaN-boxed value is stored as the `u64` it is, so the
//!    interpreter and the JIT read and write the same bytes.
//! 2. **The frame base is LIR local 0**: the `i64` `8 × fp`, the byte offset
//!    of the current frame in region 0 ([`locals_rel`]). Register `r` is at
//!    byte `8 (hdr_slots + r)` from it ([`reg_off`]), a header slot `k` at
//!    `8 k` ([`hdr_off`]). Every access is a `bounds_check` followed by a
//!    `load` or `store`, as LIR requires; under the relation and
//!    [`js::state_wf`] the check never fails, and the statement says so (no
//!    exit but a handler exit).
//! 3. **Locals `1 ..` are scratch.** A lowering keeps intermediate values in
//!    locals `1 .. nlocals()`, all `i64`, so the relation says they have that
//!    type and nothing else about them.
//! 4. **`pc` is a position in the code, not a value.** Code of one function is
//!    one LIR body whose control flow is the bytecode's; the lowering of the
//!    op at `pc` runs when control reaches that op. Falling off the end of a
//!    lowering is "continue with the op at `pc + 1`", and a branch to label
//!    `lbl` is "continue at the jump's target" (the lowering takes `lbl`, the
//!    depth the whole-function layout gives that target; that layout is a
//!    later slice). The statement therefore says what `pc` *becomes*
//!    ([`outcome_refines`]), not what a LIR value is.
//! 5. **The operand stack is empty between ops.** Every bytecode value lives
//!    in region 0, so LIR's operand stack is empty when a lowering starts and
//!    when it falls through or branches. At an exit the stack holds scratch
//!    values the handler does not read, so the relation does not mention it.
//! 6. **Only the frame is represented.** A bytecode state has more than the
//!    region: the heap, the code tables, the inline-cache tables, the thrown
//!    value and the termination flag. LIR has no such thing in this slice, and
//!    none of the lowered ops changes any of them, so a lowering's
//!    [`outcome_refines`] says they are *unchanged* ([`same_unrepresented`]),
//!    and an exit hands the handler the state the relation names, with those
//!    fields as they were. How the heap and the caches are laid out in bytes
//!    is the heap crate's (phase-7.md 7.5) and not yet fixed, so no op that
//!    reads or writes them is lowered (`GetProp`, `SetProp` and the rest).
//! 7. **An exit names its handler, and carries `pc`.** `exit(c, [i32])` with
//!    `c =` [`handler_index`]`(op_handler(op))` and the one operand `pc`. The
//!    host reads the op at `pc` of the current function, as the interpreter
//!    does, and runs `handler(h, s, op)` on the frame region in memory and the
//!    rest of the state it already has. [`handler_of_index`] is the host's
//!    decoding.
//! 8. **A lowering may exit before the fast path fails.** `step` calls the
//!    handler when `fast_path` fails, and jit.md reads that as "inline the
//!    fast path, exit otherwise". That is exact only when the inline test is
//!    exactly `fast_path`. Small-integer `Add` cannot be: its `fast_path` is
//!    "two Numbers", whose result for two doubles is `f64_add_finite`, which
//!    LIR cannot compute (modelling choice 6 of both specs: the rounding is
//!    uninterpreted, and two different uninterpreted functions are unrelated).
//!    So the lowering tests the cases it can do (two int32 operands, the sum
//!    in range) and exits for the rest, **including cases where `fast_path`
//!    holds**. That is a correct implementation of `step` only if the handler
//!    computes `fast_step` there, which is the handler's contract (7.8: a
//!    handler is the op's whole semantics, the fast path only an inlined part
//!    of it). **That is [`handler_complete`], an explicit hypothesis of
//!    [`crate::front::contract::lowers`], not an axiom**: it is `step`'s own
//!    shape, `handler(h, s, op) == fast_step(s, op)` wherever `fast_path`
//!    holds, and 7.8 has to prove it of each handler. Where a lowering's exits
//!    are exactly `!fast_path` it is not used.

/// The bytecode machine's semantics, re-exported so that this crate's
/// modules read one namespace.
pub use clazel_js_vm::spec as js;
/// LIR's semantics, re-exported likewise.
pub use clazel_lir::spec as lir;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: the frame in LIR
// ============================================================================

/// The LIR region that holds the value stack (modelling choice 1).
pub open spec fn stack_region() -> lir::RegionId {
    0
}

/// The number of LIR locals a lowering uses: local 0 is the frame base, the
/// others are scratch (modelling choices 2 and 3).
pub open spec fn nlocals() -> nat {
    4
}

/// The byte offset from the frame base of header slot `k`
/// ([`js::hdr_callee`], [`js::hdr_this`], ...).
pub open spec fn hdr_off(k: nat) -> nat {
    8 * k
}

/// The byte offset from the frame base of register `r`
/// ([`js::reg_slot`]: the header, then the arguments and registers).
pub open spec fn reg_off(r: nat) -> nat {
    8 * (js::hdr_slots() + r)
}

/// The LIR address of slot `j` of the value-stack region.
pub open spec fn slot_addr(lay: lir::Layout, j: int) -> nat
    recommends
        lay.len() > 0,
{
    (lay[0].base + 8 * j) as nat
}

// ============================================================================
// Section: the state relation
// ============================================================================

/// The layout has the value stack as region 0, exactly as large as the
/// bytecode machine's region, and every region lies below `2^64`.
pub open spec fn layout_ok(lay: lir::Layout, s: js::State) -> bool {
    &&& lay.len() >= 1
    &&& lir::layout_wf(lay)
    &&& lay[0].bound == 8 * s.region.len()
}

/// LIR's memory holds the bytecode machine's region: slot `j` is the 8 bytes
/// at its address, little-endian (modelling choice 1).
pub open spec fn mem_rel(lay: lir::Layout, region: Seq<u64>, m: lir::Mem) -> bool
    recommends
        lay.len() > 0,
{
    forall|j: int|
        #![trigger region[j]]
        0 <= j < region.len() ==> lir::read_le(m, slot_addr(lay, j), 8) == region[j] as nat
}

/// The LIR locals: local 0 is the frame base in bytes, the rest are `i64`
/// scratch (modelling choices 2 and 3).
pub open spec fn locals_rel(s: js::State, l: Seq<lir::Val>) -> bool {
    &&& l.len() == nlocals()
    &&& l[0] == lir::Val::I64((8 * s.fp) as u64)
    &&& forall|j: int| 1 <= j < l.len() ==> #[trigger] l[j] is I64
}

/// **The state relation**: the bytecode machine state `s` and the LIR state
/// `st` agree on the frame. The operand stack is not part of it (modelling
/// choice 5), and nothing of `s` but its region and `fp` is represented
/// (modelling choice 6).
pub open spec fn rel(lay: lir::Layout, s: js::State, st: lir::St) -> bool {
    &&& layout_ok(lay, s)
    &&& locals_rel(s, st.locals)
    &&& mem_rel(lay, s.region, st.mem)
}

/// The parts of the bytecode state that LIR does not represent are the same
/// in `s` and `s2` (modelling choice 6).
pub open spec fn same_unrepresented(s: js::State, s2: js::State) -> bool {
    &&& s2.heap == s.heap
    &&& s2.codes == s.codes
    &&& s2.ics == s.ics
    &&& s2.exception == s.exception
    &&& s2.terminate == s.terminate
}

// ============================================================================
// Section: exits
// ============================================================================

/// The exit code of a handler (modelling choice 7): its position in
/// [`js::HandlerId`]'s declaration. [`handler_of_index`] inverts it.
pub open spec fn handler_index(h: js::HandlerId) -> nat {
    match h {
        js::HandlerId::Add => 0,
        js::HandlerId::Sub => 1,
        js::HandlerId::Mul => 2,
        js::HandlerId::Div => 3,
        js::HandlerId::Mod => 4,
        js::HandlerId::Exp => 5,
        js::HandlerId::Neg => 6,
        js::HandlerId::Inc => 7,
        js::HandlerId::Dec => 8,
        js::HandlerId::BitAnd => 9,
        js::HandlerId::BitOr => 10,
        js::HandlerId::BitXor => 11,
        js::HandlerId::Shl => 12,
        js::HandlerId::Shr => 13,
        js::HandlerId::UShr => 14,
        js::HandlerId::BitNot => 15,
        js::HandlerId::Lt => 16,
        js::HandlerId::Le => 17,
        js::HandlerId::Gt => 18,
        js::HandlerId::Ge => 19,
        js::HandlerId::StrictEq => 20,
        js::HandlerId::LooseEq => 21,
        js::HandlerId::Not => 22,
        js::HandlerId::ToNumeric => 23,
        js::HandlerId::ToNumber => 24,
        js::HandlerId::ToBoolean => 25,
        js::HandlerId::Terminate => 26,
        js::HandlerId::ThrowHole => 27,
        js::HandlerId::GetProp => 28,
        js::HandlerId::SetProp => 29,
        js::HandlerId::GetElem => 30,
        js::HandlerId::SetElem => 31,
        js::HandlerId::Call => 32,
        js::HandlerId::Return => 33,
        js::HandlerId::EnvAccess => 34,
        js::HandlerId::TypeOf => 35,
        js::HandlerId::InstanceOf => 36,
        js::HandlerId::HasProperty => 37,
        js::HandlerId::DeleteProp => 38,
        js::HandlerId::GetGlobal => 39,
        js::HandlerId::SetGlobal => 40,
        js::HandlerId::GetGlobalOrUndefined => 41,
        js::HandlerId::DeclareGlobals => 42,
        js::HandlerId::DefineProp => 43,
        js::HandlerId::DefineElem => 44,
        js::HandlerId::SetLiteralProto => 45,
        js::HandlerId::NewObject => 46,
        js::HandlerId::NewArray => 47,
        js::HandlerId::NewEnv => 48,
        js::HandlerId::NewClosure => 49,
        js::HandlerId::New => 50,
        js::HandlerId::CallSpread => 51,
        js::HandlerId::GetIterator => 52,
        js::HandlerId::IterNext => 53,
        js::HandlerId::IterClose => 54,
        js::HandlerId::Yield => 55,
        js::HandlerId::Await => 56,
        js::HandlerId::Throw => 57,
        js::HandlerId::ThrowError => 58,
        js::HandlerId::ToPropertyKey => 59,
        js::HandlerId::ToString => 60,
        js::HandlerId::CopyDataProperties => 61,
        js::HandlerId::GetTemplateObject => 62,
        js::HandlerId::NewSpread => 63,
        js::HandlerId::SuperCall => 64,
        js::HandlerId::SuperCallSpread => 65,
        js::HandlerId::InitInstance => 66,
        js::HandlerId::ClassSetup => 67,
        js::HandlerId::DefineMethod => 68,
        js::HandlerId::SetHomeObject => 69,
        js::HandlerId::SetInstanceInit => 70,
        js::HandlerId::NewPrivateName => 71,
        js::HandlerId::GetPrivate => 72,
        js::HandlerId::SetPrivate => 73,
        js::HandlerId::DefinePrivate => 74,
        js::HandlerId::HasPrivate => 75,
        js::HandlerId::GetSuperBase => 76,
        js::HandlerId::GetSuper => 77,
        js::HandlerId::SetSuper => 78,
        js::HandlerId::GetNewTarget => 79,
        js::HandlerId::ConstructResult => 80,
        js::HandlerId::CreateUnmappedArguments => 81,
        js::HandlerId::CreateMappedArguments => 82,
        js::HandlerId::CreateRestArray => 83,
        js::HandlerId::ForInIterator => 84,
        js::HandlerId::InitGlobalLexical => 85,
        js::HandlerId::NewRegExp => 86,
        js::HandlerId::GeneratorStart => 87,
        js::HandlerId::YieldDelegate => 88,
        js::HandlerId::GetAsyncIterator => 89,
        js::HandlerId::IterCallMethod => 90,
        js::HandlerId::IterComplete => 91,
        js::HandlerId::IterValue => 92,
        js::HandlerId::ThrowIfNotObject => 93,
        js::HandlerId::ToObject => 94,
        js::HandlerId::WithHas => 95,
        js::HandlerId::WithGet => 96,
        js::HandlerId::WithSet => 97,
        js::HandlerId::WithDelete => 98,
        js::HandlerId::DeleteGlobal => 99,
        js::HandlerId::DirectEval => 100,
        js::HandlerId::GetImportBinding => 101,
        js::HandlerId::ImportCall => 102,
        js::HandlerId::ImportMeta => 103,
        js::HandlerId::DirectEvalSpread => 104,
    }
}

/// The handler an exit code names: the host's decoding of
/// [`handler_index`], `None` for a code that is no handler's.
pub open spec fn handler_of_index(n: nat) -> Option<js::HandlerId> {
    if n == 0 {
        Some(js::HandlerId::Add)
    } else if n == 1 {
        Some(js::HandlerId::Sub)
    } else if n == 2 {
        Some(js::HandlerId::Mul)
    } else if n == 3 {
        Some(js::HandlerId::Div)
    } else if n == 4 {
        Some(js::HandlerId::Mod)
    } else if n == 5 {
        Some(js::HandlerId::Exp)
    } else if n == 6 {
        Some(js::HandlerId::Neg)
    } else if n == 7 {
        Some(js::HandlerId::Inc)
    } else if n == 8 {
        Some(js::HandlerId::Dec)
    } else if n == 9 {
        Some(js::HandlerId::BitAnd)
    } else if n == 10 {
        Some(js::HandlerId::BitOr)
    } else if n == 11 {
        Some(js::HandlerId::BitXor)
    } else if n == 12 {
        Some(js::HandlerId::Shl)
    } else if n == 13 {
        Some(js::HandlerId::Shr)
    } else if n == 14 {
        Some(js::HandlerId::UShr)
    } else if n == 15 {
        Some(js::HandlerId::BitNot)
    } else if n == 16 {
        Some(js::HandlerId::Lt)
    } else if n == 17 {
        Some(js::HandlerId::Le)
    } else if n == 18 {
        Some(js::HandlerId::Gt)
    } else if n == 19 {
        Some(js::HandlerId::Ge)
    } else if n == 20 {
        Some(js::HandlerId::StrictEq)
    } else if n == 21 {
        Some(js::HandlerId::LooseEq)
    } else if n == 22 {
        Some(js::HandlerId::Not)
    } else if n == 23 {
        Some(js::HandlerId::ToNumeric)
    } else if n == 24 {
        Some(js::HandlerId::ToNumber)
    } else if n == 25 {
        Some(js::HandlerId::ToBoolean)
    } else if n == 26 {
        Some(js::HandlerId::Terminate)
    } else if n == 27 {
        Some(js::HandlerId::ThrowHole)
    } else if n == 28 {
        Some(js::HandlerId::GetProp)
    } else if n == 29 {
        Some(js::HandlerId::SetProp)
    } else if n == 30 {
        Some(js::HandlerId::GetElem)
    } else if n == 31 {
        Some(js::HandlerId::SetElem)
    } else if n == 32 {
        Some(js::HandlerId::Call)
    } else if n == 33 {
        Some(js::HandlerId::Return)
    } else if n == 34 {
        Some(js::HandlerId::EnvAccess)
    } else if n == 35 {
        Some(js::HandlerId::TypeOf)
    } else if n == 36 {
        Some(js::HandlerId::InstanceOf)
    } else if n == 37 {
        Some(js::HandlerId::HasProperty)
    } else if n == 38 {
        Some(js::HandlerId::DeleteProp)
    } else if n == 39 {
        Some(js::HandlerId::GetGlobal)
    } else if n == 40 {
        Some(js::HandlerId::SetGlobal)
    } else if n == 41 {
        Some(js::HandlerId::GetGlobalOrUndefined)
    } else if n == 42 {
        Some(js::HandlerId::DeclareGlobals)
    } else if n == 43 {
        Some(js::HandlerId::DefineProp)
    } else if n == 44 {
        Some(js::HandlerId::DefineElem)
    } else if n == 45 {
        Some(js::HandlerId::SetLiteralProto)
    } else if n == 46 {
        Some(js::HandlerId::NewObject)
    } else if n == 47 {
        Some(js::HandlerId::NewArray)
    } else if n == 48 {
        Some(js::HandlerId::NewEnv)
    } else if n == 49 {
        Some(js::HandlerId::NewClosure)
    } else if n == 50 {
        Some(js::HandlerId::New)
    } else if n == 51 {
        Some(js::HandlerId::CallSpread)
    } else if n == 52 {
        Some(js::HandlerId::GetIterator)
    } else if n == 53 {
        Some(js::HandlerId::IterNext)
    } else if n == 54 {
        Some(js::HandlerId::IterClose)
    } else if n == 55 {
        Some(js::HandlerId::Yield)
    } else if n == 56 {
        Some(js::HandlerId::Await)
    } else if n == 57 {
        Some(js::HandlerId::Throw)
    } else if n == 58 {
        Some(js::HandlerId::ThrowError)
    } else if n == 59 {
        Some(js::HandlerId::ToPropertyKey)
    } else if n == 60 {
        Some(js::HandlerId::ToString)
    } else if n == 61 {
        Some(js::HandlerId::CopyDataProperties)
    } else if n == 62 {
        Some(js::HandlerId::GetTemplateObject)
    } else if n == 63 {
        Some(js::HandlerId::NewSpread)
    } else if n == 64 {
        Some(js::HandlerId::SuperCall)
    } else if n == 65 {
        Some(js::HandlerId::SuperCallSpread)
    } else if n == 66 {
        Some(js::HandlerId::InitInstance)
    } else if n == 67 {
        Some(js::HandlerId::ClassSetup)
    } else if n == 68 {
        Some(js::HandlerId::DefineMethod)
    } else if n == 69 {
        Some(js::HandlerId::SetHomeObject)
    } else if n == 70 {
        Some(js::HandlerId::SetInstanceInit)
    } else if n == 71 {
        Some(js::HandlerId::NewPrivateName)
    } else if n == 72 {
        Some(js::HandlerId::GetPrivate)
    } else if n == 73 {
        Some(js::HandlerId::SetPrivate)
    } else if n == 74 {
        Some(js::HandlerId::DefinePrivate)
    } else if n == 75 {
        Some(js::HandlerId::HasPrivate)
    } else if n == 76 {
        Some(js::HandlerId::GetSuperBase)
    } else if n == 77 {
        Some(js::HandlerId::GetSuper)
    } else if n == 78 {
        Some(js::HandlerId::SetSuper)
    } else if n == 79 {
        Some(js::HandlerId::GetNewTarget)
    } else if n == 80 {
        Some(js::HandlerId::ConstructResult)
    } else if n == 81 {
        Some(js::HandlerId::CreateUnmappedArguments)
    } else if n == 82 {
        Some(js::HandlerId::CreateMappedArguments)
    } else if n == 83 {
        Some(js::HandlerId::CreateRestArray)
    } else if n == 84 {
        Some(js::HandlerId::ForInIterator)
    } else if n == 85 {
        Some(js::HandlerId::InitGlobalLexical)
    } else if n == 86 {
        Some(js::HandlerId::NewRegExp)
    } else if n == 87 {
        Some(js::HandlerId::GeneratorStart)
    } else if n == 88 {
        Some(js::HandlerId::YieldDelegate)
    } else if n == 89 {
        Some(js::HandlerId::GetAsyncIterator)
    } else if n == 90 {
        Some(js::HandlerId::IterCallMethod)
    } else if n == 91 {
        Some(js::HandlerId::IterComplete)
    } else if n == 92 {
        Some(js::HandlerId::IterValue)
    } else if n == 93 {
        Some(js::HandlerId::ThrowIfNotObject)
    } else if n == 94 {
        Some(js::HandlerId::ToObject)
    } else if n == 95 {
        Some(js::HandlerId::WithHas)
    } else if n == 96 {
        Some(js::HandlerId::WithGet)
    } else if n == 97 {
        Some(js::HandlerId::WithSet)
    } else if n == 98 {
        Some(js::HandlerId::WithDelete)
    } else if n == 99 {
        Some(js::HandlerId::DeleteGlobal)
    } else if n == 100 {
        Some(js::HandlerId::DirectEval)
    } else if n == 101 {
        Some(js::HandlerId::GetImportBinding)
    } else if n == 102 {
        Some(js::HandlerId::ImportCall)
    } else if n == 103 {
        Some(js::HandlerId::ImportMeta)
    } else if n == 104 {
        Some(js::HandlerId::DirectEvalSpread)
    } else {
        None
    }
}

/// The handler computes `fast_step` wherever `fast_path` holds
/// (modelling choice 8). A hypothesis of the refinement statement about the
/// handlers, which phase-7.md 7.8 must prove of each; **not an axiom**.
pub open spec fn handler_complete(s: js::State, op: js::Op) -> bool {
    js::fast_path(s, op) ==> js::handler(js::op_handler(op), s, op) == js::fast_step(s, op)
}

/// The target of a jump op, `None` for any other.
pub open spec fn jump_target(op: js::Op) -> Option<nat> {
    match op {
        js::Op::Jump { target } => Some(target),
        js::Op::JumpIfUndefined { target, .. } => Some(target),
        js::Op::JumpIfNotUndefined { target, .. } => Some(target),
        js::Op::JumpIfNullish { target, .. } => Some(target),
        js::Op::JumpIfNotNullish { target, .. } => Some(target),
        js::Op::JumpIfTrue { target, .. } => Some(target),
        js::Op::JumpIfFalse { target, .. } => Some(target),
        js::Op::Loop { target } => Some(target),
        _ => None,
    }
}

// ============================================================================
// Section: what a lowering's outcome must be
// ============================================================================

/// The amount of fuel from which every lowering of this crate has its
/// outcome (LIR's `eval` is fuelled; "not enough fuel" is not a claim). A
/// lowering has no loop, so its depth is bounded by a constant.
pub open spec fn lower_fuel() -> nat {
    128
}

/// What LIR's outcome `o` of a lowering of `op` must be, from the bytecode
/// state `s` (modelling choices 4 to 8):
///
/// - **`Normal`**: the op took its fast path and fell through. The bytecode
///   state is `step(s, op)`, at `pc + 1`, related to LIR's, with the
///   unrepresented parts unchanged and LIR's operand stack empty.
/// - **`Branch(lbl)`**: the op took its fast path and jumped to its target,
///   which is at the label the lowering was given.
/// - **`Exit`**: with the code that names the op's handler and `pc` as the
///   one operand; the frame as it was (`rel(s)`), so the handler's result,
///   `handler(h, s, op)`, is `step(s, op)`.
/// - **Anything else** (`Stuck`, `OutOfFuel`) is false: the lowering is total
///   and never leaves through the bounds check.
pub open spec fn outcome_refines(
    lay: lir::Layout,
    s: js::State,
    op: js::Op,
    lbl: nat,
    o: lir::Outcome,
) -> bool {
    match o {
        lir::Outcome::Normal(st2) => {
            let s2 = js::fast_step(s, op);
            &&& js::fast_path(s, op)
            &&& js::step(s, op) == s2
            &&& s2.pc == s.pc + 1
            &&& st2.stack == Seq::<lir::Val>::empty()
            &&& rel(lay, s2, st2)
            &&& same_unrepresented(s, s2)
        },
        lir::Outcome::Branch(l, st2) => {
            let s2 = js::fast_step(s, op);
            &&& js::fast_path(s, op)
            &&& js::step(s, op) == s2
            &&& l == lbl
            &&& jump_target(op) == Some(s2.pc)
            &&& st2.stack == Seq::<lir::Val>::empty()
            &&& rel(lay, s2, st2)
            &&& same_unrepresented(s, s2)
        },
        lir::Outcome::Exit(c, vals, st2) => {
            &&& c == handler_index(js::op_handler(op))
            &&& vals == seq![lir::Val::I32(s.pc as u32)]
            &&& rel(lay, s, st2)
            &&& js::handler(js::op_handler(op), s, op) == js::step(s, op)
        },
        _ => false,
    }
}

} // verus!
