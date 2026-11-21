//! The instruction set (phase-7.md item 7.4): the op list, each op's class,
//! and the handler an op calls out to.
//!
//! This file is the "op list" of 7.4's commit. The semantics of every op is
//! in [`crate::spec`] (`step`); this file only says what the ops are, which
//! operands they carry, and how the JIT must treat each one.
//!
//! # Core, guarded and handler ops
//!
//! jit.md J.1 requires that "every op that can allocate, call out or throw is
//! a distinguished op, so it maps to an exit". Three classes ([`OpClass`])
//! make that explicit:
//!
//! - **Core** ops never allocate, never call out and never throw, whatever
//!   the machine state. `step` defines them in full. The JIT lowers each one
//!   inline, with no exit.
//! - **Handler** ops always do at least one of those things. `step` defines
//!   them as the uninterpreted `handler(h, s, op)` with `h = op_handler(op)`.
//!   The JIT lowers each one to an exit that calls the same Rust handler the
//!   interpreter calls (phase-7.md 7.8).
//! - **Guarded** ops have a fast path under a stated condition and call a
//!   handler otherwise. `fast_path(s, op)` in [`crate::spec`] is the
//!   condition, `step` is the fast result when it holds and the handler's
//!   result when it does not. The JIT lowers the fast path inline, guards it
//!   by that condition, and exits to the handler on the other branch
//!   (jit.md J.10: "fast paths inline ... everything else is an exit").
//!   Every property get, call and `+` is guarded: whether it allocates or
//!   throws depends on the operands.
//!
//! Operands are `nat`s so that this file needs no encoding decision: `dst`,
//! `src`, `a`, `b` and the other register names are register numbers
//! (register `r` is slot `fp + HDR_SLOTS + r`, arguments first, see
//! `spec::reg_slot`), `k` indexes the function's constant pool, `target` is an
//! op index in the same function, `ic` indexes the function's inline-cache
//! table, and `key` indexes the constant pool for a property name. The
//! binary encoding of ops belongs to the compiler (7.7).
//!
//! # What this list leaves out
//!
//! The op list covers the categories 7.4 names. Language features that 7.7
//! compiles to *more handler ops* (classes, private names, `super`, `with`,
//! `eval`, tagged templates, regular-expression literals, destructuring
//! helpers, spread into array literals, optional-chaining helpers, `delete`
//! of references, `import()`) are added the same way: a new variant here, in
//! class [`OpClass::Handler`], with a new [`HandlerId`]. Nothing in the
//! semantics of the ops below changes when one is added, because a handler op
//! is opaque to `step`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// How the JIT must treat an op (see the file header).
pub enum OpClass {
    /// Never allocates, calls out or throws. Total and defined in full.
    Core,
    /// Fast path under `fast_path`, handler call otherwise.
    Guarded,
    /// Always a handler call.
    Handler,
}

/// The identity of a handler, one per handler function in phase-7.md 7.8.
/// A guarded op's slow path calls the same handler a handler op of the
/// same name would (for example `Add`'s slow path is [`HandlerId::Add`], which
/// does ToPrimitive, string concatenation and BigInt addition, ECMA-262
/// §13.15.3). This is also the exit code the JIT passes (jit.md J.5's
/// `exit(code, operands)`).
pub enum HandlerId {
    /// `+`: §13.15.3 ApplyStringOrNumericBinaryOperator.
    Add,
    /// `-`, §13.15.3.
    Sub,
    /// `*`, §13.15.3.
    Mul,
    /// `/`, §13.15.3.
    Div,
    /// `%`, §13.15.3.
    Mod,
    /// `**`, §13.6.1 and Number::exponentiate §6.1.6.1.3.
    Exp,
    /// Unary `-`, §13.5.5.1.
    Neg,
    /// `++`, §13.4.
    Inc,
    /// `--`, §13.4.
    Dec,
    /// `&`, §13.15.3.
    BitAnd,
    /// `|`, §13.15.3.
    BitOr,
    /// `^`, §13.15.3.
    BitXor,
    /// `<<`, §13.15.3.
    Shl,
    /// `>>`, §13.15.3.
    Shr,
    /// `>>>`, §13.15.3.
    UShr,
    /// `~`, §13.5.6.1.
    BitNot,
    /// `<`, §13.10.1 with IsLessThan §7.2.12.
    Lt,
    /// `<=`, §13.10.1.
    Le,
    /// `>`, §13.10.1.
    Gt,
    /// `>=`, §13.10.1.
    Ge,
    /// `===` and `!==`, IsStrictlyEqual §7.2.14 (string and BigInt contents).
    StrictEq,
    /// `==` and `!=`, IsLooselyEqual §7.2.13.
    LooseEq,
    /// `!`, ToBoolean §7.1.2 (strings, BigInts, IsHTMLDDA).
    Not,
    /// ToNumeric §7.1.3.
    ToNumeric,
    /// ToNumber §7.1.4†, for the operand of unary `+` (§13.5.4.1†).
    ToNumber,
    /// `JumpIfTrue` and `JumpIfFalse`: ToBoolean §7.1.2.
    ToBoolean,
    /// The termination check at a back-edge: ends the evaluation with an
    /// error JS cannot catch (phase-7.md, "Limits and stopping").
    Terminate,
    /// A TDZ read: throws a ReferenceError, §9.1.1.1.6 step 2.
    ThrowHole,
    /// Property get that missed its cache: Get §7.3.2, [[Get]] §10.1.8.
    GetProp,
    /// Property set that missed its cache: Set §7.3.4, [[Set]] §10.1.9.
    SetProp,
    /// Element get off the dense path.
    GetElem,
    /// Element set off the dense path.
    SetElem,
    /// A call that is not a plain call of an ordinary function: Call §7.3.13.
    Call,
    /// A return that is not a plain return, §14.10.1.
    Return,
    /// An environment access that missed.
    EnvAccess,
    /// `typeof`, §13.5.3.1.
    TypeOf,
    /// `instanceof`, §13.10.2 InstanceofOperator.
    InstanceOf,
    /// `in`, §13.10.1 and HasProperty §7.3.11.
    HasProperty,
    /// `delete obj[key]`, §13.5.1.2.
    DeleteProp,
    /// A global variable read, ResolveBinding §9.4.2 and GetValue §6.2.5.5.
    GetGlobal,
    /// A global variable write, PutValue §6.2.5.6.
    SetGlobal,
    /// A global variable read that does not throw for an unresolvable
    /// reference: `typeof`'s step 2.a, §13.5.3.1 (IsUnresolvableReference
    /// §6.2.5.2†), then GetValue §6.2.5.5.
    GetGlobalOrUndefined,
    /// GlobalDeclarationInstantiation, §16.1.7†.
    DeclareGlobals,
    /// CreateDataPropertyOrThrow §7.3.7† with a constant key, for object and
    /// array literals.
    DefineProp,
    /// CreateDataPropertyOrThrow §7.3.7† with a key from a register (after
    /// ToPropertyKey §7.1.19†).
    DefineElem,
    /// The `__proto__: value` of an object literal, §13.2.5.5† step 7:
    /// `[[SetPrototypeOf]]` when the value is an Object or null.
    SetLiteralProto,
    /// Object literal, §13.2.5.
    NewObject,
    /// Array literal, §13.2.4.
    NewArray,
    /// NewDeclarativeEnvironment §9.1.2.2.
    NewEnv,
    /// Function object creation, OrdinaryFunctionCreate §10.2.3.
    NewClosure,
    /// `new`, EvaluateNew §13.3.5.1.1 and [[Construct]] §10.2.2.
    New,
    /// A call with a spread argument list, §13.3.8.1.
    CallSpread,
    /// GetIterator §7.4.4.
    GetIterator,
    /// IteratorNext, IteratorComplete and IteratorValue §7.4.6 to §7.4.8.
    IterNext,
    /// IteratorClose §7.4.11.
    IterClose,
    /// Generator suspend, GeneratorYield §27.5.3.6 and Yield §27.5.3.7.
    Yield,
    /// Async suspend, Await §27.7.5.3.
    Await,
    /// `throw`, §14.14.1.
    Throw,
    /// A throw the compiler knows the kind of, for example assignment to a
    /// constant (a TypeError).
    ThrowError,
    /// ToPropertyKey, §7.1.19†.
    ToPropertyKey,
    /// ToString, §7.1.17†.
    ToString,
    /// CopyDataProperties, §7.3.25†.
    CopyDataProperties,
    /// GetTemplateObject, §13.2.8.4†.
    GetTemplateObject,
    /// `new` with spread arguments, §13.3.5.1.1.
    NewSpread,
    /// SuperCall evaluation, §13.3.7.1†.
    SuperCall,
    /// SuperCall evaluation with spread arguments, §13.3.7.1†.
    SuperCallSpread,
    /// InitializeInstanceElements, §7.3.34†.
    InitInstance,
    /// ClassDefinitionEvaluation, §15.7.14†.
    ClassSetup,
    /// DefineMethodProperty, §15.4.5†.
    DefineMethod,
    /// MakeMethod, §10.2.7†.
    SetHomeObject,
    /// `[[Fields]]` and `[[PrivateMethods]]` of a class, §15.7.14†.
    SetInstanceInit,
    /// NewPrivateEnvironment, §9.2.1.1†.
    NewPrivateName,
    /// PrivateGet, §7.3.31†.
    GetPrivate,
    /// PrivateSet, §7.3.32†.
    SetPrivate,
    /// PrivateFieldAdd and PrivateMethodOrAccessorAdd, §7.3.30†.
    DefinePrivate,
    /// `#x in obj`, §13.10.1†.
    HasPrivate,
    /// GetSuperBase, §9.1.1.3.5†.
    GetSuperBase,
    /// Super property read, GetValue §6.2.5.5†.
    GetSuper,
    /// Super property write, PutValue §6.2.5.6†.
    SetSuper,
    /// GetNewTarget, §9.4.4†.
    GetNewTarget,
    /// The result of a derived constructor, §10.2.2† steps 10 to 12.
    ConstructResult,
    /// CreateUnmappedArgumentsObject, §10.4.4.6†.
    CreateUnmappedArguments,
    /// CreateMappedArgumentsObject, §10.4.4.7†.
    CreateMappedArguments,
    /// The array of a rest parameter, §10.2.11† step 24.
    CreateRestArray,
    /// EnumerateObjectProperties, §14.7.5.9†.
    ForInIterator,
    /// InitializeBinding on the global declarative record, §9.1.1.4.2†.
    InitGlobalLexical,
    /// RegExpCreate §22.2.3.1†, for a regular expression literal (§13.2.7.3†).
    NewRegExp,
}

/// The error constructors a compiler-known throw can name.
pub enum ErrorKind {
    /// `TypeError`.
    TypeError,
    /// `ReferenceError`.
    ReferenceError,
    /// `SyntaxError`.
    SyntaxError,
    /// `RangeError`.
    RangeError,
}

/// One instruction. Field names are the operand roles named in the file
/// header; `dst` is always written, `src`, `a`, `b`, `obj`, `idx`, `val`,
/// `cond`, `callee`, `this`, `env` are read.
pub enum Op {
    // ---------------------------------------------------------------
    // Core: never allocate, call out or throw.
    // ---------------------------------------------------------------
    /// Does nothing.
    Nop,
    /// `dst := src`. Register moves.
    Move {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := consts[k]`. A constant of the function's pool: a double, an
    /// int32, a special, or a heap reference to an interned string, a
    /// BigInt or a function template (the pool is a root, phase-7.md 7.6).
    LoadConst {
        /// The register written.
        dst: nat,
        /// The constant-pool index.
        k: nat,
    },
    /// `dst := imm` as an int32.
    LoadInt {
        /// The register written.
        dst: nat,
        /// The immediate int32.
        imm: i32,
    },
    /// `dst := undefined`.
    LoadUndefined {
        /// The register written.
        dst: nat,
    },
    /// `dst := null`.
    LoadNull {
        /// The register written.
        dst: nat,
    },
    /// `dst := true` or `false`.
    LoadBool {
        /// The register written.
        dst: nat,
        /// The boolean loaded.
        flag: bool,
    },
    /// `dst := hole`, the uninitialized-binding marker of the temporal dead
    /// zone (§9.1.1.1.6) and of array holes. Never visible to JS.
    LoadHole {
        /// The register written.
        dst: nat,
    },
    /// `dst := this`, the frame header's `this` slot.
    GetThis {
        /// The register written.
        dst: nat,
    },
    /// `dst := callee`, the frame header's callee slot (`new.target`-free;
    /// the function itself, for named function expressions).
    GetCallee {
        /// The register written.
        dst: nat,
    },
    /// `dst := argc` as an int32, from the frame header.
    GetArgc {
        /// The register written.
        dst: nat,
    },
    /// `dst := exception`: delivers the thrown value at a catch handler
    /// (§14.15.2 Catch clause, step "Let thrownValue be ..."), after
    /// unwinding (a handler's job) has stored it.
    GetException {
        /// The register written.
        dst: nat,
    },
    /// `pc := target`. Forward jumps and the loop-exit edge.
    Jump {
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target` if `src` is `undefined`, else the next op.
    JumpIfUndefined {
        /// The register read.
        src: nat,
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target` if `src` is not `undefined`.
    JumpIfNotUndefined {
        /// The register read.
        src: nat,
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target` if `src` is `undefined` or `null` (`??`, `?.`).
    JumpIfNullish {
        /// The register read.
        src: nat,
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target` if `src` is neither `undefined` nor `null`.
    JumpIfNotNullish {
        /// The register read.
        src: nat,
        /// The op index jumped to.
        target: nat,
    },

    // ---------------------------------------------------------------
    // Guarded: fast path when `fast_path` holds, else a handler.
    // ---------------------------------------------------------------
    /// `dst := a + b` on Numbers. Number::add, §6.1.6.1.7.
    Add {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a - b` on Numbers. Number::subtract, §6.1.6.1.8.
    Sub {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a * b` on Numbers. Number::multiply, §6.1.6.1.4.
    Mul {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a / b` on Numbers. Number::divide, §6.1.6.1.5.
    Div {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a % b` on Numbers. Number::remainder, §6.1.6.1.6.
    Mod {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := -src` on a Number. Number::unaryMinus, §6.1.6.1.1.
    Neg {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := src + 1` on a Number (the numeric part of `++`, §13.4.2.1).
    Inc {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := src - 1` on a Number (the numeric part of `--`, §13.4.3.1).
    Dec {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := a & b` on Numbers. Number::bitwiseAND, §6.1.6.1.17.
    BitAnd {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a | b` on Numbers. Number::bitwiseOR, §6.1.6.1.19.
    BitOr {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a ^ b` on Numbers. Number::bitwiseXOR, §6.1.6.1.18.
    BitXor {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a << b` on Numbers. Number::leftShift, §6.1.6.1.9.
    Shl {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a >> b` on Numbers. Number::signedRightShift, §6.1.6.1.10.
    Shr {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a >>> b` on Numbers. Number::unsignedRightShift, §6.1.6.1.11.
    UShr {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := ~src` on a Number. Number::bitwiseNOT, §6.1.6.1.2.
    BitNot {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := a < b` on Numbers, §13.10.1 with Number::lessThan §6.1.6.1.12.
    Lt {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a <= b` on Numbers, §13.10.1.
    Le {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a > b` on Numbers, §13.10.1.
    Gt {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a >= b` on Numbers, §13.10.1.
    Ge {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a === b`, IsStrictlyEqual §7.2.14, §13.11.1.
    StrictEq {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a !== b`, §13.11.1.
    StrictNe {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := !src`, ToBoolean §7.1.2, §13.5.7.1.
    Not {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := ToNumeric(src)`, §7.1.3, on a Number (the identity).
    ToNumeric {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := ToNumber(src)`, §7.1.4†, on a Number (the identity, step 1).
    /// Unlike [`Op::ToNumeric`], a BigInt is a TypeError (step 3), so this is
    /// the op of unary `+` (§13.5.4.1†: "Return ? ToNumber(? GetValue(expr))").
    /// A Symbol is a TypeError (step 2); an Object goes through ToPrimitive
    /// (steps 9 and 10). Everything but a Number is the handler's.
    ToNumber {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `pc := target` if ToBoolean(`cond`), §14.6.2.
    JumpIfTrue {
        /// The register tested.
        cond: nat,
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target` if not ToBoolean(`cond`), §14.6.2.
    JumpIfFalse {
        /// The register tested.
        cond: nat,
        /// The op index jumped to.
        target: nat,
    },
    /// `pc := target`, a loop back-edge. The termination flag is checked
    /// here (phase-7.md, "Limits and stopping"), and the interpreter and the
    /// JIT count back-edges here for tiering (7.8, jit.md J.10); neither
    /// count is observable, so neither is in the state.
    Loop {
        /// The op index jumped to.
        target: nat,
    },
    /// Throws a ReferenceError if `src` is the hole, else the next op: the
    /// TDZ check (§9.1.1.1.6 GetBindingValue step 2, §9.1.1.1.5
    /// SetMutableBinding step 3).
    ThrowIfHole {
        /// The register read.
        src: nat,
    },
    /// `dst := obj.key`, with an inline cache: Get §7.3.2 specialised to an
    /// own data property found by shape.
    GetProp {
        /// The register written.
        dst: nat,
        /// The register holding the object.
        obj: nat,
        /// The constant-pool index of the property name.
        key: nat,
        /// The inline-cache index.
        ic: nat,
    },
    /// `obj.key := val`, with an inline cache: Set §7.3.4 specialised to an
    /// existing own writable data property found by shape.
    SetProp {
        /// The register holding the object.
        obj: nat,
        /// The constant-pool index of the property name.
        key: nat,
        /// The register holding the value stored.
        val: nat,
        /// The inline-cache index.
        ic: nat,
    },
    /// `dst := obj[idx]` on a dense element.
    GetElem {
        /// The register written.
        dst: nat,
        /// The register holding the object.
        obj: nat,
        /// The register (or slot index, for environment ops) of the element.
        idx: nat,
    },
    /// `obj[idx] := val` on a dense element that exists.
    SetElem {
        /// The register holding the object.
        obj: nat,
        /// The register (or slot index, for environment ops) of the element.
        idx: nat,
        /// The register holding the value stored.
        val: nat,
    },
    /// `dst := callee(args[0..argc])` with `this`. The caller lays the
    /// arguments in `argc` consecutive registers from `args`. Call §7.3.13,
    /// [[Call]] §10.2.1, EvaluateCall §13.3.6.2.
    Call {
        /// The register written.
        dst: nat,
        /// The register holding the function.
        callee: nat,
        /// The register holding `this`.
        this: nat,
        /// The first of the consecutive argument registers (or the array register).
        args: nat,
        /// The number of arguments.
        argc: nat,
    },
    /// `return src` from the current frame. §14.10.1, [[Call]] §10.2.1
    /// step 7 ("If result is a return completion, return result.[[Value]]").
    Return {
        /// The register read.
        src: nat,
    },
    /// `dst := env.slots[idx]`: a captured variable, GetBindingValue
    /// §9.1.1.1.6 on a declarative environment.
    GetEnvSlot {
        /// The register written.
        dst: nat,
        /// The register holding the environment.
        env: nat,
        /// The register (or slot index, for environment ops) of the element.
        idx: nat,
    },
    /// `env.slots[idx] := src`, SetMutableBinding §9.1.1.1.5.
    SetEnvSlot {
        /// The register holding the environment.
        env: nat,
        /// The register (or slot index, for environment ops) of the element.
        idx: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := env.parent`: one hop of the scope chain, the outer environment
    /// of §9.1.2.1 GetIdentifierReference step 3.
    GetEnvParent {
        /// The register written.
        dst: nat,
        /// The register holding the environment.
        env: nat,
    },
    /// `dst := callee.env`: the environment the running closure captured
    /// (OrdinaryFunctionCreate §10.2.3, [[Environment]]).
    GetCalleeEnv {
        /// The register written.
        dst: nat,
    },

    // ---------------------------------------------------------------
    // Handler: always a handler call.
    // ---------------------------------------------------------------
    /// `dst := a ** b`, §13.6.1.
    Exp {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a == b`, §13.11.1.
    LooseEq {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a != b`, §13.11.1.
    LooseNe {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := typeof src`, §13.5.3.1.
    TypeOf {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := a instanceof b`, §13.10.2.
    InstanceOf {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := a in b`, §13.10.1.
    HasProperty {
        /// The register written.
        dst: nat,
        /// The left operand register.
        a: nat,
        /// The right operand register.
        b: nat,
    },
    /// `dst := delete obj[idx]`, §13.5.1.2.
    DeleteProp {
        /// The register written.
        dst: nat,
        /// The register holding the object.
        obj: nat,
        /// The register (or slot index, for environment ops) of the element.
        idx: nat,
    },
    /// `dst := global.key`, with an inline cache (the handler may install it).
    GetGlobal {
        /// The register written.
        dst: nat,
        /// The constant-pool index of the property name.
        key: nat,
        /// The inline-cache index.
        ic: nat,
    },
    /// `global.key := src`.
    SetGlobal {
        /// The constant-pool index of the property name.
        key: nat,
        /// The register read.
        src: nat,
        /// The inline-cache index.
        ic: nat,
    },
    /// `dst := {}`.
    NewObject {
        /// The register written.
        dst: nat,
    },
    /// `dst := []` with room for `len` elements.
    NewArray {
        /// The register written.
        dst: nat,
        /// The element capacity.
        len: nat,
    },
    /// `dst := global.key`, or `undefined` when `key` is an unresolvable
    /// reference: the operand evaluation of `typeof identifier`, §13.5.3.1
    /// (Runtime Semantics: Evaluation, UnaryExpression : `typeof`
    /// UnaryExpression) step 2.a, "If IsUnresolvableReference(val) is true,
    /// return "undefined"" (IsUnresolvableReference §6.2.5.2†), else step 3,
    /// "Set val to ? GetValue(val)" (§6.2.5.5, so a getter, a Proxy trap or a
    /// binding in its temporal dead zone still throws). Feeding the result to
    /// [`Op::TypeOf`] is then the standard's `typeof`, because `typeof
    /// undefined` is the same string whether the reference is unresolvable or
    /// resolves to `undefined`. Unlike [`Op::GetGlobal`] it does not throw a
    /// ReferenceError (§6.2.5.5 step 3) for an unresolvable reference.
    GetGlobalOrUndefined {
        /// The register written.
        dst: nat,
        /// The constant-pool index of the name.
        key: nat,
    },
    /// GlobalDeclarationInstantiation(script, env), §16.1.7†, run once on
    /// entry to a script, as the first op of its function (ScriptEvaluation
    /// §16.1.6†, step 11 "Let result be Completion(GlobalDeclarationInstantiation
    /// (script, globalEnv))" comes before the evaluation of the script's
    /// statements in step 12). `consts[k]` is a heap reference to the script's
    /// declaration record, built by the loader from what the compiler lists:
    /// the LexicallyScopedDeclarations (each bound name, constant or not,
    /// §16.1.7† step 13), the VarScopedDeclarations in source order (each a
    /// variable's name, or a function's name and function template, step 5),
    /// and the names Annex B.3.2.2† adds at step 12 (functions in blocks).
    /// The handler is steps 1 to 18: the SyntaxError and TypeError checks of
    /// steps 3, 4, 8 and 10 (HasVarDeclaration §9.1.1.4.12†, HasLexicalDeclaration
    /// §9.1.1.4.13†, HasRestrictedGlobalProperty §9.1.1.4.14†, CanDeclareGlobalVar
    /// §9.1.1.4.15†, CanDeclareGlobalFunction §9.1.1.4.16†), all before any
    /// binding is created, then the lexical bindings (step 15), the function
    /// objects (step 16, InstantiateFunctionObject over the global
    /// environment, CreateGlobalFunctionBinding §9.1.1.4.18†) and the
    /// variables (step 17, CreateGlobalVarBinding §9.1.1.4.17†).
    DeclareGlobals {
        /// The constant-pool index of the declaration record.
        k: nat,
    },
    /// `CreateDataPropertyOrThrow(obj, consts[key], val)`, §7.3.7† (step 1
    /// CreateDataProperty §7.3.5†, which defines the own property with
    /// `[[Writable]]`, `[[Enumerable]]` and `[[Configurable]]` all true by
    /// `obj.[[DefineOwnProperty]]`; step 2 throws a TypeError if that fails).
    /// It is not `Set` (§7.3.4): it never reads the prototype chain, so a
    /// setter or a read-only property inherited from it is not seen. Emitted
    /// for each property of an object literal, §13.2.5.5† step 9, "Perform !
    /// CreateDataPropertyOrThrow(object, propKey, propValue)", and for each
    /// element of an array literal, §13.2.4.1† ArrayAccumulation. The key is
    /// a property name constant, a string or a canonical numeric string.
    DefineProp {
        /// The register holding the object.
        obj: nat,
        /// The constant-pool index of the property name.
        key: nat,
        /// The register holding the value stored.
        val: nat,
    },
    /// As [`Op::DefineProp`], with the key in register `idx`, converted by
    /// ToPropertyKey §7.1.19† when the op runs: a computed property name
    /// (§13.2.5.4†) and an array literal's index. An element that is the hole
    /// (an elision) is the handler's to leave absent. An object key whose
    /// conversion has side effects is converted when this op runs, which is
    /// after the value expression, where the standard converts it first; the
    /// op list has no ToPropertyKey op yet, and `SetElem` had the same gap.
    DefineElem {
        /// The register holding the object.
        obj: nat,
        /// The register holding the key.
        idx: nat,
        /// The register holding the value stored.
        val: nat,
    },
    /// The `__proto__: val` form of an object literal, §13.2.5.5† steps 3
    /// and 7: "If propValue is an Object or propValue is null, then Perform !
    /// object.[[SetPrototypeOf]](propValue)", and nothing otherwise, never a
    /// property definition. `obj` is the literal's fresh ordinary object, so
    /// the call cannot fail.
    SetLiteralProto {
        /// The register holding the object.
        obj: nat,
        /// The register holding the value.
        val: nat,
    },
    /// `dst := new environment` with `size` slots (all holes) and `parent`.
    NewEnv {
        /// The register written.
        dst: nat,
        /// The register holding the parent environment.
        parent: nat,
        /// The number of slots.
        size: nat,
    },
    /// `dst := closure of function template `func` over `env``.
    NewClosure {
        /// The register written.
        dst: nat,
        /// The index of the function template.
        func: nat,
        /// The register holding the environment.
        env: nat,
    },
    /// `dst := new callee(args[0..argc])`.
    New {
        /// The register written.
        dst: nat,
        /// The register holding the function.
        callee: nat,
        /// The first of the consecutive argument registers (or the array register).
        args: nat,
        /// The number of arguments.
        argc: nat,
    },
    /// `dst := callee.apply(this, array in args)` for `f(...xs)`.
    CallSpread {
        /// The register written.
        dst: nat,
        /// The register holding the function.
        callee: nat,
        /// The register holding `this`.
        this: nat,
        /// The first of the consecutive argument registers (or the array register).
        args: nat,
    },
    /// `dst := GetIterator(src)`.
    GetIterator {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `value := iterator.next()`; `done := whether it was done`.
    IterNext {
        /// The register receiving the value.
        value: nat,
        /// The register receiving the done flag.
        done: nat,
        /// The register holding the iterator record.
        iter: nat,
    },
    /// `IteratorClose(iter)`.
    IterClose {
        /// The register holding the iterator record.
        iter: nat,
    },
    /// Suspends the running generator, giving `src` to its consumer. On
    /// resume, `value` receives the sent value and `mode` an int32: 0 next,
    /// 1 throw, 2 return (the compiler follows with `Jump`s on it).
    Yield {
        /// The register read.
        src: nat,
        /// The register receiving the value.
        value: nat,
        /// The register receiving the resume mode.
        mode: nat,
    },
    /// As `Yield`, for `await`.
    Await {
        /// The register read.
        src: nat,
        /// The register receiving the value.
        value: nat,
        /// The register receiving the resume mode.
        mode: nat,
    },
    /// `throw src`.
    Throw {
        /// The register read.
        src: nat,
    },
    /// Throws a new error of `kind` with message `consts[msg]`.
    ThrowError {
        /// The error constructor.
        kind: ErrorKind,
        /// The constant-pool index of the message.
        msg: nat,
    },
    /// `dst := ToPropertyKey(src)`, §7.1.19†: ToPrimitive with hint string (step 1), then a Symbol
    /// is itself (step 2) and anything else is ToString (step 3). It may call user code and throw,
    /// so it is always a handler call. It is emitted for a computed property name of an object
    /// literal or a class element (ComputedPropertyName evaluation, §13.2.5.4†: "Return ?
    /// ToPropertyKey(propName)"), whose key must be converted when the name is evaluated, before
    /// the value expression, which [`Op::DefineElem`] alone cannot do. The result is a string or a
    /// Symbol, so converting it again (by `DefineElem`, `GetElem` or `HasProperty`) has no effect.
    ToPropertyKey {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := ToString(src)`, §7.1.17†: a Symbol is a TypeError (step 1), an Object goes through
    /// ToPrimitive with hint string (step 10). It is the conversion of each substitution of a
    /// template literal (§13.2.8.6†, TemplateLiteral : TemplateHead Expression TemplateSpans, "Let
    /// sub be ? ToString(subValue)"), which `+` (ToPrimitive with hint default) must not stand in
    /// for.
    ToString {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// `CopyDataProperties(obj, src, excluded)`, §7.3.25†, where `excluded` is the `nexcl` property
    /// keys (already converted by ToPropertyKey, so strings and Symbols) in consecutive registers
    /// from `excl`: if `src` is `undefined` or `null` nothing is copied (step 2); otherwise `from`
    /// is ToObject(`src`) and each own key that is not excluded and whose descriptor is enumerable
    /// is copied with Get and CreateDataPropertyOrThrow (step 4). It is the object spread of an
    /// object literal (§13.2.5.5† PropertyDefinition : `...` AssignmentExpression, with no excluded
    /// keys) and the rest property of an object pattern (§13.15.5.3†, §14.3.3.2†
    /// RestBindingInitialization, with the keys of the pattern's other properties).
    CopyDataProperties {
        /// The register holding the target object.
        obj: nat,
        /// The register holding the source value.
        src: nat,
        /// The first of the registers holding the excluded property keys.
        excl: nat,
        /// The number of excluded property keys.
        nexcl: nat,
    },
    /// `dst := GetTemplateObject(site)`, §13.2.8.4†, where `consts[k]` is a heap reference to the
    /// record of the template literal at this site, built by the loader from what the compiler
    /// lists: the cooked strings (a string, or `undefined` for a malformed escape in a tagged
    /// template) and the raw strings of each TemplateString (TemplateStrings, §13.2.8.3†). The
    /// handler looks the site up in the realm's `[[TemplateMap]]` (steps 1 and 2: the same site
    /// gives the same object, whatever the call), and otherwise creates the frozen array of cooked
    /// strings with its frozen `raw` array (steps 3 to 14) and records it.
    GetTemplateObject {
        /// The register written.
        dst: nat,
        /// The constant-pool index of the template record.
        k: nat,
    },
    /// `dst := new callee(...array in args)`: as [`Op::New`] where the arguments are the elements
    /// of the array in register `args`, which the compiler built from the argument list with its
    /// spread elements already iterated (ArgumentListEvaluation, §13.3.8.1†). EvaluateNew
    /// §13.3.5.1.1 steps 5 and 6 (IsConstructor, then Construct).
    NewSpread {
        /// The register written.
        dst: nat,
        /// The register holding the function.
        callee: nat,
        /// The register holding the array of arguments.
        args: nat,
    },
    /// `dst := super(args[0..argc])`, §13.3.7.1† (Runtime Semantics: Evaluation, SuperCall :
    /// `super` Arguments): `func` is the active function (GetSuperConstructor, §13.3.7.2†:
    /// `func.[[GetPrototypeOf]]()`, step 5), which must be a constructor (step 6, else a
    /// TypeError); the result is Construct(superConstructor, args, `newtarget`) (step 7). `this` is
    /// the register of the `this` binding: if it is not the hole the binding is already initialized
    /// and the handler throws a ReferenceError (BindThisValue, §9.1.1.3.1†, step 1), after the
    /// construction, as the standard does. It does not store the result: the compiler stores `dst`
    /// into the `this` binding and follows with [`Op::InitInstance`] (steps 9 and 10).
    SuperCall {
        /// The register written.
        dst: nat,
        /// The register holding the active function.
        func: nat,
        /// The register holding `new.target`.
        newtarget: nat,
        /// The register holding the current `this` binding (the hole until `super()` returns).
        this: nat,
        /// The first of the argument registers.
        args: nat,
        /// The number of arguments.
        argc: nat,
    },
    /// As [`Op::SuperCall`], with the arguments the elements of the array in register `args`
    /// (ArgumentListEvaluation, §13.3.8.1†, with the spread elements already iterated by the
    /// compiler's code).
    SuperCallSpread {
        /// The register written.
        dst: nat,
        /// The register holding the active function.
        func: nat,
        /// The register holding `new.target`.
        newtarget: nat,
        /// The register holding the current `this` binding.
        this: nat,
        /// The register holding the array of arguments.
        args: nat,
    },
    /// `InitializeInstanceElements(obj, func)`, §7.3.34†: runs the instance initializer that
    /// [`Op::SetInstanceInit`] stored on the class constructor `func`, if any, with `this` = `obj`:
    /// it adds the class's private methods and accessors to `obj` (steps 2 and 3,
    /// PrivateMethodOrAccessorAdd) and defines its fields (steps 4 and 5, DefineField), in order.
    /// It runs at the start of a base class constructor (§10.2.2† [[Construct]] step 6.b) and after
    /// `super()` returns in a derived one (§13.3.7.1† step 10).
    InitInstance {
        /// The register holding the new object.
        obj: nat,
        /// The register holding the constructor.
        func: nat,
    },
    /// ClassDefinitionEvaluation §15.7.14†, steps 5 to 14 and 16 to 17, and MakeClassConstructor
    /// §10.2.5†, on the closure in `ctor` (a [`crate::bytecode::FunctionKind::Class`] or `Derived`
    /// function template): if `derived` is false, protoParent is %Object.prototype% and
    /// constructorParent %Function.prototype% (step 5); otherwise `heritage` is the value of the
    /// ClassHeritage: `null` gives a null protoParent and %Function.prototype% (step 8.a), a
    /// non-constructor is a TypeError (step 8.d), else protoParent is its `prototype` property,
    /// which must be an Object or null (a TypeError otherwise, steps 8.f to 8.h), and
    /// constructorParent is the value itself. Then `proto` := OrdinaryObjectCreate(protoParent)
    /// (step 9) is written to `proto`, `ctor.[[Prototype]]` is set to constructorParent (step
    /// 14.a), the closure becomes a class constructor of the kind base or derived
    /// (MakeClassConstructor, step 14), `prototype` is defined on it, non-writable, non-enumerable
    /// and non-configurable (MakeConstructor with writablePrototype false, step 16), its home
    /// object is `proto` (MakeMethod, step 15) and `proto.constructor` is `ctor`, non-enumerable
    /// (CreateMethodProperty, step 17).
    ClassSetup {
        /// The register holding the constructor closure.
        ctor: nat,
        /// The register written with the class's prototype object.
        proto: nat,
        /// The register holding the value of the `extends` clause.
        heritage: nat,
        /// Whether the class has an `extends` clause.
        derived: bool,
    },
    /// DefineMethodProperty(`obj`, `key`, `func`, `enumerable`), §15.4.5†, for `form` 0, and the
    /// getter and setter forms of MethodDefinition evaluation (§15.4.5†,
    /// PropertyDefinitionEvaluation of `get` and `set`) for `form` 1 and 2: SetFunctionName(`func`,
    /// `key`, prefix) with the prefix `"get"` or `"set"` for the accessors (§10.2.9†), then
    /// DefinePropertyOrThrow of a data property for a method (writable, configurable, enumerable as
    /// given) or of an accessor property whose `[[Get]]` or `[[Set]]` is `func` and whose other
    /// half is kept if there is one (configurable, enumerable as given). `key` is already converted
    /// (ToPropertyKey, a string or a Symbol). An object literal's methods are enumerable, a class's
    /// are not (ClassElementEvaluation, §15.7.10†).
    DefineMethod {
        /// The register holding the object.
        obj: nat,
        /// The register holding the property key.
        key: nat,
        /// The register holding the method closure.
        func: nat,
        /// 0 method, 1 getter, 2 setter.
        form: nat,
        /// Whether the property is enumerable.
        enumerable: bool,
    },
    /// MakeMethod(`func`, `obj`), §10.2.7†: sets `func.[[HomeObject]]` to `obj`, which `super.x`
    /// reads ([`Op::GetSuperBase`]). Emitted for each method, accessor and initializer function of
    /// a class or object literal that is a method (§15.4.5† step 2, §15.7.10†).
    SetHomeObject {
        /// The register holding the function.
        func: nat,
        /// The register holding the home object.
        obj: nat,
    },
    /// Stores the closure `init` as the instance initializer of class constructor `ctor`
    /// (ClassDefinitionEvaluation §15.7.14† steps 31 and 32, `F.[[PrivateMethods]]` and
    /// `F.[[Fields]]`): `init` is a method (its home object the class's prototype) whose body adds
    /// the class's private instance methods and defines its instance fields, in order, on `this`;
    /// [`Op::InitInstance`] calls it.
    SetInstanceInit {
        /// The register holding the class constructor.
        ctor: nat,
        /// The register holding the initializer closure.
        init: nat,
    },
    /// `dst := a new Private Name` with description `consts[k]` (a string, `"#x"`), §6.2.12†: one
    /// per private identifier declared by a class, created each time the class is evaluated
    /// (ClassDefinitionEvaluation §15.7.14† step 6, NewPrivateEnvironment §9.2.1.1†). The value is
    /// an opaque heap reference, only ever an operand of the private-name ops.
    NewPrivateName {
        /// The register written.
        dst: nat,
        /// The constant-pool index of the description.
        k: nat,
    },
    /// `dst := obj.#name`: PrivateGet(`obj`, `name`), §7.3.31† (a primitive `obj` is a TypeError,
    /// as is an `obj` without the element, §13.3.2.1†; a field, method or accessor is read as the
    /// element's kind says).
    GetPrivate {
        /// The register written.
        dst: nat,
        /// The register holding the object.
        obj: nat,
        /// The register holding the Private Name.
        name: nat,
    },
    /// `obj.#name := val`: PrivateSet(`obj`, `name`, `val`), §7.3.32† (a TypeError for an `obj`
    /// without the element, for a method, and for an accessor without a setter).
    SetPrivate {
        /// The register holding the object.
        obj: nat,
        /// The register holding the Private Name.
        name: nat,
        /// The register holding the value stored.
        val: nat,
    },
    /// Adds a private element to `obj`: PrivateFieldAdd(`obj`, `name`, `val`) §7.3.30† for `form`
    /// 0, and PrivateMethodOrAccessorAdd §7.3.31† for the others (`val` is the function; a getter
    /// and a setter of the same name make one accessor element), which throw a TypeError if `obj`
    /// already has an element of that name (the double initialization of a return-override trick).
    /// SetFunctionName gives a method its name `"#x"` (and `"get #x"`, `"set #x"`), §10.2.9†.
    DefinePrivate {
        /// The register holding the object.
        obj: nat,
        /// The register holding the Private Name.
        name: nat,
        /// The register holding the value or function.
        val: nat,
        /// 0 field, 1 method, 2 getter, 3 setter.
        form: nat,
    },
    /// `dst := #name in obj`, §13.10.1† (RelationalExpression : PrivateIdentifier `in`
    /// ShiftExpression, step 5: a non-Object `obj` is a TypeError, then PrivateElementFind).
    HasPrivate {
        /// The register written.
        dst: nat,
        /// The register holding the Private Name.
        name: nat,
        /// The register holding the object.
        obj: nat,
    },
    /// `dst := GetSuperBase()`, §9.1.1.3.5† (GetSuperBase of a function Environment Record):
    /// `func.[[HomeObject]].[[GetPrototypeOf]]()`, the object `super.x` looks up properties on.
    /// Emitted for `super.x` and `super[x]` (§13.3.7.1†, SuperProperty evaluation:
    /// MakeSuperPropertyReference, §13.3.7.3†), after the `this` binding is read.
    GetSuperBase {
        /// The register written.
        dst: nat,
        /// The register holding the method whose home object is read.
        func: nat,
    },
    /// `dst := base.[[Get]](key, this)`: GetValue of a super reference (§6.2.5.5† step 3.b: the
    /// reference's base value is `base`, the receiver is `this`). `key` is converted by
    /// ToPropertyKey by this op (§13.3.7.3†: for `super[x]` the conversion is delayed, as in
    /// §13.3.3†); a null base is a TypeError (ToObject, step 3.a).
    GetSuper {
        /// The register written.
        dst: nat,
        /// The register holding the super base.
        base: nat,
        /// The register holding the property key.
        key: nat,
        /// The register holding the receiver.
        this: nat,
    },
    /// `base.[[Set]](key, val, this)`: PutValue of a super reference (§6.2.5.6† steps 5.b to 5.d),
    /// with the receiver `this`, which throws a TypeError if the set returns false in strict mode
    /// code (the strictness of the function).
    SetSuper {
        /// The register holding the super base.
        base: nat,
        /// The register holding the property key.
        key: nat,
        /// The register holding the value stored.
        val: nat,
        /// The register holding the receiver.
        this: nat,
    },
    /// `dst := new.target` of the running function: GetNewTarget §9.4.4† (the frame's
    /// `[[NewTarget]]`: `undefined` unless the function was called by [[Construct]]), §13.3.12.1†
    /// (MetaProperty : `new` `.` `target`).
    GetNewTarget {
        /// The register written.
        dst: nat,
    },
    /// `dst :=` the result of returning `val` from a derived class constructor (§10.2.2†
    /// [[Construct]] steps 10 to 12 with a derived kind): an Object `val` is the result; otherwise
    /// a `val` that is not `undefined` is a TypeError (step 10.b); otherwise the `this` binding
    /// (`this` is the hole if `super()` has not returned: a ReferenceError, step 12, GetThisBinding
    /// §9.1.1.3.4†). The compiler emits it before every `Return` of a derived constructor; the
    /// result of the call is then used as it is.
    ConstructResult {
        /// The register written.
        dst: nat,
        /// The register holding the returned value.
        val: nat,
        /// The register holding the `this` binding.
        this: nat,
    },
    /// `dst := CreateUnmappedArgumentsObject(argumentsList)`, §10.4.4.6†
    /// (FunctionDeclarationInstantiation §10.2.11† step 22.b.i): the `arguments` object of a strict
    /// function or of one with a non-simple parameter list, from the frame's actual arguments.
    CreateUnmappedArguments {
        /// The register written.
        dst: nat,
    },
    /// `dst := CreateMappedArgumentsObject(func, formals, argumentsList, env)`, §10.4.4.7†
    /// (FunctionDeclarationInstantiation §10.2.11† step 22.b.ii): the exotic `arguments` object of
    /// a sloppy function with a simple parameter list, whose indices alias the parameters'
    /// bindings. `env` is the environment object that holds them (the compiler puts every parameter
    /// in it), and `consts[k]` is a heap reference to the map record the loader builds from what
    /// the compiler lists: for each formal parameter, the slot of `env` it is bound to, or none for
    /// a parameter name that a later one repeats (§10.4.4.7† steps 16 to 20).
    CreateMappedArguments {
        /// The register written.
        dst: nat,
        /// The register holding the environment object that holds the parameters.
        env: nat,
        /// The constant-pool index of the parameter map record.
        k: nat,
    },
    /// `dst := CreateArrayFromList(argumentsList[from..])`: the value of a rest parameter
    /// (§10.2.11† FunctionDeclarationInstantiation step 24 and IteratorBindingInitialization of a
    /// FunctionRestParameter, §15.1.4†), an array of the actual arguments from index `from` on,
    /// empty if there are fewer.
    CreateRestArray {
        /// The register written.
        dst: nat,
        /// The index of the first argument in the array.
        from: nat,
    },
    /// `dst := the for-in iterator of src`: ForIn/OfHeadEvaluation with `enumerate` (§14.7.5.6†)
    /// calls EnumerateObjectProperties(ToObject(`src`)) (§14.7.5.9†), or gives an iterator that is
    /// done at once if `src` is `undefined` or `null` (step 6.a of ForIn/OfHeadEvaluation: a
    /// `break` completion). The result is an iterator record for [`Op::IterNext`], over the
    /// enumerable string keys of the object and its prototype chain, each key once and only while
    /// it is still a property when reached; it is never closed.
    ForInIterator {
        /// The register written.
        dst: nat,
        /// The register read.
        src: nat,
    },
    /// InitializeBinding(`consts[key]`, `src`) on the global Environment Record (§9.1.1.4.2†
    /// InitializeBinding step 2: "If DclRec.HasBinding(N) is true, return !
    /// DclRec.InitializeBinding(N, V)"), whose [[DeclarativeRecord]] holds the binding that
    /// [`Op::DeclareGlobals`] created, uninitialized (GlobalDeclarationInstantiation §16.1.7† step
    /// 15: CreateMutableBinding or CreateImmutableBinding). It is the evaluation of a top-level
    /// `let`, `const` or `class` declaration (§14.3.1.2† LexicalBinding evaluation, "Perform !
    /// InitializeReferencedBinding(lhs, value)", §15.7.15†). Reads and writes of the binding are
    /// [`Op::GetGlobal`] and [`Op::SetGlobal`], which resolve a name in the declarative record
    /// before the global object (ResolveBinding §9.4.2†, GetIdentifierReference §9.1.2.1) and so
    /// throw a ReferenceError for the uninitialized binding (GetBindingValue §9.1.1.1.6† step 2)
    /// and a TypeError for a `const` (SetMutableBinding §9.1.1.1.5† step 5).
    InitGlobalLexical {
        /// The constant-pool index of the name.
        key: nat,
        /// The register read.
        src: nat,
    },
    /// `dst := RegExpCreate(pattern, flags)` for the literal whose record is `consts[k]` (its
    /// pattern source text and its flags). RegularExpressionLiteral evaluation (§13.2.7.3†): "Let
    /// pattern be CodePointsAsString of the BodyText" (step 1), "Let flags be CodePointsAsString of
    /// the FlagText" (step 2), "Return ! RegExpCreate(pattern, flags)" (step 3). Every evaluation
    /// creates a new RegExp object, so a literal in a loop gives a new object each time and the
    /// record is shared. The `!` is the parser's early error (§13.2.7.2†: the body is a valid
    /// Pattern for the flags and the flags are valid), so the handler never sees a pattern it
    /// cannot compile; this crate does not compile the pattern, the regular expression engine does,
    /// when the heap loads the record. It allocates, so it is always a handler call.
    NewRegExp {
        /// The register written.
        dst: nat,
        /// The constant-pool index of the literal's record (pattern text and flags).
        k: nat,
    },
}

/// The class of an op (see the file header).
pub open spec fn op_class(op: Op) -> OpClass {
    match op {
        Op::Nop
        | Op::Move { .. }
        | Op::LoadConst { .. }
        | Op::LoadInt { .. }
        | Op::LoadUndefined { .. }
        | Op::LoadNull { .. }
        | Op::LoadBool { .. }
        | Op::LoadHole { .. }
        | Op::GetThis { .. }
        | Op::GetCallee { .. }
        | Op::GetArgc { .. }
        | Op::GetException { .. }
        | Op::Jump { .. }
        | Op::JumpIfUndefined { .. }
        | Op::JumpIfNotUndefined { .. }
        | Op::JumpIfNullish { .. }
        | Op::JumpIfNotNullish { .. } => OpClass::Core,
        Op::Add { .. }
        | Op::Sub { .. }
        | Op::Mul { .. }
        | Op::Div { .. }
        | Op::Mod { .. }
        | Op::Neg { .. }
        | Op::Inc { .. }
        | Op::Dec { .. }
        | Op::BitAnd { .. }
        | Op::BitOr { .. }
        | Op::BitXor { .. }
        | Op::Shl { .. }
        | Op::Shr { .. }
        | Op::UShr { .. }
        | Op::BitNot { .. }
        | Op::Lt { .. }
        | Op::Le { .. }
        | Op::Gt { .. }
        | Op::Ge { .. }
        | Op::StrictEq { .. }
        | Op::StrictNe { .. }
        | Op::Not { .. }
        | Op::ToNumeric { .. }
        | Op::ToNumber { .. }
        | Op::JumpIfTrue { .. }
        | Op::JumpIfFalse { .. }
        | Op::Loop { .. }
        | Op::ThrowIfHole { .. }
        | Op::GetProp { .. }
        | Op::SetProp { .. }
        | Op::GetElem { .. }
        | Op::SetElem { .. }
        | Op::Call { .. }
        | Op::Return { .. }
        | Op::GetEnvSlot { .. }
        | Op::SetEnvSlot { .. }
        | Op::GetEnvParent { .. }
        | Op::GetCalleeEnv { .. } => OpClass::Guarded,
        Op::Exp { .. }
        | Op::LooseEq { .. }
        | Op::LooseNe { .. }
        | Op::TypeOf { .. }
        | Op::InstanceOf { .. }
        | Op::HasProperty { .. }
        | Op::DeleteProp { .. }
        | Op::GetGlobal { .. }
        | Op::SetGlobal { .. }
        | Op::GetGlobalOrUndefined { .. }
        | Op::DeclareGlobals { .. }
        | Op::DefineProp { .. }
        | Op::DefineElem { .. }
        | Op::SetLiteralProto { .. }
        | Op::NewObject { .. }
        | Op::NewArray { .. }
        | Op::NewEnv { .. }
        | Op::NewClosure { .. }
        | Op::New { .. }
        | Op::CallSpread { .. }
        | Op::GetIterator { .. }
        | Op::IterNext { .. }
        | Op::IterClose { .. }
        | Op::Yield { .. }
        | Op::Await { .. }
        | Op::Throw { .. }
        | Op::ToPropertyKey { .. }
        | Op::ToString { .. }
        | Op::CopyDataProperties { .. }
        | Op::GetTemplateObject { .. }
        | Op::NewSpread { .. }
        | Op::SuperCall { .. }
        | Op::SuperCallSpread { .. }
        | Op::InitInstance { .. }
        | Op::ClassSetup { .. }
        | Op::DefineMethod { .. }
        | Op::SetHomeObject { .. }
        | Op::SetInstanceInit { .. }
        | Op::NewPrivateName { .. }
        | Op::GetPrivate { .. }
        | Op::SetPrivate { .. }
        | Op::DefinePrivate { .. }
        | Op::HasPrivate { .. }
        | Op::GetSuperBase { .. }
        | Op::GetSuper { .. }
        | Op::SetSuper { .. }
        | Op::GetNewTarget { .. }
        | Op::ConstructResult { .. }
        | Op::CreateUnmappedArguments { .. }
        | Op::CreateMappedArguments { .. }
        | Op::CreateRestArray { .. }
        | Op::ForInIterator { .. }
        | Op::InitGlobalLexical { .. }
        | Op::NewRegExp { .. }
        | Op::ThrowError { .. } => OpClass::Handler,
    }
}

/// The handler an op calls when it is a handler op, or when it is a guarded
/// op whose guard failed. For a core op the value is unused (`Nop`'s
/// arbitrary choice is `HandlerId::Throw`).
pub open spec fn op_handler(op: Op) -> HandlerId {
    match op {
        Op::Add { .. } => HandlerId::Add,
        Op::Sub { .. } => HandlerId::Sub,
        Op::Mul { .. } => HandlerId::Mul,
        Op::Div { .. } => HandlerId::Div,
        Op::Mod { .. } => HandlerId::Mod,
        Op::Exp { .. } => HandlerId::Exp,
        Op::Neg { .. } => HandlerId::Neg,
        Op::Inc { .. } => HandlerId::Inc,
        Op::Dec { .. } => HandlerId::Dec,
        Op::BitAnd { .. } => HandlerId::BitAnd,
        Op::BitOr { .. } => HandlerId::BitOr,
        Op::BitXor { .. } => HandlerId::BitXor,
        Op::Shl { .. } => HandlerId::Shl,
        Op::Shr { .. } => HandlerId::Shr,
        Op::UShr { .. } => HandlerId::UShr,
        Op::BitNot { .. } => HandlerId::BitNot,
        Op::Lt { .. } => HandlerId::Lt,
        Op::Le { .. } => HandlerId::Le,
        Op::Gt { .. } => HandlerId::Gt,
        Op::Ge { .. } => HandlerId::Ge,
        Op::StrictEq { .. } | Op::StrictNe { .. } => HandlerId::StrictEq,
        Op::LooseEq { .. } | Op::LooseNe { .. } => HandlerId::LooseEq,
        Op::Not { .. } => HandlerId::Not,
        Op::ToNumeric { .. } => HandlerId::ToNumeric,
        Op::ToNumber { .. } => HandlerId::ToNumber,
        Op::JumpIfTrue { .. } | Op::JumpIfFalse { .. } => HandlerId::ToBoolean,
        Op::Loop { .. } => HandlerId::Terminate,
        Op::ThrowIfHole { .. } => HandlerId::ThrowHole,
        Op::GetProp { .. } => HandlerId::GetProp,
        Op::SetProp { .. } => HandlerId::SetProp,
        Op::GetElem { .. } => HandlerId::GetElem,
        Op::SetElem { .. } => HandlerId::SetElem,
        Op::Call { .. } => HandlerId::Call,
        Op::Return { .. } => HandlerId::Return,
        Op::GetEnvSlot { .. }
        | Op::SetEnvSlot { .. }
        | Op::GetEnvParent { .. }
        | Op::GetCalleeEnv { .. } => HandlerId::EnvAccess,
        Op::TypeOf { .. } => HandlerId::TypeOf,
        Op::InstanceOf { .. } => HandlerId::InstanceOf,
        Op::HasProperty { .. } => HandlerId::HasProperty,
        Op::DeleteProp { .. } => HandlerId::DeleteProp,
        Op::GetGlobal { .. } => HandlerId::GetGlobal,
        Op::SetGlobal { .. } => HandlerId::SetGlobal,
        Op::GetGlobalOrUndefined { .. } => HandlerId::GetGlobalOrUndefined,
        Op::DeclareGlobals { .. } => HandlerId::DeclareGlobals,
        Op::DefineProp { .. } => HandlerId::DefineProp,
        Op::DefineElem { .. } => HandlerId::DefineElem,
        Op::SetLiteralProto { .. } => HandlerId::SetLiteralProto,
        Op::NewObject { .. } => HandlerId::NewObject,
        Op::NewArray { .. } => HandlerId::NewArray,
        Op::NewEnv { .. } => HandlerId::NewEnv,
        Op::NewClosure { .. } => HandlerId::NewClosure,
        Op::New { .. } => HandlerId::New,
        Op::CallSpread { .. } => HandlerId::CallSpread,
        Op::GetIterator { .. } => HandlerId::GetIterator,
        Op::IterNext { .. } => HandlerId::IterNext,
        Op::IterClose { .. } => HandlerId::IterClose,
        Op::Yield { .. } => HandlerId::Yield,
        Op::Await { .. } => HandlerId::Await,
        Op::Throw { .. } | Op::Nop => HandlerId::Throw,
        Op::ThrowError { .. } => HandlerId::ThrowError,
        Op::NewRegExp { .. } => HandlerId::NewRegExp,
        Op::InitGlobalLexical { .. } => HandlerId::InitGlobalLexical,
        Op::ToPropertyKey { .. } => HandlerId::ToPropertyKey,
        Op::ToString { .. } => HandlerId::ToString,
        Op::CopyDataProperties { .. } => HandlerId::CopyDataProperties,
        Op::GetTemplateObject { .. } => HandlerId::GetTemplateObject,
        Op::NewSpread { .. } => HandlerId::NewSpread,
        Op::SuperCall { .. } => HandlerId::SuperCall,
        Op::SuperCallSpread { .. } => HandlerId::SuperCallSpread,
        Op::InitInstance { .. } => HandlerId::InitInstance,
        Op::ClassSetup { .. } => HandlerId::ClassSetup,
        Op::DefineMethod { .. } => HandlerId::DefineMethod,
        Op::SetHomeObject { .. } => HandlerId::SetHomeObject,
        Op::SetInstanceInit { .. } => HandlerId::SetInstanceInit,
        Op::NewPrivateName { .. } => HandlerId::NewPrivateName,
        Op::GetPrivate { .. } => HandlerId::GetPrivate,
        Op::SetPrivate { .. } => HandlerId::SetPrivate,
        Op::DefinePrivate { .. } => HandlerId::DefinePrivate,
        Op::HasPrivate { .. } => HandlerId::HasPrivate,
        Op::GetSuperBase { .. } => HandlerId::GetSuperBase,
        Op::GetSuper { .. } => HandlerId::GetSuper,
        Op::SetSuper { .. } => HandlerId::SetSuper,
        Op::GetNewTarget { .. } => HandlerId::GetNewTarget,
        Op::ConstructResult { .. } => HandlerId::ConstructResult,
        Op::CreateUnmappedArguments { .. } => HandlerId::CreateUnmappedArguments,
        Op::CreateMappedArguments { .. } => HandlerId::CreateMappedArguments,
        Op::CreateRestArray { .. } => HandlerId::CreateRestArray,
        Op::ForInIterator { .. } => HandlerId::ForInIterator,
        // Core ops never call a handler; the value is not used.
        _ => HandlerId::Throw,
    }
}

/// The register an op writes its result to when it is a call, which is where
/// a `Return` delivers its value. Only calls have one.
pub open spec fn call_dst(op: Op) -> Option<nat> {
    match op {
        Op::Call { dst, .. } => Some(dst),
        Op::CallSpread { dst, .. } => Some(dst),
        _ => None,
    }
}

} // verus!
