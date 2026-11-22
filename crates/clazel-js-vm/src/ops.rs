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
