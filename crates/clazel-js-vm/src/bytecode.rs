//! The executable bytecode the compiler ([`crate::compile`]) emits (phase-7.md
//! item 7.7).
//!
//! [`Instr`] is [`crate::ops::Op`] with `u32` operands instead of `nat`s, one
//! variant per variant, with the same field names and the same meaning: the
//! semantics of each is `spec fn step` in [`crate::spec`], and nothing here
//! adds an op the spec does not describe. [`check_function`] is
//! [`crate::spec::code_wf`] (and so `op_wf`) written as executable code; the
//! compiler's tests run it over every function they compile. It is a
//! transcription, not a proof: nothing ties the two, so the claim is the
//! crate's tier (0).
//!
//! # What is not in the spec's `Code`, and how it is modelled here
//!
//! - **The constant pool is not `u64` values.** The spec's
//!   [`crate::spec::Code::consts`] holds NaN-boxed values, among them heap
//!   references to interned strings, which the heap (item 7.5, not on `main`)
//!   creates. [`Const`] holds what the heap will intern: a Number as its
//!   IEEE 754 bit pattern, a string as UTF-16 code units, a BigInt as the text
//!   of its literal. Loading the pool into a heap is the interpreter's job
//!   (7.8).
//! - **The exception table** is a handler input to `spec fn step`
//!   ("Exceptions are handler results"), so it is not in `Code`. [`Handler`] is
//!   this crate's form of it: the first entry, in table order, whose
//!   `start <= pc < end` catches an exception thrown at `pc`, and unwinding
//!   continues at its `target`, which holds a [`Instr::GetException`]. Inner
//!   `try` statements come first.
//! - **Function templates** are [`Program::functions`]: `NewClosure::func` is an
//!   index into it, and `Program::main` is the script's own function. A
//!   function's [`FunctionCode::kind`] and [`FunctionCode::strict`] are the
//!   facts about a template that the handlers need (an arrow function has no
//!   `prototype` and is not a constructor, strictness decides what a failed
//!   assignment does), which the spec leaves to "decided by the heap when the
//!   function is created" (`FnInfo::fast_callable`).
//! - **Every op carries a source span** ([`FunctionCode::spans`], parallel to
//!   [`FunctionCode::instrs`], checked by [`check_function`]): code point
//!   offsets into the source text, the span of the AST node the op was
//!   emitted for.

/// A register number: register `r` is slot `fp + HDR_SLOTS + r` of the frame
/// (`spec::reg_slot`), the arguments first.
pub type Reg = u32;

/// The limit on ops in a function and on registers in a frame: the return
/// address packs a `pc` and a frame base into 24 bits each (`spec::ret_limit`).
pub const LIMIT: u32 = 0xFF_FFFF;

/// A span of the source text, in code points: `start..end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    /// The first code point.
    pub start: usize,
    /// One past the last code point.
    pub end: usize,
}

/// The error constructors a compiler-known throw can name
/// ([`crate::ops::ErrorKind`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

macro_rules! instrs {
    ($( $v:ident $( { $( $f:ident : $t:ty ),* $(,)? } )? ),* $(,)?) => {
        /// One instruction: [`crate::ops::Op`] with `u32` operands. Each
        /// variant is the same-named `Op` variant, with the same operands and
        /// meaning (the docs of `Op` and `spec fn step` are the documentation).
        #[derive(Clone, Debug, PartialEq)]
        pub enum Instr {
            $(
                #[doc = concat!("The op [`crate::ops::Op::", stringify!($v), "`].")]
                $v $( { $( #[doc = concat!("The `", stringify!($f), "` operand of the op.")] $f : $t ),* } )?
            ),*
        }
    };
}

instrs! {
    Nop,
    Move { dst: Reg, src: Reg },
    LoadConst { dst: Reg, k: u32 },
    LoadInt { dst: Reg, imm: i32 },
    LoadUndefined { dst: Reg },
    LoadNull { dst: Reg },
    LoadBool { dst: Reg, flag: bool },
    LoadHole { dst: Reg },
    GetThis { dst: Reg },
    GetCallee { dst: Reg },
    GetArgc { dst: Reg },
    GetException { dst: Reg },
    Jump { target: u32 },
    JumpIfUndefined { src: Reg, target: u32 },
    JumpIfNotUndefined { src: Reg, target: u32 },
    JumpIfNullish { src: Reg, target: u32 },
    JumpIfNotNullish { src: Reg, target: u32 },
    Add { dst: Reg, a: Reg, b: Reg },
    Sub { dst: Reg, a: Reg, b: Reg },
    Mul { dst: Reg, a: Reg, b: Reg },
    Div { dst: Reg, a: Reg, b: Reg },
    Mod { dst: Reg, a: Reg, b: Reg },
    Neg { dst: Reg, src: Reg },
    Inc { dst: Reg, src: Reg },
    Dec { dst: Reg, src: Reg },
    BitAnd { dst: Reg, a: Reg, b: Reg },
    BitOr { dst: Reg, a: Reg, b: Reg },
    BitXor { dst: Reg, a: Reg, b: Reg },
    Shl { dst: Reg, a: Reg, b: Reg },
    Shr { dst: Reg, a: Reg, b: Reg },
    UShr { dst: Reg, a: Reg, b: Reg },
    BitNot { dst: Reg, src: Reg },
    Lt { dst: Reg, a: Reg, b: Reg },
    Le { dst: Reg, a: Reg, b: Reg },
    Gt { dst: Reg, a: Reg, b: Reg },
    Ge { dst: Reg, a: Reg, b: Reg },
    StrictEq { dst: Reg, a: Reg, b: Reg },
    StrictNe { dst: Reg, a: Reg, b: Reg },
    Not { dst: Reg, src: Reg },
    ToNumeric { dst: Reg, src: Reg },
    ToNumber { dst: Reg, src: Reg },
    JumpIfTrue { cond: Reg, target: u32 },
    JumpIfFalse { cond: Reg, target: u32 },
    Loop { target: u32 },
    ThrowIfHole { src: Reg },
    GetProp { dst: Reg, obj: Reg, key: u32, ic: u32 },
    SetProp { obj: Reg, key: u32, val: Reg, ic: u32 },
    GetElem { dst: Reg, obj: Reg, idx: Reg },
    SetElem { obj: Reg, idx: Reg, val: Reg },
    Call { dst: Reg, callee: Reg, this: Reg, args: Reg, argc: u32 },
    Return { src: Reg },
    GetEnvSlot { dst: Reg, env: Reg, idx: u32 },
    SetEnvSlot { env: Reg, idx: u32, src: Reg },
    GetEnvParent { dst: Reg, env: Reg },
    GetCalleeEnv { dst: Reg },
    Exp { dst: Reg, a: Reg, b: Reg },
    LooseEq { dst: Reg, a: Reg, b: Reg },
    LooseNe { dst: Reg, a: Reg, b: Reg },
    TypeOf { dst: Reg, src: Reg },
    InstanceOf { dst: Reg, a: Reg, b: Reg },
    HasProperty { dst: Reg, a: Reg, b: Reg },
    DeleteProp { dst: Reg, obj: Reg, idx: Reg },
    GetGlobal { dst: Reg, key: u32, ic: u32 },
    SetGlobal { key: u32, src: Reg, ic: u32 },
    GetGlobalOrUndefined { dst: Reg, key: u32 },
    DeclareGlobals { k: u32 },
    DefineProp { obj: Reg, key: u32, val: Reg },
    DefineElem { obj: Reg, idx: Reg, val: Reg },
    SetLiteralProto { obj: Reg, val: Reg },
    NewObject { dst: Reg },
    NewArray { dst: Reg, len: u32 },
    NewEnv { dst: Reg, parent: Reg, size: u32 },
    NewClosure { dst: Reg, func: u32, env: Reg },
    New { dst: Reg, callee: Reg, args: Reg, argc: u32 },
    CallSpread { dst: Reg, callee: Reg, this: Reg, args: Reg },
    GetIterator { dst: Reg, src: Reg },
    IterNext { value: Reg, done: Reg, iter: Reg },
    IterClose { iter: Reg },
    Yield { src: Reg, value: Reg, mode: Reg },
    Await { src: Reg, value: Reg, mode: Reg },
    Throw { src: Reg },
    ThrowError { kind: ErrorKind, msg: u32 },
}

impl Instr {
    /// The op index this op jumps to, for the ops that jump.
    pub fn target(&self) -> Option<u32> {
        match self {
            Instr::Jump { target }
            | Instr::JumpIfUndefined { target, .. }
            | Instr::JumpIfNotUndefined { target, .. }
            | Instr::JumpIfNullish { target, .. }
            | Instr::JumpIfNotNullish { target, .. }
            | Instr::JumpIfTrue { target, .. }
            | Instr::JumpIfFalse { target, .. }
            | Instr::Loop { target } => Some(*target),
            _ => None,
        }
    }

    /// Replaces the jump target of an op that jumps; false for any other op.
    pub fn set_target(&mut self, t: u32) -> bool {
        match self {
            Instr::Jump { target }
            | Instr::JumpIfUndefined { target, .. }
            | Instr::JumpIfNotUndefined { target, .. }
            | Instr::JumpIfNullish { target, .. }
            | Instr::JumpIfNotNullish { target, .. }
            | Instr::JumpIfTrue { target, .. }
            | Instr::JumpIfFalse { target, .. }
            | Instr::Loop { target } => {
                *target = t;
                true
            }
            _ => false,
        }
    }

    /// `spec::falls_through`: the op can continue at the next op.
    pub fn falls_through(&self) -> bool {
        !matches!(
            self,
            Instr::Jump { .. }
                | Instr::Loop { .. }
                | Instr::Return { .. }
                | Instr::Throw { .. }
                | Instr::ThrowError { .. }
        )
    }
}

/// A constant of a function's pool: what the heap interns when it loads the
/// function (see the module header).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Const {
    /// A Number, as its IEEE 754 binary64 bit pattern (never a NaN).
    Number(u64),
    /// A string: UTF-16 code units, lone surrogates allowed.
    String(Vec<u16>),
    /// A BigInt: the digits of its literal, with the radix prefix (`0x`, `0o`,
    /// `0b`) if it has one, without the `n` suffix and the `_` separators.
    BigInt(Vec<u16>),
    /// A script's declaration record, which [`Instr::DeclareGlobals`] reads:
    /// the heap builds it when it loads the function (see
    /// [`crate::ops::Op::DeclareGlobals`]).
    GlobalDeclarations(GlobalDecls),
}

/// What GlobalDeclarationInstantiation (§16.1.7†) reads of a script.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct GlobalDecls {
    /// The names of the LexicallyScopedDeclarations (step 13), each with
    /// whether it is a constant.
    pub lexical: Vec<(Vec<u16>, bool)>,
    /// The VarScopedDeclarations (step 5), in source order.
    pub var_scoped: Vec<VarScoped>,
    /// The names Annex B.3.2.2† adds at step 12: functions declared in
    /// blocks, in source order.
    pub annexb: Vec<Vec<u16>>,
}

/// A var-scoped declaration of a script.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VarScoped {
    /// A `var` (one bound name).
    Var(Vec<u16>),
    /// A function declaration: its name and its template in
    /// [`Program::functions`].
    Function {
        /// The function's name.
        name: Vec<u16>,
        /// The index of its template.
        func: u32,
    },
}

/// An exception-table entry (see the module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Handler {
    /// The first op index covered.
    pub start: u32,
    /// One past the last op index covered.
    pub end: u32,
    /// The op index unwinding continues at; a [`Instr::GetException`].
    pub target: u32,
}

/// What kind of function a template is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionKind {
    /// The script's own code.
    Script,
    /// A function declaration or expression.
    Normal,
    /// An arrow function.
    Arrow,
    /// A method of an object literal.
    Method,
}

/// One function's code (`spec::Code` and the facts about the template the
/// module header lists).
#[derive(Clone, Debug, PartialEq)]
pub struct FunctionCode {
    /// The function's own name (a declaration's or an expression's), as UTF-16
    /// code units; empty for an anonymous function.
    pub name: Vec<u16>,
    /// What kind of function it is.
    pub kind: FunctionKind,
    /// Whether the code is strict mode code.
    pub strict: bool,
    /// The span of the whole function in the source text.
    pub span: Span,
    /// The number of parameters; registers `0..nparams` hold the arguments.
    pub nparams: u32,
    /// The number of registers after the parameters.
    pub nregs: u32,
    /// The size of the inline-cache table.
    pub nics: u32,
    /// The ops.
    pub instrs: Vec<Instr>,
    /// The span of each op, parallel to `instrs`.
    pub spans: Vec<Span>,
    /// The constant pool.
    pub consts: Vec<Const>,
    /// The exception table.
    pub handlers: Vec<Handler>,
}

/// A compiled script: every function of it, and the script's own.
#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    /// All function templates; `NewClosure::func` indexes this.
    pub functions: Vec<FunctionCode>,
    /// The index of the script's own function (always 0).
    pub main: u32,
}

/// `spec::reg_ok`.
fn reg_ok(f: &FunctionCode, r: Reg) -> bool {
    r < f.nparams.saturating_add(f.nregs)
}

/// `spec::regs_ok`.
fn regs_ok(f: &FunctionCode, r: Reg, n: u32) -> bool {
    r.saturating_add(n) <= f.nparams.saturating_add(f.nregs)
}

/// `spec::op_wf`, and the checks of `spec::code_wf` and of this module's own
/// tables, for function `f` of a program of `nfuncs` functions: every
/// register inside the frame, every constant, target and cache index in its
/// table, no op that can continue is the last, the function fits the return
/// address, the spans are parallel to the ops, and the exception table is in
/// range.
pub fn check_function(f: &FunctionCode, nfuncs: usize) -> Result<(), &'static str> {
    let n = f.instrs.len();
    if n >= LIMIT as usize || f.nparams.saturating_add(f.nregs) >= LIMIT {
        return Err("function exceeds the return-address limit");
    }
    if f.spans.len() != n {
        return Err("spans are not parallel to ops");
    }
    let target_ok = |t: u32| (t as usize) < n;
    let konst = |k: u32| (k as usize) < f.consts.len();
    let ic = |i: u32| i < f.nics;
    for (i, ins) in f.instrs.iter().enumerate() {
        if ins.falls_through() && i.saturating_add(1) >= n {
            return Err("an op that falls through is the last");
        }
        let ok = match *ins {
            Instr::Nop => true,
            Instr::Move { dst, src } => reg_ok(f, dst) && reg_ok(f, src),
            Instr::LoadConst { dst, k } => reg_ok(f, dst) && konst(k),
            Instr::LoadInt { dst, .. }
            | Instr::LoadUndefined { dst }
            | Instr::LoadNull { dst }
            | Instr::LoadBool { dst, .. }
            | Instr::LoadHole { dst }
            | Instr::GetThis { dst }
            | Instr::GetCallee { dst }
            | Instr::GetArgc { dst }
            | Instr::GetException { dst }
            | Instr::GetCalleeEnv { dst }
            | Instr::NewObject { dst }
            | Instr::NewArray { dst, .. } => reg_ok(f, dst),
            Instr::Jump { target } | Instr::Loop { target } => target_ok(target),
            Instr::JumpIfUndefined { src, target }
            | Instr::JumpIfNotUndefined { src, target }
            | Instr::JumpIfNullish { src, target }
            | Instr::JumpIfNotNullish { src, target } => reg_ok(f, src) && target_ok(target),
            Instr::JumpIfTrue { cond, target } | Instr::JumpIfFalse { cond, target } => {
                reg_ok(f, cond) && target_ok(target)
            }
            Instr::Add { dst, a, b }
            | Instr::Sub { dst, a, b }
            | Instr::Mul { dst, a, b }
            | Instr::Div { dst, a, b }
            | Instr::Mod { dst, a, b }
            | Instr::BitAnd { dst, a, b }
            | Instr::BitOr { dst, a, b }
            | Instr::BitXor { dst, a, b }
            | Instr::Shl { dst, a, b }
            | Instr::Shr { dst, a, b }
            | Instr::UShr { dst, a, b }
            | Instr::Lt { dst, a, b }
            | Instr::Le { dst, a, b }
            | Instr::Gt { dst, a, b }
            | Instr::Ge { dst, a, b }
            | Instr::StrictEq { dst, a, b }
            | Instr::StrictNe { dst, a, b }
            | Instr::Exp { dst, a, b }
            | Instr::LooseEq { dst, a, b }
            | Instr::LooseNe { dst, a, b }
            | Instr::InstanceOf { dst, a, b }
            | Instr::HasProperty { dst, a, b } => reg_ok(f, dst) && reg_ok(f, a) && reg_ok(f, b),
            Instr::Neg { dst, src }
            | Instr::Inc { dst, src }
            | Instr::Dec { dst, src }
            | Instr::BitNot { dst, src }
            | Instr::Not { dst, src }
            | Instr::ToNumeric { dst, src }
            | Instr::ToNumber { dst, src }
            | Instr::TypeOf { dst, src }
            | Instr::GetIterator { dst, src } => reg_ok(f, dst) && reg_ok(f, src),
            Instr::ThrowIfHole { src }
            | Instr::Return { src }
            | Instr::Throw { src }
            | Instr::IterClose { iter: src } => reg_ok(f, src),
            Instr::GetProp {
                dst,
                obj,
                key,
                ic: c,
            } => reg_ok(f, dst) && reg_ok(f, obj) && konst(key) && ic(c),
            Instr::SetProp {
                obj,
                key,
                val,
                ic: c,
            } => reg_ok(f, obj) && konst(key) && reg_ok(f, val) && ic(c),
            Instr::GetElem { dst, obj, idx } | Instr::DeleteProp { dst, obj, idx } => {
                reg_ok(f, dst) && reg_ok(f, obj) && reg_ok(f, idx)
            }
            Instr::SetElem { obj, idx, val } => reg_ok(f, obj) && reg_ok(f, idx) && reg_ok(f, val),
            Instr::Call {
                dst,
                callee,
                this,
                args,
                argc,
            } => reg_ok(f, dst) && reg_ok(f, callee) && reg_ok(f, this) && regs_ok(f, args, argc),
            Instr::GetEnvSlot { dst, env, .. } => reg_ok(f, dst) && reg_ok(f, env),
            Instr::SetEnvSlot { env, src, .. } => reg_ok(f, env) && reg_ok(f, src),
            Instr::GetEnvParent { dst, env } => reg_ok(f, dst) && reg_ok(f, env),
            Instr::GetGlobal { dst, key, ic: c } => reg_ok(f, dst) && konst(key) && ic(c),
            Instr::GetGlobalOrUndefined { dst, key } => reg_ok(f, dst) && konst(key),
            // `spec::op_wf`'s `value_wf(consts[k])`: the constant is a declaration
            // record, whose functions are templates of the program.
            Instr::DeclareGlobals { k } => match f.consts.get(k as usize) {
                Some(Const::GlobalDeclarations(d)) => d.var_scoped.iter().all(|v| match v {
                    VarScoped::Function { func, .. } => (*func as usize) < nfuncs,
                    VarScoped::Var(_) => true,
                }),
                _ => false,
            },
            Instr::DefineProp { obj, key, val } => reg_ok(f, obj) && konst(key) && reg_ok(f, val),
            Instr::DefineElem { obj, idx, val } => {
                reg_ok(f, obj) && reg_ok(f, idx) && reg_ok(f, val)
            }
            Instr::SetLiteralProto { obj, val } => reg_ok(f, obj) && reg_ok(f, val),
            Instr::SetGlobal { key, src, ic: c } => konst(key) && reg_ok(f, src) && ic(c),
            Instr::NewEnv { dst, parent, .. } => reg_ok(f, dst) && reg_ok(f, parent),
            Instr::NewClosure { dst, func, env } => {
                reg_ok(f, dst) && reg_ok(f, env) && (func as usize) < nfuncs
            }
            Instr::New {
                dst,
                callee,
                args,
                argc,
            } => reg_ok(f, dst) && reg_ok(f, callee) && regs_ok(f, args, argc),
            Instr::CallSpread {
                dst,
                callee,
                this,
                args,
            } => reg_ok(f, dst) && reg_ok(f, callee) && reg_ok(f, this) && reg_ok(f, args),
            Instr::IterNext { value, done, iter } => {
                reg_ok(f, value) && reg_ok(f, done) && reg_ok(f, iter)
            }
            Instr::Yield { src, value, mode } | Instr::Await { src, value, mode } => {
                reg_ok(f, src) && reg_ok(f, value) && reg_ok(f, mode)
            }
            Instr::ThrowError { msg, .. } => konst(msg),
        };
        if !ok {
            return Err("an operand is out of range");
        }
    }
    for h in &f.handlers {
        if h.start > h.end || (h.end as usize) > n || !target_ok(h.target) {
            return Err("an exception-table entry is out of range");
        }
        if !matches!(
            f.instrs.get(h.target as usize),
            Some(Instr::GetException { .. })
        ) {
            return Err("a handler target is not a GetException");
        }
    }
    Ok(())
}

/// [`check_function`] over every function of the program, and `main` in range.
pub fn check_program(p: &Program) -> Result<(), &'static str> {
    if (p.main as usize) >= p.functions.len() {
        return Err("main is out of range");
    }
    for f in &p.functions {
        check_function(f, p.functions.len())?;
    }
    Ok(())
}
