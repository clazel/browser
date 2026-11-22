//! The compiler from the AST to bytecode (phase-7.md item 7.7, first slice):
//! [`compile_script`].
//!
//! # What it compiles
//!
//! - **Expressions:** literals (numbers, BigInts, strings, `true`, `false`,
//!   `null`), identifiers, `this`, the unary, binary, logical, conditional and
//!   comma operators, assignment (simple, compound and logical), `++` and `--`,
//!   calls, `new`, member access, object literals (data properties, methods and
//!   `__proto__:`) and array literals without spread, and function and arrow
//!   function expressions; `typeof` of a global, unary `+` as `ToNumber`.
//! - **Statements:** `var`, `let` and `const` with temporal-dead-zone checks,
//!   blocks, `if`, `while`, `do`-`while` and `for`, `switch`, labels, `break`,
//!   `continue`, `return`, `throw`, `try`/`catch`/`finally`, and function
//!   declarations, with Annex B.3.3's block-level hoisting.
//! - **Closures:** scope analysis ([`crate::scope`]) puts a binding that no
//!   inner function refers to in a register and a captured one in a slot of an
//!   environment object that its scope creates on entry.
//!
//! # What it does not compile yet
//!
//! It returns [`CompileError::NotYetCompiled`] with a stated feature, never a
//! panic: destructuring, spread, rest and default parameters, classes and
//! `super`, generators and async functions, `with` and direct `eval`, modules,
//! template literals, regular expression literals, optional chaining, accessors,
//! `for`-`in` and `for`-`of`, the `arguments` object, `new.target`, and the few
//! forms listed on [`CompileError::NotYetCompiled`]'s users in this file
//! (`delete` of a global variable, a function declaration as the body of an
//! `if` or a label). A script's top-level `let`, `const` and `class` are
//! locals of the script function, not bindings of the global declarative
//! record (`DeclareGlobals`'s record lists none), and a computed property name
//! is converted to a key when its define op runs, not before the value.
//!
//! # Conventions of the output
//!
//! - **Registers.** Registers `0..nparams` are the arguments. A binding that is
//!   not captured has a register for as long as its scope is entered, then
//!   temporaries are allocated above, stack-wise.
//! - **The current environment** of a function is kept in registers: the
//!   function's `GetCalleeEnv` in its first register after the arguments, and
//!   one register for each scope of the function that creates an environment.
//!   Reaching a captured binding is `GetEnvParent` as many times as scopes that
//!   create an environment lie between, then `GetEnvSlot` or `SetEnvSlot`.
//! - **Temporal dead zone.** A `let` or `const` register or slot starts as the
//!   hole (§9.1.1.1.1 CreateMutableBinding, uninitialized) and a read or write
//!   before its declaration runs [`Instr::ThrowIfHole`]. The check is left out
//!   where the reference is in the same function as the declaration and after
//!   it in the source text (and the scope is not a `switch`'s), because then
//!   every path to it passes the initialization.
//! - **Loops** end in [`Instr::Loop`], the op that checks the termination flag.
//! - **`finally`** is compiled once. A completion that enters it (normal,
//!   throw, and each `break`, `continue` and `return` that leaves the `try`)
//!   stores a code in a register, and the block ends in a dispatch on it.
//! - **Source spans.** Every op is emitted with the span of the AST node it
//!   was compiled for.
//!
//! # Where the standard is followed
//!
//! Comments cite ECMA-262 (see `spec.rs` for the pinned edition). The steps
//! this slice implements: §14.15.3 (try-finally completion), §14.7.4.4
//! CreatePerIterationEnvironment, §14.12.4 (switch evaluation), §9.1.1.1.5
//! SetMutableBinding steps 3 to 6, §9.1.1.1.6 GetBindingValue step 2 (TDZ),
//! §15.2.5 InstantiateOrdinaryFunctionExpression, §10.2.11
//! FunctionDeclarationInstantiation, and Annex B.3.3.1.

use crate::bytecode::{
    Const, ErrorKind, FunctionCode, FunctionKind, GlobalDecls, Handler, Instr, LIMIT, Program, Reg,
    Span, VarScoped,
};
use crate::literal::{self, Number};
use crate::scope::{self, Analysis, BKind, NONE, SKind, Target, span_of};
use clazel_js_syntax::ast::{Ast, Node, NodeKind, Op as AOp};
use std::collections::HashMap;

/// Why a script was not compiled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The script uses a construct this slice does not compile (see the module
    /// header). Not a failure of the compiler: the construct is `feature`, at
    /// `span`.
    NotYetCompiled {
        /// The construct.
        feature: &'static str,
        /// Where it is.
        span: Span,
    },
    /// A function or a table is larger than the bytecode can hold (ops or
    /// registers beyond [`LIMIT`], more than `u32` constants and so on).
    TooLarge(&'static str),
    /// The AST was not what the parser guarantees, or the compiler has a bug.
    /// Never expected: the tests count these.
    Internal(&'static str),
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::NotYetCompiled { feature, span } => {
                write!(
                    f,
                    "not yet compiled: {feature} at {}..{}",
                    span.start, span.end
                )
            }
            CompileError::TooLarge(what) => write!(f, "too large: {what}"),
            CompileError::Internal(what) => write!(f, "internal error: {what}"),
        }
    }
}

impl std::error::Error for CompileError {}

type R<T> = Result<T, CompileError>;

/// Compiles a parsed script (`ast` was parsed from `src`, code points) to a
/// [`Program`].
///
/// Total: every AST has a result, and the compiler never panics. A script
/// with a construct of the module header's second list is a
/// [`CompileError::NotYetCompiled`].
pub fn compile_script(ast: &Ast, src: &[u32]) -> Result<Program, CompileError> {
    // Compilation recurses once per level of the AST (at most MAX_DEPTH of
    // them, each a few frames): a program that deep needs a bigger stack than
    // a test thread has, as the parser does.
    const SMALL: usize = 256;
    if ast.nodes.len() <= SMALL {
        return compile_inner(ast, src);
    }
    std::thread::scope(|s| {
        match std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(s, || compile_inner(ast, src))
        {
            Ok(h) => h
                .join()
                .unwrap_or(Err(CompileError::Internal("the compiler thread panicked"))),
            Err(_) => compile_inner(ast, src),
        }
    })
}

fn compile_inner(ast: &Ast, src: &[u32]) -> Result<Program, CompileError> {
    scope::check_supported(ast)?;
    let an = scope::analyze(ast, src)?;
    let root = ast.root;
    let rn = ast
        .nodes
        .get(root as usize)
        .ok_or(CompileError::Internal("no root"))?;
    if rn.kind != NodeKind::Script {
        return Err(CompileError::NotYetCompiled {
            feature: "modules",
            span: span_of(ast, root as usize),
        });
    }
    let eval_name = an
        .names
        .iter()
        .position(|n| n.iter().copied().eq("eval".chars().map(u32::from)))
        .and_then(|p| u32::try_from(p).ok())
        .unwrap_or(NONE);
    let mut cg = Cg {
        ast,
        src,
        an: &an,
        out: Vec::new(),
        loc: vec![None; an.bindings.len()],
        eval_name,
        f: FnState::new(FunctionKind::Script, false, Span { start: 0, end: 0 }, 0),
    };
    let main = cg.compile_function(root, FunctionKind::Script)?;
    let mut functions = Vec::with_capacity(cg.out.len());
    for f in cg.out {
        functions.push(f.ok_or(CompileError::Internal(
            "a function was reserved but not compiled",
        ))?);
    }
    Ok(Program { functions, main })
}

/// How a `break` or `continue` reaches its target, and what a `return` does,
/// when it passes a `finally`.
#[derive(Clone, Copy, Debug)]
enum Exit {
    /// `break` to the control entry at this index.
    Break(usize),
    /// `continue` to the control entry at this index.
    Continue(usize),
    /// `return`, the value in a register.
    Return,
}

/// An entry of the control stack: what a `break`, a `continue` or a `return`
/// passes.
enum Ctl {
    Loop {
        labels: Vec<u32>,
        brk: usize,
        cont: usize,
    },
    Switch {
        labels: Vec<u32>,
        brk: usize,
    },
    Labelled {
        labels: Vec<u32>,
        brk: usize,
    },
    Finally {
        fin: usize,
        ctype: Reg,
        cvalue: Reg,
        pending: Vec<Exit>,
    },
}

/// The state of the function being compiled.
struct FnState {
    kind: FunctionKind,
    strict: bool,
    span: Span,
    instrs: Vec<Instr>,
    spans: Vec<Span>,
    consts: Vec<Const>,
    const_map: HashMap<Const, u32>,
    nics: u32,
    next_reg: Reg,
    max_reg: Reg,
    /// Label to op index, once bound.
    labels: Vec<Option<u32>>,
    /// Exception-table entries, by label.
    handlers: Vec<(usize, usize, usize)>,
    ctl: Vec<Ctl>,
    cur_scope: u32,
    /// The register holding the function's callee environment.
    base_env: Reg,
    /// The register holding the environment of each entered scope that creates one.
    env_regs: HashMap<u32, Reg>,
    /// The register watermark at each entered scope.
    scope_marks: Vec<Reg>,
}

impl FnState {
    fn new(kind: FunctionKind, strict: bool, span: Span, nparams: u32) -> Self {
        FnState {
            kind,
            strict,
            span,
            instrs: Vec::new(),
            spans: Vec::new(),
            consts: Vec::new(),
            const_map: HashMap::new(),
            nics: 0,
            next_reg: nparams,
            max_reg: nparams,
            labels: Vec::new(),
            handlers: Vec::new(),
            ctl: Vec::new(),
            cur_scope: NONE,
            base_env: 0,
            env_regs: HashMap::new(),
            scope_marks: Vec::new(),
        }
    }
}

/// The code generator.
struct Cg<'a> {
    ast: &'a Ast,
    src: &'a [u32],
    an: &'a Analysis,
    out: Vec<Option<FunctionCode>>,
    /// The register of each binding that is not captured, once its scope is entered.
    loc: Vec<Option<Reg>>,
    /// The interned name `eval`, or [`NONE`].
    eval_name: u32,
    f: FnState,
}

/// Whether compiling the kind writes its destination register only with its
/// last op, after every operand has been read. Only these may be compiled
/// straight into a binding's register: for any other kind the destination
/// could be overwritten before an operand that reads it is evaluated.
fn final_op_kind(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::NumericLiteral
            | NodeKind::StringLiteral
            | NodeKind::NullLiteral
            | NodeKind::BooleanLiteral
            | NodeKind::ThisExpression
            | NodeKind::IdentifierReference
            | NodeKind::FunctionExpression
            | NodeKind::ArrowFunction
            | NodeKind::MemberExpression
            | NodeKind::CallExpression
            | NodeKind::NewExpression
            | NodeKind::UnaryExpression
            | NodeKind::ExponentiationExpression
            | NodeKind::MultiplicativeExpression
            | NodeKind::AdditiveExpression
            | NodeKind::ShiftExpression
            | NodeKind::RelationalExpression
            | NodeKind::EqualityExpression
            | NodeKind::BitwiseANDExpression
            | NodeKind::BitwiseXORExpression
            | NodeKind::BitwiseORExpression
    )
}

/// The op for a binary operator (§13.6 to §13.12), or of a compound
/// assignment (§13.15.2), writing `dst`.
fn binary_instr(kind: NodeKind, op: AOp, dst: Reg, a: Reg, b: Reg) -> Option<Instr> {
    Some(match (kind, op) {
        (NodeKind::ExponentiationExpression, _) | (_, AOp::ExpAssign) => Instr::Exp { dst, a, b },
        (NodeKind::MultiplicativeExpression, AOp::Mul) | (_, AOp::MulAssign) => {
            Instr::Mul { dst, a, b }
        }
        (NodeKind::MultiplicativeExpression, AOp::Div) | (_, AOp::DivAssign) => {
            Instr::Div { dst, a, b }
        }
        (NodeKind::MultiplicativeExpression, AOp::Rem) | (_, AOp::RemAssign) => {
            Instr::Mod { dst, a, b }
        }
        (NodeKind::AdditiveExpression, AOp::Add) | (_, AOp::AddAssign) => Instr::Add { dst, a, b },
        (NodeKind::AdditiveExpression, AOp::Sub) | (_, AOp::SubAssign) => Instr::Sub { dst, a, b },
        (NodeKind::ShiftExpression, AOp::Shl) | (_, AOp::ShlAssign) => Instr::Shl { dst, a, b },
        (NodeKind::ShiftExpression, AOp::Shr) | (_, AOp::ShrAssign) => Instr::Shr { dst, a, b },
        (NodeKind::ShiftExpression, AOp::UShr) | (_, AOp::UShrAssign) => Instr::UShr { dst, a, b },
        (NodeKind::RelationalExpression, AOp::Lt) => Instr::Lt { dst, a, b },
        (NodeKind::RelationalExpression, AOp::Gt) => Instr::Gt { dst, a, b },
        (NodeKind::RelationalExpression, AOp::Le) => Instr::Le { dst, a, b },
        (NodeKind::RelationalExpression, AOp::Ge) => Instr::Ge { dst, a, b },
        (NodeKind::RelationalExpression, AOp::InstanceOf) => Instr::InstanceOf { dst, a, b },
        (NodeKind::RelationalExpression, AOp::In) => Instr::HasProperty { dst, a, b },
        (NodeKind::EqualityExpression, AOp::Eq) => Instr::LooseEq { dst, a, b },
        (NodeKind::EqualityExpression, AOp::Ne) => Instr::LooseNe { dst, a, b },
        (NodeKind::EqualityExpression, AOp::StrictEq) => Instr::StrictEq { dst, a, b },
        (NodeKind::EqualityExpression, AOp::StrictNe) => Instr::StrictNe { dst, a, b },
        (NodeKind::BitwiseANDExpression, _) | (_, AOp::BitAndAssign) => Instr::BitAnd { dst, a, b },
        (NodeKind::BitwiseXORExpression, _) | (_, AOp::BitXorAssign) => Instr::BitXor { dst, a, b },
        (NodeKind::BitwiseORExpression, _) | (_, AOp::BitOrAssign) => Instr::BitOr { dst, a, b },
        _ => return None,
    })
}

/// A member access's property, by its kind.
enum Prop {
    /// `.name`: the constant-pool index of the name.
    Named(u32),
    /// `[expr]`: the register holding the key.
    Computed(Reg),
}

impl<'a> Cg<'a> {
    // ------------------------------------------------------------------
    // Small helpers
    // ------------------------------------------------------------------

    fn node(&self, n: u32) -> R<&'a Node> {
        let ast: &'a Ast = self.ast;
        ast.nodes
            .get(n as usize)
            .ok_or(CompileError::Internal("node index out of range"))
    }

    fn child(&self, nd: &Node, i: usize) -> R<u32> {
        nd.children
            .get(i)
            .copied()
            .ok_or(CompileError::Internal("missing child"))
    }

    fn sp(&self, n: u32) -> Span {
        span_of(self.ast, n as usize)
    }

    fn not_yet<T>(&self, feature: &'static str, n: u32) -> R<T> {
        Err(CompileError::NotYetCompiled {
            feature,
            span: self.sp(n),
        })
    }

    fn emit(&mut self, i: Instr, sp: Span) -> R<()> {
        if self.f.instrs.len() >= (LIMIT as usize).saturating_sub(2) {
            return Err(CompileError::TooLarge("ops in a function"));
        }
        self.f.instrs.push(i);
        self.f.spans.push(sp);
        Ok(())
    }

    fn alloc(&mut self) -> R<Reg> {
        self.alloc_n(1)
    }

    fn alloc_n(&mut self, n: u32) -> R<Reg> {
        let r = self.f.next_reg;
        let end = r
            .checked_add(n)
            .ok_or(CompileError::TooLarge("registers"))?;
        if end >= LIMIT.saturating_sub(2) {
            return Err(CompileError::TooLarge("registers"));
        }
        self.f.next_reg = end;
        if end > self.f.max_reg {
            self.f.max_reg = end;
        }
        Ok(r)
    }

    fn mark(&self) -> Reg {
        self.f.next_reg
    }

    fn release(&mut self, m: Reg) {
        self.f.next_reg = m;
    }

    fn konst(&mut self, c: Const) -> R<u32> {
        if let Some(&k) = self.f.const_map.get(&c) {
            return Ok(k);
        }
        let k =
            u32::try_from(self.f.consts.len()).map_err(|_| CompileError::TooLarge("constants"))?;
        self.f.consts.push(c.clone());
        self.f.const_map.insert(c, k);
        Ok(k)
    }

    fn str_const(&mut self, s: &str) -> R<u32> {
        self.konst(Const::String(s.encode_utf16().collect()))
    }

    fn ic(&mut self) -> u32 {
        let i = self.f.nics;
        self.f.nics = i.saturating_add(1);
        i
    }

    fn label(&mut self) -> usize {
        self.f.labels.push(None);
        self.f.labels.len().saturating_sub(1)
    }

    fn bind(&mut self, l: usize) -> R<()> {
        let here = u32::try_from(self.f.instrs.len()).map_err(|_| CompileError::TooLarge("ops"))?;
        let slot = self
            .f
            .labels
            .get_mut(l)
            .ok_or(CompileError::Internal("no such label"))?;
        *slot = Some(here);
        Ok(())
    }

    fn is_bound(&self, l: usize) -> bool {
        matches!(self.f.labels.get(l), Some(Some(_)))
    }

    fn label_id(l: usize) -> R<u32> {
        u32::try_from(l).map_err(|_| CompileError::TooLarge("labels"))
    }

    /// A jump to `l`: a back-edge ([`Instr::Loop`]) when `l` is already bound.
    fn jump(&mut self, l: usize, sp: Span) -> R<()> {
        let target = Self::label_id(l)?;
        if self.is_bound(l) {
            self.emit(Instr::Loop { target }, sp)
        } else {
            self.emit(Instr::Jump { target }, sp)
        }
    }

    fn jump_if_false(&mut self, cond: Reg, l: usize, sp: Span) -> R<()> {
        let target = Self::label_id(l)?;
        self.emit(Instr::JumpIfFalse { cond, target }, sp)
    }

    fn jump_if_true(&mut self, cond: Reg, l: usize, sp: Span) -> R<()> {
        let target = Self::label_id(l)?;
        self.emit(Instr::JumpIfTrue { cond, target }, sp)
    }

    fn load_int(&mut self, dst: Reg, v: i32, sp: Span) -> R<()> {
        self.emit(Instr::LoadInt { dst, imm: v }, sp)
    }

    fn name_units(&self, name: u32) -> R<Vec<u16>> {
        let cps = self
            .an
            .names
            .get(name as usize)
            .ok_or(CompileError::Internal("no such name"))?;
        Ok(literal::to_utf16(cps))
    }

    fn name_of(&self, n: u32) -> u32 {
        self.an.name_of.get(n as usize).copied().unwrap_or(NONE)
    }

    fn res(&self, n: u32) -> u32 {
        self.an.res.get(n as usize).copied().unwrap_or(NONE)
    }

    /// `n` with parentheses removed (§13.2.9: a parenthesized reference is the
    /// same reference).
    fn unparen(&self, mut n: u32) -> R<u32> {
        loop {
            let nd = self.node(n)?;
            if nd.kind == NodeKind::ParenthesizedExpression {
                n = self.child(nd, 0)?;
            } else {
                return Ok(n);
            }
        }
    }

    // ------------------------------------------------------------------
    // Environments and bindings
    // ------------------------------------------------------------------

    fn scope(&self, s: u32) -> R<&'a scope::Scope> {
        let an: &'a Analysis = self.an;
        an.scopes
            .get(s as usize)
            .ok_or(CompileError::Internal("no such scope"))
    }

    fn binding(&self, b: u32) -> R<&'a scope::Binding> {
        let an: &'a Analysis = self.an;
        an.bindings
            .get(b as usize)
            .ok_or(CompileError::Internal("no such binding"))
    }

    fn cur_func_index(&self) -> R<u32> {
        Ok(self.scope(self.f.cur_scope)?.func)
    }

    /// The register holding the environment of the innermost scope at or
    /// above the current one that creates one (the current environment), or
    /// the function's callee environment if there is none in this function.
    fn current_env_reg(&self) -> R<Reg> {
        let func = self.cur_func_index()?;
        let mut s = self.f.cur_scope;
        while s != NONE {
            let sc = self.scope(s)?;
            if sc.has_env() {
                if sc.func == func {
                    return self
                        .f
                        .env_regs
                        .get(&s)
                        .copied()
                        .ok_or(CompileError::Internal("scope has no environment register"));
                }
                return Ok(self.f.base_env);
            }
            s = sc.parent;
        }
        Ok(self.f.base_env)
    }

    /// A register holding the environment object that has binding `b`'s slot.
    /// Emits `GetEnvParent` into a fresh temporary for each scope that creates
    /// an environment between the current scope and `b`'s (§9.1.2.1
    /// GetIdentifierReference step 3: the outer environment). The caller
    /// releases the temporary with `mark`/`release`.
    fn env_for(&mut self, b: u32, sp: Span) -> R<Reg> {
        let target = self.binding(b)?.scope;
        let func = self.cur_func_index()?;
        let mut s = self.f.cur_scope;
        let mut hops: u32 = 0;
        let mut start: Option<Reg> = None;
        loop {
            if s == NONE {
                return Err(CompileError::Internal("binding's scope is not an ancestor"));
            }
            let sc = self.scope(s)?;
            if sc.has_env() {
                if start.is_none() {
                    start = Some(if sc.func == func {
                        self.f
                            .env_regs
                            .get(&s)
                            .copied()
                            .ok_or(CompileError::Internal("scope has no environment register"))?
                    } else {
                        self.f.base_env
                    });
                }
                if s != target {
                    hops = hops.saturating_add(1);
                }
            }
            if s == target {
                break;
            }
            s = sc.parent;
        }
        let mut reg = start.ok_or(CompileError::Internal(
            "captured binding in a scope without an environment",
        ))?;
        if hops > 0 {
            let t = self.alloc()?;
            let mut from = reg;
            for _ in 0..hops {
                self.emit(Instr::GetEnvParent { dst: t, env: from }, sp)?;
                from = t;
            }
            reg = t;
        }
        Ok(reg)
    }

    /// The register of a binding that is not captured.
    fn reg_of(&self, b: u32) -> R<Reg> {
        self.loc
            .get(b as usize)
            .copied()
            .flatten()
            .ok_or(CompileError::Internal("binding has no register"))
    }

    /// Whether a reference at `refpos` to the `let` or `const` binding `b`
    /// needs the TDZ check (module header).
    fn needs_tdz(&self, b: u32, refpos: usize) -> R<bool> {
        let bd = self.binding(b)?;
        if !matches!(bd.kind, BKind::Let | BKind::Const) || bd.decl_fn != NONE {
            return Ok(false);
        }
        let same_fn = self.cur_func_index()? == self.scope(bd.scope)?.func;
        let in_switch = self.scope(bd.scope)?.kind == SKind::Switch;
        Ok(!(same_fn && refpos >= bd.init_end && !in_switch))
    }

    /// A binding that a read or a write needs no check or environment for.
    fn simple_local(&self, n: u32) -> R<Option<Reg>> {
        let b = self.res(n);
        if b == NONE {
            return Ok(None);
        }
        let bd = self.binding(b)?;
        if bd.captured || matches!(bd.kind, BKind::Const | BKind::FuncName | BKind::This) {
            return Ok(None);
        }
        let start = self.node(n)?.start;
        if self.needs_tdz(b, start)? {
            return Ok(None);
        }
        Ok(Some(self.reg_of(b)?))
    }

    /// `dst := value of binding b`, referenced at `refpos`.
    fn read_binding(&mut self, b: u32, refpos: usize, dst: Reg, sp: Span) -> R<()> {
        let bd = self.binding(b)?;
        let tdz = self.needs_tdz(b, refpos)?;
        if bd.captured {
            let m = self.mark();
            let env = self.env_for(b, sp)?;
            self.emit(
                Instr::GetEnvSlot {
                    dst,
                    env,
                    idx: bd.slot,
                },
                sp,
            )?;
            self.release(m);
            if tdz {
                // §9.1.1.1.6 step 2: an uninitialized binding is a ReferenceError.
                self.emit(Instr::ThrowIfHole { src: dst }, sp)?;
            }
        } else {
            let r = self.reg_of(b)?;
            if tdz {
                self.emit(Instr::ThrowIfHole { src: r }, sp)?;
            }
            if r != dst {
                self.emit(Instr::Move { dst, src: r }, sp)?;
            }
        }
        Ok(())
    }

    /// Initializes binding `b` (a declaration's initialization: no TDZ check,
    /// and the `const` rule does not apply).
    fn init_binding(&mut self, b: u32, src: Reg, sp: Span) -> R<()> {
        let bd = self.binding(b)?;
        if bd.captured {
            let m = self.mark();
            let env = self.env_for(b, sp)?;
            self.emit(
                Instr::SetEnvSlot {
                    env,
                    idx: bd.slot,
                    src,
                },
                sp,
            )?;
            self.release(m);
        } else {
            let r = self.reg_of(b)?;
            if r != src {
                self.emit(Instr::Move { dst: r, src }, sp)?;
            }
        }
        Ok(())
    }

    fn throw_error(&mut self, kind: ErrorKind, msg: &str, sp: Span) -> R<()> {
        let k = self.str_const(msg)?;
        self.emit(Instr::ThrowError { kind, msg: k }, sp)
    }

    /// Assigns `src` to binding `b`, referenced at `refpos`:
    /// §9.1.1.1.5 SetMutableBinding (step 3 TDZ; step 5 the immutable case)
    /// and §15.2.5 for a function expression's own name.
    fn write_binding(&mut self, b: u32, src: Reg, refpos: usize, sp: Span) -> R<()> {
        let bd = self.binding(b)?;
        let tdz = self.needs_tdz(b, refpos)?;
        match bd.kind {
            BKind::Const => {
                if tdz {
                    self.check_hole(b, sp)?;
                }
                self.throw_error(ErrorKind::TypeError, "Assignment to constant variable.", sp)
            }
            BKind::FuncName => {
                if self.f.strict {
                    self.throw_error(ErrorKind::TypeError, "Assignment to constant variable.", sp)
                } else {
                    Ok(())
                }
            }
            _ => {
                if tdz {
                    self.check_hole(b, sp)?;
                }
                self.init_binding(b, src, sp)
            }
        }
    }

    /// Throws if binding `b` currently holds the hole.
    fn check_hole(&mut self, b: u32, sp: Span) -> R<()> {
        let bd = self.binding(b)?;
        if bd.captured {
            let m = self.mark();
            let t = self.alloc()?;
            let env = self.env_for(b, sp)?;
            self.emit(
                Instr::GetEnvSlot {
                    dst: t,
                    env,
                    idx: bd.slot,
                },
                sp,
            )?;
            self.emit(Instr::ThrowIfHole { src: t }, sp)?;
            self.release(m);
        } else {
            let r = self.reg_of(b)?;
            self.emit(Instr::ThrowIfHole { src: r }, sp)?;
        }
        Ok(())
    }

    /// `dst := the identifier reference n`: a binding, or a global
    /// (§9.1.2.1 GetIdentifierReference, GetValue §6.2.5.5).
    fn read_ident(&mut self, n: u32, dst: Reg) -> R<()> {
        let sp = self.sp(n);
        let b = self.res(n);
        if b == NONE {
            let name = self.name_of(n);
            let key = self.konst(Const::String(self.name_units(name)?))?;
            let ic = self.ic();
            self.emit(Instr::GetGlobal { dst, key, ic }, sp)
        } else {
            let start = self.node(n)?.start;
            self.read_binding(b, start, dst, sp)
        }
    }

    /// Assigns `src` to the identifier reference `n` (PutValue §6.2.5.6).
    fn write_ident(&mut self, n: u32, src: Reg) -> R<()> {
        let sp = self.sp(n);
        let b = self.res(n);
        if b == NONE {
            let name = self.name_of(n);
            let key = self.konst(Const::String(self.name_units(name)?))?;
            let ic = self.ic();
            self.emit(Instr::SetGlobal { key, src, ic }, sp)
        } else {
            let start = self.node(n)?.start;
            self.write_binding(b, src, start, sp)
        }
    }

    // ------------------------------------------------------------------
    // Scopes
    // ------------------------------------------------------------------

    /// Enters scope `s`: gives its bindings registers or slots, creates its
    /// environment object if it has one, and initializes its bindings:
    /// parameters into captured slots, `var`s to `undefined`, `let` and `const`
    /// to the hole, and hoisted functions (§10.2.11 steps 27 to 36,
    /// §14.2.3 BlockDeclarationInstantiation, §16.1.7).
    fn enter_scope(&mut self, s: u32, sp: Span) -> R<()> {
        let sc = self.scope(s)?;
        let mark = self.mark();
        self.f.scope_marks.push(mark);
        for &b in &sc.bindings {
            let bd = self.binding(b)?;
            if bd.captured {
                continue;
            }
            let r = if sc.kind == SKind::Function && bd.param != NONE {
                bd.param
            } else {
                self.alloc()?
            };
            if let Some(slot) = self.loc.get_mut(b as usize) {
                *slot = Some(r);
            }
        }
        if sc.has_env() {
            let parent = if matches!(sc.kind, SKind::Function | SKind::Script) {
                self.f.base_env
            } else {
                self.current_env_reg()?
            };
            let r = self.alloc()?;
            self.emit(
                Instr::NewEnv {
                    dst: r,
                    parent,
                    size: sc.env_size,
                },
                sp,
            )?;
            self.f.env_regs.insert(s, r);
        }
        self.f.cur_scope = s;
        for &b in &sc.bindings {
            let bd = self.binding(b)?;
            match bd.kind {
                BKind::Var => {
                    if bd.param != NONE {
                        if bd.captured {
                            self.init_binding(b, bd.param, sp)?;
                        }
                    } else if bd.decl_fn == NONE {
                        let m = self.mark();
                        let t = self.alloc()?;
                        self.emit(Instr::LoadUndefined { dst: t }, sp)?;
                        self.init_binding(b, t, sp)?;
                        self.release(m);
                    }
                }
                BKind::Let | BKind::Const => {
                    if bd.decl_fn == NONE && !bd.captured {
                        let r = self.reg_of(b)?;
                        self.emit(Instr::LoadHole { dst: r }, sp)?;
                    }
                }
                BKind::Catch => {}
                BKind::FuncName => {
                    let m = self.mark();
                    let t = self.alloc()?;
                    self.emit(Instr::GetCallee { dst: t }, sp)?;
                    self.init_binding(b, t, sp)?;
                    self.release(m);
                }
                BKind::This => {
                    let m = self.mark();
                    let t = self.alloc()?;
                    self.emit(Instr::GetThis { dst: t }, sp)?;
                    self.init_binding(b, t, sp)?;
                    self.release(m);
                }
            }
        }
        // Hoisted function declarations, in source order.
        for &fnode in &sc.funcs {
            let fnn = self.node(fnode)?;
            let name_node = self.child(fnn, 0)?;
            let name = self.name_of(name_node);
            let m = self.mark();
            // A script's functions were created by `DeclareGlobals` (§16.1.7†
            // step 16), before this prologue.
            if sc.kind != SKind::Script
                && let Some(&b) = sc.names.get(&name)
                && self.binding(b)?.decl_fn == fnode
            {
                let t = self.alloc()?;
                self.make_closure(fnode, t, FunctionKind::Normal)?;
                self.init_binding(b, t, self.sp(fnode))?;
            }
            self.release(m);
        }
        Ok(())
    }

    fn exit_scope(&mut self, s: u32) -> R<()> {
        let sc = self.scope(s)?;
        if let Some(m) = self.f.scope_marks.pop() {
            self.release(m);
        }
        self.f.env_regs.remove(&s);
        self.f.cur_scope = sc.parent;
        Ok(())
    }

    // ------------------------------------------------------------------
    // Functions
    // ------------------------------------------------------------------

    /// Compiles the function (or script) node `fnode` to a new entry of the
    /// program, and returns its index.
    fn compile_function(&mut self, fnode: u32, kind: FunctionKind) -> R<u32> {
        let nd = self.node(fnode)?;
        let sc_id = self
            .an
            .own_scope
            .get(fnode as usize)
            .copied()
            .unwrap_or(NONE);
        let sc = self.scope(sc_id)?;
        let index =
            u32::try_from(self.out.len()).map_err(|_| CompileError::TooLarge("functions"))?;
        self.out.push(None);
        // Parameters, name and body.
        let (nparams, body): (u32, Option<u32>) = match nd.kind {
            NodeKind::Script => (0, None),
            NodeKind::ArrowFunction => {
                let p = self.child(nd, 0)?;
                let pn = self.node(p)?;
                let np = if pn.kind == NodeKind::FormalParameters {
                    pn.children.len()
                } else {
                    1
                };
                (
                    u32::try_from(np).map_err(|_| CompileError::TooLarge("parameters"))?,
                    Some(self.child(nd, 1)?),
                )
            }
            _ => {
                let p = self.child(nd, 1)?;
                let np = self.node(p)?.children.len();
                (
                    u32::try_from(np).map_err(|_| CompileError::TooLarge("parameters"))?,
                    Some(self.child(nd, 2)?),
                )
            }
        };
        let name: Vec<u16> = match nd.kind {
            NodeKind::FunctionDeclaration | NodeKind::FunctionExpression => {
                let nm = self.child(nd, 0)?;
                if self.node(nm)?.kind == NodeKind::BindingIdentifier {
                    self.name_units(self.name_of(nm))?
                } else {
                    Vec::new()
                }
            }
            NodeKind::MethodDefinition => {
                let k = self.child(nd, 0)?;
                let kn = self.node(k)?;
                match kn.kind {
                    NodeKind::IdentifierName => literal::name_units_at(self.src, kn.start)?,
                    NodeKind::StringLiteral => literal::string_at(self.src, kn.start)?,
                    _ => Vec::new(),
                }
            }
            _ => Vec::new(),
        };
        let span = Span {
            start: nd.start,
            end: nd.end,
        };
        let saved = std::mem::replace(&mut self.f, FnState::new(kind, sc.strict, span, nparams));
        let r = self.function_body(nd, sc_id, body);
        let st = std::mem::replace(&mut self.f, saved);
        r?;
        let mut instrs = st.instrs;
        let spans = st.spans;
        // Resolve labels to op indices.
        let labels = st.labels;
        let resolve = |l: usize| -> R<u32> {
            labels
                .get(l)
                .copied()
                .flatten()
                .ok_or(CompileError::Internal("a label was never bound"))
        };
        for i in instrs.iter_mut() {
            if let Some(t) = i.target() {
                let to = resolve(t as usize)?;
                i.set_target(to);
            }
        }
        let mut handlers = Vec::new();
        for (a, b, c) in st.handlers {
            let (start, end, target) = (resolve(a)?, resolve(b)?, resolve(c)?);
            if start < end {
                handlers.push(Handler { start, end, target });
            }
        }
        let code = FunctionCode {
            name,
            kind,
            strict: st.strict,
            span,
            nparams,
            nregs: st.max_reg.saturating_sub(nparams),
            nics: st.nics,
            instrs,
            spans,
            consts: st.consts,
            handlers,
        };
        if let Some(slot) = self.out.get_mut(index as usize) {
            *slot = Some(code);
        }
        Ok(index)
    }

    /// §16.1.7† GlobalDeclarationInstantiation, as the script's first op:
    /// `DeclareGlobals` over a record of the script's `var`s (the
    /// VarScopedDeclarations, step 5), its top-level functions (compiled here,
    /// to templates) and the functions Annex B.3.2.2† hoists out of blocks
    /// (step 12). No op when the script declares none of them. The record's
    /// `lexical` list is empty: the script's top-level `let`, `const` and
    /// `class` are still locals of the script function, not bindings of the
    /// global declarative record (they would need an op that initializes one).
    fn declare_globals(&mut self, sc_id: u32, sp: Span) -> R<()> {
        let sc = self.scope(sc_id)?;
        let mut entries: Vec<(usize, VarScoped)> = Vec::new();
        for &v in &self.an.global_vars {
            let vn = self.node(v)?;
            let name_node = self.child(vn, 0)?;
            let name = self.name_units(self.name_of(name_node))?;
            entries.push((vn.start, VarScoped::Var(name)));
        }
        for &fnode in &sc.funcs {
            let fnn = self.node(fnode)?;
            let name_node = self.child(fnn, 0)?;
            let name = self.name_units(self.name_of(name_node))?;
            let func = self.compile_function(fnode, FunctionKind::Normal)?;
            entries.push((fnn.start, VarScoped::Function { name, func }));
        }
        entries.sort_by_key(|e| e.0);
        let mut annexb: Vec<(usize, Vec<u16>)> = Vec::new();
        for (&fnode, target) in &self.an.annexb {
            if let Target::Global(g) = *target {
                annexb.push((self.node(fnode)?.start, self.name_units(g)?));
            }
        }
        annexb.sort_by_key(|e| e.0);
        let decls = GlobalDecls {
            lexical: Vec::new(),
            var_scoped: entries.into_iter().map(|e| e.1).collect(),
            annexb: annexb.into_iter().map(|e| e.1).collect(),
        };
        if decls.var_scoped.is_empty() && decls.annexb.is_empty() {
            return Ok(());
        }
        let k = self.konst(Const::GlobalDeclarations(decls))?;
        self.emit(Instr::DeclareGlobals { k }, sp)
    }

    /// The prologue, the body and the implicit return of function `nd`.
    fn function_body(&mut self, nd: &Node, sc_id: u32, body: Option<u32>) -> R<()> {
        let span = self.f.span;
        let start = Span {
            start: span.start,
            end: span.start,
        };
        let end = Span {
            start: span.end,
            end: span.end,
        };
        // The environment the closure was created in (§10.2.3 [[Environment]]).
        let base = self.alloc()?;
        self.f.base_env = base;
        if self.f.kind == FunctionKind::Script {
            self.emit(Instr::LoadUndefined { dst: base }, start)?;
        } else {
            self.emit(Instr::GetCalleeEnv { dst: base }, start)?;
        }
        if self.f.kind == FunctionKind::Script {
            self.declare_globals(sc_id, start)?;
        }
        self.enter_scope(sc_id, start)?;
        match nd.kind {
            NodeKind::Script => {
                for &c in &nd.children {
                    self.stmt(c, &[])?;
                }
            }
            _ => {
                let b = body.ok_or(CompileError::Internal("function without a body"))?;
                let bn = self.node(b)?;
                if bn.kind == NodeKind::FunctionBody {
                    for &c in &bn.children {
                        self.stmt(c, &[])?;
                    }
                } else {
                    // An arrow function's expression body (§15.3.4: the body is
                    // returned).
                    let m = self.mark();
                    let r = self.expr_any(b)?;
                    self.emit(Instr::Return { src: r }, self.sp(b))?;
                    self.release(m);
                }
            }
        }
        let m = self.mark();
        let t = self.alloc()?;
        self.emit(Instr::LoadUndefined { dst: t }, end)?;
        self.emit(Instr::Return { src: t }, end)?;
        self.release(m);
        Ok(())
    }

    /// `dst := a closure of the function at fnode`, over the current environment.
    fn make_closure(&mut self, fnode: u32, dst: Reg, kind: FunctionKind) -> R<()> {
        let id = self.compile_function(fnode, kind)?;
        let env = self.current_env_reg()?;
        self.emit(Instr::NewClosure { dst, func: id, env }, self.sp(fnode))
    }

    // ------------------------------------------------------------------
    // Statements
    // ------------------------------------------------------------------

    fn stmts(&mut self, list: &[u32]) -> R<()> {
        for &c in list {
            self.stmt(c, &[])?;
        }
        Ok(())
    }

    /// Compiles statement `n`; `labels` are the labels directly on it.
    fn stmt(&mut self, n: u32, labels: &[u32]) -> R<()> {
        let nd = self.node(n)?;
        let sp = self.sp(n);
        match nd.kind {
            NodeKind::EmptyStatement | NodeKind::DebuggerStatement => Ok(()),
            NodeKind::ExpressionStatement => {
                let e = self.child(nd, 0)?;
                self.expr_to(e, None, true)
            }
            NodeKind::VariableStatement | NodeKind::VariableDeclarationList => {
                for &d in &nd.children {
                    self.var_declaration(d)?;
                }
                Ok(())
            }
            NodeKind::LexicalDeclaration => {
                for &d in &nd.children {
                    self.lexical_binding(d)?;
                }
                Ok(())
            }
            NodeKind::BlockStatement => {
                let s = self.an.own_scope.get(n as usize).copied().unwrap_or(NONE);
                self.enter_scope(s, sp)?;
                self.stmts(&nd.children)?;
                self.exit_scope(s)
            }
            NodeKind::IfStatement => {
                let (test, cons, alt) =
                    (self.child(nd, 0)?, self.child(nd, 1)?, self.child(nd, 2)?);
                let else_l = self.label();
                let m = self.mark();
                let c = self.expr_any(test)?;
                self.jump_if_false(c, else_l, self.sp(test))?;
                self.release(m);
                self.stmt(cons, &[])?;
                if self.node(alt)?.kind == NodeKind::Absent {
                    self.bind(else_l)
                } else {
                    let end_l = self.label();
                    self.jump(end_l, sp)?;
                    self.bind(else_l)?;
                    self.stmt(alt, &[])?;
                    self.bind(end_l)
                }
            }
            NodeKind::WhileStatement => self.while_stmt(nd, sp, labels),
            NodeKind::DoWhileStatement => self.do_while_stmt(nd, sp, labels),
            NodeKind::ForStatement => self.for_stmt(n, nd, sp, labels),
            NodeKind::SwitchStatement => self.switch_stmt(n, nd, sp, labels),
            NodeKind::LabelledStatement => {
                let lab = self.child(nd, 0)?;
                let body = self.child(nd, 1)?;
                let mut all = labels.to_vec();
                all.push(self.name_of(lab));
                let bn = self.node(body)?;
                match bn.kind {
                    NodeKind::WhileStatement
                    | NodeKind::DoWhileStatement
                    | NodeKind::ForStatement
                    | NodeKind::SwitchStatement
                    | NodeKind::LabelledStatement => self.stmt(body, &all),
                    _ => {
                        let brk = self.label();
                        self.f.ctl.push(Ctl::Labelled { labels: all, brk });
                        self.stmt(body, &[])?;
                        self.f.ctl.pop();
                        self.bind(brk)
                    }
                }
            }
            NodeKind::BreakStatement | NodeKind::ContinueStatement => {
                let is_break = nd.kind == NodeKind::BreakStatement;
                let lab = self.child(nd, 0)?;
                let label = if self.node(lab)?.kind == NodeKind::LabelIdentifier {
                    Some(self.name_of(lab))
                } else {
                    None
                };
                let target = self.find_target(is_break, label)?;
                let exit = if is_break {
                    Exit::Break(target)
                } else {
                    Exit::Continue(target)
                };
                self.emit_exit(exit, None, sp)
            }
            NodeKind::ReturnStatement => {
                let e = self.child(nd, 0)?;
                let m = self.mark();
                let r = if self.node(e)?.kind == NodeKind::Absent {
                    let t = self.alloc()?;
                    self.emit(Instr::LoadUndefined { dst: t }, sp)?;
                    t
                } else {
                    self.expr_any(e)?
                };
                self.emit_exit(Exit::Return, Some(r), sp)?;
                self.release(m);
                Ok(())
            }
            NodeKind::ThrowStatement => {
                let e = self.child(nd, 0)?;
                let m = self.mark();
                let r = self.expr_any(e)?;
                self.emit(Instr::Throw { src: r }, sp)?;
                self.release(m);
                Ok(())
            }
            NodeKind::TryStatement => self.try_stmt(nd, sp),
            NodeKind::FunctionDeclaration => self.annexb_copy(n, sp),
            _ => Err(CompileError::Internal("unexpected statement kind")),
        }
    }

    /// `var a = e, b;`: an initializer is an assignment to the name (a `var`
    /// inside a `catch (a)` assigns the parameter: Annex B.3.4).
    fn var_declaration(&mut self, d: u32) -> R<()> {
        let nd = self.node(d)?;
        let (target, init) = (self.child(nd, 0)?, self.child(nd, 1)?);
        if self.node(init)?.kind == NodeKind::Absent {
            return Ok(());
        }
        self.assign_to_ident(target, init, false)
    }

    /// `let a = e, b;` and `const c = e;`: the initialization of the binding
    /// (§14.3.1.2 step 3 InitializeReferencedBinding).
    fn lexical_binding(&mut self, d: u32) -> R<()> {
        let nd = self.node(d)?;
        let (target, init) = (self.child(nd, 0)?, self.child(nd, 1)?);
        if self.node(init)?.kind == NodeKind::Absent {
            // `let a;` initializes to undefined (§14.3.1.2 step 3.b).
            let b = self.res(target);
            let m = self.mark();
            let t = self.alloc()?;
            self.emit(Instr::LoadUndefined { dst: t }, self.sp(d))?;
            self.init_binding(b, t, self.sp(d))?;
            self.release(m);
            return Ok(());
        }
        self.assign_to_ident(target, init, true)
    }

    /// Evaluates `init` and stores it in the binding that identifier `target`
    /// names: initialization if `is_init`, else assignment.
    fn assign_to_ident(&mut self, target: u32, init: u32, is_init: bool) -> R<()> {
        let sp = self.sp(target);
        let b = self.res(target);
        if b != NONE {
            let bd = self.binding(b)?;
            if !bd.captured && (is_init || self.simple_local(target)?.is_some()) {
                let r = self.reg_of(b)?;
                return self.expr_to(init, Some(r), false);
            }
        }
        let m = self.mark();
        let v = self.expr_any(init)?;
        if is_init {
            self.init_binding(b, v, sp)?;
        } else {
            self.write_ident(target, v)?;
        }
        self.release(m);
        Ok(())
    }

    /// Annex B.3.3.1: evaluating a block-level function declaration copies the
    /// block's binding to the variable of the same name.
    fn annexb_copy(&mut self, n: u32, sp: Span) -> R<()> {
        let Some(&target) = self.an.annexb.get(&n) else {
            return Ok(());
        };
        let nd = self.node(n)?;
        let name_node = self.child(nd, 0)?;
        let name = self.name_of(name_node);
        let owner = self.an.owner_scope.get(n as usize).copied().unwrap_or(NONE);
        let block_b = *self
            .scope(owner)?
            .names
            .get(&name)
            .ok_or(CompileError::Internal("block function has no binding"))?;
        let m = self.mark();
        let t = self.alloc()?;
        self.read_binding(block_b, self.node(n)?.end, t, sp)?;
        match target {
            Target::Binding(b) => self.init_binding(b, t, sp)?,
            Target::Global(g) => {
                let key = self.konst(Const::String(self.name_units(g)?))?;
                let ic = self.ic();
                self.emit(Instr::SetGlobal { key, src: t, ic }, sp)?;
            }
        }
        self.release(m);
        Ok(())
    }

    fn while_stmt(&mut self, nd: &Node, sp: Span, labels: &[u32]) -> R<()> {
        let (test, body) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let top = self.label();
        let end = self.label();
        self.bind(top)?;
        let m = self.mark();
        let c = self.expr_any(test)?;
        self.jump_if_false(c, end, self.sp(test))?;
        self.release(m);
        self.f.ctl.push(Ctl::Loop {
            labels: labels.to_vec(),
            brk: end,
            cont: top,
        });
        self.stmt(body, &[])?;
        self.f.ctl.pop();
        self.jump(top, sp)?;
        self.bind(end)
    }

    fn do_while_stmt(&mut self, nd: &Node, sp: Span, labels: &[u32]) -> R<()> {
        let (body, test) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let top = self.label();
        let cont = self.label();
        let end = self.label();
        self.bind(top)?;
        self.f.ctl.push(Ctl::Loop {
            labels: labels.to_vec(),
            brk: end,
            cont,
        });
        self.stmt(body, &[])?;
        self.f.ctl.pop();
        self.bind(cont)?;
        let m = self.mark();
        let c = self.expr_any(test)?;
        self.jump_if_false(c, end, self.sp(test))?;
        self.release(m);
        self.jump(top, sp)?;
        self.bind(end)
    }

    fn for_stmt(&mut self, n: u32, nd: &Node, sp: Span, labels: &[u32]) -> R<()> {
        let (init, test, update, body) = (
            self.child(nd, 0)?,
            self.child(nd, 1)?,
            self.child(nd, 2)?,
            self.child(nd, 3)?,
        );
        let s = self.an.own_scope.get(n as usize).copied().unwrap_or(NONE);
        if s != NONE {
            self.enter_scope(s, sp)?;
        }
        let initn = self.node(init)?;
        match initn.kind {
            NodeKind::Absent => {}
            NodeKind::LexicalDeclaration | NodeKind::VariableDeclarationList => {
                self.stmt(init, &[])?
            }
            _ => self.expr_to(init, None, true)?,
        }
        let per_iteration = s != NONE && self.scope(s)?.has_env();
        if per_iteration {
            self.copy_env(s, sp)?;
        }
        let top = self.label();
        let cont = self.label();
        let end = self.label();
        self.bind(top)?;
        if self.node(test)?.kind != NodeKind::Absent {
            let m = self.mark();
            let c = self.expr_any(test)?;
            self.jump_if_false(c, end, self.sp(test))?;
            self.release(m);
        }
        self.f.ctl.push(Ctl::Loop {
            labels: labels.to_vec(),
            brk: end,
            cont,
        });
        self.stmt(body, &[])?;
        self.f.ctl.pop();
        self.bind(cont)?;
        if per_iteration {
            self.copy_env(s, sp)?;
        }
        if self.node(update)?.kind != NodeKind::Absent {
            self.expr_to(update, None, true)?;
        }
        self.jump(top, sp)?;
        self.bind(end)?;
        if s != NONE {
            self.exit_scope(s)?;
        }
        Ok(())
    }

    /// §14.7.4.4 CreatePerIterationEnvironment: a fresh environment object
    /// with the current values of the loop's bindings, so that a closure made
    /// in one iteration keeps that iteration's values.
    fn copy_env(&mut self, s: u32, sp: Span) -> R<()> {
        let sc = self.scope(s)?;
        let env = *self
            .f
            .env_regs
            .get(&s)
            .ok_or(CompileError::Internal("loop scope has no environment"))?;
        let m = self.mark();
        let parent = self.alloc()?;
        let fresh = self.alloc()?;
        let t = self.alloc()?;
        self.emit(Instr::GetEnvParent { dst: parent, env }, sp)?;
        self.emit(
            Instr::NewEnv {
                dst: fresh,
                parent,
                size: sc.env_size,
            },
            sp,
        )?;
        for &b in &sc.bindings {
            let bd = self.binding(b)?;
            if bd.captured {
                self.emit(
                    Instr::GetEnvSlot {
                        dst: t,
                        env,
                        idx: bd.slot,
                    },
                    sp,
                )?;
                self.emit(
                    Instr::SetEnvSlot {
                        env: fresh,
                        idx: bd.slot,
                        src: t,
                    },
                    sp,
                )?;
            }
        }
        self.emit(
            Instr::Move {
                dst: env,
                src: fresh,
            },
            sp,
        )?;
        self.release(m);
        Ok(())
    }

    /// §14.12.4 CaseBlockEvaluation: the discriminant, the case tests in
    /// order by `===`, then the default clause, then the clauses from the one
    /// chosen on, falling through.
    fn switch_stmt(&mut self, n: u32, nd: &Node, sp: Span, labels: &[u32]) -> R<()> {
        let disc = self.child(nd, 0)?;
        let m = self.mark();
        let d = self.alloc()?;
        self.expr_to(disc, Some(d), true)?;
        let s = self.an.own_scope.get(n as usize).copied().unwrap_or(NONE);
        self.enter_scope(s, sp)?;
        let end = self.label();
        let mut body_labels = Vec::new();
        let mut default_l: Option<usize> = None;
        let clauses: Vec<u32> = nd.children.iter().skip(1).copied().collect();
        for &c in &clauses {
            let l = self.label();
            body_labels.push(l);
            if self.node(c)?.kind == NodeKind::DefaultClause {
                default_l = Some(l);
            }
        }
        for (i, &c) in clauses.iter().enumerate() {
            let cn = self.node(c)?;
            if cn.kind == NodeKind::CaseClause {
                let test = self.child(cn, 0)?;
                let m2 = self.mark();
                let t = self.expr_any(test)?;
                let r = self.alloc()?;
                self.emit(Instr::StrictEq { dst: r, a: d, b: t }, self.sp(test))?;
                let l = *body_labels
                    .get(i)
                    .ok_or(CompileError::Internal("clause label"))?;
                self.jump_if_true(r, l, self.sp(test))?;
                self.release(m2);
            }
        }
        self.jump(default_l.unwrap_or(end), sp)?;
        self.f.ctl.push(Ctl::Switch {
            labels: labels.to_vec(),
            brk: end,
        });
        for (i, &c) in clauses.iter().enumerate() {
            let cn = self.node(c)?;
            self.bind(
                *body_labels
                    .get(i)
                    .ok_or(CompileError::Internal("clause label"))?,
            )?;
            let skip = if cn.kind == NodeKind::CaseClause {
                1
            } else {
                0
            };
            let list: Vec<u32> = cn.children.iter().skip(skip).copied().collect();
            self.stmts(&list)?;
        }
        self.f.ctl.pop();
        self.bind(end)?;
        self.exit_scope(s)?;
        self.release(m);
        Ok(())
    }

    /// The control-stack index a `break` or `continue` (with `label`) goes to.
    fn find_target(&self, is_break: bool, label: Option<u32>) -> R<usize> {
        let mut i = self.f.ctl.len();
        while i > 0 {
            i = i.saturating_sub(1);
            let entry = self
                .f
                .ctl
                .get(i)
                .ok_or(CompileError::Internal("control stack"))?;
            match (entry, label) {
                (Ctl::Loop { .. }, None) => return Ok(i),
                (Ctl::Switch { .. }, None) if is_break => return Ok(i),
                (Ctl::Loop { labels, .. }, Some(l))
                | (Ctl::Switch { labels, .. }, Some(l))
                | (Ctl::Labelled { labels, .. }, Some(l))
                    if labels.contains(&l) && (is_break || matches!(entry, Ctl::Loop { .. })) =>
                {
                    return Ok(i);
                }
                _ => {}
            }
        }
        Err(CompileError::Internal("break or continue without a target"))
    }

    /// A `break`, `continue` or `return` from the current position: a jump to the
    /// target, or, if a `finally` lies between, into it with a code for where to
    /// go afterwards (§14.15.3 and §14.10.1: the finally block runs, then the
    /// completion continues).
    fn emit_exit(&mut self, exit: Exit, val: Option<Reg>, sp: Span) -> R<()> {
        let mut idx = self.f.ctl.len();
        while idx > 0 {
            idx = idx.saturating_sub(1);
            let entry = self
                .f
                .ctl
                .get_mut(idx)
                .ok_or(CompileError::Internal("control stack"))?;
            match entry {
                Ctl::Finally {
                    fin,
                    ctype,
                    cvalue,
                    pending,
                } => {
                    let code = i32::try_from(pending.len().saturating_add(2))
                        .map_err(|_| CompileError::TooLarge("completions of a finally"))?;
                    pending.push(exit);
                    let (fin, ctype, cvalue) = (*fin, *ctype, *cvalue);
                    if let Some(v) = val {
                        self.emit(
                            Instr::Move {
                                dst: cvalue,
                                src: v,
                            },
                            sp,
                        )?;
                    }
                    self.load_int(ctype, code, sp)?;
                    return self.jump(fin, sp);
                }
                Ctl::Loop { brk, cont, .. } => {
                    let target = match exit {
                        Exit::Break(t) if t == idx => Some(*brk),
                        Exit::Continue(t) if t == idx => Some(*cont),
                        _ => None,
                    };
                    if let Some(l) = target {
                        return self.jump(l, sp);
                    }
                }
                Ctl::Switch { brk, .. } | Ctl::Labelled { brk, .. } => {
                    if let Exit::Break(t) = exit
                        && t == idx
                    {
                        let l = *brk;
                        return self.jump(l, sp);
                    }
                }
            }
        }
        match (exit, val) {
            (Exit::Return, Some(v)) => self.emit(Instr::Return { src: v }, sp),
            _ => Err(CompileError::Internal("exit without a target")),
        }
    }

    /// §14.15.3 and §14.15.4: `try` with `catch`, `finally` or both.
    ///
    /// Layout, with the finally parts only if there is a `finally`:
    /// ```text
    /// try block                 <- protected by catch_l (and exc_l)
    /// jump norm
    /// catch_l: GetException; catch block        <- protected by exc_l
    /// jump norm
    /// exc_l: GetException cvalue; ctype := 1; jump fin
    /// norm: ctype := 0
    /// fin: finally block; dispatch on ctype
    /// ```
    fn try_stmt(&mut self, nd: &Node, sp: Span) -> R<()> {
        let (block, catch, fin) = (self.child(nd, 0)?, self.child(nd, 1)?, self.child(nd, 2)?);
        let has_catch = self.node(catch)?.kind == NodeKind::Catch;
        let has_fin = self.node(fin)?.kind == NodeKind::Finally;
        let m = self.mark();
        let (ctype, cvalue) = if has_fin {
            (self.alloc()?, self.alloc()?)
        } else {
            (0, 0)
        };
        let fin_l = self.label();
        let norm_l = self.label();
        if has_fin {
            self.f.ctl.push(Ctl::Finally {
                fin: fin_l,
                ctype,
                cvalue,
                pending: Vec::new(),
            });
        }
        let try_start = self.label();
        let try_end = self.label();
        let catch_l = self.label();
        let catch_end = self.label();
        self.bind(try_start)?;
        self.stmt(block, &[])?;
        self.bind(try_end)?;
        self.jump(norm_l, sp)?;
        if has_catch {
            self.bind(catch_l)?;
            let cn = self.node(catch)?;
            let (param, cblock) = (self.child(cn, 0)?, self.child(cn, 1)?);
            let cs = self
                .an
                .own_scope
                .get(catch as usize)
                .copied()
                .unwrap_or(NONE);
            let m2 = self.mark();
            let e = self.alloc()?;
            self.emit(Instr::GetException { dst: e }, self.sp(catch))?;
            self.enter_scope(cs, self.sp(catch))?;
            if self.node(param)?.kind == NodeKind::BindingIdentifier {
                let name = self.name_of(param);
                if let Some(&b) = self.scope(cs)?.names.get(&name) {
                    self.init_binding(b, e, self.sp(param))?;
                }
            }
            self.stmt(cblock, &[])?;
            self.exit_scope(cs)?;
            self.release(m2);
            self.bind(catch_end)?;
            self.jump(norm_l, sp)?;
            self.f.handlers.push((try_start, try_end, catch_l));
        }
        if has_fin {
            let exc_l = self.label();
            self.bind(exc_l)?;
            self.emit(Instr::GetException { dst: cvalue }, self.sp(fin))?;
            self.load_int(ctype, 1, self.sp(fin))?;
            self.jump(fin_l, self.sp(fin))?;
            let covered_end = if has_catch { catch_end } else { try_end };
            self.f.handlers.push((try_start, covered_end, exc_l));
            self.bind(norm_l)?;
            self.load_int(ctype, 0, self.sp(fin))?;
            self.bind(fin_l)?;
            let pending = match self.f.ctl.pop() {
                Some(Ctl::Finally { pending, .. }) => pending,
                _ => return Err(CompileError::Internal("control stack")),
            };
            let fb = self.child(self.node(fin)?, 0)?;
            self.stmt(fb, &[])?;
            // Dispatch on how the finally was entered: 1 rethrows, each later
            // code continues a `break`, `continue` or `return` from here.
            let fsp = self.sp(fin);
            let m3 = self.mark();
            let k = self.alloc()?;
            let c = self.alloc()?;
            let next = self.label();
            self.load_int(k, 1, fsp)?;
            self.emit(
                Instr::StrictEq {
                    dst: c,
                    a: ctype,
                    b: k,
                },
                fsp,
            )?;
            self.jump_if_false(c, next, fsp)?;
            self.emit(Instr::Throw { src: cvalue }, fsp)?;
            self.bind(next)?;
            for (i, ex) in pending.iter().enumerate() {
                let code = i32::try_from(i.saturating_add(2))
                    .map_err(|_| CompileError::TooLarge("completions"))?;
                let next = self.label();
                self.load_int(k, code, fsp)?;
                self.emit(
                    Instr::StrictEq {
                        dst: c,
                        a: ctype,
                        b: k,
                    },
                    fsp,
                )?;
                self.jump_if_false(c, next, fsp)?;
                let val = if matches!(ex, Exit::Return) {
                    Some(cvalue)
                } else {
                    None
                };
                self.emit_exit(*ex, val, fsp)?;
                self.bind(next)?;
            }
            self.release(m3);
        } else {
            self.bind(norm_l)?;
        }
        self.release(m);
        Ok(())
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    /// Compiles `n` and returns the register holding its value: the register
    /// of a local binding if that is all `n` is, else a fresh temporary
    /// (released by the caller's `release`).
    fn expr_any(&mut self, n: u32) -> R<Reg> {
        let n = self.unparen(n)?;
        let nd = self.node(n)?;
        if nd.kind == NodeKind::IdentifierReference
            && let Some(r) = self.simple_local(n)?
        {
            return Ok(r);
        }
        let t = self.alloc()?;
        self.expr_to(n, Some(t), true)?;
        Ok(t)
    }

    /// As [`Self::expr_any`], for an operand that is evaluated before the
    /// expressions `later`: if one of them can assign a local variable, the
    /// operand's value is copied out of the variable's register first
    /// (§13.15.2 evaluates the left operand before the right).
    fn operand(&mut self, n: u32, later: &[u32]) -> R<Reg> {
        let before = self.mark();
        let r = self.expr_any(n)?;
        if r < before
            && later.iter().any(|&l| {
                self.an
                    .contains_assign
                    .get(l as usize)
                    .copied()
                    .unwrap_or(false)
            })
        {
            let t = self.alloc()?;
            self.emit(Instr::Move { dst: t, src: r }, self.sp(n))?;
            return Ok(t);
        }
        Ok(r)
    }

    /// Compiles `n` into `dst` (`None`: the value is not needed). `early_ok`
    /// says `dst` may be written before `n` has read everything it reads (it
    /// is a temporary); if not, only a kind that writes it last is compiled
    /// straight into it.
    fn expr_to(&mut self, n: u32, dst: Option<Reg>, early_ok: bool) -> R<()> {
        let nd = self.node(n)?;
        let sp = self.sp(n);
        if nd.kind == NodeKind::ParenthesizedExpression {
            let c = self.child(nd, 0)?;
            return self.expr_to(c, dst, early_ok);
        }
        if let Some(d) = dst
            && !early_ok
            && !final_op_kind(nd.kind)
        {
            let m = self.mark();
            let t = self.alloc()?;
            self.expr_to(n, Some(t), true)?;
            self.emit(Instr::Move { dst: d, src: t }, sp)?;
            self.release(m);
            return Ok(());
        }
        match nd.kind {
            NodeKind::AssignmentExpression => return self.assignment(n, nd, dst),
            NodeKind::UpdateExpression => return self.update(n, nd, dst),
            NodeKind::Expression => {
                let last = nd.children.len().saturating_sub(1);
                for (i, &c) in nd.children.iter().enumerate() {
                    if i == last {
                        self.expr_to(c, dst, early_ok)?;
                    } else {
                        self.expr_to(c, None, true)?;
                    }
                }
                return Ok(());
            }
            _ => {}
        }
        let m = self.mark();
        let d = match dst {
            Some(d) => d,
            None => self.alloc()?,
        };
        self.expr_value(n, nd, d, sp)?;
        self.release(m);
        Ok(())
    }

    fn load_number(&mut self, d: Reg, nd: &Node, negate: bool, sp: Span) -> R<()> {
        match literal::number_at(self.src, nd.start, nd.end)? {
            Number::Value(v) => {
                let v = if negate { -v } else { v };
                let is_int = v.fract() == 0.0
                    && v >= f64::from(i32::MIN)
                    && v <= f64::from(i32::MAX)
                    && !(v == 0.0 && v.is_sign_negative());
                if is_int {
                    self.load_int(d, v as i32, sp)
                } else {
                    let k = self.konst(Const::Number(v.to_bits()))?;
                    self.emit(Instr::LoadConst { dst: d, k }, sp)
                }
            }
            Number::BigInt(digits) => {
                let k = self.konst(Const::BigInt(digits))?;
                self.emit(Instr::LoadConst { dst: d, k }, sp)?;
                if negate {
                    self.emit(Instr::Neg { dst: d, src: d }, sp)?;
                }
                Ok(())
            }
        }
    }

    /// Everything but assignment, update and the comma operator, into `d`.
    fn expr_value(&mut self, n: u32, nd: &Node, d: Reg, sp: Span) -> R<()> {
        match nd.kind {
            NodeKind::NumericLiteral => self.load_number(d, nd, false, sp),
            NodeKind::StringLiteral => {
                let units = literal::string_at(self.src, nd.start)?;
                let k = self.konst(Const::String(units))?;
                self.emit(Instr::LoadConst { dst: d, k }, sp)
            }
            NodeKind::NullLiteral => self.emit(Instr::LoadNull { dst: d }, sp),
            NodeKind::BooleanLiteral => {
                let flag = self.src.get(nd.start).copied() == Some(u32::from(b't'));
                self.emit(Instr::LoadBool { dst: d, flag }, sp)
            }
            NodeKind::ThisExpression => {
                let b = self.res(n);
                if b == NONE {
                    self.emit(Instr::GetThis { dst: d }, sp)
                } else {
                    self.read_binding(b, nd.start, d, sp)
                }
            }
            NodeKind::IdentifierReference => self.read_ident(n, d),
            NodeKind::FunctionExpression => self.make_closure(n, d, FunctionKind::Normal),
            NodeKind::ArrowFunction => self.make_closure(n, d, FunctionKind::Arrow),
            NodeKind::MemberExpression => {
                let (obj, prop) = (self.child(nd, 0)?, self.child(nd, 1)?);
                let o = self.operand(obj, &[prop])?;
                match self.property(nd, prop)? {
                    Prop::Named(key) => {
                        let ic = self.ic();
                        self.emit(
                            Instr::GetProp {
                                dst: d,
                                obj: o,
                                key,
                                ic,
                            },
                            sp,
                        )
                    }
                    Prop::Computed(idx) => self.emit(
                        Instr::GetElem {
                            dst: d,
                            obj: o,
                            idx,
                        },
                        sp,
                    ),
                }
            }
            NodeKind::CallExpression => self.call(nd, d, sp),
            NodeKind::NewExpression => self.new_expr(nd, d, sp),
            NodeKind::UnaryExpression => self.unary(nd, d, sp),
            NodeKind::LogicalANDExpression
            | NodeKind::LogicalORExpression
            | NodeKind::CoalesceExpression => {
                let (l, r) = (self.child(nd, 0)?, self.child(nd, 1)?);
                let end = self.label();
                self.expr_to(l, Some(d), true)?;
                match nd.kind {
                    NodeKind::LogicalANDExpression => self.jump_if_false(d, end, sp)?,
                    NodeKind::LogicalORExpression => self.jump_if_true(d, end, sp)?,
                    _ => {
                        let target = Self::label_id(end)?;
                        self.emit(Instr::JumpIfNotNullish { src: d, target }, sp)?;
                    }
                }
                self.expr_to(r, Some(d), true)?;
                self.bind(end)
            }
            NodeKind::ConditionalExpression => {
                let (t, a, b) = (self.child(nd, 0)?, self.child(nd, 1)?, self.child(nd, 2)?);
                let else_l = self.label();
                let end = self.label();
                let m = self.mark();
                let c = self.expr_any(t)?;
                self.jump_if_false(c, else_l, self.sp(t))?;
                self.release(m);
                self.expr_to(a, Some(d), true)?;
                self.jump(end, sp)?;
                self.bind(else_l)?;
                self.expr_to(b, Some(d), true)?;
                self.bind(end)
            }
            NodeKind::ArrayLiteral => self.array_literal(nd, d, sp),
            NodeKind::ObjectLiteral => self.object_literal(nd, d, sp),
            NodeKind::ExponentiationExpression
            | NodeKind::MultiplicativeExpression
            | NodeKind::AdditiveExpression
            | NodeKind::ShiftExpression
            | NodeKind::RelationalExpression
            | NodeKind::EqualityExpression
            | NodeKind::BitwiseANDExpression
            | NodeKind::BitwiseXORExpression
            | NodeKind::BitwiseORExpression => {
                let (l, r) = (self.child(nd, 0)?, self.child(nd, 1)?);
                let m = self.mark();
                let a = self.operand(l, &[r])?;
                let b = self.expr_any(r)?;
                let ins = binary_instr(nd.kind, nd.op, d, a, b)
                    .ok_or(CompileError::Internal("unknown binary operator"))?;
                self.emit(ins, sp)?;
                self.release(m);
                Ok(())
            }
            _ => Err(CompileError::Internal("unexpected expression kind")),
        }
    }

    /// The property of a member expression `nd` whose property child is `prop`.
    fn property(&mut self, nd: &Node, prop: u32) -> R<Prop> {
        match nd.op {
            AOp::Dot => {
                let pn = self.node(prop)?;
                let units = literal::name_units_at(self.src, pn.start)?;
                Ok(Prop::Named(self.konst(Const::String(units))?))
            }
            AOp::Bracket => Ok(Prop::Computed(self.expr_any(prop)?)),
            _ => self.not_yet("private member access", prop),
        }
    }

    fn unary(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let operand = self.child(nd, 0)?;
        let m = self.mark();
        match nd.op {
            AOp::Minus => {
                let on = self.node(operand)?;
                if on.kind == NodeKind::NumericLiteral {
                    return self.load_number(d, on, true, sp);
                }
                let r = self.expr_any(operand)?;
                self.emit(Instr::Neg { dst: d, src: r }, sp)?;
            }
            AOp::Plus => {
                // §13.5.4.1†: "Return ? ToNumber(? GetValue(expr))".
                let r = self.expr_any(operand)?;
                self.emit(Instr::ToNumber { dst: d, src: r }, sp)?;
            }
            AOp::BitNot => {
                let r = self.expr_any(operand)?;
                self.emit(Instr::BitNot { dst: d, src: r }, sp)?;
            }
            AOp::LogicalNot => {
                let r = self.expr_any(operand)?;
                self.emit(Instr::Not { dst: d, src: r }, sp)?;
            }
            AOp::Void => {
                self.expr_to(operand, None, true)?;
                self.emit(Instr::LoadUndefined { dst: d }, sp)?;
            }
            AOp::Typeof => {
                let inner = self.unparen(operand)?;
                if self.node(inner)?.kind == NodeKind::IdentifierReference
                    && self.res(inner) == NONE
                {
                    // §13.5.3.1 step 2.a: `typeof` of an unresolvable reference is
                    // "undefined", and GetGlobal throws for one; step 3 is
                    // GetValue otherwise.
                    let name = self.name_of(inner);
                    let key = self.konst(Const::String(self.name_units(name)?))?;
                    let m = self.mark();
                    let t = self.alloc()?;
                    self.emit(Instr::GetGlobalOrUndefined { dst: t, key }, self.sp(inner))?;
                    self.emit(Instr::TypeOf { dst: d, src: t }, sp)?;
                    self.release(m);
                } else {
                    let r = self.expr_any(operand)?;
                    self.emit(Instr::TypeOf { dst: d, src: r }, sp)?;
                }
            }
            AOp::Delete => {
                let inner = self.unparen(operand)?;
                let inn = self.node(inner)?;
                match inn.kind {
                    NodeKind::MemberExpression => {
                        let (obj, prop) = (self.child(inn, 0)?, self.child(inn, 1)?);
                        let o = self.operand(obj, &[prop])?;
                        let idx = match self.property(inn, prop)? {
                            Prop::Computed(r) => r,
                            Prop::Named(k) => {
                                let r = self.alloc()?;
                                self.emit(Instr::LoadConst { dst: r, k }, sp)?;
                                r
                            }
                        };
                        self.emit(
                            Instr::DeleteProp {
                                dst: d,
                                obj: o,
                                idx,
                            },
                            sp,
                        )?;
                    }
                    NodeKind::IdentifierReference => {
                        return self.not_yet("delete of a variable", inner);
                    }
                    _ => {
                        // §13.5.1.2 step 5: `delete` of a non-reference is true,
                        // after evaluating the operand.
                        self.expr_to(operand, None, true)?;
                        self.emit(Instr::LoadBool { dst: d, flag: true }, sp)?;
                    }
                }
            }
            _ => return Err(CompileError::Internal("unknown unary operator")),
        }
        self.release(m);
        Ok(())
    }

    /// §13.3.6 calls: the callee, `this`, then the arguments in consecutive
    /// registers. A member callee passes its object as `this`
    /// (§13.3.6.1 EvaluateCall step 1: the reference's base).
    fn call(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let (callee, args) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let cn_id = self.unparen(callee)?;
        let cn = self.node(cn_id)?;
        if cn.kind == NodeKind::IdentifierReference
            && callee == cn_id
            && self.eval_name != NONE
            && self.name_of(cn_id) == self.eval_name
        {
            return self.not_yet("direct eval", cn_id);
        }
        let m = self.mark();
        let (fr, this) = (self.alloc()?, self.alloc()?);
        if cn.kind == NodeKind::MemberExpression {
            let (obj, prop) = (self.child(cn, 0)?, self.child(cn, 1)?);
            self.expr_to(obj, Some(this), true)?;
            match self.property(cn, prop)? {
                Prop::Named(key) => {
                    let ic = self.ic();
                    self.emit(
                        Instr::GetProp {
                            dst: fr,
                            obj: this,
                            key,
                            ic,
                        },
                        self.sp(cn_id),
                    )?;
                }
                Prop::Computed(idx) => {
                    self.emit(
                        Instr::GetElem {
                            dst: fr,
                            obj: this,
                            idx,
                        },
                        self.sp(cn_id),
                    )?;
                }
            }
        } else {
            self.expr_to(cn_id, Some(fr), true)?;
            self.emit(Instr::LoadUndefined { dst: this }, sp)?;
        }
        let (base, argc) = self.arguments(args)?;
        self.emit(
            Instr::Call {
                dst: d,
                callee: fr,
                this,
                args: base,
                argc,
            },
            sp,
        )?;
        self.release(m);
        Ok(())
    }

    /// Evaluates an `Arguments` node into consecutive registers: the first
    /// register and the count (`this`'s register is not used: the caller
    /// passes one when there are none).
    fn arguments(&mut self, args: u32) -> R<(Reg, u32)> {
        let an = self.node(args)?;
        let argc =
            u32::try_from(an.children.len()).map_err(|_| CompileError::TooLarge("arguments"))?;
        let base = self.alloc_n(argc)?;
        for (i, &a) in an.children.iter().enumerate() {
            let r = base
                .saturating_add(u32::try_from(i).map_err(|_| CompileError::TooLarge("arguments"))?);
            self.expr_to(a, Some(r), true)?;
        }
        Ok((base, argc))
    }

    /// §13.3.5.1 `new`.
    fn new_expr(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let (callee, args) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let m = self.mark();
        let fr = self.alloc()?;
        self.expr_to(callee, Some(fr), true)?;
        let (base, argc) = if self.node(args)?.kind == NodeKind::Absent {
            (fr, 0)
        } else {
            self.arguments(args)?
        };
        self.emit(
            Instr::New {
                dst: d,
                callee: fr,
                args: base,
                argc,
            },
            sp,
        )?;
        self.release(m);
        Ok(())
    }

    /// §13.2.4.1†: `NewArray` and one `DefineElem` per element
    /// (CreateDataPropertyOrThrow); an elision defines the hole, which the
    /// handler leaves absent.
    fn array_literal(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let len = u32::try_from(nd.children.len())
            .map_err(|_| CompileError::TooLarge("array literal"))?;
        self.emit(Instr::NewArray { dst: d, len }, sp)?;
        for (i, &e) in nd.children.iter().enumerate() {
            let m = self.mark();
            let esp = self.sp(e);
            let idx = self.alloc()?;
            let imm = i32::try_from(i).map_err(|_| CompileError::TooLarge("array literal"))?;
            self.load_int(idx, imm, esp)?;
            let v = if self.node(e)?.kind == NodeKind::Elision {
                let t = self.alloc()?;
                self.emit(Instr::LoadHole { dst: t }, esp)?;
                t
            } else {
                self.expr_any(e)?
            };
            self.emit(
                Instr::DefineElem {
                    obj: d,
                    idx,
                    val: v,
                },
                esp,
            )?;
            self.release(m);
        }
        Ok(())
    }

    /// §13.2.5.4 object literals: `NewObject` and one `DefineProp` or
    /// `DefineElem` per property (§13.2.5.5† step 9, CreateDataPropertyOrThrow,
    /// which does not see a setter or a read-only property on the prototype
    /// chain), and `SetLiteralProto` for `__proto__: value` (step 7).
    fn object_literal(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        self.emit(Instr::NewObject { dst: d }, sp)?;
        for &p in &nd.children {
            let pn = self.node(p)?;
            let psp = self.sp(p);
            let m = self.mark();
            let (key_node, value_node, is_method) = match pn.kind {
                NodeKind::PropertyDefinition => match pn.op {
                    AOp::Shorthand => (self.child(pn, 0)?, self.child(pn, 0)?, false),
                    AOp::KeyValue => (self.child(pn, 0)?, self.child(pn, 1)?, false),
                    _ => return self.not_yet("spread", p),
                },
                NodeKind::MethodDefinition => (self.child(pn, 0)?, p, true),
                _ => return Err(CompileError::Internal("unexpected object literal member")),
            };
            let kn = self.node(key_node)?;
            let plain_key: Option<Vec<u16>> = match kn.kind {
                NodeKind::IdentifierName | NodeKind::IdentifierReference => {
                    Some(literal::name_units_at(self.src, kn.start)?)
                }
                NodeKind::StringLiteral => Some(literal::string_at(self.src, kn.start)?),
                _ => None,
            };
            let proto: Vec<u16> = "__proto__".encode_utf16().collect();
            // §13.2.5.5† step 3: `__proto__: value`, with a non-computed key.
            let is_proto_setter =
                pn.op == AOp::KeyValue && plain_key.as_deref() == Some(proto.as_slice());
            // The key first (§13.2.5.5 PropertyDefinitionEvaluation: the property
            // name is evaluated before the value).
            let key = match plain_key {
                Some(units) => Prop::Named(self.konst(Const::String(units))?),
                None => {
                    let r = self.alloc()?;
                    if kn.kind == NodeKind::NumericLiteral {
                        self.load_number(r, kn, false, self.sp(key_node))?;
                    } else if kn.kind == NodeKind::ComputedPropertyName {
                        let inner = self.child(kn, 0)?;
                        self.expr_to(inner, Some(r), true)?;
                    } else {
                        return Err(CompileError::Internal("unexpected property name"));
                    }
                    Prop::Computed(r)
                }
            };
            let v = if is_method {
                let t = self.alloc()?;
                self.make_closure(p, t, FunctionKind::Method)?;
                t
            } else {
                self.expr_any(value_node)?
            };
            if is_proto_setter {
                self.emit(Instr::SetLiteralProto { obj: d, val: v }, psp)?;
            } else {
                match key {
                    Prop::Named(k) => self.emit(
                        Instr::DefineProp {
                            obj: d,
                            key: k,
                            val: v,
                        },
                        psp,
                    )?,
                    Prop::Computed(idx) => self.emit(
                        Instr::DefineElem {
                            obj: d,
                            idx,
                            val: v,
                        },
                        psp,
                    )?,
                }
            }
            self.release(m);
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Assignment and update
    // ------------------------------------------------------------------

    /// §13.15.2 AssignmentExpression evaluation, for a reference target.
    fn assignment(&mut self, n: u32, nd: &Node, dst: Option<Reg>) -> R<()> {
        let (target, value) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let t = self.unparen(target)?;
        let tn = self.node(t)?;
        let sp = self.sp(n);
        let m = self.mark();
        // The register that ends up holding the assigned value.
        let result: Reg;
        match tn.kind {
            NodeKind::IdentifierReference => {
                if nd.op == AOp::Assign {
                    if let Some(r) = self.simple_local(t)? {
                        self.expr_to(value, Some(r), false)?;
                        result = r;
                    } else {
                        let v = self.alloc()?;
                        self.expr_to(value, Some(v), true)?;
                        self.write_ident(t, v)?;
                        result = v;
                    }
                } else if let Some(short) = Self::logical_assign(nd.op) {
                    let cur = self.alloc()?;
                    self.read_ident(t, cur)?;
                    let end = self.label();
                    self.short_circuit(short, cur, end, sp)?;
                    self.expr_to(value, Some(cur), true)?;
                    self.write_ident(t, cur)?;
                    self.bind(end)?;
                    result = cur;
                } else {
                    // §13.15.2 step 3: the old value is read before the right side.
                    let local = self.simple_local(t)?;
                    let a = match local {
                        Some(r) => {
                            if self
                                .an
                                .contains_assign
                                .get(value as usize)
                                .copied()
                                .unwrap_or(false)
                            {
                                let c = self.alloc()?;
                                self.emit(Instr::Move { dst: c, src: r }, sp)?;
                                c
                            } else {
                                r
                            }
                        }
                        None => {
                            let c = self.alloc()?;
                            self.read_ident(t, c)?;
                            c
                        }
                    };
                    let b = self.expr_any(value)?;
                    let out = match local {
                        Some(r) => r,
                        None => self.alloc()?,
                    };
                    let ins = binary_instr(NodeKind::Script, nd.op, out, a, b)
                        .ok_or(CompileError::Internal("unknown compound assignment"))?;
                    self.emit(ins, sp)?;
                    if local.is_none() {
                        self.write_ident(t, out)?;
                    }
                    result = out;
                }
            }
            NodeKind::MemberExpression if matches!(tn.op, AOp::Dot | AOp::Bracket) => {
                let (obj, prop) = (self.child(tn, 0)?, self.child(tn, 1)?);
                let o = self.operand(obj, &[prop, value])?;
                let key = match self.property(tn, prop)? {
                    Prop::Computed(r) => {
                        // Protect a key held in a variable from the right side.
                        if self
                            .an
                            .contains_assign
                            .get(value as usize)
                            .copied()
                            .unwrap_or(false)
                            && r < m
                        {
                            let c = self.alloc()?;
                            self.emit(Instr::Move { dst: c, src: r }, sp)?;
                            Prop::Computed(c)
                        } else {
                            Prop::Computed(r)
                        }
                    }
                    k => k,
                };
                if nd.op == AOp::Assign {
                    let v = self.alloc()?;
                    self.expr_to(value, Some(v), true)?;
                    self.store_prop(o, &key, v, sp)?;
                    result = v;
                } else if let Some(short) = Self::logical_assign(nd.op) {
                    let cur = self.alloc()?;
                    self.load_prop(cur, o, &key, sp)?;
                    let end = self.label();
                    self.short_circuit(short, cur, end, sp)?;
                    self.expr_to(value, Some(cur), true)?;
                    self.store_prop(o, &key, cur, sp)?;
                    self.bind(end)?;
                    result = cur;
                } else {
                    let cur = self.alloc()?;
                    self.load_prop(cur, o, &key, sp)?;
                    let b = self.expr_any(value)?;
                    let out = self.alloc()?;
                    let ins = binary_instr(NodeKind::Script, nd.op, out, cur, b)
                        .ok_or(CompileError::Internal("unknown compound assignment"))?;
                    self.emit(ins, sp)?;
                    self.store_prop(o, &key, out, sp)?;
                    result = out;
                }
            }
            _ => return self.not_yet("assignment to this kind of target", t),
        }
        if let Some(d) = dst
            && d != result
        {
            self.emit(
                Instr::Move {
                    dst: d,
                    src: result,
                },
                sp,
            )?;
        }
        self.release(m);
        Ok(())
    }

    /// For `&&=`, `||=` and `??=` (§13.15.2 step 4 to 6), how to skip the
    /// assignment.
    fn logical_assign(op: AOp) -> Option<AOp> {
        match op {
            AOp::LogicalAndAssign | AOp::LogicalOrAssign | AOp::CoalesceAssign => Some(op),
            _ => None,
        }
    }

    /// Jumps to `end` if the logical assignment `op` does not assign, given
    /// the current value in `cur`.
    fn short_circuit(&mut self, op: AOp, cur: Reg, end: usize, sp: Span) -> R<()> {
        match op {
            AOp::LogicalAndAssign => self.jump_if_false(cur, end, sp),
            AOp::LogicalOrAssign => self.jump_if_true(cur, end, sp),
            _ => {
                let target = Self::label_id(end)?;
                self.emit(Instr::JumpIfNotNullish { src: cur, target }, sp)
            }
        }
    }

    fn load_prop(&mut self, dst: Reg, obj: Reg, key: &Prop, sp: Span) -> R<()> {
        match *key {
            Prop::Named(key) => {
                let ic = self.ic();
                self.emit(Instr::GetProp { dst, obj, key, ic }, sp)
            }
            Prop::Computed(idx) => self.emit(Instr::GetElem { dst, obj, idx }, sp),
        }
    }

    fn store_prop(&mut self, obj: Reg, key: &Prop, val: Reg, sp: Span) -> R<()> {
        match *key {
            Prop::Named(key) => {
                let ic = self.ic();
                self.emit(Instr::SetProp { obj, key, val, ic }, sp)
            }
            Prop::Computed(idx) => self.emit(Instr::SetElem { obj, idx, val }, sp),
        }
    }

    /// §13.4 update expressions: ToNumeric of the old value, then `Inc` or
    /// `Dec`; the result is the new value for a prefix operator and the
    /// numeric old value for a postfix one.
    fn update(&mut self, n: u32, nd: &Node, dst: Option<Reg>) -> R<()> {
        let operand = self.child(nd, 0)?;
        let t = self.unparen(operand)?;
        let tn = self.node(t)?;
        let sp = self.sp(n);
        let m = self.mark();
        let prefix = matches!(nd.op, AOp::PrefixIncrement | AOp::PrefixDecrement);
        let inc = matches!(nd.op, AOp::PrefixIncrement | AOp::PostfixIncrement);
        let step = |dst: Reg, src: Reg| {
            if inc {
                Instr::Inc { dst, src }
            } else {
                Instr::Dec { dst, src }
            }
        };
        let wanted_old = !prefix && dst.is_some();
        let result: Reg;
        match tn.kind {
            NodeKind::IdentifierReference => {
                if let Some(r) = self.simple_local(t)? {
                    if wanted_old {
                        let old = self.alloc()?;
                        self.emit(Instr::ToNumeric { dst: old, src: r }, sp)?;
                        self.emit(step(r, old), sp)?;
                        result = old;
                    } else {
                        self.emit(step(r, r), sp)?;
                        result = r;
                    }
                } else {
                    let cur = self.alloc()?;
                    self.read_ident(t, cur)?;
                    let (old, new) = self.step_values(cur, wanted_old, &step, sp)?;
                    self.write_ident(t, new)?;
                    result = if prefix { new } else { old };
                }
            }
            NodeKind::MemberExpression if matches!(tn.op, AOp::Dot | AOp::Bracket) => {
                let (obj, prop) = (self.child(tn, 0)?, self.child(tn, 1)?);
                let o = self.operand(obj, &[prop])?;
                let key = self.property(tn, prop)?;
                let cur = self.alloc()?;
                self.load_prop(cur, o, &key, sp)?;
                let (old, new) = self.step_values(cur, wanted_old, &step, sp)?;
                self.store_prop(o, &key, new, sp)?;
                result = if prefix { new } else { old };
            }
            _ => return self.not_yet("update of this kind of target", t),
        }
        if let Some(d) = dst
            && d != result
        {
            self.emit(
                Instr::Move {
                    dst: d,
                    src: result,
                },
                sp,
            )?;
        }
        self.release(m);
        Ok(())
    }

    /// The numeric old value (only if `wanted_old`, else `cur`) and the new
    /// value, as registers.
    fn step_values(
        &mut self,
        cur: Reg,
        wanted_old: bool,
        step: &dyn Fn(Reg, Reg) -> Instr,
        sp: Span,
    ) -> R<(Reg, Reg)> {
        let old = if wanted_old {
            let o = self.alloc()?;
            self.emit(Instr::ToNumeric { dst: o, src: cur }, sp)?;
            o
        } else {
            cur
        };
        let new = self.alloc()?;
        self.emit(step(new, old), sp)?;
        Ok((old, new))
    }
}
