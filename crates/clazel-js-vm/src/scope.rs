//! Scope analysis (phase-7.md item 7.7): which bindings there are, which
//! scope each is in, and which are captured by an inner function.
//!
//! The compiler puts a binding that no inner function refers to in a register,
//! and a captured one in a slot of an environment object that the scope
//! creates when it is entered. Everything here is computed from the arena
//! with loops over it, never recursion, using the arena's order: a child has
//! a smaller index than its parent, so a scan from the last node to the first
//! visits a node after its parent, and a scan from the first to the last
//! visits it after its children.
//!
//! # Scopes
//!
//! - One **function scope** per function holds its parameters, its `var`s, its
//!   function declarations and the `let`, `const` bindings at the top of its
//!   body. When a parameter has an initializer or a computed name
//!   (ECMA-262 §10.2.11 FunctionDeclarationInstantiation step 28), the function
//!   scope holds the parameters only and a **body scope** inside it holds the
//!   body's declarations, so that a closure in a default value does not see them.
//! - The **script scope** holds only the script's top-level `let` and `const`.
//!   Its `var`s and functions are properties of the global object
//!   (§16.1.7 GlobalDeclarationInstantiation) and so have no binding: a
//!   reference to one is a global reference.
//! - Blocks, `for` statements with a lexical declaration, `switch` statements
//!   and `catch` clauses have their own scope, and so does a `with` statement's
//!   body: an object environment (§14.11.2†), whose environment object holds
//!   the object in its one slot.
//! - **Direct eval** (§19.2.1.1†): the code that `eval` runs can name any
//!   binding visible at the call, so each such binding of each enclosing scope is
//!   captured, and the caller's `this`, `new.target`, function and `arguments`
//!   are bindings. A sloppy caller's function scope also has a binding for the
//!   variable object that the `var`s of its eval code become properties of.
//!   A reference that leaves a `with` body or such a function without finding its
//!   name inside first looks in that object (the compiler's `dyn_scopes`).
//! - A named function expression's own name (§15.2.5 step 3, `funcEnv`) is a
//!   binding of its function scope when nothing there declares that name,
//!   which is observationally the same as the standard's extra scope.
//! - An arrow function's `this` is the `this` of the nearest enclosing
//!   non-arrow function (or the script): that function keeps it in a captured
//!   binding, so that no op beyond [`crate::bytecode::Instr::GetThis`] is
//!   needed.
//!
//! # Annex B
//!
//! B.3.3.1: in sloppy mode code a function declared in a block also creates a
//! `var` of its name in the function (or the global object) when no lexical
//! declaration in between would make that an early error and the name is not a
//! parameter. [`Analysis::annexb`] records, for such a declaration, the variable
//! its evaluation copies the block's binding to.

use crate::bytecode::{Flavor, Span};
use crate::compile::CompileError;
use crate::literal;
use clazel_js_syntax::ast::{Ast, Node, NodeKind, Op as AOp};
use std::collections::HashMap;

/// "No scope", "no binding" and "no node": the absent value of an index.
pub const NONE: u32 = u32::MAX;

/// What declared a binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BKind {
    /// A parameter, a `var` or a function declared at the top of a function.
    Var,
    /// A `let` or a function declared in a block: has a temporal dead zone
    /// (a function's is over when its block is entered).
    Let,
    /// A `const`.
    Const,
    /// A `catch` parameter.
    Catch,
    /// A function expression's own name: immutable.
    FuncName,
    /// The `this` an arrow function uses.
    This,
    /// The `this` of a derived class constructor: the hole until `super()`
    /// returns (§9.1.1.3.1† BindThisValue), read with a check.
    DerivedThis,
    /// The `new.target` an arrow function uses.
    NewTarget,
    /// The running function, which an arrow function inside a method reads for
    /// `super` (its home object) and `super()` (its prototype).
    Callee,
    /// The `arguments` object of a non-arrow function.
    Arguments,
    /// A private name (`#x`) of a class, holding its Private Name.
    PrivateName,
    /// A value the compiler keeps for a class: the key of a computed field name
    /// and a private method's function.
    Hidden,
    /// A named or default import (`import { x } from "m"`): an indirect
    /// binding that [`crate::bytecode::Instr::GetImportBinding`] reads and
    /// that cannot be assigned (§9.1.1.5.5† CreateImportBinding).
    Import,
    /// The binding object of a `with` statement's object environment, in slot 0
    /// of the environment object its scope creates (§14.11.2† step 4:
    /// NewObjectEnvironment(obj, true, oldEnv)).
    WithObject,
    /// The variable object of a sloppy function that calls direct eval: a
    /// null-prototype object that the declarations of the eval code become
    /// properties of (§19.2.1.3† EvalDeclarationInstantiation).
    EvalVars,
}

/// A binding.
#[derive(Clone, Debug)]
pub struct Binding {
    /// The interned name.
    pub name: u32,
    /// What declared it.
    pub kind: BKind,
    /// The scope it is in.
    pub scope: u32,
    /// For a parameter, its index (the last, for a repeated name); else [`NONE`].
    pub param: u32,
    /// The function declaration node that initializes it when its scope is
    /// entered, or [`NONE`].
    pub decl_fn: u32,
    /// An inner function refers to it: it lives in an environment object.
    pub captured: bool,
    /// For a `let` or `const`, the end of its declaration: a reference at or
    /// after it in the same function runs after the binding is initialized.
    pub init_end: usize,
    /// For a captured binding, its slot in its scope's environment object.
    pub slot: u32,
}

/// What kind of scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SKind {
    /// The script's.
    Script,
    /// A module's (§16.2.1.6.4† InitializeEnvironment): like a function's, but
    /// every binding is in the module environment object, which the runtime
    /// creates when it links the module and the body runs in.
    Module,
    /// A function's.
    Function,
    /// A block's.
    Block,
    /// A `for` statement's lexical declaration.
    For,
    /// A `switch` statement's case block.
    Switch,
    /// A `catch` clause's parameter.
    Catch,
    /// A class: its inner name binding, its private names and the values the
    /// compiler keeps for its elements (§15.7.14† classScope).
    Class,
    /// A `with` statement's body: an object environment (§14.11.2†), whose
    /// environment object holds the object in slot 0.
    With,
    /// The body of a function whose parameter list has expressions: the
    /// separate environment for the body's `var`s and top-level declarations
    /// (§10.2.11† step 28.f: "varEnv be NewDeclarativeEnvironment(env)"), inside
    /// the function scope that holds the parameters.
    Body,
}

/// A scope.
#[derive(Clone, Debug)]
pub struct Scope {
    /// The enclosing scope, or [`NONE`] for the script's.
    pub parent: u32,
    /// The function (an index into [`Analysis::funcs`]) the scope is in.
    pub func: u32,
    /// What kind of scope.
    pub kind: SKind,
    /// The strictness of the code in it.
    pub strict: bool,
    /// The bindings, in the order they were declared.
    pub bindings: Vec<u32>,
    /// Name to binding.
    pub names: HashMap<u32, u32>,
    /// The function declarations hoisted to the entry of the scope, in source order.
    pub funcs: Vec<u32>,
    /// The number of slots of the environment object the scope creates when it
    /// is entered; 0 means it creates none.
    pub env_size: u32,
}

impl Scope {
    /// Whether the scope creates an environment object.
    pub fn has_env(&self) -> bool {
        self.env_size > 0
    }
}

/// A function.
#[derive(Clone, Debug)]
pub struct Func {
    /// Its node.
    pub node: u32,
    /// Its scope.
    pub scope: u32,
    /// An arrow function.
    pub arrow: bool,
    /// The scope it is created in, or [`NONE`] for the script.
    pub parent_scope: u32,
    /// The constructor of a class with an `extends` clause.
    pub derived_ctor: bool,
}

/// The scopes of a class (a `ClassDeclaration` or `ClassExpression`).
#[derive(Clone, Copy, Debug)]
pub struct ClassInfo {
    /// The class scope.
    pub scope: u32,
    /// The scope of the function that adds the private methods and defines the
    /// fields of each instance (the initializer, §15.7.14† `[[Fields]]`).
    pub inst_scope: u32,
    /// The scope of the function that runs the static fields and static blocks.
    pub static_scope: u32,
}

/// What `this`, `new.target` and the running function are for a node that
/// reads them: a binding, or [`NONE`] to read the frame directly.
#[derive(Clone, Copy, Debug)]
pub struct Special {
    /// The `this` binding.
    pub this_b: u32,
    /// The `new.target` binding.
    pub nt_b: u32,
    /// The running function's binding.
    pub callee_b: u32,
}

/// The variable that evaluating a block-level function declaration also
/// assigns (Annex B.3.3.1).
#[derive(Clone, Copy, Debug)]
pub enum Target {
    /// A binding of the function.
    Binding(u32),
    /// A property of the global object, by interned name.
    Global(u32),
}

/// The result of scope analysis.
#[derive(Debug)]
pub struct Analysis {
    /// Interned names, as code points.
    pub names: Vec<Vec<u32>>,
    /// The scopes: a scope has a smaller index than the scopes inside it.
    pub scopes: Vec<Scope>,
    /// The bindings.
    pub bindings: Vec<Binding>,
    /// The functions; the script is function 0.
    pub funcs: Vec<Func>,
    /// For a node that creates a scope, the scope, else [`NONE`].
    pub own_scope: Vec<u32>,
    /// For a node, the scope it sits in (for a function node, the scope the
    /// function is created in).
    pub owner_scope: Vec<u32>,
    /// For an identifier reference, a binding target of a declaration or an
    /// arrow function's `this`: the binding it names, or [`NONE`] for a
    /// global (or the non-arrow `this`).
    pub res: Vec<u32>,
    /// For an identifier or label node, its interned name, else [`NONE`].
    pub name_of: Vec<u32>,
    /// Block-level function declarations that also assign a variable.
    pub annexb: HashMap<u32, Target>,
    /// The `var` declarations (nodes) directly in the script, outside any
    /// function, in arena order: the global object's variables
    /// (§16.1.7 GlobalDeclarationInstantiation step 10).
    pub global_vars: Vec<u32>,
    /// Whether evaluating the node can assign a variable of the current
    /// function (an assignment or an update, outside inner functions).
    pub contains_assign: Vec<bool>,
    /// For a class node, its scopes.
    pub classes: HashMap<u32, ClassInfo>,
    /// For a `this`, `new.target`, `super.x` or `super()` node, where it reads
    /// them from.
    pub special: HashMap<u32, Special>,
    /// For a class element (a field with a computed name, a private method or
    /// accessor), the binding that keeps its key or function.
    pub hidden: HashMap<u32, u32>,
    /// The script's top-level `let`, `const` and `class` names (interned), each
    /// with whether it is a constant, in source order: bindings of the global
    /// declarative record, not of a scope (§16.1.7† step 13).
    pub global_lexicals: Vec<(u32, bool)>,
    /// For a scope whose references may reach a property of an object before
    /// any binding (a `with` body, or the function scope of sloppy code that
    /// calls direct eval), the binding that holds that object.
    pub dyn_binding: HashMap<u32, u32>,
    /// The direct eval calls (`CallExpression` nodes), in arena order.
    pub eval_calls: Vec<u32>,
    /// For a function declaration that is the body of an `if` clause (Annex
    /// B.3.4†), the block scope it is treated as being in.
    pub implicit_blocks: HashMap<u32, u32>,
    /// The binding `*default*` of an `export default` of an expression, an
    /// anonymous function or an anonymous class, or [`NONE`].
    pub default_binding: u32,
}

/// The node at `i`.
fn node(ast: &Ast, i: usize) -> Result<&Node, CompileError> {
    ast.nodes
        .get(i)
        .ok_or(CompileError::Internal("node index out of range"))
}

/// The span of node `i`.
pub fn span_of(ast: &Ast, i: usize) -> Span {
    match ast.nodes.get(i) {
        Some(n) => Span {
            start: n.start,
            end: n.end,
        },
        None => Span { start: 0, end: 0 },
    }
}

/// Whether the kind creates a function scope.
fn is_function(k: NodeKind) -> bool {
    is_decl_kind(k)
        || is_fexpr_kind(k)
        || is_arrow_kind(k)
        || matches!(k, NodeKind::MethodDefinition | NodeKind::ClassStaticBlock)
}

/// A function declaration of any flavor (§15.2, §15.5, §15.6, §15.8).
pub fn is_decl_kind(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::FunctionDeclaration
            | NodeKind::GeneratorDeclaration
            | NodeKind::AsyncFunctionDeclaration
            | NodeKind::AsyncGeneratorDeclaration
    )
}

/// A function expression of any flavor.
pub fn is_fexpr_kind(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::FunctionExpression
            | NodeKind::GeneratorExpression
            | NodeKind::AsyncFunctionExpression
            | NodeKind::AsyncGeneratorExpression
    )
}

/// An arrow function, async or not (§15.3, §15.9).
pub fn is_arrow_kind(k: NodeKind) -> bool {
    matches!(k, NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction)
}

/// Whether the function node is a generator, an async function or both.
pub fn flavor_of(nd: &Node) -> Flavor {
    match nd.kind {
        NodeKind::GeneratorDeclaration | NodeKind::GeneratorExpression => Flavor::Generator,
        NodeKind::AsyncFunctionDeclaration
        | NodeKind::AsyncFunctionExpression
        | NodeKind::AsyncArrowFunction => Flavor::Async,
        NodeKind::AsyncGeneratorDeclaration | NodeKind::AsyncGeneratorExpression => {
            Flavor::AsyncGenerator
        }
        NodeKind::MethodDefinition => match nd.op {
            AOp::GeneratorMethod => Flavor::Generator,
            AOp::AsyncMethod => Flavor::Async,
            AOp::AsyncGeneratorMethod => Flavor::AsyncGenerator,
            _ => Flavor::Plain,
        },
        _ => Flavor::Plain,
    }
}

/// The `BindingIdentifier` nodes a binding target binds (BoundNames, §8.2.1†):
/// the target itself, or the identifiers of a pattern, in source order,
/// without those inside initializers and computed names.
pub fn bound_idents(ast: &Ast, target: u32) -> Result<Vec<u32>, CompileError> {
    let mut out = Vec::new();
    let mut stack = vec![target];
    while let Some(n) = stack.pop() {
        let nd = node(ast, n as usize)?;
        match nd.kind {
            NodeKind::BindingIdentifier => out.push(n),
            NodeKind::ObjectBindingPattern | NodeKind::ArrayBindingPattern => {
                stack.extend(nd.children.iter().rev().copied());
            }
            NodeKind::BindingProperty => {
                if let Some(&c) = nd.children.last() {
                    stack.push(c);
                }
            }
            NodeKind::BindingElement
            | NodeKind::BindingRestElement
            | NodeKind::BindingRestProperty
            | NodeKind::FunctionRestParameter => {
                if let Some(&c) = nd.children.first() {
                    stack.push(c);
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// Whether a `FormalParameters` node is a simple parameter list (§15.1.1†
/// IsSimpleParameterList): only plain identifiers, no initializer, no rest.
pub fn is_simple_params(ast: &Ast, fp: u32) -> Result<bool, CompileError> {
    for &c in &node(ast, fp as usize)?.children {
        let cn = node(ast, c as usize)?;
        if cn.kind != NodeKind::BindingElement {
            return Ok(false);
        }
        let target = cn.children.first().copied().unwrap_or(NONE);
        let init = cn.children.get(1).copied().unwrap_or(NONE);
        if target == NONE
            || init == NONE
            || node(ast, target as usize)?.kind != NodeKind::BindingIdentifier
            || node(ast, init as usize)?.kind != NodeKind::Absent
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Whether `stmts` start with a Use Strict Directive (§11.2.1): an expression
/// statement that is a string literal written exactly `"use strict"` or
/// `'use strict'`, among the directives that start the list.
fn has_use_strict(ast: &Ast, src: &[u32], stmts: &[u32]) -> Result<bool, CompileError> {
    for &s in stmts {
        let sn = node(ast, s as usize)?;
        if sn.kind != NodeKind::ExpressionStatement {
            return Ok(false);
        }
        let Some(&e) = sn.children.first() else {
            return Ok(false);
        };
        let en = node(ast, e as usize)?;
        if en.kind != NodeKind::StringLiteral {
            return Ok(false);
        }
        let text: Vec<u32> = src.get(en.start..en.end).unwrap_or(&[]).to_vec();
        let a: Vec<u32> = "\"use strict\"".chars().map(u32::from).collect();
        let b: Vec<u32> = "'use strict'".chars().map(u32::from).collect();
        if text == a || text == b {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The analysis in progress.
struct Builder<'a> {
    ast: &'a Ast,
    a: Analysis,
    intern: HashMap<Vec<u32>, u32>,
}

impl Builder<'_> {
    fn intern(&mut self, cps: Vec<u32>) -> Result<u32, CompileError> {
        if let Some(&id) = self.intern.get(&cps) {
            return Ok(id);
        }
        let id = u32::try_from(self.a.names.len()).map_err(|_| CompileError::TooLarge("names"))?;
        self.a.names.push(cps.clone());
        self.intern.insert(cps, id);
        Ok(id)
    }

    fn scope(&self, s: u32) -> Result<&Scope, CompileError> {
        self.a
            .scopes
            .get(s as usize)
            .ok_or(CompileError::Internal("scope index out of range"))
    }

    fn scope_mut(&mut self, s: u32) -> Result<&mut Scope, CompileError> {
        self.a
            .scopes
            .get_mut(s as usize)
            .ok_or(CompileError::Internal("scope index out of range"))
    }

    fn binding_mut(&mut self, b: u32) -> Result<&mut Binding, CompileError> {
        self.a
            .bindings
            .get_mut(b as usize)
            .ok_or(CompileError::Internal("binding index out of range"))
    }

    /// The nearest function or script scope at or above `s`.
    fn fn_scope(&self, mut s: u32) -> Result<u32, CompileError> {
        loop {
            let sc = self.scope(s)?;
            if matches!(
                sc.kind,
                SKind::Function | SKind::Script | SKind::Body | SKind::Module
            ) {
                return Ok(s);
            }
            s = sc.parent;
        }
    }

    /// The binding of `name` in scope `s`, declared as `kind` if there is none.
    fn declare(&mut self, s: u32, name: u32, kind: BKind) -> Result<u32, CompileError> {
        if let Some(&b) = self.scope(s)?.names.get(&name) {
            return Ok(b);
        }
        let b =
            u32::try_from(self.a.bindings.len()).map_err(|_| CompileError::TooLarge("bindings"))?;
        self.a.bindings.push(Binding {
            name,
            kind,
            scope: s,
            param: NONE,
            decl_fn: NONE,
            captured: false,
            init_end: 0,
            slot: 0,
        });
        let sc = self.scope_mut(s)?;
        sc.names.insert(name, b);
        sc.bindings.push(b);
        Ok(b)
    }

    /// Resolves `name` from scope `from`: the binding, marking it captured if
    /// it is in another function, or [`NONE`].
    fn resolve(&mut self, from: u32, name: u32) -> Result<u32, CompileError> {
        let func = self.scope(from)?.func;
        let mut s = from;
        while s != NONE {
            let sc = self.scope(s)?;
            if let Some(&b) = sc.names.get(&name) {
                if sc.func != func {
                    self.binding_mut(b)?.captured = true;
                }
                return Ok(b);
            }
            s = sc.parent;
        }
        Ok(NONE)
    }
}

/// Runs scope analysis over `ast`, whose source text is `src` (code points).
pub fn analyze(ast: &Ast, src: &[u32]) -> Result<Analysis, CompileError> {
    let n = ast.nodes.len();
    let mut parent = vec![NONE; n];
    for (i, nd) in ast.nodes.iter().enumerate() {
        for &c in &nd.children {
            if let Some(p) = parent.get_mut(c as usize) {
                *p = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
            }
        }
    }
    let mut b = Builder {
        ast,
        a: Analysis {
            names: Vec::new(),
            scopes: Vec::new(),
            bindings: Vec::new(),
            funcs: Vec::new(),
            own_scope: vec![NONE; n],
            owner_scope: vec![NONE; n],
            res: vec![NONE; n],
            name_of: vec![NONE; n],
            annexb: HashMap::new(),
            global_vars: Vec::new(),
            contains_assign: vec![false; n],
            classes: HashMap::new(),
            special: HashMap::new(),
            hidden: HashMap::new(),
            global_lexicals: Vec::new(),
            dyn_binding: HashMap::new(),
            eval_calls: Vec::new(),
            implicit_blocks: HashMap::new(),
            default_binding: NONE,
        },
        intern: HashMap::new(),
    };
    names_pass(&mut b, src)?;
    scopes_pass(&mut b, src, &parent)?;
    derived_pass(&mut b, src)?;
    declare_pass(&mut b, &parent)?;
    with_pass(&mut b)?;
    var_arguments_pass(&mut b)?;
    annexb_pass(&mut b)?;
    funcname_pass(&mut b)?;
    reference_pass(&mut b, &parent)?;
    eval_pass(&mut b)?;
    finish_pass(&mut b)?;
    Ok(b.a)
}

/// Interns the name of every identifier and label node.
fn names_pass(b: &mut Builder<'_>, src: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        if matches!(
            nd.kind,
            NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier
        ) {
            let id = {
                let cps = literal::name_at(src, nd.start)?;
                b.intern(cps)?
            };
            if let Some(slot) = b.a.name_of.get_mut(i) {
                *slot = id;
            }
        } else if nd.kind == NodeKind::PrivateIdentifier {
            // A private name is a binding of its class's scope, named `#x`
            // (no identifier can contain a `#`).
            let mut cps = vec![u32::from(b'#')];
            cps.extend(literal::name_at(src, nd.start)?);
            let id = b.intern(cps)?;
            if let Some(slot) = b.a.name_of.get_mut(i) {
                *slot = id;
            }
        }
    }
    Ok(())
}

/// Creates the scopes and functions, parents first.
fn scopes_pass(b: &mut Builder<'_>, src: &[u32], parent: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    let n = ast.nodes.len();
    let mut ctx = vec![NONE; n];
    for i in (0..n).rev() {
        let nd = node(ast, i)?;
        let i32_ = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
        let p = parent.get(i).copied().unwrap_or(NONE);
        let owner = if p == NONE {
            NONE
        } else {
            let pn = node(ast, p as usize)?;
            let outer_first = (matches!(
                pn.kind,
                NodeKind::SwitchStatement | NodeKind::MethodDefinition | NodeKind::WithStatement
            ) || is_decl_kind(pn.kind)
                || is_fexpr_kind(pn.kind))
                && pn.children.first() == Some(&i32_);
            let from = if outer_first { &b.a.owner_scope } else { &ctx };
            let mut o = from.get(p as usize).copied().unwrap_or(NONE);
            // A field's initializer runs in the class's initializer function,
            // and a static block is created there (§15.7.14† steps 31 to 35).
            let field_init =
                pn.kind == NodeKind::FieldDefinition && pn.children.get(1) == Some(&i32_);
            if field_init || nd.kind == NodeKind::ClassStaticBlock {
                let is_static = if field_init { pn.flag } else { true };
                let cb = parent.get(p as usize).copied().unwrap_or(NONE);
                let cls = if cb == NONE {
                    NONE
                } else {
                    parent.get(cb as usize).copied().unwrap_or(NONE)
                };
                if let Some(info) = b.a.classes.get(&cls) {
                    o = if is_static {
                        info.static_scope
                    } else {
                        info.inst_scope
                    };
                }
            }
            o
        };
        // Annex B.3.4†: a function declaration as the body of an `if` is treated
        // as if it were in a block of its own.
        let owner = if nd.kind == NodeKind::FunctionDeclaration
            && p != NONE
            && node(ast, p as usize)?.kind == NodeKind::IfStatement
            && owner != NONE
        {
            let sid =
                u32::try_from(b.a.scopes.len()).map_err(|_| CompileError::TooLarge("scopes"))?;
            let (func, strict) = {
                let os = b.scope(owner)?;
                (os.func, os.strict)
            };
            b.a.scopes.push(Scope {
                parent: owner,
                func,
                kind: SKind::Block,
                strict,
                bindings: Vec::new(),
                names: HashMap::new(),
                funcs: Vec::new(),
                env_size: 0,
            });
            b.a.implicit_blocks.insert(i32_, sid);
            sid
        } else {
            owner
        };
        if let Some(o) = b.a.owner_scope.get_mut(i) {
            *o = owner;
        }
        let kind = match nd.kind {
            NodeKind::Script => Some(SKind::Script),
            NodeKind::Module => Some(SKind::Module),
            k if is_function(k) => Some(SKind::Function),
            NodeKind::BlockStatement => Some(SKind::Block),
            NodeKind::ForStatement => {
                let init = nd.children.first().copied().unwrap_or(NONE);
                if init != NONE && node(ast, init as usize)?.kind == NodeKind::LexicalDeclaration {
                    Some(SKind::For)
                } else {
                    None
                }
            }
            NodeKind::ForInStatement | NodeKind::ForOfStatement => {
                let head = nd.children.first().copied().unwrap_or(NONE);
                if head != NONE
                    && node(ast, head as usize)?.kind == NodeKind::ForDeclaration
                    && node(ast, head as usize)?.op != AOp::Var
                {
                    Some(SKind::For)
                } else {
                    None
                }
            }
            NodeKind::SwitchStatement => Some(SKind::Switch),
            NodeKind::WithStatement => Some(SKind::With),
            NodeKind::FunctionBody if body_scope_needed(ast, parent, i)? => Some(SKind::Body),
            NodeKind::Catch => Some(SKind::Catch),
            NodeKind::ClassDeclaration | NodeKind::ClassExpression => Some(SKind::Class),
            _ => None,
        };
        let mut here = owner;
        if let Some(kind) = kind {
            let sid =
                u32::try_from(b.a.scopes.len()).map_err(|_| CompileError::TooLarge("scopes"))?;
            let inherited_strict = if owner == NONE {
                false
            } else {
                b.scope(owner)?.strict
            };
            let (func, strict) = match kind {
                SKind::Script | SKind::Function => {
                    let fid = u32::try_from(b.a.funcs.len())
                        .map_err(|_| CompileError::TooLarge("functions"))?;
                    let stmts: &[u32] = match nd.kind {
                        NodeKind::Script => &nd.children,
                        _ => match nd.children.last() {
                            Some(&body) => {
                                let bn = node(ast, body as usize)?;
                                if bn.kind == NodeKind::FunctionBody {
                                    &bn.children
                                } else {
                                    &[]
                                }
                            }
                            None => &[],
                        },
                    };
                    let strict = inherited_strict || has_use_strict(ast, src, stmts)?;
                    b.a.funcs.push(Func {
                        node: i32_,
                        scope: sid,
                        arrow: is_arrow_kind(nd.kind),
                        parent_scope: owner,
                        derived_ctor: false,
                    });
                    (fid, strict)
                }
                SKind::Module => {
                    let fid = u32::try_from(b.a.funcs.len())
                        .map_err(|_| CompileError::TooLarge("functions"))?;
                    b.a.funcs.push(Func {
                        node: i32_,
                        scope: sid,
                        arrow: false,
                        parent_scope: owner,
                        derived_ctor: false,
                    });
                    (fid, true)
                }
                SKind::Class => (b.scope(owner)?.func, true),
                _ => (b.scope(owner)?.func, inherited_strict),
            };
            b.a.scopes.push(Scope {
                parent: owner,
                func,
                kind,
                strict,
                bindings: Vec::new(),
                names: HashMap::new(),
                funcs: Vec::new(),
                env_size: 0,
            });
            if let Some(o) = b.a.own_scope.get_mut(i) {
                *o = sid;
            }
            here = sid;
            if kind == SKind::Class {
                // The two synthetic functions of a class: the instance
                // initializer and the static initializer (each its own function
                // scope, inside the class scope).
                let mut made = [NONE; 2];
                for slot in made.iter_mut() {
                    let isid = u32::try_from(b.a.scopes.len())
                        .map_err(|_| CompileError::TooLarge("scopes"))?;
                    let fid = u32::try_from(b.a.funcs.len())
                        .map_err(|_| CompileError::TooLarge("functions"))?;
                    b.a.funcs.push(Func {
                        node: i32_,
                        scope: isid,
                        arrow: false,
                        parent_scope: sid,
                        derived_ctor: false,
                    });
                    b.a.scopes.push(Scope {
                        parent: sid,
                        func: fid,
                        kind: SKind::Function,
                        strict: true,
                        bindings: Vec::new(),
                        names: HashMap::new(),
                        funcs: Vec::new(),
                        env_size: 0,
                    });
                    *slot = isid;
                }
                b.a.classes.insert(
                    i32_,
                    ClassInfo {
                        scope: sid,
                        inst_scope: made[0],
                        static_scope: made[1],
                    },
                );
            }
        }
        if let Some(c) = ctx.get_mut(i) {
            *c = here;
        }
    }
    Ok(())
}

/// Marks the constructors of classes with an `extends` clause.
fn derived_pass(b: &mut Builder<'_>, src: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    for nd in ast.nodes.iter() {
        if !matches!(
            nd.kind,
            NodeKind::ClassDeclaration | NodeKind::ClassExpression
        ) {
            continue;
        }
        let heritage = nd.children.get(1).copied().unwrap_or(NONE);
        if heritage == NONE || node(ast, heritage as usize)?.kind == NodeKind::Absent {
            continue;
        }
        let body = nd.children.get(2).copied().unwrap_or(NONE);
        if body == NONE {
            continue;
        }
        for &m in &node(ast, body as usize)?.children {
            if is_constructor_method(ast, src, m)?
                && let Some(fi) = b.a.funcs.iter().position(|f| f.node == m)
            {
                let fscope = b.a.funcs.get(fi).map(|f| f.scope).unwrap_or(NONE);
                if let Some(f) = b.a.funcs.get_mut(fi) {
                    f.derived_ctor = true;
                }
                // The constructor always has a `this` binding: the hole until
                // `super()` returns, which `return` reads (§10.2.2† step 12).
                let name = b.intern(vec![u32::MAX])?;
                b.declare(fscope, name, BKind::DerivedThis)?;
            }
        }
    }
    Ok(())
}

/// Whether class element `m` is the class's `constructor` method (§15.7.1†
/// ClassElement : MethodDefinition with the PropName "constructor", not
/// static).
pub fn is_constructor_method(ast: &Ast, src: &[u32], m: u32) -> Result<bool, CompileError> {
    let mn = node(ast, m as usize)?;
    if mn.kind != NodeKind::MethodDefinition || mn.flag || mn.op != AOp::Method {
        return Ok(false);
    }
    let Some(&key) = mn.children.first() else {
        return Ok(false);
    };
    let kn = node(ast, key as usize)?;
    let units = match kn.kind {
        NodeKind::IdentifierName => literal::name_units_at(src, kn.start)?,
        NodeKind::StringLiteral => literal::string_at(src, kn.start)?,
        _ => return Ok(false),
    };
    Ok(units.iter().copied().eq("constructor".encode_utf16()))
}

/// Declares every binding: parameters, `var`s, lexical declarations, function
/// declarations, `catch` parameters, the bindings of a class's scope, in
/// arena (so source) order.
fn declare_pass(b: &mut Builder<'_>, parent: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        let owner = b.a.owner_scope.get(i).copied().unwrap_or(NONE);
        let node_id = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
        // The interned name of the first child, if it is a binding identifier.
        let first_name: Option<u32> = match nd.children.first() {
            Some(&t) if node(ast, t as usize)?.kind == NodeKind::BindingIdentifier => {
                b.a.name_of.get(t as usize).copied()
            }
            _ => None,
        };
        match nd.kind {
            NodeKind::BindingIdentifier => {
                // The local names of an import declaration (§16.2.1.6.4†
                // InitializeEnvironment steps 7 and 8).
                let p = parent.get(i).copied().unwrap_or(NONE);
                if p != NONE {
                    let kind = match node(ast, p as usize)?.kind {
                        NodeKind::ImportClause | NodeKind::ImportSpecifier => Some(BKind::Import),
                        NodeKind::NameSpaceImport => Some(BKind::Const),
                        _ => None,
                    };
                    if let (Some(kind), Some(&name)) = (kind, b.a.name_of.get(i)) {
                        b.declare(owner, name, kind)?;
                    }
                }
            }
            NodeKind::ExportDeclaration => {
                // `export default` of an expression or an anonymous class binds
                // `*default*` (§16.2.3.7† ExportDeclaration evaluation).
                let anonymous_class = nd.op == AOp::ExportDefaultClass
                    && match nd.children.first() {
                        Some(&c) => match node(ast, c as usize)?.children.first() {
                            Some(&nm) => {
                                node(ast, nm as usize)?.kind != NodeKind::BindingIdentifier
                            }
                            None => false,
                        },
                        None => false,
                    };
                if nd.op == AOp::ExportDefaultExpression || anonymous_class {
                    let name = b.intern("*default*".chars().map(u32::from).collect())?;
                    let bid = b.declare(owner, name, BKind::Let)?;
                    b.binding_mut(bid)?.init_end = nd.end;
                    b.a.default_binding = bid;
                }
            }
            NodeKind::VariableDeclaration => {
                let Some(&target) = nd.children.first() else {
                    return Err(CompileError::Internal("var declaration has no target"));
                };
                declare_vars(b, owner, target)?;
            }
            NodeKind::ForDeclaration => {
                let Some(&target) = nd.children.first() else {
                    return Err(CompileError::Internal("for declaration has no target"));
                };
                if node(ast, target as usize)?.kind == NodeKind::VariableDeclaration {
                    // Annex B.3.5: declared by the VariableDeclaration itself.
                } else if nd.op == AOp::Var {
                    declare_vars(b, owner, target)?;
                } else {
                    let p = parent.get(i).copied().unwrap_or(NONE);
                    let body_start = if p == NONE {
                        nd.end
                    } else {
                        let body = node(ast, p as usize)?
                            .children
                            .get(2)
                            .copied()
                            .unwrap_or(NONE);
                        node(ast, body as usize)?.start
                    };
                    for id in bound_idents(ast, target)? {
                        let name = b.a.name_of.get(id as usize).copied().unwrap_or(NONE);
                        let kind = if nd.op == AOp::Const {
                            BKind::Const
                        } else {
                            BKind::Let
                        };
                        let bid = b.declare(owner, name, kind)?;
                        b.binding_mut(bid)?.init_end = body_start;
                    }
                }
            }
            NodeKind::LexicalBinding => {
                let Some(&target) = nd.children.first() else {
                    return Err(CompileError::Internal("lexical binding has no target"));
                };
                let is_const = match parent.get(i).copied() {
                    Some(p) if p != NONE => node(ast, p as usize)?.op == AOp::Const,
                    _ => false,
                };
                let at_top = b.scope(owner)?.kind == SKind::Script;
                for id in bound_idents(ast, target)? {
                    let name = b.a.name_of.get(id as usize).copied().unwrap_or(NONE);
                    if at_top {
                        // A top-level lexical declaration binds in the global
                        // declarative record (§16.1.7† step 13), which references
                        // reach as a global.
                        b.a.global_lexicals.push((name, is_const));
                        continue;
                    }
                    let bid = b.declare(
                        owner,
                        name,
                        if is_const { BKind::Const } else { BKind::Let },
                    )?;
                    b.binding_mut(bid)?.init_end = nd.end;
                }
            }
            k if is_decl_kind(k) => {
                // `export default function () {}` binds `*default*`.
                let name = match first_name {
                    Some(n) => n,
                    None => b.intern("*default*".chars().map(u32::from).collect())?,
                };
                let owner_kind = b.scope(owner)?.kind;
                b.scope_mut(owner)?.funcs.push(node_id);
                match owner_kind {
                    SKind::Script => {}
                    SKind::Function | SKind::Body | SKind::Module => {
                        let bid = b.declare(owner, name, BKind::Var)?;
                        b.binding_mut(bid)?.decl_fn = node_id;
                        if first_name.is_none() {
                            b.a.default_binding = bid;
                        }
                    }
                    _ => {
                        let bid = b.declare(owner, name, BKind::Let)?;
                        b.binding_mut(bid)?.decl_fn = node_id;
                    }
                }
            }
            NodeKind::FormalParameters => {
                let simple = is_simple_params(ast, node_id)?;
                for (idx, &el) in nd.children.iter().enumerate() {
                    let en = node(ast, el as usize)?;
                    for id in bound_idents(ast, el)? {
                        let name = b.a.name_of.get(id as usize).copied().unwrap_or(NONE);
                        if simple {
                            let bid = b.declare(owner, name, BKind::Var)?;
                            b.binding_mut(bid)?.param = u32::try_from(idx)
                                .map_err(|_| CompileError::TooLarge("parameters"))?;
                        } else {
                            // A parameter list with initializers or patterns
                            // binds its names in order, each with a temporal
                            // dead zone until its own element has run
                            // (§10.2.11† step 21, IteratorBindingInitialization).
                            let bid = b.declare(owner, name, BKind::Let)?;
                            b.binding_mut(bid)?.init_end = en.end;
                        }
                    }
                }
            }
            k if is_arrow_kind(k) => {
                if let Some(name) = first_name {
                    let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
                    let bid = b.declare(own, name, BKind::Var)?;
                    b.binding_mut(bid)?.param = 0;
                }
            }
            NodeKind::Catch => {
                if let Some(&param) = nd.children.first() {
                    let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
                    for id in bound_idents(ast, param)? {
                        let name = b.a.name_of.get(id as usize).copied().unwrap_or(NONE);
                        b.declare(own, name, BKind::Catch)?;
                    }
                }
            }
            NodeKind::ClassDeclaration | NodeKind::ClassExpression => {
                let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
                if let Some(name) = first_name {
                    if nd.kind == NodeKind::ClassDeclaration {
                        // The declaration's own binding, like a `let`.
                        if b.scope(owner)?.kind == SKind::Script {
                            b.a.global_lexicals.push((name, false));
                        } else {
                            let bid = b.declare(owner, name, BKind::Let)?;
                            b.binding_mut(bid)?.init_end = nd.end;
                        }
                    }
                    // The class's inner name: immutable, in its dead zone until
                    // the class is defined (§15.7.14† step 27).
                    let bid = b.declare(own, name, BKind::Const)?;
                    b.binding_mut(bid)?.init_end = nd.end;
                }
                let Some(&body) = nd.children.get(2) else {
                    return Err(CompileError::Internal("class without a body"));
                };
                for &el in &node(ast, body as usize)?.children {
                    declare_class_element(b, own, el)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Declares the `var` names of a binding target in the function scope (or
/// records them as the global object's variables).
fn declare_vars(b: &mut Builder<'_>, owner: u32, target: u32) -> Result<(), CompileError> {
    let fs = b.fn_scope(owner)?;
    for id in bound_idents(b.ast, target)? {
        let name = b.a.name_of.get(id as usize).copied().unwrap_or(NONE);
        if matches!(
            b.scope(fs)?.kind,
            SKind::Function | SKind::Body | SKind::Module
        ) {
            b.declare(fs, name, BKind::Var)?;
        } else {
            b.a.global_vars.push(id);
        }
    }
    Ok(())
}

/// Declares what class element `el` needs in class scope `own`: a private
/// name, and a hidden binding for a computed field name or a private method.
fn declare_class_element(b: &mut Builder<'_>, own: u32, el: u32) -> Result<(), CompileError> {
    let ast = b.ast;
    let en = node(ast, el as usize)?;
    if !matches!(
        en.kind,
        NodeKind::MethodDefinition | NodeKind::FieldDefinition
    ) {
        return Ok(());
    }
    let key = en.children.first().copied().unwrap_or(NONE);
    if key == NONE {
        return Ok(());
    }
    let kn = node(ast, key as usize)?;
    let hidden_name = b.intern(vec![u32::MAX - 1, el])?;
    match kn.kind {
        NodeKind::PrivateIdentifier => {
            let name = b.a.name_of.get(key as usize).copied().unwrap_or(NONE);
            let bid = b.declare(own, name, BKind::PrivateName)?;
            b.binding_mut(bid)?.captured = true;
            if en.kind == NodeKind::MethodDefinition {
                let h = b.declare(own, hidden_name, BKind::Hidden)?;
                b.binding_mut(h)?.captured = true;
                b.a.hidden.insert(el, h);
            }
        }
        NodeKind::ComputedPropertyName if en.kind == NodeKind::FieldDefinition => {
            let h = b.declare(own, hidden_name, BKind::Hidden)?;
            b.binding_mut(h)?.captured = true;
            b.a.hidden.insert(el, h);
        }
        _ => {}
    }
    Ok(())
}

/// Annex B.3.3.1 for every function declared in a block of sloppy mode code.
fn annexb_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        if nd.kind != NodeKind::FunctionDeclaration {
            continue;
        }
        let owner = b.a.owner_scope.get(i).copied().unwrap_or(NONE);
        let osc = b.scope(owner)?;
        if matches!(
            osc.kind,
            SKind::Script | SKind::Function | SKind::Body | SKind::Module
        ) || osc.strict
        {
            continue;
        }
        let Some(&nm) = nd.children.first() else {
            continue;
        };
        let name = b.a.name_of.get(nm as usize).copied().unwrap_or(NONE);
        // A lexical declaration of the name between the block and the function
        // would make `var name` an early error.
        let mut s = osc.parent;
        let mut blocked = false;
        let fs = loop {
            let sc = b.scope(s)?;
            if matches!(sc.kind, SKind::Function | SKind::Script | SKind::Body) {
                break s;
            }
            if let Some(&bid) = sc.names.get(&name)
                && let Some(bd) = b.a.bindings.get(bid as usize)
                && matches!(bd.kind, BKind::Let | BKind::Const)
            {
                blocked = true;
            }
            s = sc.parent;
        };
        let fsc = b.scope(fs)?;
        // A parameter of that name, or a lexical declaration at the top of the
        // function, stops the hoisting.
        if let Some(&bid) = fsc.names.get(&name)
            && let Some(bd) = b.a.bindings.get(bid as usize)
            && (bd.param != NONE || matches!(bd.kind, BKind::Let | BKind::Const))
        {
            blocked = true;
        }
        // The parameters are in the function scope outside a body scope.
        if fsc.kind == SKind::Body
            && let Some(&bid) = b.scope(fsc.parent)?.names.get(&name)
            && let Some(bd) = b.a.bindings.get(bid as usize)
            && bd.param != NONE
        {
            blocked = true;
        }
        if blocked {
            continue;
        }
        let target = if fsc.kind == SKind::Script {
            Target::Global(name)
        } else {
            Target::Binding(b.declare(fs, name, BKind::Var)?)
        };
        let id = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
        b.a.annexb.insert(id, target);
    }
    Ok(())
}

/// A named function expression's own name, where nothing in the function
/// declares it.
fn funcname_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        if !is_fexpr_kind(nd.kind) {
            continue;
        }
        let Some(&nm) = nd.children.first() else {
            continue;
        };
        if node(ast, nm as usize)?.kind != NodeKind::BindingIdentifier {
            continue;
        }
        let name = b.a.name_of.get(nm as usize).copied().unwrap_or(NONE);
        let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
        if !b.scope(own)?.names.contains_key(&name) {
            b.declare(own, name, BKind::FuncName)?;
        }
    }
    Ok(())
}

/// The function that a `this`, `new.target`, `super` or `arguments` at
/// `owner` belongs to: `(here, home)`, the function the node is in and the
/// nearest enclosing non-arrow function (§9.4.3† GetThisEnvironment).
fn home_func(b: &Builder<'_>, owner: u32) -> Result<(u32, u32), CompileError> {
    let here = b.scope(owner)?.func;
    let mut f = here;
    while let Some(fi) = b.a.funcs.get(f as usize) {
        if fi.arrow {
            f = b.scope(fi.parent_scope)?.func;
        } else {
            break;
        }
    }
    Ok((here, f))
}

/// The binding through which `this` is read at `owner`, or [`NONE`] to read
/// the frame's `this`: needed in an arrow function (the home function keeps
/// `this` in a captured binding) and in a derived constructor (where it is
/// the hole until `super()` returns).
fn this_binding(b: &mut Builder<'_>, owner: u32) -> Result<u32, CompileError> {
    let (here, home) = home_func(b, owner)?;
    let derived =
        b.a.funcs
            .get(home as usize)
            .map(|f| f.derived_ctor)
            .unwrap_or(false);
    if here == home && !derived {
        return Ok(NONE);
    }
    let home_scope =
        b.a.funcs
            .get(home as usize)
            .map(|f| f.scope)
            .unwrap_or(NONE);
    let name = b.intern(vec![u32::MAX])?;
    let kind = if derived {
        BKind::DerivedThis
    } else {
        BKind::This
    };
    let bid = b.declare(home_scope, name, kind)?;
    if here != home {
        b.binding_mut(bid)?.captured = true;
    }
    Ok(bid)
}

/// The captured binding that carries a per-function value (`new.target`, the
/// running function) into an arrow function at `owner`, or [`NONE`] when the
/// node is directly in the function that has it.
fn carried_binding(
    b: &mut Builder<'_>,
    owner: u32,
    tag: u32,
    kind: BKind,
) -> Result<u32, CompileError> {
    let (here, home) = home_func(b, owner)?;
    if here == home {
        return Ok(NONE);
    }
    let home_scope =
        b.a.funcs
            .get(home as usize)
            .map(|f| f.scope)
            .unwrap_or(NONE);
    let name = b.intern(vec![tag])?;
    let bid = b.declare(home_scope, name, kind)?;
    b.binding_mut(bid)?.captured = true;
    Ok(bid)
}

/// `arguments` at `owner`, where ordinary resolution found `r`: the implicit
/// `arguments` binding of the nearest non-arrow function (§10.2.11† step 22),
/// unless a binding of that name is declared between the reference and that
/// function. [`NONE`] at the top level of a script (a global).
fn arguments_binding(b: &mut Builder<'_>, owner: u32, r: u32) -> Result<u32, CompileError> {
    let (here, f) = home_func(b, owner)?;
    if f == 0 {
        return Ok(r);
    }
    if r != NONE {
        let rf =
            b.a.bindings
                .get(r as usize)
                .and_then(|bd| b.a.scopes.get(bd.scope as usize))
                .map(|sc| sc.func)
                .unwrap_or(NONE);
        let mut g = here;
        loop {
            if g == rf {
                return Ok(r);
            }
            if g == f {
                break;
            }
            let Some(fi) = b.a.funcs.get(g as usize) else {
                break;
            };
            g = b.scope(fi.parent_scope)?.func;
        }
    }
    let home_scope = b.a.funcs.get(f as usize).map(|fi| fi.scope).unwrap_or(NONE);
    let name = b.intern("arguments".chars().map(u32::from).collect())?;
    let fresh = !b.scope(home_scope)?.names.contains_key(&name);
    let bid = b.declare(home_scope, name, BKind::Arguments)?;
    if fresh {
        let fnode = b.a.funcs.get(f as usize).map(|fi| fi.node).unwrap_or(NONE);
        capture_mapped_params(b, home_scope, fnode)?;
    }
    if here != f {
        b.binding_mut(bid)?.captured = true;
    }
    Ok(bid)
}

/// Whether the `FunctionBody` node `i` gets a scope of its own, apart from the
/// function's: its function has parameter expressions (§15.1.5†
/// ContainsExpression of the FormalParameters: an initializer, or a computed
/// property name in a pattern), which is when §10.2.11† step 28 makes a separate
/// environment for the body's `var`s, so that a closure in a default value does
/// not see them.
fn body_scope_needed(ast: &Ast, parent: &[u32], i: usize) -> Result<bool, CompileError> {
    let f = parent.get(i).copied().unwrap_or(NONE);
    if f == NONE {
        return Ok(false);
    }
    let fnn = node(ast, f as usize)?;
    if !is_function(fnn.kind) || fnn.children.len() < 2 {
        return Ok(false);
    }
    let Some(&fp) = fnn.children.get(fnn.children.len().saturating_sub(2)) else {
        return Ok(false);
    };
    if node(ast, fp as usize)?.kind != NodeKind::FormalParameters {
        return Ok(false);
    }
    let mut stack = vec![fp];
    while let Some(n) = stack.pop() {
        let nd = node(ast, n as usize)?;
        match nd.kind {
            NodeKind::FormalParameters
            | NodeKind::ObjectBindingPattern
            | NodeKind::ArrayBindingPattern
            | NodeKind::BindingRestElement
            | NodeKind::BindingRestProperty
            | NodeKind::FunctionRestParameter => stack.extend(nd.children.iter().copied()),
            NodeKind::BindingIdentifier | NodeKind::Absent => {}
            NodeKind::BindingElement => {
                if let Some(&init) = nd.children.get(1)
                    && node(ast, init as usize)?.kind != NodeKind::Absent
                {
                    return Ok(true);
                }
                stack.extend(nd.children.first().copied());
            }
            NodeKind::BindingProperty => {
                if nd.children.len() == 2
                    && let Some(&key) = nd.children.first()
                    && node(ast, key as usize)?.kind == NodeKind::ComputedPropertyName
                {
                    return Ok(true);
                }
                stack.extend(nd.children.last().copied());
            }
            _ => return Ok(true),
        }
    }
    Ok(false)
}

/// The binding object of each `with` statement's scope (always captured: the
/// scope's environment object holds it in slot 0).
fn with_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    let name = b.intern(vec![u32::MAX - 5])?;
    for s in 0..b.a.scopes.len() {
        let sid = u32::try_from(s).map_err(|_| CompileError::TooLarge("scopes"))?;
        if b.scope(sid)?.kind != SKind::With {
            continue;
        }
        let bid = b.declare(sid, name, BKind::WithObject)?;
        b.binding_mut(bid)?.captured = true;
        b.a.dyn_binding.insert(sid, bid);
    }
    Ok(())
}

/// §10.2.11† FunctionDeclarationInstantiation step 27.b: a `var arguments` in
/// a function that has an `arguments` object shares its binding (the object
/// is bound to `arguments` in step 22, before the `var`s, which skip a name
/// that is bound already). The function has no parameter, function
/// declaration or lexical declaration of that name; the binding that
/// `declare_pass` made for the `var` becomes the `arguments` binding.
fn var_arguments_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    let arguments = b.intern("arguments".chars().map(u32::from).collect())?;
    for bid in 0..b.a.bindings.len() {
        let bd =
            b.a.bindings
                .get(bid)
                .ok_or(CompileError::Internal("binding"))?;
        if bd.name != arguments || bd.kind != BKind::Var || bd.param != NONE || bd.decl_fn != NONE {
            continue;
        }
        let sc = b.scope(bd.scope)?;
        if !matches!(sc.kind, SKind::Function | SKind::Body) {
            continue;
        }
        let in_body = sc.kind == SKind::Body;
        let Some(f) = b.a.funcs.get(sc.func as usize) else {
            continue;
        };
        let (fnode, fscope, arrow) = (f.node, f.scope, f.arrow);
        if arrow || (!in_body && fscope != bd.scope) {
            continue;
        }
        // The synthetic functions of a class (initializers) and static blocks
        // have no `arguments`.
        let nk = node(b.ast, fnode as usize)?.kind;
        if matches!(
            nk,
            NodeKind::ClassDeclaration | NodeKind::ClassExpression | NodeKind::ClassStaticBlock
        ) {
            continue;
        }
        if in_body {
            // The `arguments` object is bound in the parameter scope (step 22),
            // and the body's `var` of that name starts with its value
            // (step 28.f.i.2: "initialValue be ! env.GetBindingValue(n, false)").
            b.declare(fscope, arguments, BKind::Arguments)?;
            continue;
        }
        let id = u32::try_from(bid).map_err(|_| CompileError::TooLarge("bindings"))?;
        b.binding_mut(id)?.kind = BKind::Arguments;
        capture_mapped_params(b, fscope, fnode)?;
    }
    Ok(())
}

/// A sloppy function with a simple parameter list gets a mapped `arguments`
/// object, whose indices alias the parameters: they live in the environment
/// object (§10.4.4.7†).
fn capture_mapped_params(
    b: &mut Builder<'_>,
    home_scope: u32,
    fnode: u32,
) -> Result<(), CompileError> {
    let strict = b.scope(home_scope)?.strict;
    let simple = match b.ast.nodes.get(fnode as usize) {
        Some(nd) => match nd.children.get(1) {
            Some(&fp) => {
                node(b.ast, fp as usize)?.kind == NodeKind::FormalParameters
                    && is_simple_params(b.ast, fp)?
            }
            None => false,
        },
        None => false,
    };
    if !strict && simple {
        let ids: Vec<u32> = b.scope(home_scope)?.bindings.clone();
        for id in ids {
            let bd = b.binding_mut(id)?;
            if bd.param != NONE {
                bd.captured = true;
            }
        }
    }
    Ok(())
}

/// Direct eval (§13.3.6.1† step 6, §19.2.1.1†): the code that `eval` runs can
/// name any binding visible at the call, by name, and can declare `var`s in the
/// calling function. So every binding of every scope that encloses a direct
/// eval is captured (an environment slot, which the eval code's compiler finds
/// by name through [`crate::bytecode::EvalScopeInfo`]), the caller's `this`,
/// `new.target`, function and `arguments` are bindings too, and a sloppy
/// caller's function scope has a binding for the variable object.
fn eval_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    let ast = b.ast;
    let eval = b.intern("eval".chars().map(u32::from).collect())?;
    let arguments = b.intern("arguments".chars().map(u32::from).collect())?;
    let this_name = b.intern(vec![u32::MAX])?;
    let nt_name = b.intern(vec![u32::MAX - 2])?;
    let callee_name = b.intern(vec![u32::MAX - 3])?;
    let vars_name = b.intern(vec![u32::MAX - 4])?;
    let mut calls: Vec<u32> = Vec::new();
    for (i, nd) in ast.nodes.iter().enumerate() {
        if nd.kind != NodeKind::CallExpression {
            continue;
        }
        let Some(&c) = nd.children.first() else {
            continue;
        };
        if node(ast, c as usize)?.kind == NodeKind::IdentifierReference
            && b.a.name_of.get(c as usize).copied() == Some(eval)
        {
            calls.push(u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?);
        }
    }
    for &i in &calls {
        let owner = b.a.owner_scope.get(i as usize).copied().unwrap_or(NONE);
        let (_, home) = home_func(b, owner)?;
        if home != 0 {
            let (home_scope, home_node, derived) = match b.a.funcs.get(home as usize) {
                Some(f) => (f.scope, f.node, f.derived_ctor),
                None => return Err(CompileError::Internal("no such function")),
            };
            if !derived {
                b.declare(home_scope, this_name, BKind::This)?;
            }
            b.declare(home_scope, nt_name, BKind::NewTarget)?;
            b.declare(home_scope, callee_name, BKind::Callee)?;
            let nk = node(ast, home_node as usize)?.kind;
            if !matches!(
                nk,
                NodeKind::ClassDeclaration | NodeKind::ClassExpression | NodeKind::ClassStaticBlock
            ) {
                let r = b.resolve(owner, arguments)?;
                arguments_binding(b, owner, r)?;
            }
        }
        if !b.scope(owner)?.strict {
            let fs = b.fn_scope(owner)?;
            if matches!(b.scope(fs)?.kind, SKind::Function | SKind::Body) {
                let bid = b.declare(fs, vars_name, BKind::EvalVars)?;
                b.a.dyn_binding.insert(fs, bid);
            }
        }
        b.a.eval_calls.push(i);
    }
    for &i in &calls {
        let mut s = b.a.owner_scope.get(i as usize).copied().unwrap_or(NONE);
        while s != NONE {
            let ids: Vec<u32> = b.scope(s)?.bindings.clone();
            for id in ids {
                b.binding_mut(id)?.captured = true;
            }
            s = b.scope(s)?.parent;
        }
    }
    Ok(())
}

/// Resolves every reference, marking captured bindings.
fn reference_pass(b: &mut Builder<'_>, parent: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    let arguments = b.intern("arguments".chars().map(u32::from).collect())?;
    // The binding identifiers that are targets of a declaration.
    let mut target = vec![false; ast.nodes.len()];
    for nd in ast.nodes.iter() {
        let mut roots: Vec<u32> = Vec::new();
        match nd.kind {
            NodeKind::VariableDeclaration | NodeKind::LexicalBinding | NodeKind::Catch => {
                roots.extend(nd.children.first().copied());
            }
            NodeKind::ForDeclaration => {
                if let Some(&t) = nd.children.first()
                    && node(ast, t as usize)?.kind != NodeKind::VariableDeclaration
                {
                    roots.push(t);
                }
            }
            NodeKind::FormalParameters => roots.extend(nd.children.iter().copied()),
            k if is_arrow_kind(k) => {
                if let Some(&t) = nd.children.first()
                    && node(ast, t as usize)?.kind == NodeKind::BindingIdentifier
                {
                    roots.push(t);
                }
            }
            _ => {}
        }
        for root in roots {
            if node(ast, root as usize)?.kind == NodeKind::Absent {
                continue;
            }
            for id in bound_idents(ast, root)? {
                if let Some(t) = target.get_mut(id as usize) {
                    *t = true;
                }
            }
        }
    }
    let new_target_tag = u32::MAX - 2;
    let callee_tag = u32::MAX - 3;
    for (i, nd) in ast.nodes.iter().enumerate() {
        let owner = b.a.owner_scope.get(i).copied().unwrap_or(NONE);
        let name = b.a.name_of.get(i).copied().unwrap_or(NONE);
        let node_id = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
        let r = match nd.kind {
            NodeKind::IdentifierReference => {
                let r = b.resolve(owner, name)?;
                if name == arguments {
                    arguments_binding(b, owner, r)?
                } else {
                    r
                }
            }
            NodeKind::BindingIdentifier => {
                let p = parent.get(i).copied().unwrap_or(NONE);
                if target.get(i).copied().unwrap_or(false) {
                    b.resolve(owner, name)?
                } else if p != NONE
                    && node(ast, p as usize)?.kind == NodeKind::ClassDeclaration
                    && node(ast, p as usize)?.children.first() == Some(&node_id)
                {
                    // The class declaration's own binding, in the enclosing scope.
                    let outer = b.a.owner_scope.get(p as usize).copied().unwrap_or(NONE);
                    b.resolve(outer, name)?
                } else {
                    NONE
                }
            }
            NodeKind::PrivateIdentifier => b.resolve(owner, name)?,
            NodeKind::ThisExpression => this_binding(b, owner)?,
            NodeKind::NewTarget => carried_binding(b, owner, new_target_tag, BKind::NewTarget)?,
            NodeKind::SuperProperty | NodeKind::SuperCall => {
                let this_b = this_binding(b, owner)?;
                let nt_b = carried_binding(b, owner, new_target_tag, BKind::NewTarget)?;
                let callee_b = carried_binding(b, owner, callee_tag, BKind::Callee)?;
                b.a.special.insert(
                    node_id,
                    Special {
                        this_b,
                        nt_b,
                        callee_b,
                    },
                );
                continue;
            }
            _ => continue,
        };
        if let Some(slot) = b.a.res.get_mut(i) {
            *slot = r;
        }
    }
    Ok(())
}

/// Assigns environment slots, and computes `contains_assign`.
fn finish_pass(b: &mut Builder<'_>) -> Result<(), CompileError> {
    for s in 0..b.a.scopes.len() {
        let ids: Vec<u32> =
            b.a.scopes
                .get(s)
                .map(|sc| sc.bindings.clone())
                .unwrap_or_default();
        // Every binding of a module's scope has a slot of the module
        // environment, so that other modules can reach an export.
        if b.a.scopes.get(s).map(|sc| sc.kind) == Some(SKind::Module) {
            for &bid in &ids {
                b.binding_mut(bid)?.captured = true;
            }
        }
        let mut size: u32 = 0;
        for bid in ids {
            let bd = b.binding_mut(bid)?;
            if bd.captured {
                bd.slot = size;
                size = size
                    .checked_add(1)
                    .ok_or(CompileError::TooLarge("environment"))?;
            }
        }
        if let Some(sc) = b.a.scopes.get_mut(s) {
            sc.env_size = size;
        }
    }
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        let v = if is_function(nd.kind) {
            false
        } else if matches!(
            nd.kind,
            NodeKind::AssignmentExpression | NodeKind::UpdateExpression
        ) {
            true
        } else {
            nd.children.iter().any(|&c| {
                b.a.contains_assign
                    .get(c as usize)
                    .copied()
                    .unwrap_or(false)
            })
        };
        if let Some(slot) = b.a.contains_assign.get_mut(i) {
            *slot = v;
        }
    }
    Ok(())
}
