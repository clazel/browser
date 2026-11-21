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
//!   body. (ECMA-262 §10.2.11 FunctionDeclarationInstantiation uses a separate
//!   environment for the body only when a parameter has an initializer, which
//!   this slice does not compile.)
//! - The **script scope** holds only the script's top-level `let` and `const`.
//!   Its `var`s and functions are properties of the global object
//!   (§16.1.7 GlobalDeclarationInstantiation) and so have no binding: a
//!   reference to one is a global reference.
//! - Blocks, `for` statements with a lexical declaration, `switch` statements
//!   and `catch` clauses have their own scope.
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

use crate::bytecode::Span;
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
    matches!(
        k,
        NodeKind::FunctionDeclaration
            | NodeKind::FunctionExpression
            | NodeKind::ArrowFunction
            | NodeKind::MethodDefinition
    )
}

/// The first construct of the AST this slice of the compiler does not compile,
/// as a "not yet compiled" error; `Ok` if there is none. Checked before
/// anything else, so that a program with such a construct is reported as
/// not yet compiled, never as an internal failure of what follows.
pub fn check_supported(ast: &Ast) -> Result<(), CompileError> {
    for (i, n) in ast.nodes.iter().enumerate() {
        let feature: Option<&'static str> = match n.kind {
            NodeKind::Module
            | NodeKind::ImportDeclaration
            | NodeKind::ImportClause
            | NodeKind::NameSpaceImport
            | NodeKind::NamedImports
            | NodeKind::ImportSpecifier
            | NodeKind::WithClause
            | NodeKind::ImportAttribute
            | NodeKind::ExportDeclaration
            | NodeKind::NamedExports
            | NodeKind::ExportSpecifier
            | NodeKind::ImportMeta => Some("modules"),
            NodeKind::ImportCall => Some("dynamic import"),
            NodeKind::ForInStatement | NodeKind::ForOfStatement | NodeKind::ForDeclaration => {
                Some("for-in and for-of loops")
            }
            NodeKind::WithStatement => Some("with statements"),
            NodeKind::GeneratorDeclaration
            | NodeKind::GeneratorExpression
            | NodeKind::AsyncFunctionDeclaration
            | NodeKind::AsyncFunctionExpression
            | NodeKind::AsyncGeneratorDeclaration
            | NodeKind::AsyncGeneratorExpression
            | NodeKind::AsyncArrowFunction
            | NodeKind::YieldExpression
            | NodeKind::AwaitExpression => Some("generators and async functions"),
            NodeKind::ClassDeclaration
            | NodeKind::ClassExpression
            | NodeKind::ClassBody
            | NodeKind::FieldDefinition
            | NodeKind::ClassStaticBlock
            | NodeKind::SuperProperty
            | NodeKind::SuperCall
            | NodeKind::PrivateIdentifier => Some("classes, super and private names"),
            NodeKind::NewTarget => Some("new.target"),
            NodeKind::ObjectBindingPattern
            | NodeKind::ArrayBindingPattern
            | NodeKind::BindingProperty
            | NodeKind::BindingRestElement
            | NodeKind::BindingRestProperty
            | NodeKind::ObjectAssignmentPattern
            | NodeKind::ArrayAssignmentPattern
            | NodeKind::AssignmentProperty
            | NodeKind::AssignmentElement
            | NodeKind::AssignmentRestElement
            | NodeKind::AssignmentRestProperty
            | NodeKind::CoverInitializedName => Some("destructuring"),
            NodeKind::FunctionRestParameter => Some("rest parameters"),
            NodeKind::SpreadElement => Some("spread"),
            NodeKind::TemplateLiteral | NodeKind::TemplateElement | NodeKind::TaggedTemplate => {
                Some("template literals")
            }
            NodeKind::RegularExpressionLiteral => Some("regular expression literals"),
            NodeKind::OptionalExpression | NodeKind::OptionalChain => Some("optional chaining"),
            NodeKind::PropertyDefinition if n.op == AOp::Spread => Some("spread"),
            NodeKind::MethodDefinition if n.op != AOp::Method => {
                Some("accessors and generator or async methods")
            }
            NodeKind::BindingElement => {
                // A parameter's initializer (a binding element elsewhere is in a
                // pattern, which is reported above).
                match n.children.get(1) {
                    Some(&c) if node(ast, c as usize)?.kind != NodeKind::Absent => {
                        Some("default parameter values")
                    }
                    _ => None,
                }
            }
            NodeKind::IfStatement | NodeKind::LabelledStatement => {
                // Annex B.3.2: a function declaration as the body of an `if` or a
                // label.
                let mut found = false;
                for &c in &n.children {
                    if node(ast, c as usize)?.kind == NodeKind::FunctionDeclaration {
                        found = true;
                    }
                }
                if found {
                    Some("a function declaration as the body of an if or a label")
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(feature) = feature {
            return Err(CompileError::NotYetCompiled {
                feature,
                span: span_of(ast, i),
            });
        }
    }
    Ok(())
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
            if matches!(sc.kind, SKind::Function | SKind::Script) {
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
        },
        intern: HashMap::new(),
    };
    names_pass(&mut b, src)?;
    scopes_pass(&mut b, src, &parent)?;
    declare_pass(&mut b, &parent)?;
    annexb_pass(&mut b)?;
    funcname_pass(&mut b)?;
    reference_pass(&mut b, &parent)?;
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
            let outer_first = matches!(
                pn.kind,
                NodeKind::SwitchStatement
                    | NodeKind::FunctionDeclaration
                    | NodeKind::FunctionExpression
                    | NodeKind::MethodDefinition
            ) && pn.children.first() == Some(&i32_);
            let from = if outer_first { &b.a.owner_scope } else { &ctx };
            from.get(p as usize).copied().unwrap_or(NONE)
        };
        if let Some(o) = b.a.owner_scope.get_mut(i) {
            *o = owner;
        }
        let kind = match nd.kind {
            NodeKind::Script => Some(SKind::Script),
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
            NodeKind::SwitchStatement => Some(SKind::Switch),
            NodeKind::Catch => Some(SKind::Catch),
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
                        arrow: nd.kind == NodeKind::ArrowFunction,
                        parent_scope: owner,
                    });
                    (fid, strict)
                }
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
        }
        if let Some(c) = ctx.get_mut(i) {
            *c = here;
        }
    }
    Ok(())
}

/// Declares every binding: parameters, `var`s, lexical declarations, function
/// declarations and `catch` parameters, in arena (so source) order.
fn declare_pass(b: &mut Builder<'_>, parent: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    for (i, nd) in ast.nodes.iter().enumerate() {
        let owner = b.a.owner_scope.get(i).copied().unwrap_or(NONE);
        // The interned name of the first child, if it is a binding identifier.
        let first_name: Option<u32> = match nd.children.first() {
            Some(&t) if node(ast, t as usize)?.kind == NodeKind::BindingIdentifier => {
                b.a.name_of.get(t as usize).copied()
            }
            _ => None,
        };
        match nd.kind {
            NodeKind::VariableDeclaration => {
                let Some(name) = first_name else {
                    return Err(CompileError::Internal("var target is not an identifier"));
                };
                let fs = b.fn_scope(owner)?;
                if b.scope(fs)?.kind == SKind::Function {
                    b.declare(fs, name, BKind::Var)?;
                } else {
                    let id = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
                    b.a.global_vars.push(id);
                }
            }
            NodeKind::LexicalBinding => {
                let Some(name) = first_name else {
                    return Err(CompileError::Internal(
                        "lexical target is not an identifier",
                    ));
                };
                let is_const = match parent.get(i).copied() {
                    Some(p) if p != NONE => node(ast, p as usize)?.op == AOp::Const,
                    _ => false,
                };
                let bid = b.declare(
                    owner,
                    name,
                    if is_const { BKind::Const } else { BKind::Let },
                )?;
                b.binding_mut(bid)?.init_end = nd.end;
            }
            NodeKind::FunctionDeclaration => {
                let Some(name) = first_name else {
                    return Err(CompileError::Internal("function declaration has no name"));
                };
                let owner_kind = b.scope(owner)?.kind;
                let node_id = u32::try_from(i).map_err(|_| CompileError::TooLarge("nodes"))?;
                b.scope_mut(owner)?.funcs.push(node_id);
                match owner_kind {
                    SKind::Script => {}
                    SKind::Function => {
                        let bid = b.declare(owner, name, BKind::Var)?;
                        b.binding_mut(bid)?.decl_fn = node_id;
                    }
                    _ => {
                        let bid = b.declare(owner, name, BKind::Let)?;
                        b.binding_mut(bid)?.decl_fn = node_id;
                    }
                }
            }
            NodeKind::BindingElement => {
                let p = parent.get(i).copied().unwrap_or(NONE);
                if p != NONE && node(ast, p as usize)?.kind == NodeKind::FormalParameters {
                    let pn = node(ast, p as usize)?;
                    let idx = pn
                        .children
                        .iter()
                        .position(|&c| c as usize == i)
                        .unwrap_or(0);
                    let Some(name) = first_name else {
                        return Err(CompileError::Internal("parameter is not an identifier"));
                    };
                    let bid = b.declare(owner, name, BKind::Var)?;
                    b.binding_mut(bid)?.param =
                        u32::try_from(idx).map_err(|_| CompileError::TooLarge("parameters"))?;
                }
            }
            NodeKind::ArrowFunction => {
                if let Some(name) = first_name {
                    let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
                    let bid = b.declare(own, name, BKind::Var)?;
                    b.binding_mut(bid)?.param = 0;
                }
            }
            NodeKind::Catch => {
                if let Some(name) = first_name {
                    let own = b.a.own_scope.get(i).copied().unwrap_or(NONE);
                    b.declare(own, name, BKind::Catch)?;
                }
            }
            _ => {}
        }
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
        if matches!(osc.kind, SKind::Script | SKind::Function) || osc.strict {
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
            if matches!(sc.kind, SKind::Function | SKind::Script) {
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
        if nd.kind != NodeKind::FunctionExpression {
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

/// Resolves every reference, marking captured bindings.
fn reference_pass(b: &mut Builder<'_>, parent: &[u32]) -> Result<(), CompileError> {
    let ast = b.ast;
    let arguments = b.intern("arguments".chars().map(u32::from).collect())?;
    for (i, nd) in ast.nodes.iter().enumerate() {
        let owner = b.a.owner_scope.get(i).copied().unwrap_or(NONE);
        let name = b.a.name_of.get(i).copied().unwrap_or(NONE);
        let r = match nd.kind {
            NodeKind::IdentifierReference => {
                let r = b.resolve(owner, name)?;
                if r == NONE && name == arguments {
                    // `arguments` of a non-arrow function is its arguments object.
                    let mut f = b.scope(owner)?.func;
                    while f != 0 {
                        let Some(fi) = b.a.funcs.get(f as usize) else {
                            break;
                        };
                        if !fi.arrow {
                            return Err(CompileError::NotYetCompiled {
                                feature: "the arguments object",
                                span: span_of(ast, i),
                            });
                        }
                        f = b.scope(fi.parent_scope)?.func;
                    }
                }
                r
            }
            NodeKind::BindingIdentifier => {
                let p = parent.get(i).copied().unwrap_or(NONE);
                let is_target = p != NONE
                    && matches!(
                        node(ast, p as usize)?.kind,
                        NodeKind::VariableDeclaration | NodeKind::LexicalBinding
                    )
                    && node(ast, p as usize)?.children.first() == u32::try_from(i).ok().as_ref();
                if is_target {
                    b.resolve(owner, name)?
                } else {
                    NONE
                }
            }
            NodeKind::ThisExpression => {
                let mut f = b.scope(owner)?.func;
                let here = f;
                let mut is_arrow = false;
                while let Some(fi) = b.a.funcs.get(f as usize) {
                    if fi.arrow {
                        is_arrow = true;
                        f = b.scope(fi.parent_scope)?.func;
                    } else {
                        break;
                    }
                }
                if is_arrow && f != here {
                    let home = b.a.funcs.get(f as usize).map(|fi| fi.scope).unwrap_or(NONE);
                    let this_name = b.intern(vec![u32::MAX])?;
                    let bid = b.declare(home, this_name, BKind::This)?;
                    b.binding_mut(bid)?.captured = true;
                    bid
                } else {
                    NONE
                }
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
