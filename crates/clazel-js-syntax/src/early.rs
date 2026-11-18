//! Early errors (ECMA-262 §16 and the rules it names), as a walk over the
//! arena with the environment of each node: the same rules as
//! [`crate::spec::early_local`] and [`crate::spec::child_env`], which this
//! mirrors. Not proven: tested (`tests/test262.rs`).
//!
//! Not checked, as in the spec: `IsValidRegularExpressionLiteral` of a regular
//! expression's contents (`clazel-js-regexp`, item 7.10, is not written, so
//! every regular expression literal is taken as valid), §16.2.1.1's rules on
//! duplicate and undeclared exports, and the rules for code a direct `eval`
//! processes.

use crate::api::ParseError;
use crate::ast::{Ast, Node, NodeKind as K, Op};
use crate::token::{
    lex, name_is, name_is_reserved_always, name_is_strict_reserved,
};
use clazel_js_lexer::spec::Goal;
use std::collections::HashSet;

/// What the early errors read of the position of a node (`spec::EarlyEnv`).
#[derive(Clone, Copy)]
struct Env {
    strict: bool,
    module: bool,
    yield_: bool,
    await_: bool,
    in_loop: bool,
    in_breakable: bool,
    super_prop: bool,
    super_call: bool,
    new_target: bool,
    no_arguments: bool,
    no_yield_await: bool,
    derived: bool,
}

/// The parts of an [`Env`] that a function-like construct sets (the
/// arguments of `spec::env_fn`): `[Yield]`, `[Await]`, `super.x` allowed,
/// `super()` allowed, `new.target` allowed, `arguments` not allowed, and no
/// `yield` or `await` expression allowed.
#[derive(Clone, Copy)]
struct Fl {
    y: bool,
    aw: bool,
    sp: bool,
    sc: bool,
    nt: bool,
    na: bool,
    nya: bool,
}

/// A declared name, and whether it is a plain `FunctionDeclaration`.
struct Decl {
    name: Vec<u32>,
    plain_function: bool,
}

/// The assignment target type of §8.6.4.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Target {
    Simple,
    WebCompat,
    Invalid,
}

struct Chk<'a> {
    src: &'a [u32],
    nodes: &'a [Node],
    /// The labels in scope, and whether each labels an iteration statement.
    labels: Vec<(Vec<u32>, bool)>,
    /// The `#names` that the enclosing class bodies declare.
    privates: Vec<Vec<u32>>,
}

/// Rejects `ast` if it has an early error (the rules of `spec::early_local`).
pub fn check(src: &[u32], ast: &Ast, module: bool) -> Result<(), ParseError> {
    let mut c = Chk { src, nodes: &ast.nodes, labels: Vec::new(), privates: Vec::new() };
    let root = ast.root as usize;
    let strict = module || c.has_use_strict(c.ch(root));
    let env = Env {
        strict,
        module,
        yield_: false,
        await_: module,
        in_loop: false,
        in_breakable: false,
        super_prop: false,
        super_call: false,
        new_target: false,
        no_arguments: false,
        no_yield_await: false,
        derived: false,
    };
    if c.walk(root, env) { Ok(()) } else { Err(ParseError::Syntax) }
}

fn is_assignment_pattern(k: K) -> bool {
    matches!(k, K::ObjectAssignmentPattern | K::ArrayAssignmentPattern)
}

fn is_function_kind(k: K) -> bool {
    matches!(
        k,
        K::FunctionDeclaration
            | K::FunctionExpression
            | K::GeneratorDeclaration
            | K::GeneratorExpression
            | K::AsyncFunctionDeclaration
            | K::AsyncFunctionExpression
            | K::AsyncGeneratorDeclaration
            | K::AsyncGeneratorExpression
    )
}

fn is_generator_kind(k: K) -> bool {
    matches!(
        k,
        K::GeneratorDeclaration | K::GeneratorExpression | K::AsyncGeneratorDeclaration | K::AsyncGeneratorExpression
    )
}

fn is_async_kind(k: K) -> bool {
    matches!(
        k,
        K::AsyncFunctionDeclaration
            | K::AsyncFunctionExpression
            | K::AsyncGeneratorDeclaration
            | K::AsyncGeneratorExpression
    )
}

fn is_function_expression_kind(k: K) -> bool {
    matches!(
        k,
        K::FunctionExpression | K::GeneratorExpression | K::AsyncFunctionExpression | K::AsyncGeneratorExpression
    )
}

/// `s`, read as UTF-16 code units, has no lone surrogate (`spec::well_formed_utf16`).
fn well_formed_utf16(s: &[u32]) -> bool {
    s.iter().enumerate().all(|(k, u)| {
        let next = s.get(k.saturating_add(1));
        let prev = k.checked_sub(1).and_then(|p| s.get(p));
        (!(0xD800..=0xDBFF).contains(u) || next.is_some_and(|x| (0xDC00..=0xDFFF).contains(x)))
            && (!(0xDC00..=0xDFFF).contains(u) || prev.is_some_and(|x| (0xD800..=0xDBFF).contains(x)))
    })
}

fn has_dup(ns: &[Vec<u32>]) -> bool {
    let mut seen: HashSet<&Vec<u32>> = HashSet::new();
    ns.iter().any(|n| !seen.insert(n))
}

fn intersects(xs: &[Vec<u32>], ys: &[Vec<u32>]) -> bool {
    if xs.is_empty() || ys.is_empty() {
        return false;
    }
    let set: HashSet<&Vec<u32>> = ys.iter().collect();
    xs.iter().any(|x| set.contains(x))
}

impl<'a> Chk<'a> {
    // ----- the arena, read totally -------------------------------------

    fn node(&self, i: usize) -> Option<&'a Node> {
        self.nodes.get(i)
    }

    fn kd(&self, i: usize) -> K {
        self.node(i).map_or(K::Script, |n| n.kind)
    }

    fn op(&self, i: usize) -> Op {
        self.node(i).map_or(Op::None, |n| n.op)
    }

    fn flag(&self, i: usize) -> bool {
        self.node(i).is_some_and(|n| n.flag)
    }

    /// The children of `i`.
    fn ch(&self, i: usize) -> &'a [u32] {
        self.node(i).map_or(&[], |n| n.children.as_slice())
    }

    /// Child `k` of `i`, `usize::MAX` (outside the arena) if none.
    fn k(&self, i: usize, k: usize) -> usize {
        self.ch(i).get(k).map_or(usize::MAX, |c| *c as usize)
    }

    /// The name of the identifier, string or private name node `i`.
    fn name(&self, i: usize) -> Vec<u32> {
        let Some(n) = self.node(i) else { return Vec::new() };
        lex(self.src, n.start, Goal::InputElementDiv, true).map(|t| t.name).unwrap_or_default()
    }

    /// The first token of node `i`.
    fn tok(&self, i: usize) -> Option<crate::token::Tok> {
        let n = self.node(i)?;
        lex(self.src, n.start, Goal::InputElementDiv, true)
    }

    // ----- static semantics --------------------------------------------

    /// `AssignmentTargetType` (§8.6.4).
    fn target_type(&self, c: usize, strict: bool) -> Target {
        match self.kd(c) {
            K::IdentifierReference => {
                let n = self.name(c);
                if strict && (name_is(&n, "eval") || name_is(&n, "arguments")) {
                    Target::Invalid
                } else {
                    Target::Simple
                }
            }
            K::MemberExpression | K::SuperProperty => Target::Simple,
            K::ParenthesizedExpression => {
                let k0 = self.k(c, 0);
                if k0 < c { self.target_type(k0, strict) } else { Target::Invalid }
            }
            K::CallExpression => {
                if strict { Target::Invalid } else { Target::WebCompat }
            }
            _ => Target::Invalid,
        }
    }

    fn destructuring_target_ok(&self, c: usize, strict: bool) -> bool {
        is_assignment_pattern(self.kd(c)) || self.target_type(c, strict) == Target::Simple
    }

    fn strip_parens(&self, mut c: usize) -> usize {
        while self.kd(c) == K::ParenthesizedExpression {
            let k0 = self.k(c, 0);
            if k0 >= c {
                break;
            }
            c = k0;
        }
        c
    }

    fn is_iteration(&self, mut c: usize) -> bool {
        loop {
            match self.kd(c) {
                K::DoWhileStatement | K::WhileStatement | K::ForStatement | K::ForInStatement | K::ForOfStatement => {
                    return true;
                }
                K::LabelledStatement => {
                    let k1 = self.k(c, 1);
                    if k1 >= c {
                        return false;
                    }
                    c = k1;
                }
                _ => return false,
            }
        }
    }

    fn is_labelled_function(&self, mut c: usize) -> bool {
        while self.kd(c) == K::LabelledStatement {
            let k1 = self.k(c, 1);
            if self.kd(k1) == K::FunctionDeclaration {
                return true;
            }
            if k1 >= c {
                return false;
            }
            c = k1;
        }
        false
    }

    /// §11.2.1: a Directive Prologue item.
    fn is_directive(&self, c: usize) -> bool {
        self.kd(c) == K::ExpressionStatement && self.kd(self.k(c, 0)) == K::StringLiteral
    }

    /// A directive whose string is exactly `"use strict"` or `'use strict'`.
    fn is_use_strict_directive(&self, c: usize) -> bool {
        if !self.is_directive(c) {
            return false;
        }
        let s = self.k(c, 0);
        let Some(n) = self.node(s) else { return false };
        let Some(text) = self.src.get(n.start..n.end) else { return false };
        text.len() == 12
            && matches!(text.first(), Some(0x22 | 0x27))
            && text.get(1..11).is_some_and(|t| name_is(t, "use strict"))
            && text.last() == text.first()
    }

    fn has_use_strict(&self, ks: &[u32]) -> bool {
        for c in ks {
            let c = *c as usize;
            if !self.is_directive(c) {
                return false;
            }
            if self.is_use_strict_directive(c) {
                return true;
            }
        }
        false
    }

    /// `IsSimpleParameterList` of a `FormalParameters` node.
    fn is_simple_params(&self, params: usize) -> bool {
        self.ch(params).iter().all(|p| {
            let p = *p as usize;
            self.kd(p) == K::BindingElement
                && self.kd(self.k(p, 0)) == K::BindingIdentifier
                && self.kd(self.k(p, 1)) == K::Absent
        })
    }

    /// `PropName` of `c` is `w`: an identifier or string key.
    fn prop_name_is(&self, c: usize, w: &str) -> bool {
        matches!(self.kd(c), K::IdentifierName | K::StringLiteral) && name_is(&self.name(c), w)
    }

    fn is_constructor_named(&self, c: usize) -> bool {
        self.kd(c) == K::MethodDefinition && !self.flag(c) && self.prop_name_is(self.k(c, 0), "constructor")
    }

    /// BoundNames of the binding node `c`.
    fn bound_names(&self, c: usize) -> Vec<Vec<u32>> {
        let mut out = Vec::new();
        self.bound_names_into(c, &mut out);
        out
    }

    fn bound_names_into(&self, c: usize, out: &mut Vec<Vec<u32>>) {
        match self.kd(c) {
            K::BindingIdentifier => out.push(self.name(c)),
            K::BindingElement
            | K::BindingRestElement
            | K::BindingRestProperty
            | K::FunctionRestParameter
            | K::VariableDeclaration
            | K::LexicalBinding
            | K::ForDeclaration => {
                let k0 = self.k(c, 0);
                if k0 < c {
                    self.bound_names_into(k0, out);
                }
            }
            K::BindingProperty => {
                let last = self.ch(c).last().map_or(usize::MAX, |x| *x as usize);
                if last < c {
                    self.bound_names_into(last, out);
                }
            }
            K::ObjectBindingPattern
            | K::ArrayBindingPattern
            | K::FormalParameters
            | K::VariableStatement
            | K::LexicalDeclaration
            | K::VariableDeclarationList => {
                for x in self.ch(c) {
                    let x = *x as usize;
                    if x < c {
                        self.bound_names_into(x, out);
                    }
                }
            }
            _ => {}
        }
    }

    /// LexicallyDeclaredNames of one item (TopLevel with `top`).
    fn lex_names_item(&self, c: usize, top: bool, out: &mut Vec<Decl>) {
        let k0 = self.k(c, 0);
        match self.kd(c) {
            K::LexicalDeclaration => {
                for n in self.bound_names(c) {
                    out.push(Decl { name: n, plain_function: false });
                }
            }
            K::ClassDeclaration => {
                if self.kd(k0) == K::BindingIdentifier {
                    out.push(Decl { name: self.name(k0), plain_function: false });
                }
            }
            K::FunctionDeclaration | K::GeneratorDeclaration | K::AsyncFunctionDeclaration | K::AsyncGeneratorDeclaration => {
                if !top && self.kd(k0) == K::BindingIdentifier {
                    out.push(Decl { name: self.name(k0), plain_function: self.kd(c) == K::FunctionDeclaration });
                }
            }
            K::LabelledStatement => {
                let k1 = self.k(c, 1);
                if !top && k1 < c {
                    self.lex_names_item(k1, top, out);
                }
            }
            K::ImportDeclaration => {
                if k0 < c {
                    self.bound_names_import(k0, out);
                }
            }
            K::ExportDeclaration
                if matches!(self.op(c), Op::ExportDecl | Op::ExportDefaultHoistable | Op::ExportDefaultClass)
                    && k0 < c =>
            {
                self.lex_names_item(k0, false, out);
            }
            _ => {}
        }
    }

    /// The names an `ImportClause` binds.
    fn bound_names_import(&self, c: usize, out: &mut Vec<Decl>) {
        let (k0, k1) = (self.k(c, 0), self.k(c, 1));
        if self.kd(k0) == K::BindingIdentifier {
            out.push(Decl { name: self.name(k0), plain_function: false });
        }
        if self.kd(k1) == K::NameSpaceImport {
            out.push(Decl { name: self.name(self.k(k1, 0)), plain_function: false });
        } else if self.kd(k1) == K::NamedImports {
            for s in self.ch(k1) {
                out.push(Decl { name: self.name(self.k(*s as usize, 1)), plain_function: false });
            }
        }
    }

    fn lex_names_list(&self, ks: &[u32], from: usize, top: bool) -> Vec<Decl> {
        let mut out = Vec::new();
        for c in ks.iter().skip(from) {
            self.lex_names_item(*c as usize, top, &mut out);
        }
        out
    }

    fn has_forbidden_duplicate(ds: &[Decl], strict: bool) -> bool {
        let mut index: std::collections::HashMap<&Vec<u32>, Vec<&Decl>> = std::collections::HashMap::new();
        for d in ds {
            if index
                .get(&d.name)
                .is_some_and(|prev| prev.iter().any(|p| !(!strict && p.plain_function && d.plain_function)))
            {
                return true;
            }
            index.entry(&d.name).or_default().push(d);
        }
        false
    }

    fn plain(ds: &[Decl]) -> Vec<Vec<u32>> {
        ds.iter().map(|d| d.name.clone()).collect()
    }

    /// VarDeclaredNames of statement `c` (TopLevel with `top`).
    fn var_names_item(&self, c: usize, top: bool, out: &mut Vec<Vec<u32>>) {
        let ks = self.ch(c);
        let k0 = self.k(c, 0);
        let k1 = self.k(c, 1);
        let k2 = self.k(c, 2);
        let k3 = self.k(c, 3);
        match self.kd(c) {
            K::VariableStatement | K::VariableDeclarationList => self.bound_names_into(c, out),
            K::BlockStatement => self.var_names_list(c, ks, 0, out),
            K::IfStatement => {
                self.var_names_sub(c, k1, out);
                self.var_names_sub(c, k2, out);
            }
            K::DoWhileStatement => self.var_names_sub(c, k0, out),
            K::WhileStatement => self.var_names_sub(c, k1, out),
            K::ForStatement => {
                self.var_names_sub(c, k0, out);
                self.var_names_sub(c, k3, out);
            }
            K::ForInStatement | K::ForOfStatement => {
                if k0 < c && self.kd(k0) == K::ForDeclaration && self.op(k0) == Op::Var {
                    self.bound_names_into(k0, out);
                }
                self.var_names_sub(c, k2, out);
            }
            K::WithStatement => self.var_names_sub(c, k1, out),
            K::SwitchStatement | K::CaseClause => self.var_names_list(c, ks, 1, out),
            K::DefaultClause => self.var_names_list(c, ks, 0, out),
            K::LabelledStatement => {
                if k1 < c {
                    self.var_names_item(k1, top, out);
                }
            }
            K::TryStatement => {
                self.var_names_sub(c, k0, out);
                self.var_names_sub(c, k1, out);
                self.var_names_sub(c, k2, out);
            }
            K::Catch => self.var_names_sub(c, k1, out),
            K::Finally => self.var_names_sub(c, k0, out),
            K::FunctionDeclaration | K::GeneratorDeclaration | K::AsyncFunctionDeclaration | K::AsyncGeneratorDeclaration => {
                if top && self.kd(k0) == K::BindingIdentifier {
                    out.push(self.name(k0));
                }
            }
            K::ExportDeclaration if self.op(c) == Op::ExportVar => self.var_names_sub(c, k0, out),
            _ => {}
        }
    }

    fn var_names_sub(&self, c: usize, s: usize, out: &mut Vec<Vec<u32>>) {
        if s < c {
            self.var_names_item(s, false, out);
        }
    }

    fn var_names_list(&self, n: usize, ks: &[u32], from: usize, out: &mut Vec<Vec<u32>>) {
        for c in ks.iter().skip(from) {
            self.var_names_sub(n, *c as usize, out);
        }
    }

    fn top_var_names_list(&self, ks: &[u32]) -> Vec<Vec<u32>> {
        let mut out = Vec::new();
        for c in ks {
            self.var_names_item(*c as usize, true, &mut out);
        }
        out
    }

    /// §14.2.1, §15.2.1, §16.1.1: the lexical names of a list are unique and
    /// not var-declared.
    fn list_early(&self, n: usize, ks: &[u32], strict: bool, top: bool) -> bool {
        let lex = self.lex_names_list(ks, 0, top);
        let vars = if top {
            self.top_var_names_list(ks)
        } else {
            let mut v = Vec::new();
            self.var_names_list(n, ks, 0, &mut v);
            v
        };
        !Self::has_forbidden_duplicate(&lex, strict) && !intersects(&Self::plain(&lex), &vars)
    }

    /// §15.1.1 and the other rules shared by the function-like productions.
    fn function_early(&self, params: usize, body_ks: &[u32], unique: bool, strict: bool) -> bool {
        let names = self.bound_names(params);
        let simple = self.is_simple_params(params);
        if self.has_use_strict(body_ks) && !simple {
            return false;
        }
        let lex = Self::plain(&self.lex_names_list(body_ks, 0, true));
        if intersects(&names, &lex) {
            return false;
        }
        !((strict || unique || !simple) && has_dup(&names))
    }

    /// §15.7.1 the early errors of the elements of a `ClassBody`.
    fn class_body_early(&self, ks: &[u32]) -> bool {
        let mut constructors = 0usize;
        for c in ks {
            let c = *c as usize;
            let key = self.k(c, 0);
            let is_static = self.flag(c);
            if self.is_constructor_named(c) {
                constructors = constructors.saturating_add(1);
                if self.op(c) != Op::Method {
                    return false;
                }
            }
            if self.kd(c) == K::MethodDefinition && is_static && self.prop_name_is(key, "prototype") {
                return false;
            }
            if self.kd(c) == K::FieldDefinition
                && (self.prop_name_is(key, "constructor") || (is_static && self.prop_name_is(key, "prototype")))
            {
                return false;
            }
            if self.kd(key) == K::PrivateIdentifier && name_is(&self.name(key), "constructor") {
                return false;
            }
        }
        if constructors > 1 {
            return false;
        }
        // Private names are declared once, except a getter and a setter pair.
        let mut seen: std::collections::HashMap<Vec<u32>, Vec<(Op, bool, bool)>> = std::collections::HashMap::new();
        for c in ks {
            let c = *c as usize;
            let key = self.k(c, 0);
            if self.kd(key) == K::PrivateIdentifier {
                let nm = self.name(key);
                let entry = (self.op(c), self.flag(c), self.kd(c) == K::MethodDefinition);
                if let Some(prev) = seen.get(&nm) {
                    let ok = prev.len() == 1
                        && prev.iter().all(|(po, ps, pm)| {
                            *pm && entry.2
                                && ((*po == Op::Getter && entry.0 == Op::Setter)
                                    || (*po == Op::Setter && entry.0 == Op::Getter))
                                && *ps == entry.1
                        });
                    if !ok {
                        return false;
                    }
                }
                seen.entry(nm).or_default().push(entry);
            }
        }
        true
    }

    fn private_declared(&self, nm: &[u32]) -> bool {
        self.privates.iter().any(|p| p.as_slice() == nm)
    }

    fn is_proto_entry(&self, c: usize) -> bool {
        self.kd(c) == K::PropertyDefinition && self.op(c) == Op::KeyValue && self.prop_name_is(self.k(c, 0), "__proto__")
    }

    /// §13.5.1.1: `delete` of an identifier or private member in strict code.
    fn delete_error(&self, operand: usize, strict: bool) -> bool {
        let o = self.strip_parens(operand);
        let last = self.ch(o).last().map_or(usize::MAX, |x| *x as usize);
        strict
            && (self.kd(o) == K::IdentifierReference
                || (self.kd(o) == K::MemberExpression && self.op(o) == Op::PrivateDot)
                || (self.kd(o) == K::OptionalExpression
                    && self.kd(last) == K::OptionalChain
                    && self.op(last) == Op::ChainPrivateDot))
    }

    /// §13.1.1 identifiers.
    fn identifier_ok(&self, n: usize, env: Env) -> bool {
        let nm = self.name(n);
        let is_yield = name_is(&nm, "yield");
        let is_await = name_is(&nm, "await");
        let kind = self.kd(n);
        !(kind == K::BindingIdentifier && env.strict && (name_is(&nm, "arguments") || name_is(&nm, "eval")))
            && !(env.strict && name_is_strict_reserved(&nm))
            && !(env.module && is_await)
            && !(env.yield_ && is_yield)
            && !(env.await_ && is_await)
            && !name_is_reserved_always(&nm)
            && !(kind == K::IdentifierReference && env.no_arguments && name_is(&nm, "arguments"))
    }

    // ----- the rules of one node ---------------------------------------

    fn local(&self, n: usize, env: Env) -> bool {
        let ks = self.ch(n);
        let (k0, k1, k2, k3) = (self.k(n, 0), self.k(n, 1), self.k(n, 2), self.k(n, 3));
        match self.kd(n) {
            K::IdentifierReference | K::BindingIdentifier | K::LabelIdentifier => self.identifier_ok(n, env),
            K::NumericLiteral | K::StringLiteral => {
                !(env.strict && self.tok(n).is_some_and(|t| t.legacy))
            }
            K::ObjectLiteral => {
                let protos = ks.iter().filter(|c| self.is_proto_entry(**c as usize)).count();
                protos <= 1
            }
            K::CoverInitializedName => false,
            K::SuperProperty => env.super_prop,
            K::SuperCall => env.super_call,
            K::NewTarget => env.new_target,
            K::ImportMeta => env.module,
            K::MemberExpression => self.op(n) != Op::PrivateDot || self.private_declared(&self.name(k1)),
            K::OptionalChain => {
                self.op(n) != Op::ChainTemplate
                    && (self.op(n) != Op::ChainPrivateDot || self.private_declared(&self.name(k0)))
            }
            K::RelationalExpression => self.kd(k0) != K::PrivateIdentifier || self.private_declared(&self.name(k0)),
            K::UnaryExpression => !(self.op(n) == Op::Delete && self.delete_error(k0, env.strict)),
            K::UpdateExpression => self.target_type(k0, env.strict) != Target::Invalid,
            K::AssignmentExpression => {
                let op = self.op(n);
                (op == Op::Assign && is_assignment_pattern(self.kd(k0)))
                    || (self.target_type(k0, env.strict) != Target::Invalid
                        && (!matches!(op, Op::LogicalAndAssign | Op::LogicalOrAssign | Op::CoalesceAssign)
                            || self.target_type(k0, env.strict) == Target::Simple))
            }
            K::AssignmentProperty => self.op(n) != Op::Shorthand || self.target_type(k0, env.strict) == Target::Simple,
            K::AssignmentElement | K::AssignmentRestElement => self.destructuring_target_ok(k0, env.strict),
            K::AssignmentRestProperty => {
                !is_assignment_pattern(self.kd(k0)) && self.destructuring_target_ok(k0, env.strict)
            }
            K::YieldExpression | K::AwaitExpression => !env.no_yield_await,
            K::BlockStatement => self.list_early(n, ks, env.strict, false),
            K::LexicalDeclaration => {
                let bn = self.bound_names(n);
                !bn.iter().any(|x| name_is(x, "let"))
                    && !has_dup(&bn)
                    && (self.op(n) != Op::Const
                        || ks.iter().all(|b| self.kd(self.k(*b as usize, 1)) != K::Absent))
            }
            K::IfStatement => {
                !self.is_labelled_function(k1)
                    && !self.is_labelled_function(k2)
                    && !(env.strict && (self.kd(k1) == K::FunctionDeclaration || self.kd(k2) == K::FunctionDeclaration))
            }
            K::DoWhileStatement => !self.is_labelled_function(k0),
            K::WhileStatement => !self.is_labelled_function(k1),
            K::ForStatement => {
                if self.is_labelled_function(k3) {
                    return false;
                }
                if self.kd(k0) == K::LexicalDeclaration {
                    let mut v = Vec::new();
                    self.var_names_sub(n, k3, &mut v);
                    let bn = self.bound_names(k0);
                    if intersects(&bn, &v) {
                        return false;
                    }
                }
                true
            }
            K::ForInStatement | K::ForOfStatement => {
                // 15.7.1 ContainsAwait: no `for await` in a static block.
                if self.kd(n) == K::ForOfStatement && self.flag(n) && env.no_yield_await {
                    return false;
                }
                if self.is_labelled_function(k2) {
                    return false;
                }
                if self.kd(k0) == K::ForDeclaration {
                    let bn = self.bound_names(k0);
                    if self.op(k0) != Op::Var {
                        let mut v = Vec::new();
                        self.var_names_sub(n, k2, &mut v);
                        if bn.iter().any(|x| name_is(x, "let")) || has_dup(&bn) || intersects(&bn, &v) {
                            return false;
                        }
                    }
                    let d = self.k(k0, 0);
                    if self.kd(d) == K::VariableDeclaration {
                        // Annex B.3.5.
                        return !env.strict
                            && self.kd(self.k(d, 0)) == K::BindingIdentifier
                            && self.kd(self.k(d, 1)) != K::Absent;
                    }
                    true
                } else {
                    is_assignment_pattern(self.kd(k0)) || self.target_type(k0, env.strict) != Target::Invalid
                }
            }
            K::ContinueStatement => {
                if self.kd(k0) == K::LabelIdentifier {
                    let nm = self.name(k0);
                    self.labels.iter().any(|(l, it)| *l == nm && *it)
                } else {
                    env.in_loop
                }
            }
            K::BreakStatement => {
                if self.kd(k0) == K::LabelIdentifier {
                    let nm = self.name(k0);
                    self.labels.iter().any(|(l, _)| *l == nm)
                } else {
                    env.in_breakable
                }
            }
            K::WithStatement => !env.strict && !self.is_labelled_function(k1),
            K::SwitchStatement => {
                let mut lex = Vec::new();
                for c in ks.iter().skip(1) {
                    let c = *c as usize;
                    let from = if self.kd(c) == K::CaseClause { 1 } else { 0 };
                    lex.extend(self.lex_names_list(self.ch(c), from, false));
                }
                let mut vars = Vec::new();
                self.var_names_list(n, ks, 1, &mut vars);
                !Self::has_forbidden_duplicate(&lex, env.strict) && !intersects(&Self::plain(&lex), &vars)
            }
            K::LabelledStatement => {
                let nm = self.name(k0);
                !self.labels.iter().any(|(l, _)| *l == nm) && !(env.strict && self.kd(k1) == K::FunctionDeclaration)
            }
            K::Catch => {
                let bn = self.bound_names(k0);
                let bk = self.ch(k1);
                let lex = Self::plain(&self.lex_names_list(bk, 0, false));
                if has_dup(&bn) || intersects(&bn, &lex) {
                    return false;
                }
                if self.kd(k0) != K::BindingIdentifier {
                    let mut v = Vec::new();
                    self.var_names_list(k1, bk, 0, &mut v);
                    if intersects(&bn, &v) {
                        return false;
                    }
                }
                true
            }
            K::FunctionBody => self.list_early(n, ks, env.strict, true),
            k if is_function_kind(k) => {
                let body = self.ch(k2);
                self.function_early(k1, body, false, env.strict || self.has_use_strict(body))
            }
            K::ArrowFunction | K::AsyncArrowFunction => {
                let body: &[u32] = if self.kd(k1) == K::FunctionBody { self.ch(k1) } else { &[] };
                self.function_early(k0, body, true, env.strict || self.has_use_strict(body))
            }
            K::MethodDefinition => {
                let body = self.ch(k2);
                self.function_early(k1, body, true, env.strict || self.has_use_strict(body))
            }
            K::ClassBody => self.class_body_early(ks),
            K::Script => self.list_early(n, ks, env.strict, true),
            K::Module => self.list_early(n, ks, true, false) && self.exports_early(n, ks),
            K::ExportSpecifier => self.export_name_ok(k0) && self.export_name_ok(k1),
            K::ImportSpecifier => self.export_name_ok(k0),
            K::WithClause => {
                let keys: Vec<Vec<u32>> = ks.iter().map(|c| self.name(self.k(*c as usize, 0))).collect();
                !has_dup(&keys)
            }
            K::ExportDeclaration => {
                (self.op(n) != Op::ExportNamed
                    || self.ch(k0).iter().all(|s| {
                        let loc = self.k(*s as usize, 0);
                        let nm = self.name(loc);
                        self.kd(loc) != K::StringLiteral
                            && !name_is_reserved_always(&nm)
                            && !name_is(&nm, "yield")
                            && !name_is(&nm, "await")
                            && !name_is_strict_reserved(&nm)
                    }))
                    && (self.op(n) != Op::ExportAllAs || self.export_name_ok(k0))
            }
            _ => true,
        }
    }

    /// §16.2.2.1, §16.2.3.1: a `StringLiteral` that is a `ModuleExportName` is well
    /// formed (`spec::module_export_name_ok`).
    fn export_name_ok(&self, c: usize) -> bool {
        self.kd(c) != K::StringLiteral || well_formed_utf16(&self.name(c))
    }

    /// `spec::exported_names_item`: the names an export declaration exports.
    fn exported_names_item(&self, c: usize) -> Vec<Vec<u32>> {
        if self.kd(c) != K::ExportDeclaration {
            return Vec::new();
        }
        let k0 = self.k(c, 0);
        match self.op(c) {
            Op::ExportAll => Vec::new(),
            Op::ExportAllAs => vec![self.name(k0)],
            Op::ExportFrom | Op::ExportNamed => self
                .ch(k0)
                .iter()
                .map(|s| {
                    let s = *s as usize;
                    let e = self.k(s, 1);
                    if self.kd(e) == K::Absent { self.name(self.k(s, 0)) } else { self.name(e) }
                })
                .collect(),
            Op::ExportVar => self.bound_names(k0),
            Op::ExportDecl => {
                let mut out = Vec::new();
                self.lex_names_item(k0, false, &mut out);
                Self::plain(&out)
            }
            _ => vec!["default".chars().map(u32::from).collect()],
        }
    }

    /// §16.2.1.1: no name is exported twice, and every local name of an
    /// `export { ... };` is declared in the module (`spec::exports_early`).
    fn exports_early(&self, n: usize, ks: &[u32]) -> bool {
        let mut exported = Vec::new();
        let mut local = Vec::new();
        for c in ks {
            let c = *c as usize;
            exported.extend(self.exported_names_item(c));
            if self.kd(c) == K::ExportDeclaration && self.op(c) == Op::ExportNamed {
                for s in self.ch(self.k(c, 0)) {
                    local.push(self.name(self.k(*s as usize, 0)));
                }
            }
        }
        if has_dup(&exported) {
            return false;
        }
        if local.is_empty() {
            return true;
        }
        let mut declared = Self::plain(&self.lex_names_list(ks, 0, false));
        self.var_names_list(n, ks, 0, &mut declared);
        let set: HashSet<&Vec<u32>> = declared.iter().collect();
        local.iter().all(|l| set.contains(l))
    }

    // ----- the environment of the children -----------------------------

    /// A function-like environment: no label, no loop.
    fn env_fn(env: Env, strict: bool, f: Fl) -> Env {
        Env {
            strict,
            module: env.module,
            yield_: f.y,
            await_: f.aw,
            in_loop: false,
            in_breakable: false,
            super_prop: f.sp,
            super_call: f.sc,
            new_target: f.nt,
            no_arguments: f.na,
            no_yield_await: f.nya,
            derived: env.derived,
        }
    }

    /// The flags of an arrow function's parameters (`params`) or body, which
    /// inherit `super`, `new.target` and `arguments` from the enclosing code.
    fn arrow_flags(env: Env, y: bool, aw: bool, params: bool) -> Fl {
        Fl {
            y,
            aw,
            sp: env.super_prop,
            sc: env.super_call,
            nt: env.new_target,
            na: env.no_arguments,
            nya: params,
        }
    }

    /// The environment of child `k` of `n`, and whether the labels are cleared.
    fn child_env(&self, n: usize, k: usize, env: Env) -> (Env, bool) {
        let kind = self.kd(n);
        let (k0, k1, k2) = (self.k(n, 0), self.k(n, 1), self.k(n, 2));
        let g = is_generator_kind(kind);
        let aw = is_async_kind(kind);
        let fn_strict = env.strict || self.has_use_strict(self.ch(k2));
        let arrow_strict =
            env.strict || (self.kd(k1) == K::FunctionBody && self.has_use_strict(self.ch(k1)));
        let loop_body = |b: bool| if b { Env { in_loop: true, in_breakable: true, ..env } } else { env };
        match kind {
            kd if is_function_kind(kd) => {
                if k == 0 {
                    let expr = is_function_expression_kind(kd);
                    (
                        Env {
                            strict: fn_strict,
                            yield_: if expr { g } else { env.yield_ },
                            await_: if expr { aw } else { env.await_ },
                            ..env
                        },
                        false,
                    )
                } else {
                    let f = Fl { y: g, aw, sp: false, sc: false, nt: true, na: false, nya: k == 1 };
                    (Self::env_fn(env, fn_strict, f), true)
                }
            }
            K::ArrowFunction => {
                if k == 0 {
                    (Self::env_fn(env, arrow_strict, Self::arrow_flags(env, env.yield_, env.await_, true)), false)
                } else {
                    (Self::env_fn(env, arrow_strict, Self::arrow_flags(env, false, false, false)), true)
                }
            }
            K::AsyncArrowFunction => {
                if k == 0 {
                    let y = self.kd(k0) == K::BindingIdentifier && env.yield_;
                    (Self::env_fn(env, arrow_strict, Self::arrow_flags(env, y, true, true)), false)
                } else {
                    (Self::env_fn(env, arrow_strict, Self::arrow_flags(env, false, true, false)), true)
                }
            }
            K::MethodDefinition => {
                if k == 0 {
                    (env, false)
                } else {
                    let op = self.op(n);
                    let mg = matches!(op, Op::GeneratorMethod | Op::AsyncGeneratorMethod);
                    let ma = matches!(op, Op::AsyncMethod | Op::AsyncGeneratorMethod);
                    let sc = env.derived && self.is_constructor_named(n) && op == Op::Method;
                    let f = Fl { y: mg, aw: ma, sp: true, sc, nt: true, na: false, nya: k == 1 };
                    (Self::env_fn(env, fn_strict, f), true)
                }
            }
            K::FieldDefinition => {
                if k == 1 {
                    let f = Fl { y: env.yield_, aw: env.await_, sp: true, sc: false, nt: true, na: true, nya: false };
                    (Self::env_fn(env, env.strict, f), true)
                } else {
                    (env, false)
                }
            }
            // 15.7.1 ContainsAwait: no `await` and no `for await` in a static block.
            K::ClassStaticBlock => {
                let f = Fl { y: false, aw: true, sp: true, sc: false, nt: true, na: true, nya: true };
                (Self::env_fn(env, env.strict, f), true)
            }
            K::ClassDeclaration | K::ClassExpression => (
                Env {
                    strict: true,
                    derived: if k == 2 { self.kd(k1) != K::Absent } else { env.derived },
                    ..env
                },
                false,
            ),
            K::ObjectLiteral => (Env { derived: false, ..env }, false),
            K::DoWhileStatement => (loop_body(k == 0), false),
            K::WhileStatement => (loop_body(k == 1), false),
            K::ForStatement => (loop_body(k == 3), false),
            K::ForInStatement | K::ForOfStatement => (loop_body(k == 2), false),
            K::SwitchStatement => (if k >= 1 { Env { in_breakable: true, ..env } } else { env }, false),
            _ => (env, false),
        }
    }

    /// Node `n` and everything below it meet the early errors.
    fn walk(&mut self, n: usize, env: Env) -> bool {
        if !self.local(n, env) {
            return false;
        }
        let kind = self.kd(n);
        let kids = self.ch(n);
        let pushed_privates = if kind == K::ClassBody {
            let before = self.privates.len();
            for c in kids {
                let key = self.k(*c as usize, 0);
                if self.kd(key) == K::PrivateIdentifier {
                    let nm = self.name(key);
                    self.privates.push(nm);
                }
            }
            Some(before)
        } else {
            None
        };
        let mut ok = true;
        for (k, c) in kids.iter().enumerate() {
            let c = *c as usize;
            if c >= n {
                return false;
            }
            let (cenv, clear) = self.child_env(n, k, env);
            let saved = if clear { Some(std::mem::take(&mut self.labels)) } else { None };
            let pushed_label = kind == K::LabelledStatement && k == 1;
            if pushed_label {
                let nm = self.name(self.k(n, 0));
                let it = self.is_iteration(self.k(n, 1));
                self.labels.push((nm, it));
            }
            let r = self.walk(c, cenv);
            if pushed_label {
                self.labels.pop();
            }
            if let Some(s) = saved {
                self.labels = s;
            }
            if !r {
                ok = false;
                break;
            }
        }
        if let Some(b) = pushed_privates {
            self.privates.truncate(b);
        }
        ok
    }
}
