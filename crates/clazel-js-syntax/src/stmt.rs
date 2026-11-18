//! The parser's statements, declarations, functions, classes and binding
//! patterns (ECMA-262 §14, §15, §14.3.3, §16.1).

use crate::ast::{NodeKind as K, Op};
use crate::parser::{Cx, Parser, R, syn};
use clazel_js_lexer::spec::ElementKind;

impl<'a> Parser<'a> {
    // ----- Script (§16.1) ----------------------------------------------

    /// `Script` or `Module`: every item until the end of the source text.
    pub fn parse_program(&mut self) -> R<u32> {
        let cx = Cx { y: false, a: self.module, i: true, r: false };
        let start = if self.t.eof { 0 } else { self.t.start };
        let mut items = Vec::new();
        while !self.t.eof {
            let item = if self.module { self.parse_module_item(cx)? } else { self.parse_item(cx)? };
            items.push(item);
        }
        let end = if items.is_empty() { 0 } else { self.prev_end };
        let kind = if self.module { K::Module } else { K::Script };
        Ok(self.mk(kind, Op::None, false, start, end, items))
    }

    // ----- Statement lists and items (§14.2) ---------------------------

    /// A `StatementListItem`: a `Statement` or a `Declaration`.
    pub fn parse_item(&mut self, cx: Cx) -> R<u32> {
        if self.t.is_w("function") {
            return self.parse_function(cx, None, false, false);
        }
        if self.t.is_w("async") {
            let nx = self.peek()?;
            if nx.is_w("function") && !nx.nl {
                let s = self.t.start;
                return self.parse_function(cx, Some(s), false, false);
            }
        }
        if self.t.is_w("class") {
            return self.parse_class(cx, false, false);
        }
        if self.t.is_w("const") {
            return self.parse_lexical(cx, Op::Const);
        }
        if self.t.is_w("let") && self.let_starts_declaration()? {
            return self.parse_lexical(cx, Op::Let);
        }
        self.parse_statement(cx)
    }

    /// The `let` at the current token begins a `LexicalDeclaration` (the next
    /// token can start a binding), as against an identifier named `let`.
    pub fn let_starts_declaration(&self) -> R<bool> {
        let nx = self.peek()?;
        Ok(nx.is_p("[")
            || nx.is_p("{")
            || (nx.is_name() && !crate::token::is_reserved_always(word_of(&nx.name))))
    }

    /// `{ StatementList? }`, the items up to the `}` (not consumed).
    fn parse_items_until_brace(&mut self, cx: Cx) -> R<Vec<u32>> {
        let mut items = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            items.push(self.parse_item(cx)?);
        }
        Ok(items)
    }

    /// `Block` (§14.2).
    fn parse_block(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.expect_p("{")?;
        let items = self.parse_items_until_brace(cx)?;
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::BlockStatement, Op::None, false, start, end, items))
    }

    /// `LexicalDeclaration` (§14.3.1).
    fn parse_lexical(&mut self, cx: Cx, op: Op) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let cxi = cx.with_in(true);
        let mut kids = vec![self.parse_binding_decl(cxi, K::LexicalBinding, false)?];
        while self.eat_p(",")? {
            kids.push(self.parse_binding_decl(cxi, K::LexicalBinding, false)?);
        }
        let end = self.semi()?;
        Ok(self.mk(K::LexicalDeclaration, op, false, start, end, kids))
    }

    /// `VariableDeclaration` or `LexicalBinding`: a target and its initializer.
    /// A pattern needs one, unless `in_for` (the head of `for-in` and `for-of`).
    pub fn parse_binding_decl(&mut self, cx: Cx, kind: K, in_for: bool) -> R<u32> {
        let target = self.parse_binding_target(cx)?;
        let start = self.st(target);
        let (init, end) = if self.t.is_p("=") {
            self.bump()?;
            let e = self.parse_assign(cx)?;
            (e, self.en(e))
        } else {
            if !in_for && self.kind(target) != K::BindingIdentifier {
                return syn();
            }
            let end = self.en(target);
            (self.absent(), end)
        };
        Ok(self.mk(kind, Op::None, false, start, end, vec![target, init]))
    }

    // ----- Statement (§14) ---------------------------------------------

    /// A `Statement`.
    pub fn parse_statement(&mut self, cx: Cx) -> R<u32> {
        self.nest(|p| p.parse_statement_inner(cx))
    }

    /// The body of an `if` or a labelled statement: a `Statement`, or (Annex
    /// B.3.2, B.3.3) a `FunctionDeclaration`.
    fn parse_stmt_or_function(&mut self, cx: Cx) -> R<u32> {
        if self.t.is_w("function") {
            let nx = self.peek()?;
            if nx.is_p("*") {
                return syn();
            }
            return self.parse_function(cx, None, false, false);
        }
        self.parse_statement(cx)
    }

    fn parse_statement_inner(&mut self, cx: Cx) -> R<u32> {
        if self.t.eof {
            return syn();
        }
        let start = self.t.start;
        if self.t.is_p("{") {
            return self.parse_block(cx);
        }
        if self.t.is_p(";") {
            let e = self.t.end;
            self.bump()?;
            return Ok(self.leaf(K::EmptyStatement, start, e));
        }
        if self.t.is_name() {
            match self.t.s {
                "var" => return self.parse_var_statement(cx),
                "if" => return self.parse_if(cx),
                "do" => return self.parse_do(cx),
                "while" => return self.parse_while(cx),
                "for" => return self.parse_for(cx),
                "continue" | "break" => return self.parse_jump(cx),
                "return" => return self.parse_return(cx),
                "with" => return self.parse_with(cx),
                "switch" => return self.parse_switch(cx),
                "throw" => return self.parse_throw(cx),
                "try" => return self.parse_try(cx),
                "debugger" => {
                    let kw_end = self.t.end;
                    self.bump()?;
                    let end = self.semi()?;
                    let _ = kw_end;
                    return Ok(self.leaf(K::DebuggerStatement, start, end));
                }
                "function" | "class" | "const" => return syn(),
                "let" => {
                    let nx = self.peek()?;
                    if nx.is_p("[") {
                        return syn();
                    }
                }
                "async" => {
                    let nx = self.peek()?;
                    if nx.is_w("function") && !nx.nl {
                        return syn();
                    }
                }
                _ => {}
            }
            // `Identifier :` is a labelled statement.
            if self.ident_ok(cx) {
                let nx = self.peek()?;
                if nx.is_p(":") {
                    let label = self.parse_ident(K::LabelIdentifier, cx)?;
                    self.bump()?;
                    let body = self.parse_stmt_or_function(cx)?;
                    let end = self.en(body);
                    return Ok(self.mk(K::LabelledStatement, Op::None, false, start, end, vec![label, body]));
                }
            }
        }
        let e = self.parse_expression(cx.with_in(true))?;
        let end = self.semi()?;
        Ok(self.mk(K::ExpressionStatement, Op::None, false, start, end, vec![e]))
    }

    /// `VariableStatement` (§14.3.2).
    fn parse_var_statement(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let cxi = cx.with_in(true);
        let mut kids = vec![self.parse_binding_decl(cxi, K::VariableDeclaration, false)?];
        while self.eat_p(",")? {
            kids.push(self.parse_binding_decl(cxi, K::VariableDeclaration, false)?);
        }
        let end = self.semi()?;
        Ok(self.mk(K::VariableStatement, Op::None, false, start, end, kids))
    }

    /// `( Expression )`, the head of `if`, `while`, `with` and `switch`.
    fn parse_paren_head(&mut self, cx: Cx) -> R<u32> {
        self.expect_p("(")?;
        let e = self.parse_expression(cx.with_in(true))?;
        self.expect_p(")")?;
        Ok(e)
    }

    /// `IfStatement` (§14.6).
    fn parse_if(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let test = self.parse_paren_head(cx)?;
        let cons = self.parse_stmt_or_function(cx)?;
        let (alt, end) = if self.t.is_w("else") {
            self.bump()?;
            let a = self.parse_stmt_or_function(cx)?;
            (a, self.en(a))
        } else {
            (self.absent(), self.en(cons))
        };
        Ok(self.mk(K::IfStatement, Op::None, false, start, end, vec![test, cons, alt]))
    }

    /// `DoWhileStatement` (§14.7.2), with §12.10.1's third rule for the `;`.
    fn parse_do(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let body = self.parse_statement(cx)?;
        self.expect_w("while")?;
        let test = self.parse_paren_head(cx)?;
        let end = if self.t.is_p(";") {
            let e = self.t.end;
            self.bump()?;
            e
        } else {
            self.prev_end
        };
        Ok(self.mk(K::DoWhileStatement, Op::None, false, start, end, vec![body, test]))
    }

    /// `WhileStatement` (§14.7.3).
    fn parse_while(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let test = self.parse_paren_head(cx)?;
        let body = self.parse_statement(cx)?;
        let end = self.en(body);
        Ok(self.mk(K::WhileStatement, Op::None, false, start, end, vec![test, body]))
    }

    /// `WithStatement` (§14.11).
    fn parse_with(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let obj = self.parse_paren_head(cx)?;
        let body = self.parse_statement(cx)?;
        let end = self.en(body);
        Ok(self.mk(K::WithStatement, Op::None, false, start, end, vec![obj, body]))
    }

    /// `ContinueStatement` and `BreakStatement` (§14.8, §14.9).
    fn parse_jump(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        let kind = if self.t.is_w("continue") { K::ContinueStatement } else { K::BreakStatement };
        self.bump()?;
        let label = if self.t.is_name() && !self.t.nl && self.ident_ok(cx) {
            self.parse_ident(K::LabelIdentifier, cx)?
        } else {
            self.absent()
        };
        let end = self.semi()?;
        Ok(self.mk(kind, Op::None, false, start, end, vec![label]))
    }

    /// `ReturnStatement` (§14.10).
    fn parse_return(&mut self, cx: Cx) -> R<u32> {
        if !cx.r {
            return syn();
        }
        let start = self.t.start;
        self.bump()?;
        let e = if self.t.nl || self.t.eof || self.t.is_p(";") || self.t.is_p("}") {
            self.absent()
        } else {
            self.parse_expression(cx.with_in(true))?
        };
        let end = self.semi()?;
        Ok(self.mk(K::ReturnStatement, Op::None, false, start, end, vec![e]))
    }

    /// `ThrowStatement` (§14.14).
    fn parse_throw(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        if self.t.nl {
            return syn();
        }
        let e = self.parse_expression(cx.with_in(true))?;
        let end = self.semi()?;
        Ok(self.mk(K::ThrowStatement, Op::None, false, start, end, vec![e]))
    }

    /// `SwitchStatement` (§14.12).
    fn parse_switch(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let disc = self.parse_paren_head(cx)?;
        self.expect_p("{")?;
        let mut kids = vec![disc];
        while !self.t.is_p("}") {
            let cs = self.t.start;
            let mut clause_kids = Vec::new();
            let kind = if self.t.is_w("case") {
                self.bump()?;
                clause_kids.push(self.parse_expression(cx.with_in(true))?);
                K::CaseClause
            } else if self.t.is_w("default") {
                // §14.12: a `CaseBlock` has at most one `DefaultClause`.
                if kids.iter().any(|c| self.kind(*c) == K::DefaultClause) {
                    return syn();
                }
                self.bump()?;
                K::DefaultClause
            } else {
                return syn();
            };
            let mut end = self.t.end;
            self.expect_p(":")?;
            while !(self.t.is_p("}") || self.t.is_w("case") || self.t.is_w("default")) {
                if self.t.eof {
                    return syn();
                }
                let it = self.parse_item(cx)?;
                end = self.en(it);
                clause_kids.push(it);
            }
            kids.push(self.mk(kind, Op::None, false, cs, end, clause_kids));
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::SwitchStatement, Op::None, false, start, end, kids))
    }

    /// `TryStatement` (§14.15).
    fn parse_try(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let block = self.parse_block(cx)?;
        let mut end = self.en(block);
        let catch = if self.t.is_w("catch") {
            let cs = self.t.start;
            self.bump()?;
            let param = if self.t.is_p("(") {
                self.bump()?;
                let p = self.parse_binding_target(cx)?;
                self.expect_p(")")?;
                p
            } else {
                self.absent()
            };
            let b = self.parse_block(cx)?;
            end = self.en(b);
            self.mk(K::Catch, Op::None, false, cs, end, vec![param, b])
        } else {
            self.absent()
        };
        let finally = if self.t.is_w("finally") {
            let fs = self.t.start;
            self.bump()?;
            let b = self.parse_block(cx)?;
            end = self.en(b);
            self.mk(K::Finally, Op::None, false, fs, end, vec![b])
        } else {
            self.absent()
        };
        if self.kind(catch) == K::Absent && self.kind(finally) == K::Absent {
            return syn();
        }
        Ok(self.mk(K::TryStatement, Op::None, false, start, end, vec![block, catch, finally]))
    }

    // ----- for (§14.7.4, §14.7.5) --------------------------------------

    /// `for ( ... ) Statement` in all its forms.
    fn parse_for(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let is_await = if self.t.is_w("await") {
            if !cx.a {
                return syn();
            }
            self.bump()?;
            true
        } else {
            false
        };
        self.expect_p("(")?;
        let cxn = cx.with_in(false);
        // The initializer, or the head of `for-in` and `for-of`.
        if self.t.is_p(";") {
            if is_await {
                return syn();
            }
            let init = self.absent();
            return self.parse_for_rest(cx, start, init);
        }
        if self.t.is_w("var") || self.t.is_w("const") || (self.t.is_w("let") && self.let_starts_declaration()?) {
            let dstart = self.t.start;
            let op = if self.t.is_w("var") {
                Op::Var
            } else if self.t.is_w("let") {
                Op::Let
            } else {
                Op::Const
            };
            let (decl_kind, list_kind) = if op == Op::Var {
                (K::VariableDeclaration, K::VariableDeclarationList)
            } else {
                (K::LexicalBinding, K::LexicalDeclaration)
            };
            self.bump()?;
            let first = self.parse_binding_decl(cxn, decl_kind, true)?;
            if self.t.is_w("of") || self.t.is_w("in") {
                let of = self.t.is_w("of");
                let target = self.child(first, 0);
                let has_init = self.kind(self.child(first, 1)) != K::Absent;
                let binding = if has_init {
                    // Annex B.3.5: `for (var a = 1 in x)`.
                    if of || op != Op::Var || self.kind(target) != K::BindingIdentifier {
                        return syn();
                    }
                    first
                } else {
                    target
                };
                let head = self.mk(K::ForDeclaration, op, false, dstart, self.en(first), vec![binding]);
                return self.parse_for_in_of(cx, start, head, of, is_await);
            }
            if is_await {
                return syn();
            }
            // A classic `for`: the rest of the list.
            let mut kids = vec![first];
            if self.kind(self.child(first, 1)) == K::Absent && self.kind(self.child(first, 0)) != K::BindingIdentifier {
                return syn();
            }
            while self.eat_p(",")? {
                kids.push(self.parse_binding_decl(cxn, decl_kind, false)?);
            }
            let init = if op == Op::Var {
                let end = self.prev_end;
                self.mk(list_kind, Op::None, false, dstart, end, kids)
            } else {
                // A `LexicalDeclaration` takes a real `;` (§12.10.1, rule 4).
                if !self.t.is_p(";") {
                    return syn();
                }
                let end = self.t.end;
                self.bump()?;
                let d = self.mk(list_kind, op, false, dstart, end, kids);
                return self.parse_for_after_init(cx, start, d, false);
            };
            return self.parse_for_rest(cx, start, init);
        }
        // An expression, or a `LeftHandSideExpression` or pattern before `in`/`of`.
        let first_is_let = self.t.is_w("let");
        let first_is_async = self.t.is_w("async");
        let e0 = self.parse_assign(cxn)?;
        if self.t.is_w("of") || self.t.is_w("in") {
            let of = self.t.is_w("of");
            if of && (first_is_let || (first_is_async && !is_await && self.kind(e0) == K::IdentifierReference)) {
                return syn();
            }
            let head = self.as_assign_target(e0)?;
            if self.lvl(head) < 14 && !matches!(self.kind(head), K::ObjectAssignmentPattern | K::ArrayAssignmentPattern) {
                return syn();
            }
            return self.parse_for_in_of(cx, start, head, of, is_await);
        }
        if is_await {
            return syn();
        }
        let init = if self.t.is_p(",") {
            let s = self.st(e0);
            let mut items = vec![e0];
            let mut end = self.en(e0);
            while self.eat_p(",")? {
                let e = self.parse_assign(cxn)?;
                end = self.en(e);
                items.push(e);
            }
            self.mk(K::Expression, Op::None, false, s, end, items)
        } else {
            e0
        };
        self.parse_for_rest(cx, start, init)
    }

    /// After a classic `for`'s initializer (not a `LexicalDeclaration`): the `;`.
    fn parse_for_rest(&mut self, cx: Cx, start: usize, init: u32) -> R<u32> {
        self.expect_p(";")?;
        self.parse_for_after_init(cx, start, init, true)
    }

    /// The test, the update and the body of a classic `for`.
    fn parse_for_after_init(&mut self, cx: Cx, start: usize, init: u32, _semi_done: bool) -> R<u32> {
        let cxi = cx.with_in(true);
        let test = if self.t.is_p(";") { self.absent() } else { self.parse_expression(cxi)? };
        self.expect_p(";")?;
        let update = if self.t.is_p(")") { self.absent() } else { self.parse_expression(cxi)? };
        self.expect_p(")")?;
        let body = self.parse_statement(cx)?;
        let end = self.en(body);
        Ok(self.mk(K::ForStatement, Op::None, false, start, end, vec![init, test, update, body]))
    }

    /// `for ( head in/of expression ) Statement`, at the `in` or `of`.
    fn parse_for_in_of(&mut self, cx: Cx, start: usize, head: u32, of: bool, is_await: bool) -> R<u32> {
        if is_await && !of {
            return syn();
        }
        self.bump()?;
        let cxi = cx.with_in(true);
        let e = if of { self.parse_assign(cxi)? } else { self.parse_expression(cxi)? };
        self.expect_p(")")?;
        let body = self.parse_statement(cx)?;
        let end = self.en(body);
        let kind = if of { K::ForOfStatement } else { K::ForInStatement };
        Ok(self.mk(kind, Op::None, is_await, start, end, vec![head, e, body]))
    }

    // ----- Binding patterns (§14.3.3) ----------------------------------

    /// `BindingIdentifier` or `BindingPattern`.
    pub fn parse_binding_target(&mut self, cx: Cx) -> R<u32> {
        if self.t.is_p("[") {
            self.nest(|p| p.parse_array_binding(cx))
        } else if self.t.is_p("{") {
            self.nest(|p| p.parse_object_binding(cx))
        } else {
            self.parse_ident(K::BindingIdentifier, cx)
        }
    }

    /// `BindingElement` (and `SingleNameBinding`): a target with an optional initializer.
    pub fn parse_binding_element(&mut self, cx: Cx) -> R<u32> {
        let target = self.parse_binding_target(cx)?;
        let start = self.st(target);
        let (init, end) = if self.t.is_p("=") {
            self.bump()?;
            let e = self.parse_assign(cx.with_in(true))?;
            (e, self.en(e))
        } else {
            (self.absent(), self.en(target))
        };
        Ok(self.mk(K::BindingElement, Op::None, false, start, end, vec![target, init]))
    }

    fn parse_array_binding(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let mut kids = Vec::new();
        while !self.t.is_p("]") {
            if self.t.eof {
                return syn();
            }
            if self.t.is_p(",") {
                let (s, e) = (self.t.start, self.t.end);
                self.bump()?;
                kids.push(self.leaf(K::Elision, s, e));
                continue;
            }
            if self.t.is_p("...") {
                let s = self.t.start;
                self.bump()?;
                let t = self.parse_binding_target(cx)?;
                let e = self.en(t);
                kids.push(self.mk(K::BindingRestElement, Op::None, false, s, e, vec![t]));
                if !self.t.is_p("]") {
                    return syn();
                }
                break;
            }
            kids.push(self.parse_binding_element(cx)?);
            if !self.eat_p(",")? && !self.t.is_p("]") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::ArrayBindingPattern, Op::None, false, start, end, kids))
    }

    fn parse_object_binding(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let mut kids = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            let ps = self.t.start;
            if self.t.is_p("...") {
                self.bump()?;
                let t = self.parse_ident(K::BindingIdentifier, cx)?;
                let e = self.en(t);
                kids.push(self.mk(K::BindingRestProperty, Op::None, false, ps, e, vec![t]));
                if !self.t.is_p("}") {
                    return syn();
                }
                break;
            }
            let shorthand = self.t.is_name() && !self.peek()?.is_p(":");
            if shorthand {
                let bi = self.parse_ident(K::BindingIdentifier, cx)?;
                let (init, end) = if self.t.is_p("=") {
                    self.bump()?;
                    let e = self.parse_assign(cx.with_in(true))?;
                    (e, self.en(e))
                } else {
                    (self.absent(), self.en(bi))
                };
                let el = self.mk(K::BindingElement, Op::None, false, ps, end, vec![bi, init]);
                kids.push(self.mk(K::BindingProperty, Op::Shorthand, false, ps, end, vec![el]));
            } else {
                let name = self.parse_prop_name(cx)?;
                self.expect_p(":")?;
                let el = self.parse_binding_element(cx)?;
                let end = self.en(el);
                kids.push(self.mk(K::BindingProperty, Op::KeyValue, false, ps, end, vec![name, el]));
            }
            if !self.eat_p(",")? && !self.t.is_p("}") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::ObjectBindingPattern, Op::None, false, start, end, kids))
    }

    // ----- Functions (§15) ---------------------------------------------

    /// `FormalParameters`, from `(` to `)`.
    pub fn parse_formal_params(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.expect_p("(")?;
        let mut kids = Vec::new();
        while !self.t.is_p(")") {
            if self.t.eof {
                return syn();
            }
            if self.t.is_p("...") {
                let s = self.t.start;
                self.bump()?;
                let t = self.parse_binding_target(cx)?;
                let e = self.en(t);
                kids.push(self.mk(K::FunctionRestParameter, Op::None, false, s, e, vec![t]));
                if !self.t.is_p(")") {
                    return syn();
                }
                break;
            }
            kids.push(self.parse_binding_element(cx)?);
            if !self.eat_p(",")? && !self.t.is_p(")") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::FormalParameters, Op::None, false, start, end, kids))
    }

    /// `FunctionBody` and its relatives: `{ StatementList }`.
    pub fn parse_function_body(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.expect_p("{")?;
        let items = self.parse_items_until_brace(cx)?;
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::FunctionBody, Op::None, false, start, end, items))
    }

    /// A function, generator, async function or async generator, declaration
    /// or expression, at `function` (or at `async` when `async_start`).
    /// `deflt`: the name may be absent (`export default`).
    pub fn parse_function(&mut self, cx: Cx, async_start: Option<usize>, is_expr: bool, deflt: bool) -> R<u32> {
        self.nest(|p| p.parse_function_inner(cx, async_start, is_expr, deflt))
    }

    fn parse_function_inner(&mut self, cx: Cx, async_start: Option<usize>, is_expr: bool, deflt: bool) -> R<u32> {
        let start = async_start.unwrap_or(self.t.start);
        let is_async = async_start.is_some();
        if is_async {
            self.bump()?;
        }
        self.expect_w("function")?;
        let is_gen = self.eat_p("*")?;
        let fcx = Cx { y: is_gen, a: is_async, i: true, r: false };
        let name = if is_expr {
            if self.t.is_name() && !self.t.is_p("(") {
                self.parse_ident(K::BindingIdentifier, fcx)?
            } else {
                self.absent()
            }
        } else if self.t.is_name() && self.ident_ok(cx) {
            self.parse_ident(K::BindingIdentifier, cx)?
        } else if deflt {
            self.absent()
        } else {
            return syn();
        };
        let params = self.parse_formal_params(fcx)?;
        let body = self.parse_function_body(Cx { r: true, ..fcx })?;
        let end = self.en(body);
        let kind = match (is_async, is_gen, is_expr) {
            (false, false, false) => K::FunctionDeclaration,
            (false, false, true) => K::FunctionExpression,
            (false, true, false) => K::GeneratorDeclaration,
            (false, true, true) => K::GeneratorExpression,
            (true, false, false) => K::AsyncFunctionDeclaration,
            (true, false, true) => K::AsyncFunctionExpression,
            (true, true, false) => K::AsyncGeneratorDeclaration,
            (true, true, true) => K::AsyncGeneratorExpression,
        };
        Ok(self.mk(kind, Op::None, false, start, end, vec![name, params, body]))
    }

    /// The rest of a `MethodDefinition` (§15.4) after its name: `( ... ) { ... }`.
    pub fn parse_method(&mut self, _cx: Cx, op: Op, is_static: bool, start: usize, name: u32) -> R<u32> {
        let is_gen = matches!(op, Op::GeneratorMethod | Op::AsyncGeneratorMethod);
        let is_async = matches!(op, Op::AsyncMethod | Op::AsyncGeneratorMethod);
        let pcx = Cx { y: is_gen, a: is_async, i: true, r: false };
        let params = self.parse_formal_params(pcx)?;
        let n = self.nchildren(params);
        match op {
            Op::Getter if n != 0 => return syn(),
            Op::Setter if n != 1 || self.kind(self.child(params, 0)) != K::BindingElement => return syn(),
            _ => {}
        }
        let body = self.parse_function_body(Cx { r: true, ..pcx })?;
        let end = self.en(body);
        Ok(self.mk(K::MethodDefinition, op, is_static, start, end, vec![name, params, body]))
    }

    // ----- Classes (§15.7) ---------------------------------------------

    /// `ClassDeclaration` or `ClassExpression`, at `class`.
    pub fn parse_class(&mut self, cx: Cx, is_expr: bool, deflt: bool) -> R<u32> {
        self.nest(|p| p.parse_class_inner(cx, is_expr, deflt))
    }

    fn parse_class_inner(&mut self, cx: Cx, is_expr: bool, deflt: bool) -> R<u32> {
        let start = self.t.start;
        self.expect_w("class")?;
        let name = if self.t.is_name() && self.ident_ok(cx) {
            self.parse_ident(K::BindingIdentifier, cx)?
        } else if is_expr || deflt {
            self.absent()
        } else {
            return syn();
        };
        let heritage = if self.t.is_w("extends") {
            self.bump()?;
            self.parse_lhs(cx)?
        } else {
            self.absent()
        };
        let body = self.parse_class_body(cx)?;
        let end = self.en(body);
        let kind = if is_expr { K::ClassExpression } else { K::ClassDeclaration };
        Ok(self.mk(kind, Op::None, false, start, end, vec![name, heritage, body]))
    }

    /// `ClassBody`.
    fn parse_class_body(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.expect_p("{")?;
        let mut kids = Vec::new();
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            if self.t.is_p(";") {
                self.bump()?;
                continue;
            }
            kids.push(self.parse_class_element(cx)?);
        }
        let end = self.t.end;
        self.bump()?;
        Ok(self.mk(K::ClassBody, Op::None, false, start, end, kids))
    }

    /// `ClassElementName`: a `PropertyName` or a `PrivateIdentifier`.
    fn parse_class_element_name(&mut self, cx: Cx) -> R<u32> {
        if self.t.kind == ElementKind::PrivateIdentifier && !self.t.eof {
            let (s, e) = (self.t.start, self.t.end);
            self.bump()?;
            Ok(self.leaf(K::PrivateIdentifier, s, e))
        } else {
            self.parse_prop_name(cx)
        }
    }

    /// One `ClassElement` that is not `;`.
    fn parse_class_element(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        let mut is_static = false;
        if self.t.is_w("static") {
            let nx = self.peek()?;
            if !self.ends_name(&nx) {
                is_static = true;
                self.bump()?;
                if self.t.is_p("{") {
                    let bcx = Cx { y: false, a: true, i: true, r: false };
                    let body = self.parse_function_body(bcx)?;
                    let end = self.en(body);
                    return Ok(self.mk(K::ClassStaticBlock, Op::None, false, start, end, vec![body]));
                }
            }
        }
        let mstart = self.t.start;
        let _ = mstart;
        if self.t.is_p("*") {
            self.bump()?;
            let name = self.parse_class_element_name(cx)?;
            return self.parse_method(cx, Op::GeneratorMethod, is_static, start, name);
        }
        if self.t.is_w("async") {
            let nx = self.peek()?;
            if !self.ends_name(&nx) && !nx.nl {
                self.bump()?;
                let op = if self.eat_p("*")? { Op::AsyncGeneratorMethod } else { Op::AsyncMethod };
                let name = self.parse_class_element_name(cx)?;
                return self.parse_method(cx, op, is_static, start, name);
            }
        }
        if self.t.is_w("get") || self.t.is_w("set") {
            let nx = self.peek()?;
            if !self.ends_name(&nx) {
                let op = if self.t.is_w("get") { Op::Getter } else { Op::Setter };
                self.bump()?;
                let name = self.parse_class_element_name(cx)?;
                return self.parse_method(cx, op, is_static, start, name);
            }
        }
        let name = self.parse_class_element_name(cx)?;
        if self.t.is_p("(") {
            return self.parse_method(cx, Op::Method, is_static, start, name);
        }
        // A field.
        let init = if self.t.is_p("=") {
            self.bump()?;
            self.parse_assign(Cx { y: false, a: false, i: true, r: false })?
        } else {
            self.absent()
        };
        let end = self.semi()?;
        Ok(self.mk(K::FieldDefinition, Op::None, is_static, start, end, vec![name, init]))
    }
}

/// The ASCII word `n` as a `&str` if it is short and ASCII, `""` otherwise.
fn word_of(n: &[u32]) -> &'static str {
    const RESERVED: &[&str] = &[
        "break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do",
        "else", "enum", "export", "extends", "false", "finally", "for", "function", "if", "import",
        "in", "instanceof", "new", "null", "return", "super", "switch", "this", "throw", "true",
        "try", "typeof", "var", "void", "while", "with",
    ];
    for w in RESERVED {
        if crate::token::name_is(n, w) {
            return w;
        }
    }
    ""
}
