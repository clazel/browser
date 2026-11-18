//! The parser's expressions (ECMA-262 §13, §15.3, §15.5, §15.9) and its
//! patterns: precedence climbing for the binary operators, and the cover
//! grammars (§13.2.9, §13.15.5) read as the refined production by converting
//! the arena nodes once the token that decides (`=`, `=>`) is seen
//! ([`crate::cover`]).

use crate::ast::{NodeKind as K, Op};
use crate::parser::{Cx, Cover, Parser, R, syn};
use clazel_js_lexer::spec::{ElementKind, TemplateKind};

/// The cx of the body of an arrow function with a braced body, and of its
/// expression body (`In` kept by the caller).
fn arrow_body_cx(is_async: bool, i: bool, braced: bool) -> Cx {
    Cx { y: false, a: is_async, i: if braced { true } else { i }, r: braced }
}

impl<'a> Parser<'a> {
    // ----- Expression, AssignmentExpression (§13.15, §13.16) -----------

    /// `Expression`: assignment expressions separated by `,` (§13.16).
    pub fn parse_expression(&mut self, cx: Cx) -> R<u32> {
        let first = self.parse_assign(cx)?;
        if !self.t.is_p(",") {
            return Ok(first);
        }
        let start = self.st(first);
        let mut items = vec![first];
        let mut end = self.en(first);
        while self.t.is_p(",") {
            self.bump()?;
            let e = self.parse_assign(cx)?;
            end = self.en(e);
            items.push(e);
        }
        Ok(self.mk(K::Expression, Op::None, false, start, end, items))
    }

    /// `AssignmentExpression`, `ArrowFunction`, `AsyncArrowFunction` and
    /// `YieldExpression`.
    pub fn parse_assign(&mut self, cx: Cx) -> R<u32> {
        self.nest(|p| p.parse_assign_inner(cx))
    }

    fn parse_assign_inner(&mut self, cx: Cx) -> R<u32> {
        if cx.y && self.t.is_w("yield") {
            return self.parse_yield(cx);
        }
        if self.t.is_name() {
            // `x => ...` and `async x => ...`.
            let nx = self.peek()?;
            if self.t.is_w("async") && !nx.nl && nx.is_name() && !matches!(nx.s, "function" | "in" | "instanceof")
            {
                let nx2 = self.peek_after(&nx)?;
                if nx2.is_p("=>") && !nx2.nl {
                    return self.parse_async_ident_arrow(cx);
                }
            }
            if nx.is_p("=>") && !nx.nl && self.ident_ok(cx) {
                let p = self.parse_ident(K::BindingIdentifier, cx)?;
                return self.parse_arrow_rest(cx, p, self.st(p), false);
            }
        }
        let lhs = self.parse_cond(cx)?;
        if self.t.is_p("=>") {
            return self.parse_arrow_from_cover(cx, lhs);
        }
        if let Some(op) = self.assign_op() {
            let ok = if op == Op::Assign {
                matches!(self.kind(lhs), K::ObjectLiteral | K::ArrayLiteral) || self.lvl(lhs) >= 14
            } else {
                self.lvl(lhs) >= 14
            };
            if !ok {
                return syn();
            }
            let target = if op == Op::Assign { self.as_assign_target(lhs)? } else { lhs };
            self.bump()?;
            let rhs = self.parse_assign(cx)?;
            let (s, e) = (self.st(lhs), self.en(rhs));
            return Ok(self.mk(K::AssignmentExpression, op, false, s, e, vec![target, rhs]));
        }
        Ok(lhs)
    }

    /// The assignment operator at the current token.
    fn assign_op(&self) -> Option<Op> {
        if self.t.eof || !matches!(self.t.kind, ElementKind::Punctuator | ElementKind::DivPunctuator) {
            return None;
        }
        Some(match self.t.s {
            "=" => Op::Assign,
            "*=" => Op::MulAssign,
            "/=" => Op::DivAssign,
            "%=" => Op::RemAssign,
            "+=" => Op::AddAssign,
            "-=" => Op::SubAssign,
            "<<=" => Op::ShlAssign,
            ">>=" => Op::ShrAssign,
            ">>>=" => Op::UShrAssign,
            "&=" => Op::BitAndAssign,
            "^=" => Op::BitXorAssign,
            "|=" => Op::BitOrAssign,
            "**=" => Op::ExpAssign,
            "&&=" => Op::LogicalAndAssign,
            "||=" => Op::LogicalOrAssign,
            "??=" => Op::CoalesceAssign,
            _ => return None,
        })
    }

    /// §15.5 `YieldExpression`.
    fn parse_yield(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        let kw_end = self.t.end;
        self.bump()?;
        let ends = self.t.nl
            || self.t.eof
            || (!self.t.is_name() && matches!(self.t.s, ")" | "]" | "}" | "," | ";" | ":" | "?" | "=>"))
            || self.t.is_w("in")
            || matches!(self.t.kind, ElementKind::Template(TemplateKind::Middle | TemplateKind::Tail));
        if ends {
            let a = self.absent();
            return Ok(self.mk(K::YieldExpression, Op::YieldPlain, false, start, kw_end, vec![a]));
        }
        let delegate = self.eat_p("*")?;
        let e = self.parse_assign(cx)?;
        let op = if delegate { Op::YieldDelegate } else { Op::YieldPlain };
        let end = self.en(e);
        Ok(self.mk(K::YieldExpression, op, false, start, end, vec![e]))
    }

    /// `ConditionalExpression` (§13.14).
    fn parse_cond(&mut self, cx: Cx) -> R<u32> {
        let test = self.parse_binary(cx, 0)?;
        if !self.t.is_p("?") {
            return Ok(test);
        }
        self.bump()?;
        let cons = self.parse_assign(cx.with_in(true))?;
        self.expect_p(":")?;
        let alt = self.parse_assign(cx)?;
        let (s, e) = (self.st(test), self.en(alt));
        Ok(self.mk(K::ConditionalExpression, Op::None, false, s, e, vec![test, cons, alt]))
    }

    /// The binary operator at the current token and its precedence (§13.6 to
    /// §13.13: `??` 0, `||` 1, `&&` 2, `|` 3, `^` 4, `&` 5, equality 6,
    /// relational 7, shift 8, additive 9, multiplicative 10).
    fn binary_op(&self, cx: Cx) -> Option<(K, Op, u8)> {
        if self.t.eof {
            return None;
        }
        if self.t.is_name() {
            return match self.t.s {
                "instanceof" => Some((K::RelationalExpression, Op::InstanceOf, 7)),
                "in" if cx.i => Some((K::RelationalExpression, Op::In, 7)),
                _ => None,
            };
        }
        if !matches!(self.t.kind, ElementKind::Punctuator | ElementKind::DivPunctuator) {
            return None;
        }
        Some(match self.t.s {
            "??" => (K::CoalesceExpression, Op::Coalesce, 0),
            "||" => (K::LogicalORExpression, Op::LogicalOr, 1),
            "&&" => (K::LogicalANDExpression, Op::LogicalAnd, 2),
            "|" => (K::BitwiseORExpression, Op::BitOr, 3),
            "^" => (K::BitwiseXORExpression, Op::BitXor, 4),
            "&" => (K::BitwiseANDExpression, Op::BitAnd, 5),
            "==" => (K::EqualityExpression, Op::Eq, 6),
            "!=" => (K::EqualityExpression, Op::Ne, 6),
            "===" => (K::EqualityExpression, Op::StrictEq, 6),
            "!==" => (K::EqualityExpression, Op::StrictNe, 6),
            "<" => (K::RelationalExpression, Op::Lt, 7),
            ">" => (K::RelationalExpression, Op::Gt, 7),
            "<=" => (K::RelationalExpression, Op::Le, 7),
            ">=" => (K::RelationalExpression, Op::Ge, 7),
            "<<" => (K::ShiftExpression, Op::Shl, 8),
            ">>" => (K::ShiftExpression, Op::Shr, 8),
            ">>>" => (K::ShiftExpression, Op::UShr, 8),
            "+" => (K::AdditiveExpression, Op::Add, 9),
            "-" => (K::AdditiveExpression, Op::Sub, 9),
            "*" => (K::MultiplicativeExpression, Op::Mul, 10),
            "/" => (K::MultiplicativeExpression, Op::Div, 10),
            "%" => (K::MultiplicativeExpression, Op::Rem, 10),
            _ => return None,
        })
    }

    /// The binary operators of precedence at least `min` (precedence climbing).
    fn parse_binary(&mut self, cx: Cx, min: u8) -> R<u32> {
        let mut left = if self.t.kind == ElementKind::PrivateIdentifier && !self.t.eof {
            // §13.10 `RelationalExpression : PrivateIdentifier in ShiftExpression`.
            let nx = self.peek()?;
            if !(nx.is_w("in") && cx.i && min <= 7) {
                return syn();
            }
            let (s, e) = (self.t.start, self.t.end);
            self.bump()?;
            self.leaf(K::PrivateIdentifier, s, e)
        } else {
            self.parse_exp(cx)?
        };
        while let Some((kind, op, prec)) = self.binary_op(cx) {
            if prec < min {
                break;
            }
            let mixes = match kind {
                K::CoalesceExpression => !(self.lvl(left) >= 3 || self.kind(left) == K::CoalesceExpression),
                K::LogicalORExpression | K::LogicalANDExpression => self.kind(left) == K::CoalesceExpression,
                _ => false,
            };
            if mixes {
                return syn();
            }
            if self.kind(left) == K::PrivateIdentifier && op != Op::In {
                return syn();
            }
            self.bump()?;
            let right = if kind == K::CoalesceExpression {
                self.parse_binary(cx, 3)?
            } else {
                self.parse_binary(cx, prec.saturating_add(1))?
            };
            let (s, e) = (self.st(left), self.en(right));
            left = self.mk(kind, op, false, s, e, vec![left, right]);
        }
        if self.kind(left) == K::PrivateIdentifier {
            return syn();
        }
        Ok(left)
    }

    /// `ExponentiationExpression` (§13.6): `UpdateExpression ** ExponentiationExpression`
    /// or a `UnaryExpression`.
    fn parse_exp(&mut self, cx: Cx) -> R<u32> {
        let u = self.parse_unary(cx)?;
        if !self.t.is_p("**") {
            return Ok(u);
        }
        if self.lvl(u) < 13 {
            return syn();
        }
        self.bump()?;
        let r = self.nest(|p| p.parse_exp(cx))?;
        let (s, e) = (self.st(u), self.en(r));
        Ok(self.mk(K::ExponentiationExpression, Op::Exp, false, s, e, vec![u, r]))
    }

    /// `UnaryExpression` (§13.5), `UpdateExpression` (§13.4), `AwaitExpression`.
    fn parse_unary(&mut self, cx: Cx) -> R<u32> {
        if self.t.eof {
            return syn();
        }
        let start = self.t.start;
        let op = if self.t.is_name() {
            match self.t.s {
                "delete" => Some(Op::Delete),
                "void" => Some(Op::Void),
                "typeof" => Some(Op::Typeof),
                _ => None,
            }
        } else if matches!(self.t.kind, ElementKind::Punctuator) {
            match self.t.s {
                "+" => Some(Op::Plus),
                "-" => Some(Op::Minus),
                "~" => Some(Op::BitNot),
                "!" => Some(Op::LogicalNot),
                "++" => Some(Op::PrefixIncrement),
                "--" => Some(Op::PrefixDecrement),
                _ => None,
            }
        } else {
            None
        };
        if let Some(op) = op {
            self.bump()?;
            let operand = self.nest(|p| p.parse_unary(cx))?;
            let end = self.en(operand);
            let kind = if matches!(op, Op::PrefixIncrement | Op::PrefixDecrement) {
                K::UpdateExpression
            } else {
                K::UnaryExpression
            };
            return Ok(self.mk(kind, op, false, start, end, vec![operand]));
        }
        if cx.a && self.t.is_w("await") {
            self.bump()?;
            let operand = self.nest(|p| p.parse_unary(cx))?;
            let end = self.en(operand);
            return Ok(self.mk(K::AwaitExpression, Op::None, false, start, end, vec![operand]));
        }
        let e = self.parse_lhs(cx)?;
        if (self.t.is_p("++") || self.t.is_p("--")) && !self.t.nl {
            let op = if self.t.is_p("++") { Op::PostfixIncrement } else { Op::PostfixDecrement };
            let end = self.t.end;
            self.bump()?;
            let s = self.st(e);
            return Ok(self.mk(K::UpdateExpression, op, false, s, end, vec![e]));
        }
        Ok(e)
    }

    // ----- LeftHandSideExpression (§13.3) ------------------------------

    /// `LeftHandSideExpression`: member, call and optional chain expressions.
    pub fn parse_lhs(&mut self, cx: Cx) -> R<u32> {
        let mut e = if self.t.is_w("new") {
            self.nest(|p| p.parse_new(cx))?
        } else if self.t.is_w("super") {
            self.parse_super(cx)?
        } else if self.t.is_w("import") {
            self.parse_import_expr(cx)?
        } else {
            self.parse_primary(cx)?
        };
        loop {
            if self.t.eof {
                break;
            }
            if self.t.is_p(".") {
                e = self.parse_dot(e)?;
            } else if self.t.is_p("[") {
                e = self.parse_bracket(cx, e)?;
            } else if self.t.is_p("(") {
                let callee_is_async = self.kind(e) == K::IdentifierReference
                    && self.en(e).saturating_sub(self.st(e)) == 5
                    && !self.t.nl
                    && self.src.get(self.st(e)..self.en(e)).is_some_and(|t| crate::token::name_is(t, "async"));
                let args = self.parse_arguments(cx)?;
                let (s, en) = (self.st(e), self.en(args));
                if !matches!(self.lvl(e), 15 | 17) {
                    return syn();
                }
                let call = self.mk(K::CallExpression, Op::None, false, s, en, vec![e, args]);
                if callee_is_async {
                    self.async_calls.insert(call);
                }
                e = call;
            } else if self.t.kind == ElementKind::Template(TemplateKind::NoSubstitution)
                || self.t.kind == ElementKind::Template(TemplateKind::Head)
            {
                e = self.parse_tagged(cx, e)?;
            } else if self.t.is_p("?.") {
                return self.parse_optional(cx, e);
            } else {
                break;
            }
        }
        Ok(e)
    }

    /// `MemberExpression . IdentifierName` and `. PrivateIdentifier`.
    fn parse_dot(&mut self, obj: u32) -> R<u32> {
        if !matches!(self.lvl(obj), 15 | 17) {
            return syn();
        }
        self.bump()?;
        let (s, e) = (self.t.start, self.t.end);
        let (name, op) = if self.t.is_name() {
            (self.leaf(K::IdentifierName, s, e), Op::Dot)
        } else if self.t.kind == ElementKind::PrivateIdentifier && !self.t.eof {
            (self.leaf(K::PrivateIdentifier, s, e), Op::PrivateDot)
        } else {
            return syn();
        };
        self.bump()?;
        let os = self.st(obj);
        Ok(self.mk(K::MemberExpression, op, false, os, e, vec![obj, name]))
    }

    /// `MemberExpression [ Expression ]`.
    fn parse_bracket(&mut self, cx: Cx, obj: u32) -> R<u32> {
        if !matches!(self.lvl(obj), 15 | 17) {
            return syn();
        }
        self.bump()?;
        let idx = self.parse_expression(cx.with_in(true))?;
        let end = self.t.end;
        self.expect_p("]")?;
        let os = self.st(obj);
        Ok(self.mk(K::MemberExpression, Op::Bracket, false, os, end, vec![obj, idx]))
    }

    /// `MemberExpression TemplateLiteral[+Tagged]`.
    fn parse_tagged(&mut self, cx: Cx, tag: u32) -> R<u32> {
        if !matches!(self.lvl(tag), 15 | 17) {
            return syn();
        }
        let tpl = self.parse_template(cx, true)?;
        let (s, e) = (self.st(tag), self.en(tpl));
        Ok(self.mk(K::TaggedTemplate, Op::None, false, s, e, vec![tag, tpl]))
    }

    /// §13.3.9 `OptionalExpression`: the base and then its links.
    fn parse_optional(&mut self, cx: Cx, base: u32) -> R<u32> {
        if !matches!(self.lvl(base), 15 | 17) {
            return syn();
        }
        let start = self.st(base);
        let mut kids = vec![base];
        let mut end = self.en(base);
        loop {
            if self.t.eof {
                break;
            }
            let flag = self.t.is_p("?.");
            let link_start = self.t.start;
            if flag {
                self.bump()?;
                if self.t.kind == ElementKind::Template(TemplateKind::NoSubstitution)
                    || self.t.kind == ElementKind::Template(TemplateKind::Head)
                {
                    return syn();
                }
            } else if !(self.t.is_p(".") || self.t.is_p("[") || self.t.is_p("(")) {
                if self.t.kind == ElementKind::Template(TemplateKind::NoSubstitution)
                    || self.t.kind == ElementKind::Template(TemplateKind::Head)
                {
                    return syn();
                }
                break;
            }
            let link = if self.t.is_p("(") {
                let args = self.parse_arguments(cx)?;
                end = self.en(args);
                self.mk(K::OptionalChain, Op::ChainCall, flag, link_start, end, vec![args])
            } else if self.t.is_p("[") {
                self.bump()?;
                let idx = self.parse_expression(cx.with_in(true))?;
                end = self.t.end;
                self.expect_p("]")?;
                self.mk(K::OptionalChain, Op::ChainBracket, flag, link_start, end, vec![idx])
            } else {
                if !flag {
                    // `.`
                    self.bump()?;
                }
                let (s, e) = (self.t.start, self.t.end);
                let (name, op) = if self.t.is_name() {
                    (self.leaf(K::IdentifierName, s, e), Op::ChainDot)
                } else if self.t.kind == ElementKind::PrivateIdentifier && !self.t.eof {
                    (self.leaf(K::PrivateIdentifier, s, e), Op::ChainPrivateDot)
                } else {
                    return syn();
                };
                self.bump()?;
                end = e;
                self.mk(K::OptionalChain, op, flag, link_start, end, vec![name])
            };
            kids.push(link);
        }
        Ok(self.mk(K::OptionalExpression, Op::None, false, start, end, kids))
    }

    /// `Arguments` (§13.3.8).
    pub fn parse_arguments(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.expect_p("(")?;
        let cxi = cx.with_in(true);
        let mut items = Vec::new();
        while !self.t.is_p(")") {
            if self.t.eof {
                return syn();
            }
            let item = if self.t.is_p("...") {
                let s = self.t.start;
                self.bump()?;
                let e = self.parse_assign(cxi)?;
                let end = self.en(e);
                self.mk(K::SpreadElement, Op::None, false, s, end, vec![e])
            } else {
                self.parse_assign(cxi)?
            };
            items.push(item);
            if !self.eat_p(",")? {
                break;
            }
        }
        let end = self.t.end;
        self.expect_p(")")?;
        Ok(self.mk(K::Arguments, Op::None, false, start, end, items))
    }

    /// `new` (§13.3.5, §13.3.12).
    fn parse_new(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        if self.t.is_p(".") {
            self.bump()?;
            if !self.t.is_w("target") {
                return syn();
            }
            let end = self.t.end;
            self.bump()?;
            return Ok(self.leaf(K::NewTarget, start, end));
        }
        let callee = self.parse_member_no_call(cx)?;
        if self.t.is_p("(") {
            let args = self.parse_arguments(cx)?;
            let end = self.en(args);
            Ok(self.mk(K::NewExpression, Op::None, false, start, end, vec![callee, args]))
        } else {
            let a = self.absent();
            let end = self.en(callee);
            Ok(self.mk(K::NewExpression, Op::None, false, start, end, vec![callee, a]))
        }
    }

    /// The `MemberExpression` that is the callee of `new`: no call, no `?.`.
    fn parse_member_no_call(&mut self, cx: Cx) -> R<u32> {
        let mut e = if self.t.is_w("new") {
            self.nest(|p| p.parse_new(cx))?
        } else if self.t.is_w("super") {
            let s = self.parse_super(cx)?;
            if self.kind(s) == K::SuperCall {
                return syn();
            }
            s
        } else if self.t.is_w("import") {
            let i = self.parse_import_expr(cx)?;
            if self.kind(i) != K::ImportMeta {
                return syn();
            }
            i
        } else {
            self.parse_primary(cx)?
        };
        loop {
            if self.t.eof {
                break;
            }
            if self.t.is_p(".") {
                e = self.parse_dot(e)?;
            } else if self.t.is_p("[") {
                e = self.parse_bracket(cx, e)?;
            } else if self.t.kind == ElementKind::Template(TemplateKind::NoSubstitution)
                || self.t.kind == ElementKind::Template(TemplateKind::Head)
            {
                e = self.parse_tagged(cx, e)?;
            } else {
                break;
            }
        }
        Ok(e)
    }

    /// `super . IdentifierName`, `super [ Expression ]` and `super Arguments` (§13.3.7).
    fn parse_super(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        if self.t.is_p("(") {
            let args = self.parse_arguments(cx)?;
            let end = self.en(args);
            Ok(self.mk(K::SuperCall, Op::None, false, start, end, vec![args]))
        } else if self.t.is_p(".") {
            self.bump()?;
            if !self.t.is_name() {
                return syn();
            }
            let (s, e) = (self.t.start, self.t.end);
            let name = self.leaf(K::IdentifierName, s, e);
            self.bump()?;
            Ok(self.mk(K::SuperProperty, Op::Dot, false, start, e, vec![name]))
        } else if self.t.is_p("[") {
            self.bump()?;
            let idx = self.parse_expression(cx.with_in(true))?;
            let end = self.t.end;
            self.expect_p("]")?;
            Ok(self.mk(K::SuperProperty, Op::Bracket, false, start, end, vec![idx]))
        } else {
            syn()
        }
    }

    /// `import ( ... )` and `import . meta` (§13.3.10, §13.3.12).
    fn parse_import_expr(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        if self.t.is_p(".") {
            self.bump()?;
            if !self.t.is_w("meta") {
                return syn();
            }
            let end = self.t.end;
            self.bump()?;
            return Ok(self.leaf(K::ImportMeta, start, end));
        }
        self.expect_p("(")?;
        let cxi = cx.with_in(true);
        let spec = self.parse_assign(cxi)?;
        let mut opts = None;
        if self.eat_p(",")? && !self.t.is_p(")") {
            opts = Some(self.parse_assign(cxi)?);
            self.eat_p(",")?;
        }
        let end = self.t.end;
        self.expect_p(")")?;
        let o = match opts {
            Some(o) => o,
            None => {
                let p = self.prev_end;
                self.leaf(K::Absent, p, p)
            }
        };
        Ok(self.mk(K::ImportCall, Op::None, false, start, end, vec![spec, o]))
    }

    // ----- PrimaryExpression (§13.2) -----------------------------------

    /// `PrimaryExpression`.
    pub fn parse_primary(&mut self, cx: Cx) -> R<u32> {
        if self.t.eof {
            return syn();
        }
        let (s, e) = (self.t.start, self.t.end);
        match self.t.kind {
            ElementKind::IdentifierName => match self.t.s {
                "this" => {
                    self.bump()?;
                    Ok(self.leaf(K::ThisExpression, s, e))
                }
                "null" => {
                    self.bump()?;
                    Ok(self.leaf(K::NullLiteral, s, e))
                }
                "true" | "false" => {
                    self.bump()?;
                    Ok(self.leaf(K::BooleanLiteral, s, e))
                }
                "function" => self.parse_function(cx, None, true, false),
                "class" => self.parse_class(cx, true, false),
                "async" => {
                    let nx = self.peek()?;
                    if nx.is_w("function") && !nx.nl {
                        self.parse_function(cx, Some(s), true, false)
                    } else {
                        self.parse_ident(K::IdentifierReference, cx)
                    }
                }
                _ => self.parse_ident(K::IdentifierReference, cx),
            },
            ElementKind::NumericLiteral => {
                self.bump()?;
                Ok(self.leaf(K::NumericLiteral, s, e))
            }
            ElementKind::StringLiteral => {
                self.bump()?;
                Ok(self.leaf(K::StringLiteral, s, e))
            }
            // The first token is read with `InputElementHashbangOrRegExp`.
            ElementKind::RegularExpressionLiteral => {
                self.bump()?;
                Ok(self.leaf(K::RegularExpressionLiteral, s, e))
            }
            ElementKind::Template(TemplateKind::NoSubstitution | TemplateKind::Head) => {
                self.parse_template(cx, false)
            }
            ElementKind::Punctuator | ElementKind::DivPunctuator => match self.t.s {
                "(" => self.parse_paren(cx),
                "[" => self.parse_array(cx),
                "{" => self.parse_object(cx),
                "/" | "/=" => {
                    self.relex_regexp()?;
                    let (s, e) = (self.t.start, self.t.end);
                    self.bump()?;
                    Ok(self.leaf(K::RegularExpressionLiteral, s, e))
                }
                _ => syn(),
            },
            _ => syn(),
        }
    }

    /// `TemplateLiteral` (§13.2.8).
    pub fn parse_template(&mut self, cx: Cx, tagged: bool) -> R<u32> {
        let start = self.t.start;
        let mut kids = Vec::new();
        let cxi = cx.with_in(true);
        loop {
            let (s, e) = (self.t.start, self.t.end);
            let kind = self.t.kind;
            let first = kids.is_empty();
            let ok = match kind {
                ElementKind::Template(TemplateKind::NoSubstitution | TemplateKind::Head) => first,
                ElementKind::Template(TemplateKind::Middle | TemplateKind::Tail) => !first,
                _ => false,
            };
            if !ok || (!tagged && self.t.invalid_escape) {
                return syn();
            }
            let el = self.leaf(K::TemplateElement, s, e);
            kids.push(el);
            self.bump()?;
            match kind {
                ElementKind::Template(TemplateKind::NoSubstitution | TemplateKind::Tail) => {
                    return Ok(self.mk(K::TemplateLiteral, Op::None, false, start, e, kids));
                }
                _ => {
                    let ex = self.parse_expression(cxi)?;
                    kids.push(ex);
                    if !self.t.is_p("}") {
                        return syn();
                    }
                    self.relex_template_tail()?;
                }
            }
        }
    }

    /// `( ... )`: a `ParenthesizedExpression`, or the cover of an arrow
    /// function's parameters (§13.2.9).
    fn parse_paren(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let cxi = cx.with_in(true);
        let mut items: Vec<u32> = Vec::new();
        let mut trailing = false;
        let mut has_rest = false;
        while !self.t.is_p(")") {
            if self.t.eof {
                return syn();
            }
            if self.t.is_p("...") {
                let s = self.t.start;
                self.bump()?;
                let target = self.parse_binding_target(cxi)?;
                let end = self.en(target);
                let rest = self.mk(K::FunctionRestParameter, Op::None, false, s, end, vec![target]);
                items.push(rest);
                has_rest = true;
                if !self.t.is_p(")") {
                    return syn();
                }
                break;
            }
            let item = self.parse_assign(cxi)?;
            items.push(item);
            if self.t.is_p(",") {
                self.bump()?;
                if self.t.is_p(")") {
                    trailing = true;
                }
            } else if !self.t.is_p(")") {
                return syn();
            }
        }
        let end = self.t.end;
        self.expect_p(")")?;
        let cover_items = items.clone();
        let children = if items.len() == 1 && !trailing && !has_rest {
            items
        } else if items.len() >= 2 && !trailing && !has_rest {
            let (s, e) = (self.st(items.first().copied().unwrap_or(u32::MAX)), self.en(items.last().copied().unwrap_or(u32::MAX)));
            vec![self.mk(K::Expression, Op::None, false, s, e, items)]
        } else {
            items
        };
        let id = self.mk(K::ParenthesizedExpression, Op::None, false, start, end, children);
        if cover_items.is_empty() || trailing || has_rest {
            self.bad.insert(id);
        }
        self.covers.insert(id, Cover { items: cover_items });
        Ok(id)
    }

    /// `ArrayLiteral` (§13.2.4).
    fn parse_array(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let cxi = cx.with_in(true);
        let mut kids = Vec::new();
        let mut rest_comma = false;
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
            let is_spread = self.t.is_p("...");
            let item = if is_spread {
                let s = self.t.start;
                self.bump()?;
                let e = self.parse_assign(cxi)?;
                let end = self.en(e);
                self.mk(K::SpreadElement, Op::None, false, s, end, vec![e])
            } else {
                self.parse_assign(cxi)?
            };
            kids.push(item);
            if self.t.is_p(",") {
                if is_spread {
                    rest_comma = true;
                }
                self.bump()?;
            } else if !self.t.is_p("]") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        let id = self.mk(K::ArrayLiteral, Op::None, false, start, end, kids);
        if rest_comma {
            self.rest_comma.insert(id);
        }
        Ok(id)
    }

    /// `ObjectLiteral` (§13.2.5).
    fn parse_object(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let mut kids = Vec::new();
        let mut rest_comma = false;
        while !self.t.is_p("}") {
            if self.t.eof {
                return syn();
            }
            let p = self.parse_property(cx)?;
            let is_spread = self.kind(p) == K::PropertyDefinition && self.op(p) == Op::Spread;
            kids.push(p);
            if self.t.is_p(",") {
                if is_spread {
                    rest_comma = true;
                }
                self.bump()?;
            } else if !self.t.is_p("}") {
                return syn();
            }
        }
        let end = self.t.end;
        self.bump()?;
        let id = self.mk(K::ObjectLiteral, Op::None, false, start, end, kids);
        if rest_comma {
            self.rest_comma.insert(id);
        }
        Ok(id)
    }

    /// The token ends a property or class element name's modifier: what
    /// follows `get`, `set`, `async` or `static` when it is itself the name.
    pub fn ends_name(&self, t: &crate::token::Tok) -> bool {
        t.eof || (!t.is_name() && matches!(t.s, "," | ":" | "(" | "}" | "=" | ";"))
    }

    /// `PropertyName` (§13.2.5): an `IdentifierName`, `StringLiteral`,
    /// `NumericLiteral` or `ComputedPropertyName`.
    pub fn parse_prop_name(&mut self, cx: Cx) -> R<u32> {
        let (s, e) = (self.t.start, self.t.end);
        if self.t.eof {
            return syn();
        }
        match self.t.kind {
            ElementKind::IdentifierName => {
                self.bump()?;
                Ok(self.leaf(K::IdentifierName, s, e))
            }
            ElementKind::StringLiteral => {
                self.bump()?;
                Ok(self.leaf(K::StringLiteral, s, e))
            }
            ElementKind::NumericLiteral => {
                self.bump()?;
                Ok(self.leaf(K::NumericLiteral, s, e))
            }
            ElementKind::Punctuator if self.t.is_p("[") => {
                self.bump()?;
                let ex = self.parse_assign(cx.with_in(true))?;
                let end = self.t.end;
                self.expect_p("]")?;
                Ok(self.mk(K::ComputedPropertyName, Op::None, false, s, end, vec![ex]))
            }
            _ => syn(),
        }
    }

    /// One `PropertyDefinition` or `MethodDefinition` of an object literal.
    fn parse_property(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        if self.t.is_p("...") {
            self.bump()?;
            let e = self.parse_assign(cx.with_in(true))?;
            let end = self.en(e);
            return Ok(self.mk(K::PropertyDefinition, Op::Spread, false, start, end, vec![e]));
        }
        // Modifiers.
        if self.t.is_p("*") {
            self.bump()?;
            let name = self.parse_prop_name(cx)?;
            return self.parse_method(cx, Op::GeneratorMethod, false, start, name);
        }
        if self.t.is_w("async") {
            let nx = self.peek()?;
            if !self.ends_name(&nx) && !nx.nl {
                self.bump()?;
                let op = if self.eat_p("*")? { Op::AsyncGeneratorMethod } else { Op::AsyncMethod };
                let name = self.parse_prop_name(cx)?;
                return self.parse_method(cx, op, false, start, name);
            }
        }
        if self.t.is_w("get") || self.t.is_w("set") {
            let nx = self.peek()?;
            if !self.ends_name(&nx) {
                let op = if self.t.is_w("get") { Op::Getter } else { Op::Setter };
                self.bump()?;
                let name = self.parse_prop_name(cx)?;
                return self.parse_method(cx, op, false, start, name);
            }
        }
        // `name : value`, `name ( ... ) { ... }`, shorthand.
        if self.t.is_name() {
            let nx = self.peek()?;
            if !(nx.is_p(":") || nx.is_p("(")) {
                // Shorthand `x` or `x = init` (a `CoverInitializedName`).
                let id = self.parse_ident(K::IdentifierReference, cx)?;
                if self.t.is_p("=") {
                    self.bump()?;
                    let init = self.parse_assign(cx.with_in(true))?;
                    let end = self.en(init);
                    let n = self.mk(K::CoverInitializedName, Op::None, false, start, end, vec![id, init]);
                    self.bad.insert(n);
                    return Ok(n);
                }
                let end = self.en(id);
                return Ok(self.mk(K::PropertyDefinition, Op::Shorthand, false, start, end, vec![id]));
            }
        }
        let name = self.parse_prop_name(cx)?;
        if self.t.is_p("(") {
            return self.parse_method(cx, Op::Method, false, start, name);
        }
        self.expect_p(":")?;
        let v = self.parse_assign(cx.with_in(true))?;
        let end = self.en(v);
        Ok(self.mk(K::PropertyDefinition, Op::KeyValue, false, start, end, vec![name, v]))
    }

    // ----- Arrow functions (§15.3, §15.9) ------------------------------

    /// `async x => ...`, at `async`.
    fn parse_async_ident_arrow(&mut self, cx: Cx) -> R<u32> {
        let start = self.t.start;
        self.bump()?;
        let p = self.parse_ident(K::BindingIdentifier, Cx { a: true, ..cx })?;
        self.parse_arrow_rest(cx, p, start, true)
    }

    /// From `=>` on, with the parameters `params` (a `BindingIdentifier` or
    /// `FormalParameters`) already parsed; `start` is where the function starts.
    fn parse_arrow_rest(&mut self, cx: Cx, params: u32, start: usize, is_async: bool) -> R<u32> {
        if !self.t.is_p("=>") || self.t.nl {
            return syn();
        }
        self.bump()?;
        let kind = if is_async { K::AsyncArrowFunction } else { K::ArrowFunction };
        if self.t.is_p("{") {
            let body = self.parse_function_body(arrow_body_cx(is_async, cx.i, true))?;
            let end = self.en(body);
            Ok(self.mk(kind, Op::None, false, start, end, vec![params, body]))
        } else {
            let body = self.parse_assign(arrow_body_cx(is_async, cx.i, false))?;
            let end = self.en(body);
            Ok(self.mk(kind, Op::None, false, start, end, vec![params, body]))
        }
    }

    /// `lhs =>`: `lhs` is a parenthesized cover or an `async (...)` call.
    fn parse_arrow_from_cover(&mut self, cx: Cx, lhs: u32) -> R<u32> {
        if self.t.nl {
            return syn();
        }
        if self.kind(lhs) == K::ParenthesizedExpression && self.covers.contains_key(&lhs) {
            let items = self.covers.get(&lhs).map(|c| c.items.clone()).unwrap_or_default();
            let (s, e) = (self.st(lhs), self.en(lhs));
            let params = self.cover_to_params(&items, s, e)?;
            return self.parse_arrow_rest(cx, params, s, false);
        }
        if self.kind(lhs) == K::CallExpression && self.async_calls.contains(&lhs) {
            let callee = self.child(lhs, 0);
            let args = self.child(lhs, 1);
            let start = self.st(callee);
            let items = self.node(args).map(|n| n.children.clone()).unwrap_or_default();
            let (s, e) = (self.st(args), self.en(args));
            let mut conv = Vec::new();
            let n = items.len();
            for (k, it) in items.iter().enumerate() {
                if self.kind(*it) == K::SpreadElement {
                    if k.saturating_add(1) != n || self.args_trailing_comma(args) {
                        return syn();
                    }
                    let t = self.as_binding_target(self.child(*it, 0))?;
                    let (is_, ie) = (self.st(*it), self.en(*it));
                    conv.push(self.mk(K::FunctionRestParameter, Op::None, false, is_, ie, vec![t]));
                } else {
                    conv.push(*it);
                }
            }
            let params = self.cover_to_params(&conv, s, e)?;
            return self.parse_arrow_rest(cx, params, start, true);
        }
        syn()
    }

    /// Whether the `Arguments` node `args` ends with a `,` before its `)`.
    fn args_trailing_comma(&self, args: u32) -> bool {
        let Some(last) = self.node(args).and_then(|n| n.children.last().copied()) else {
            return false;
        };
        let e = self.en(last);
        crate::token::lex(self.src, e, clazel_js_lexer::spec::Goal::InputElementDiv, false)
            .is_some_and(|t| t.is_p(","))
    }

    /// The `FormalParameters` node of an arrow function, from the items of its
    /// cover (`span`: the `(` to the `)`).
    fn cover_to_params(&mut self, items: &[u32], s: usize, e: usize) -> R<u32> {
        let mut out = Vec::new();
        let n = items.len();
        for (k, it) in items.iter().enumerate() {
            if self.kind(*it) == K::FunctionRestParameter {
                if k.saturating_add(1) != n {
                    return syn();
                }
                out.push(*it);
            } else {
                out.push(self.as_binding_element(*it)?);
            }
        }
        Ok(self.mk(K::FormalParameters, Op::None, false, s, e, out))
    }
}
