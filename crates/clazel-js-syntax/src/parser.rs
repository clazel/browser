//! The recursive-descent parser: the core (tokens, nodes, ASI, the depth
//! counter). The grammar is in [`crate::expr`], [`crate::stmt`] and
//! [`crate::module`]; the early errors are in [`crate::early`].
//!
//! This is the *proposer* of the design: it is plain Rust, whose output is an
//! arena that [`crate::check::finish`] (proven in Verus) accepts only when it
//! is well formed, within the source text and within [`MAX_DEPTH`]. That the
//! arena is the *right* parse (the rest of [`crate::contract::parse_ensures`])
//! is not proven; it is tested (`tests/`).

use crate::api::ParseError;
use crate::ast::{Node, NodeKind, Op};
use crate::spec::MAX_DEPTH;
use crate::token::{Tok, lex, name_is, name_is_reserved};
use clazel_js_lexer::spec::{ElementKind, Goal};
use std::collections::{HashMap, HashSet};

/// The result of a parsing function.
pub type R<T> = Result<T, ParseError>;

/// The error for a source text that is not derived by the grammar.
pub fn syn<T>() -> R<T> {
    Err(ParseError::Syntax)
}

/// The grammar parameters `[Yield]`, `[Await]`, `[In]`, `[Return]` (§5.1.5).
#[derive(Clone, Copy)]
pub struct Cx {
    /// `[Yield]`.
    pub y: bool,
    /// `[Await]`.
    pub a: bool,
    /// `[In]`.
    pub i: bool,
    /// `[Return]`.
    pub r: bool,
}

impl Cx {
    /// The same context with `[In]` set.
    pub fn with_in(self, i: bool) -> Cx {
        Cx { i, ..self }
    }
}

/// What a `ParenthesizedExpression` read as the cover grammar of §13.2.9 holds,
/// for the case that an `=>` follows.
pub struct Cover {
    /// The items: assignment expressions, then maybe a `FunctionRestParameter`.
    pub items: Vec<u32>,
}

/// The parser.
pub struct Parser<'a> {
    /// The source text.
    pub src: &'a [u32],
    /// Annex B.1.1 applies (scripts).
    pub html: bool,
    /// The goal symbol is `Module`.
    pub module: bool,
    /// The current token.
    pub t: Tok,
    /// The end of the token before the current one.
    pub prev_end: usize,
    /// The arena (garbage included: [`crate::check`] sees the compacted one).
    pub nodes: Vec<Node>,
    /// The tokens consumed so far.
    pub rec: Vec<crate::arena_d::DTok>,
    /// Where a `;` was inserted (before the token with this index), and which.
    pub gap_events: Vec<(usize, crate::spec::Ins)>,
    /// `spec::lvl` of each node.
    pub lv: Vec<i32>,
    /// The nesting of recursive calls that each sit inside a node.
    pub depth: usize,
    /// Nodes that are only valid as a cover grammar (§13.2.5.1's
    /// `CoverInitializedName`, `()`, `(a,)`, `(...a)`): an error if reachable.
    pub bad: HashSet<u32>,
    /// The covers of the parenthesized expressions.
    pub covers: HashMap<u32, Cover>,
    /// `CallExpression`s that are `async (...)` with no line terminator before
    /// the `(`: candidates for the head of an async arrow function.
    pub async_calls: HashSet<u32>,
    /// Array and object literals in which a `,` follows a `...` element.
    pub rest_comma: HashSet<u32>,
}

impl<'a> Parser<'a> {
    /// A parser at the start of `src`.
    pub fn new(src: &'a [u32], module: bool) -> R<Parser<'a>> {
        let html = !module;
        let t = lex(src, 0, Goal::InputElementHashbangOrRegExp, html).ok_or(ParseError::Syntax)?;
        Ok(Parser {
            src,
            html,
            module,
            t,
            prev_end: 0,
            nodes: Vec::new(),
            rec: Vec::new(),
            gap_events: Vec::new(),
            lv: Vec::new(),
            depth: 0,
            bad: HashSet::new(),
            covers: HashMap::new(),
            async_calls: HashSet::new(),
            rest_comma: HashSet::new(),
        })
    }

    // ----- tokens -----------------------------------------------------

    /// Moves to the next token, read with `InputElementDiv`.
    pub fn bump(&mut self) -> R<()> {
        if !self.t.eof {
            self.rec.push(crate::token::dtok_of(&self.t));
        }
        self.prev_end = self.t.end;
        let t = lex(self.src, self.t.end, Goal::InputElementDiv, self.html)
            .ok_or(ParseError::Syntax)?;
        self.t = t;
        Ok(())
    }

    /// The token after the current one (read with `InputElementDiv`).
    pub fn peek(&self) -> R<Tok> {
        lex(self.src, self.t.end, Goal::InputElementDiv, self.html).ok_or(ParseError::Syntax)
    }

    /// The token after `t`.
    pub fn peek_after(&self, t: &Tok) -> R<Tok> {
        lex(self.src, t.end, Goal::InputElementDiv, self.html).ok_or(ParseError::Syntax)
    }

    /// The current `/` or `/=` is the start of a regular expression literal:
    /// read it again with `InputElementRegExp`.
    pub fn relex_regexp(&mut self) -> R<()> {
        let nl = self.t.nl;
        let mut t = lex(self.src, self.t.start, Goal::InputElementRegExp, self.html)
            .ok_or(ParseError::Syntax)?;
        t.nl = nl;
        if t.kind != ElementKind::RegularExpressionLiteral {
            return syn();
        }
        self.t = t;
        Ok(())
    }

    /// The current `}` ends a template substitution: read it again with
    /// `InputElementTemplateTail`.
    pub fn relex_template_tail(&mut self) -> R<()> {
        let nl = self.t.nl;
        let mut t = lex(
            self.src,
            self.t.start,
            Goal::InputElementTemplateTail,
            self.html,
        )
        .ok_or(ParseError::Syntax)?;
        t.nl = nl;
        self.t = t;
        Ok(())
    }

    /// The current token is the punctuator `p`; consumes it.
    pub fn eat_p(&mut self, p: &str) -> R<bool> {
        if self.t.is_p(p) {
            self.bump()?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Consumes the punctuator `p`, or a syntax error.
    pub fn expect_p(&mut self, p: &str) -> R<()> {
        if self.t.is_p(p) { self.bump() } else { syn() }
    }

    /// Consumes the word `w`, or a syntax error.
    pub fn expect_w(&mut self, w: &str) -> R<()> {
        if self.t.is_w(w) { self.bump() } else { syn() }
    }

    /// §12.10: the end of a statement that ends with `;`: a real `;`, or one
    /// inserted before a `}`, the end of the input or a token after a line
    /// terminator. Returns the end of the statement (the `;` token's end, or
    /// the end of the last token when inserted).
    pub fn semi(&mut self) -> R<usize> {
        if self.t.is_p(";") {
            let e = self.t.end;
            self.bump()?;
            Ok(e)
        } else if self.t.eof || self.t.nl || self.t.is_p("}") {
            self.gap_events
                .push((self.rec.len(), crate::spec::Ins::Semicolon));
            Ok(self.prev_end)
        } else {
            syn()
        }
    }

    /// Runs `f` one level deeper; [`ParseError::TooDeep`] past [`MAX_DEPTH`].
    pub fn nest<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        // Each nested call sits inside a node, but one node can have two (an
        // assignment expression whose right side is a function), so the counter
        // may be a few times the height: it bounds the stack, and [`crate::check`]
        // applies the exact limit, to the height.
        if self.depth >= MAX_DEPTH.saturating_mul(4) {
            return Err(ParseError::TooDeep);
        }
        self.depth = self.depth.saturating_add(1);
        let r = f(self);
        self.depth = self.depth.saturating_sub(1);
        r
    }

    // ----- nodes ------------------------------------------------------

    /// Adds a node; its id.
    pub fn mk(
        &mut self,
        kind: NodeKind,
        op: Op,
        flag: bool,
        start: usize,
        end: usize,
        children: Vec<u32>,
    ) -> u32 {
        let id = u32::try_from(self.nodes.len()).unwrap_or(u32::MAX);
        let first = children.first().copied();
        self.nodes.push(Node {
            kind,
            op,
            flag,
            start,
            end,
            children,
        });
        // A chain of `MemberExpression` and `TaggedTemplate` nodes is 17 when
        // its base is, 15 otherwise (remembered, so that a long chain is not
        // walked at every link).
        let l = match kind {
            NodeKind::MemberExpression | NodeKind::TaggedTemplate => {
                if first.is_some_and(|c| c < id && self.lvl(c) == 17) {
                    17
                } else {
                    15
                }
            }
            k => self.lvl_kind(id, k),
        };
        self.lv.push(l);
        id
    }

    /// A node with no children.
    pub fn leaf(&mut self, kind: NodeKind, start: usize, end: usize) -> u32 {
        self.mk(kind, Op::None, false, start, end, Vec::new())
    }

    /// An absent optional symbol, at the end of the previous token.
    pub fn absent(&mut self) -> u32 {
        let p = self.prev_end;
        self.leaf(NodeKind::Absent, p, p)
    }

    /// The node `id`.
    pub fn node(&self, id: u32) -> Option<&Node> {
        self.nodes.get(id as usize)
    }

    /// The kind of `id`; `Script` (a kind no position accepts) if there is none.
    pub fn kind(&self, id: u32) -> NodeKind {
        self.node(id).map_or(NodeKind::Script, |n| n.kind)
    }

    /// The op of `id`.
    pub fn op(&self, id: u32) -> Op {
        self.node(id).map_or(Op::None, |n| n.op)
    }

    /// The start of `id`.
    pub fn st(&self, id: u32) -> usize {
        self.node(id).map_or(usize::MAX, |n| n.start)
    }

    /// The end of `id`.
    pub fn en(&self, id: u32) -> usize {
        self.node(id).map_or(usize::MAX, |n| n.end)
    }

    /// Child `k` of `id`, `u32::MAX` (which no check accepts) if none.
    pub fn child(&self, id: u32, k: usize) -> u32 {
        self.node(id)
            .and_then(|n| n.children.get(k).copied())
            .unwrap_or(u32::MAX)
    }

    /// The number of children of `id`.
    pub fn nchildren(&self, id: u32) -> usize {
        self.node(id).map_or(0, |n| n.children.len())
    }

    /// The binding strength of expression `id` (`spec::lvl`).
    pub fn lvl(&self, id: u32) -> i32 {
        self.lv.get(id as usize).copied().unwrap_or(-100)
    }

    /// `lvl` of a node of kind `k` that is not a member chain's link.
    fn lvl_kind(&self, id: u32, k: NodeKind) -> i32 {
        use NodeKind as K;
        match k {
            K::Expression => -1,
            K::ConditionalExpression
            | K::AssignmentExpression
            | K::ArrowFunction
            | K::AsyncArrowFunction
            | K::YieldExpression
            | K::CoalesceExpression => 0,
            K::LogicalORExpression => 1,
            K::LogicalANDExpression => 2,
            K::BitwiseORExpression => 3,
            K::BitwiseXORExpression => 4,
            K::BitwiseANDExpression => 5,
            K::EqualityExpression => 6,
            K::RelationalExpression => 7,
            K::ShiftExpression => 8,
            K::AdditiveExpression => 9,
            K::MultiplicativeExpression => 10,
            K::ExponentiationExpression => 11,
            K::UnaryExpression | K::AwaitExpression => 12,
            K::UpdateExpression => 13,
            K::OptionalExpression => 14,
            K::CallExpression | K::SuperCall | K::ImportCall => 15,
            K::NewExpression => {
                if self.nchildren(id) == 2 && self.kind(self.child(id, 1)) == K::Absent {
                    16
                } else {
                    17
                }
            }
            K::IdentifierReference
            | K::ThisExpression
            | K::NullLiteral
            | K::BooleanLiteral
            | K::NumericLiteral
            | K::StringLiteral
            | K::RegularExpressionLiteral
            | K::TemplateLiteral
            | K::ArrayLiteral
            | K::ObjectLiteral
            | K::ParenthesizedExpression
            | K::FunctionExpression
            | K::GeneratorExpression
            | K::AsyncFunctionExpression
            | K::AsyncGeneratorExpression
            | K::ClassExpression
            | K::SuperProperty
            | K::ImportMeta
            | K::NewTarget => 17,
            _ => -100,
        }
    }

    // ----- identifiers ------------------------------------------------

    /// The resolved name `n` is an `Identifier` in context `cx` (§13.1): not a
    /// `ReservedWord`, except `yield` when `[~Yield]` and `await` when `[~Await]`.
    pub fn name_ok(n: &[u32], cx: Cx) -> bool {
        if name_is(n, "yield") {
            !cx.y
        } else if name_is(n, "await") {
            !cx.a
        } else {
            !name_is_reserved(n)
        }
    }

    /// The current token can be an `Identifier` in `cx`.
    pub fn ident_ok(&self, cx: Cx) -> bool {
        self.t.is_name() && Self::name_ok(&self.t.name, cx)
    }

    /// Parses an `Identifier` as a node of `kind` (`IdentifierReference`,
    /// `BindingIdentifier` or `LabelIdentifier`).
    pub fn parse_ident(&mut self, kind: NodeKind, cx: Cx) -> R<u32> {
        if !self.ident_ok(cx) {
            return syn();
        }
        let (s, e) = (self.t.start, self.t.end);
        self.bump()?;
        Ok(self.leaf(kind, s, e))
    }

    /// Whether `id` has any cover-only node reachable (checked at the end).
    pub fn reachable_bad(&self, root: u32) -> bool {
        if self.bad.is_empty() {
            return false;
        }
        let mut stack = vec![root];
        let mut seen: HashSet<u32> = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            if self.bad.contains(&id) {
                return true;
            }
            if let Some(n) = self.node(id) {
                stack.extend(n.children.iter().copied());
            }
        }
        false
    }
}
