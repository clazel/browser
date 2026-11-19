//! The parser of CSS Syntax Level 3 (§5 "Parsing", with the entry points of
//! §5.3.1 and the algorithms of §5.4), transcribed from the standard alone; see
//! the header of [`super`] for the text, the tokenizer and the modelling choices
//! that this file shares.
//!
//! ## Modelling choices
//!
//! - The standard's token stream is a list of tokens, an index and a stack of
//!   marks. Here it is the list ([`Lex`]es, which the tokenizer made) and the
//!   index `p`, passed and returned by every algorithm; the next token is the
//!   token at `p`, `<EOF-token>` at and past the end ([`i_next`]), and a token
//!   stream is "empty" when `p` is at or past the end ([`i_empty`]). A mark is the
//!   index at the time of "mark": "discard a mark" forgets it, "restore a mark"
//!   goes back to it, and nothing else touches the stack, so each is a `let`.
//! - Every algorithm returns what the standard says it returns and the index
//!   after what it consumed. "Return nothing" is `None` (or [`IQRes::Nothing`]).
//!   An algorithm that "processes" a stream is a recursion over the index; the
//!   standard's "Repeat until one of the actions returns something" is the
//!   recursion that the other branches end.
//! - The input of an entry point is a string of code points ("normalize into a
//!   token stream", step 3: filter code points, tokenize), as `Seq<int>`; the
//!   other kinds of input ("a list of CSS tokens and/or component values") and
//!   input byte streams ("decode bytes") are not modelled, and nor is the
//!   "parse something according to a CSS grammar" hook, which hands the
//!   unspecified result of "parse a list of component values" to a grammar.
//!   The An+B microsyntax (§6) is not transcribed.
//! - "If |rule| is valid in the current context" and "If |decl| is valid in
//!   the current context": the standard leaves what is valid to the specs of
//!   each context. Every rule and declaration is valid here ([`i_valid_rule`],
//!   [`i_valid_decl`]), so no "invalid rule error" is ever returned, though the
//!   algorithms that handle one are written as the standard writes them.
//! - The "original text" of a declaration is the segment of the string that
//!   was tokenized (after "filter code points") from the first token's start to
//!   the last token's end ([`i_text_of`]), given the token indexes of the first
//!   and the one after the last. The standard says "the original source text
//!   string"; this takes it to be the string the tokenizer read, which is also
//!   the only one the tokens have positions in.
//! - A "custom property name string" is a string that starts with "--" (the
//!   standard uses the term and the qualified-rule step uses that test).
//! - "Consume a block's contents" at an end token, as written, never appends
//!   the declarations it still holds (`docs/ERRATA.md`, "CSS Syntax §5.5.5").
//!   This file specifies the evident intent: it appends them, as the at-rule
//!   and rule branches do before they go on.
//! - Results are trees: component values, declarations and rules are `ghost`
//!   algebraic types, with lists as `Seq`s of them.

use super::*;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §5.2 CSS parsing results

/// A component value: "one of the preserved tokens, a function, or a simple
/// block".
pub ghost enum ICv {
    /// A preserved token.
    Token(ITok),
    /// A function: its name and a list of component values.
    Function(Seq<int>, Seq<ICv>),
    /// A simple block: its associated token (`<{-token>`, `<[-token>` or
    /// `<(-token>`) and a list of component values.
    Block(ITok, Seq<ICv>),
}

/// A declaration: "a name, a value consisting of a list of component values, an
/// important flag" and an optional original text.
pub ghost struct IDecl {
    /// Its name.
    pub name: Seq<int>,
    /// Its value.
    pub value: Seq<ICv>,
    /// The important flag.
    pub important: bool,
    /// The original text, when captured.
    pub original_text: Option<Seq<int>>,
}

/// What "consume a block's contents" lists: "rules or lists of declarations".
pub ghost enum IItem {
    /// A rule.
    Rule(IRule),
    /// A list of declarations.
    Decls(Seq<IDecl>),
}

/// A rule: an at-rule, a qualified rule, or a nested declarations rule.
pub ghost enum IRule {
    /// An at-rule: name, prelude and, for a block at-rule, what "consume a
    /// block" returned as its child rules.
    AtRule {
        /// Its name.
        name: Seq<int>,
        /// Its prelude.
        prelude: Seq<ICv>,
        /// The child rules, `None` for a statement at-rule.
        block: Option<Seq<IItem>>,
    },
    /// A qualified rule: prelude, declarations and child rules.
    QualifiedRule {
        /// Its prelude.
        prelude: Seq<ICv>,
        /// Its declarations.
        decls: Seq<IDecl>,
        /// Its child rules.
        children: Seq<IRule>,
    },
    /// A nested declarations rule, "containing the list as its declarations".
    NestedDeclarations {
        /// Its declarations.
        decls: Seq<IDecl>,
    },
}

/// What "consume a qualified rule" can return.
pub ghost enum IQRes {
    /// "Return nothing."
    Nothing,
    /// An "invalid rule error".
    InvalidRule,
    /// A rule.
    Rule(IRule),
}

/// What an entry point returns: a syntax error, or the value.
pub ghost enum IParsed<T> {
    /// "Return a syntax error."
    SyntaxError,
    /// The value.
    Value(T),
}

/// "If |rule| is valid in the current context": always (see the header).
pub open spec fn i_valid_rule(r: IRule) -> bool { true }

/// "If |decl| is valid in the current context": always (see the header).
pub open spec fn i_valid_decl(d: IDecl) -> bool { true }

// ---------------------------------------------------------------------
// §5.3 Token streams

/// How many tokens remain from index `p`: the measure of the recursions.
pub open spec fn i_remaining(toks: Seq<Lex>, p: nat) -> nat {
    if toks.len() > p { (toks.len() - p) as nat } else { 0 }
}

/// "next token": the token at the index, an `<EOF-token>` past the end.
pub open spec fn i_next(toks: Seq<Lex>, p: nat) -> ITok {
    if p < toks.len() { toks[p as int].tok } else { ITok::Eof }
}

/// "empty": the next token is an `<EOF-token>`.
pub open spec fn i_empty(toks: Seq<Lex>, p: nat) -> bool { p >= toks.len() }

/// "discard a token": "If the token stream is not empty, increment index."
pub open spec fn i_discard(toks: Seq<Lex>, p: nat) -> nat {
    if i_empty(toks, p) { p } else { p + 1 }
}

/// "discard whitespace": "While the next token is a `<whitespace-token>`,
/// discard a token."
pub open spec fn i_discard_whitespace(toks: Seq<Lex>, p: nat) -> nat
    decreases i_remaining(toks, p),
{
    if i_next(toks, p) == ITok::Whitespace { i_discard_whitespace(toks, p + 1) } else { p }
}

/// The ending token of a simple block: "the mirror variant of the next token".
pub open spec fn i_mirror(t: ITok) -> ITok {
    match t {
        ITok::OpenCurly => ITok::CloseCurly,
        ITok::OpenSquare => ITok::CloseSquare,
        _ => ITok::CloseParen,
    }
}

/// The component value that is a whitespace token.
pub open spec fn i_is_ws(v: ICv) -> bool { v == ICv::Token(ITok::Whitespace) }

/// "While the last item in the list is a `<whitespace-token>`, remove that
/// token."
pub open spec fn i_strip_trailing_ws(v: Seq<ICv>) -> Seq<ICv>
    decreases v.len(),
{
    if v.len() > 0 && i_is_ws(v[v.len() - 1]) {
        i_strip_trailing_ws(v.subrange(0, v.len() - 1))
    } else {
        v
    }
}

// ---------------------------------------------------------------------
// §5.4 Parser algorithms: component values

/// §5.4.10 "consume a component value" from `p`: the value and the index after.
///
/// "Consume a simple block" and "consume a function" are called with the index
/// after the token they start with (their first step is to discard it), which
/// shows that the call goes forward.
pub open spec fn i_consume_component_value(toks: Seq<Lex>, p: nat) -> (ICv, nat)
    decreases i_remaining(toks, p), 1nat,
{
    let t = i_next(toks, p);
    if t == ITok::OpenCurly || t == ITok::OpenSquare || t == ITok::OpenParen {
        i_consume_simple_block(toks, p + 1, t)
    } else if t is Function {
        i_consume_function(toks, p + 1, t->Function_0)
    } else {
        // "consume a token and return the result"
        (ICv::Token(t), p + 1)
    }
}

/// §5.4.11 "consume a simple block", whose opening token `open` has been
/// discarded: `p` is the index after it.
pub open spec fn i_consume_simple_block(toks: Seq<Lex>, p: nat, open: ITok) -> (ICv, nat)
    decreases i_remaining(toks, p), 3nat,
{
    // "Discard a token", then "process".
    let (value, q) = i_simple_block_loop(toks, p, i_mirror(open), seq![]);
    (ICv::Block(open, value), q)
}

/// The "process" of §5.4.11: `p` is the index, `ending` the ending token.
pub open spec fn i_simple_block_loop(toks: Seq<Lex>, p: nat, ending: ITok, value: Seq<ICv>) -> (Seq<ICv>, nat)
    decreases i_remaining(toks, p), 2nat,
{
    let t = i_next(toks, p);
    if t == ITok::Eof || t == ending {
        (value, i_discard(toks, p))
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        i_simple_block_loop(toks, fwd(p, q), ending, value + seq![v])
    }
}

/// §5.4.12 "consume a function", whose function token, with value `name`, has
/// been consumed: `p` is the index after it.
pub open spec fn i_consume_function(toks: Seq<Lex>, p: nat, name: Seq<int>) -> (ICv, nat)
    decreases i_remaining(toks, p), 3nat,
{
    let (value, q) = i_function_loop(toks, p, seq![]);
    (ICv::Function(name, value), q)
}

/// The "process" of §5.4.12.
pub open spec fn i_function_loop(toks: Seq<Lex>, p: nat, value: Seq<ICv>) -> (Seq<ICv>, nat)
    decreases i_remaining(toks, p), 2nat,
{
    let t = i_next(toks, p);
    if t == ITok::Eof || t == ITok::CloseParen {
        (value, i_discard(toks, p))
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        i_function_loop(toks, fwd(p, q), value + seq![v])
    }
}

/// §5.4.9 "consume a list of component values" from `p`, given an optional
/// |stop token| and |nested|, and the values so far.
pub open spec fn i_consume_list_of_component_values(
    toks: Seq<Lex>,
    p: nat,
    stop: Option<ITok>,
    nested: bool,
    values: Seq<ICv>,
) -> (Seq<ICv>, nat)
    decreases i_remaining(toks, p),
{
    let t = i_next(toks, p);
    if t == ITok::Eof || (stop is Some && t == stop->Some_0) {
        (values, p)
    } else if t == ITok::CloseCurly {
        if nested {
            (values, p)
        } else {
            // "this is a parse error. Consume a token and append the result".
            i_consume_list_of_component_values(toks, p + 1, stop, nested, values + seq![ICv::Token(t)])
        }
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        i_consume_list_of_component_values(toks, fwd(p, q), stop, nested, values + seq![v])
    }
}

/// "Consume a component value" |k| times from `p`: the index after them.
pub open spec fn i_skip_component_values(toks: Seq<Lex>, p: nat, k: nat) -> nat
    decreases i_remaining(toks, p), 4nat, k,
{
    if k == 0 {
        p
    } else {
        let (_v, q) = i_consume_component_value(toks, p);
        i_skip_component_values(toks, fwd(p, q), (k - 1) as nat)
    }
}

/// "Consume the remnants of a bad declaration" from `p`, given |nested|: the
/// index after what it consumed.
pub open spec fn i_consume_bad_declaration_remnants(toks: Seq<Lex>, p: nat, nested: bool) -> nat
    decreases i_remaining(toks, p),
{
    let t = i_next(toks, p);
    if t == ITok::Eof || t == ITok::Semicolon {
        i_discard(toks, p)
    } else if t == ITok::CloseCurly {
        if nested { p } else { i_consume_bad_declaration_remnants(toks, p + 1, nested) }
    } else {
        let (_v, q) = i_consume_component_value(toks, p);
        i_consume_bad_declaration_remnants(toks, fwd(p, q), nested)
    }
}

// ---------------------------------------------------------------------
// §5.4.7 Consume a declaration

/// "A string that starts with two U+002D HYPHEN-MINUS": a custom property
/// name string.
pub open spec fn i_custom_property_name(name: Seq<int>) -> bool {
    name.len() >= 2 && name[0] == 0x2D && name[1] == 0x2D
}

/// The segment of the source `src` that the tokens `toks[a..b)` were consumed
/// from: from the start of the first to the end of the last; empty for no
/// tokens.
pub open spec fn i_text_of(toks: Seq<Lex>, src: Seq<int>, a: nat, b: nat) -> Seq<int> {
    if a >= b || b > toks.len() {
        seq![]
    } else {
        src.subrange(toks[a as int].start as int, toks[(b - 1) as int].end as int)
    }
}

/// Whether a component value is a `{}-block`.
pub open spec fn i_is_curly_block(v: ICv) -> bool {
    match v {
        ICv::Block(t, _) => t == ITok::OpenCurly,
        _ => false,
    }
}

/// "|decl|'s value contains a top-level simple block with an associated token
/// of `<{-token>`, and also contains any other non-`<whitespace-token>` value."
pub open spec fn i_curly_block_with_others(v: Seq<ICv>) -> bool {
    exists|i: int, j: int|
        0 <= i < v.len() && 0 <= j < v.len() && i != j && i_is_curly_block(v[i]) && !i_is_ws(v[j])
}

/// §5.4.13 "consume the value of a unicode-range descriptor" from a string:
/// "Let |tokens| be the result of tokenizing |input string| with |unicode
/// ranges allowed| set to true. Consume a list of component values from
/// |tokens|, and return the result."
pub open spec fn i_consume_unicode_range_value(text: Seq<int>) -> Seq<ICv> {
    i_consume_list_of_component_values(i_tokenize(text, true), 0, None, false, seq![]).0
}

/// "If the last two non-`<whitespace-token>`s in |decl|'s value are a
/// `<delim-token>` with the value "!" followed by an `<ident-token>` with a
/// value that is an ASCII case-insensitive match for "important", remove them
/// from |decl|'s value and set |decl|'s important flag." Returns the value
/// and the flag; `value` is not stripped.
pub open spec fn i_take_important(v: Seq<ICv>) -> (Seq<ICv>, bool) {
    // Index of the last non-whitespace item + 1, and of the one before it.
    let ia = i_strip_trailing_ws(v).len();
    let a = i_strip_trailing_ws(v);
    let imp = if ia > 0 { (ia - 1) as nat } else { 0 };
    let ib = if ia > 0 { i_strip_trailing_ws(a.subrange(0, imp as int)).len() } else { 0 };
    let bang = if ib > 0 { (ib - 1) as nat } else { 0 };
    let is_important = ia > 0 && match a[imp as int] {
        ICv::Token(ITok::Ident(x)) => i_ci_match(x, seq![0x69 as int, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61, 0x6E, 0x74]),
        _ => false,
    };
    if is_important && ib > 0 && v[bang as int] == ICv::Token(ITok::Delim(0x21)) {
        (v.subrange(0, bang as int) + v.subrange(ib as int, imp as int) + v.subrange(ia as int, v.len() as int), true)
    } else {
        (v, false)
    }
}

/// §5.4.7 "consume a declaration" from `p`, given |nested|, over the tokens
/// `toks` which were consumed from `src`: the declaration, if "anything was
/// returned", and the index after what it consumed.
pub open spec fn i_consume_declaration(toks: Seq<Lex>, src: Seq<int>, p: nat, nested: bool) -> (Option<IDecl>, nat) {
    // 1. "If the next token is an `<ident-token>`, consume a token and set |decl|'s name":
    match i_next(toks, p) {
        ITok::Ident(name) => {
            // 2. "Discard whitespace."
            let q = i_discard_whitespace(toks, p + 1);
            // 3. "If the next token is a `<colon-token>`, discard a token."
            if i_next(toks, q) == ITok::Colon {
                // 4. "Discard whitespace."
                let vs = i_discard_whitespace(toks, q + 1);
                // 5. "Consume a list of component values ... with `<semicolon-token>` as the stop token".
                let (listed, ve) = i_consume_list_of_component_values(toks, vs, Some(ITok::Semicolon), nested, seq![]);
                // 6. "important".
                let (taken, important) = i_take_important(listed);
                // 7. "While the last item in |decl|'s value is a `<whitespace-token>`, remove that token."
                let value = i_strip_trailing_ws(taken);
                // 8.
                if i_custom_property_name(name) {
                    // "set |decl|'s original text to the segment of the original source text
                    // string corresponding to the tokens of |decl|'s value".
                    let end = i_skip_component_values(toks, vs, value.len());
                    let decl = IDecl { name, value, important, original_text: Some(i_text_of(toks, src, vs, end)) };
                    (if i_valid_decl(decl) { Some(decl) } else { None }, ve)
                } else if i_curly_block_with_others(value) {
                    (None, ve)
                } else {
                    let value2 = if i_ci_match(name, seq![
                        0x75 as int, 0x6E, 0x69, 0x63, 0x6F, 0x64, 0x65, 0x2D, 0x72, 0x61, 0x6E, 0x67, 0x65,
                    ]) {
                        // "consume the value of a unicode-range descriptor from the segment of
                        // the original source text string corresponding to the tokens returned
                        // by the consume a list of component values call".
                        i_consume_unicode_range_value(i_text_of(toks, src, vs, ve))
                    } else {
                        value
                    };
                    let decl = IDecl { name, value: value2, important, original_text: None };
                    // 9.
                    (if i_valid_decl(decl) { Some(decl) } else { None }, ve)
                }
            } else {
                (None, i_consume_bad_declaration_remnants(toks, q, nested))
            }
        },
        _ => (None, i_consume_bad_declaration_remnants(toks, p, nested)),
    }
}

// ---------------------------------------------------------------------
// §5.4.2 to §5.4.6 Rules

/// The list of child rules of a qualified rule: "replace [the lists of
/// declarations] with nested declarations rules containing the list".
pub open spec fn i_child_rules(items: Seq<IItem>) -> Seq<IRule>
    decreases items.len(),
{
    if items.len() == 0 {
        seq![]
    } else {
        let rest = i_child_rules(items.subrange(1, items.len() as int));
        match items[0] {
            IItem::Rule(r) => seq![r] + rest,
            IItem::Decls(ds) => seq![IRule::NestedDeclarations { decls: ds }] + rest,
        }
    }
}

/// "the first two non-`<whitespace-token>` values of |rule|'s prelude are an
/// `<ident-token>` whose value starts with "--" followed by a
/// `<colon-token>`".
pub open spec fn i_prelude_is_custom_property(prelude: Seq<ICv>) -> bool {
    let a = i_first_non_ws(prelude, 0);
    match a {
        Some(i) => match prelude[i as int] {
            ICv::Token(ITok::Ident(name)) => {
                i_custom_property_name(name) && match i_first_non_ws(prelude, i + 1) {
                    Some(j) => prelude[j as int] == ICv::Token(ITok::Colon),
                    None => false,
                }
            },
            _ => false,
        },
        None => false,
    }
}

/// The index, from `k`, of the first value that is not a `<whitespace-token>`.
pub open spec fn i_first_non_ws(v: Seq<ICv>, k: nat) -> Option<nat>
    decreases v.len() - k,
{
    if k >= v.len() {
        None
    } else if i_is_ws(v[k as int]) {
        i_first_non_ws(v, k + 1)
    } else {
        Some(k)
    }
}

/// §5.4.5 "consume a block" from `p`, the index of its `<{-token>`: "Discard a
/// token. Consume a block's contents ... Discard a token. Return |rules|."
pub open spec fn i_consume_block(toks: Seq<Lex>, src: Seq<int>, p: nat) -> (Seq<IItem>, nat) {
    i_consume_block_rest(toks, src, p + 1)
}

/// The steps of "consume a block" after the first: `p` is the index after the
/// `<{-token>`. The callers inside the recursion call this, which shows that the
/// call goes forward.
pub open spec fn i_consume_block_rest(toks: Seq<Lex>, src: Seq<int>, p: nat) -> (Seq<IItem>, nat)
    decreases i_remaining(toks, p), 7nat,
{
    let (rules, q) = i_consume_block_contents(toks, src, p, seq![], seq![]);
    (rules, i_discard(toks, q))
}

/// §5.4.6 "consume a block's contents" from `p`, with |rules| and |decls| so far.
pub open spec fn i_consume_block_contents(
    toks: Seq<Lex>,
    src: Seq<int>,
    p: nat,
    rules: Seq<IItem>,
    decls: Seq<IDecl>,
) -> (Seq<IItem>, nat)
    decreases i_remaining(toks, p), 6nat,
{
    let t = i_next(toks, p);
    if t == ITok::Whitespace || t == ITok::Semicolon {
        i_consume_block_contents(toks, src, p + 1, rules, decls)
    } else if t == ITok::Eof || t == ITok::CloseCurly {
        // The evident intent: "If |decls| is not empty, append it to |rules|".
        (if decls.len() > 0 { rules + seq![IItem::Decls(decls)] } else { rules }, p)
    } else if t is AtKeyword {
        let rules1 = if decls.len() > 0 { rules + seq![IItem::Decls(decls)] } else { rules };
        let (rule, q) = i_at_rule_process(toks, src, p + 1, true, t->AtKeyword_0, seq![]);
        let rules2 = match rule {
            Some(r) => rules1 + seq![IItem::Rule(r)],
            None => rules1,
        };
        i_consume_block_contents(toks, src, fwd(p, q), rules2, seq![])
    } else {
        // "Mark |input|. Consume a declaration from |input|, with |nested| set to true."
        let (decl, q) = i_consume_declaration(toks, src, p, true);
        match decl {
            // "append it to |decls|, and discard a mark"
            Some(d) => i_consume_block_contents(toks, src, fwd(p, q), rules, decls + seq![d]),
            // "Otherwise, restore a mark ..., then consume a qualified rule from |input|, with
            // |nested| set to true, and `<semicolon-token>` as the |stop token|."
            None => {
                let (res, q2) = i_consume_qualified_rule(toks, src, p, Some(ITok::Semicolon), true, seq![]);
                let flushed = if decls.len() > 0 { rules + seq![IItem::Decls(decls)] } else { rules };
                match res {
                    IQRes::Nothing => i_consume_block_contents(toks, src, fwd(p, q2), rules, decls),
                    IQRes::InvalidRule => i_consume_block_contents(toks, src, fwd(p, q2), flushed, seq![]),
                    IQRes::Rule(r) => i_consume_block_contents(
                        toks, src, fwd(p, q2), flushed + seq![IItem::Rule(r)], seq![],
                    ),
                }
            },
        }
    }
}

/// §5.4.3 "consume an at-rule" from `p`, the index of its `<at-keyword-token>`,
/// given |nested|.
pub open spec fn i_consume_at_rule(toks: Seq<Lex>, src: Seq<int>, p: nat, nested: bool) -> (Option<IRule>, nat) {
    let name = match i_next(toks, p) {
        ITok::AtKeyword(n) => n,
        _ => seq![],
    };
    // "Consume a token", then "process".
    i_at_rule_process(toks, src, p + 1, nested, name, seq![])
}

/// The "process" of §5.4.3, after the token that names the rule: `p` is the
/// index after it. The callers inside the recursion call this, which shows that
/// the call goes forward.
pub open spec fn i_at_rule_process(
    toks: Seq<Lex>,
    src: Seq<int>,
    p: nat,
    nested: bool,
    name: Seq<int>,
    prelude: Seq<ICv>,
) -> (Option<IRule>, nat)
    decreases i_remaining(toks, p), 0nat,
{
    let t = i_next(toks, p);
    let statement = IRule::AtRule { name, prelude, block: None };
    if t == ITok::Semicolon || t == ITok::Eof {
        (if i_valid_rule(statement) { Some(statement) } else { None }, i_discard(toks, p))
    } else if t == ITok::CloseCurly {
        if nested {
            (if i_valid_rule(statement) { Some(statement) } else { None }, p)
        } else {
            i_at_rule_process(toks, src, p + 1, nested, name, prelude + seq![ICv::Token(t)])
        }
    } else if t == ITok::OpenCurly {
        let (items, q) = i_consume_block_rest(toks, src, p + 1);
        let rule = IRule::AtRule { name, prelude, block: Some(items) };
        (if i_valid_rule(rule) { Some(rule) } else { None }, q)
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        i_at_rule_process(toks, src, fwd(p, q), nested, name, prelude + seq![v])
    }
}

/// §5.4.4 "consume a qualified rule" from `p`, given an optional |stop token|
/// and |nested|, with the prelude so far.
pub open spec fn i_consume_qualified_rule(
    toks: Seq<Lex>,
    src: Seq<int>,
    p: nat,
    stop: Option<ITok>,
    nested: bool,
    prelude: Seq<ICv>,
) -> (IQRes, nat)
    decreases i_remaining(toks, p), 5nat,
{
    let t = i_next(toks, p);
    if t == ITok::Eof || (stop is Some && t == stop->Some_0) {
        (IQRes::Nothing, p)
    } else if t == ITok::CloseCurly {
        if nested {
            (IQRes::Nothing, p)
        } else {
            i_consume_qualified_rule(toks, src, p + 1, stop, nested, prelude + seq![ICv::Token(t)])
        }
    } else if t == ITok::OpenCurly {
        if i_prelude_is_custom_property(prelude) {
            if nested {
                (IQRes::Nothing, i_consume_bad_declaration_remnants(toks, p, true))
            } else {
                let (_items, q) = i_consume_block_rest(toks, src, p + 1);
                (IQRes::Nothing, q)
            }
        } else {
            let (child_rules, q) = i_consume_block_rest(toks, src, p + 1);
            let first_is_decls = child_rules.len() > 0 && child_rules[0] is Decls;
            let decls = if first_is_decls { child_rules[0]->Decls_0 } else { seq![] };
            let rest = if first_is_decls { child_rules.subrange(1, child_rules.len() as int) } else { child_rules };
            let rule = IRule::QualifiedRule { prelude, decls, children: i_child_rules(rest) };
            (if i_valid_rule(rule) { IQRes::Rule(rule) } else { IQRes::InvalidRule }, q)
        }
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        i_consume_qualified_rule(toks, src, fwd(p, q), stop, nested, prelude + seq![v])
    }
}

/// §5.4.1 "consume a stylesheet's contents" from `p`, with the rules so far.
pub open spec fn i_consume_stylesheet_contents(toks: Seq<Lex>, src: Seq<int>, p: nat, rules: Seq<IRule>) -> Seq<IRule>
    decreases i_remaining(toks, p), 7nat,
{
    let t = i_next(toks, p);
    if t == ITok::Whitespace || t == ITok::Cdo || t == ITok::Cdc {
        i_consume_stylesheet_contents(toks, src, p + 1, rules)
    } else if t == ITok::Eof {
        rules
    } else if t is AtKeyword {
        let (rule, q) = i_at_rule_process(toks, src, p + 1, false, t->AtKeyword_0, seq![]);
        i_consume_stylesheet_contents(toks, src, fwd(p, q), match rule {
            Some(r) => rules + seq![r],
            None => rules,
        })
    } else {
        let (res, q) = i_consume_qualified_rule(toks, src, p, None, false, seq![]);
        i_consume_stylesheet_contents(toks, src, fwd(p, q), match res {
            IQRes::Rule(r) => rules + seq![r],
            _ => rules,
        })
    }
}

// ---------------------------------------------------------------------
// §5.3.1 Parser entry points, on a token stream

/// §5.3.3 "parse a stylesheet's contents" (and §5.3.2 "parse a stylesheet",
/// whose result is the rules of the stylesheet), on a stream.
pub open spec fn i_parse_stylesheet_contents_of(toks: Seq<Lex>, src: Seq<int>) -> Seq<IRule> {
    i_consume_stylesheet_contents(toks, src, 0, seq![])
}

/// The loop of §5.3.4 "parse a list of declarations", from `p`, with the
/// declarations so far.
pub open spec fn i_declarations_loop(toks: Seq<Lex>, src: Seq<int>, p: nat, decls: Seq<IDecl>) -> Seq<IDecl>
    decreases i_remaining(toks, p),
{
    if i_empty(toks, p) {
        decls
    } else {
        // "Discard whitespace from |input|."
        let q = i_discard_whitespace(toks, p);
        let t = i_next(toks, q);
        if t == ITok::Semicolon {
            i_declarations_loop(toks, src, fwd(p, q + 1), decls)
        } else if t is AtKeyword {
            let (_rule, r) = i_consume_at_rule(toks, src, q, false);
            i_declarations_loop(toks, src, fwd(p, r), decls)
        } else {
            let (decl, r) = i_consume_declaration(toks, src, q, false);
            i_declarations_loop(toks, src, fwd(p, r), match decl {
                Some(d) => decls + seq![d],
                None => decls,
            })
        }
    }
}

/// §5.3.4 "parse a list of declarations", on a stream.
pub open spec fn i_parse_list_of_declarations_of(toks: Seq<Lex>, src: Seq<int>) -> Seq<IDecl> {
    i_declarations_loop(toks, src, 0, seq![])
}

/// §5.3.5 "parse a rule", on a stream.
pub open spec fn i_parse_rule_of(toks: Seq<Lex>, src: Seq<int>) -> IParsed<IRule> {
    let p = i_discard_whitespace(toks, 0);
    if i_empty(toks, p) {
        IParsed::SyntaxError
    } else {
        let rule: Option<(IRule, nat)> = if i_next(toks, p) is AtKeyword {
            match i_consume_at_rule(toks, src, p, false) {
                (Some(r), q) => Some((r, q)),
                (None, _) => None,
            }
        } else {
            match i_consume_qualified_rule(toks, src, p, None, false, seq![]) {
                (IQRes::Rule(r), q) => Some((r, q)),
                _ => None,
            }
        };
        match rule {
            None => IParsed::SyntaxError,
            Some((r, q)) => {
                if i_empty(toks, i_discard_whitespace(toks, q)) { IParsed::Value(r) } else { IParsed::SyntaxError }
            },
        }
    }
}

/// §5.3.6 "parse a declaration", on a stream.
pub open spec fn i_parse_declaration_of(toks: Seq<Lex>, src: Seq<int>) -> IParsed<IDecl> {
    let p = i_discard_whitespace(toks, 0);
    if i_empty(toks, p) {
        IParsed::SyntaxError
    } else {
        match i_consume_declaration(toks, src, p, false) {
            (Some(d), q) => {
                if i_empty(toks, i_discard_whitespace(toks, q)) { IParsed::Value(d) } else { IParsed::SyntaxError }
            },
            (None, _) => IParsed::SyntaxError,
        }
    }
}

/// §5.3.7 "parse a component value", on a stream.
pub open spec fn i_parse_component_value_of(toks: Seq<Lex>) -> IParsed<ICv> {
    let p = i_discard_whitespace(toks, 0);
    if i_empty(toks, p) {
        IParsed::SyntaxError
    } else {
        let (v, q) = i_consume_component_value(toks, p);
        if i_empty(toks, i_discard_whitespace(toks, q)) { IParsed::Value(v) } else { IParsed::SyntaxError }
    }
}

/// §5.3.8 "parse a list of component values", on a stream.
pub open spec fn i_parse_list_of_component_values_of(toks: Seq<Lex>) -> Seq<ICv> {
    i_consume_list_of_component_values(toks, 0, None, false, seq![]).0
}

/// The loop of §5.3.9 "parse a comma-separated list of component values".
pub open spec fn i_comma_groups_loop(toks: Seq<Lex>, p: nat, groups: Seq<Seq<ICv>>) -> Seq<Seq<ICv>>
    decreases i_remaining(toks, p),
{
    if i_empty(toks, p) {
        groups
    } else {
        let (group, q) = i_consume_list_of_component_values(toks, p, Some(ITok::Comma), false, seq![]);
        i_comma_groups_loop(toks, fwd(p, i_discard(toks, q)), groups + seq![group])
    }
}

/// §5.3.9 "parse a comma-separated list of component values", on a stream.
pub open spec fn i_parse_comma_separated_list_of_component_values_of(toks: Seq<Lex>) -> Seq<Seq<ICv>> {
    i_comma_groups_loop(toks, 0, seq![])
}

// ---------------------------------------------------------------------
// §5.3.1 Parser entry points, on a string

/// §5.3.1 "normalize into a token stream", step 3: "filter code points from
/// |input|, tokenize the result". The tokens and the string they were
/// consumed from.
pub open spec fn i_normalize(input: Seq<int>) -> (Seq<Lex>, Seq<int>) {
    let s = i_filter(input);
    (i_tokenize(s, false), s)
}

/// "parse a stylesheet" and "parse a stylesheet's contents" of a string.
pub open spec fn i_parse_stylesheet_contents(input: Seq<int>) -> Seq<IRule> {
    let (toks, src) = i_normalize(input);
    i_parse_stylesheet_contents_of(toks, src)
}

/// "parse a list of declarations" of a string.
pub open spec fn i_parse_list_of_declarations(input: Seq<int>) -> Seq<IDecl> {
    let (toks, src) = i_normalize(input);
    i_parse_list_of_declarations_of(toks, src)
}

/// "parse a rule" of a string.
pub open spec fn i_parse_rule(input: Seq<int>) -> IParsed<IRule> {
    let (toks, src) = i_normalize(input);
    i_parse_rule_of(toks, src)
}

/// "parse a declaration" of a string.
pub open spec fn i_parse_declaration(input: Seq<int>) -> IParsed<IDecl> {
    let (toks, src) = i_normalize(input);
    i_parse_declaration_of(toks, src)
}

/// "parse a component value" of a string.
pub open spec fn i_parse_component_value(input: Seq<int>) -> IParsed<ICv> {
    i_parse_component_value_of(i_normalize(input).0)
}

/// "parse a list of component values" of a string.
pub open spec fn i_parse_list_of_component_values(input: Seq<int>) -> Seq<ICv> {
    i_parse_list_of_component_values_of(i_normalize(input).0)
}

/// "parse a comma-separated list of component values" of a string.
pub open spec fn i_parse_comma_separated_list_of_component_values(input: Seq<int>) -> Seq<Seq<ICv>> {
    i_parse_comma_separated_list_of_component_values_of(i_normalize(input).0)
}

} // verus!
