//! A second definition of selector parsing, matching and specificity, from the Selectors
//! Level 4 text alone (`selectors-4/Overview.bs` of `w3c/csswg-drafts` at commit
//! `5b65dd3a82c1019dca6158823e995a52d1d4204a`, <https://drafts.csswg.org/selectors-4/>),
//! sections cited as `§N` by their number in that text: §3 "Structure and Terminology",
//! §3.3 "Data Model", §3.5 "Pseudo-classes", §3.6 (invalid selectors), §4 "Logical
//! Combinations", §5 "Elemental selectors", §6 "Attribute selectors", §14 "Tree-Structural
//! pseudo-classes", §15 "Combinators", §17 "Calculating a selector's specificity", §18
//! "Grammar" and §19 "API Hooks" ("parse a selector", "match a selector against an
//! element").
//!
//! This section of the file is the definitions only. They were written before this
//! crate's `spec.rs`, `contract.rs`, `lemmas.rs`, `exec_*.rs`, `algorithm.rs`,
//! `examples.rs`, `mutations.json`, `README.md` and `tests/` were opened.
//! What was read first: this crate's `Cargo.toml` and `lib.rs`; the headers of
//! `clazel-displaylist`'s, `clazel-dom`'s and `clazel-treebuilder`'s `independent.rs`; the
//! pin line of the crate's sources; the standard at that commit; `clazel-dom`'s spec
//! types and readers (the arena); and `clazel-css`'s `parser/spec.rs` for the shape of a
//! component value, and for `a_n_plus_b`, which this file uses as it is (the An+B
//! microsyntax is CSS Syntax §6, a different standard from Selectors, and not what this
//! file is a second reading of). The commit subjects of this crate showed in `git log`,
//! and its theorem names are in `Cargo.toml`.
//!
//! ## Modelling choices
//!
//! - **What is parsed.** A selector is parsed from the list of component values CSS
//!   Syntax produces from its text ("parse a list of component values"), not from
//!   code points: [`i_parse_selector_list`] takes a `Seq<ComponentValue>`. The grammar
//!   (§18) is over tokens, so this loses nothing the grammar says.
//! - **Positions, not sub-sequences.** Each parsing function reads a range
//!   `[p, end)` of one sequence, so that a function's argument is, structurally,
//!   smaller than the sequence it is in, which is what makes the recursion
//!   terminate.
//! - **Namespaces.** What §2.1/§5.3 call "declared" prefixes and the default
//!   namespace are an [`ICtx`]: a map from prefix to namespace and an optional default.
//!   A type selector with no prefix is `ns|E` with the default namespace, or `*|E`
//!   if there is none (§5.3); a compound selector with no type selector gets
//!   `ns|*` when there is a default (§5.3), except the subject of a selector inside
//!   `:is()`, `:where()` and `:not()` unless it names a type or universal selector
//!   explicitly (§4.1, §4.2). Attribute names take no default (§6.4).
//!   An undeclared prefix is an invalid selector (§3.6).
//! - **Invalid selectors** are `None`. A selector list with an invalid selector is
//!   invalid (§3.6); `:is()` and `:where()` take a forgiving list and drop the invalid
//!   ones (§18.1); `:not()` and `:has()` do not.
//! - **What is supported.** §3.6 says a user agent must treat as invalid any
//!   pseudo-class, pseudo-element or combinator it has no support for. This file
//!   supports the selectors that depend on nothing but the tree and the element's
//!   attributes: the type and universal selectors, `#id`, `.class`, the seven attribute
//!   matchers, the four combinators, and `:is() :where() :not() :has() :root :empty
//!   :scope :defined :first-child :last-child :only-child :nth-child() :nth-last-child()
//!   :first-of-type :last-of-type :only-of-type :nth-of-type() :nth-last-of-type()`.
//!   Every other pseudo-class, every pseudo-element (including the four legacy
//!   single-colon ones) and `:has()` inside `:has()` are invalid. Pseudo-elements are
//!   not matched (§19.3 "match against a pseudo-element" is not transcribed).
//! - **Case.** Names and values are compared as the data-model paragraph says by
//!   default: identical (§3.3 "Characters and case sensitivity"). The exceptions are the
//!   ones the text states: class names and IDs in a document in quirks mode, and attribute
//!   values with the `i` flag, are ASCII case-insensitive. The host-language rules the text
//!   defers to (HTML's lower-casing of element and attribute names) are not modelled.
//!   An attribute selector's keywords (`i`, `s`) and the pseudo-class names are ASCII
//!   case-insensitive (the same paragraph).
//! - **Class and ID.** Both are the attribute with no namespace and that local name,
//!   on any element (DOM's "ID" and "class list"); an element can have several, and
//!   any of them can match (§8 "If an element has multiple ID attributes, all of them
//!   must be treated as IDs").
//! - **`:empty`** is: no child is an element, and no child is a text node with a
//!   non-white-space character. White space is the standard's own (§3.3: space, tab, line
//!   feed, carriage return, form feed).
//! - **`:scope`** is the scoping root when there is one, and the root of the tree
//!   otherwise (§12 "If there is no scoping root then :scope represents the root of the
//!   tree the element is in"), which is an element whose parent is the document node.
//!   A scoping root is an element's id.
//! - **`:defined`**: the arena records no custom element registry, so every element is
//!   defined (§5.4: "If the host language does not have this sort of distinction, all
//!   elements in it match").
//! - **Siblings and position.** "Inclusive siblings" are the element children of the
//!   element's parent, in order, and the element alone when it has no parent. Counting
//!   starts at 1. `:nth-child(An+B of S)` counts the inclusive siblings that match `S`
//!   (and the element must match `S`); without `S` every element counts (§14.1).
//!   `:first-child`, `:last-child`, `:first-of-type`, `:last-of-type` are the
//!   `:nth-` forms with `1`, as the text says; `:only-child` and `:only-of-type` are
//!   the element having no sibling, and none of its type.
//! - **Relative selectors.** `:has()` takes relative selectors, which this file writes
//!   as a complex selector with an optional leading combinator ([`IComplex::lead`]),
//!   related to an anchor element (§3.4). A relative selector matches the anchor when
//!   some element of the document matches it.
//! - **Specificity** (§17) is `(A, B, C)` of natural numbers, with no limit: the
//!   standard allows an implementation to clamp, which is a choice this file does not make.
//!   It is a function of the selector alone; the specificity "in effect for a match" of a
//!   list is that of the most specific selector in it that matches ([`i_specificity`]).
//!   A type selector counts one for `C`, a universal selector (`*`, with or without a
//!   namespace) counts nothing; the default namespace added to a compound selector adds
//!   nothing (it is a universal selector).
//! - **Arithmetic.** An+B's `A` and `B` are `int`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use clazel_css::parser::spec::{ComponentValue, Token, a_n_plus_b};
use clazel_dom::spec::Namespace;
#[cfg(verus_only)]
use clazel_dom::spec::{Attr, Document, NodeId, NodeKind, index_of, is_descendant, parent};

verus! {

// ------------------------------------------------------------------------------------
// The selectors, as this file reads them
// ------------------------------------------------------------------------------------

/// The namespace part of a type selector or attribute name (§5.3, §6.4): `ns|`, `*|`,
/// `|`.
pub ghost enum INs {
    /// `*|`: any namespace, including none.
    Any,
    /// `|`: no namespace.
    NoNs,
    /// `ns|` (or the default namespace).
    Is(Namespace),
}

/// The name part of a type selector.
pub ghost enum IName {
    /// `*`, the universal selector.
    Star,
    /// An identifier.
    Local(Seq<u32>),
}

/// §5.1 type selector and §5.2 universal selector, as `ns|name`.
pub ghost struct IType {
    /// The namespace.
    pub ns: INs,
    /// The name.
    pub name: IName,
}

/// §6.1 and §6.2: the matcher of an attribute selector.
pub ghost enum IAttrOp {
    /// `[att]`.
    Exists,
    /// `[att=val]`.
    Eq,
    /// `[att~=val]`.
    Includes,
    /// `[att|=val]`.
    Dash,
    /// `[att^=val]`.
    Prefix,
    /// `[att$=val]`.
    Suffix,
    /// `[att*=val]`.
    Substring,
}

/// §6 an attribute selector.
pub ghost struct IAttr {
    /// The namespace of the attribute's name.
    pub ns: INs,
    /// The attribute's local name.
    pub name: Seq<u32>,
    /// How the value is compared.
    pub op: IAttrOp,
    /// The value to compare with (empty for `[att]`).
    pub value: Seq<u32>,
    /// The `i` flag: ASCII case-insensitive. Without a flag, or with `s`, false.
    pub ci: bool,
}

/// §3 combinators.
pub ghost enum IComb {
    /// White space.
    Descendant,
    /// `>`.
    Child,
    /// `+`.
    Next,
    /// `~`.
    Subsequent,
}

/// §3 a simple selector other than a type selector.
pub ghost enum ISimple {
    /// `#id` (§8).
    Id(Seq<u32>),
    /// `.class` (§7).
    Class(Seq<u32>),
    /// `[...]` (§6).
    Attr(IAttr),
    /// `:is(...)` (§4.1).
    Is(Seq<IComplex>),
    /// `:where(...)` (§4.3).
    Where(Seq<IComplex>),
    /// `:not(...)` (§4.2).
    Not(Seq<IComplex>),
    /// `:has(...)` (§4.4), of relative selectors.
    Has(Seq<IComplex>),
    /// `:root` (§14 "root").
    Root,
    /// `:empty`.
    Empty,
    /// `:scope`.
    Scope,
    /// `:defined`.
    Defined,
    /// `:nth-child(An+B of S)` and `:nth-last-child(An+B of S)` (`last`), and with them
    /// `:first-child` and `:last-child`.
    NthChild {
        /// A.
        a: int,
        /// B.
        b: int,
        /// Counting from the end.
        last: bool,
        /// Whether there is an `of S`.
        has_of: bool,
        /// S.
        of: Seq<IComplex>,
    },
    /// `:nth-of-type(An+B)` and `:nth-last-of-type(An+B)` (`last`), and with them
    /// `:first-of-type` and `:last-of-type`.
    NthType {
        /// A.
        a: int,
        /// B.
        b: int,
        /// Counting from the end.
        last: bool,
    },
    /// `:only-child`.
    OnlyChild,
    /// `:only-of-type`.
    OnlyOfType,
}

/// §3 a compound selector: a type selector or none, then simple selectors.
pub ghost struct ICompound {
    /// The type or universal selector, if there is one (after the default namespace).
    pub ty: Option<IType>,
    /// The other simple selectors, in order.
    pub subs: Seq<ISimple>,
}

/// §3 a complex selector, and §3.4 a relative selector (with `lead`): compounds
/// separated by combinators. `combs[k]` is between `units[k]` and `units[k + 1]`.
pub ghost struct IComplex {
    /// The combinator before the first compound: `None` in a complex selector, always
    /// `Some` in a relative selector (white space if none was written).
    pub lead: Option<IComb>,
    /// The compound selectors, left to right.
    pub units: Seq<ICompound>,
    /// The combinators between them.
    pub combs: Seq<IComb>,
}

/// What a selector is parsed against (§2.1 declared prefixes): the namespace prefixes
/// declared, and the default namespace.
pub ghost struct ICtx {
    /// The default namespace, if one is declared.
    pub default_ns: Option<Namespace>,
    /// The prefixes declared.
    pub decls: Map<Seq<u32>, Namespace>,
}

// ------------------------------------------------------------------------------------
// Characters
// ------------------------------------------------------------------------------------

/// §3.3 "ASCII case-insensitive": the lower-case form of an ASCII letter.
pub open spec fn i_lower(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// §3.3 "ASCII case-insensitive" equality of two strings.
pub open spec fn i_ci_eq(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.len() == b.len() && forall|k: int| 0 <= k < a.len() ==> i_lower(#[trigger] a[k]) == i_lower(b[k])
}

/// §3.3 white space: space, tab, line feed, carriage return, form feed.
pub open spec fn i_white(c: u32) -> bool {
    c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x0C
}

// ------------------------------------------------------------------------------------
// §18 Grammar: reading component values
// ------------------------------------------------------------------------------------

/// A `<whitespace-token>`.
pub open spec fn i_is_ws(c: ComponentValue) -> bool {
    match c {
        ComponentValue::Token { token: Token::Whitespace } => true,
        _ => false,
    }
}

/// A `<delim-token>` of code point `d`.
pub open spec fn i_is_delim(c: ComponentValue, d: u32) -> bool {
    match c {
        ComponentValue::Token { token: Token::Delim { value } } => value == d,
        _ => false,
    }
}

/// A `<comma-token>`.
pub open spec fn i_is_comma(c: ComponentValue) -> bool {
    match c {
        ComponentValue::Token { token: Token::Comma } => true,
        _ => false,
    }
}

/// A `<colon-token>`.
pub open spec fn i_is_colon(c: ComponentValue) -> bool {
    match c {
        ComponentValue::Token { token: Token::Colon } => true,
        _ => false,
    }
}

/// An `<ident-token>`'s value.
pub open spec fn i_ident(c: ComponentValue) -> Option<Seq<u32>> {
    match c {
        ComponentValue::Token { token: Token::Ident { value } } => Some(value),
        _ => None,
    }
}

/// §18 `<combinator>` = '>' | '+' | '~'.
pub open spec fn i_comb_of(c: ComponentValue) -> Option<IComb> {
    if i_is_delim(c, 0x3E) {
        Some(IComb::Child)
    } else if i_is_delim(c, 0x2B) {
        Some(IComb::Next)
    } else if i_is_delim(c, 0x7E) {
        Some(IComb::Subsequent)
    } else {
        None
    }
}

/// How many steps a loop over `[p, end)` that moves forward at least one item per step needs
/// (one more than the items, for the step that finds the end). Termination of such loops is by
/// this count, which is more than they ever use.
pub open spec fn i_fuel(p: int, end: int) -> nat {
    if end >= p {
        (end - p + 1) as nat
    } else {
        0
    }
}

/// The first index in `[p, end)` that is not white space, or `end`.
pub open spec fn i_skip_ws(v: Seq<ComponentValue>, p: int, end: int) -> int
    decreases end - p,
{
    if p < end && i_is_ws(v[p]) {
        i_skip_ws(v, p + 1, end)
    } else {
        p
    }
}

/// The end of `[p, end)` without its trailing white space.
pub open spec fn i_trim_end(v: Seq<ComponentValue>, p: int, end: int) -> int
    decreases end - p,
{
    if p < end && i_is_ws(v[end - 1]) {
        i_trim_end(v, p, end - 1)
    } else {
        end
    }
}

/// The index of the first top-level `<comma-token>` in `[p, end)`, or `end`.
pub open spec fn i_comma(v: Seq<ComponentValue>, p: int, end: int) -> int
    decreases end - p,
{
    if p < end && !i_is_comma(v[p]) {
        i_comma(v, p + 1, end)
    } else {
        p
    }
}

/// The namespace of a prefix (§2.1): declared or not.
pub open spec fn i_prefix(cx: ICtx, prefix: Seq<u32>) -> Option<Namespace> {
    if cx.decls.dom().contains(prefix) {
        Some(cx.decls[prefix])
    } else {
        None
    }
}

/// §5.3 "E": the namespace of an unprefixed type selector. "If no default namespace has
/// been declared for selectors, this is equivalent to *|E. Otherwise it is equivalent to
/// ns|E where ns is the default namespace."
pub open spec fn i_default_ns(cx: ICtx) -> INs {
    match cx.default_ns {
        Some(n) => INs::Is(n),
        None => INs::Any,
    }
}

/// §18 `<type-selector>` = `<wq-name>` | `<ns-prefix>`? '*', at `p`. `None` is an
/// invalid selector (an undeclared prefix, or a `|` with no name after it);
/// `Some(None)` is no type selector here; `Some(Some((t, q)))` is one, ending at `q`.
pub open spec fn i_type_selector(v: Seq<ComponentValue>, p: int, end: int, cx: ICtx) -> Option<
    Option<(IType, int)>,
> {
    if p >= end {
        Some(None)
    } else if i_ident(v[p]) is Some {
        let n = i_ident(v[p]).unwrap();
        if p + 1 < end && i_is_delim(v[p + 1], 0x7C) {
            // `ns|E` or `ns|*`
            match i_prefix(cx, n) {
                None => None,
                Some(ns) => {
                    if p + 2 < end && i_ident(v[p + 2]) is Some {
                        Some(
                            Some(
                                (
                                    IType {
                                        ns: INs::Is(ns),
                                        name: IName::Local(i_ident(v[p + 2]).unwrap()),
                                    },
                                    p + 3,
                                ),
                            ),
                        )
                    } else if p + 2 < end && i_is_delim(v[p + 2], 0x2A) {
                        Some(Some((IType { ns: INs::Is(ns), name: IName::Star }, p + 3)))
                    } else {
                        None
                    }
                },
            }
        } else {
            Some(Some((IType { ns: i_default_ns(cx), name: IName::Local(n) }, p + 1)))
        }
    } else if i_is_delim(v[p], 0x2A) {
        if p + 1 < end && i_is_delim(v[p + 1], 0x7C) {
            // `*|E` or `*|*`
            if p + 2 < end && i_ident(v[p + 2]) is Some {
                Some(
                    Some(
                        (
                            IType { ns: INs::Any, name: IName::Local(i_ident(v[p + 2]).unwrap()) },
                            p + 3,
                        ),
                    ),
                )
            } else if p + 2 < end && i_is_delim(v[p + 2], 0x2A) {
                Some(Some((IType { ns: INs::Any, name: IName::Star }, p + 3)))
            } else {
                None
            }
        } else {
            Some(Some((IType { ns: i_default_ns(cx), name: IName::Star }, p + 1)))
        }
    } else if i_is_delim(v[p], 0x7C) {
        // `|E` or `|*`
        if p + 1 < end && i_ident(v[p + 1]) is Some {
            Some(
                Some(
                    (
                        IType { ns: INs::NoNs, name: IName::Local(i_ident(v[p + 1]).unwrap()) },
                        p + 2,
                    ),
                ),
            )
        } else if p + 1 < end && i_is_delim(v[p + 1], 0x2A) {
            Some(Some((IType { ns: INs::NoNs, name: IName::Star }, p + 2)))
        } else {
            None
        }
    } else {
        Some(None)
    }
}

/// The value of a `<string-token>`.
pub open spec fn i_string(c: ComponentValue) -> Option<Seq<u32>> {
    match c {
        ComponentValue::Token { token: Token::String { value } } => Some(value),
        _ => None,
    }
}

/// §18 `<attr-matcher>` = [ '~' | '|' | '^' | '$' | '*' ]? '=' at `q`: the matcher and where
/// it ends. "White space is forbidden between the components of an `<attr-matcher>`."
pub open spec fn i_attr_matcher(b: Seq<ComponentValue>, q: int) -> Option<(IAttrOp, int)> {
    if q >= b.len() {
        None
    } else if i_is_delim(b[q], 0x3D) {
        Some((IAttrOp::Eq, q + 1))
    } else if q + 1 < b.len() && i_is_delim(b[q + 1], 0x3D) {
        if i_is_delim(b[q], 0x7E) {
            Some((IAttrOp::Includes, q + 2))
        } else if i_is_delim(b[q], 0x7C) {
            Some((IAttrOp::Dash, q + 2))
        } else if i_is_delim(b[q], 0x5E) {
            Some((IAttrOp::Prefix, q + 2))
        } else if i_is_delim(b[q], 0x24) {
            Some((IAttrOp::Suffix, q + 2))
        } else if i_is_delim(b[q], 0x2A) {
            Some((IAttrOp::Substring, q + 2))
        } else {
            None
        }
    } else {
        None
    }
}

/// §18 `<wq-name>` of an attribute selector at `p` (§6.4: no default namespace applies):
/// the namespace, the local name and where it ends. `[a|=b]` is the name `a` and the
/// matcher `|=`, not the prefix `a`.
pub open spec fn i_attr_name(b: Seq<ComponentValue>, p: int, cx: ICtx) -> Option<(INs, Seq<u32>, int)> {
    if p >= b.len() {
        None
    } else if i_ident(b[p]) is Some {
        let n = i_ident(b[p]).unwrap();
        if p + 1 < b.len() && i_is_delim(b[p + 1], 0x7C) && !(p + 2 < b.len() && i_is_delim(
            b[p + 2],
            0x3D,
        )) {
            match i_prefix(cx, n) {
                None => None,
                Some(ns) => {
                    if p + 2 < b.len() && i_ident(b[p + 2]) is Some {
                        Some((INs::Is(ns), i_ident(b[p + 2]).unwrap(), p + 3))
                    } else {
                        None
                    }
                },
            }
        } else {
            Some((INs::NoNs, n, p + 1))
        }
    } else if i_is_delim(b[p], 0x2A) {
        if p + 2 < b.len() && i_is_delim(b[p + 1], 0x7C) && i_ident(b[p + 2]) is Some {
            Some((INs::Any, i_ident(b[p + 2]).unwrap(), p + 3))
        } else {
            None
        }
    } else if i_is_delim(b[p], 0x7C) {
        if p + 1 < b.len() && i_ident(b[p + 1]) is Some {
            Some((INs::NoNs, i_ident(b[p + 1]).unwrap(), p + 2))
        } else {
            None
        }
    } else {
        None
    }
}

/// §18 `<attribute-selector>`, from the component values inside the brackets:
/// `[ <wq-name> ]` or `[ <wq-name> <attr-matcher> [ <string-token> | <ident-token> ]
/// <attr-modifier>? ]`, with the `i` and `s` modifiers ASCII case-insensitive (§3.3).
/// White space is allowed inside the brackets, between these components.
pub open spec fn i_attribute_selector(b: Seq<ComponentValue>, cx: ICtx) -> Option<IAttr> {
    match i_attr_name(b, i_skip_ws(b, 0, b.len() as int), cx) {
        None => None,
        Some((ns, name, after_name)) => {
            let q = i_skip_ws(b, after_name, b.len() as int);
            if q == b.len() {
                Some(IAttr { ns, name, op: IAttrOp::Exists, value: Seq::empty(), ci: false })
            } else {
                match i_attr_matcher(b, q) {
                    None => None,
                    Some((op, after_op)) => {
                        let r = i_skip_ws(b, after_op, b.len() as int);
                        if r >= b.len() {
                            None
                        } else {
                            let value = if i_ident(b[r]) is Some {
                                i_ident(b[r])
                            } else {
                                i_string(b[r])
                            };
                            match value {
                                None => None,
                                Some(val) => {
                                    let s = i_skip_ws(b, r + 1, b.len() as int);
                                    if s == b.len() {
                                        Some(IAttr { ns, name, op, value: val, ci: false })
                                    } else {
                                        match i_ident(b[s]) {
                                            None => None,
                                            Some(m) => {
                                                if i_skip_ws(b, s + 1, b.len() as int) != b.len() {
                                                    None
                                                } else if i_ci_eq(m, seq![0x69u32]) {
                                                    Some(IAttr { ns, name, op, value: val, ci: true })
                                                } else if i_ci_eq(m, seq![0x73u32]) {
                                                    Some(IAttr { ns, name, op, value: val, ci: false })
                                                } else {
                                                    None
                                                }
                                            },
                                        }
                                    }
                                },
                            }
                        }
                    },
                }
            }
        },
    }
}

/// The first top-level `of` keyword (ASCII case-insensitive) in `[p, end)`, or `end`: where
/// `:nth-child(An+B of S)` splits.
pub open spec fn i_find_of(v: Seq<ComponentValue>, p: int, end: int) -> int
    decreases end - p,
{
    if p < end && !(i_ident(v[p]) is Some && i_ci_eq(i_ident(v[p]).unwrap(), seq![0x6Fu32, 0x66])) {
        i_find_of(v, p + 1, end)
    } else {
        p
    }
}

/// `:name` for the pseudo-classes that take no arguments, §3.5 and §14 and §5.4: `None` is a
/// pseudo-class this file has no support for (§3.6: invalid).
pub open spec fn i_pseudo_ident(name: Seq<u32>) -> Option<ISimple> {
    if i_ci_eq(name, seq![0x72u32, 0x6F, 0x6F, 0x74]) {
        Some(ISimple::Root)
    } else if i_ci_eq(name, seq![0x65u32, 0x6D, 0x70, 0x74, 0x79]) {
        Some(ISimple::Empty)
    } else if i_ci_eq(name, seq![0x73u32, 0x63, 0x6F, 0x70, 0x65]) {
        Some(ISimple::Scope)
    } else if i_ci_eq(name, seq![0x64u32, 0x65, 0x66, 0x69, 0x6E, 0x65, 0x64]) {
        Some(ISimple::Defined)
    } else if i_ci_eq(name, seq![0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        // "Same as :nth-child(1)."
        Some(ISimple::NthChild { a: 0, b: 1, last: false, has_of: false, of: Seq::empty() })
    } else if i_ci_eq(name, seq![0x6Cu32, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        // "Same as :nth-last-child(1)."
        Some(ISimple::NthChild { a: 0, b: 1, last: true, has_of: false, of: Seq::empty() })
    } else if i_ci_eq(name, seq![0x6Fu32, 0x6E, 0x6C, 0x79, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        Some(ISimple::OnlyChild)
    } else if i_ci_eq(
        name,
        seq![0x66u32, 0x69, 0x72, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        // "represents the same element as :nth-of-type(1)."
        Some(ISimple::NthType { a: 0, b: 1, last: false })
    } else if i_ci_eq(
        name,
        seq![0x6Cu32, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(ISimple::NthType { a: 0, b: 1, last: true })
    } else if i_ci_eq(
        name,
        seq![0x6Fu32, 0x6E, 0x6C, 0x79, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ) {
        Some(ISimple::OnlyOfType)
    } else {
        None
    }
}

/// §18 `<selector-list>` and the other lists, from `[p, end)` of `v`: `<complex-selector>#`,
/// `<relative-selector>#` (`rel`), and with `forgiving` §18.1 "parse as a forgiving selector
/// list": the selectors that fail are removed. `exempt` is for the lists of `:is()`,
/// `:where()` and `:not()`, whose subjects get no default namespace (§4.1, §4.2).
/// `in_has` is true inside `:has()`, where `:has()` is invalid (§4.4).
pub open spec fn i_clist(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cx: ICtx,
    forgiving: bool,
    rel: bool,
    exempt: bool,
    in_has: bool,
) -> Option<Seq<IComplex>>
    decreases v, 5nat, end - p
    via i_clist_decreases
{
    let q = i_comma(v, p, end);
    let one = i_complex(v, p, q, cx, rel, exempt, in_has);
    if q >= end {
        match one {
            Some(c) => Some(seq![c]),
            None => if forgiving {
                Some(Seq::empty())
            } else {
                None
            },
        }
    } else {
        match i_clist(v, q + 1, end, cx, forgiving, rel, exempt, in_has) {
            None => None,
            Some(rest) => match one {
                Some(c) => Some(seq![c] + rest),
                None => if forgiving {
                    Some(rest)
                } else {
                    None
                },
            },
        }
    }
}

/// §18 `<complex-selector>` (or `<relative-selector>`, with `rel`) in `[p, end)`: the
/// white space around it is not part of it, an empty selector is invalid (§3.6), and the
/// default namespace is applied last to the compounds that have no type selector (§5.3).
pub open spec fn i_complex(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cx: ICtx,
    rel: bool,
    exempt: bool,
    in_has: bool,
) -> Option<IComplex>
    decreases v, 4nat, end - p,
{
    let start = i_skip_ws(v, p, end);
    let stop = i_trim_end(v, start, end);
    if start >= stop {
        None
    } else {
        let lead_comb = i_comb_of(v[start]);
        let (lead, body) = if rel {
            match lead_comb {
                Some(c) => (Some(c), i_skip_ws(v, start + 1, stop)),
                None => (Some(IComb::Descendant), start),
            }
        } else {
            (None, start)
        };
        if !rel && lead_comb is Some {
            None
        } else {
            match i_units(v, body, stop, cx, in_has, i_fuel(body, stop)) {
                None => None,
                Some((units, combs)) => Some(
                    IComplex { lead, units: i_with_default_ns(units, cx, exempt), combs },
                ),
            }
        }
    }
}

/// §5.3: "compound selectors without type selectors in them still only match elements in
/// that default namespace", except, with `exempt`, the last (subject) compound.
pub open spec fn i_with_default_ns(units: Seq<ICompound>, cx: ICtx, exempt: bool) -> Seq<ICompound> {
    Seq::new(
        units.len(),
        |k: int|
            if units[k].ty is None && cx.default_ns is Some && !(exempt && k == units.len() - 1) {
                ICompound {
                    ty: Some(IType { ns: i_default_ns(cx), name: IName::Star }),
                    subs: units[k].subs,
                }
            } else {
                units[k]
            },
    )
}

/// §18 `<complex-selector>` = `<compound-selector>` [ `<combinator>`? `<compound-selector>` ]*
/// over `[p, end)`, which has no white space at either end: the compounds and the
/// combinators between them. "Whitespace is required between two compounds if the
/// combinator between them is omitted. (This indicates the descendant combinator.)"
pub open spec fn i_units(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cx: ICtx,
    in_has: bool,
    fuel: nat,
) -> Option<(Seq<ICompound>, Seq<IComb>)>
    decreases v, 3nat, fuel,
{
    if fuel == 0 {
        None
    } else {
    match i_compound(v, p, end, cx, in_has) {
        None => None,
        Some((c, q)) => {
            if q >= end {
                Some((seq![c], Seq::empty()))
            } else {
                let r = i_skip_ws(v, q, end);
                if r >= end {
                    Some((seq![c], Seq::empty()))
                } else if i_comb_of(v[r]) is Some {
                    let comb = i_comb_of(v[r]).unwrap();
                    let r2 = i_skip_ws(v, r + 1, end);
                    if r2 >= end {
                        None
                    } else {
                        match i_units(v, r2, end, cx, in_has, (fuel - 1) as nat) {
                            None => None,
                            Some((cs, bs)) => Some((seq![c] + cs, seq![comb] + bs)),
                        }
                    }
                } else if r > q {
                    match i_units(v, r, end, cx, in_has, (fuel - 1) as nat) {
                        None => None,
                        Some((cs, bs)) => Some((seq![c] + cs, seq![IComb::Descendant] + bs)),
                    }
                } else {
                    None
                }
            }
        },
    }
    }
}

/// §18 `<compound-selector>` = [ `<type-selector>`? `<subclass-selector>`* ]! at `p`: the
/// compound and where it ends. "White space is forbidden between any of the top-level
/// components of a `<compound-selector>`."
pub open spec fn i_compound(v: Seq<ComponentValue>, p: int, end: int, cx: ICtx, in_has: bool) -> Option<
    (ICompound, int),
>
    decreases v, 2nat, end - p,
{
    match i_type_selector(v, p, end, cx) {
        None => None,
        Some(ty) => {
            let after_type = match ty {
                Some((_, q)) => q,
                None => p,
            };
            match i_subs(v, after_type, end, cx, in_has, i_fuel(after_type, end)) {
                None => None,
                Some((subs, q)) => {
                    // The `!`: at least one of the two parts.
                    if ty is None && subs.len() == 0 {
                        None
                    } else {
                        Some(
                            (
                                ICompound {
                                    ty: match ty {
                                        Some((t, _)) => Some(t),
                                        None => None,
                                    },
                                    subs,
                                },
                                q,
                            ),
                        )
                    }
                },
            }
        },
    }
}

/// §18 `<subclass-selector>`* from `p`, up to a white space, a combinator or `end`: the
/// simple selectors and where they end.
pub open spec fn i_subs(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cx: ICtx,
    in_has: bool,
    fuel: nat,
) -> Option<(Seq<ISimple>, int)>
    decreases v, 1nat, fuel,
{
    if fuel == 0 {
        None
    } else if p >= end || i_is_ws(v[p]) || i_comb_of(v[p]) is Some {
        Some((Seq::empty(), p))
    } else {
        match i_sub_one(v, p, end, cx, in_has) {
            None => None,
            Some((s, q)) => match i_subs(v, q, end, cx, in_has, (fuel - 1) as nat) {
                None => None,
                Some((rest, r)) => Some((seq![s] + rest, r)),
            },
        }
    }
}

/// One `<subclass-selector>` at `p` (which is not white space or a combinator), and where it
/// ends.
pub open spec fn i_sub_one(v: Seq<ComponentValue>, p: int, end: int, cx: ICtx, in_has: bool) -> Option<
    (ISimple, int),
>
    decreases v, 0nat, 0int,
{
    match v[p] {
        // `<id-selector>` = `<hash-token>`, whose value "must be an identifier".
        ComponentValue::Token { token: Token::Hash { value, is_id } } => if is_id {
            Some((ISimple::Id(value), p + 1))
        } else {
            None
        },
        // `<class-selector>` = '.' `<ident-token>`
        ComponentValue::Token { token: Token::Delim { value } } => if value == 0x2E && p + 1 < end
            && p + 1 < v.len() && i_ident(v[p + 1]) is Some {
            Some((ISimple::Class(i_ident(v[p + 1]).unwrap()), p + 2))
        } else {
            None
        },
        // `<attribute-selector>`
        ComponentValue::SimpleBlock { associated_token: Token::OpenSquare, value } => match i_attribute_selector(
            value,
            cx,
        ) {
            Some(a) => Some((ISimple::Attr(a), p + 1)),
            None => None,
        },
        // `<pseudo-class-selector>` = ':' `<ident-token>` | ':' `<function-token>` `<any-value>` ')'
        ComponentValue::Token { token: Token::Colon } => if p < 0 || p + 1 >= end || p + 1 >= v.len() {
            None
        } else {
            match v[p + 1] {
                ComponentValue::Token { token: Token::Ident { value } } => match i_pseudo_ident(value) {
                    Some(s) => Some((s, p + 2)),
                    None => None,
                },
                ComponentValue::Function { name, value } => match i_pseudo_function(
                    name,
                    value,
                    cx,
                    in_has,
                ) {
                    Some(s) => Some((s, p + 2)),
                    None => None,
                },
                // `::` begins a `<pseudo-element-selector>`: not supported.
                _ => None,
            }
        },
        _ => None,
    }
}

/// The functional pseudo-classes, with their arguments' grammars: `:is()` and `:where()` take
/// a `<forgiving-selector-list>` (§4.1, §4.3), `:not()` a `<complex-real-selector-list>`
/// (§4.2), `:has()` a `<relative-selector-list>` (§4.4), `:nth-child()` and
/// `:nth-last-child()` `An+B` and optionally `of` and a `<complex-real-selector-list>` (§14.1),
/// `:nth-of-type()` and `:nth-last-of-type()` `An+B` (§14.2).
pub open spec fn i_pseudo_function(
    name: Seq<u32>,
    args: Seq<ComponentValue>,
    cx: ICtx,
    in_has: bool,
) -> Option<ISimple>
    decreases args, 7nat, 0int,
{
    if i_ci_eq(name, seq![0x69u32, 0x73]) {
        match i_clist(args, 0, args.len() as int, cx, true, false, true, in_has) {
            Some(l) => Some(ISimple::Is(l)),
            None => None,
        }
    } else if i_ci_eq(name, seq![0x77u32, 0x68, 0x65, 0x72, 0x65]) {
        match i_clist(args, 0, args.len() as int, cx, true, false, true, in_has) {
            Some(l) => Some(ISimple::Where(l)),
            None => None,
        }
    } else if i_ci_eq(name, seq![0x6Eu32, 0x6F, 0x74]) {
        match i_clist(args, 0, args.len() as int, cx, false, false, true, in_has) {
            Some(l) => Some(ISimple::Not(l)),
            None => None,
        }
    } else if i_ci_eq(name, seq![0x68u32, 0x61, 0x73]) {
        // "':has()' cannot be nested."
        if in_has {
            None
        } else {
            match i_clist(args, 0, args.len() as int, cx, false, true, false, true) {
                Some(l) => Some(ISimple::Has(l)),
                None => None,
            }
        }
    } else if i_ci_eq(name, seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64]) {
        i_nth_child(args, false, cx, in_has)
    } else if i_ci_eq(
        name,
        seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x63, 0x68, 0x69, 0x6C, 0x64],
    ) {
        i_nth_child(args, true, cx, in_has)
    } else if i_ci_eq(name, seq![0x6Eu32, 0x74, 0x68, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70, 0x65]) {
        match a_n_plus_b(args) {
            Some((a, b)) => Some(ISimple::NthType { a, b, last: false }),
            None => None,
        }
    } else if i_ci_eq(
        name,
        seq![
            0x6Eu32, 0x74, 0x68, 0x2D, 0x6C, 0x61, 0x73, 0x74, 0x2D, 0x6F, 0x66, 0x2D, 0x74, 0x79, 0x70,
            0x65,
        ],
    ) {
        match a_n_plus_b(args) {
            Some((a, b)) => Some(ISimple::NthType { a, b, last: true }),
            None => None,
        }
    } else {
        None
    }
}

/// `:nth-child(An+B [of S]?)` and `:nth-last-child(...)` (§14.1): `S` is a
/// `<complex-real-selector-list>`; a list that is empty or invalid makes the pseudo-class
/// invalid.
pub open spec fn i_nth_child(args: Seq<ComponentValue>, last: bool, cx: ICtx, in_has: bool) -> Option<
    ISimple,
>
    decreases args, 6nat, 0int,
{
    let k = i_find_of(args, 0, args.len() as int);
    if k >= args.len() {
        match a_n_plus_b(args) {
            Some((a, b)) => Some(
                ISimple::NthChild { a, b, last, has_of: false, of: Seq::empty() },
            ),
            None => None,
        }
    } else {
        match a_n_plus_b(args.subrange(0, k)) {
            None => None,
            Some((a, b)) => match i_clist(args, k + 1, args.len() as int, cx, false, false, false, in_has) {
                Some(l) => Some(ISimple::NthChild { a, b, last, has_of: true, of: l }),
                None => None,
            },
        }
    }
}

/// §19.1 "parse a selector": a `<selector-list>` of the component values `v`, `None` if it
/// is invalid.
pub open spec fn i_parse_selector_list(v: Seq<ComponentValue>, cx: ICtx) -> Option<Seq<IComplex>> {
    i_clist(v, 0, v.len() as int, cx, false, false, false, false)
}

/// §19.2 "parse a relative selector": a `<relative-selector-list>`.
pub open spec fn i_parse_relative_selector_list(v: Seq<ComponentValue>, cx: ICtx) -> Option<
    Seq<IComplex>,
> {
    i_clist(v, 0, v.len() as int, cx, false, true, false, false)
}

// ------------------------------------------------------------------------------------
// The tree
// ------------------------------------------------------------------------------------

/// `n` is an element of the arena.
pub open spec fn i_is_el(doc: Document, n: NodeId) -> bool {
    n < doc.nodes.len() && doc.nodes[n as int].kind is Element
}

/// An element's namespace.
pub open spec fn i_ns(doc: Document, n: NodeId) -> Option<Namespace> {
    match doc.nodes[n as int].kind {
        NodeKind::Element { namespace, .. } => namespace,
        _ => None,
    }
}

/// An element's local name.
pub open spec fn i_local(doc: Document, n: NodeId) -> Seq<u32> {
    match doc.nodes[n as int].kind {
        NodeKind::Element { local_name, .. } => local_name,
        _ => Seq::empty(),
    }
}

/// An element's attributes, in order.
pub open spec fn i_attrs(doc: Document, n: NodeId) -> Seq<Attr> {
    match doc.nodes[n as int].kind {
        NodeKind::Element { attributes, .. } => attributes,
        _ => Seq::empty(),
    }
}

/// The document is in quirks mode: class names and IDs match ASCII case-insensitively (§7, §8).
pub open spec fn i_quirks(doc: Document) -> bool {
    match doc.nodes[0].kind {
        NodeKind::Document { mode, .. } => mode is Quirks,
        _ => false,
    }
}

/// The elements among `s`, in order.
pub open spec fn i_elements(doc: Document, s: Seq<NodeId>) -> Seq<NodeId>
    decreases s.len(),
{
    if s.len() == 0 {
        s
    } else if i_is_el(doc, s[0]) {
        seq![s[0]] + i_elements(doc, s.drop_first())
    } else {
        i_elements(doc, s.drop_first())
    }
}

/// §14 "inclusive siblings": the element children of the parent, in order, or the
/// element alone if it has no parent.
pub open spec fn i_sibs(doc: Document, e: NodeId) -> Seq<NodeId> {
    match parent(doc, e) {
        None => seq![e],
        Some(p) => i_elements(doc, doc.nodes[p as int].children),
    }
}

/// §15: `p` and `e` are elements related as `c` says, `p` being the one on the left.
pub open spec fn i_related(doc: Document, c: IComb, p: NodeId, e: NodeId) -> bool {
    i_is_el(doc, p) && i_is_el(doc, e) && match c {
        // "an arbitrary descendant of some ancestor element"
        IComb::Descendant => is_descendant(doc, e, p),
        IComb::Child => parent(doc, e) == Some(p),
        // "the element represented by the first compound selector immediately precedes the
        // element represented by the second one", non-elements ignored.
        IComb::Next => {
            let sibs = i_sibs(doc, e);
            let i = index_of(sibs, e);
            parent(doc, e) is Some && i > 0 && sibs[i - 1] == p
        },
        // "precedes (not necessarily immediately)", sharing a parent.
        IComb::Subsequent => {
            let sibs = i_sibs(doc, e);
            parent(doc, e) is Some && parent(doc, p) == parent(doc, e) && 0 <= index_of(sibs, p)
                < index_of(sibs, e)
        },
    }
}

// ------------------------------------------------------------------------------------
// §6 and §7, §8: attribute values, classes and IDs
// ------------------------------------------------------------------------------------

/// Two strings are equal as a case flag says.
pub open spec fn i_same(ci: bool, a: Seq<u32>, b: Seq<u32>) -> bool {
    if ci {
        i_ci_eq(a, b)
    } else {
        a == b
    }
}

/// `val[i..j]` is one of the "whitespace-separated list of words" (§6.1) of `val`.
pub open spec fn i_word(val: Seq<u32>, i: int, j: int) -> bool {
    0 <= i < j <= val.len() && (i == 0 || i_white(val[i - 1])) && (j == val.len() || i_white(val[j]))
        && forall|k: int| i <= k < j ==> !i_white(#[trigger] val[k])
}

/// `val` is a whitespace-separated list of words, one of which is `word` (compared as `ci` says).
pub open spec fn i_has_word(ci: bool, val: Seq<u32>, word: Seq<u32>) -> bool {
    exists|i: int, j: int| i_word(val, i, j) && i_same(ci, val.subrange(i, j), word)
}

/// §6.1 and §6.2: an attribute's value `val` meets a matcher with value `sv`.
pub open spec fn i_value_matches(op: IAttrOp, ci: bool, val: Seq<u32>, sv: Seq<u32>) -> bool {
    match op {
        IAttrOp::Exists => true,
        // "exactly 'val'"
        IAttrOp::Eq => i_same(ci, val, sv),
        // "a whitespace-separated list of words, one of which is exactly 'val'. If 'val'
        // contains whitespace, it will never represent anything. Also if 'val' is the empty
        // string, it will never represent anything."
        IAttrOp::Includes => i_has_word(ci, val, sv),
        // "exactly 'val' or beginning with 'val' immediately followed by '-'"
        IAttrOp::Dash => i_same(ci, val, sv) || (val.len() > sv.len() && i_same(
            ci,
            val.subrange(0, sv.len() as int),
            sv,
        ) && val[sv.len() as int] == 0x2D),
        // "begins with the prefix 'val'. If 'val' is the empty string then the selector does
        // not represent anything."
        IAttrOp::Prefix => sv.len() > 0 && val.len() >= sv.len() && i_same(
            ci,
            val.subrange(0, sv.len() as int),
            sv,
        ),
        IAttrOp::Suffix => sv.len() > 0 && val.len() >= sv.len() && i_same(
            ci,
            val.subrange(val.len() - sv.len(), val.len() as int),
            sv,
        ),
        IAttrOp::Substring => sv.len() > 0 && exists|i: int|
            0 <= i && i + sv.len() <= val.len() && i_same(
                ci,
                #[trigger] val.subrange(i, i + sv.len()),
                sv,
            ),
    }
}

/// §6.4: an attribute's namespace meets the one an attribute selector names.
pub open spec fn i_attr_ns_matches(n: INs, a: Option<Namespace>) -> bool {
    match n {
        INs::Any => true,
        INs::NoNs => a is None,
        INs::Is(x) => a == Some(x),
    }
}

/// §6: the element has an attribute that the attribute selector matches.
pub open spec fn i_attr_matches(doc: Document, e: NodeId, s: IAttr) -> bool {
    exists|k: int|
        0 <= k < i_attrs(doc, e).len() && {
            let a = #[trigger] i_attrs(doc, e)[k];
            a.local_name == s.name && i_attr_ns_matches(s.ns, a.namespace) && i_value_matches(
                s.op,
                s.ci,
                a.value,
                s.value,
            )
        }
}

/// §8 ID selector: the element has an ID. "If an element has multiple ID attributes, all of
/// them must be treated as IDs." In quirks mode the comparison is ASCII case-insensitive.
pub open spec fn i_has_id(doc: Document, e: NodeId, id: Seq<u32>) -> bool {
    exists|k: int|
        0 <= k < i_attrs(doc, e).len() && {
            let a = #[trigger] i_attrs(doc, e)[k];
            a.namespace is None && a.local_name == seq![0x69u32, 0x64] && i_same(
                i_quirks(doc),
                a.value,
                id,
            )
        }
}

/// §7 class selector: the element's `class` attribute, a whitespace-separated list of
/// classes, has the class (ASCII case-insensitively in quirks mode).
pub open spec fn i_has_class(doc: Document, e: NodeId, class: Seq<u32>) -> bool {
    exists|k: int|
        0 <= k < i_attrs(doc, e).len() && {
            let a = #[trigger] i_attrs(doc, e)[k];
            a.namespace is None && a.local_name == seq![0x63u32, 0x6C, 0x61, 0x73, 0x73]
                && i_has_word(i_quirks(doc), a.value, class)
        }
}

/// §5.1 and §5.2: the element meets a type or universal selector.
pub open spec fn i_type_matches(doc: Document, e: NodeId, t: IType) -> bool {
    (match t.ns {
        INs::Any => true,
        INs::NoNs => i_ns(doc, e) is None,
        INs::Is(x) => i_ns(doc, e) == Some(x),
    }) && (match t.name {
        IName::Star => true,
        IName::Local(n) => i_local(doc, e) == n,
    })
}

// ------------------------------------------------------------------------------------
// §14 child-indexed pseudo-classes
// ------------------------------------------------------------------------------------

/// §14.1: `pos` is `An+B` for some non-negative integer `n`.
pub open spec fn i_anb(a: int, b: int, pos: int) -> bool {
    exists|n: int| n >= 0 && #[trigger] (a * n) + b == pos
}

/// §14: the document white space check of `:empty`: the node is not an element, and is not a
/// text node with data other than white space.
pub open spec fn i_node_is_empty_content(doc: Document, n: NodeId) -> bool {
    match doc.nodes[n as int].kind {
        NodeKind::Element { .. } => false,
        NodeKind::Text { data } => forall|k: int| 0 <= k < data.len() ==> i_white(#[trigger] data[k]),
        _ => true,
    }
}

/// §14 `:empty`: "an element that has no children except, optionally, document white space
/// characters"; comments and the like do not count.
pub open spec fn i_is_empty(doc: Document, e: NodeId) -> bool {
    forall|k: int|
        0 <= k < doc.nodes[e as int].children.len() ==> {
            let c = #[trigger] doc.nodes[e as int].children[k];
            c >= doc.nodes.len() || i_node_is_empty_content(doc, c)
        }
}

/// §14 `:root`: "the root of the document", the element whose parent is the document node.
pub open spec fn i_is_root(doc: Document, e: NodeId) -> bool {
    match parent(doc, e) {
        Some(p) => p < doc.nodes.len() && doc.nodes[p as int].kind is Document,
        None => false,
    }
}

/// §12 `:scope`: the scoping root if there is one, else the root of the tree.
pub open spec fn i_is_scope(doc: Document, scope: Option<NodeId>, e: NodeId) -> bool {
    match scope {
        Some(s) => s == e,
        None => i_is_root(doc, e),
    }
}

/// §14.2 the elements of `sibs[lo..hi)` of the same type (namespace and local name) as `e`.
pub open spec fn i_cnt_type(doc: Document, sibs: Seq<NodeId>, e: NodeId, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        (if i_ns(doc, sibs[hi - 1]) == i_ns(doc, e) && i_local(doc, sibs[hi - 1]) == i_local(doc, e) {
            1int
        } else {
            0int
        }) + i_cnt_type(doc, sibs, e, lo, hi - 1)
    }
}

// ------------------------------------------------------------------------------------
// §19.3 matching
// ------------------------------------------------------------------------------------

/// How many of `sibs[lo..hi)` count towards a position in `:nth-child(An+B of S)`: those that
/// match `S`, or all of them without an `of`.
pub open spec fn i_cnt(
    doc: Document,
    scope: Option<NodeId>,
    has_of: bool,
    of: Seq<IComplex>,
    sibs: Seq<NodeId>,
    lo: int,
    hi: int,
) -> int
    decreases of, 6nat, hi - lo,
{
    if lo >= hi {
        0
    } else {
        (if !has_of || i_m_list(doc, scope, of, sibs[hi - 1]) {
            1int
        } else {
            0int
        }) + i_cnt(doc, scope, has_of, of, sibs, lo, hi - 1)
    }
}

/// "A given element is said to match a selector list when it matches any (at least one) of the
/// selectors in that selector list."
pub open spec fn i_m_list(doc: Document, scope: Option<NodeId>, l: Seq<IComplex>, e: NodeId) -> bool
    decreases l, 5nat, 0int,
{
    exists|k: int| 0 <= k < l.len() && #[trigger] i_m_complex(doc, scope, l[k], None, e)
}

/// §19.3: a complex selector (a relative one, against `anchor`) matches `e`: "process it
/// compound selector at a time, in right-to-left order".
pub open spec fn i_m_complex(
    doc: Document,
    scope: Option<NodeId>,
    c: IComplex,
    anchor: Option<NodeId>,
    e: NodeId,
) -> bool
    decreases c, 4nat, 0int,
{
    c.units.len() > 0 && i_m_at(doc, scope, c, anchor, c.units.len() - 1, e)
}

/// The recursive step of §19.3, for the compound selector `c.units[k]` and the element `e`.
pub open spec fn i_m_at(
    doc: Document,
    scope: Option<NodeId>,
    c: IComplex,
    anchor: Option<NodeId>,
    k: int,
    e: NodeId,
) -> bool
    decreases c, 3nat, k,
{
    // "If any simple selectors in the rightmost compound selector does not match the element,
    // return failure."
    0 <= k < c.units.len() && i_m_compound(doc, scope, c.units[k], e) && if k <= 0 {
        // "Otherwise, if there is only one compound selector in the complex selector, return
        // success." A relative selector is also related to its anchor (§3.4).
        match c.lead {
            None => true,
            Some(comb) => match anchor {
                Some(a) => i_related(doc, comb, a, e),
                None => false,
            },
        }
    } else {
        // "Otherwise, consider all possible elements that could be related to this element by
        // the rightmost combinator. If the operation of matching the selector [without] this
        // compound selector and rightmost combinator against any one of these elements returns
        // success, then return success."
        exists|p: NodeId|
            i_related(doc, c.combs[k - 1], p, e) && #[trigger] i_m_at(doc, scope, c, anchor, k - 1, p)
    }
}

/// §3: "A given element is said to match a compound selector when it matches all simple
/// selectors in the compound selector."
pub open spec fn i_m_compound(doc: Document, scope: Option<NodeId>, c: ICompound, e: NodeId) -> bool
    decreases c, 2nat, 0int,
{
    i_is_el(doc, e) && (match c.ty {
        Some(t) => i_type_matches(doc, e, t),
        None => true,
    }) && forall|k: int| 0 <= k < c.subs.len() ==> i_m_simple(doc, scope, #[trigger] c.subs[k], e)
}

/// An element matches a simple selector other than a type selector.
pub open spec fn i_m_simple(doc: Document, scope: Option<NodeId>, s: ISimple, e: NodeId) -> bool
    decreases s, 1nat, 0int,
{
    match s {
        ISimple::Id(id) => i_has_id(doc, e, id),
        ISimple::Class(class) => i_has_class(doc, e, class),
        ISimple::Attr(a) => i_attr_matches(doc, e, a),
        // "the pseudo-class matches any element that matches any of the selectors in the list."
        // An empty list "is valid but matches nothing."
        ISimple::Is(l) => i_m_list(doc, scope, l, e),
        ISimple::Where(l) => i_m_list(doc, scope, l, e),
        // "It represents an element that is not represented by its argument."
        ISimple::Not(l) => !i_m_list(doc, scope, l, e),
        // "It represents an element if any of the relative selectors would match at least one
        // element when anchored against this element."
        ISimple::Has(l) => exists|k: int, x: NodeId|
            0 <= k < l.len() && i_is_el(doc, x) && #[trigger] i_m_complex(doc, scope, l[k], Some(e), x),
        ISimple::Root => i_is_root(doc, e),
        ISimple::Empty => i_is_empty(doc, e),
        ISimple::Scope => i_is_scope(doc, scope, e),
        ISimple::Defined => true,
        ISimple::NthChild { a, b, last, has_of, of } => {
            let sibs = i_sibs(doc, e);
            let i = index_of(sibs, e);
            i >= 0 && (!has_of || i_m_list(doc, scope, of, e)) && i_anb(
                a,
                b,
                1 + if last {
                    i_cnt(doc, scope, has_of, of, sibs, i + 1, sibs.len() as int)
                } else {
                    i_cnt(doc, scope, has_of, of, sibs, 0, i)
                },
            )
        },
        ISimple::NthType { a, b, last } => {
            let sibs = i_sibs(doc, e);
            let i = index_of(sibs, e);
            i >= 0 && i_anb(
                a,
                b,
                1 + if last {
                    i_cnt_type(doc, sibs, e, i + 1, sibs.len() as int)
                } else {
                    i_cnt_type(doc, sibs, e, 0, i)
                },
            )
        },
        // "an element that has no siblings"
        ISimple::OnlyChild => i_sibs(doc, e).len() == 1,
        ISimple::OnlyOfType => {
            let sibs = i_sibs(doc, e);
            i_cnt_type(doc, sibs, e, 0, sibs.len() as int) == 1
        },
    }
}

/// §19.3 "match a selector against an element": the selector list (a list of complex
/// selectors) matches the element if any of its complex selectors does.
pub open spec fn i_match_selector(doc: Document, scope: Option<NodeId>, l: Seq<IComplex>, e: NodeId) -> bool {
    i_is_el(doc, e) && i_m_list(doc, scope, l, e)
}

// ------------------------------------------------------------------------------------
// §17 Specificity
// ------------------------------------------------------------------------------------

/// §17 specificity (A, B, C).
pub ghost struct ISpec {
    /// ID selectors.
    pub a: nat,
    /// Class selectors, attribute selectors and pseudo-classes.
    pub b: nat,
    /// Type selectors and pseudo-elements.
    pub c: nat,
}

/// (0, 0, 0).
pub open spec fn i_sp_zero() -> ISpec {
    ISpec { a: 0, b: 0, c: 0 }
}

/// Specificities added component by component.
pub open spec fn i_sp_add(x: ISpec, y: ISpec) -> ISpec {
    ISpec { a: x.a + y.a, b: x.b + y.b, c: x.c + y.c }
}

/// §17 "Specificities are compared by comparing the three components in order": `x` is at
/// least as specific as `y`.
pub open spec fn i_sp_ge(x: ISpec, y: ISpec) -> bool {
    x.a > y.a || (x.a == y.a && (x.b > y.b || (x.b == y.b && x.c >= y.c)))
}

/// The more specific of two.
pub open spec fn i_sp_max(x: ISpec, y: ISpec) -> ISpec {
    if i_sp_ge(x, y) {
        x
    } else {
        y
    }
}

/// §17 "the specificity of the most specific complex selector in its selector list argument";
/// (0, 0, 0) for an empty list.
pub open spec fn i_sp_list(l: Seq<IComplex>, k: int) -> ISpec
    decreases l, 4nat, l.len() - k,
{
    if k < 0 || k >= l.len() {
        i_sp_zero()
    } else {
        i_sp_max(i_sp_complex(l[k], 0), i_sp_list(l, k + 1))
    }
}

/// §17 a complex selector's specificity: the sum of its compound selectors'.
pub open spec fn i_sp_complex(c: IComplex, k: int) -> ISpec
    decreases c, 3nat, c.units.len() - k,
{
    if k < 0 || k >= c.units.len() {
        i_sp_zero()
    } else {
        i_sp_add(i_sp_compound(c.units[k]), i_sp_complex(c, k + 1))
    }
}

/// §17 a compound selector's: its type selector (the universal selector is ignored), then its
/// other simple selectors.
pub open spec fn i_sp_compound(c: ICompound) -> ISpec
    decreases c, 2nat, 0int,
{
    i_sp_add(
        match c.ty {
            Some(IType { name: IName::Local(_), .. }) => ISpec { a: 0, b: 0, c: 1 },
            _ => i_sp_zero(),
        },
        i_sp_subs(c.subs, 0),
    )
}

/// The sum of the specificities of `subs[k..]`.
pub open spec fn i_sp_subs(subs: Seq<ISimple>, k: int) -> ISpec
    decreases subs, 2nat, subs.len() - k,
{
    if k < 0 || k >= subs.len() {
        i_sp_zero()
    } else {
        i_sp_add(i_sp_simple(subs[k]), i_sp_subs(subs, k + 1))
    }
}

/// §17 a simple selector's.
pub open spec fn i_sp_simple(s: ISimple) -> ISpec
    decreases s, 1nat, 0int,
{
    match s {
        ISimple::Id(_) => ISpec { a: 1, b: 0, c: 0 },
        ISimple::Class(_) => ISpec { a: 0, b: 1, c: 0 },
        ISimple::Attr(_) => ISpec { a: 0, b: 1, c: 0 },
        // ":is(), :not(), or :has() ... replaced by the specificity of the most specific
        // complex selector in its selector list argument."
        ISimple::Is(l) => i_sp_list(l, 0),
        ISimple::Not(l) => i_sp_list(l, 0),
        ISimple::Has(l) => i_sp_list(l, 0),
        // "The specificity of a :where() pseudo-class is replaced by zero."
        ISimple::Where(_) => i_sp_zero(),
        // ":nth-child() ... is the specificity of the pseudo-class itself (counting as one
        // pseudo-class selector) plus the specificity of the most specific complex selector in
        // its selector list argument (if any)."
        ISimple::NthChild { has_of, of, .. } => i_sp_add(
            ISpec { a: 0, b: 1, c: 0 },
            if has_of {
                i_sp_list(of, 0)
            } else {
                i_sp_zero()
            },
        ),
        // Every other pseudo-class is one pseudo-class selector.
        _ => ISpec { a: 0, b: 1, c: 0 },
    }
}

/// §17 "For a given matching process against the list, the specificity in effect is that of
/// the most specific selector in the list that matches": that of the most specific complex
/// selector of `l[k..]` that matches `e`, or none.
pub open spec fn i_specificity_from(
    doc: Document,
    scope: Option<NodeId>,
    l: Seq<IComplex>,
    e: NodeId,
    k: int,
) -> Option<ISpec>
    decreases l, 6nat, l.len() - k,
{
    if k < 0 || k >= l.len() {
        None
    } else {
        let rest = i_specificity_from(doc, scope, l, e, k + 1);
        if i_m_complex(doc, scope, l[k], None, e) {
            match rest {
                Some(r) => Some(i_sp_max(i_sp_complex(l[k], 0), r)),
                None => Some(i_sp_complex(l[k], 0)),
            }
        } else {
            rest
        }
    }
}

/// The specificity in effect when `l` matches `e`, if it does.
pub open spec fn i_specificity(doc: Document, scope: Option<NodeId>, l: Seq<IComplex>, e: NodeId) -> Option<
    ISpec,
> {
    i_specificity_from(doc, scope, l, e, 0)
}

// ------------------------------------------------------------------------------------
// Termination
// ------------------------------------------------------------------------------------
//
// The parsing functions move a position forward, and Verus has to be told that they do.

/// `i_skip_ws` moves forward, and stops at `end`.
pub proof fn lemma_skip_ws(v: Seq<ComponentValue>, p: int, end: int)
    ensures
        p <= i_skip_ws(v, p, end),
        p <= end ==> i_skip_ws(v, p, end) <= end,
    decreases end - p,
{
    if p < end && i_is_ws(v[p]) {
        lemma_skip_ws(v, p + 1, end);
    }
}

/// `i_comma` moves forward, and stops at `end`.
pub proof fn lemma_comma(v: Seq<ComponentValue>, p: int, end: int)
    ensures
        p <= i_comma(v, p, end),
        p <= end ==> i_comma(v, p, end) <= end,
    decreases end - p,
{
    if p < end && !i_is_comma(v[p]) {
        lemma_comma(v, p + 1, end);
    }
}

#[via_fn]
proof fn i_clist_decreases(
    v: Seq<ComponentValue>,
    p: int,
    end: int,
    cx: ICtx,
    forgiving: bool,
    rel: bool,
    exempt: bool,
    in_has: bool,
) {
    lemma_comma(v, p, end);
}

} // verus!
