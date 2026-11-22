//! DOM §4.2.6† `querySelector()` and `querySelectorAll()` (mixin
//! `ParentNode`), and §4.9† `matches()` and `closest()` (interface
//! `Element`), over a `clazel-dom` arena, with `clazel-selectors` (Phase 5)
//! for the selectors themselves.
//!
//! <https://dom.spec.whatwg.org/#scope-match-a-selectors-string>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit).
//!
//! Tier 0, not proven: this crate only calls `clazel-selectors`' proven
//! parser and matcher and walks the tree. Every walk is iterative (a work
//! list), so a deep tree does not overflow the stack.
//!
//! Modelling choices:
//! - Selectors text is a slice of code points, as every string of the arena
//!   is. The bindings (items 7.8 and 7.12) convert a script string.
//! - A node is an index of the arena, as in `clazel-dom`.
//! - DOM §4.2.6† "parse a selector" failing is [`SyntaxError`], which the
//!   bindings turn into a `DOMException` named `SyntaxError`. So is text
//!   longer than `clazel-css`'s `MAX_PARSER_INPUT`, which the parser's
//!   contract does not accept (the standard has no such limit).
//! - Each operation parses the selector once, then matches it per element.
//! - "Match a selector against an element" is `clazel-selectors`'
//!   `exec_match::matches`: it looks at the element's ancestors and
//!   siblings in the arena, also outside the node queried, as the standard
//!   wants (`#a p` queried on a node inside `#a` finds its `p`).
//! - A node id that is not in the arena, or is not an element where an
//!   element is required, matches nothing: `matches` is false, `closest`
//!   and `query_selector` are `None`, `query_selector_all` is empty.
//! - Template contents are not children in the arena, so a query does not
//!   enter them, as the standard has it.
//!
//! Known gap: `clazel-selectors` does not parse `:scope`, nor the other
//! pseudo-classes outside its subset, so such a selector is a
//! [`SyntaxError`] here. DOM says `:scope` is the node the method is called
//! on; that needs the matcher's support, and `clazel-selectors` is not this
//! crate's to change. `tests/conformance_selectors.rs` lists what this
//! costs among the WPT selectors.

use clazel_css::parser::contract::MAX_PARSER_INPUT;
use clazel_dom::exec::{Arena, ExecKind};
use clazel_selectors::exec_check::check;
use clazel_selectors::exec_match::matches as match_against_element;
use clazel_selectors::exec_parse::parse_selector;
use clazel_selectors::exec_types::ExecSelectors;

/// DOM §4.2.6† "parse a selector" failed: the bindings throw a
/// `DOMException` named `SyntaxError`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SyntaxError;

impl core::fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SyntaxError: the selector is not valid")
    }
}

impl std::error::Error for SyntaxError {}

/// A parsed selector list, to match against many elements.
pub struct Selector {
    parsed: ExecSelectors,
}

impl Selector {
    /// Selectors 4 §21.1† "parse a selector" on `text`; [`SyntaxError`] if it
    /// fails (DOM §4.2.6†: "If s is failure, then throw a "SyntaxError"
    /// DOMException").
    pub fn parse(text: &[u32]) -> Result<Selector, SyntaxError> {
        if text.len() > MAX_PARSER_INPUT {
            return Err(SyntaxError);
        }
        let parsed = parse_selector(text).ok_or(SyntaxError)?;
        // The parser's contract says its result passes `check`; matching
        // requires it, so a result that did not is refused, not matched.
        if !check(&parsed) {
            return Err(SyntaxError);
        }
        Ok(Selector { parsed })
    }

    /// Whether `x` is an element of `arena` that this selector matches
    /// (Selectors 4 §21.3† "match a selector against an element").
    pub fn matches(&self, arena: &Arena, x: usize) -> bool {
        x < arena.len()
            && matches!(arena.kind(x), ExecKind::Element { .. })
            && match_against_element(arena, &self.parsed, x)
    }
}

/// The descendants of `root`, in tree order, visiting each once, stopping as
/// soon as `visit` returns true. The walk is a work list: the children of a
/// node are pushed in reverse, so the first pops first.
fn walk_descendants(arena: &Arena, root: usize, mut visit: impl FnMut(usize) -> bool) {
    if root >= arena.len() {
        return;
    }
    let mut stack: Vec<usize> = arena.children(root).iter().rev().copied().collect();
    while let Some(n) = stack.pop() {
        if visit(n) {
            return;
        }
        stack.extend(arena.children(n).iter().rev().copied());
    }
}

/// DOM §4.2.6† `querySelector(selectors)`: "return the first result of
/// running scope-match a selectors string selectors against this, if the
/// result is not an empty list; otherwise null". The first element in tree
/// order, among the descendants of `root` only (never `root` itself), that
/// the selectors match.
///
/// DOM §4.2.6† "scope-match a selectors string": 1. "Let s be the result of
/// parse a selector selectors." 2. "If s is failure, then throw a
/// "SyntaxError" DOMException." 3. "Return the result of match a selector
/// against a tree with s and node's root using scoping root node."
pub fn query_selector(
    arena: &Arena,
    root: usize,
    selectors: &[u32],
) -> Result<Option<usize>, SyntaxError> {
    let s = Selector::parse(selectors)?;
    let mut found = None;
    walk_descendants(arena, root, |n| {
        let hit = s.matches(arena, n);
        if hit {
            found = Some(n);
        }
        hit
    });
    Ok(found)
}

/// DOM §4.2.6† `querySelectorAll(selectors)`: all the elements that
/// [`query_selector`] could return, in tree order. (A `NodeList` that is
/// static: this is a snapshot.)
pub fn query_selector_all(
    arena: &Arena,
    root: usize,
    selectors: &[u32],
) -> Result<Vec<usize>, SyntaxError> {
    let s = Selector::parse(selectors)?;
    let mut found = Vec::new();
    walk_descendants(arena, root, |n| {
        if s.matches(arena, n) {
            found.push(n);
        }
        false
    });
    Ok(found)
}

/// DOM §4.9† `matches(selectors)`: 1. "Let s be the result of parse a
/// selector given selectors." 2. "If s is failure, then throw a
/// "SyntaxError" DOMException." 3. "If the result of match a selector
/// against an element, using s, this, and :scope element this, returns
/// success, then return true; otherwise, return false."
pub fn matches(arena: &Arena, element: usize, selectors: &[u32]) -> Result<bool, SyntaxError> {
    let s = Selector::parse(selectors)?;
    Ok(s.matches(arena, element))
}

/// DOM §4.9† `closest(selectors)`: 1.-2. as [`matches`]. 3. "Let elements be
/// this's inclusive ancestors that are elements, in reverse tree order."
/// 4. "For each element in elements, if match a selector against an
/// element, using s, element, and :scope element this, returns success,
/// return element." 5. "Return null."
pub fn closest(
    arena: &Arena,
    element: usize,
    selectors: &[u32],
) -> Result<Option<usize>, SyntaxError> {
    let s = Selector::parse(selectors)?;
    let mut cur = (element < arena.len()).then_some(element);
    while let Some(n) = cur {
        if s.matches(arena, n) {
            return Ok(Some(n));
        }
        cur = arena.parent(n);
    }
    Ok(None)
}
