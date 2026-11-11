//! The cascade, inheritance and computed values (phase-5.md item 5.7).
//!
//! [`cascade`] gives every element of a document its computed values for the subset: it
//! finds the declarations that apply to the element (from the user agent style sheet, the
//! presentational hints, the author style sheets and its `style` attribute), sorts them as
//! CSS Cascade 4 §6.1 says, takes each property's winner (rolling back for `revert`),
//! defaults the properties with no winner or a CSS-wide keyword (§7), and computes each
//! value (§4.4), parents before children. The result is a [`ComputedTable`], one entry per
//! node id, which items 5.13 to 5.16 (layout) and 5.20 (the renderer) read.
//!
//! The standards, each pinned in the module that transcribes it:
//!
//! - CSS Cascade 4, W3C Candidate Recommendation Snapshot of 13 January 2022
//!   (<https://www.w3.org/TR/2022/CR-css-cascade-4-20220113/>): §4 value processing, §5
//!   filtering ([`rules`]), §6.1 the sorting order, §6.2 origins, §6.3 importance, §6.4
//!   presentational hints ([`sort`]), §7 defaulting ([`compute`]); CSS Cascade 5 of the same
//!   date for `revert-layer` only. Sections marked † in other modules are from documents
//!   read at their current drafts, not at a pinned commit (phase-5.md's convention).
//! - CSS 2.1 §6.4.4 (presentational hints) and the property definition tables of the
//!   specifications `values/` cites ([`computed`], [`compute`]).
//! - HTML at commit 4c54fae1 (`data/html-4c54fae1/`): §15's user agent style sheet
//!   ([`ua`]), presentational hints ([`hints`]) and the microsyntaxes they use ([`legacy`]).
//! - CSS Logical Properties 1 for the flow-relative properties the user agent sheet uses
//!   ([`logical`]).
//!
//! # Modelling choices
//!
//! - **Origins.** The user agent origin holds HTML §15's sheet; the **user origin is
//!   empty** (Clazel has no user style sheets yet), so "Important user declarations" and
//!   "Normal user declarations" never occur, and `revert` from the author origin reaches the
//!   user agent's declarations. There are no animations or transitions.
//! - **One encapsulation context** (§6.1 "Context"): no shadow trees, so the context
//!   criterion never separates two declarations.
//! - **Presentational hints** enter the cascade in §6.4's "author presentational hint
//!   origin", between the user and author origins, with **specificity zero** (CSS 2.1
//!   §6.4.4: "given a specificity equal to zero"), the hints of the standard's CSS blocks
//!   (`data/hints.css`) before those of its prose ([`hints`]). Nothing in the subset tells
//!   §6.4's origin from CSS 2.1's "start of the author style sheet".
//! - **Order of appearance** is the order the sources are read: the user agent sheet, its
//!   quirks-mode rules, the rules HTML gives in prose ([`ua::prose`]), the hints, the author
//!   sheets in `sources::Sources::rules_for`'s order, and the `style` attribute last. Only
//!   declarations of one level and specificity are ever compared by it.
//! - **Filtering** (§5): a declaration outside the subset (unknown property or value outside
//!   its grammar) is dropped, as CSS Syntax says; a rule whose selector list
//!   `clazel-selectors` cannot parse is dropped.
//! - **Inheritance** follows the element tree: an element's parent element is its parent
//!   node if that is an element; the document element inherits initial values (§7.2).
//!   Elements in a `template`'s contents are not in the document tree and get no style.
//! - **Computed colours are resolved**: `currentcolor` in `background-color`, the border
//!   colours and `text-decoration-color` computes to the element's `color`. CSS Color 4
//!   keeps the keyword as the computed value, so that a descendant inheriting one of these
//!   (only through `inherit`, since none is inherited) would see its own colour; that case
//!   is the one difference, and nothing in the subset's exit page uses it.
//! - **Writing mode** is `horizontal-tb` and `ltr` everywhere ([`logical`], and `text-align:
//!   match-parent`).
//! - **Lengths** are 1/64 px in an `i32`, as `values/` converts them; computed lengths are
//!   rounded there once.
//! - **The walk is iterative**, with an explicit stack and at most one step per node, and
//!   visits each node at most once ([`preorder`]).

pub mod compute;
pub mod computed;
pub mod hints;
pub mod legacy;
pub mod logical;
pub mod rules;
pub mod sort;
pub mod ua;

use std::collections::HashMap;

use clazel_dom::exec::{Arena, ExecKind};

use crate::sources::{Device, Sources};
use crate::values::{Declared, Specified};
use compute::{Context, LONGHAND_COUNT, compute, index};
pub use computed::{ComputedStyle, ComputedTable, Family};
use hints::{html_element, is_html};
use rules::{Longhands, Selectors, read_declarations};
use sort::{Candidate, Level, Priority, Specificity, cascaded};

/// Where a prepared rule comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Origin {
    /// The user agent style sheet.
    Ua,
    /// HTML's presentational hints written as CSS (`data/hints.css`).
    Hint,
    /// An author style sheet.
    Author,
}

/// A style rule ready to match.
struct Prepared {
    origin: Origin,
    selectors: Selectors,
    /// Its declarations' longhands.
    declarations: Vec<Longhands>,
    /// The order of appearance of its first longhand.
    order: u32,
    /// A hint rule "only if border is not equivalent to zero" (`ua::needs_nonzero_border`).
    needs_border: bool,
}

/// One declared value on one element: its longhand, its place in the sort, and its value.
struct Entry<'a> {
    longhand: usize,
    priority: Priority,
    value: &'a Specified,
}

/// The nodes reachable from node 0 of a graph of `n` nodes whose children `children`
/// gives, in preorder, each at most once. Iterative, and the loop runs at most `n + 1`
/// steps, each popping one id and, if it is in range and not seen before, pushing its
/// children: on a tree (which a `clazel-dom` arena is, by its proven well-formedness) that
/// visits every node reachable from node 0, since each is pushed once; on any other graph
/// it still ends, having visited at most `n + 1` ids, each once.
pub fn preorder<'a>(n: usize, children: impl Fn(usize) -> &'a [usize]) -> Vec<usize> {
    let mut seen = vec![false; n];
    let mut out = Vec::new();
    let mut stack: Vec<usize> = vec![0];
    for _ in 0..n.saturating_add(1) {
        let Some(id) = stack.pop() else { break };
        match seen.get_mut(id) {
            Some(s) if !*s => *s = true,
            _ => continue,
        }
        out.push(id);
        stack.extend(children(id).iter().rev());
    }
    out
}

/// The nodes of `arena` reachable from the document (node 0), in tree order (preorder),
/// each at most once.
pub fn tree_order(arena: &Arena) -> Vec<usize> {
    preorder(arena.len(), |id| arena.children(id))
}

/// The `body` element's `link` attribute as a legacy colour (HTML §15.3.2): "the body
/// element" is the first child of the document element (an `html` element) that is a
/// `body` or `frameset` element.
fn body_link_color(arena: &Arena) -> Option<computed::Rgba> {
    let root = arena
        .children(0)
        .iter()
        .copied()
        .find(|&c| matches!(arena.kind(c), ExecKind::Element { .. }))?;
    if !is_html(arena, root, "html") {
        return None;
    }
    let body = arena
        .children(root)
        .iter()
        .copied()
        .find(|&c| is_html(arena, c, "body") || is_html(arena, c, "frameset"))?;
    if !is_html(arena, body, "body") {
        return None;
    }
    let (_, attributes) = html_element(arena, body)?;
    hints::attribute(attributes, "link").and_then(legacy::legacy_color)
}

/// Every style rule that applies on `device`, prepared, in order of appearance, and the
/// order of appearance after the last of them.
fn prepare(sources: &Sources, device: Device) -> (Vec<Prepared>, u32) {
    let ua::Sheets {
        ua,
        ua_quirks,
        hints: hint_sheet,
    } = ua::sheets();
    let mut rules = Vec::new();
    let mut order: u32 = 0;
    let mut add = |origin: Origin, r: &crate::sources::StyleRule, quirks: bool| {
        let Some(selectors) = Selectors::parse(&r.selectors) else {
            return;
        };
        let declarations = read_declarations(&r.declarations, quirks);
        let count: usize = declarations.iter().map(|d| d.set.len()).sum();
        if count == 0 {
            return;
        }
        rules.push(Prepared {
            origin,
            selectors,
            declarations,
            order,
            needs_border: origin == Origin::Hint && ua::needs_nonzero_border(&r.selectors),
        });
        order = order.saturating_add(u32::try_from(count).unwrap_or(u32::MAX));
    };
    for r in ua.rules_for(device) {
        add(Origin::Ua, r, false);
    }
    if sources.quirks {
        for r in ua_quirks.rules_for(device) {
            add(Origin::Ua, r, false);
        }
    }
    for r in hint_sheet.rules_for(device) {
        add(Origin::Hint, r, false);
    }
    for (_, r) in sources.rules_for(device) {
        add(Origin::Author, r, sources.quirks);
    }
    (rules, order)
}

/// The priority of a declaration of `origin`.
fn priority(origin: Origin, important: bool, specificity: Specificity, order: u32) -> Priority {
    match origin {
        Origin::Hint => Priority {
            level: Level::Hint,
            attached: false,
            specificity: Specificity::default(),
            order,
        },
        Origin::Ua | Origin::Author => Priority {
            level: Level::of(origin == Origin::Ua, important),
            attached: false,
            specificity,
            order,
        },
    }
}

/// Push the entries of `declarations` at `make(important, k)`'s priority, `k` counting the
/// longhands from 0.
fn push_all<'a>(
    entries: &mut Vec<Entry<'a>>,
    declarations: &'a [Longhands],
    mut make: impl FnMut(bool, u32) -> Priority,
) {
    let mut k: u32 = 0;
    for lh in declarations {
        for d in &lh.set {
            entries.push(Entry {
                longhand: index(d.property),
                priority: make(lh.important, k),
                value: &d.value,
            });
            k = k.saturating_add(1);
        }
    }
}

fn push_declared<'a>(
    entries: &mut Vec<Entry<'a>>,
    set: &'a [Declared],
    mut make: impl FnMut(u32) -> Priority,
) {
    let mut k: u32 = 0;
    for d in set {
        entries.push(Entry {
            longhand: index(d.property),
            priority: make(k),
            value: &d.value,
        });
        k = k.saturating_add(1);
    }
}

/// §4.2: each longhand's cascaded value among `entries`, indexed by [`index`].
fn cascaded_values<'a>(entries: &mut [Entry<'a>]) -> Vec<Option<&'a Specified>> {
    let mut out: Vec<Option<&'a Specified>> = vec![None; LONGHAND_COUNT];
    entries.sort_by_key(|e| (e.longhand, e.priority));
    let mut start = 0usize;
    for _ in 0..entries.len() {
        let Some(first) = entries.get(start) else {
            break;
        };
        let l = first.longhand;
        let end = entries
            .iter()
            .skip(start)
            .position(|e| e.longhand != l)
            .map_or(entries.len(), |p| start.saturating_add(p));
        let group = entries.get(start..end).unwrap_or_default();
        let candidates: Vec<Candidate> = group
            .iter()
            .map(|e| Candidate {
                priority: e.priority,
                wide: match e.value {
                    Specified::Wide(w) => Some(*w),
                    Specified::Value(_) => None,
                },
            })
            .collect();
        if let Some(i) = cascaded(&candidates)
            && let (Some(e), Some(slot)) = (group.get(i), out.get_mut(l))
        {
            *slot = Some(e.value);
        }
        start = end;
    }
    out
}

/// The computed values of every element of the document in `arena`, whose style sources
/// are `sources` (`sources::collect` of the same arena, with its links loaded), on
/// `device`. `arena` must be a document the tree builder made (selector matching needs a
/// well-formed tree).
pub fn cascade(arena: &Arena, sources: &Sources, device: Device) -> ComputedTable {
    let quirks = sources.quirks;
    let (mut rules, after_rules) = prepare(sources, device);
    let attributes: HashMap<usize, Vec<Longhands>> = sources
        .attributes
        .iter()
        .map(|a| (a.node, read_declarations(&a.declarations, quirks)))
        .collect();
    let hint_cx = hints::Context {
        quirks,
        link_color: body_link_color(arena),
    };
    let n = arena.len();
    let mut table = ComputedTable {
        styles: vec![None; n],
        families: vec![vec![Family::Generic("serif")]],
    };
    let initial = ComputedStyle::initial();
    let mut root_font_size = computed::MEDIUM_PX64;
    for x in tree_order(arena) {
        if !matches!(arena.kind(x), ExecKind::Element { .. }) {
            continue;
        }
        let parent_element = arena
            .parent(x)
            .filter(|&p| matches!(arena.kind(p), ExecKind::Element { .. }));
        let is_root = parent_element.is_none();
        let parent = parent_element
            .and_then(|p| table.get(p))
            .cloned()
            .unwrap_or_else(|| initial.clone());
        let element_hints = hints::hints(arena, x, hint_cx);
        let prose = ua::prose(arena, x, parent.text_align, quirks);
        let mut entries: Vec<Entry<'_>> = Vec::new();
        for r in &mut rules {
            let Some(spec) = r.selectors.match_element(arena, x) else {
                continue;
            };
            if r.needs_border && !ua::border_not_zero(arena, x) {
                continue;
            }
            let (origin, base) = (r.origin, r.order);
            push_all(&mut entries, &r.declarations, |important, k| {
                priority(origin, important, spec, base.saturating_add(k))
            });
        }
        let mut order = after_rules;
        for p in &prose {
            let base = order;
            push_declared(&mut entries, &p.set, |k| {
                priority(Origin::Ua, false, p.specificity, base.saturating_add(k))
            });
            order = order.saturating_add(u32::try_from(p.set.len()).unwrap_or(u32::MAX));
        }
        let base = order;
        push_declared(&mut entries, &element_hints.set, |k| {
            priority(
                Origin::Hint,
                false,
                Specificity::default(),
                base.saturating_add(k),
            )
        });
        order = order.saturating_add(u32::try_from(element_hints.set.len()).unwrap_or(u32::MAX));
        if let Some(own) = attributes.get(&x) {
            let base = order;
            push_all(&mut entries, own, |important, k| Priority {
                level: Level::of(false, important),
                attached: true,
                specificity: Specificity::default(),
                order: base.saturating_add(k),
            });
        }
        let values = cascaded_values(&mut entries);
        let mut cx = Context {
            parent: &parent,
            root_font_size,
            is_root,
            families: &mut table.families,
        };
        let mut style = compute(&values, &mut cx);
        style.align_descendants = element_hints.align;
        if is_root {
            root_font_size = style.font_size;
        }
        if let Some(slot) = table.styles.get_mut(x) {
            *slot = Some(style);
        }
    }
    table
}

#[cfg(test)]
mod tests;
