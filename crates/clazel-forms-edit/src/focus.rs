//! Which elements can have the focus, and the order Tab visits them
//! (phase-6.md item 6.15).
//!
//! Sources: HTML §6.6 "Focus" (§6.6.2 "Focusable areas", §6.6.3 "The
//! `tabindex` attribute", §6.6.4 "Sequential focus navigation"; numbers as
//! the multipage build at the commit item 6.13 pins has them), whose rule
//! this module follows: an element with a `tabindex` attribute that parses
//! as an integer is focusable, and the sequential navigation order is the
//! elements with a positive `tabindex` in increasing order of it (ties in tree
//! order), then those with `tabindex` 0 or none, in tree order; a negative
//! `tabindex` makes an element focusable by a click but not by Tab.
//!
//! Modelling choices (listed):
//! - **What is focusable without `tabindex`**: `a` with an `href`, and a
//!   `button`, `input` (not in the Hidden state), `select` or `textarea` that
//!   is not disabled. (`summary`, `iframe`, editing hosts and scrollable
//!   boxes are not: no script, no scrolling by keyboard yet.) A disabled
//!   control is not focusable whatever its `tabindex`.
//! - **A radio button group is one stop** (§6.6.4's platform convention,
//!   which engines follow): the checked button of its group, or the first when
//!   none is checked. The caller filters; this module orders.
//! - **Tab at the end wraps** to the other end of the sequence (a tab with
//!   no browser chrome to hand the focus to).
//! - Shadow trees, `inert`, `hidden` and `display: none` are not looked at:
//!   an element with no box is still in the order (the document has no
//!   scripts to hide things, and `display: none` elements are rare in a
//!   form's own markup); listed.

use clazel_dom::exec::Arena;
use clazel_forms::exec::entry::is_disabled_exec;
use clazel_forms::exec::read::input_type_exec;
use clazel_forms::spec::InputType;

use crate::dom::{attr, has, is, parse_integer, valid};

/// What makes an element focusable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Focusable {
    /// The element's `tabindex` value (0 when it has none).
    pub tabindex: i64,
    /// Whether Tab reaches it (`tabindex` not negative).
    pub sequential: bool,
}

/// Whether control `n` is a submittable element that is disabled.
pub fn disabled(arena: &Arena, n: usize) -> bool {
    (is(arena, n, "button")
        || is(arena, n, "input")
        || is(arena, n, "select")
        || is(arena, n, "textarea"))
        && is_disabled_exec(arena, n)
}

/// Whether `n` is focusable, and how (the module's rules).
pub fn focusable(arena: &Arena, n: usize) -> Option<Focusable> {
    if !valid(arena, n) || disabled(arena, n) {
        return None;
    }
    let natural = (is(arena, n, "a") && has(arena, n, "href"))
        || is(arena, n, "button")
        || is(arena, n, "select")
        || is(arena, n, "textarea")
        || (is(arena, n, "input") && !matches!(input_type_exec(arena, n), InputType::Hidden));
    let tabindex = attr(arena, n, "tabindex").and_then(|v| parse_integer(&v));
    match tabindex {
        Some(t) => Some(Focusable {
            tabindex: t,
            sequential: t >= 0,
        }),
        None => natural.then_some(Focusable {
            tabindex: 0,
            sequential: true,
        }),
    }
}

/// The sort key of a stop: positive `tabindex` first by value, then the
/// rest, each in tree order (`index` is the node's place in tree order).
pub fn key(f: Focusable, index: usize) -> (bool, i64, usize) {
    if f.tabindex > 0 {
        (false, f.tabindex, index)
    } else {
        (true, 0, index)
    }
}

/// The nodes Tab visits, in order, from `order` (the nodes in tree order),
/// each with its key.
pub fn sequence(arena: &Arena, order: &[usize]) -> Vec<(usize, (bool, i64, usize))> {
    let mut stops: Vec<(usize, (bool, i64, usize))> = order
        .iter()
        .enumerate()
        .filter_map(|(i, &n)| {
            let f = focusable(arena, n)?;
            f.sequential.then(|| (n, key(f, i)))
        })
        .collect();
    stops.sort_by_key(|&(_, k)| k);
    stops
}
