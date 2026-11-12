//! List items' markers: their ordinals and their text (phase-5.md item
//! 5.13, "list items (§12.5†, a marker box with `list-style-type`)").
//!
//! Sources: CSS 2.1 §12.5 "Lists" and §12.4.1 "Nested counters and scope";
//! CSS Lists 3 §4.5† (the order of `counter-reset`, `counter-increment` and
//! `counter-set`) and §4.6† (the implicit `list-item` counter); CSS Counter
//! Styles 3 §6† and §7† (the predefined counter styles); HTML §15.3.7
//! "Lists" at commit `4c54fae1` (`ol, ul, menu { counter-reset: list-item;
//! }`, and the `start` and `value` attributes as presentational hints for
//! `counter-reset` and `counter-set`).
//!
//! Modelling choices:
//!
//! - **Counters are not in the subset** (`counter-reset`, `counter-set`
//!   and `counter-increment` are not computed), so the `list-item` counter
//!   is computed here from what the user agent style sheet and HTML's hints
//!   would give it: reset to 0 by each `ol`, `ul` and `menu` element (to
//!   `start` − 1 for an `ol` whose `start` parses as an integer), incremented
//!   by 1 by each list item (CSS Lists 3 §4.6†), and set by an `li`'s
//!   `value` when it parses as an integer, after the increment (§4.5†:
//!   reset, then increment, then set).
//! - **Scope.** A list item's counter is the one of its nearest ancestor
//!   `ol`, `ul` or `menu`; a list item with none shares a counter with its
//!   siblings (§12.4.1: a counter instantiated on an element is in scope for
//!   its following siblings). CSS also puts an element's following siblings
//!   and their descendants in its counter's scope; those cases (a list item
//!   after a list, outside it) count from the list item's own scope here
//!   (listed).
//! - **`reversed`** on `ol` is not applied: such a list counts up (listed).
//! - **`list-style-position`** is not in the subset: every marker is a box
//!   placed as `outside` places it, by layout, and is its list item's first
//!   child. HTML's quirks-mode rule `li { list-style-position: inside; }`
//!   is therefore not applied (listed).
//! - **Counter styles**: `disc`, `circle`, `square`, `disclosure-open`,
//!   `disclosure-closed`, `decimal`, `decimal-leading-zero`, `lower-roman`,
//!   `upper-roman`, `lower-alpha`, `lower-latin`, `upper-alpha`,
//!   `upper-latin` and `lower-greek` are drawn as Counter Styles 3 defines
//!   them, with their fallback (`decimal`) outside their ranges. Every other
//!   predefined or unknown name is drawn as `decimal` (an unknown name
//!   "names no style", Counter Styles 3 §1.2†). A `<string>` is its text.

use std::collections::HashMap;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::ListStyleType;
use clazel_style::cascade::hints::{attribute, html_element, is_html};
use clazel_style::cascade::legacy::integer;
use clazel_style::cascade::tree_order;

/// Whose `list-item` counter a list item uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Scope {
    /// The nearest ancestor `ol`, `ul` or `menu`.
    List(usize),
    /// None: the list item's parent (or the document).
    Parent(Option<usize>),
}

/// HTML §15.3.7: `ol, ul, menu { counter-reset: list-item; }`.
fn resets(arena: &Arena, x: usize) -> bool {
    is_html(arena, x, "ol") || is_html(arena, x, "ul") || is_html(arena, x, "menu")
}

/// The ordinal of each list item of `arena` (the elements `is_list_item`
/// says have `display: list-item`), indexed by node id; 0 for other nodes.
/// One pass in tree order, with each node's nearest list ancestor found
/// from its parent's (no walk up the tree per node).
pub fn ordinals(arena: &Arena, is_list_item: impl Fn(usize) -> bool) -> Vec<i64> {
    let n = arena.len();
    let mut ordinal = vec![0i64; n];
    // nearest[x]: the nearest inclusive ancestor of x that resets the
    // counter. Parents come before children in tree order.
    let mut nearest: Vec<Option<usize>> = vec![None; n];
    let mut counters: HashMap<Scope, i64> = HashMap::new();
    for x in tree_order(arena) {
        let parent = arena.parent(x);
        let from_parent = parent.and_then(|p| nearest.get(p).copied().flatten());
        let own = if matches!(arena.kind(x), ExecKind::Element { .. }) && resets(arena, x) {
            Some(x)
        } else {
            from_parent
        };
        if let Some(slot) = nearest.get_mut(x) {
            *slot = own;
        }
        if !is_list_item(x) {
            continue;
        }
        let scope = from_parent.map_or(Scope::Parent(parent), Scope::List);
        let start = match scope {
            // `ol`'s `start` hint: `counter-reset: list-item (value − 1)`.
            Scope::List(list) if is_html(arena, list, "ol") => html_element(arena, list)
                .and_then(|(_, a)| attribute(a, "start"))
                .and_then(integer)
                .map_or(0, |v| v.saturating_sub(1)),
            _ => 0,
        };
        let counter = counters.entry(scope).or_insert(start);
        // CSS Lists 3 §4.6†: the implicit increment by 1.
        *counter = counter.saturating_add(1);
        // `li`'s `value` hint: `counter-set: list-item value`, after the
        // increment (§4.5†).
        if is_html(arena, x, "li")
            && let Some(v) = html_element(arena, x)
                .and_then(|(_, a)| attribute(a, "value"))
                .and_then(integer)
        {
            *counter = v;
        }
        if let Some(slot) = ordinal.get_mut(x) {
            *slot = *counter;
        }
    }
    ordinal
}

/// `decimal` (Counter Styles 3 §6.1†: numeric, "0 1 2 3 4 5 6 7 8 9"), with
/// `-` for a negative value.
fn decimal(v: i64) -> String {
    v.to_string()
}

/// An additive Roman numeral for 1 to 3999 (Counter Styles 3 §6.1†,
/// `upper-roman`: "range: 1 3999"), or `None` outside the range.
fn roman(v: i64, upper: bool) -> Option<String> {
    if !(1..=3999).contains(&v) {
        return None;
    }
    const TABLE: [(i64, &str); 13] = [
        (1000, "m"),
        (900, "cm"),
        (500, "d"),
        (400, "cd"),
        (100, "c"),
        (90, "xc"),
        (50, "l"),
        (40, "xl"),
        (10, "x"),
        (9, "ix"),
        (5, "v"),
        (4, "iv"),
        (1, "i"),
    ];
    let mut rest = v;
    let mut out = String::new();
    for (weight, symbol) in TABLE {
        // At most 3 of each weight for a value up to 3999.
        for _ in 0..4 {
            if rest < weight {
                break;
            }
            rest = rest.saturating_sub(weight);
            out.push_str(symbol);
        }
    }
    Some(if upper { out.to_uppercase() } else { out })
}

/// An alphabetic counter (Counter Styles 3 §2†, "alphabetic": "a, b, …, z,
/// aa, ab, …"), for values of 1 and more; `None` below 1.
fn alphabetic(v: i64, symbols: &[char]) -> Option<String> {
    let base = i64::try_from(symbols.len()).ok().filter(|&b| b > 0)?;
    if v < 1 {
        return None;
    }
    let mut value = v;
    let mut out: Vec<char> = Vec::new();
    // Each step divides by at least 2 (`base` ≥ 2 for every style used), so
    // 64 steps cover every `i64`.
    for _ in 0..64 {
        if value < 1 {
            break;
        }
        value = value.saturating_sub(1);
        let digit = usize::try_from(value.rem_euclid(base)).unwrap_or(0);
        out.push(symbols.get(digit).copied().unwrap_or('?'));
        value = value.checked_div(base).unwrap_or(0);
    }
    out.reverse();
    Some(out.into_iter().collect())
}

/// The marker text of a list item with `list-style-type` `style` and
/// ordinal `ordinal`, with the style's suffix (". " for a numbered style,
/// " " for a symbol, Counter Styles 3 §6†); `None` for `none`.
pub fn text(style: &ListStyleType, ordinal: i64) -> Option<String> {
    let name = match style {
        ListStyleType::None => return None,
        ListStyleType::String(s) => return Some(super::replaced::string(s)),
        ListStyleType::Named(n) => *n,
        ListStyleType::Custom(_) => "decimal",
    };
    let symbol = |c: char| Some(format!("{c} "));
    let latin_lower: Vec<char> = ('a'..='z').collect();
    let latin_upper: Vec<char> = ('A'..='Z').collect();
    // α to ω without the final sigma (Counter Styles 3 §6.1†, `lower-greek`).
    let greek: Vec<char> = ('α'..='ω').filter(|&c| c != 'ς').collect();
    let numbered = match name {
        "disc" => return symbol('\u{2022}'),
        "circle" => return symbol('\u{25E6}'),
        "square" => return symbol('\u{25AA}'),
        "disclosure-open" => return symbol('\u{25BE}'),
        "disclosure-closed" => return symbol('\u{25B8}'),
        "decimal-leading-zero" if (0..10).contains(&ordinal) => Some(format!("0{ordinal}")),
        "decimal-leading-zero" if (-9..0).contains(&ordinal) => {
            Some(format!("-0{}", ordinal.unsigned_abs()))
        }
        "lower-roman" => roman(ordinal, false),
        "upper-roman" => roman(ordinal, true),
        "lower-alpha" | "lower-latin" => alphabetic(ordinal, &latin_lower),
        "upper-alpha" | "upper-latin" => alphabetic(ordinal, &latin_upper),
        "lower-greek" => alphabetic(ordinal, &greek),
        _ => None,
    };
    Some(format!(
        "{}. ",
        numbered.unwrap_or_else(|| decimal(ordinal))
    ))
}
