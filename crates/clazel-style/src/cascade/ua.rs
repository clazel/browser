//! The user agent style sheet: HTML §15's CSS blocks, which `cargo xtask tables` copies
//! into `data/ua.css`, `data/ua-quirks.css` and `data/hints.css` (`xtask/src/ua_sheet.rs`
//! says which block goes where), and the user agent rules §15 gives in prose.
//!
//! # Adaptations
//!
//! The files are the standard's text as written. Two things in them are outside the subset
//! of items 5.5 and 5.6, and are adapted here, where the files are read:
//!
//! - **`:heading`** (Selectors 5†, which §15.3.5 and §15.3.6 use) is not one of 5.5's
//!   pseudo-classes. In the user agent sheets only, `:heading` is read as `:is(h1, h2, h3,
//!   h4, h5, h6)` and `:heading(N, …)` as `:is(hN, …)` for the levels 1 to 6 it lists:
//!   the elements they match when no `headingoffset` attribute is set (HTML's
//!   `headingoffset` is not implemented). The specificity changes from a pseudo-class's to
//!   a type selector's; no other rule of the sheets sets the properties these rules set on
//!   headings, so the cascade's result is the same.
//! - **Flow-relative properties** (`margin-block`, `padding-inline-start`,
//!   `border-block-style`, …) are mapped to physical ones by [`super::logical`], for every
//!   origin.
//!
//! Every other declaration outside the subset (`content-visibility`, `position`, `float`,
//! `unicode-bidi`, `box-sizing`, `appearance`, `fit-content`, `calc()`, system colours, …)
//! is invalid and dropped by the cascade's filtering, as CSS says; `@namespace` is
//! recognised and ignored (5.8); `@media (scripting)` is false (scripting is off, and
//! 5.8 evaluates the unknown feature as false).
//!
//! # Rules given in prose
//!
//! [`prose`] gives, for one element, the user agent rules §15 states in prose:
//!
//! - §15.3.2: `body`'s margins default to 8px ("If none of the attributes for a property are
//!   found, or if the value of the attribute that was found cannot be parsed successfully,
//!   then a default value of 8px is expected to be used for that property instead"); the
//!   attributes themselves are hints (`hints.rs`), so they win when they parse;
//! - §15.3.8: "a rule in their user agent style sheet that matches th elements that have a
//!   parent node whose computed value for the 'text-align' property is its initial value,
//!   whose declaration block consists of just a single declaration that sets the
//!   'text-align' property to the value 'center'";
//! - §15.3.9, margin collapsing quirks: in quirks mode, user agent rules setting
//!   `margin-block-start` or `margin-block-end` to zero on some elements with default
//!   margins. They exist to override the sheet's margins, so they are given a specificity
//!   above any selector's ([`QUIRK_SPECIFICITY`]).

use clazel_dom::exec::{Arena, ExecKind};

use super::computed::TextAlign;
use super::hints::{html_element, is_html};
use super::sort::Specificity;
use crate::sources::StyleSheet;
use crate::values::component::Component;
use crate::values::longhand::Longhand;
use crate::values::number::{Length, LengthUnit, Num};
use crate::values::{Declared, Specified};

/// `data/ua.css`.
const UA: &str = include_str!("../../data/ua.css");
/// `data/ua-quirks.css`.
const UA_QUIRKS: &str = include_str!("../../data/ua-quirks.css");
/// `data/hints.css`.
const HINTS: &str = include_str!("../../data/hints.css");

/// Which of the three sheets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sheet {
    /// User agent rules, every document.
    Ua,
    /// User agent rules, quirks mode only.
    UaQuirks,
    /// Presentational hints.
    Hints,
}

/// `:heading` and `:heading(…)` in a selector's text, rewritten as the module says.
pub fn rewrite_heading(selectors: &str) -> String {
    const PSEUDO: &str = ":heading";
    let mut out = String::new();
    let mut rest = selectors;
    for _ in 0..selectors.len() {
        let Some(i) = rest.find(PSEUDO) else { break };
        out.push_str(rest.get(..i).unwrap_or_default());
        rest = rest
            .get(i.saturating_add(PSEUDO.len())..)
            .unwrap_or_default();
        let levels: Vec<u32> = if let Some(args) = rest.strip_prefix('(') {
            let end = args.find(')').unwrap_or(args.len());
            let inner = args.get(..end).unwrap_or_default();
            rest = args.get(end.saturating_add(1)..).unwrap_or_default();
            inner
                .split(',')
                .filter_map(|s| s.trim().parse::<u32>().ok())
                .filter(|n| (1..=6).contains(n))
                .collect()
        } else {
            (1..=6).collect()
        };
        let names: Vec<String> = levels.iter().map(|n| format!("h{n}")).collect();
        out.push_str(&format!(":is({})", names.join(", ")));
    }
    out.push_str(rest);
    out
}

/// One of the sheets, parsed, with `:heading` rewritten.
pub fn sheet(which: Sheet) -> StyleSheet {
    let text = match which {
        Sheet::Ua => UA,
        Sheet::UaQuirks => UA_QUIRKS,
        Sheet::Hints => HINTS,
    };
    let code_points: Vec<u32> = text.chars().map(u32::from).collect();
    let mut sheet = StyleSheet::parse(&code_points);
    for rule in &mut sheet.rules {
        let s: String = rule
            .selectors
            .iter()
            .filter_map(|&c| char::from_u32(c))
            .collect();
        if s.contains(":heading") {
            rule.selectors = rewrite_heading(&s).chars().map(u32::from).collect();
        }
    }
    sheet
}

/// True for the `table[border]` rules of the hints sheet that §15.3.8 marks "only if border
/// is not equivalent to zero": "expected to only be applied if the border attribute
/// mentioned in the selectors for the rule is not only present but, when parsed using the
/// rules for parsing non-negative integers, is also found to have a value other than zero
/// or to generate an error". Two blocks carry the mark; each is the only rule of the sheet
/// whose selectors mention `table[border]`.
pub fn needs_nonzero_border(selectors: &[u32]) -> bool {
    let s: String = selectors
        .iter()
        .filter_map(|&c| char::from_u32(c))
        .collect();
    s.contains("table[border]")
}

/// Whether the `border` attribute of the table that element `x` is, or is in, is "not
/// equivalent to zero" (see [`needs_nonzero_border`]). The table is the nearest ancestor (or
/// `x`) that is a `table`, which for the marked selectors (`table[border]` and its cells
/// through `tr` and row groups) is the one the selector named.
pub fn border_not_zero(arena: &Arena, x: usize) -> bool {
    let mut n = Some(x);
    for _ in 0..arena.len() {
        let Some(id) = n else { break };
        if is_html(arena, id, "table") {
            let border =
                html_element(arena, id).and_then(|(_, a)| super::hints::attribute(a, "border"));
            return border.is_some_and(|b| super::legacy::non_negative_integer(b) != Some(0));
        }
        n = arena.parent(id);
    }
    false
}

/// The specificity of the margin collapsing quirks' rules: above every selector.
pub const QUIRK_SPECIFICITY: Specificity = Specificity {
    a: u32::MAX,
    b: u32::MAX,
    c: u32::MAX,
};

/// A prose rule: its declarations and the specificity they cascade at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProseRule {
    /// The specificity.
    pub specificity: Specificity,
    /// The declarations.
    pub set: Vec<Declared>,
}

fn px(v: i64) -> Specified {
    Specified::Value(vec![Component::Length(Length {
        value: Num::from_int(v),
        unit: LengthUnit::Px,
    })])
}

/// §15.3.9: "A node is substantial if it is a text node that is not inter-element
/// whitespace, or if it is an element node."
fn substantial(arena: &Arena, n: usize) -> bool {
    match arena.kind(n) {
        ExecKind::Element { .. } => true,
        // Inter-element whitespace (HTML §3.2.5.2†): a text node of ASCII whitespace only.
        ExecKind::Text { data } => !data
            .iter()
            .all(|&c| matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)),
        _ => false,
    }
}

/// §15.3.9: "A node is blank if it is an element that contains no substantial nodes."
fn blank(arena: &Arena, x: usize) -> bool {
    !arena.children(x).iter().any(|&c| substantial(arena, c))
}

/// §15.3.9: "The elements with default margins".
const DEFAULT_MARGINS: &[&str] = &[
    "blockquote",
    "dir",
    "dl",
    "h1",
    "h2",
    "h3",
    "h4",
    "h5",
    "h6",
    "listing",
    "menu",
    "ol",
    "p",
    "plaintext",
    "pre",
    "ul",
    "xmp",
];

/// The user agent rules §15 gives in prose for element `x` (see the module's documentation),
/// given its parent's computed `text-align` and the document's mode.
pub fn prose(
    arena: &Arena,
    x: usize,
    parent_text_align: TextAlign,
    quirks: bool,
) -> Vec<ProseRule> {
    let mut out = Vec::new();
    let Some((name, _)) = html_element(arena, x) else {
        return out;
    };
    let named = |s: &str| name.iter().copied().eq(s.chars().map(u32::from));
    let type_selector = Specificity { a: 0, b: 0, c: 1 };
    if named("body") {
        out.push(ProseRule {
            specificity: type_selector,
            set: [
                Longhand::MarginTop,
                Longhand::MarginRight,
                Longhand::MarginBottom,
                Longhand::MarginLeft,
            ]
            .into_iter()
            .map(|property| Declared {
                property,
                value: px(8),
            })
            .collect(),
        });
    }
    if named("th") && parent_text_align == TextAlign::Start {
        out.push(ProseRule {
            specificity: type_selector,
            set: vec![Declared {
                property: Longhand::TextAlign,
                value: Specified::Value(vec![Component::Keyword("center")]),
            }],
        });
    }
    if !quirks || !DEFAULT_MARGINS.iter().any(|d| named(d)) {
        return out;
    }
    let Some(parent) = arena.parent(x) else {
        return out;
    };
    let in_cell = is_html(arena, parent, "td") || is_html(arena, parent, "th");
    if !in_cell && !is_html(arena, parent, "body") {
        return out;
    }
    let siblings = arena.children(parent);
    let at = siblings.iter().position(|&s| s == x).unwrap_or(0);
    let before = siblings.get(..at).unwrap_or_default();
    let after = siblings.get(at.saturating_add(1)..).unwrap_or_default();
    let first = !before.iter().any(|&s| substantial(arena, s));
    let last = !after.iter().any(|&s| substantial(arena, s));
    let is_blank = blank(arena, x);
    let mut top = false;
    let mut bottom = false;
    // "any element with default margins that is the child of a body, td, or th element and
    // has no substantial previous siblings is expected to have a user-agent level style
    // sheet rule that sets its 'margin-block-start' property to zero."
    if first {
        top = true;
        // "... has no substantial previous siblings, and is blank, ... sets its
        // 'margin-block-end' property to zero also."
        bottom |= is_blank;
    }
    // "any element with default margins that is the child of a td or th element, has no
    // substantial following siblings, and is blank, ... sets its 'margin-block-start'
    // property to zero."
    if in_cell && last && is_blank {
        top = true;
    }
    // "any p element that is the child of a td or th element and has no substantial
    // following siblings, ... sets its 'margin-block-end' property to zero."
    if in_cell && last && named("p") {
        bottom = true;
    }
    let mut set = Vec::new();
    if top {
        set.push(Declared {
            property: Longhand::MarginTop,
            value: px(0),
        });
    }
    if bottom {
        set.push(Declared {
            property: Longhand::MarginBottom,
            value: px(0),
        });
    }
    if !set.is_empty() {
        out.push(ProseRule {
            specificity: QUIRK_SPECIFICITY,
            set,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn heading_rewrite() {
        assert_eq!(rewrite_heading(":heading"), ":is(h1, h2, h3, h4, h5, h6)");
        assert_eq!(rewrite_heading(":heading(2)"), ":is(h2)");
        assert_eq!(rewrite_heading(":heading(6, 7, 8, 9) x"), ":is(h6) x");
        assert_eq!(
            rewrite_heading("a, :heading, b"),
            "a, :is(h1, h2, h3, h4, h5, h6), b"
        );
    }

    #[test]
    fn sheets_parse() {
        let ua = sheet(Sheet::Ua);
        let quirks = sheet(Sheet::UaQuirks);
        let hints = sheet(Sheet::Hints);
        assert!(ua.rules.len() > 60, "{}", ua.rules.len());
        assert_eq!(quirks.rules.len(), 8);
        assert!(hints.rules.len() > 30, "{}", hints.rules.len());
        assert!(ua.rules.iter().all(|r| {
            let s: String = r
                .selectors
                .iter()
                .filter_map(|&c| char::from_u32(c))
                .collect();
            !s.contains(":heading")
        }));
        assert_eq!(
            hints
                .rules
                .iter()
                .filter(|r| needs_nonzero_border(&r.selectors))
                .count(),
            2
        );
    }
}
