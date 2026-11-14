//! Property values of Phase 5's subset (phase-5.md item 5.6).
//!
//! For each property the exit page needs (phase-5.md, "What the exit page needs", as 5.0(b)
//! fixed it), its value grammar from its defining specification, read from the component
//! values `clazel-css` parses (CSS Syntax 3 §5.4, "parse a list of component values", the
//! normalizing step of "parse something according to a CSS grammar", whose grammar is the
//! property's); shorthands expanded into longhands; the CSS-wide keywords; the Quirks Mode
//! Standard's two value quirks; and CSSOM's serialization, enough for WPT's expected
//! strings. Each grammar cites its section where it is written ([`longhand`],
//! [`shorthand`], [`color`], [`grammar`], [`number`]); a section marked † was written from
//! the documents as read on 2026-11-10 at their current drafts, not at a pinned commit
//! (phase-5.md's convention).
//!
//! # Modelling choices
//!
//! - **The subset.** Only the longhands in [`longhand::LONGHANDS`] and the shorthands in
//!   [`shorthand::SHORTHANDS`] are known; any other property, and any value outside the
//!   subset's grammar (`calc()` and the other math functions, viewport units, `var()`,
//!   `display`'s two-value syntax, the intrinsic sizing keywords, colour spaces other than
//!   sRGB, `image-set()`, several background layers), is invalid, so the declaration is
//!   dropped as CSS Syntax 3 says. The README lists them with the "parsed, no effect"
//!   properties.
//! - **Whitespace** between components is not read: no grammar of the subset gives it a
//!   meaning ([`items`]).
//! - **Numbers** are millionths in an `i64`, rounded once from the token's exact value and
//!   clamped to ±10^9 ([`number::Num::from_parts`]); CSS Values 4 §5.1 allows clamping to
//!   an implementation's range. Used lengths are 1/64 px in an `i32`, clamped to ±(2^30 -
//!   1) ([`number::to_px64`]); `ex` is 0.5 em.
//! - **Colours** resolve to 8-bit sRGB when parsed; named colours keep their name
//!   ([`color`]).
//! - **Specified values keep the order CSSOM serializes**, so a grammar that allows any
//!   order (`text-indent`, `text-decoration-line`) stores the canonical one.
//! - **`oblique 0deg`** is stored as `normal`, as the WPT cases expect engines to serialize
//!   it.
//! - **Quirks mode** is a flag: the hashless hex colour quirk and the unitless length quirk
//!   apply only to the properties on the Quirks Mode Standard's lists (§3.6† and §3.7†),
//!   when the property is set directly, never inside `border`, `border-*`, `background` or
//!   `font`. Limited-quirks mode is no-quirks mode for both.
//! - **Property names** match ASCII case-insensitively; `word-wrap` is `overflow-wrap`.
//!   Vendor-prefixed properties are unknown.

pub mod color;
pub mod component;
pub mod grammar;
pub mod items;
pub mod longhand;
pub mod number;
pub mod shorthand;

#[cfg(kani)]
mod proofs;

use component::{Component, to_string};
use items::{Cursor, Src, Values, eq_ignore_case, lookup};
use longhand::{ALIASES, LONGHANDS, Longhand};
use shorthand::{SHORTHANDS, Shorthand};

/// The CSS-wide keywords (CSS Values 4 §4.1.1†; CSS Cascade 5 adds `revert-layer`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Wide {
    /// `initial`.
    Initial,
    /// `inherit`.
    Inherit,
    /// `unset`.
    Unset,
    /// `revert`.
    Revert,
    /// `revert-layer`.
    RevertLayer,
}

/// The CSS-wide keywords, with their names.
pub const WIDE_KEYWORDS: &[(&str, Wide)] = &[
    ("initial", Wide::Initial),
    ("inherit", Wide::Inherit),
    ("unset", Wide::Unset),
    ("revert", Wide::Revert),
    ("revert-layer", Wide::RevertLayer),
];

impl Wide {
    /// The keyword.
    pub fn name(self) -> &'static str {
        WIDE_KEYWORDS
            .iter()
            .find(|(_, w)| *w == self)
            .map_or("", |(n, _)| n)
    }
}

/// True if `s` is a CSS-wide keyword or `default`, which no `<custom-ident>` may be (CSS
/// Values 4 §4.2). `revert-rule`, a CSS-wide keyword of CSS Cascade 6†, is reserved too,
/// though as a value it is not in the subset.
pub fn is_reserved_ident(s: &[u32]) -> bool {
    WIDE_KEYWORDS.iter().any(|(k, _)| eq_ignore_case(s, k))
        || eq_ignore_case(s, "default")
        || eq_ignore_case(s, "revert-rule")
}

/// A longhand's specified value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Specified {
    /// A CSS-wide keyword.
    Wide(Wide),
    /// A value of the property's grammar.
    Value(Vec<Component>),
}

/// One longhand and its value, as a declaration sets it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declared {
    /// The longhand.
    pub property: Longhand,
    /// Its value.
    pub value: Specified,
}

/// A property of the subset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Property {
    /// A longhand.
    Longhand(Longhand),
    /// A shorthand.
    Shorthand(Shorthand),
}

/// The property named `name`, ASCII case-insensitively.
pub fn property(name: &[u32]) -> Option<Property> {
    lookup(LONGHANDS, name)
        .or_else(|| lookup(ALIASES, name))
        .map(Property::Longhand)
        .or_else(|| lookup(SHORTHANDS, name).map(Property::Shorthand))
}

impl Property {
    /// The longhands the property sets.
    pub fn longhands(self) -> Vec<Longhand> {
        match self {
            Property::Longhand(l) => vec![l],
            Property::Shorthand(s) => s.longhands().to_vec(),
        }
    }
}

/// The value of `p` read from all of `src`, as the longhands it sets; `None` if `src` is
/// not a value of `p`'s grammar, so a declaration of it is dropped.
pub fn parse_items(p: Property, src: Src<'_>, quirks: bool) -> Option<Vec<Declared>> {
    let mut c = Cursor::new(src);
    // A CSS-wide keyword must be the whole value (CSS Values 4 §4.1.1†).
    if let Some(w) = grammar::whole(c, |c| c.ident().and_then(|s| lookup(WIDE_KEYWORDS, s))) {
        return Some(
            p.longhands()
                .into_iter()
                .map(|property| Declared {
                    property,
                    value: Specified::Wide(w),
                })
                .collect(),
        );
    }
    let out = match p {
        Property::Longhand(l) => vec![Declared {
            property: l,
            value: Specified::Value(l.parse(&mut c, quirks)?),
        }],
        Property::Shorthand(s) => s
            .parse(&mut c, quirks)?
            .into_iter()
            .zip(s.longhands().iter().copied())
            .map(|(v, property)| Declared {
                property,
                value: Specified::Value(v),
            })
            .collect(),
    };
    c.at_end().then_some(out)
}

/// The declarations a declaration `name: value` sets, for a property of the subset; `None`
/// if the property is unknown or the value is invalid for it. `value` is the declaration's
/// value as code points, without `!important` (which `clazel-css` takes off).
pub fn parse(name: &[u32], value: &[u32], quirks: bool) -> Option<Vec<Declared>> {
    let p = property(name)?;
    let v = Values::parse(value)?;
    parse_items(p, v.src(), quirks)
}

/// CSSOM's `getPropertyValue(name)` of a declaration block holding `block` (the last
/// declaration of a longhand wins): a longhand's value serialized, or a shorthand's from
/// its longhands; the empty string if a longhand is missing or no value of the shorthand
/// gives what they hold (CSSOM §6.6.1† "serialize a CSS declaration block" steps for
/// shorthands, "getPropertyValue()" steps 1 and 2).
pub fn get_property_value(block: &[Declared], name: &[u32]) -> String {
    let Some(p) = property(name) else {
        return String::new();
    };
    let value_of = |l: Longhand| {
        block
            .iter()
            .rev()
            .find(|d| d.property == l)
            .map(|d| &d.value)
    };
    match p {
        Property::Longhand(l) => match value_of(l) {
            None => String::new(),
            Some(Specified::Wide(w)) => w.name().to_owned(),
            Some(Specified::Value(v)) => to_string(v),
        },
        Property::Shorthand(s) => {
            let mut values = Vec::new();
            let mut wide = Vec::new();
            for &l in s.longhands() {
                match value_of(l) {
                    None => return String::new(),
                    Some(Specified::Wide(w)) => wide.push(*w),
                    Some(Specified::Value(v)) => values.push(v.clone()),
                }
            }
            // All one CSS-wide keyword: that keyword; a mixture: nothing.
            if let Some(&w) = wide.first() {
                return if values.is_empty() && wide.iter().all(|x| *x == w) {
                    w.name().to_owned()
                } else {
                    String::new()
                };
            }
            s.serialize(&values).unwrap_or_default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    /// `e.style[p] = v; e.style.getPropertyValue(p)`.
    fn set(p: &str, v: &str, quirks: bool) -> String {
        let block = parse(&u(p), &u(v), quirks).unwrap_or_default();
        get_property_value(&block, &u(p))
    }

    #[test]
    fn longhands_and_shorthands() {
        let cases = [
            ("margin", "10px 20% auto", "10px 20% auto"),
            ("margin", "1px 1px 1px 1px", "1px"),
            ("margin", "1px 2px 1px 2px", "1px 2px"),
            ("margin-top", "-1.5em", "-1.5em"),
            ("padding", "-1px", ""),
            ("width", "0", "0px"),
            ("border", "green double thin", "thin double green"),
            ("border-top", "thin", "thin"),
            ("border-bottom", "green", "green"),
            (
                "text-decoration",
                "rgba(10, 20, 30, 0.4) dotted",
                "dotted rgba(10, 20, 30, 0.4)",
            ),
            ("text-decoration", "solid", "none"),
            ("text-decoration-line", "blink underline", "underline blink"),
            (
                "text-indent",
                "each-line hanging 3px",
                "3px hanging each-line",
            ),
            (
                "font-family",
                "\"New Century Schoolbook\", serif",
                "New Century Schoolbook, serif",
            ),
            (
                "font-family",
                "Verdana, Geneva, sans-serif",
                "Verdana, Geneva, sans-serif",
            ),
            ("font", "bold 10pt / 1.2 Verdana", "bold 10pt / 1.2 Verdana"),
            (
                "font",
                "italic small-caps 12px serif",
                "italic small-caps 12px serif",
            ),
            ("overflow", "hidden hidden", "hidden"),
            ("background", "#ff6600", "rgb(255, 102, 0)"),
            (
                "background",
                "url(a.png) no-repeat",
                "url(\"a.png\") no-repeat",
            ),
            ("margin", "inherit", "inherit"),
            ("Color", "RED", "red"),
            ("word-wrap", "break-word", "break-word"),
            (
                "transform",
                "rotate(45deg) translateX(1px)",
                "rotate(45deg) translateX(1px)",
            ),
            ("display", "inline-block", "inline-block"),
            (
                "background-image",
                "linear-gradient(to right, red, blue 50%)",
                "linear-gradient(to right, red, blue 50%)",
            ),
        ];
        for (p, v, want) in cases {
            assert_eq!(set(p, v, false), want, "{p}: {v}");
        }
    }

    #[test]
    fn quirks() {
        assert_eq!(set("margin", "1 2px", true), "1px 2px");
        assert_eq!(set("margin", "1 2px", false), "");
        assert_eq!(set("color", "abc", true), "rgb(170, 187, 204)");
        assert_eq!(set("border", "1px solid abc", true), "");
        assert_eq!(set("font", "normal normal normal 40 sans-serif", true), "");
        assert_eq!(set("line-height", "2", true), "2");
    }

    #[test]
    fn unknown_and_invalid() {
        assert_eq!(set("-webkit-box-sizing", "border-box", false), "");
        assert_eq!(set("width", "calc(1px)", false), "");
        assert_eq!(set("margin", "1px 2px 3px 4px 5px", false), "");
        assert_eq!(set("margin", "inherit 1px", false), "");
    }
}
