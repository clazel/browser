//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Each harness runs one operation on **every** input within the bound in its comment (a
//! symbolic array and a symbolic length, or a symbolic state). Kani checks that no panic,
//! arithmetic overflow or read outside a slice is reachable, and its unwinding assertions
//! check that every loop finishes within the stated bound. The bounds are also in the
//! crate's README.
//!
//! The harnesses are cut along the grammars' structure, so that each fits a CI runner:
//!
//! - **The cursor steps** ([`cursor_bump_any_4`] and the rest), from any cursor over any
//!   four items: every step that consumes moves the cursor forward and stays inside the
//!   list it reads, and a function's argument cursor lies inside its parent. This is the
//!   loop body of every grammar: each loop over items is written
//!   `for _ in 0..c.budget()` and consumes an item per iteration or stops, so it never needs
//!   more than `items.len() + 1` iterations.
//! - **The keyword tables**: a lookup's loop body on any string up to the longest name
//!   ([`table_lookup_any_20`]), and the units, CSS-wide keywords and cursor keywords as
//!   whole tables.
//! - **The value types** (`<length>`, `<percentage>`, `<number>`, `<angle>`, `<url>`,
//!   `<string>`, `<custom-ident>`, `<color>`, the arguments of `rgb()` and `hsl()`, and the
//!   colour quirks), each on any items up to the count in its name, over any [`TEXT`]
//!   code points.
//! - **The numeric conversions**: from a token's digits, to 1/64 px, to degrees, HSL to
//!   RGB.
//!
//! Not done, each exceeding 20 minutes (or 12 GB) locally even at small bounds, so covered
//! only by the unit tests and the WPT conformance test:
//!
//! - the whole-declaration harnesses (each longhand's and shorthand's grammar on any
//!   sequence of items): four of them ran 5 h 48 min at one item without finishing, and
//!   `display` alone took 329 s at two items. The grammars are built only from the steps
//!   and value types above, with the workspace lints (no indexing, no unchecked
//!   arithmetic, no `unwrap`, no `panic`) on every line;
//! - the named-colour and counter-style tables run whole over a symbolic string, and
//!   `<color>` on an identifier (the named-colour lookup);
//! - `rgb()` with seven items (legacy syntax with alpha); `hsl()` with seven verifies in
//!   18 minutes at 14 GB, beyond a CI runner;
//! - `Values::from_rows`, the adapter from `clazel-css`'s rows: it calls the tokenizer,
//!   and even one row over one code point exceeds 5 minutes. The tokenizer and parser are
//!   proven by Verus in `clazel-css`;
//! - serialization: formatting a `String` is beyond CBMC at useful sizes. The
//!   conformance test round-trips every case.

use super::color::{from_hex, hsl, hsl_to_rgb, parse_color, quirky_ident, quirky_number, rgb};
use super::grammar::{self, Range};
use super::items::{Cursor, Item, Src, eq_ignore_case, keyword_in, lookup};
use super::longhand::{CURSORS, LINE_STYLES};
use super::number::{
    ANGLE_UNITS, Angle, LENGTH_UNITS, Length, MAX_NUM, MAX_PX64, Num, SCALE, degrees,
    percentage_px64, to_px64,
};
use super::{WIDE_KEYWORDS, is_reserved_ident};

/// The code points of text the value-type harnesses read.
pub const TEXT: usize = 3;
/// The most code points of a number part or an exponent part.
pub const DIGITS: usize = 4;

/// A symbolic string of at most `N` code points.
fn string<const N: usize>(data: &[u32; N]) -> &[u32] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    data.get(..len).unwrap_or_default()
}

/// A cursor at any position of any list of at most `N` items over `text`, as
/// [`Cursor::new`] and [`Cursor::function`] leave one: `pos <= end <= items.len()`.
fn any_cursor<'a, const N: usize>(text: &'a [u32], items: &'a [Item; N]) -> Cursor<'a> {
    let items = string_of(items);
    let end: usize = kani::any();
    kani::assume(end <= items.len());
    let pos: usize = kani::any();
    kani::assume(pos <= end);
    Cursor {
        src: Src { text, items },
        pos,
        end,
    }
}

/// A symbolic prefix of `items`.
fn string_of<const N: usize>(items: &[Item; N]) -> &[Item] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    items.get(..len).unwrap_or_default()
}

/// Every list of at most `N` items over any [`TEXT`] code points, given to `f` from its
/// start. The text has its full length: spans are arbitrary, so every shorter string is a
/// span of it. The item count is a loop with a constant bound, so every list the grammar
/// sees has a length its loops are unrolled to.
fn with_any_items<const N: usize>(f: impl Fn(Cursor<'_>)) {
    let text: [u32; TEXT] = kani::any();
    let items: [Item; N] = kani::any();
    for n in 0..=N {
        f(Cursor::new(Src {
            text: &text,
            items: items.get(..n).unwrap_or_default(),
        }));
    }
}

// The cursor steps.

/// [`Cursor::bump`] from any cursor over any 4 items: it moves forward, within the list.
#[kani::proof]
fn cursor_bump_any_4() {
    let text: [u32; TEXT] = kani::any();
    let items: [Item; 4] = kani::any();
    let mut c = any_cursor(&text, &items);
    let (pos, end) = (c.pos, c.end);
    if c.bump().is_some() {
        assert!(c.pos > pos && c.pos <= end && c.end == end);
    } else {
        assert!(c.pos == pos && pos == end);
    }
}

/// [`Cursor::function`] from any cursor over any 4 items: it moves forward, within the
/// list, and the argument cursor is a cursor inside what it skipped.
#[kani::proof]
fn cursor_function_any_4() {
    let text: [u32; TEXT] = kani::any();
    let items: [Item; 4] = kani::any();
    let mut c = any_cursor(&text, &items);
    let (pos, end) = (c.pos, c.end);
    if let Some((_, args)) = c.function() {
        assert!(c.pos > pos && c.pos <= end);
        assert!(args.pos == pos.saturating_add(1) && args.pos <= args.end && args.end == c.pos);
        assert!(args.end <= args.src.items.len());
    } else {
        assert!(c.pos == pos);
    }
}

/// The one-item steps ([`Cursor::ident`], [`Cursor::keyword`], [`Cursor::comma`],
/// [`Cursor::delim`]) from any cursor over any 4 items: each consumes exactly one item
/// or none.
#[kani::proof]
fn cursor_one_item_steps_any_4() {
    let text: [u32; TEXT] = kani::any();
    let items: [Item; 4] = kani::any();
    let c0 = any_cursor(&text, &items);
    let step = |moved: bool, c: &Cursor<'_>| {
        if moved {
            assert!(c.pos == c0.pos.saturating_add(1) && c.pos <= c0.end);
        } else {
            assert!(c.pos == c0.pos);
        }
    };
    let mut c = c0;
    let moved = c.ident().is_some();
    step(moved, &c);
    let mut c = c0;
    let moved = c.keyword(LINE_STYLES).is_some();
    step(moved, &c);
    let mut c = c0;
    let moved = c.comma();
    step(moved, &c);
    let mut c = c0;
    let moved = c.delim(kani::any());
    step(moved, &c);
}

// The keyword tables, each on any string up to its longest name.

/// A table lookup's loop body on any string up to 20 code points (the longest name of
/// any table): the comparison with a name of each length class, as every table runs it.
/// The large tables themselves (148 named colours, 54 counter styles) are each a
/// constant-bound loop of this body; run over a symbolic string they do not fit (the named
/// colours exceed 20 minutes), so their contents are checked by the unit tests.
#[kani::proof]
#[kani::unwind(22)]
fn table_lookup_any_20() {
    let data: [u32; 20] = kani::any();
    let s = string(&data);
    let _ = keyword_in(&["lightgoldenrodyellow", "disc", ""], s);
    let _ = eq_ignore_case(s, "cjk-earthly-branch");
}

/// The cursor keywords (longest name: 13 code points).
#[kani::proof]
#[kani::unwind(40)]
fn cursors_any_13() {
    let data: [u32; 13] = kani::any();
    let _ = keyword_in(CURSORS, string(&data));
}

/// The units and the CSS-wide keywords (longest: 12 code points).
#[kani::proof]
#[kani::unwind(14)]
fn units_and_wide_keywords_any_12() {
    let data: [u32; 12] = kani::any();
    let s = string(&data);
    let _ = lookup(LENGTH_UNITS, s);
    let _ = lookup(ANGLE_UNITS, s);
    let _ = lookup(WIDE_KEYWORDS, s);
    let _ = is_reserved_ident(s);
}

// The value types, each on any items up to what its grammar reads.

/// `<length>` and `<length-percentage>`, in any range and quirks or not, on any one item.
#[kani::proof]
#[kani::unwind(14)]
fn length_any_1() {
    with_any_items::<1>(|c| {
        let mut c1 = c;
        let _ = grammar::length(&mut c1, kani::any(), kani::any());
        let mut c2 = c;
        let _ = grammar::length_percentage(&mut c2, kani::any(), kani::any());
    });
}

/// `<percentage>`, `<number>` and `<angle>` on any one item.
#[kani::proof]
#[kani::unwind(14)]
fn number_percentage_angle_any_1() {
    with_any_items::<1>(|c| {
        let range = if kani::any() {
            Range::All
        } else {
            Range::NonNegative
        };
        let mut c1 = c;
        let _ = grammar::percentage(&mut c1, range);
        let mut c2 = c;
        let _ = grammar::number(&mut c2, range);
        let mut c3 = c;
        let _ = grammar::angle(&mut c3, kani::any());
    });
}

/// `<url>`, `<string>` and `<custom-ident>` on any two items (`url(` and its string).
#[kani::proof]
#[kani::unwind(14)]
fn url_string_ident_any_2() {
    with_any_items::<2>(|c| {
        let mut c1 = c;
        let _ = grammar::url(&mut c1);
        let mut c2 = c;
        let _ = grammar::string(&mut c2);
        let mut c3 = c;
        let _ = grammar::custom_ident(&mut c3, &["none"]);
    });
}

/// `<color>` on any one item but an identifier, over any [`TEXT`] code points, quirks or
/// not: hex, the quirky number and dimension, and a colour function with no arguments.
/// An identifier goes to the named-colour table (see [`table_lookup_any_20`]) and the
/// quirky ident ([`hex_any_8`]); with it the harness exceeds 20 minutes.
#[kani::proof]
#[kani::unwind(10)]
fn color_any_1() {
    let text: [u32; TEXT] = kani::any();
    let item: Item = kani::any();
    kani::assume(!matches!(item, Item::Ident(_)));
    let items = [item];
    for n in 0..=1 {
        let mut c = Cursor::new(Src {
            text: &text,
            items: items.get(..n).unwrap_or_default(),
        });
        let _ = parse_color(&mut c, kani::any());
    }
}

/// `rgb()` and `rgba()`'s arguments: any 5 items (`r, g, b` or `r g b / a`). Seven items,
/// the legacy form with alpha, exceed 20 minutes.
#[kani::proof]
#[kani::unwind(8)]
fn rgb_args_any_5() {
    with_any_items::<5>(|c| {
        let _ = rgb(c);
    });
}

/// `hsl()` and `hsla()`'s arguments: any 5 items. Seven items verify locally in 18 minutes
/// at 14 GB, beyond a CI runner.
#[kani::proof]
#[kani::unwind(8)]
fn hsl_args_any_5() {
    with_any_items::<5>(|c| {
        let _ = hsl(c);
    });
}

// The numeric conversions.

/// A token's value, from any number part and exponent part of up to [`DIGITS`] code
/// points: within ±[`MAX_NUM`].
#[kani::proof]
#[kani::unwind(6)]
fn number_conversion_clamps() {
    let part: [u32; DIGITS] = kani::any();
    let exp: [u32; DIGITS] = kani::any();
    let n = Num::from_parts(string(&part), string(&exp), kani::any());
    assert!(n.millionths <= MAX_NUM && n.millionths >= -MAX_NUM);
}

/// Any length, in any unit, at any font sizes, and any percentage of any basis, to 1/64 px:
/// within ±[`MAX_PX64`].
#[kani::proof]
fn lengths_convert_and_clamp() {
    let l: Length = kani::any();
    let px = to_px64(l, kani::any(), kani::any());
    assert!(px <= MAX_PX64 && px >= -MAX_PX64);
    let p = percentage_px64(kani::any(), kani::any());
    assert!(p <= MAX_PX64 && p >= -MAX_PX64);
}

/// Any angle to degrees: within ±[`MAX_NUM`].
#[kani::proof]
fn angles_convert_and_clamp() {
    let a: Angle = kani::any();
    let d = degrees(a);
    assert!(d <= MAX_NUM && d >= -MAX_NUM);
}

/// HSL to RGB on any hue, saturation and lightness, in range or not.
#[kani::proof]
fn hsl_converts() {
    let h6: i64 = kani::any();
    kani::assume(h6 >= 0 && h6 < 6 * SCALE);
    let s: i64 = kani::any();
    kani::assume(s >= 0 && s <= SCALE);
    let l: i64 = kani::any();
    kani::assume(l >= 0 && l <= SCALE);
    let _ = hsl_to_rgb(h6, s, l);
    let _ = hsl_to_rgb(kani::any(), kani::any(), kani::any());
}
