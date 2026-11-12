//! Kani harnesses (Tier 1) for the cascade. Compiled only under `cargo kani`.
//!
//! Each harness runs one operation on **every** input within the bound in its name and
//! comment. Kani checks that no panic, arithmetic overflow or read outside a slice is
//! reachable, and its unwinding assertions that every loop ends within the bound; the
//! harnesses also assert what the operation is for. The bounds, times and peak memory are in
//! the crate's README.
//!
//! - **The sort order** ([`priority_is_the_sort_order`]): §6.1's order on priorities is the
//!   lexicographic order of its criteria. The sort itself is the standard library's
//!   `sort_by_key` on that order; a harness running it on any four candidates was stopped
//!   at the 20-minute cap (7.8 GB), and was removed.
//! - **The cascaded value** ([`cascaded_any_4`]): on any four candidates, sorted, the winner
//!   is in range, is never `revert` or `revert-layer`, and is the last candidate when no
//!   candidate rolls back.
//! - **The computed values** ([`font_size_any`], [`font_weight_any`], [`length_any`],
//!   [`snap_any`]): the conversions to 1/64 px on any value, unit and font sizes.
//! - **The legacy microsyntaxes** ([`integer_any_6`], [`dimension_any_6`],
//!   [`legacy_font_size_any_6`]) on any string up to six code points.
//!
//! Not done (see the README): the walk, [`super::preorder`]: every harness of it exceeded
//! the local 8 GB cap, down to three nodes of at most one child each (11 GB in 31 s), its
//! allocations being sized by a symbolic node count; its order and termination on real
//! trees are checked by the unit test and the golden test (1,761 documents), and its loop
//! is bounded by the node count by construction. `cascade` itself, which parses the user agent style sheet with
//! `clazel-css`'s tokenizer (too slow under Kani even at one code point, as in `values/`) and
//! matches selectors through `clazel-selectors` (proven by Verus there); `compute` on a
//! whole element's cascaded values; the presentational hints and the prose rules, which read
//! a `clazel-dom` arena; [`super::legacy::legacy_color`], whose named-colour lookup is the
//! table `values/` could not run whole either, and whose digit steps (which build, pad and
//! cut a vector) exceeded 8 GB locally at six code points (127 s) and at three (46 s); and
//! the logical property mapping, which calls `values/`' grammars.

use super::compute::{font_size, font_weight, snap_border_width};
use super::legacy::{Dimension, MAX_INT, dimension, integer, legacy_font_size};
use super::sort::{Candidate, Priority, cascaded};
use crate::values::Wide;
use crate::values::component::Component;
use crate::values::number::{Length, MAX_PX64, Num, SCALE, to_px64};

/// A symbolic string of at most `N` code points.
fn string<const N: usize>(data: &[u32; N]) -> &[u32] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    data.get(..len).unwrap_or_default()
}

/// §6.1: priorities compare by level, then element-attachment, then specificity, then order.
#[kani::proof]
fn priority_is_the_sort_order() {
    let x: Priority = kani::any();
    let y: Priority = kani::any();
    let key = |p: Priority| {
        (
            p.level,
            p.attached,
            (p.specificity.a, p.specificity.b, p.specificity.c),
            p.order,
        )
    };
    assert!(x.cmp(&y) == key(x).cmp(&key(y)));
}

/// [`cascaded`] on any four candidates in sorted order: the winner is in range and never a
/// rollback keyword; with no rollback keyword among them, it is the greatest.
#[kani::proof]
#[kani::unwind(6)]
fn cascaded_any_4() {
    let list: [Candidate; 4] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 4);
    let part = list.get(..len).unwrap_or_default();
    for i in 1..len {
        if let (Some(a), Some(b)) = (part.get(i - 1), part.get(i)) {
            kani::assume(a.priority <= b.priority);
        }
    }
    let rolls_back = |c: &Candidate| matches!(c.wide, Some(Wide::Revert | Wide::RevertLayer));
    match cascaded(part) {
        Some(i) => {
            let c = part.get(i);
            assert!(c.is_some());
            assert!(!c.is_some_and(rolls_back));
        }
        None => assert!(part.iter().any(rolls_back) || part.is_empty()),
    }
    if !part.iter().any(rolls_back) && len > 0 {
        assert!(cascaded(part) == Some(len - 1));
    }
}

/// `font-size` from each keyword of its grammar, any length and any percentage, with any
/// parent and root sizes: within `0 ..= MAX_PX64`. The keywords are taken one by one (a
/// keyword picked by a symbolic index makes every string comparison symbolic in length).
#[kani::proof]
#[kani::unwind(12)]
fn font_size_any() {
    const KEYWORDS: [&str; 10] = [
        "xx-small",
        "x-small",
        "small",
        "medium",
        "large",
        "x-large",
        "xx-large",
        "xxx-large",
        "larger",
        "smaller",
    ];
    let parent: i32 = kani::any();
    let rem: i32 = kani::any();
    kani::assume((0..=MAX_PX64).contains(&parent) && (0..=MAX_PX64).contains(&rem));
    let in_range = |v: Option<i32>| v.is_none_or(|v| (0..=MAX_PX64).contains(&v));
    for k in KEYWORDS {
        assert!(font_size(&[Component::Keyword(k)], parent, rem).is_some());
        assert!(in_range(font_size(&[Component::Keyword(k)], parent, rem)));
    }
    assert!(in_range(font_size(
        &[Component::Length(kani::any())],
        parent,
        rem
    )));
    assert!(in_range(font_size(
        &[Component::Percentage(kani::any())],
        parent,
        rem
    )));
}

/// `font-weight` from each keyword and any number, with any inherited weight in 1 to 1000:
/// a keyword gives 100, 400, 700 or 900, or keeps the inherited weight.
#[kani::proof]
#[kani::unwind(12)]
fn font_weight_any() {
    let w: i64 = kani::any();
    kani::assume((SCALE..=SCALE * 1000).contains(&w));
    let parent = Num {
        millionths: w,
        is_integer: false,
    };
    for k in ["normal", "bold", "bolder", "lighter"] {
        let v = font_weight(&[Component::Keyword(k)], parent);
        assert!(
            v.is_some_and(|v| v == parent || (100 * SCALE..=900 * SCALE).contains(&v.millionths))
        );
    }
    let n: Num = kani::any();
    assert!(font_weight(&[Component::Number(n)], parent) == Some(n));
}

/// Any length with any font sizes to 1/64 px: within ±`MAX_PX64` (the conversion every
/// computed length goes through).
#[kani::proof]
fn length_any() {
    let l: Length = kani::any();
    let em: i32 = kani::any();
    let rem: i32 = kani::any();
    kani::assume((0..=MAX_PX64).contains(&em) && (0..=MAX_PX64).contains(&rem));
    let v = to_px64(l, em, rem);
    assert!((-MAX_PX64..=MAX_PX64).contains(&v));
}

/// "Snap as a border width" on any width: zero, or a whole number of pixels, never more
/// than the width rounded up to one pixel.
#[kani::proof]
fn snap_any() {
    let w: i32 = kani::any();
    let s = snap_border_width(w);
    assert!(s >= 0 && s % 64 == 0);
    assert!(s <= w.max(64));
    assert!((w > 0) == (s > 0));
}

/// The rules for parsing integers on any string of up to six code points.
#[kani::proof]
#[kani::unwind(8)]
fn integer_any_6() {
    let data: [u32; 6] = kani::any();
    let s = string(&data);
    if let Some(v) = integer(s) {
        assert!((-MAX_INT..=MAX_INT).contains(&v));
    }
}

/// The rules for parsing dimension values on any string of up to six code points: a
/// number of at least zero.
#[kani::proof]
#[kani::unwind(8)]
fn dimension_any_6() {
    let data: [u32; 6] = kani::any();
    let s = string(&data);
    if let Some(Dimension::Length(n) | Dimension::Percentage(n)) = dimension(s) {
        assert!(n.millionths >= 0);
    }
}

/// The rules for parsing a legacy font size on any string of up to six code points.
#[kani::proof]
#[kani::unwind(8)]
fn legacy_font_size_any_6() {
    let data: [u32; 6] = kani::any();
    let s = string(&data);
    let _ = legacy_font_size(s);
}
