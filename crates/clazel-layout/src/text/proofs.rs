//! Kani harnesses for white space processing and line breaking. Compiled
//! only under `cargo kani`.
//!
//! Each harness runs one operation on **any** input within a stated bound
//! (symbolic values, symbolic lengths up to a fixed maximum). Kani checks
//! that no panic, arithmetic overflow or out-of-bounds index is reachable,
//! and its unwinding assertions check that every loop finishes within the
//! bound; the harnesses also assert properties the standards state. Bounds
//! are in each harness's name and comment, and in the crate README with the
//! time and memory each took.
//!
//! What is covered:
//!
//! - UAX #14's rules ([`super::uax14::break_at`], the decision
//!   `breaks_with_rules` makes at each position) on any 2 characters'
//!   properties (any class, any flags) at both positions, and on any 3 at
//!   each inner position: LB3 at eot, LB4 after BK, LB7 before SP and ZW,
//!   LB9 inside an absorbed sequence, and a mandatory break only where LB3,
//!   LB4 or LB5 put one. (All positions of 3 characters in one harness
//!   exceeded the 8 GB cap; split by position.)
//! - CSS's opportunities ([`super::wrap::wraps_from_breaks`]) on any 2 units
//!   with any properties, styles and UAX #14 decisions: one per unit,
//!   forced where UAX #14 is mandatory, and no soft or emergency one where
//!   `white-space` forbids wrapping.
//! - Phase II ([`super::lines::trim`]) on any 3 units and any bounds, and
//!   choosing lines ([`super::lines::break_lines`]) on any 3 units, any
//!   opportunities, any advances and any available width: lines cover the
//!   units in order, each non-empty, and the loop ends; the intrinsic sizes
//!   on the same.
//! - Tab stops ([`super::lines::tab_advance`]) on any values.
//!
//! What is not covered, and why:
//!
//! - **Phase I** ([`super::collapse::collapse_raw`]): a harness over any
//!   classified characters with any styles (no unit added, no two
//!   collapsible spaces next to each other) exceeded the 8 GB memory cap at
//!   4, 3 and even 2 characters, so it was removed. Phase I is covered by
//!   the unit tests; its loops index only through `get`.
//! - **The character tables** ([`super::classes`]): a bisection over
//!   thousands of ranges, for which a symbolic character makes the formula
//!   too large; the harnesses take the properties as arbitrary values
//!   instead, so they hold whatever the tables say. The tables are checked
//!   by `tests/conformance_linebreak.rs` (every line of `LineBreakTest.txt`).
//! - **[`super::collapse::collapse`]'s reading of `&str`** into classified
//!   characters, which has no arithmetic beyond `char_indices`.
//! - **Longer inputs**: every loop advances by at least one character per
//!   iteration (checked by the unwinding bounds), and every index goes
//!   through `get`; longer inputs are covered by the unit and conformance
//!   tests.

use super::classes::{Lb, Props};
use super::collapse::Unit;
use super::lines::{break_lines, max_content, min_content, tab_advance, trim};
use super::uax14::{Break, Rule, absorbed, break_at};
use super::wrap::{Wrap, wraps, wraps_from_breaks};

/// The first `len` values of `all`, for any `len` up to `N`: any sequence
/// of at most `N` values when `all` is arbitrary. (A slice of a fixed array
/// keeps the formula far smaller than building a `Vec`.)
fn prefix<T, const N: usize>(all: &[T; N]) -> &[T] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    all.get(..len).unwrap_or(&[])
}

/// The properties UAX #14 states for the decision `b` at position `i` of
/// `text` (between characters `i - 1` and `i`; eot at `text.len()`).
fn check_break(text: &[Props], i: usize, b: Break) {
    let class = |k: usize| text.get(k).map(|p| p.class);
    let before = i.checked_sub(1).and_then(class);
    if i >= text.len() {
        // LB3: "! eot".
        assert!(b == Break::Mandatory);
        return;
    }
    // LB4: "BK !".
    if before == Some(Lb::BK) {
        assert!(b == Break::Mandatory);
    }
    // LB7: "× SP", "× ZW", unless LB4 or LB5 made it mandatory.
    if matches!(class(i), Some(Lb::SP | Lb::ZW)) {
        assert!(b != Break::Allowed);
    }
    // LB9: no break inside "X (CM | ZWJ)*".
    if absorbed(text).get(i).copied().unwrap_or(false) {
        assert!(b == Break::Prohibited);
    }
    // Mandatory breaks only after BK, CR (not before LF), LF and NL.
    if b == Break::Mandatory {
        assert!(matches!(before, Some(Lb::BK | Lb::CR | Lb::LF | Lb::NL)));
    }
}

/// UAX #14 at either position of any 2 characters' properties (any
/// classes, any flags): between them, and eot.
#[kani::proof]
#[kani::unwind(4)]
fn uax14_any_2() {
    let text: [Props; 2] = kani::any();
    let i: usize = kani::any();
    kani::assume(i == 1 || i == 2);
    let (b, _) = break_at(&text, i);
    check_break(&text, i, b);
}

/// UAX #14 between the first two of any 3 characters' properties, with one
/// character of context after the position.
#[kani::proof]
#[kani::unwind(4)]
fn uax14_at_1_of_3() {
    let text: [Props; 3] = kani::any();
    let (b, _) = break_at(&text, 1);
    check_break(&text, 1, b);
}

/// UAX #14 between the last two of any 3 characters' properties, with one
/// character of context before the position.
#[kani::proof]
#[kani::unwind(4)]
fn uax14_at_2_of_3() {
    let text: [Props; 3] = kani::any();
    let (b, _) = break_at(&text, 2);
    check_break(&text, 2, b);
}

/// CSS's opportunities on any 2 units with any properties and any UAX #14
/// decisions (the CSS layer alone; the rules are the harnesses above).
#[kani::proof]
#[kani::unwind(4)]
fn wraps_any_2() {
    let units_all: [Unit; 2] = kani::any();
    let units = prefix(&units_all);
    let props: [Props; 2] = kani::any();
    let rules: [(Break, Rule); 2] = kani::any();
    let out = wraps_from_breaks(units, &props, &rules);
    assert!(out.len() == units.len());
    for (i, w) in out.iter().enumerate() {
        let here = units.get(i).map(|u| u.style.white_space);
        let next = units.get(i.saturating_add(1)).map(|u| u.style.white_space);
        // Forced exactly where UAX #14 says mandatory (or at the end).
        let mandatory = rules.get(i).is_some_and(|r| r.0 == Break::Mandatory);
        if mandatory {
            assert!(*w == Wrap::Forced);
        }
        // Where neither character's white-space wraps, only forced breaks.
        if here.is_some_and(|w| !wraps(w)) && next.is_some_and(|w| !wraps(w)) {
            assert!(matches!(w, Wrap::None | Wrap::Forced));
        }
    }
}

/// Phase II on any 3 units and any bounds. Bounds above 4 are assumed
/// away: `trim` clamps both with `min` (to the unit count and to `end`), so
/// for 3 units any larger value behaves as 4 does.
#[kani::proof]
#[kani::unwind(5)]
fn trim_any_3() {
    let units_all: [Unit; 3] = kani::any();
    let units = prefix(&units_all);
    let start: usize = kani::any();
    let end: usize = kani::any();
    kani::assume(start <= 4 && end <= 4);
    let forced: bool = kani::any();
    let t = trim(units, start, end, forced);
    assert!(t.start <= t.hang && t.hang <= t.end && t.end <= units.len());
}

/// Choosing lines on any 3 units, opportunities, advances and width.
#[kani::proof]
#[kani::unwind(5)]
fn break_lines_any_3() {
    let units_all: [Unit; 3] = kani::any();
    let units = prefix(&units_all);
    let wraps_all: [Wrap; 3] = kani::any();
    let wraps = prefix(&wraps_all);
    let widths: [i32; 3] = kani::any();
    let available: i32 = kani::any();
    let lines = break_lines(units, wraps, available, |i, _| {
        widths.get(i).copied().unwrap_or(0)
    });
    let mut next = 0;
    for l in &lines {
        assert!(l.start == next && l.start < l.end);
        next = l.end;
    }
    assert!(next == units.len());
}

/// The intrinsic sizes on any 3 units, opportunities and advances.
#[kani::proof]
#[kani::unwind(5)]
fn intrinsic_any_3() {
    let units_all: [Unit; 3] = kani::any();
    let units = prefix(&units_all);
    let wraps_all: [Wrap; 3] = kani::any();
    let wraps = prefix(&wraps_all);
    let widths: [i32; 3] = kani::any();
    let w = |i: usize, _: i32| widths.get(i).copied().unwrap_or(0);
    let _ = min_content(units, wraps, w);
    let _ = max_content(units, wraps, w);
}

/// Tab stops on any pen, tab size and half `ch`.
#[kani::proof]
fn tab_advance_any() {
    let pen: i32 = kani::any();
    let tab: i32 = kani::any();
    let half: i32 = kani::any();
    let d = tab_advance(pen, tab, half);
    assert!(d >= 0);
    if tab > 0 {
        // At most two tab stops away.
        assert!(i64::from(d) <= i64::from(tab).saturating_mul(2));
    } else {
        assert!(d == 0);
    }
}
