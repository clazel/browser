//! Kani harnesses for white space processing and line breaking. Compiled
//! only under `cargo kani`.
//!
//! Most harnesses check **one step from any state**: any value of the
//! step's state that satisfies its invariant (`state.rs`), and any next
//! input. Kani checks that no panic, arithmetic overflow or out-of-bounds
//! index is reachable, the properties asserted, and that the step keeps the
//! invariant. The start state satisfies the invariant (asserted too), so by
//! induction every state a driver reaches on a text of **any length** does,
//! and every step it takes has the checked properties. A few harnesses run
//! a whole driver on bounded inputs, as a cross-check that the driver calls
//! its step correctly. Bounds, times and memory are in the crate README.
//!
//! Proved for every length (step harnesses):
//!
//! - UAX #14 ([`super::uax14::step`], [`uax14_step_any`]): LB2 at sot, LB4
//!   after BK, LB7 before SP and ZW, LB9 inside an absorbed sequence, a
//!   mandatory break only after BK, CR, LF or NL, and the invariant kept.
//!   The rules with unbounded left context (LB8's `ZW SP*`, LB14 to LB17's
//!   `SP*`, LB25's `NU ( SY | IS )*`, LB30a's `(RI RI)*`, LB9's `X (CM |
//!   ZWJ)*`) are summarised in the state, so they are covered at every
//!   length; the right context is at most two items, passed as arguments.
//! - Phase I ([`super::collapse::step`], [`collapse_step_any`]): at most one
//!   unit added per character, a retraction only of a pending space, no
//!   collapsible space kept right after another (bidi formatting characters
//!   aside), and the invariant kept.
//! - The CSS opportunity at a position ([`super::wrap::wrap_at`],
//!   [`wrap_at_any`]): forced exactly where UAX #14 is mandatory (or at the
//!   end), and nothing soft or emergency where neither unit's `white-space`
//!   wraps. It reads only the two units around the position.
//! - Measuring ([`super::state::Measure::add`], [`measure_add_any`]) and
//!   choosing lines ([`super::lines::fit_step`], [`fit_step_any`]): a line
//!   ends after at least one unit and at most at the unit added, and a line
//!   that goes on keeps the invariant.
//! - Tab stops ([`super::lines::tab_advance`], [`tab_advance_any`]): any
//!   values.
//!
//! Checked on bounded inputs only (driver harnesses):
//!
//! - [`super::uax14::breaks_with_rules`] against `reference.rs`'s reading
//!   of the rules on any 2 characters' properties
//!   ([`uax14_driver_matches_reference_2`]);
//! - the intrinsic sizes' driver (`widest`, over [`Measure::add`]) on any
//!   3 units ([`intrinsic_any_3`]);
//! - Phase II ([`super::lines::trim`], [`trim_any_3`]), which walks back
//!   from a line's end rather than stepping over a state.
//!
//! What is not covered, and why:
//!
//! - **The character tables** ([`super::classes`]): a bisection over
//!   thousands of ranges, for which a symbolic character makes the formula
//!   too large; the harnesses take the properties as arbitrary values
//!   instead, so they hold whatever the tables say. The tables are checked
//!   by `tests/conformance_linebreak.rs` (every line of `LineBreakTest.txt`).
//! - **That the steps compute exactly the rules** beyond the asserted
//!   properties: the step and `reference.rs`'s reading are compared by the
//!   unit tests (every short string over an alphabet of every class, and
//!   random long ones) and by the bounded driver harness, not for every
//!   length.
//! - **The Phase I and line-choosing drivers** ([`super::collapse::collapse_raw`],
//!   [`super::lines::break_lines`]) as whole loops: harnesses running them
//!   on any 3 and then any 2 inputs both exceeded the 8 GB cap and were
//!   removed. Their steps are covered for every length; the drivers only
//!   feed units to the steps, apply Phase I's retraction and start a new
//!   line at each end, and are covered by the unit tests (Phase I against
//!   `reference.rs` on every sequence of up to 4 over 30 symbols and on
//!   random long ones; lines by CSS Text 3's own examples).
//! - **[`super::collapse::collapse`]'s reading of `&str`** into classified
//!   characters, which has no arithmetic beyond `char_indices`.

use super::classes::{Lb, Props};
use super::collapse::{self, Kind, Raw, Unit};
use super::lines::{fit_step, max_content, min_content, tab_advance, trim};
use super::reference;
use super::state::{BreakState, CollapseState, Emit, Fit, FitState, Last, Measure, Side};
use super::uax14::{self, Break, Rule, breaks_with_rules};
use super::wrap::{Wrap, wrap_at, wraps};

/// The first `len` values of `all`, for any `len` up to `N`: any sequence
/// of at most `N` values when `all` is arbitrary. (A slice of a fixed array
/// keeps the formula far smaller than building a `Vec`.)
fn prefix<T, const N: usize>(all: &[T; N]) -> &[T] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    all.get(..len).unwrap_or(&[])
}

/// LB9's "X".
fn is_base(c: Lb) -> bool {
    !matches!(c, Lb::BK | Lb::CR | Lb::LF | Lb::NL | Lb::SP | Lb::ZW)
}

/// One UAX #14 step from any state satisfying the invariant, with any next
/// character and any right context.
#[kani::proof]
fn uax14_step_any() {
    assert!(BreakState::START.invariant());
    let state: BreakState = kani::any();
    kani::assume(state.invariant());
    let c: Props = kani::any();
    let next: Option<Props> = kani::any();
    let after_next: Option<Props> = kani::any();
    let (b, _, after) = uax14::step(&state, c, next, after_next);
    assert!(after.invariant());
    let before = state.raw_prev;
    // LB2: "sot ×".
    if state.a.is_none() {
        assert!(b == Break::Prohibited);
    }
    // LB4: "BK !".
    if before == Some(Lb::BK) {
        assert!(b == Break::Mandatory);
    }
    // LB7: "× SP", "× ZW", unless LB4 or LB5 made it mandatory.
    if matches!(c.class, Lb::SP | Lb::ZW) {
        assert!(b != Break::Allowed);
    }
    // LB9: no break inside "X (CM | ZWJ)*".
    if matches!(c.class, Lb::CM | Lb::ZWJ) && before.is_some_and(is_base) {
        assert!(b == Break::Prohibited);
    }
    // Mandatory breaks only after BK, CR (not before LF), LF and NL.
    if b == Break::Mandatory {
        assert!(matches!(before, Some(Lb::BK | Lb::CR | Lb::LF | Lb::NL)));
    }
}

/// The UAX #14 driver against the reference reading, on any 2 characters.
#[kani::proof]
#[kani::unwind(4)]
fn uax14_driver_matches_reference_2() {
    let text: [Props; 2] = kani::any();
    let ours = breaks_with_rules(&text);
    let theirs = reference::breaks_with_rules(&text);
    assert!(ours.len() == 2 && theirs.len() == 2);
    assert!(ours.first() == theirs.first());
    assert!(ours.get(1) == theirs.get(1));
}

/// Whether `raw` is one `collapse::classify` gives (it never classifies a
/// character as a space or tab kind after Phase I).
fn classifiable(raw: Raw) -> bool {
    !matches!(
        raw,
        Raw::Other(Kind::CollapsibleSpace | Kind::PreservedSpace | Kind::PreservedTab)
    )
}

/// One Phase I step from any state satisfying the invariant, with any next
/// character and any `white-space`.
#[kani::proof]
fn collapse_step_any() {
    assert!(CollapseState::START.invariant());
    let state: CollapseState = kani::any();
    kani::assume(state.invariant());
    let raw: Raw = kani::any();
    kani::assume(classifiable(raw));
    let ws = kani::any();
    let (emit, after) = collapse::step(&state, raw, ws);
    assert!(after.invariant());
    // The last unit kept before this character, once any retraction is done.
    let before = match emit {
        Emit::Retract | Emit::RetractAndPush(_) => {
            // Only a pending space is retracted.
            assert!(state.pending.is_some());
            state.pending.unwrap_or(Last::Other)
        }
        _ => state.last,
    };
    // No collapsible space right after another one (step 4).
    if let Emit::Push(Kind::CollapsibleSpace) | Emit::RetractAndPush(Kind::CollapsibleSpace) = emit
    {
        assert!(!matches!(before, Last::Space | Last::ConvertedBreak));
    }
}

/// The CSS opportunity at any position: any two units around it and any
/// UAX #14 decision there.
#[kani::proof]
fn wrap_at_any() {
    let here: Side = kani::any();
    let next: Option<Side> = kani::any();
    let b: Break = kani::any();
    let rule: Rule = kani::any();
    let w = wrap_at(&here, next.as_ref(), b, rule);
    // Forced exactly where UAX #14 is mandatory, or at the end.
    assert!((w == Wrap::Forced) == (b == Break::Mandatory || next.is_none()));
    // Where neither unit's white-space wraps, only forced breaks.
    if let Some(n) = next
        && !wraps(here.unit.style.white_space)
        && !wraps(n.unit.style.white_space)
    {
        assert!(matches!(w, Wrap::None | Wrap::Forced));
    }
}

/// Measuring: any measure, any unit, any advance.
#[kani::proof]
fn measure_add_any() {
    let m: Measure = kani::any();
    let u: Unit = kani::any();
    let advance: i32 = kani::any();
    let after = m.add(&u, advance);
    if !m.takes_width(&u) {
        assert!(after == m);
    } else {
        assert!(!after.leading);
    }
}

/// One step of choosing lines from any state satisfying the invariant.
#[kani::proof]
fn fit_step_any() {
    let i: usize = kani::any();
    kani::assume(i < usize::MAX);
    assert!(FitState::new(i).invariant(i));
    let state: FitState = kani::any();
    kani::assume(state.invariant(i));
    let u: Unit = kani::any();
    let advance: i32 = kani::any();
    let wrap: Wrap = kani::any();
    let available: i32 = kani::any();
    match fit_step(&state, i, &u, advance, wrap, available) {
        // The line holds at least one unit and ends at most after unit `i`.
        Fit::End { end, .. } => assert!(state.start < end && end <= i.saturating_add(1)),
        // It goes on from the same start, keeping the invariant.
        Fit::Continue(next) => {
            assert!(next.start == state.start);
            assert!(next.invariant(i.saturating_add(1)));
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
