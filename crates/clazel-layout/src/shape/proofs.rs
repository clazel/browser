//! Kani harnesses for the shaper's arithmetic and indexing. Compiled only
//! under `cargo kani`.
//!
//! Each harness runs one operation on **any** state within a stated bound
//! (symbolic values, symbolic lengths up to a fixed maximum). Kani checks
//! that no panic, arithmetic overflow or out-of-bounds index is reachable,
//! and its unwinding assertions check that every loop finishes within the
//! bound. Bounds are in each harness's name and comment, and in the crate
//! README with the time and memory each took.
//!
//! What is covered: placing one glyph from any pen position at any size
//! and `unitsPerEm` ([`place_step_any`], the body of [`super::place`]'s
//! loop for every run length) and whole runs of up to 2 glyphs
//! ([`place_any_2`]); the pen's accumulation, clamping and scaling on any
//! values; adding any ValueRecord to any glyph; finding the next base on any
//! run of up to 6 glyphs from any index; and both kerning passes on any run
//! of up to 4 glyphs with any pair answers, including their termination.
//!
//! What is not covered, and why:
//!
//! - **Reading the face** (`cmap`, `hmtx`, `GPOS`, `kern`): that is
//!   `clazel-font`'s code, with its own harnesses (item 5.9). The passes
//!   here are checked with the pair lookups as arbitrary answers, so they
//!   hold whatever the font says.
//! - **[`super::Shaper::glyphs`]** iterates a `&str` and calls the face;
//!   its only arithmetic is none (an advance converted from `u16`), and it
//!   is covered by unit and differential tests.
//! - **Runs longer than the bounds**: the pass loops make progress by at
//!   least one glyph per iteration (checked by the unwinding bound), and
//!   their bodies index only through `get` and `get_mut`; longer runs are
//!   covered by the differential test.

use clazel_font::layout::{PairValue, ValueRecord};

use super::UnitGlyph;
use super::fixed::{advance_pen, clamp_i32, place, place_step, to_26_6};
use super::kerning::{add_value, kern_pass, next_base, pair_pass};

fn any_glyph() -> UnitGlyph {
    UnitGlyph {
        glyph: kani::any(),
        cluster: kani::any(),
        mark: kani::any(),
        x_advance: kani::any(),
        x_offset: kani::any(),
        y_offset: kani::any(),
    }
}

fn any_value() -> ValueRecord {
    ValueRecord {
        x_placement: kani::any(),
        y_placement: kani::any(),
        x_advance: kani::any(),
        y_advance: kani::any(),
    }
}

/// Any run of at most `N` glyphs.
fn any_run<const N: usize>() -> Vec<UnitGlyph> {
    let len: usize = kani::any();
    kani::assume(len <= N);
    let mut v = Vec::with_capacity(N);
    for _ in 0..len {
        v.push(any_glyph());
    }
    v
}

/// Scaling any value at any size and `unitsPerEm` never panics; the result
/// is 0 for a negative size, and clamping keeps the sign.
#[kani::proof]
fn to_26_6_any() {
    let v: i32 = kani::any();
    let size: i32 = kani::any();
    let upem: u16 = kani::any();
    let r = to_26_6(v, size, upem);
    if size < 0 || upem == 0 {
        assert!(r == 0);
    }
    if size >= 0 && v >= 0 {
        assert!(r >= 0);
    }
}

/// The pen's accumulation and clamping on any values.
#[kani::proof]
fn pen_any() {
    let pen: i64 = kani::any();
    let adv: i32 = kani::any();
    let next = advance_pen(pen, adv);
    if let Some(exact) = pen.checked_add(i64::from(adv)) {
        assert!(next == exact);
    }
    let c = clamp_i32(next);
    if let Ok(x) = i32::try_from(next) {
        assert!(c == x);
    }
}

/// One glyph placed from any pen position, at any size and `unitsPerEm`:
/// the body of `place`'s loop, for every run length.
#[kani::proof]
fn place_step_any() {
    let pen: i64 = kani::any();
    let g = any_glyph();
    let size: i32 = kani::any();
    let upem: u16 = kani::any();
    let (placed, next) = place_step(pen, &g, size, upem);
    assert!(placed.glyph == g.glyph && placed.cluster == g.cluster);
    assert!(next == advance_pen(pen, g.x_advance));
}

/// Whole runs of up to 2 glyphs at any size and `unitsPerEm`.
#[kani::proof]
#[kani::unwind(3)]
fn place_any_2() {
    let run = any_run::<2>();
    let size: i32 = kani::any();
    let upem: u16 = kani::any();
    let placed = place(&run, size, upem);
    assert!(placed.glyphs.len() == run.len());
}

/// Adding any ValueRecord to any glyph saturates, never overflows.
#[kani::proof]
fn add_value_any() {
    let mut g = any_glyph();
    let before = g;
    let v = any_value();
    add_value(&mut g, &v);
    assert!(g.glyph == before.glyph && g.mark == before.mark);
}

/// The next base after any index, in any run of up to 6 glyphs, is inside
/// the run, after the index, and not a mark.
#[kani::proof]
#[kani::unwind(7)]
fn next_base_any_6() {
    let run = any_run::<6>();
    let i: usize = kani::any();
    if let Some(j) = next_base(&run, i) {
        assert!(j > i && j < run.len());
        assert!(run.get(j).is_some_and(|g| !g.mark));
    }
}

/// The `GPOS` pair pass on any run of up to 4 glyphs, with any answer for
/// every pair: no panic, no overflow, and it terminates.
#[kani::proof]
#[kani::unwind(6)]
fn pair_pass_any_4() {
    let mut run = any_run::<4>();
    let len = run.len();
    pair_pass(&mut run, |_, _| {
        if kani::any() {
            Some(PairValue {
                first: any_value(),
                second: any_value(),
            })
        } else {
            None
        }
    });
    assert!(run.len() == len);
}

/// The `kern` table pass on any run of up to 4 glyphs, with any value for
/// every pair.
#[kani::proof]
#[kani::unwind(6)]
fn kern_pass_any_4() {
    let mut run = any_run::<4>();
    let len = run.len();
    kern_pass(&mut run, |_, _| kani::any());
    assert!(run.len() == len);
}
