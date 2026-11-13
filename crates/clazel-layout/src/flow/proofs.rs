//! Kani harnesses for block and inline formatting. Compiled only under
//! `cargo kani`.
//!
//! Each harness checks **one step from any state** satisfying its
//! invariant (`state.rs`), with any input: no panic, arithmetic overflow or
//! out-of-bounds index is reachable, the step keeps the invariant, and the
//! properties its contract states hold. The start states satisfy the
//! invariants (asserted too), so by induction every state the walk reaches
//! on a tree of **any size and depth** does, and every step it takes has
//! the checked properties. Where a contract is an equation (§10.3.3's sum,
//! §10.8.1's halves), it is checked in `i64` on inputs within 2^22 px in
//! magnitude, where no `i32` sum of four of them saturates; a second harness checks that
//! any input, at any size, is handled without panic or overflow.
//!
//! §8.3.1's rule is written a second time here, from the section's three
//! sentences, and the set's `resolve` is checked against it.
//!
//! Proved for every size (step harnesses): the margin set
//! ([`collapsed_any`]), the flow's steps ([`enter_any`], [`place_any`],
//! [`close_any`], [`exit_any`], [`finish_any`]), a line box's extent
//! ([`line_extent_any`]). For any input: §10.3.3 ([`solve_block_any`],
//! [`solve_block_sum`]), align descendants ([`align_any`]), §10.4
//! ([`width_min_max_any`]), shrink-to-fit ([`shrink_to_fit_any`]), §10.7
//! and the quirks' fill ([`heights_any`]), §10.8.1's half-leading
//! ([`half_leading_any`]), §16.2's offset ([`align_offset_any`]), the
//! walk's roles ([`role_any`]), and the length arithmetic
//! ([`halves_any`], [`times_any`]).
//!
//! Not covered, and why: the drivers (`block.rs`'s walk and resolution
//! walk, `inline.rs`'s preparation, line building and vertical alignment
//! loop, `intrinsic.rs`'s pass), whose state is the arena, the frames and
//! the fragment vectors; reading style and shaping (`clazel-style`'s and
//! items 5.10 and 5.11's); and item 5.12's line choice (`fit_step`, proved
//! there). The unit and golden tests run the drivers.

use super::block::role;
use super::heights::{child_basis, half_leading, min_max as height_min_max, quirk_fill};
use super::inline::align_offset;
use super::length::{half_down, half_up, times};
use super::margins::{close, enter, exit, finish, place};
use super::state::{
    Align, BlockFacts, Collapsed, Entry, Exited, Flow, LineExtent, Role, UsedWidths, WidthInput,
};
use super::widths::{align, min_max as width_min_max, shrink_to_fit, solve_block};
use crate::boxes::Class;

/// 2^22 px in 1/64 px: within it, no sum of four values saturates.
const BOUND: i32 = 1 << 28;

fn small(v: i32) -> bool {
    v > -BOUND && v < BOUND
}

/// §8.3.1's rule for a set of two margins, written a second time: "the
/// resulting margin width is the maximum of the collapsing margins' widths.
/// In the case of negative margins, the maximum of the absolute values of
/// the negative adjoining margins is deducted from the maximum of the
/// positive adjoining margins. If there are no positive margins, the
/// maximum of the absolute values of the adjoining margins is deducted from
/// zero."
fn collapsed_two(a: i32, b: i32) -> i64 {
    let (a, b) = (i64::from(a), i64::from(b));
    if a >= 0 && b >= 0 {
        a.max(b)
    } else if a < 0 && b < 0 {
        0 - a.abs().max(b.abs())
    } else {
        let pos = if a >= 0 { a } else { b };
        let neg = if a < 0 { a } else { b };
        pos - neg.abs()
    }
}

/// The margin set: invariant kept, order of adjoining irrelevant, union
/// symmetric, and the result §8.3.1's rule.
#[kani::proof]
fn collapsed_any() {
    assert!(Collapsed::NONE.invariant());
    let c: Collapsed = kani::any();
    kani::assume(c.invariant());
    let (a, b): (i32, i32) = (kani::any(), kani::any());
    let ab = c.adjoin(a).adjoin(b);
    assert!(ab.invariant());
    assert!(ab == c.adjoin(b).adjoin(a));
    let d: Collapsed = kani::any();
    kani::assume(d.invariant());
    assert!(c.join(d) == d.join(c));
    assert!(c.join(d).invariant());
    // One margin is itself; two margins follow the rule.
    assert!(Collapsed::of(a).resolve() == a);
    assert!(i64::from(Collapsed::of(a).adjoin(b).resolve()) == collapsed_two(a, b));
}

/// `margins::enter`: the parent keeps nothing pending and does not move;
/// the child opens exactly when its top margin adjoins its first child's.
#[kani::proof]
fn enter_any() {
    let parent: Flow = kani::any();
    kani::assume(parent.invariant());
    let facts: BlockFacts = kani::any();
    let mt: i32 = kani::any();
    let (entry, next) = enter(parent, facts, mt);
    assert!(next.invariant());
    assert!(next.pending == Collapsed::NONE);
    assert!(next.y == parent.y && next.open == parent.open && next.placed == parent.placed);
    let m = parent.pending.adjoin(mt);
    match entry {
        Entry::Open(x) => {
            assert!(facts.top_adjoins() && x == m);
            assert!(Flow::open(x).invariant());
        }
        Entry::Content(x) => assert!(!facts.top_adjoins() && x == m),
    }
}

/// `margins::place`: content goes after the frame's `y` and the margins.
#[kani::proof]
fn place_any() {
    let frame: Flow = kani::any();
    kani::assume(frame.invariant() && !frame.open);
    let m: Collapsed = kani::any();
    kani::assume(m.invariant());
    let (top, next) = place(frame, m);
    assert!(top == frame.y.saturating_add(m.resolve()));
    assert!(next.invariant() && !next.open && next.placed);
    assert!(next.y == frame.y && next.pending == Collapsed::NONE);
}

/// `margins::close`: an open frame becomes closed at its top.
#[kani::proof]
fn close_any() {
    let frame: Flow = kani::any();
    kani::assume(frame.invariant() && frame.open);
    let next = close(frame);
    assert!(next.invariant() && !next.open && next.placed && next.y == 0);
}

/// `margins::exit`: a child that collapsed through hands its margins on;
/// a placed child moves the flow to its bottom.
#[kani::proof]
fn exit_any() {
    let parent: Flow = kani::any();
    kani::assume(parent.invariant());
    let child: Exited = kani::any();
    let next = exit(parent, child);
    match child {
        Exited::Through(p) => {
            kani::assume(p.invariant());
            assert!(next.y == parent.y && next.open == parent.open && next.pending == p);
        }
        Exited::Placed { bottom, pending } => {
            kani::assume(pending.invariant());
            assert!(next.y == bottom && !next.open && next.placed && next.pending == pending);
        }
    }
    assert!(next.invariant());
}

/// `margins::finish`: §8.3.1's and §10.6.3's cases.
#[kani::proof]
fn finish_any() {
    let flow: Flow = kani::any();
    kani::assume(flow.invariant());
    let facts: BlockFacts = kani::any();
    let f = finish(flow, facts);
    assert!(f.out.invariant());
    assert!(!(f.through && f.resolve));
    if f.through {
        assert!(flow.open && facts.may_collapse_through() && f.content == 0);
        assert!(f.out == flow.pending);
    }
    if f.resolve {
        assert!(flow.open && !facts.may_collapse_through() && f.content == 0);
    }
    if !flow.open {
        assert!(!f.through && !f.resolve);
        if facts.bottom_adjoins() {
            assert!(f.content == flow.y && f.out == flow.pending);
        } else {
            assert!(f.content == flow.y.saturating_add(flow.pending.resolve()));
        }
    }
    // Nothing goes on past a bottom that does not adjoin.
    if !f.through && !facts.bottom_adjoins() {
        assert!(f.out == Collapsed::NONE);
    }
}

/// §10.3.3 on any input: no panic or overflow, and the width never
/// negative.
#[kani::proof]
fn solve_block_any() {
    let input: WidthInput = kani::any();
    let u = solve_block(input);
    assert!(u.width >= 0);
}

/// §10.3.3's equality and rules on inputs where no sum saturates.
#[kani::proof]
fn solve_block_sum() {
    let input: WidthInput = kani::any();
    kani::assume(small(input.containing) && small(input.edges));
    kani::assume(input.margin_left.is_none_or(small));
    kani::assume(input.margin_right.is_none_or(small));
    kani::assume(input.width.is_none_or(small));
    let u = solve_block(input);
    let sum = i64::from(u.margin_left)
        + i64::from(input.edges)
        + i64::from(u.width)
        + i64::from(u.margin_right);
    assert!(sum == i64::from(input.containing));
    // A width given (and not negative) is kept.
    if let Some(w) = input.width
        && w >= 0
    {
        assert!(u.width == w);
    }
    // A margin given is kept, unless it is the right one of a box rule 2
    // over-constrains.
    if let Some(l) = input.margin_left {
        assert!(u.margin_left == l);
    }
    // Rule 5: two `auto` margins are equal, to the 1/64 px, when nothing
    // is too wide.
    if input.margin_left.is_none()
        && input.margin_right.is_none()
        && let Some(w) = input.width
        && w >= 0
        && i64::from(input.edges) + i64::from(w) <= i64::from(input.containing)
    {
        let d = i64::from(u.margin_right) - i64::from(u.margin_left);
        assert!(d == 0 || d == 1);
    }
}

/// HTML's align descendants: only a forced box moves; the sum and the
/// width are kept.
#[kani::proof]
fn align_any() {
    let u: UsedWidths = kani::any();
    kani::assume(small(u.margin_left) && small(u.margin_right));
    let to: Align = kani::any();
    let v = align(u, to);
    assert!(v.width == u.width);
    assert!(
        i64::from(v.margin_left) + i64::from(v.margin_right)
            == i64::from(u.margin_left) + i64::from(u.margin_right)
    );
    if !u.forced_right {
        assert!(v == u);
    }
}

/// §10.4's steps 2 and 3.
#[kani::proof]
fn width_min_max_any() {
    let (t, min, max): (i32, i32, Option<i32>) = (kani::any(), kani::any(), kani::any());
    let again = width_min_max(t, min, max);
    let after_max = match max {
        Some(m) if t > m => m,
        _ => t,
    };
    if after_max < min {
        assert!(again == Some(min));
    } else if after_max != t {
        assert!(again == Some(after_max));
    } else {
        assert!(again.is_none());
    }
}

/// §10.3.5's formula.
#[kani::proof]
fn shrink_to_fit_any() {
    let (lo, hi, avail): (i32, i32, i32) = (kani::any(), kani::any(), kani::any());
    let w = shrink_to_fit(lo, hi, avail);
    assert!(w == lo.max(avail).min(hi));
    if lo >= 0 && hi >= 0 {
        assert!(w >= 0);
    }
}

/// §10.7, the quirks' fill and the percentage basis.
#[kani::proof]
fn heights_any() {
    let (t, min, max): (i32, i32, Option<i32>) = (kani::any(), kani::any(), kani::any());
    let h = height_min_max(t, min, max);
    assert!(h >= 0 && h >= min);
    if let Some(m) = max
        && m >= min
        && m >= 0
    {
        assert!(h <= m);
    }
    let (normal, avail, margins): (i32, i32, i32) = (kani::any(), kani::any(), kani::any());
    let f = quirk_fill(normal, avail, margins);
    assert!(f >= normal && f >= avail.saturating_sub(margins));
    let (d, q, p, i): (Option<i32>, bool, bool, Option<i32>) =
        (kani::any(), kani::any(), kani::any(), kani::any());
    let b = child_basis(d, q, p, i);
    assert!(d.is_none() || b == d);
    if !q {
        assert!(b == d);
    }
}

/// §10.8.1's halves of the leading add up to it.
#[kani::proof]
fn half_leading_any() {
    let (a, d, l): (i32, i32, i32) = (kani::any(), kani::any(), kani::any());
    let (above, below) = half_leading(a, d, l);
    if small(a) && small(d) && small(l) {
        assert!(i64::from(above) + i64::from(below) == i64::from(l));
        let leading = i64::from(l) - i64::from(a) - i64::from(d);
        let top_half = i64::from(above) - i64::from(a);
        assert!(top_half * 2 == leading || top_half * 2 == leading - 1);
    }
}

/// A line box's extent: the invariant is kept and it covers each box.
#[kani::proof]
fn line_extent_any() {
    assert!(LineExtent::EMPTY.invariant());
    let e: LineExtent = kani::any();
    kani::assume(e.invariant());
    let (top, bottom): (i32, i32) = (kani::any(), kani::any());
    let n = e.add(top, bottom);
    assert!(n.invariant() && n.any);
    assert!(n.top <= top && n.bottom >= bottom.max(top));
    if e.any {
        assert!(n.top <= e.top && n.bottom >= e.bottom);
    }
}

/// §16.2: the content stays in the line box when it fits, and is
/// start-aligned when it does not.
#[kani::proof]
fn align_offset_any() {
    let to: Align = kani::any();
    let (avail, width): (i32, i32) = (kani::any(), kani::any());
    let off = align_offset(to, avail, width);
    if i64::from(width) >= i64::from(avail) {
        assert!(off == 0);
    } else {
        assert!(off >= 0 && i64::from(off) <= i64::from(avail) - i64::from(width));
    }
    if to == Align::Left {
        assert!(off == 0);
    }
}

/// The walk's roles, for any class.
#[kani::proof]
fn role_any() {
    let c: Class = kani::any();
    let r = role(c);
    match c {
        Class::Root => assert!(r == Role::Root),
        Class::Marker => assert!(r == Role::Marker),
        Class::Column | Class::ColumnGroup => assert!(r == Role::Column),
        Class::Inline | Class::Text { .. } => assert!(r == Role::Inline),
        Class::Cell => assert!(r == Role::Cell),
        Class::RowGroup | Class::Row => assert!(r == Role::Track),
        Class::Table { .. } | Class::Caption => assert!(r == Role::Flow),
        _ => {
            if c.is_block_level() {
                assert!(r == Role::Flow);
            }
            if c.is_atomic_inline() {
                assert!(r == Role::Atomic);
            }
        }
    }
}

/// Halves of a length add up to it.
#[kani::proof]
fn halves_any() {
    let v: i32 = kani::any();
    assert!(i64::from(half_down(v)) + i64::from(half_up(v)) == i64::from(v));
}

/// A number times a length (`line-height: <number>`) does not overflow,
/// for any number and length.
#[kani::proof]
fn times_any() {
    let n: clazel_style::values::number::Num = kani::any();
    let px: i32 = kani::any();
    let t = times(n, px);
    if px == 0 {
        assert!(t == 0);
    }
}
