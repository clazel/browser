//! Kani harnesses for the box tree. Compiled only under `cargo kani`.
//!
//! Most harnesses check **one step from any state**: any value of the
//! step's state that satisfies its invariant (`state.rs`), and any next
//! input. Kani checks that no panic, arithmetic overflow or out-of-bounds
//! index is reachable, the properties asserted, and that the step keeps the
//! invariant. The start state satisfies the invariant (asserted too), so by
//! induction every state a driver reaches on a tree of **any size and
//! depth** does, and every step it takes has the checked properties.
//! Bounds, times and memory are in the crate README.
//!
//! The postconditions of §17.2.1's stages are written here a second time,
//! from the section's goal rather than its rules ("the 'missing' elements
//! must be assumed in order for the table model to work"): after stage 2,
//! a table holds only proper table children, a row group only rows and a
//! row only cells; after stage 3, no proper table child is misparented and
//! every cell is in a row. The harnesses check that the rules' decisions
//! establish them, for any parent and child.
//!
//! Proved for every size (step harnesses):
//!
//! - box generation: [`super::generate::decide`] on any node
//!   ([`decide_any`]) and [`super::generate::walk_step`] from any frame
//!   ([`walk_step_any`]);
//! - §17.2.1 stage 1 on any child and siblings ([`irrelevant_any`]);
//!   stage 2's and stage 3's decision for any parent and child
//!   ([`stage_2_any`], [`stage_3_any`]), and the grouping step they share
//!   from any state ([`group_step_any`]);
//! - §9.2.1.1's split step from any state ([`split_step_any`]).
//!
//! Also for any value: the marker's numbering
//! ([`super::marker::roman_counts`], [`roman_any`];
//! [`super::marker::alphabetic_digits`] in base 26, [`alphabetic_any`]).
//!
//! Not covered, and why: the grouping driver (`table::regroup`) on any 3
//! children of one parent (`regroup_any_3`, removed: it passed the 8 GB
//! cap after 13.7 minutes, mostly in the drop glue of the arena's boxes;
//! its step and per-child decisions are covered above); the drivers that
//! walk the arena
//! (`generate::generate`, `table::stage_1` to `stage_3`,
//! `anonymous::split`, `anonymous::text_runs`, `BoxTree::compact`) as whole
//! loops over trees, whose state is a `Vec` of boxes holding `String`s (the
//! steps they call are covered for every size, and the unit and golden
//! tests run the drivers); reading the DOM (`clazel-dom`'s, proven there)
//! and the computed style (`clazel-style`'s); and Phase I
//! (`text::collapse`, whose step item 5.12 proves).

use super::anonymous::split_step;
use super::generate::{NodeClass, NodeInfo, decide, walk_step};
use super::marker;
use super::state::{Decision, Frame, Group, Place, Principal, SplitEvent, SplitState, group_step};
use super::table::{
    irrelevant_1, irrelevant_2, is_misparented, is_proper_table_child, wrapper_2, wrapper_3_1,
    wrapper_3_2,
};
use super::tree::{BoxKind, BoxTree, Class};

/// The class of an anonymous box a rule makes.
fn class_of(k: &BoxKind) -> Class {
    match k {
        BoxKind::Row => Class::Row,
        BoxKind::Cell => Class::Cell,
        BoxKind::Table { inline } => Class::Table { inline: *inline },
        _ => Class::Root,
    }
}

/// Stage 2's goal, for a child of `parent`: "Generate missing child
/// wrappers" leaves a table with only rows, row groups, columns, column
/// groups and captions, a row group with only rows, and a row with only
/// cells.
fn wrapped_ok(parent: Class, c: Class) -> bool {
    match parent {
        Class::Table { .. } => matches!(
            c,
            Class::Row | Class::RowGroup | Class::Column | Class::ColumnGroup | Class::Caption
        ),
        Class::RowGroup => c == Class::Row,
        Class::Row => c == Class::Cell,
        _ => true,
    }
}

/// Stage 3's goal, for a child of `parent`: a row only in a table or row
/// group, a column only in a table or column group, a row group, column
/// group or caption only in a table, and a cell only in a row.
fn parented_ok(parent: Class, c: Class) -> bool {
    let table = matches!(parent, Class::Table { .. });
    match c {
        Class::Row => table || parent == Class::RowGroup,
        Class::Column => table || parent == Class::ColumnGroup,
        Class::RowGroup | Class::ColumnGroup | Class::Caption => table,
        Class::Cell => parent == Class::Row,
        _ => true,
    }
}

/// What a node generates, for any node.
#[kani::proof]
fn decide_any() {
    let n: NodeInfo = kani::any();
    let d = decide(n);
    match n.class {
        NodeClass::Document => assert!(d == Decision::Contents),
        NodeClass::Text => assert!(d == Decision::Text),
        NodeClass::Other => assert!(d == Decision::Nothing),
        NodeClass::Element => {
            assert!(d != Decision::Text);
            if n.display.is_none()
                || n.display == Some(clazel_style::cascade::computed::Display::None)
            {
                assert!(d == Decision::Nothing || d == Decision::Contents);
            }
            if d == Decision::Contents {
                assert!(n.contents && !n.replaced);
            }
            if n.replaced && !n.line_break {
                assert!(matches!(
                    d,
                    Decision::Nothing | Decision::Element(Principal::Replaced { .. })
                ));
            }
        }
    }
}

/// One step of the generation walk from any frame satisfying the
/// invariant: every frame pushed for any child satisfies it with the boxes
/// added, and only an element or the document has its children walked.
#[kani::proof]
fn walk_step_any() {
    let nodes: usize = kani::any();
    let boxes: usize = kani::any();
    // An arena never holds `usize::MAX` boxes.
    kani::assume(boxes < usize::MAX - 2);
    let frame: Frame = kani::any();
    kani::assume(frame.invariant(nodes, boxes));
    assert!(
        Frame {
            node: 0,
            parent: BoxTree::ROOT
        }
        .invariant(1, 1)
    );
    let d: Decision = kani::any();
    let w = walk_step(frame, d, boxes);
    assert!(w.added <= 2);
    let after = boxes + w.added;
    let child: usize = kani::any();
    kani::assume(child < nodes);
    if let Some(under) = w.children_under {
        assert!(
            Frame {
                node: child,
                parent: under
            }
            .invariant(nodes, after)
        );
        assert!(!matches!(
            d,
            Decision::Nothing
                | Decision::Text
                | Decision::Element(Principal::Replaced { .. } | Principal::Break)
        ));
    }
    if d == Decision::Contents {
        assert!(w.added == 0 && w.children_under == Some(frame.parent));
    }
}

/// The grouping step from any state.
#[kani::proof]
fn group_step_any() {
    let s: Group = kani::any();
    let wrapped: bool = kani::any();
    let (place, next) = group_step(s, wrapped);
    assert!((place == Place::Keep) == !wrapped);
    assert!(place != Place::Open || !s.open);
    assert!(place != Place::Join || s.open);
    assert!(next.open == wrapped);
    assert!(!Group::START.open);
}

/// Stage 1 on any child, parent and siblings: rules 1.1 and 1.2 remove
/// what they say; rules 1.3 and 1.4 remove only white-space-only text, and
/// never a column of a column group.
#[kani::proof]
fn irrelevant_any() {
    let parent: Class = kani::any();
    let c: Class = kani::any();
    let before: Option<Class> = kani::any();
    let after: Option<Class> = kani::any();
    if parent == Class::Column {
        assert!(irrelevant_1(parent, c));
    }
    if parent == Class::ColumnGroup {
        assert!(irrelevant_1(parent, c) == (c != Class::Column));
    }
    if irrelevant_2(parent, c, before, after) {
        assert!(c == Class::Text { white: true });
    }
    // Between two cells, white space always goes (1.4).
    if c == (Class::Text { white: true })
        && before == Some(Class::Cell)
        && after == Some(Class::Cell)
    {
        assert!(irrelevant_2(parent, c, before, after));
    }
}

/// Stage 2's decision for any parent and child: the child, or the
/// anonymous box that wraps it, meets stage 2's goal in the parent, and a
/// wrapped child meets it in its wrapper once the wrapper's own children
/// are regrouped.
#[kani::proof]
fn stage_2_any() {
    let parent: Class = kani::any();
    let c: Class = kani::any();
    match wrapper_2(parent, c) {
        None => assert!(wrapped_ok(parent, c)),
        Some(w) => {
            let w = class_of(&w);
            assert!(wrapped_ok(parent, w));
            // The wrapper is a row or a cell; in a row, the child is wrapped
            // again unless it is a cell.
            let inner = wrapper_2(w, c).map_or(c, |k| class_of(&k));
            assert!(wrapped_ok(w, inner));
        }
    }
}

/// Stage 3's decisions (rule 3.1, then rule 3.2) for any parent and any
/// child that stage 2 left: what ends up in the parent, and the child in
/// what wraps it, meet stage 3's goal; an inline parent gets an inline
/// table.
#[kani::proof]
fn stage_3_any() {
    let parent: Class = kani::any();
    let c: Class = kani::any();
    kani::assume(wrapped_ok(parent, c));
    let first = wrapper_3_1(parent, c).map_or(c, |k| class_of(&k));
    if first != c {
        // 3.1 wrapped a cell in a row.
        assert!(parented_ok(Class::Row, c));
    }
    let placed = match wrapper_3_2(parent, first) {
        None => first,
        Some(t) => {
            let t = class_of(&t);
            assert!(
                t == Class::Table {
                    inline: parent == Class::Inline
                }
            );
            assert!(parented_ok(t, first));
            assert!(is_proper_table_child(first) && is_misparented(parent, first));
            t
        }
    };
    assert!(parented_ok(parent, placed));
}

/// §9.2.1.1's split step from any state satisfying the invariant, for any
/// event the driver can send.
#[kani::proof]
fn split_step_any() {
    assert!(SplitState::START.invariant());
    let s: SplitState = kani::any();
    kani::assume(s.invariant());
    let e: SplitEvent = kani::any();
    // The driver sends `Exit` only inside an inline box on the path, and
    // the path is never `usize::MAX` deep (each entry is a box).
    kani::assume(e != SplitEvent::Exit || s.depth > 0);
    kani::assume(s.depth < usize::MAX);
    let (a, after) = split_step(s, e);
    assert!(after.invariant());
    // Never reopens what is open, never past the path.
    assert!(a.open_from >= s.open || a.open_from == s.depth);
    assert!(a.open_from <= s.depth);
    assert!(!a.open_anonymous || !s.anonymous);
    // Fragments are opened only inside an anonymous block.
    if a.open_from < s.depth {
        assert!(s.anonymous || a.open_anonymous);
    }
    match e {
        SplitEvent::Enter => {
            assert!(after.depth == s.depth + 1 && after.open == s.open);
        }
        SplitEvent::Inline => {
            // Placed inside the innermost box: every fragment open.
            assert!(a.place_inline && after.open == s.depth && after.anonymous);
            assert!(a.open_from == s.open);
        }
        SplitEvent::Block => {
            assert!(a.place_block && after.open == 0 && !after.anonymous);
            // Every box on the path has had its "before" side.
            assert!(after.parted == s.depth);
            if s.parted < s.depth {
                assert!(a.open_from == s.open);
            }
        }
        SplitEvent::Exit => {
            assert!(a.exit && after.depth == s.depth - 1);
            // The exited box has a fragment to mark as its last.
            assert!(s.open == s.depth || a.open_from == s.open);
        }
    }
}

/// Roman numerals on any value: `None` exactly outside 1 to 3999, and
/// otherwise symbols whose weights add up to the value.
#[kani::proof]
#[kani::unwind(15)]
fn roman_any() {
    let v: i64 = kani::any();
    let counts = marker::roman_counts(v);
    assert!(counts.is_some() == (1..=3999).contains(&v));
    if let Some(c) = counts {
        let weights: [i64; 13] = [1000, 900, 500, 400, 100, 90, 50, 40, 10, 9, 5, 4, 1];
        let mut sum = 0i64;
        for i in 0..13 {
            assert!(c[i] <= 3);
            sum += weights[i] * i64::from(c[i]);
        }
        assert!(sum == v);
    }
}

/// Alphabetic numbering in base 26 on any value: no panic or overflow,
/// `None` exactly below 1, and between 1 and 14 digits (26^14 > 2^63), one
/// digit up to 26.
#[kani::proof]
#[kani::unwind(66)]
fn alphabetic_any() {
    let v: i64 = kani::any();
    let n = marker::alphabetic_digits(v, 26);
    assert!(n.is_none() == (v < 1));
    if let Some((digits, len)) = n {
        assert!(len >= 1 && len <= 14);
        if v <= 26 {
            assert!(len == 1 && i64::from(digits[0]) == v - 1);
        }
        for d in digits {
            assert!(d < 26);
        }
    }
}
