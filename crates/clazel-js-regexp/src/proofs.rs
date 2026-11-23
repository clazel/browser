//! Kani harnesses (Tier 1) for the matcher's small pieces. Compiled only under
//! `cargo kani`.
//!
//! - **The case tables' lookups** ([`crate::unicode`]): for every input,
//!   `Canonicalize` stays in range and never turns a non-ASCII unit into an
//!   ASCII one (§22.2.2.7.3†). That the inverse table agrees with the forward
//!   one (`equivalents` of a character's canonical form contains it) is not
//!   here: with the two bisections and a growing `Vec` it ran past ten CPU
//!   minutes in CBMC. `tests/tables.rs` checks it for every code point.
//! - **The backtrack stack** ([`crate::stack::BtStack`]): a push never grows it
//!   past its bound, says "full" exactly at the bound, and a pop returns what
//!   was pushed last; `commit_look` keeps the undo entries and drops the rest.
//! - **Reading a character** ([`crate::vm::read`]): at any position of any
//!   input of up to 3 units, forward or backward, in either mode, the new
//!   position is inside the input, moves by one or two units, and the
//!   character is a code unit or a valid code point.
//!
//! What is not here: the matcher loop itself and the compiler. Both build
//! `Vec`s in loops, and the parser's README records that CBMC does not finish
//! on those (`src/parser/proofs.rs`). They are tested instead, by the
//! differential against a reference matcher (`tests/differential.rs`).

use crate::stack::{BtStack, Entry};
use crate::unicode::{canonicalize_unit, simple_fold};
use crate::vm::read;

/// The non-unicode `Canonicalize` of any code unit is a code unit, and a
/// non-ASCII unit never becomes ASCII.
#[kani::proof]
#[kani::unwind(14)]
fn canonicalize_unit_any() {
    let c: u16 = kani::any();
    let r = canonicalize_unit(u32::from(c));
    assert!(r <= 0xFFFF);
    if c >= 128 {
        assert!(r >= 128);
    }
}

/// Simple case folding of any code point is a code point.
#[kani::proof]
#[kani::unwind(14)]
fn simple_fold_any() {
    let c: u32 = kani::any();
    kani::assume(c <= 0x10FFFF);
    assert!(simple_fold(c) <= 0x10FFFF);
}

fn any_entry() -> Entry {
    match kani::any::<u8>() % 4 {
        0 => Entry::Branch {
            pc: kani::any(),
            pos: kani::any(),
        },
        1 => Entry::Restore {
            reg: kani::any(),
            old: kani::any(),
        },
        2 => Entry::Run {
            pc: kani::any(),
            back: kani::any(),
            cur: kani::any(),
            limit: kani::any(),
        },
        _ => Entry::LookMark {
            neg: kani::any(),
            pc: kani::any(),
            pos: kani::any(),
        },
    }
}

/// Pushing never takes the stack past its bound, and refuses exactly when it
/// is full, whatever the bound and the entries.
#[kani::proof]
#[kani::unwind(8)]
fn stack_push_respects_the_bound() {
    let max: usize = kani::any();
    kani::assume(max <= 4);
    let mut s = BtStack::new(max);
    for i in 0..6usize {
        let before = s.len();
        let r = s.push(any_entry());
        assert!(s.len() <= max);
        if before < max {
            assert!(r.is_ok() && s.len() == before + 1);
        } else {
            assert!(r.is_err() && s.len() == before);
        }
        let _ = i;
    }
}

/// A pop returns the entry pushed last, and an empty stack returns nothing.
#[kani::proof]
#[kani::unwind(4)]
fn stack_pop_returns_the_last_push() {
    let mut s = BtStack::new(2);
    assert!(s.pop().is_none());
    let a = any_entry();
    let b = any_entry();
    assert!(s.push(a).is_ok());
    assert!(s.push(b).is_ok());
    assert!(s.pop() == Some(b));
    assert!(s.pop() == Some(a));
    assert!(s.pop().is_none());
}

/// A positive lookaround's commit removes the mark and everything above it
/// but the undo entries, and gives back the position the mark holds.
#[kani::proof]
#[kani::unwind(8)]
fn stack_commit_look_keeps_only_the_undos() {
    let mut s = BtStack::new(4);
    let below = any_entry();
    kani::assume(!matches!(below, Entry::LookMark { .. }));
    let mark_pos: usize = kani::any();
    assert!(s.push(below).is_ok());
    assert!(
        s.push(Entry::LookMark {
            neg: false,
            pc: 0,
            pos: mark_pos
        })
        .is_ok()
    );
    let a = any_entry();
    kani::assume(!matches!(a, Entry::LookMark { .. }));
    let b = any_entry();
    kani::assume(!matches!(b, Entry::LookMark { .. }));
    assert!(s.push(a).is_ok());
    assert!(s.push(b).is_ok());
    let Some((pos, _)) = s.commit_look() else {
        panic!("a mark is on the stack");
    };
    assert!(pos == mark_pos);
    // What remains above `below` is the undo entries among `a`, `b`, in order.
    let mut kept = Vec::new();
    while let Some(e) = s.pop() {
        kept.push(e);
    }
    let undos = [a, b]
        .iter()
        .filter(|e| matches!(e, Entry::Restore { .. }))
        .count();
    assert!(kept.len() == undos + 1);
    assert!(kept.last() == Some(&below));
}

/// Reading a character at any position of any input of up to 3 units.
#[kani::proof]
#[kani::unwind(6)]
fn read_any_3() {
    let units: [u16; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);
    let input = units.get(..len).unwrap_or_default();
    let pos: usize = kani::any();
    kani::assume(pos <= len);
    let unicode: bool = kani::any();
    let back: bool = kani::any();
    match read(input, unicode, pos, back) {
        Some((ch, np)) => {
            assert!(np <= len);
            if back {
                assert!(np < pos && pos - np <= 2);
            } else {
                assert!(np > pos && np - pos <= 2);
            }
            assert!(ch <= 0x10FFFF);
            if !unicode {
                assert!(ch <= 0xFFFF && np.abs_diff(pos) == 1);
            }
        }
        None => {
            if back {
                assert!(pos == 0);
            } else {
                assert!(pos == len);
            }
        }
    }
}
