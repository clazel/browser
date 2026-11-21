//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! phase-7.md 7.5: "harnesses for the arena's invariants (no slot is both
//! free and live, and generations only grow) over all heaps up to a bound".
//! The invariants are `arena::contract`'s. The bound is every sequence of
//! up to [`STEPS`] operations (each `alloc`, `free` of any reference, or
//! `get` of any reference) on an arena limited to [`LIMIT`] slots, where a
//! reference's index and generation are any value in a range a little past
//! what the arena can hold, so out-of-range and stale references are tried.
//!
//! - [`arena_ops_any`]: from an empty arena, after every operation
//!   `is_well_formed` holds and [`step_ok`] holds of the step, and every
//!   successful lookup is of a live slot of the reference's generation.
//! - [`arena_free_any_generation`]: from a state with every slot's
//!   generation set to any `u16` (so a generation at `u16::MAX`, which the
//!   first harness cannot reach in its bound, is covered), one `free` and
//!   one `alloc` keep both properties: retirement never wraps a generation.
//!
//! Not covered: arenas past the bound. [`LIMIT`] is small because the free
//! list's walk in `well_formed` is a loop. The unit tests exercise
//! retirement through all 65,535 reuses of a slot.

use crate::arena::contract::step_ok;
use crate::arena::{Arena, Ref};

/// Slots in the arena of the harnesses.
const LIMIT: usize = 2;
/// Operations per harness run.
const STEPS: usize = 3;

fn any_ref() -> Ref {
    let index: u32 = kani::any();
    let generation: u16 = kani::any();
    kani::assume(index <= 2 && generation <= 2);
    Ref { index, generation }
}

fn check(a: &Arena<u8>, before: &[crate::arena::contract::SlotView]) {
    let after = a.view();
    assert!(a.is_well_formed());
    assert!(step_ok(before, &after));
}

fn one_op(a: &mut Arena<u8>) {
    let before = a.view();
    match kani::any::<u8>() % 3 {
        0 => {
            let _ = a.alloc(kani::any());
        }
        1 => {
            let _ = a.free(any_ref());
        }
        _ => {
            let r = any_ref();
            if a.get(r).is_ok() {
                // A lookup that succeeds names a live slot of this
                // generation (invariant 5).
                let v = a.view();
                let s = v.get(r.index as usize);
                assert!(s.is_some_and(|s| {
                    s.kind == crate::arena::contract::Kind::Live && s.generation == r.generation
                }));
            }
        }
    }
    check(a, &before);
}

#[kani::proof]
#[kani::unwind(6)]
fn arena_ops_any() {
    let mut a: Arena<u8> = Arena::with_limit(LIMIT);
    for _ in 0..STEPS {
        one_op(&mut a);
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn arena_free_any_generation() {
    let mut a: Arena<u8> = Arena::with_limit(LIMIT);
    let mut refs = [None; LIMIT];
    for r in &mut refs {
        *r = a.alloc(0).ok();
    }
    for i in 0..LIMIT {
        a.set_generation(i, kani::any());
    }
    // The references made before the generations were set are the
    // harness's only way to name slots: rebuild them from the arena.
    let live: Vec<Ref> = a.iter().map(|(r, _)| r).collect();
    for r in live {
        let before = a.view();
        if kani::any() {
            let _ = a.free(r);
            check(&a, &before);
        }
    }
    let before = a.view();
    let _ = a.alloc(1);
    check(&a, &before);
}
