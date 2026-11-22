//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! phase-7.md 7.5 asks for "harnesses for the arena's invariants (no slot is
//! both free and live, and generations only grow) over all heaps up to a
//! bound". The invariants are `arena::contract`'s: after every operation
//! `is_well_formed` (invariants 1 and 2) and [`step_ok`] (3 and 4) hold.
//! The bound is small, and is stated here, not claimed larger: an arena
//! limited to [`LIMIT`] slots, with a reference's index and generation any
//! value up to 1 (so out-of-range and stale references are tried).
//!
//! - [`arena_free_free`]: from an arena of one live slot, two `free`s of
//!   any references in range.
//! - [`arena_free_any_generation`]: from a state with every slot's
//!   generation set to any `u16` (so `u16::MAX`, which the pairs cannot
//!   reach, is covered), any subset of the live slots freed and one `alloc`:
//!   retirement never wraps a generation.
//! - [`arena_lookup_any`]: after a slot is freed and reused, a lookup of
//!   any reference succeeds only for a live slot of the reference's
//!   generation (invariant 5).
//! - [`value_decode_any`], [`value_roundtrip_any`]: for any `u64`, a pattern
//!   `decode_bits` accepts is the one the constructors make from what it
//!   decoded to; and every constructed value decodes to its inputs.
//!
//! Not covered: arenas past the bound, and arbitrary sequences of
//! operations. Harnesses that ran `alloc` after a `free` of a symbolic
//! reference, or chose operations symbolically, or started from a symbolic
//! number of slots (CBMC models the vector's growth as paths), each ran for
//! 8 to 25 minutes without finishing and were dropped; `alloc` after frees is
//! covered only through [`arena_free_any_generation`] and
//! [`arena_lookup_any`]. The unit tests exercise retirement through all
//! 65,535 reuses of a slot, and longer sequences.

use crate::arena::contract::step_ok;
use crate::arena::{Arena, Ref};
use crate::value::{Decoded, Value, decode_bits};

/// Slots in the arena of the harnesses.
const LIMIT: usize = 2;

fn any_ref() -> Ref {
    let index: u32 = kani::any();
    let generation: u16 = kani::any();
    kani::assume(index <= 1 && generation <= 1);
    Ref { index, generation }
}

fn check(a: &Arena<u8>, before: &[crate::arena::contract::SlotView]) {
    let after = a.view();
    assert!(a.is_well_formed());
    assert!(step_ok(before, &after));
}

fn one_op(a: &mut Arena<u8>, free: bool) {
    let before = a.view();
    if free {
        let _ = a.free(any_ref());
    } else {
        let _ = a.alloc(0);
    }
    check(a, &before);
}

/// From an arena of one live slot, two operations (see the module header).
fn two_ops(first: bool, second: bool) {
    let mut a: Arena<u8> = Arena::with_limit(LIMIT);
    let _ = a.alloc(0);
    one_op(&mut a, first);
    one_op(&mut a, second);
}

#[kani::proof]
#[kani::unwind(6)]
fn arena_free_free() {
    two_ops(true, true);
}

#[kani::proof]
#[kani::unwind(6)]
fn arena_lookup_any() {
    // One slot freed and reused, one never freed: any reference either
    // names the live occupant of its slot or is an error (invariant 5).
    let mut a: Arena<u8> = Arena::with_limit(LIMIT);
    let first = a.alloc(0);
    let _ = a.alloc(0);
    if let Ok(r) = first {
        if kani::any::<bool>() {
            let _ = a.free(r);
        }
        if kani::any::<bool>() {
            let _ = a.alloc(0);
        }
    }
    let r = any_ref();
    let v = a.view();
    match a.get(r) {
        Ok(_) => {
            let s = usize::try_from(r.index).ok().and_then(|i| v.get(i));
            assert!(s.is_some_and(|s| {
                s.kind == crate::arena::contract::Kind::Live && s.generation == r.generation
            }));
        }
        Err(_) => {}
    }
    assert_eq!(a.is_live(r), a.get(r).is_ok());
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

fn same_bits(d: Decoded) -> Option<u64> {
    Some(match d {
        Decoded::Double(x) => Value::double(x).bits(),
        Decoded::Int32(i) => Value::int32(i).bits(),
        Decoded::Undefined => Value::UNDEFINED.bits(),
        Decoded::Null => Value::NULL.bits(),
        Decoded::Bool(b) => Value::boolean(b).bits(),
        Decoded::Hole => Value::HOLE.bits(),
        Decoded::Ref(r) => Value::heap_ref(r).bits(),
        Decoded::Raw(p) => Value::raw(p)?.bits(),
    })
}

#[kani::proof]
fn value_decode_any() {
    let bits: u64 = kani::any();
    if let Some(d) = decode_bits(bits) {
        assert_eq!(same_bits(d), Some(bits));
        assert_eq!(Value::from_bits(bits).map(Value::bits), Some(bits));
    } else {
        assert_eq!(Value::from_bits(bits), None);
    }
}

#[kani::proof]
fn value_roundtrip_any() {
    let x = f64::from_bits(kani::any());
    let v = Value::double(x);
    // A boxed double is a value, and is the double unless it was a NaN.
    assert!(Value::from_bits(v.bits()).is_some());
    if !x.is_nan() {
        assert_eq!(v.bits(), x.to_bits());
    } else {
        assert_eq!(v.bits(), crate::value::CANON_NAN);
    }
    let i: i32 = kani::any();
    assert_eq!(Value::int32(i).decode(), Decoded::Int32(i));
    let r = Ref {
        index: kani::any(),
        generation: kani::any(),
    };
    assert_eq!(Value::heap_ref(r).decode(), Decoded::Ref(r));
    let p: u64 = kani::any();
    match Value::raw(p) {
        Some(v) => assert_eq!(v.decode(), Decoded::Raw(p)),
        None => assert!(p > 0xFFFF_FFFF_FFFF),
    }
}
