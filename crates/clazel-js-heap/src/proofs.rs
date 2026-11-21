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

// ---- Second slice: elements and symbols -------------------------------
//
// Bounds, stated. The dense operations (`elements::dense`) are proven for
// one operation on a three-slot vector with indices below 5 (`dense_one_op`)
// and two sets from empty with indices below 6 (`dense_set_pair`). The fallback rule (E3) is
// proven for every `u32` index as the pure function `choose`. NOT proven:
// the sparse representation, the switch from dense to sparse, and
// `Elements` as a whole. Harnesses through `Elements::set` (which reaches
// `BTreeMap`) ran for over eight minutes without finishing and were
// dropped; those paths are covered by unit tests, including random
// sequences against the abstract array (`elements::contract::Spec`), which
// is a test, not a proof. Symbol harnesses cover the key encoding (Y4) for
// all `u32`; the table's construction (Y1 to Y3) formats strings and is
// covered by unit tests only.

use crate::elements::Elements;
use crate::elements::contract::{HOLE_BITS, MAX_DENSE, MAX_GAP, Mode, choose};
use crate::elements::dense;
use crate::string::Key;
use crate::symbol::contract::{PropertyKey, SYMBOL_BIT, SymbolId, decode, encode};

/// E3's rule is total and keeps dense storage within E4's bound.
#[kani::proof]
fn elements_choose_any() {
    let slots: u32 = kani::any();
    let index: u32 = kani::any();
    kani::assume(slots <= MAX_DENSE);
    let m = choose(Mode::Dense, slots, index);
    if m == Mode::Dense {
        // Either in range of the slots, or a write of at most MAX_GAP holes
        // below MAX_DENSE: the slot count after is at most MAX_DENSE.
        assert!(index < slots || (index < MAX_DENSE && index.saturating_sub(slots) <= MAX_GAP));
        assert!(index < MAX_DENSE);
    } else {
        assert!(index >= slots);
    }
    assert_eq!(choose(Mode::Sparse, slots, index), Mode::Sparse);
}

/// One operation (set, delete or truncate) on a dense vector of three
/// slots holding any bit patterns, against a three-cell model: reads, the
/// slot count's bound by the length (E2) and by `MAX_DENSE` (E4).
#[kani::proof]
#[kani::unwind(6)]
fn dense_one_op() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    let c: u64 = kani::any();
    let mut v: Vec<u64> = vec![a, b, c];
    let mut cells = [a, b, c];
    let i: u32 = kani::any();
    kani::assume(i < 5);
    let mut length: u32 = 3;
    match kani::any::<u8>() % 3 {
        0 => {
            let x: u64 = kani::any();
            kani::assume(x != HOLE_BITS);
            assert!(dense::set(&mut v, i, x).is_ok());
            if let Some(cell) = usize::try_from(i).ok().and_then(|i| cells.get_mut(i)) {
                *cell = x;
            }
            length = length.max(i.saturating_add(1));
        }
        1 => {
            let idx = usize::try_from(i).ok();
            let had = idx
                .and_then(|i| cells.get(i))
                .is_some_and(|&x| x != HOLE_BITS);
            assert_eq!(dense::delete(&mut v, i), had);
            if let Some(cell) = idx.and_then(|i| cells.get_mut(i)) {
                *cell = HOLE_BITS;
            }
        }
        _ => {
            dense::truncate(&mut v, i);
            length = i;
        }
    }
    assert!(u32::try_from(v.len()).is_ok_and(|n| n <= length && n <= MAX_DENSE));
    // Slots the model has (those below the vector's length) read back.
    for k in 0..3u32 {
        let kept = usize::try_from(k).ok().is_some_and(|k| k < v.len());
        let want = cells.get(usize::try_from(k).unwrap_or(0)).copied();
        if kept {
            assert_eq!(dense::get(&v, k), want);
        } else {
            assert_eq!(dense::get(&v, k), None);
        }
    }
}

/// `dense::set` at any index of the small range, after one set at 0:
/// both elements read back, nothing else appears (E1 for the dense case).
#[kani::proof]
#[kani::unwind(8)]
fn dense_set_pair() {
    let mut v: Vec<u64> = Vec::new();
    assert!(dense::set(&mut v, 0, 1).is_ok());
    let index: u32 = kani::any();
    kani::assume(index < 6);
    assert!(dense::set(&mut v, index, 2).is_ok());
    assert_eq!(dense::get(&v, index), Some(2));
    if index != 0 {
        assert_eq!(dense::get(&v, 0), Some(1));
    }
    let want_len = index.saturating_add(1).max(1);
    assert_eq!(u32::try_from(v.len()), Ok(want_len));
    assert_eq!(dense::get(&v, want_len), None);
}

/// An empty array has no element at any index.
#[kani::proof]
fn elements_empty_get_any() {
    let e = Elements::new();
    let i: u32 = kani::any();
    assert_eq!(e.get(i), None);
    assert_eq!(e.len(), 0);
}

/// Y4: for every `u32` key, decoding then encoding gives it back, and a
/// string and a symbol with the same number never share a key.
#[kani::proof]
fn symbol_key_encoding_any() {
    let k: u32 = kani::any();
    assert_eq!(encode(decode(Key(k))), Some(Key(k)));
    let n: u32 = kani::any();
    kani::assume(n < SYMBOL_BIT);
    let s = encode(PropertyKey::String(Key(n)));
    let y = encode(PropertyKey::Symbol(SymbolId(n)));
    assert!(s.is_some() && y.is_some());
    assert_ne!(s, y);
    assert_eq!(s.map(decode), Some(PropertyKey::String(Key(n))));
    assert_eq!(y.map(decode), Some(PropertyKey::Symbol(SymbolId(n))));
    // Numbers at or above 2^31 are refused, never wrapped (Y5).
    let big: u32 = kani::any();
    kani::assume(big >= SYMBOL_BIT);
    assert_eq!(encode(PropertyKey::String(Key(big))), None);
    assert_eq!(encode(PropertyKey::Symbol(SymbolId(big))), None);
}
