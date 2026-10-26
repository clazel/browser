//! Timing-safe comparison of secret byte strings (RFC 8446 §4.4.4, the
//! Finished `verify_data` check; docs/phases/phase-3.md item 3.0).
//!
//! Modelling choices:
//! - **Verus proves the result, not the timing.** The contract says only
//!   that [`constant_time_eq`] returns `a@ == b@`. Timing independence rests
//!   on the shape of the code: one pass over every index, an OR-accumulator
//!   of byte XORs, no early exit, no `break`, no branch on the data inside
//!   the loop, and no data-dependent indexing. The only branch on secret
//!   data is the final `acc == 0`, which is the standard construction.
//! - **The compiler is trusted not to undo that shape.** LLVM could in
//!   principle turn the accumulator into an early exit. We do not use
//!   `core::hint::black_box`, because its guarantee is best effort only, so
//!   this module claims no more than the shape above. It makes no claim
//!   about caches, speculation or the hardware.
//! - **Lengths are public.** The contract requires equal lengths; callers
//!   compare fixed-size values (32 octets for SHA-256 Finished), so the
//!   length never depends on a secret.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The byte at `i`, or 0 past the end. Callers keep `i < s.len()`, so the
/// fallback is unreachable; it depends on the index, never on the data.
fn byte_at(s: &[u8], i: usize) -> (out: u8)
    requires
        i < s.len(),
    ensures
        out == s@[i as int],
{
    match s.get(i) {
        Some(&v) => v,
        None => 0,
    }
}

/// Bitwise facts about `u8`: XOR is zero exactly on equal bytes, and an OR is
/// zero exactly when both sides are.
proof fn lemma_xor_zero(x: u8, y: u8)
    ensures
        (x ^ y) == 0 <==> x == y,
{
    assert((x ^ y) == 0 <==> x == y) by (bit_vector);
}

proof fn lemma_or_zero(p: u8, q: u8)
    ensures
        (p | q) == 0 <==> (p == 0 && q == 0),
{
    assert((p | q) == 0 <==> (p == 0 && q == 0)) by (bit_vector);
}

/// RFC 8446 §4.4.4: compare two Finished verify_data values without a
/// data-dependent branch or early exit.
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> (out: bool)
    requires
        a.len() == b.len(),
    ensures
        out == (a@ == b@),
{
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            a@.len() == b@.len(),
            (acc == 0) <==> (forall|k: int| 0 <= k < i ==> a@[k] == b@[k]),
        decreases a@.len() - i,
    {
        let x = byte_at(a, i);
        let y = byte_at(b, i);
        proof {
            lemma_xor_zero(x, y);
            lemma_or_zero(acc, x ^ y);
        }
        acc |= x ^ y;
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        if acc == 0 {
            assert(a@ =~= b@);
        }
    }
    acc == 0
}

} // verus!
