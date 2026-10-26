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

/// RFC 8446 §4.4.4: compare two Finished verify_data values without a
/// data-dependent branch or early exit.
pub fn constant_time_eq(a: &[u8], b: &[u8]) -> (out: bool)
    requires
        a.len() == b.len(),
    ensures
        out == (a@ == b@),
{
    // Contract-only stub (spec commit): the proof follows in the next commit.
    false
}

} // verus!
