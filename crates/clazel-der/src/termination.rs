//! Termination of the recursive subidentifier loop in [`super::spec`].
//! Verus needs this fact to accept the spec's `decreases` clause (it names a
//! `via` function in `spec.rs`, which only calls this); it says nothing else
//! about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A series that ends ends at an index in `[i, end)`.
pub proof fn lemma_series_end_bounds(b: Seq<u8>, i: nat, end: nat)
    ensures
        match series_end(b, i, end) {
            Some(j) => i <= j && j < end,
            None => true,
        },
    decreases end - i,
{
    if i < end && b[i as int] >= 128 {
        lemma_series_end_bounds(b, i + 1, end);
    }
}

} // verus!
