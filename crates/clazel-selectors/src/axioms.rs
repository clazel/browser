//! The one fact about `Vec` that Verus's model of the standard library leaves out: a vector
//! never holds `usize::MAX` elements.

#[cfg(verus_only)]
use super::exec_types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The arrays of parsed selectors are shorter than `usize::MAX`, which [`ranges_wf`] needs of
/// them (`usize` arithmetic on an index must not overflow) and no parse can disprove. Each array
/// holds elements of non-zero size (`ExecSimple`, `ExecRange`, `Combinator`, `ExecComplex`),
/// and Rust never allocates more than `isize::MAX` bytes for one `Vec` (the `Vec`
/// documentation; `RawVec` panics with "capacity overflow"), so a length is below
/// `isize::MAX`, which is below `usize::MAX`. `vstd` says only that a length fits a `usize`.
// AXIOM: a `Vec` of non-zero-size elements has fewer than `usize::MAX` elements (Rust's allocator limit).
#[verifier::external_body]
pub proof fn axiom_lengths(s: &ExecSelectors)
    ensures
        s.simples.len() < usize::MAX,
        s.compounds.len() < usize::MAX,
        s.combinators.len() < usize::MAX,
        s.complexes.len() < usize::MAX,
        s.lists.len() < usize::MAX,
{
}

} // verus!
