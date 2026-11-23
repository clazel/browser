//! Which sets of code lengths [`super::spec::code_usable`] accepts.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Which sets of code lengths are usable (the header's "Prefix codes that are
// not complete").
// ---------------------------------------------------------------------------

/// `code_usable` on small sets of lengths: complete codes are usable; one
/// code of length 1 or none are usable for the literal/length and distance
/// codes only; anything else (incomplete, over-subscribed, too long) is not.
pub proof fn lemma_code_usable_cases()
    ensures
        code_usable(seq![1nat, 1nat], false),
        code_usable(seq![2nat, 2nat, 1nat], false),
        code_usable(seq![1nat], true),
        code_usable(seq![0nat, 0nat], true),
        !code_usable(seq![1nat], false),
        !code_usable(seq![2nat], true),
        !code_usable(seq![2nat], false),
        !code_usable(seq![1nat, 1nat, 1nat], true),
        !code_usable(seq![1nat, 1nat, 16nat], false),
{
    assert(code_usable(seq![1nat, 1nat], false)) by (compute_only);
    assert(code_usable(seq![2nat, 2nat, 1nat], false)) by (compute_only);
    assert(code_usable(seq![1nat], true)) by (compute_only);
    assert(code_usable(seq![0nat, 0nat], true)) by (compute_only);
    assert(!code_usable(seq![1nat], false)) by (compute_only);
    assert(!code_usable(seq![2nat], true)) by (compute_only);
    assert(!code_usable(seq![2nat], false)) by (compute_only);
    assert(!code_usable(seq![1nat, 1nat, 1nat], true)) by (compute_only);
    assert(!code_usable(seq![1nat, 1nat, 16nat], false)) by (compute_only);
}

} // verus!
