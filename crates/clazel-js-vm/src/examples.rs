//! The standard's results, evaluated on the spec with `compute_only`. Kept
//! apart from [`super::lemmas`] so that a mutant that breaks one of them does
//! not stop Verus before it checks a kill certificate there
//! (`mutations.json`).
//!
//! - [`example_multiply_zero_signs`]: the sign of a zero product (steps 4
//!   and 5 and the step 5a erratum of Number::multiply).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sign of a zero product, §6.1.6.1.4: `-0 × 5` is `-0` (step 4.b),
/// `5 × -0` is `-0` (step 5.b), `-0 × -5` is `+0` (step 4.a), and `+0 × -5`
/// is `-0` (the step 5a erratum, docs/ERRATA.md).
pub proof fn example_multiply_zero_signs()
    ensures
        number_multiply(0x8000_0000_0000_0000u64, 0x4014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
        number_multiply(0x4014_0000_0000_0000u64, 0x8000_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
        number_multiply(0x8000_0000_0000_0000u64, 0xC014_0000_0000_0000u64) == 0u64,
        number_multiply(0u64, 0xC014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64,
{
    assert(number_multiply(0x8000_0000_0000_0000u64, 0x4014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
    assert(number_multiply(0x4014_0000_0000_0000u64, 0x8000_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
    assert(number_multiply(0x8000_0000_0000_0000u64, 0xC014_0000_0000_0000u64) == 0u64) by (compute_only);
    assert(number_multiply(0u64, 0xC014_0000_0000_0000u64) == 0x8000_0000_0000_0000u64) by (compute_only);
}

} // verus!
