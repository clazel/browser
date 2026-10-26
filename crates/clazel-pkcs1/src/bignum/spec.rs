//! What a limb sequence denotes. A number is a little-endian `Vec<u64>`:
//! limb 0 is the least significant, and `value` is
//! `limb[0] + limb[1] 2^64 + limb[2] 2^128 + ...`. Leading (high) zero
//! limbs are allowed; the length of a number is part of its type in the
//! contracts, not of its value.
//!
//! This file is our own definition (RFC 8017 does not specify the
//! arithmetic); `independent.rs` re-derives the arithmetic from the
//! Handbook of Applied Cryptography and proves the two agree.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The radix, 2^64.
pub open spec fn base() -> nat {
    0x1_0000_0000_0000_0000nat
}

/// `base()^i`, the weight of limb `i`.
pub open spec fn limb_pow(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        1
    } else {
        limb_pow((i - 1) as nat) * base()
    }
}

/// The number a little-endian limb sequence denotes.
pub open spec fn value(s: Seq<u64>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        value(s.drop_last()) + (s.last() as nat) * limb_pow((s.len() - 1) as nat)
    }
}

} // verus!
