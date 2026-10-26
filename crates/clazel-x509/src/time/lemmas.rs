//! Arithmetic facts used by the verified time-content decoder.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Ten to a decimal digit count.
pub open spec fn decimal_power10(count: nat) -> nat
    decreases count
{
    if count == 0 { 1 } else { 10 * decimal_power10((count - 1) as nat) }
}

/// A decimal string of length n denotes a value less than 10^n.
pub proof fn lemma_decimal_value_bound(bytes: Seq<u8>)
    requires
        forall|i: int| 0 <= i < bytes.len()
            ==> b'0' <= bytes[i] && bytes[i] <= b'9',
    ensures decimal_value(bytes) < decimal_power10(bytes.len()),
    decreases bytes.len()
{
    if bytes.len() > 0 {
        lemma_decimal_value_bound(bytes.drop_last());
        assert(bytes.drop_last().len() + 1 == bytes.len());
        assert(bytes.last() >= b'0' && bytes.last() <= b'9');
    }
}

/// A bounded range of n decimal bytes denotes a value less than 10^n.
pub proof fn lemma_decimal_digits_bound(bytes: Seq<u8>, pos: int, count: int)
    requires
        0 <= pos && 0 <= count && pos + count <= bytes.len(),
        digits_only(bytes, pos, count),
    ensures decimal_digits(bytes, pos, count) < decimal_power10(count as nat),
{
    lemma_decimal_value_bound(bytes.subrange(pos, pos + count));
}

} // verus!
