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


/// RFC 5280's UTCTime pivot maps `50` to 1950.
pub proof fn lemma_utc_pivot_50_is_1950()
    ensures utc_year(50) == 1950
{
    assert(utc_year(50) == 1950) by (compute_only);
}

/// UTCTime's seconds profile rejects 60.
pub proof fn lemma_reject_utc_second_60()
    ensures !utc_seconds_valid(CertificateTime {
        year: 2016, month: 12, day: 31, hour: 23, minute: 59, second: 60,
    })
{
    assert(!utc_seconds_valid(CertificateTime {
        year: 2016, month: 12, day: 31, hour: 23, minute: 59, second: 60,
    })) by (compute_only);
}

/// A certificate validity interval with reversed endpoints is rejected.
pub proof fn lemma_reject_reversed_validity()
    ensures make_validity(
        CertificateTime { year: 2021, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
        CertificateTime { year: 2020, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
    ) is None
{
    assert(make_validity(
        CertificateTime { year: 2021, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
        CertificateTime { year: 2020, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
    ) is None) by (compute_only);
}

/// RFC 5280 includes both validity endpoints.
pub proof fn lemma_validity_accepts_inclusive_end()
    ensures validity_contains(
        Validity {
            not_before: CertificateTime { year: 2020, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            not_after: CertificateTime { year: 2020, month: 1, day: 2, hour: 0, minute: 0, second: 0 },
        },
        CertificateTime { year: 2020, month: 1, day: 2, hour: 0, minute: 0, second: 0 },
    )
{
    assert(validity_contains(
        Validity {
            not_before: CertificateTime { year: 2020, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            not_after: CertificateTime { year: 2020, month: 1, day: 2, hour: 0, minute: 0, second: 0 },
        },
        CertificateTime { year: 2020, month: 1, day: 2, hour: 0, minute: 0, second: 0 },
    )) by (compute_only);
}


} // verus!
