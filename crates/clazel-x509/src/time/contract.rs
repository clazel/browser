//! Contracts for RFC 5280 certificate validity-time decoding.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Executable time decoding returns exactly the calendar value specified by
/// RFC 5280 §4.1.2.5 for the selected ASN.1 time type and complete contents.
pub open spec fn decode_time_ensures(
    kind: TimeKind, bytes: Seq<u8>, output: Option<CertificateTime>,
) -> bool {
    output == decode_time(kind, bytes)
}

/// Constructing a validity interval accepts only valid endpoints in
/// nondecreasing order; the RFC interval includes both endpoints.
pub open spec fn make_validity_ensures(
    not_before: CertificateTime,
    not_after: CertificateTime,
    output: Option<Validity>,
) -> bool {
    output == make_validity(not_before, not_after)
}

/// The interval predicate accepts exactly valid `now` values in the
/// inclusive ordering range.
pub open spec fn validity_contains_ensures(
    validity: Validity, now: CertificateTime, output: bool,
) -> bool {
    output == validity_contains(validity, now)
}

} // verus!
