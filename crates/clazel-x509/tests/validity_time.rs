//! RFC 5280 §4.1.2.5 time decoding boundaries and adversarial encodings.

use clazel_x509::time::exec::{
    decode_time, make_validity, validity_contains, CertificateTime, TimeKind,
};

fn utc(value: &[u8]) -> Option<CertificateTime> {
    decode_time(value, TimeKind::Utc)
}

fn generalized(value: &[u8]) -> Option<CertificateTime> {
    decode_time(value, TimeKind::Generalized)
}

#[test]
fn utc_century_pivot_is_1950_through_2049() {
    assert_eq!(utc(b"500101000000Z").map(|t| t.year), Some(1950));
    assert_eq!(utc(b"491231235959Z").map(|t| t.year), Some(2049));
    assert_eq!(utc(b"000101000000Z").map(|t| t.year), Some(2000));
    assert_eq!(utc(b"990101000000Z").map(|t| t.year), Some(1999));
}

#[test]
fn generalized_time_is_four_digit_and_application_processes_either_type() {
    assert_eq!(generalized(b"20500101000000Z").map(|t| t.year), Some(2050));
    // RFC 5280 requires issuers to use UTCTime through 2049, but applications
    // must process both encodings; that issuer choice is not a decoder gate.
    assert_eq!(generalized(b"20491231235959Z").map(|t| t.year), Some(2049));
    assert_eq!(generalized(b"99991231235959Z").map(|t| t.year), Some(9999));
    assert!(generalized(b"00000101000000Z").is_none());
}

#[test]
fn validates_gregorian_month_lengths_and_century_leap_years() {
    assert!(generalized(b"20000229000000Z").is_some());
    assert!(generalized(b"19000229000000Z").is_none());
    assert!(generalized(b"20000230000000Z").is_none());
    assert!(generalized(b"20240430000000Z").is_some());
    assert!(generalized(b"20240431000000Z").is_none());
}

#[test]
fn requires_exact_profile_syntax_and_handles_leap_seconds_by_type() {
    assert!(generalized(b"20161231235960Z").is_some());

    for invalid in [
        &b"500101000000+0000"[..], // offset
        &b"5001010000Z"[..],       // missing seconds
        &b"500101000000z"[..],     // lowercase z
        &b"500101000000ZZ"[..],    // trailing byte
        &b"5x0101000000Z"[..],     // non-digit
        &b"500132000000Z"[..],     // invalid day
        &b"500101240000Z"[..],     // invalid hour
        &b"500101000060Z"[..],     // leap second outside this profile
    ] {
        assert!(utc(invalid).is_none(), "accepted {invalid:?}");
    }

    for invalid in [
        &b"20500101000000+0000"[..], // offset
        &b"205001010000Z"[..],       // missing seconds
        &b"20500101000000.0Z"[..],   // fractional seconds
        &b"20500101000000ZZ"[..],    // trailing byte
        &b"2050010100006XZ"[..],     // non-digit
        &b"20501301000000Z"[..],     // invalid month
        &b"20500101240000Z"[..],     // invalid hour
        &b"20500101000060Z"[..],     // second 60 is valid only at 23:59
    ] {
        assert!(generalized(invalid).is_none(), "accepted {invalid:?}");
    }
}

#[test]
fn interval_endpoints_are_inclusive_and_reversed_ranges_fail() {
    let before = generalized(b"20500101000000Z");
    let after = generalized(b"20500101000002Z");
    assert!(before.is_some() && after.is_some());
    let (Some(before), Some(after)) = (before, after) else {
        return;
    };
    let same = generalized(b"20500101000000Z");
    assert!(same.is_some());
    let Some(same) = same else {
        return;
    };
    let interval = make_validity(before, after);
    assert!(interval.is_some());
    let Some(interval) = interval else {
        return;
    };
    assert!(validity_contains(interval, same));

    let before = generalized(b"20500101000000Z");
    let after = generalized(b"20500101000002Z");
    assert!(before.is_some() && after.is_some());
    let (Some(before), Some(after)) = (before, after) else {
        return;
    };
    let interval = make_validity(before, after);
    assert!(interval.is_some());
    let Some(interval) = interval else {
        return;
    };
    let end = generalized(b"20500101000002Z");
    assert!(end.is_some());
    let Some(end) = end else {
        return;
    };
    assert!(validity_contains(interval, end));

    let later = generalized(b"20500101000002Z");
    let earlier = generalized(b"20500101000000Z");
    assert!(later.is_some() && earlier.is_some());
    let (Some(later), Some(earlier)) = (later, earlier) else {
        return;
    };
    assert!(make_validity(later, earlier).is_none());
}
