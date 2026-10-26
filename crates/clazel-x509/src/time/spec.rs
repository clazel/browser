//! RFC 5280 §4.1.2.5 certificate validity-time specification.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2.5>
//!
//! X.690 (02/2021) §§11.7–11.8 additionally specify DER time encoding:
//! <https://www.itu.int/rec/T-REC-X.690-202102-I/en>
//!
//! Modelling choices and limits:
//! - Inputs are the contents octets of an already tag-checked DER UTCTime or
//!   GeneralizedTime value. Tag, length, and DER structure are checked by
//!   clazel-der; this function checks the complete content string.
//! - The result is Gregorian calendar fields rather than a Unix timestamp.
//!   This preserves year 1..=9999 and permits direct total ordering without
//!   platform time libraries or epoch overflow.
//! - GeneralizedTime is accepted in any supported year, and UTCTime is
//!   interpreted by RFC 5280's two-digit pivot. RFC 5280 requires issuers to
//!   encode through 2049 as UTCTime and from 2050 as GeneralizedTime, but
//!   requires applications to process either encoding; this decoder does not
//!   reject a parseable value based on its encoding/year pair.
//! - Gregorian years are 1..=9999. Seconds are 0..=59: the RFC 5280 profile
//!   does not specify leap-second handling, and this calendar representation
//!   models ordinary Gregorian civil seconds only. It therefore rejects a
//!   second value of 60 rather than aliasing it to the next minute.
//! - UTCTime content is exactly YYMMDDHHMMSSZ; GeneralizedTime content is
//!   exactly YYYYMMDDHHMMSSZ. Offsets, fractions, omitted seconds, extra
//!   bytes, and non-ASCII digits are rejected as outside RFC 5280's profile.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Calendar fields for one whole-second UTC instant.
pub struct CertificateTime {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: u8,
    pub second: u8,
}

/// ASN.1 time type from the already-checked DER universal tag.
pub enum TimeKind {
    Utc,
    Generalized,
}

/// Gregorian leap-year rule, using the proleptic Gregorian calendar.
pub open spec fn is_leap_year(year: nat) -> bool {
    year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
}

/// Number of days in a Gregorian month (zero for an invalid month).
pub open spec fn days_in_month(year: nat, month: nat) -> nat {
    if month == 1 || month == 3 || month == 5 || month == 7
        || month == 8 || month == 10 || month == 12 { 31 }
    else if month == 4 || month == 6 || month == 9 || month == 11 { 30 }
    else if month == 2 { if is_leap_year(year) { 29 } else { 28 } }
    else { 0 }
}

/// True exactly for representable Gregorian whole-second civil times.
pub open spec fn calendar_time_valid(time: CertificateTime) -> bool {
    1 <= time.year as nat && time.year as nat <= 9999
        && 1 <= time.month as nat && time.month as nat <= 12
        && 1 <= time.day as nat
        && time.day as nat <= days_in_month(time.year as nat, time.month as nat)
        && time.hour <= 23 && time.minute <= 59 && time.second <= 59
}

/// Decimal value of `count` ASCII digits beginning at `pos`.
pub open spec fn decimal_digits(bytes: Seq<u8>, pos: int, count: int) -> nat
    recommends 0 <= pos && 0 <= count && pos + count <= bytes.len()
    decreases count
{
    if count == 0 { 0 }
    else { (bytes[pos] - b'0') as nat * pow10((count - 1) as nat)
        + decimal_digits(bytes, pos + 1, count - 1) }
}

/// Small exponentiation for decimal digit parsing.
pub open spec fn pow10(power: nat) -> nat
    decreases power
{
    if power == 0 { 1 } else { 10 * pow10(power - 1) }
}

/// All bytes in a bounded range are ASCII decimal digits.
pub open spec fn digits_only(bytes: Seq<u8>, pos: int, count: int) -> bool
    recommends 0 <= pos && 0 <= count && pos + count <= bytes.len()
    decreases count
{
    if count == 0 { true }
    else { b'0' <= bytes[pos] && bytes[pos] <= b'9'
        && digits_only(bytes, pos + 1, count - 1) }
}

/// UTCTime or GeneralizedTime content under the RFC 5280 §4.1.2.5 profile.
pub open spec fn decode_time(kind: TimeKind, bytes: Seq<u8>) -> Option<CertificateTime> {
    match kind {
        TimeKind::Utc => {
            if bytes.len() != 13 || bytes[12] != b'Z' || !digits_only(bytes, 0, 12) { None }
            else {
                let yy = decimal_digits(bytes, 0, 2);
                let year = if yy >= 50 { 1900 + yy } else { 2000 + yy };
                let time = CertificateTime {
                    year: year as u16,
                    month: decimal_digits(bytes, 2, 2) as u8,
                    day: decimal_digits(bytes, 4, 2) as u8,
                    hour: decimal_digits(bytes, 6, 2) as u8,
                    minute: decimal_digits(bytes, 8, 2) as u8,
                    second: decimal_digits(bytes, 10, 2) as u8,
                };
                if calendar_time_valid(time) { Some(time) } else { None }
            }
        },
        TimeKind::Generalized => {
            if bytes.len() != 15 || bytes[14] != b'Z' || !digits_only(bytes, 0, 14) { None }
            else {
                let time = CertificateTime {
                    year: decimal_digits(bytes, 0, 4) as u16,
                    month: decimal_digits(bytes, 4, 2) as u8,
                    day: decimal_digits(bytes, 6, 2) as u8,
                    hour: decimal_digits(bytes, 8, 2) as u8,
                    minute: decimal_digits(bytes, 10, 2) as u8,
                    second: decimal_digits(bytes, 12, 2) as u8,
                };
                if calendar_time_valid(time) { Some(time) } else { None }
            }
        },
    }
}

/// Lexicographic ordering of fixed-width Gregorian UTC fields.
pub open spec fn time_le(left: CertificateTime, right: CertificateTime) -> bool {
    left.year < right.year
        || left.year == right.year && (left.month < right.month
        || left.month == right.month && (left.day < right.day
        || left.day == right.day && (left.hour < right.hour
        || left.hour == right.hour && (left.minute < right.minute
        || left.minute == right.minute && left.second <= right.second))))
}

/// A well-formed inclusive certificate validity interval.
pub struct Validity {
    pub not_before: CertificateTime,
    pub not_after: CertificateTime,
}

/// Construct a validity interval iff both endpoints are valid and ordered.
pub open spec fn make_validity(
    not_before: CertificateTime, not_after: CertificateTime,
) -> Option<Validity> {
    if calendar_time_valid(not_before) && calendar_time_valid(not_after)
        && time_le(not_before, not_after) {
        Some(Validity { not_before, not_after })
    } else { None }
}

/// RFC 5280 §4.1.2.5: the validity interval includes both endpoints.
pub open spec fn validity_contains(validity: Validity, now: CertificateTime) -> bool {
    calendar_time_valid(now)
        && time_le(validity.not_before, now)
        && time_le(now, validity.not_after)
}

} // verus!
