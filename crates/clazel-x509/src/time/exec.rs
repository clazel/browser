//! Executable RFC 5280 §4.1.2.5.1/.2 time-content decoder.

use super::spec as time_spec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// ASN.1 time kind selected by the already-validated DER tag.
pub enum TimeKind {
    /// Two-digit-year UTCTime.
    Utc,
    /// Four-digit-year GeneralizedTime.
    Generalized,
}

impl View for TimeKind {
    type V = time_spec::TimeKind;
    closed spec fn view(&self) -> Self::V {
        match self {
            TimeKind::Utc => time_spec::TimeKind::Utc,
            TimeKind::Generalized => time_spec::TimeKind::Generalized,
        }
    }
}

/// Parsed calendar fields at whole-second precision.
pub struct CertificateTime {
    /// Four-digit Gregorian year.
    pub year: u16,
    /// Month of year, 1 through 12.
    pub month: u8,
    /// Day of month, validated against the Gregorian month length.
    pub day: u8,
    /// Hour of day, 0 through 23.
    pub hour: u8,
    /// Minute of hour, 0 through 59.
    pub minute: u8,
/// Second of minute, 0 through 59, or 60 at a modeled leap second.
    pub second: u8,
}

impl View for CertificateTime {
    type V = time_spec::CertificateTime;
    closed spec fn view(&self) -> Self::V {
        time_spec::CertificateTime {
            year: self.year,
            month: self.month,
            day: self.day,
            hour: self.hour,
            minute: self.minute,
            second: self.second,
        }
    }
}

/// RFC 5280 §4.1.2.5.1/.2 numeric time fields: read ASCII digits at a fixed
/// offset using ordinary base-10 place values.
fn read_number(input: &[u8], pos: usize, count: usize) -> (result: Option<u32>)
    requires
        pos <= input.len(),
        count <= 4,
        pos + count <= input.len(),
        super::spec::digits_only(input@, pos as int, count as int),
    ensures
        result == Some(super::spec::decimal_digits(input@, pos as int, count as int) as u32),
        match result {
            Some(value) => count <= 2 ==> value < 100,
            None => false,
        },
        match result {
            Some(value) => value < 10000,
            None => false,
        }
{
    let mut value: u32 = 0;
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            count <= 4,
            pos + count <= input.len(),
            super::spec::digits_only(input@, pos as int, count as int),
            value as nat == super::spec::decimal_value(
                input@.subrange(pos as int, (pos + i) as int)),
            i == 0 ==> value == 0,
            i <= 1 ==> value < 10,
            i <= 2 ==> value < 100,
            i <= 3 ==> value < 1000,
            value < 10000,
        decreases count - i
    {
        let index = pos.saturating_add(i);
        let byte = *input.get(index)?;
        let digit = byte.saturating_sub(b'0');
        assert(input@.subrange(pos as int, (pos + i + 1) as int).drop_last()
            =~= input@.subrange(pos as int, (pos + i) as int));
        assert(input@.subrange(pos as int, (pos + i + 1) as int).last()
            == input@[(pos + i) as int]);
        value = value.saturating_mul(10).saturating_add(digit as u32);
        i = i.saturating_add(1);
    }
    Some(value)
}

/// Check the RFC 5280 §4.1.2.5 time contents against the ASCII digit fields
/// of the UTCTime and GeneralizedTime productions.
fn digits_only_exec(input: &[u8], pos: usize, count: usize) -> (result: bool)
    requires pos <= input.len(), pos + count <= input.len()
    ensures result == super::spec::digits_only(input@, pos as int, count as int)
{
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            pos + count <= input.len(),
            forall|k: int| pos as int <= k < pos as int + i as int
                ==> b'0' <= input@[k] && input@[k] <= b'9',
        decreases count - i,
    {
        let index = pos.saturating_add(i);
        let byte = match input.get(index) {
            Some(byte) => *byte,
            None => return false,
        };
        if !is_ascii_digit_exec(byte) {
            assert(!super::spec::digits_only(input@, pos as int, count as int));
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// RFC 5280 §4.1.2.5.1/.2 date-time digits are ASCII decimal digits.
fn is_ascii_digit_exec(byte: u8) -> (result: bool)
    ensures result == (b'0' <= byte && byte <= b'9')
{
    match byte.checked_sub(b'0') {
        Some(digit) => digit <= 9,
        None => false,
    }
}

/// Gregorian leap-year rule used by RFC 5280 §4.1.2.5 calendar validation.
fn is_leap_year(year: u16) -> (result: bool)
    ensures result == time_spec::is_leap_year(year as nat)
{
    year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400))
}

/// Gregorian month length for RFC 5280 §4.1.2.5 calendar validation; zero
/// for a month outside 1..=12.
fn days_in_month(year: u16, month: u8) -> (result: u8)
    ensures result as nat == time_spec::days_in_month(year as nat, month as nat)
{
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => if is_leap_year(year) { 29 } else { 28 },
        _ => 0,
    }
}

/// RFC 5280 §4.1.2.5 Gregorian date and clock-field checks. GeneralizedTime's
/// second 60 is retained only at the 23:59 leap-second position (X.680 §46.3).
fn calendar_time_valid(time: &CertificateTime) -> (result: bool)
    ensures result == time_spec::calendar_time_valid(time@)
{
    time.year >= 1 && time.year <= 9999
        && time.month >= 1 && time.month <= 12
        && time.day >= 1 && time.day <= days_in_month(time.year, time.month)
        && time.hour <= 23 && time.minute <= 59
        && (time.second <= 59 || time.second == 60 && time.hour == 23 && time.minute == 59)
}

/// Compare fixed-width UTC calendar fields lexicographically.
fn time_le(left: &CertificateTime, right: &CertificateTime) -> (result: bool)
    ensures result == time_spec::time_le(left@, right@)
{
    left.year < right.year
        || left.year == right.year && (left.month < right.month
        || left.month == right.month && (left.day < right.day
        || left.day == right.day && (left.hour < right.hour
        || left.hour == right.hour && (left.minute < right.minute
        || left.minute == right.minute && left.second <= right.second))))
}

/// RFC 5280 §4.1.2.5.1/.2: decode one complete UTCTime or GeneralizedTime
/// contents string under the profile's exact whole-second UTC form.
pub fn decode_time(input: &[u8], kind: TimeKind) -> (result: Option<CertificateTime>)
    ensures
        super::contract::decode_time_ensures(
            kind@, input@, view_time_result(result))
{
    let expected_len = match kind {
        TimeKind::Utc => 13,
        TimeKind::Generalized => 15,
    };
    // 1. Check the profile's exact field length.
    if input.len() != expected_len {
        return None;
    }
    let z_index = expected_len.checked_sub(1)?;
    // 2. RFC 5280 §4.1.2.5.1/.2 and X.690 §11.7.1/11.8.1 require Z.
    if *input.get(z_index)? != b'Z' {
        return None;
    }
    // 3. The date/time fields contain decimal digits only.
    if !digits_only_exec(input, 0, z_index) {
        return None;
    }

    // 4. Parse the year, applying RFC 5280 §4.1.2.5.1's UTC pivot.
    let (year, month_pos) = match kind {
        TimeKind::Utc => {
            let yy_value = read_number(input, 0, 2)?;
            assert(yy_value <= 99);
            let yy = yy_value as u16;
            let year = if yy >= 50 { 1900u16.checked_add(yy)? } else { 2000u16.checked_add(yy)? };
            (year, 2usize)
        },
        TimeKind::Generalized => {
            let year_value = read_number(input, 0, 4)?;
            assert(year_value <= 9999);
            (year_value as u16, 4usize)
        },
    };
    // 5. Parse MM, DD, hh, mm, and ss; offsets and fractions cannot fit.
    let day_pos = month_pos.checked_add(2)?;
    let hour_pos = month_pos.checked_add(4)?;
    let minute_pos = month_pos.checked_add(6)?;
    let second_pos = month_pos.checked_add(8)?;
    let month_value = read_number(input, month_pos, 2)?;
    let day_value = read_number(input, day_pos, 2)?;
    let hour_value = read_number(input, hour_pos, 2)?;
    let minute_value = read_number(input, minute_pos, 2)?;
    let second_value = read_number(input, second_pos, 2)?;
    assert(month_value <= 99 && day_value <= 99 && hour_value <= 99
        && minute_value <= 99 && second_value <= 99);
    assert(month_value < 256 && day_value < 256 && hour_value < 256
        && minute_value < 256 && second_value < 256);
    proof {
        super::lemmas::lemma_decimal_digits_bound(input@, month_pos as int, 2);
        super::lemmas::lemma_decimal_digits_bound(input@, month_pos as int + 2, 2);
        super::lemmas::lemma_decimal_digits_bound(input@, month_pos as int + 4, 2);
        super::lemmas::lemma_decimal_digits_bound(input@, month_pos as int + 6, 2);
        super::lemmas::lemma_decimal_digits_bound(input@, month_pos as int + 8, 2);
        assert(super::lemmas::decimal_power10(2) == 100) by (compute_only);
    }
    assert(month_value == time_spec::decimal_digits(input@, month_pos as int, 2) as u32);
    assert(day_value == time_spec::decimal_digits(input@, month_pos as int + 2, 2) as u32);
    assert(hour_value == time_spec::decimal_digits(input@, month_pos as int + 4, 2) as u32);
    assert(minute_value == time_spec::decimal_digits(input@, month_pos as int + 6, 2) as u32);
    assert(second_value == time_spec::decimal_digits(input@, month_pos as int + 8, 2) as u32);
    assert(time_spec::decimal_digits(input@, month_pos as int, 2) < 100);
    assert(time_spec::decimal_digits(input@, month_pos as int + 2, 2) < 100);
    assert(month_value as nat == time_spec::decimal_digits(input@, month_pos as int, 2));
    assert(day_value as nat == time_spec::decimal_digits(input@, month_pos as int + 2, 2));
    let month = month_value as u8;
    let day = day_value as u8;
    let hour = hour_value as u8;
    let minute = minute_value as u8;
    let second = second_value as u8;
    assert(month as nat == month_value as nat);
    assert(day as nat == day_value as nat);
    assert(hour as nat == hour_value as nat);
    assert(minute as nat == minute_value as nat);
    assert(second as nat == second_value as nat);

    let time = CertificateTime { year, month, day, hour, minute, second };
    assert(time.month as nat == time_spec::decimal_digits(input@, month_pos as int, 2));
    assert(time.day as nat == time_spec::decimal_digits(input@, day_pos as int, 2));
    assert(time.hour as nat == time_spec::decimal_digits(input@, hour_pos as int, 2));
    assert(time.minute as nat == time_spec::decimal_digits(input@, minute_pos as int, 2));
    assert(time.second as nat == time_spec::decimal_digits(input@, second_pos as int, 2));
    proof {
        match kind {
            TimeKind::Utc => {
                super::lemmas::lemma_decimal_digits_bound(input@, 0 as int, 2 as int);
                assert(super::lemmas::decimal_power10(2) == 100) by (compute_only);
                if time_spec::decimal_digits(input@, 0 as int, 2 as int) >= 50 {
                    assert(year as nat == 1900 + time_spec::decimal_digits(input@, 0 as int, 2 as int));
                } else {
                    assert(year as nat == 2000 + time_spec::decimal_digits(input@, 0 as int, 2 as int));
                }
            },
            TimeKind::Generalized => {
                super::lemmas::lemma_decimal_digits_bound(input@, 0 as int, 4 as int);
                assert(super::lemmas::decimal_power10(4) == 10000) by (compute_only);
                assert(year as nat == time_spec::decimal_digits(input@, 0 as int, 4 as int));
            },
        }
    }
    assert(time_spec::decode_time(kind@, input@) == if time_spec::calendar_time_valid(time@)
        && (kind@ == time_spec::TimeKind::Generalized || time.second <= 59) {
        Some(time@)
    } else {
        None
    });
    let second_allowed = match kind {
        TimeKind::Utc => time.second <= 59,
        TimeKind::Generalized => true,
    };
    if calendar_time_valid(&time) && second_allowed { Some(time) } else { None }
}

/// Executable view adapter used by the refinement contract.
pub open spec fn view_time_result(result: Option<CertificateTime>) -> Option<time_spec::CertificateTime> {
    match result {
        Some(time) => Some(time@),
        None => None,
    }
}

/// Construct a validity interval iff both endpoints are valid and ordered.
pub fn make_validity(
    not_before: CertificateTime, not_after: CertificateTime,
) -> (result: Option<Validity>)
    ensures super::contract::make_validity_ensures(
        not_before@, not_after@, view_validity_result(result))
{
    if !calendar_time_valid(&not_before)
        || !calendar_time_valid(&not_after)
        || !time_le(&not_before, &not_after) {
        None
    } else {
        Some(Validity { not_before, not_after })
    }
}

/// Inclusive validity interval with decoded endpoints.
pub struct Validity {
    /// Inclusive start of the certificate validity interval.
    pub not_before: CertificateTime,
    /// Inclusive end of the certificate validity interval.
    pub not_after: CertificateTime,
}

impl View for Validity {
    type V = time_spec::Validity;
    closed spec fn view(&self) -> Self::V {
        time_spec::Validity { not_before: self.not_before@, not_after: self.not_after@ }
    }
}

pub open spec fn view_validity_result(result: Option<Validity>) -> Option<time_spec::Validity> {
    match result {
        Some(validity) => Some(validity@),
        None => None,
    }
}

/// RFC 5280 §4.1.2.5: accept the inclusive interval notBefore <= now <=
/// notAfter, after confirming its endpoints are valid and ordered.
pub fn validity_contains(validity: Validity, now: CertificateTime) -> (result: bool)
    ensures super::contract::validity_contains_ensures(validity@, now@, result)
{
    calendar_time_valid(&validity.not_before)
        && calendar_time_valid(&validity.not_after)
        && time_le(&validity.not_before, &validity.not_after)
        && calendar_time_valid(&now)
        && time_le(&validity.not_before, &now)
        && time_le(&now, &validity.not_after)
}

} // verus!
