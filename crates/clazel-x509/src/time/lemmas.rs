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

/// If validity construction rejects the endpoints, no captured time is inside
/// the corresponding inclusive interval.
pub proof fn lemma_make_validity_none_excludes_time(
    not_before: CertificateTime, not_after: CertificateTime, now: CertificateTime,
)
    requires make_validity(not_before, not_after) is None
    ensures !validity_contains(Validity { not_before, not_after }, now)
{
    reveal(make_validity);
    reveal(validity_contains);
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

// Known answers, each checked independently with Python's `calendar.timegm`.

/// Example: Unix time 0.
pub proof fn lemma_example_epoch()
    ensures from_unix_seconds(0) == Some(CertificateTime { year: 1970, month: 1, day: 1, hour: 0, minute: 0, second: 0 })
{
    assert(from_unix_seconds(0) == Some(CertificateTime { year: 1970, month: 1, day: 1, hour: 0, minute: 0, second: 0 })) by (compute_only);
}

/// Example: Unix time 951782400.
pub proof fn lemma_example_2000_02_29()
    ensures from_unix_seconds(951782400) == Some(CertificateTime { year: 2000, month: 2, day: 29, hour: 0, minute: 0, second: 0 })
{
    assert(from_unix_seconds(951782400) == Some(CertificateTime { year: 2000, month: 2, day: 29, hour: 0, minute: 0, second: 0 })) by (compute_only);
}

/// Example: Unix time 951868800.
pub proof fn lemma_example_2000_03_01()
    ensures from_unix_seconds(951868800) == Some(CertificateTime { year: 2000, month: 3, day: 1, hour: 0, minute: 0, second: 0 })
{
    assert(from_unix_seconds(951868800) == Some(CertificateTime { year: 2000, month: 3, day: 1, hour: 0, minute: 0, second: 0 })) by (compute_only);
}

/// Example: Unix time 2147483647.
pub proof fn lemma_example_i32_max()
    ensures from_unix_seconds(2147483647) == Some(CertificateTime { year: 2038, month: 1, day: 19, hour: 3, minute: 14, second: 7 })
{
    assert(from_unix_seconds(2147483647) == Some(CertificateTime { year: 2038, month: 1, day: 19, hour: 3, minute: 14, second: 7 })) by (compute_only);
}

/// Example: Unix time 4107542400.
pub proof fn lemma_example_2100_03_01()
    ensures from_unix_seconds(4107542400) == Some(CertificateTime { year: 2100, month: 3, day: 1, hour: 0, minute: 0, second: 0 })
{
    assert(from_unix_seconds(4107542400) == Some(CertificateTime { year: 2100, month: 3, day: 1, hour: 0, minute: 0, second: 0 })) by (compute_only);
}



// ---------------------------------------------------------------------------
// Facts about `from_unix_seconds` (POSIX.1-2017 XBD §4.16 read backwards).
// ---------------------------------------------------------------------------

/// Days from the first day of `month` to the end of December in `year`.
pub open spec fn days_from_month(year: nat, month: nat) -> nat
    decreases 13 - month
{
    if month > 12 { 0 } else { days_in_month(year, month) + days_from_month(year, month + 1) }
}

/// Days in the years `year`, `year + 1`, ..., `year + count - 1`.
pub open spec fn days_in_years(year: nat, count: nat) -> nat
    decreases count
{
    if count == 0 { 0 } else { days_in_year(year) + days_in_years(year + 1, (count - 1) as nat) }
}

/// Days in 400 consecutive Gregorian years: the length of the calendar cycle.
pub open spec fn days_per_400_years() -> nat {
    146097
}

/// A Gregorian year is the sum of its twelve months.
pub proof fn lemma_days_in_year_is_sum_of_months(year: nat)
    ensures days_in_year(year) == days_from_month(year, 1),
{
    reveal_with_fuel(days_from_month, 14);
}

/// A month in 1..=12 is followed by the rest of the year, and is not empty.
pub proof fn lemma_days_from_month_step(year: nat, month: nat)
    requires 1 <= month <= 12,
    ensures
        days_from_month(year, month) == days_in_month(year, month) + days_from_month(year, month + 1),
        days_in_month(year, month) >= 28,
        month == 12 ==> days_from_month(year, 13) == 0,
{
}

/// The year walk stays at or above its start, and ends inside the year it
/// names.
pub proof fn lemma_year_of_day_bounds(days: nat, year: nat)
    ensures
        year <= year_of_day(days, year),
        day_in_year(days, year) < days_in_year(year_of_day(days, year)),
    decreases days
{
    if days >= days_in_year(year) {
        lemma_year_of_day_bounds((days - days_in_year(year)) as nat, year + 1);
    }
}

/// A day inside the first `count` years from `year` is in one of them.
pub proof fn lemma_year_of_day_within(days: nat, year: nat, count: nat)
    requires days < days_in_years(year, count),
    ensures year_of_day(days, year) < year + count,
    decreases count
{
    if days >= days_in_year(year) {
        lemma_year_of_day_within(
            (days - days_in_year(year)) as nat, year + 1, (count - 1) as nat);
    }
}

/// A later day is in a later year, or later in the same year.
pub proof fn lemma_year_of_day_strict(first: nat, second: nat, year: nat)
    requires first < second,
    ensures
        year_of_day(first, year) < year_of_day(second, year)
            || year_of_day(first, year) == year_of_day(second, year)
            && day_in_year(first, year) < day_in_year(second, year),
    decreases second
{
    if second >= days_in_year(year) {
        let rest = (second - days_in_year(year)) as nat;
        lemma_year_of_day_bounds(rest, year + 1);
        if first >= days_in_year(year) {
            lemma_year_of_day_strict((first - days_in_year(year)) as nat, rest, year + 1);
        }
    }
}

/// The month walk stays inside 1..=12 and ends inside the month it names.
pub proof fn lemma_month_of_day_bounds(day_of_year: nat, year: nat, month: nat)
    requires 1 <= month <= 12, day_of_year < days_from_month(year, month),
    ensures
        month <= month_of_day(day_of_year, year, month) <= 12,
        day_in_month(day_of_year, year, month)
            < days_in_month(year, month_of_day(day_of_year, year, month)),
    decreases 12 - month
{
    lemma_days_from_month_step(year, month);
    if month < 12 && day_of_year >= days_in_month(year, month) {
        lemma_month_of_day_bounds(
            (day_of_year - days_in_month(year, month)) as nat, year, month + 1);
    }
}

/// A later day of the year is in a later month, or later in the same month.
pub proof fn lemma_month_of_day_strict(first: nat, second: nat, year: nat, month: nat)
    requires 1 <= month <= 12, first < second, second < days_from_month(year, month),
    ensures
        month_of_day(first, year, month) < month_of_day(second, year, month)
            || month_of_day(first, year, month) == month_of_day(second, year, month)
            && day_in_month(first, year, month) < day_in_month(second, year, month),
    decreases 12 - month
{
    lemma_days_from_month_step(year, month);
    if month < 12 && second >= days_in_month(year, month) {
        let rest = (second - days_in_month(year, month)) as nat;
        lemma_month_of_day_bounds(rest, year, month + 1);
        if first >= days_in_month(year, month) {
            lemma_month_of_day_strict(
                (first - days_in_month(year, month)) as nat, rest, year, month + 1);
        }
    }
}

/// Gregorian leap years repeat every 400 years.
pub proof fn lemma_leap_year_period(year: nat)
    ensures is_leap_year(year + 400) == is_leap_year(year),
{
}

/// Sum over one more year at the end.
pub proof fn lemma_days_in_years_snoc(year: nat, count: nat)
    ensures days_in_years(year, count + 1) == days_in_years(year, count) + days_in_year(year + count),
    decreases count
{
    if count > 0 {
        lemma_days_in_years_snoc(year + 1, (count - 1) as nat);
        assert(days_in_years(year, count + 1)
            == days_in_year(year) + days_in_years(year + 1, count));
        assert(days_in_years(year, count)
            == days_in_year(year) + days_in_years(year + 1, (count - 1) as nat));
        assert(year + 1 + (count - 1) == year + count);
    } else {
        assert(days_in_years(year, 1) == days_in_year(year) + days_in_years(year + 1, 0));
    }
}

/// Every run of 400 consecutive Gregorian years has 146097 days.
pub proof fn lemma_days_in_400_years(year: nat)
    ensures days_in_years(year, 400) == days_per_400_years(),
    decreases year
{
    if year == 0 {
        assert(days_in_years(0, 400) == 146097) by (compute_only);
    } else {
        lemma_days_in_400_years((year - 1) as nat);
        lemma_days_in_years_snoc((year - 1) as nat, 400);
        lemma_leap_year_period((year - 1) as nat);
    }
}

/// Skipping `count` whole years at once.
pub proof fn lemma_year_of_day_skip(days: nat, year: nat, count: nat)
    requires days >= days_in_years(year, count),
    ensures
        year_of_day(days, year)
            == year_of_day((days - days_in_years(year, count)) as nat, year + count),
        day_in_year(days, year)
            == day_in_year((days - days_in_years(year, count)) as nat, year + count),
    decreases count
{
    if count > 0 {
        lemma_year_of_day_skip(
            (days - days_in_year(year)) as nat, year + 1, (count - 1) as nat);
    }
}

/// Starting the walk 400 years later gives the same day 400 years later.
pub proof fn lemma_year_of_day_translate(days: nat, year: nat)
    ensures
        year_of_day(days, year + 400) == year_of_day(days, year) + 400,
        day_in_year(days, year + 400) == day_in_year(days, year),
    decreases days
{
    lemma_leap_year_period(year);
    if days >= days_in_year(year) {
        lemma_year_of_day_translate((days - days_in_year(year)) as nat, year + 1);
    }
}

/// One 400-year cycle later is the same day of the year, 400 years on.
pub proof fn lemma_year_of_day_cycle(days: nat, year: nat, cycles: nat)
    ensures
        year_of_day(days + 146097 * cycles, year) == year_of_day(days, year) + 400 * cycles,
        day_in_year(days + 146097 * cycles, year) == day_in_year(days, year),
    decreases cycles
{
    if cycles > 0 {
        let before = (cycles - 1) as nat;
        lemma_year_of_day_cycle(days, year, before);
        let earlier = days + 146097 * before;
        lemma_days_in_400_years(year);
        lemma_year_of_day_skip(earlier + 146097, year, 400);
        lemma_year_of_day_translate(earlier, year);
    }
}
/// The year bound is the four-digit year of RFC 5280 §4.1.2.5.
pub proof fn lemma_max_year_is_9999()
    ensures max_year() == 9999,
{
}

/// 1 January 10000 is day 2932897 of the Unix calendar: 31 December 9999 is
/// day 2932896 (the last day of the 9999th year).
pub proof fn lemma_year_9999_boundary()
    ensures
        year_of_day(2932896, epoch_year()) == 9999,
        day_in_year(2932896, epoch_year()) == 364,
        year_of_day(2932897, epoch_year()) == 10000,
        day_in_year(2932897, epoch_year()) == 0,
{
    // 2932896 = 20 * 146097 + 10956, and 10956 days from 1 January 1970 is
    // 31 December 1999; 400 * 20 years later is 31 December 9999.
    lemma_year_of_day_cycle(10956, 1970, 20);
    lemma_year_of_day_cycle(10957, 1970, 20);
    assert(year_of_day(10956, 1970) == 1999) by (compute_only);
    assert(day_in_year(10956, 1970) == 364) by (compute_only);
    assert(year_of_day(10957, 1970) == 2000) by (compute_only);
    assert(day_in_year(10957, 1970) == 0) by (compute_only);
}

/// The result is `None` exactly when the count is above 9999-12-31T23:59:59Z
/// (253402300799 seconds).
pub proof fn lemma_from_unix_none_iff(t: nat)
    ensures from_unix_seconds(t) is None <==> t > 253402300799,
{
    lemma_year_9999_boundary();
    let days = t / seconds_per_day();
    if t > 253402300799 {
        assert(days >= 2932897);
        if days > 2932897 {
            lemma_year_of_day_strict(2932897, days, 1970);
        }
    } else {
        assert(days <= 2932896);
        if days < 2932896 {
            lemma_year_of_day_strict(days, 2932896, 1970);
        }
    }
}

/// A converted time is a valid UTC calendar time, with seconds 0..=59: second
/// 60 is never produced.
pub proof fn lemma_from_unix_valid(t: nat)
    ensures
        match from_unix_seconds(t) {
            Some(time) => calendar_time_valid(time) && utc_seconds_valid(time),
            None => true,
        },
{
    let days = t / seconds_per_day();
    let year = year_of_day(days, epoch_year());
    let day_of_year = day_in_year(days, epoch_year());
    lemma_year_of_day_bounds(days, epoch_year());
    lemma_days_in_year_is_sum_of_months(year);
    lemma_month_of_day_bounds(day_of_year, year, 1);
}


/// The fields of a converted time are the unwrapped numbers of the spec:
/// none of the `as` casts in `from_unix_seconds` truncates.
proof fn lemma_from_unix_fields(t: nat)
    ensures
        match from_unix_seconds(t) {
            Some(time) => {
                let days = t / seconds_per_day();
                let second_of_day = t % seconds_per_day();
                let year = year_of_day(days, epoch_year());
                let day_of_year = day_in_year(days, epoch_year());
                time.year as nat == year
                    && time.month as nat == month_of_day(day_of_year, year, 1)
                    && time.day as nat == day_in_month(day_of_year, year, 1) + 1
                    && time.hour as nat == second_of_day / 3600
                    && time.minute as nat == second_of_day % 3600 / 60
                    && time.second as nat == second_of_day % 60
                    && year <= 9999
            },
            None => true,
        },
{
    let days = t / seconds_per_day();
    let year = year_of_day(days, epoch_year());
    let day_of_year = day_in_year(days, epoch_year());
    lemma_year_of_day_bounds(days, epoch_year());
    lemma_days_in_year_is_sum_of_months(year);
    lemma_month_of_day_bounds(day_of_year, year, 1);
}

/// Within one day the clock fields (hour, minute, second) order as the
/// second of the day.
proof fn lemma_clock_fields_monotone(first: nat, second: nat)
    requires first <= second, second < 86400,
    ensures
        (first / 3600) < (second / 3600)
            || (first / 3600) == (second / 3600) && ((first % 3600 / 60) < (second % 3600 / 60)
            || (first % 3600 / 60) == (second % 3600 / 60) && (first % 60) <= (second % 60)),
{
}

/// A strictly earlier day has a strictly earlier (year, month, day).
proof fn lemma_date_fields_strict(first: nat, second: nat)
    requires
        first < second,
        year_of_day(second, epoch_year()) <= 9999,
    ensures ({
        let year1 = year_of_day(first, epoch_year());
        let year2 = year_of_day(second, epoch_year());
        let doy1 = day_in_year(first, epoch_year());
        let doy2 = day_in_year(second, epoch_year());
        year1 < year2
            || year1 == year2 && (month_of_day(doy1, year1, 1) < month_of_day(doy2, year2, 1)
            || month_of_day(doy1, year1, 1) == month_of_day(doy2, year2, 1)
            && day_in_month(doy1, year1, 1) < day_in_month(doy2, year2, 1))
    }),
{
    lemma_year_of_day_strict(first, second, epoch_year());
    let year1 = year_of_day(first, epoch_year());
    let year2 = year_of_day(second, epoch_year());
    if year1 == year2 {
        lemma_year_of_day_bounds(second, epoch_year());
        lemma_days_in_year_is_sum_of_months(year2);
        lemma_month_of_day_strict(
            day_in_year(first, epoch_year()), day_in_year(second, epoch_year()), year2, 1);
    }
}

/// Monotonicity of the clock: a later count is never an earlier time, and a
/// count that converts bounds every earlier count's conversion.
pub proof fn lemma_from_unix_monotone(a: nat, b: nat)
    requires a <= b,
    ensures
        from_unix_seconds(b) is Some ==> from_unix_seconds(a) is Some,
        from_unix_seconds(a) is Some && from_unix_seconds(b) is Some
            ==> time_le(from_unix_seconds(a)->Some_0, from_unix_seconds(b)->Some_0),
{
    lemma_from_unix_none_iff(a);
    lemma_from_unix_none_iff(b);
    lemma_from_unix_fields(a);
    lemma_from_unix_fields(b);
    let days_a = a / seconds_per_day();
    let days_b = b / seconds_per_day();
    assert(days_a <= days_b);
    if from_unix_seconds(a) is Some && from_unix_seconds(b) is Some {
        if days_a == days_b {
            lemma_clock_fields_monotone(a % 86400, b % 86400);
        } else {
            lemma_date_fields_strict(days_a, days_b);
        }
    }
}

/// Distinct counts convert to distinct times.
pub proof fn lemma_from_unix_injective(a: nat, b: nat)
    requires a != b,
    ensures
        from_unix_seconds(a) is Some && from_unix_seconds(b) is Some
            ==> from_unix_seconds(a) != from_unix_seconds(b),
{
    let lo = if a < b { a } else { b };
    let hi = if a < b { b } else { a };
    lemma_from_unix_none_iff(lo);
    lemma_from_unix_none_iff(hi);
    lemma_from_unix_fields(lo);
    lemma_from_unix_fields(hi);
    let days_lo = lo / seconds_per_day();
    let days_hi = hi / seconds_per_day();
    if from_unix_seconds(lo) is Some && from_unix_seconds(hi) is Some {
        if days_lo < days_hi {
            lemma_date_fields_strict(days_lo, days_hi);
        } else {
            assert(days_lo == days_hi);
        }
    }
}
/// Example: Unix time 253402300799, the last second RFC 5280 can name. The
/// 8030-year walk is split with the 400-year cycle, so `compute_only` only
/// walks the last month.
pub proof fn lemma_example_9999_12_31_end()
    ensures from_unix_seconds(253402300799) == Some(CertificateTime {
        year: 9999, month: 12, day: 31, hour: 23, minute: 59, second: 59,
    })
{
    lemma_year_9999_boundary();
    assert(253402300799nat / seconds_per_day() == 2932896);
    assert(253402300799nat % seconds_per_day() == 86399);
    assert(month_of_day(364, 9999, 1) == 12) by (compute_only);
    assert(day_in_month(364, 9999, 1) == 30) by (compute_only);
}

/// Example: Unix time 253402300800 is 10000-01-01T00:00:00Z, past RFC 5280.
pub proof fn lemma_example_9999_end_plus_one()
    ensures from_unix_seconds(253402300800) is None,
{
    lemma_from_unix_none_iff(253402300800);
}

/// Example: the largest `u64` is far past year 9999.
pub proof fn lemma_example_u64_max()
    ensures from_unix_seconds(18446744073709551615) is None,
{
    lemma_from_unix_none_iff(18446744073709551615);
}

} // verus!
