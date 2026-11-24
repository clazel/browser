//! `Date` (§21.4): the constructor, `Date.now`, `Date.parse`, `Date.UTC`, every
//! getter and setter of `Date.prototype` (UTC and local), the string
//! conversions, `toJSON`, `valueOf` and `@@toPrimitive`, with the Annex B
//! `getYear`, `setYear` and `toGMTString`.
//!
//! # Where the clock and the time zone come from
//!
//! Nothing here reads the operating system. The current time and `LocalTZA`
//! are [`Vm::world`] questions ([`World::NowMs`], [`World::LocalTza`]), which
//! `clazel-js` forwards to `Host::now_ms` and `Host::local_tza`. A bare VM
//! (these tests, the Test262 runner) has no hook, and its clock is the epoch
//! and its zone UTC.
//!
//! # Modelling choices
//!
//! - **Section numbers** were checked against the pinned edition's text
//!   (`spec.html` at ecma262 commit `0248456c`, `SPEC-PIN.md`): clause 21.4
//!   (`Day` is §21.4.1.3, `MakeDay` §21.4.1.28, `TimeClip` §21.4.1.31, the Date
//!   Time String Format §21.4.1.32) and Annex B.2.3 (`getYear`, `setYear`,
//!   `toGMTString`). The step numbers of `MakeDay`, `MakeTime`, `UTC`, `setSeconds`,
//!   `setFullYear`, `getYear` and `setYear` were read there too; the others
//!   are from the same edition family and a comment that folds several steps
//!   into one line says so.
//! - **Time zone (7.0(b))**: the offset is whatever the host answers, a fixed
//!   offset for the renderer's life in the browser, so a date on the other
//!   side of a daylight-saving change is off by an hour. The zone name that
//!   `toString` may add in parentheses (§21.4.4.41.3 TimeZoneString, "an
//!   implementation-defined string that is either empty or ...") is empty.
//! - **Locale (7.0(b))**: `toLocaleString`, `toLocaleDateString` and
//!   `toLocaleTimeString` ignore their arguments and give the `en-US` form,
//!   `M/D/YYYY, h:mm:ss AM`.
//! - **MakeDay's range**: a year further than 1,000,000 from 1970 is "not
//!   possible" (§21.4.1.28 step 8), whatever the date offset brings back.
//! - **`Date.parse`** reads the Date Time String Format exactly (a fractional
//!   second may have any number of digits, as engines read it), and the forms
//!   `toString` and `toUTCString` print (a weekday name optional, an optional
//!   zone name in parentheses ignored). Anything else is `NaN`.
//! - **A Date object is a host object** with the tag [`TAG_DATE`] and its
//!   `[[DateValue]]` in slot 0.

use crate::util::{arg, constructor, define, method, number, string};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Hint, Intrinsic, NativeFn, Vm, World};

/// The host tag of a Date object.
pub const TAG_DATE: u32 = 0x5401;

const MS_PER_DAY: f64 = 86_400_000.0;
const MS_PER_HOUR: f64 = 3_600_000.0;
const MS_PER_MINUTE: f64 = 60_000.0;
const MS_PER_SECOND: f64 = 1000.0;
/// §21.4.1.1: a time value is within 8.64e15 ms of the epoch.
const MAX_TIME: f64 = 8.64e15;
/// The farthest year MakeDay accepts (see the module header).
const MAX_YEAR: f64 = 1_000_000.0;

/// The names `toString` prints, from Sunday and from January.
const DAY_NAMES: [&str; 7] = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
const MONTH_NAMES: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
];
/// Days before each month in a common year, and the year's total.
const CUMULATIVE: [f64; 13] = [
    0.0, 31.0, 59.0, 90.0, 120.0, 151.0, 181.0, 212.0, 243.0, 273.0, 304.0, 334.0, 365.0,
];

/// The host's answer to `LocalTZA ( t, isUTC )`: a function of the time and
/// whether it is a UTC time.
pub type Tza<'a> = &'a mut dyn FnMut(f64, bool) -> f64;

// ---------------------------------------------------------------------
// Abstract operations (§21.4.1), pure
// ---------------------------------------------------------------------

/// `Day ( t )`, §21.4.1.3: `floor(t / msPerDay)`.
#[must_use]
pub fn day(t: f64) -> f64 {
    (t / MS_PER_DAY).floor()
}

/// `TimeWithinDay ( t )`, §21.4.1.4: `t modulo msPerDay`.
#[must_use]
pub fn time_within_day(t: f64) -> f64 {
    t.rem_euclid(MS_PER_DAY)
}

/// `DaysInYear ( y )`, §21.4.1.5: 366 for a leap year, else 365.
#[must_use]
pub fn days_in_year(y: f64) -> f64 {
    // Steps 1 to 4: divisible by 400, else by 100, else by 4.
    if y.rem_euclid(4.0) != 0.0 || (y.rem_euclid(100.0) == 0.0 && y.rem_euclid(400.0) != 0.0) {
        365.0
    } else {
        366.0
    }
}

/// `DayFromYear ( y )`, §21.4.1.6.
#[must_use]
pub fn day_from_year(y: f64) -> f64 {
    365.0 * (y - 1970.0) + ((y - 1969.0) / 4.0).floor() - ((y - 1901.0) / 100.0).floor()
        + ((y - 1601.0) / 400.0).floor()
}

/// `TimeFromYear ( y )`, §21.4.1.7: `msPerDay * DayFromYear(y)`.
#[must_use]
pub fn time_from_year(y: f64) -> f64 {
    MS_PER_DAY * day_from_year(y)
}

/// `YearFromTime ( t )`, §21.4.1.8: the largest integral y such that
/// `TimeFromYear(y) <= t`.
#[must_use]
pub fn year_from_time(t: f64) -> f64 {
    // An estimate from the mean year length, then at most a step or two.
    let mut y = (t / (MS_PER_DAY * 365.2425)).floor() + 1970.0;
    while time_from_year(y) > t {
        y -= 1.0;
    }
    while time_from_year(y + 1.0) <= t {
        y += 1.0;
    }
    y
}

/// `DayWithinYear ( t )`, §21.4.1.9: `Day(t) - DayFromYear(YearFromTime(t))`.
#[must_use]
pub fn day_within_year(t: f64) -> f64 {
    day(t) - day_from_year(year_from_time(t))
}

/// `InLeapYear ( t )`, §21.4.1.10.
#[must_use]
pub fn in_leap_year(t: f64) -> bool {
    days_in_year(year_from_time(t)) == 366.0
}

/// Days before month `m` (0 to 11) of a year, `leap` or not.
fn days_before_month(m: usize, leap: bool) -> f64 {
    let d = CUMULATIVE.get(m).copied().unwrap_or(365.0);
    if leap && m >= 2 { d + 1.0 } else { d }
}

/// `MonthFromTime ( t )`, §21.4.1.11: 0 for January to 11 for December.
#[must_use]
pub fn month_from_time(t: f64) -> f64 {
    let d = day_within_year(t);
    let leap = in_leap_year(t);
    for m in 0..12usize {
        if d < days_before_month(m.saturating_add(1), leap) {
            return m as f64;
        }
    }
    11.0
}

/// `DateFromTime ( t )`, §21.4.1.12: 1 to 31.
#[must_use]
pub fn date_from_time(t: f64) -> f64 {
    let m = month_from_time(t) as usize;
    day_within_year(t) - days_before_month(m, in_leap_year(t)) + 1.0
}

/// `WeekDay ( t )`, §21.4.1.13: `(Day(t) + 4) modulo 7`.
#[must_use]
pub fn week_day(t: f64) -> f64 {
    (day(t) + 4.0).rem_euclid(7.0)
}

/// `HourFromTime ( t )`, §21.4.1.14.
#[must_use]
pub fn hour_from_time(t: f64) -> f64 {
    (t / MS_PER_HOUR).floor().rem_euclid(24.0)
}

/// `MinFromTime ( t )`, §21.4.1.15.
#[must_use]
pub fn min_from_time(t: f64) -> f64 {
    (t / MS_PER_MINUTE).floor().rem_euclid(60.0)
}

/// `SecFromTime ( t )`, §21.4.1.16.
#[must_use]
pub fn sec_from_time(t: f64) -> f64 {
    (t / MS_PER_SECOND).floor().rem_euclid(60.0)
}

/// `msFromTime ( t )`, §21.4.1.17.
#[must_use]
pub fn ms_from_time(t: f64) -> f64 {
    t.rem_euclid(MS_PER_SECOND)
}

/// `LocalTime ( t )`, §21.4.1.25: `t + LocalTZA(t, true)`.
pub fn local_time(t: f64, tza: Tza<'_>) -> f64 {
    t + offset(tza(t, true))
}

/// `UTC ( t )`, §21.4.1.26:
/// 1. If t is not finite, return NaN.
///
/// The later steps take the system time zone's offset at t and return `t -
/// offset`. The zone is a fixed offset here (7.0(b)), the host's
/// `LocalTZA(t, false)`, so the steps for a named zone and its possible
/// instants are not needed.
pub fn utc(t: f64, tza: Tza<'_>) -> f64 {
    if !t.is_finite() {
        return f64::NAN;
    }
    t - offset(tza(t, false))
}

/// A host offset that is not a finite Number is no offset.
fn offset(o: f64) -> f64 {
    if o.is_finite() { o } else { 0.0 }
}

/// ToIntegerOrInfinity for a finite Number: truncation.
fn trunc(n: f64) -> f64 {
    n.trunc() + 0.0
}

/// `MakeTime ( hour, min, sec, ms )`, §21.4.1.27:
/// 1. If hour is not finite or min is not finite or sec is not finite or ms
///    is not finite, return NaN.
/// - Steps 2 to 5: let h, m, s, milli be ToIntegerOrInfinity of each.
/// 6. Return ((h * msPerHour + m * msPerMinute) + s * msPerSecond) + milli,
///    performing the arithmetic according to IEEE 754-2019 rules.
#[must_use]
pub fn make_time(hour: f64, min: f64, sec: f64, ms: f64) -> f64 {
    if !(hour.is_finite() && min.is_finite() && sec.is_finite() && ms.is_finite()) {
        return f64::NAN;
    }
    let (h, m, s, milli) = (trunc(hour), trunc(min), trunc(sec), trunc(ms));
    ((h * MS_PER_HOUR + m * MS_PER_MINUTE) + s * MS_PER_SECOND) + milli
}

/// `MakeDay ( year, month, date )`, §21.4.1.28:
/// 1. If year, month or date is not finite, return NaN.
/// - Steps 2 to 4: let y, m, dt be ToIntegerOrInfinity of each.
/// 5. Let ym be y + floor(m / 12).
/// 6. If ym is not finite, return NaN.
/// 7. Let mn be m modulo 12.
/// 8. Find a finite time value t such that YearFromTime(t) is ym, MonthFromTime(t)
///    is mn and DateFromTime(t) is 1; but if this is not possible (because
///    some argument is out of range), return NaN.
/// 9. Return Day(t) + dt - 1.
#[must_use]
pub fn make_day(year: f64, month: f64, date: f64) -> f64 {
    if !(year.is_finite() && month.is_finite() && date.is_finite()) {
        return f64::NAN;
    }
    let (y, m, dt) = (trunc(year), trunc(month), trunc(date));
    let ym = y + (m / 12.0).floor();
    if !ym.is_finite() || ym.abs() > MAX_YEAR {
        return f64::NAN;
    }
    let mn = m.rem_euclid(12.0) as usize;
    let first = day_from_year(ym) + days_before_month(mn, days_in_year(ym) == 366.0);
    first + dt - 1.0
}

/// `MakeDate ( day, time )`, §21.4.1.29:
/// 1. If day is not finite or time is not finite, return NaN.
/// 2. Let tv be day * msPerDay + time.
/// 3. If tv is not finite, return NaN.
/// 4. Return tv.
#[must_use]
pub fn make_date(day: f64, time: f64) -> f64 {
    if !(day.is_finite() && time.is_finite()) {
        return f64::NAN;
    }
    let tv = day * MS_PER_DAY + time;
    if tv.is_finite() { tv } else { f64::NAN }
}

/// `MakeFullYear ( year )`, §21.4.1.30:
/// 1. If year is NaN, return NaN.
/// 2. Let truncated be ! ToIntegerOrInfinity(year).
/// 3. If truncated is in the inclusive interval from 0 to 99, return
///    1900 + truncated.
/// 4. Return truncated.
#[must_use]
pub fn make_full_year(year: f64) -> f64 {
    if year.is_nan() {
        return f64::NAN;
    }
    let truncated = if year.is_finite() { trunc(year) } else { year };
    if (0.0..=99.0).contains(&truncated) {
        1900.0 + truncated
    } else {
        truncated
    }
}

/// `TimeClip ( time )`, §21.4.1.31:
/// 1. If time is not finite, return NaN.
/// 2. If abs(R(time)) > 8.64 × 10^15, return NaN.
/// 3. Return 𝔽(! ToIntegerOrInfinity(time)).
#[must_use]
pub fn time_clip(time: f64) -> f64 {
    if !time.is_finite() || time.abs() > MAX_TIME {
        return f64::NAN;
    }
    trunc(time)
}

// ---------------------------------------------------------------------
// Formatting (§21.4.4.41 and friends)
// ---------------------------------------------------------------------

fn name<'a>(table: &'a [&'a str], i: f64) -> &'a str {
    table.get(i as usize).copied().unwrap_or("")
}

fn pad(n: f64, width: usize) -> String {
    format!("{:0>width$}", n as i64)
}

/// The year as `DateString` prints it: at least four digits, `-` for a
/// negative year (§21.4.4.41.2 step 4 to 6).
fn year_string(y: f64) -> String {
    let sign = if y < 0.0 { "-" } else { "" };
    format!("{sign}{}", pad(y.abs(), 4))
}

/// `DateString ( tv )`, §21.4.4.41.2, for a local time `t`: "Tue Feb 01 2022".
#[must_use]
pub fn date_string(t: f64) -> String {
    format!(
        "{} {} {} {}",
        name(&DAY_NAMES, week_day(t)),
        name(&MONTH_NAMES, month_from_time(t)),
        pad(date_from_time(t), 2),
        year_string(year_from_time(t)),
    )
}

/// `TimeString ( tv )`, §21.4.4.41.1, for a local time `t`: "10:00:00 GMT".
#[must_use]
pub fn time_string(t: f64) -> String {
    format!(
        "{}:{}:{} GMT",
        pad(hour_from_time(t), 2),
        pad(min_from_time(t), 2),
        pad(sec_from_time(t), 2),
    )
}

/// `TimeZoneString ( tv )`, §21.4.4.41.3, for an offset in ms: "+0100". The
/// optional zone name is empty (module header).
#[must_use]
pub fn time_zone_string(offset_ms: f64) -> String {
    let sign = if offset_ms >= 0.0 { '+' } else { '-' };
    let abs = offset_ms.abs();
    let hours = (abs / MS_PER_HOUR).floor();
    let minutes = ((abs % MS_PER_HOUR) / MS_PER_MINUTE).floor();
    format!("{sign}{}{}", pad(hours, 2), pad(minutes, 2))
}

/// `ToDateString ( tv )`, §21.4.4.41.4, "Tue Feb 01 2022 10:00:00 GMT+0100".
pub fn to_date_string(tv: f64, tza: Tza<'_>) -> String {
    if tv.is_nan() {
        return "Invalid Date".to_string();
    }
    let off = offset(tza(tv, true));
    let t = tv + off;
    format!(
        "{} {}{}",
        date_string(t),
        time_string(t),
        time_zone_string(off)
    )
}

/// `Date.prototype.toUTCString`, §21.4.4.43: "Tue, 01 Feb 2022 10:00:00 GMT".
#[must_use]
pub fn to_utc_string(tv: f64) -> String {
    if tv.is_nan() {
        return "Invalid Date".to_string();
    }
    format!(
        "{}, {} {} {} {}",
        name(&DAY_NAMES, week_day(tv)),
        pad(date_from_time(tv), 2),
        name(&MONTH_NAMES, month_from_time(tv)),
        year_string(year_from_time(tv)),
        time_string(tv),
    )
}

/// `Date.prototype.toISOString`, §21.4.4.36, for a finite time value:
/// `YYYY-MM-DDTHH:mm:ss.sssZ`, with `±YYYYYY` outside 0 to 9999.
#[must_use]
pub fn to_iso_string(tv: f64) -> String {
    let y = year_from_time(tv);
    let year = if (0.0..=9999.0).contains(&y) {
        pad(y, 4)
    } else {
        format!("{}{}", if y < 0.0 { '-' } else { '+' }, pad(y.abs(), 6))
    };
    format!(
        "{year}-{}-{}T{}:{}:{}.{}Z",
        pad(month_from_time(tv) + 1.0, 2),
        pad(date_from_time(tv), 2),
        pad(hour_from_time(tv), 2),
        pad(min_from_time(tv), 2),
        pad(sec_from_time(tv), 2),
        pad(ms_from_time(tv), 3),
    )
}

/// The `en-US` date of a local time: "2/1/2022".
fn locale_date(t: f64) -> String {
    format!(
        "{}/{}/{}",
        month_from_time(t) + 1.0,
        date_from_time(t),
        year_from_time(t)
    )
}

/// The `en-US` time of a local time: "10:00:00 AM".
fn locale_time(t: f64) -> String {
    let h = hour_from_time(t);
    let h12 = if h % 12.0 == 0.0 { 12.0 } else { h % 12.0 };
    format!(
        "{}:{}:{} {}",
        h12,
        pad(min_from_time(t), 2),
        pad(sec_from_time(t), 2),
        if h < 12.0 { "AM" } else { "PM" }
    )
}

// ---------------------------------------------------------------------
// Parsing (§21.4.1.32 and the toString forms), untrusted input
// ---------------------------------------------------------------------

/// A cursor over the bytes of the string being parsed.
struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}

impl Cur<'_> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }
    fn bump(&mut self) {
        self.i = self.i.saturating_add(1);
    }
    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn at_end(&self) -> bool {
        self.i >= self.b.len()
    }
    fn skip_ws(&mut self) {
        while self.peek() == Some(b' ') {
            self.bump();
        }
    }
    /// Exactly `n` ASCII digits.
    fn digits(&mut self, n: usize) -> Option<f64> {
        let mut v = 0.0;
        for _ in 0..n {
            let d = self.peek().filter(u8::is_ascii_digit)?;
            v = v * 10.0 + f64::from(d.wrapping_sub(b'0'));
            self.bump();
        }
        Some(v)
    }
    /// One to `max` digits.
    fn up_to(&mut self, max: usize) -> Option<f64> {
        let mut v = 0.0;
        let mut n = 0usize;
        while n < max
            && let Some(d) = self.peek().filter(u8::is_ascii_digit)
        {
            v = v * 10.0 + f64::from(d.wrapping_sub(b'0'));
            self.bump();
            n = n.saturating_add(1);
        }
        if n == 0 { None } else { Some(v) }
    }
    /// A run of ASCII letters.
    fn word(&mut self) -> &str {
        let start = self.i;
        while self.peek().is_some_and(|c| c.is_ascii_alphabetic()) {
            self.bump();
        }
        self.b
            .get(start..self.i)
            .and_then(|s| core::str::from_utf8(s).ok())
            .unwrap_or("")
    }
}

/// The days in month `m` (1 to 12) of year `y`.
fn days_in_month(y: f64, m: f64) -> f64 {
    let i = (m as usize).saturating_sub(1);
    days_before_month(i.saturating_add(1), days_in_year(y) == 366.0)
        - days_before_month(i, days_in_year(y) == 366.0)
}

/// A UTC offset after its sign: `HH:mm` (or `HHmm` if `colon` is false).
fn offset_digits(c: &mut Cur<'_>, colon: bool, sign: f64) -> Option<f64> {
    let hh = c.digits(2)?;
    if colon && !c.eat(b':') {
        return None;
    }
    let mm = c.digits(2)?;
    if hh > 23.0 || mm > 59.0 {
        return None;
    }
    Some(sign * (hh * MS_PER_HOUR + mm * MS_PER_MINUTE))
}

/// The Date Time String Format, §21.4.1.32:
/// `YYYY`, `YYYY-MM`, `YYYY-MM-DD`, each of them with `THH:mm`, `THH:mm:ss`
/// or `THH:mm:ss.sss` and a `Z` or `±HH:mm` offset; `±YYYYYY` for the year
/// outside 0 to 9999 (`-000000` is not valid). A date-only form is UTC and a
/// date-time with no offset is local time. `None` if the text is not this
/// format; `Some(NaN)` if it is but an element is out of range ("Illegal
/// values (out-of-bounds as well as syntax errors) in a format string means
/// that the format string is not a valid instance of this format").
fn parse_iso(s: &str, tza: Tza<'_>) -> Option<f64> {
    let mut c = Cur {
        b: s.as_bytes(),
        i: 0,
    };
    let year = match c.peek() {
        Some(sg @ (b'+' | b'-')) => {
            c.bump();
            let y = c.digits(6)?;
            if sg == b'-' && y == 0.0 {
                return Some(f64::NAN);
            }
            if sg == b'-' { -y } else { y }
        }
        _ => c.digits(4)?,
    };
    let (mut month, mut dd) = (1.0, 1.0);
    if c.eat(b'-') {
        month = c.digits(2)?;
        if c.eat(b'-') {
            dd = c.digits(2)?;
        }
    }
    let (mut h, mut m, mut sec, mut ms) = (0.0, 0.0, 0.0, 0.0);
    let mut zone: Option<f64> = None;
    let mut has_time = false;
    if c.eat(b'T') {
        has_time = true;
        h = c.digits(2)?;
        if !c.eat(b':') {
            return None;
        }
        m = c.digits(2)?;
        if c.eat(b':') {
            sec = c.digits(2)?;
            if c.eat(b'.') {
                // The first three digits are the milliseconds; more digits
                // are read and dropped.
                let mut scale = 100.0;
                let mut any = false;
                while let Some(d) = c.peek().filter(u8::is_ascii_digit) {
                    ms += f64::from(d.wrapping_sub(b'0')) * scale;
                    scale /= 10.0;
                    any = true;
                    c.bump();
                }
                if !any {
                    return None;
                }
                ms = ms.floor();
            }
        }
        match c.peek() {
            Some(b'Z') => {
                c.bump();
                zone = Some(0.0);
            }
            Some(sg @ (b'+' | b'-')) => {
                c.bump();
                zone = Some(offset_digits(
                    &mut c,
                    true,
                    if sg == b'-' { -1.0 } else { 1.0 },
                )?);
            }
            _ => {}
        }
    }
    if !c.at_end() {
        return None;
    }
    let in_range = (1.0..=12.0).contains(&month)
        && dd >= 1.0
        && dd <= days_in_month(year, month)
        && h <= 24.0
        && m <= 59.0
        && sec <= 59.0
        && (h < 24.0 || (m == 0.0 && sec == 0.0 && ms == 0.0));
    if !in_range {
        return Some(f64::NAN);
    }
    let date = make_date(make_day(year, month - 1.0, dd), make_time(h, m, sec, ms));
    let tv = match zone {
        Some(z) => date - z,
        None if has_time => utc(date, tza),
        None => date,
    };
    Some(time_clip(tv))
}

/// The index of a month or weekday name, from its first three letters (any
/// case), if the word is one.
fn name_index(table: &[&str], w: &str) -> Option<usize> {
    let head = w.get(..3)?;
    table.iter().position(|n| n.eq_ignore_ascii_case(head))
}

/// What `toString` and `toUTCString` print, and the same with the weekday
/// left out or the day and month swapped: `Tue Feb 01 2022 10:00:00
/// GMT+0100 (CET)`, `Tue, 01 Feb 2022 10:00:00 GMT`, `Feb 01 2022`.
fn parse_legacy(s: &str, tza: Tza<'_>) -> f64 {
    let mut c = Cur {
        b: s.as_bytes(),
        i: 0,
    };
    c.skip_ws();
    // An optional weekday, then an optional comma.
    let save = c.i;
    let w = c.word().to_string();
    if name_index(&DAY_NAMES, &w).is_some() {
        c.eat(b',');
    } else {
        c.i = save;
    }
    c.skip_ws();
    let (month, day_of_month, year);
    if c.peek().is_some_and(|b| b.is_ascii_alphabetic()) {
        let w = c.word().to_string();
        let Some(mi) = name_index(&MONTH_NAMES, &w) else {
            return f64::NAN;
        };
        c.skip_ws();
        let Some(d) = day_number(&mut c) else {
            return f64::NAN;
        };
        c.eat(b',');
        c.skip_ws();
        let Some(y) = year_digits(&mut c) else {
            return f64::NAN;
        };
        (month, day_of_month, year) = (mi as f64, d, y);
    } else {
        let Some(d) = day_number(&mut c) else {
            return f64::NAN;
        };
        c.skip_ws();
        let w = c.word().to_string();
        let Some(mi) = name_index(&MONTH_NAMES, &w) else {
            return f64::NAN;
        };
        c.skip_ws();
        let Some(y) = year_digits(&mut c) else {
            return f64::NAN;
        };
        (month, day_of_month, year) = (mi as f64, d, y);
    }
    if day_of_month < 1.0 || day_of_month > days_in_month(year, month + 1.0) {
        return f64::NAN;
    }
    let (mut h, mut m, mut sec) = (0.0, 0.0, 0.0);
    c.skip_ws();
    if c.peek().is_some_and(|b| b.is_ascii_digit()) {
        let Some(hh) = c.digits(2) else {
            return f64::NAN;
        };
        if !c.eat(b':') {
            return f64::NAN;
        }
        let Some(mm) = c.digits(2) else {
            return f64::NAN;
        };
        h = hh;
        m = mm;
        if c.eat(b':') {
            let Some(ss) = c.digits(2) else {
                return f64::NAN;
            };
            sec = ss;
        }
        if h > 24.0 || m > 59.0 || sec > 59.0 || (h == 24.0 && (m != 0.0 || sec != 0.0)) {
            return f64::NAN;
        }
    }
    c.skip_ws();
    let mut zone: Option<f64> = None;
    if c.peek().is_some_and(|b| b.is_ascii_alphabetic()) {
        let w = c.word().to_string();
        if !["GMT", "UTC", "UT", "Z"]
            .iter()
            .any(|z| z.eq_ignore_ascii_case(&w))
        {
            return f64::NAN;
        }
        zone = Some(0.0);
    }
    if let Some(sg @ (b'+' | b'-')) = c.peek() {
        c.bump();
        let sign = if sg == b'-' { -1.0 } else { 1.0 };
        let colon = c.b.get(c.i.saturating_add(2)) == Some(&b':');
        match offset_digits(&mut c, colon, sign) {
            Some(z) => zone = Some(z),
            None => return f64::NAN,
        }
    }
    c.skip_ws();
    if c.eat(b'(') {
        // A zone name, ignored: up to the closing parenthesis, which must
        // end the text.
        while c.peek().is_some_and(|b| b != b')') {
            c.bump();
        }
        if !c.eat(b')') {
            return f64::NAN;
        }
        c.skip_ws();
    }
    if !c.at_end() {
        return f64::NAN;
    }
    let date = make_date(
        make_day(year, month, day_of_month),
        make_time(h, m, sec, 0.0),
    );
    let tv = match zone {
        Some(z) => date - z,
        None => utc(date, tza),
    };
    time_clip(tv)
}

/// A day of the month: one or two digits, not followed by another digit.
fn day_number(c: &mut Cur<'_>) -> Option<f64> {
    let d = c.up_to(2)?;
    if c.peek().is_some_and(|b| b.is_ascii_digit()) {
        None
    } else {
        Some(d)
    }
}

/// A year as `toString` prints it: an optional sign and one to six digits.
fn year_digits(c: &mut Cur<'_>) -> Option<f64> {
    let neg = c.eat(b'-');
    if !neg {
        c.eat(b'+');
    }
    let y = c.up_to(6)?;
    Some(if neg { -y } else { y })
}

/// `Date.parse ( string )`'s parse, §21.4.3.2: "If the String does not
/// conform to that format the function may fall back to any
/// implementation-specific heuristics or implementation-specific date
/// formats" (here the `toString` forms); unrecognised input is `NaN`.
pub fn parse(s: &str, tza: Tza<'_>) -> f64 {
    let s = s.trim_matches(' ');
    match parse_iso(s, tza) {
        Some(tv) => tv,
        None => parse_legacy(s, tza),
    }
}

// ---------------------------------------------------------------------
// The VM side
// ---------------------------------------------------------------------

/// Runs `f` with the VM's `LocalTZA` as the offset provider.
fn with_tza<R>(vm: &mut Vm, f: impl FnOnce(Tza<'_>) -> R) -> R {
    let mut tza = |time_ms: f64, is_utc: bool| vm.world(World::LocalTza { time_ms, is_utc });
    f(&mut tza)
}

fn local(vm: &mut Vm, t: f64) -> f64 {
    with_tza(vm, |z| local_time(t, z))
}

fn to_utc(vm: &mut Vm, t: f64) -> f64 {
    with_tza(vm, |z| utc(t, z))
}

/// The time value of the host's clock: whole milliseconds.
fn now(vm: &mut Vm) -> f64 {
    let n = vm.world(World::NowMs);
    if n.is_finite() { n.floor() } else { 0.0 }
}

/// Installs `Date` and `Date.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    // §21.4.4: the prototype is an ordinary object, not a Date.
    let proto = vm.heap_mut().new_object(object_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::DatePrototype, proto);
    let ctor = constructor(vm, "Date", 7, date, proto)?;
    method(vm, ctor, "now", 0, date_now)?;
    method(vm, ctor, "parse", 1, date_parse)?;
    method(vm, ctor, "UTC", 7, date_utc)?;
    let methods: [(&str, i32, NativeFn); 45] = [
        ("getDate", 0, get_date),
        ("getDay", 0, get_day),
        ("getFullYear", 0, get_full_year),
        ("getHours", 0, get_hours),
        ("getMilliseconds", 0, get_milliseconds),
        ("getMinutes", 0, get_minutes),
        ("getMonth", 0, get_month),
        ("getSeconds", 0, get_seconds),
        ("getTime", 0, get_time),
        ("getTimezoneOffset", 0, get_timezone_offset),
        ("getUTCDate", 0, get_utc_date),
        ("getUTCDay", 0, get_utc_day),
        ("getUTCFullYear", 0, get_utc_full_year),
        ("getUTCHours", 0, get_utc_hours),
        ("getUTCMilliseconds", 0, get_utc_milliseconds),
        ("getUTCMinutes", 0, get_utc_minutes),
        ("getUTCMonth", 0, get_utc_month),
        ("getUTCSeconds", 0, get_utc_seconds),
        ("getYear", 0, get_year),
        ("setDate", 1, set_date),
        ("setFullYear", 3, set_full_year),
        ("setHours", 4, set_hours),
        ("setMilliseconds", 1, set_milliseconds),
        ("setMinutes", 3, set_minutes),
        ("setMonth", 2, set_month),
        ("setSeconds", 2, set_seconds),
        ("setTime", 1, set_time),
        ("setUTCDate", 1, set_utc_date),
        ("setUTCFullYear", 3, set_utc_full_year),
        ("setUTCHours", 4, set_utc_hours),
        ("setUTCMilliseconds", 1, set_utc_milliseconds),
        ("setUTCMinutes", 3, set_utc_minutes),
        ("setUTCMonth", 2, set_utc_month),
        ("setUTCSeconds", 2, set_utc_seconds),
        ("setYear", 1, set_year),
        ("toDateString", 0, to_date_string_method),
        ("toISOString", 0, to_iso_string_method),
        ("toJSON", 1, to_json),
        ("toLocaleDateString", 0, to_locale_date_string),
        ("toLocaleString", 0, to_locale_string),
        ("toLocaleTimeString", 0, to_locale_time_string),
        ("toString", 0, to_string),
        ("toTimeString", 0, to_time_string),
        ("valueOf", 0, get_time),
        ("toUTCString", 0, to_utc_string_method),
    ];
    let mut utc_string = Value::UNDEFINED;
    for (name, len, f) in methods {
        let func = method(vm, proto, name, len, f)?;
        if name == "toUTCString" {
            utc_string = func;
        }
    }
    // Annex B §B.2.3.3 `Date.prototype.toGMTString`: "The initial value of
    // the property is the same function object as ... toUTCString".
    define(vm, proto, "toGMTString", utc_string, crate::util::METHOD)?;
    // §21.4.4.45 `Date.prototype [ @@toPrimitive ] ( hint )`: name
    // "[Symbol.toPrimitive]", { [[Writable]]: false, [[Configurable]]: true }.
    let tp = vm.new_native("[Symbol.toPrimitive]", 1, to_primitive)?;
    let ktp = vm.well_known_key(clazel_js_heap::symbol::TO_PRIMITIVE)?;
    vm.heap_mut()
        .define(proto, ktp, tp, Attrs(Attrs::CONFIGURABLE))?;
    crate::util::global(vm, "Date", ctor)
}

/// thisTimeValue ( value ), §21.4.4 (the abstract operation of that name):
/// 1. If value is an Object and value has a [[DateValue]] internal slot, then
///    a. Return value.[[DateValue]].
/// 2. Throw a TypeError exception.
fn this_time_value(vm: &mut Vm, v: Value) -> Result<f64, Abrupt> {
    if vm.heap().is_object(v)
        && vm.host_tag(v) == Some(TAG_DATE)
        && let Some(t) = vm.host_slot(v, 0).and_then(crate::util::as_number)
    {
        return Ok(t);
    }
    Err(vm.type_error("this is not a Date object"))
}

/// Stores a time value in a Date object.
fn set_slot(vm: &mut Vm, this: Value, tv: f64) {
    let _ = vm.set_host_slot(this, 0, number(tv));
}

/// A text as a Rust string, for parsing.
fn text_of(vm: &mut Vm, v: Value) -> Result<String, Abrupt> {
    Ok(vm.to_js_string(v)?.to_string_lossy())
}

/// `Date ( ...values )`, §21.4.2.1:
/// 1. If NewTarget is undefined, then
///    a. Let now be the time value (UTC) identifying the current time.
///    b. Return ToDateString(now).
/// 2. Let numberOfArgs be the number of elements in values.
/// 3. If numberOfArgs = 0, then a. Let dv be the time value (UTC) identifying
///    the current time.
/// 4. Else if numberOfArgs = 1, then
///    a. Let value be values[0].
///    b. If value is an Object and value has a [[DateValue]] internal slot,
///    then i. Let tv be thisTimeValue(value).
///    c. Else, i. Let v be ? ToPrimitive(value). ii. If v is a String, then
///    (1. Assert: the next step never returns an abrupt completion because v
///    is a String; 2. let tv be the result of parsing v as a date, in
///    exactly the same manner as for the parse method); iii. else, let tv
///    be ? ToNumber(v).
///    d. Let dv be TimeClip(tv).
/// 5. Else, a. Assert: numberOfArgs ≥ 2. b. Let y be ? ToNumber(values[0]).
///    c. Let m be ? ToNumber(values[1]). d. If numberOfArgs > 2, let dt be
///    ? ToNumber(values[2]); else, let dt be 1𝔽. e. ... h, min, s, milli
///    likewise, 0𝔽 if absent. i. Let yr be MakeFullYear(y). j. Let finalDate
///    be MakeDate(MakeDay(yr, m, dt), MakeTime(h, min, s, milli)).
///    k. Let dv be TimeClip(UTC(finalDate)).
/// 6. Let O be ? OrdinaryCreateFromConstructor(NewTarget,
///    "%Date.prototype%", « [[DateValue]] »).
/// 7. Set O.[[DateValue]] to dv.
/// 8. Return O.
fn date(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        let n = now(vm);
        let s = with_tza(vm, |z| to_date_string(n, z));
        return string(vm, &s);
    }
    let dv = match args.len() {
        0 => now(vm),
        1 => {
            let value = arg(args, 0);
            let tv = if vm.heap().is_object(value) && vm.host_tag(value) == Some(TAG_DATE) {
                this_time_value(vm, value)?
            } else {
                let v = vm.to_primitive(value, Hint::Default)?;
                if vm.heap().is_string(v) {
                    let text = text_of(vm, v)?;
                    with_tza(vm, |z| parse(&text, z))
                } else {
                    vm.to_number(v)?
                }
            };
            time_clip(tv)
        }
        _ => {
            let f = number_fields(vm, args, 7, [f64::NAN, f64::NAN, 1.0, 0.0, 0.0, 0.0, 0.0])?;
            let yr = make_full_year(f[0]);
            let final_date = make_date(make_day(yr, f[1], f[2]), make_time(f[3], f[4], f[5], f[6]));
            time_clip(to_utc(vm, final_date))
        }
    };
    let obj = vm.create_from_constructor(nt, Intrinsic::DatePrototype, ObjKind::Plain)?;
    vm.into_host_object(obj, TAG_DATE, vec![number(dv)], None)?;
    Ok(obj)
}

/// ToNumber of the first `n` arguments in order, each absent one (past the
/// first) replaced by the default.
fn number_fields(
    vm: &mut Vm,
    args: &[Value],
    n: usize,
    defaults: [f64; 7],
) -> Result<[f64; 7], Abrupt> {
    let mut out = defaults;
    for (i, slot) in out.iter_mut().enumerate().take(n) {
        if i < args.len() {
            *slot = vm.to_number(arg(args, i))?;
        }
    }
    Ok(out)
}

/// `Date.now ( )`, §21.4.3.1: "Return the Number value for the time that
/// identifies the current time."
fn date_now(vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(now(vm)))
}

/// `Date.parse ( string )`, §21.4.3.2:
/// 1. Let parsedDate be ? ToString(string).
/// 2. Let parseResult be ParseText(parsedDate, Date Time String Format) ...
///    (the format, then the `toString` forms: [`parse`]).
fn date_parse(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let text = text_of(vm, arg(args, 0))?;
    let tv = with_tza(vm, |z| parse(&text, z));
    Ok(number(tv))
}

/// `Date.UTC ( year [ , month [ , date [ , hours [ , minutes [ , seconds [ ,
/// ms ] ] ] ] ] ] )`, §21.4.3.4:
/// 1. Let y be ? ToNumber(year).
/// 2. If month is present, let m be ? ToNumber(month); else, let m be +0𝔽.
/// - Steps 3 to 6: dt (default 1𝔽), h, min, s, milli (default +0𝔽) likewise.
/// 7. Let yr be MakeFullYear(y).
/// 8. Return TimeClip(MakeDate(MakeDay(yr, m, dt), MakeTime(h, min, s, milli))).
fn date_utc(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let f = number_fields(vm, args, 7, [f64::NAN, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0])?;
    let yr = make_full_year(f[0]);
    Ok(number(time_clip(make_date(
        make_day(yr, f[1], f[2]),
        make_time(f[3], f[4], f[5], f[6]),
    ))))
}

// ----- getters -------------------------------------------------------

/// The shape of every getter (§21.4.4.2 and its siblings):
/// 1. Let dateObject be the this value.
/// 2. Perform ? RequireInternalSlot(dateObject, [[DateValue]]).
/// 3. Let t be dateObject.[[DateValue]].
/// 4. If t is NaN, return NaN.
/// 5. Return the field of LocalTime(t) (or of t, for the UTC getters).
fn get_field(vm: &mut Vm, this: Value, is_local: bool, f: fn(f64) -> f64) -> Result<Value, Abrupt> {
    let t = this_time_value(vm, this)?;
    if t.is_nan() {
        return Ok(number(f64::NAN));
    }
    let t = if is_local { local(vm, t) } else { t };
    Ok(number(f(t)))
}

macro_rules! getters {
    ($($name:ident, $local:expr, $f:expr;)*) => {$(
        fn $name(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
            get_field(vm, this, $local, $f)
        }
    )*};
}

getters! {
    get_date, true, date_from_time;
    get_day, true, week_day;
    get_full_year, true, year_from_time;
    get_hours, true, hour_from_time;
    get_milliseconds, true, ms_from_time;
    get_minutes, true, min_from_time;
    get_month, true, month_from_time;
    get_seconds, true, sec_from_time;
    get_utc_date, false, date_from_time;
    get_utc_day, false, week_day;
    get_utc_full_year, false, year_from_time;
    get_utc_hours, false, hour_from_time;
    get_utc_milliseconds, false, ms_from_time;
    get_utc_minutes, false, min_from_time;
    get_utc_month, false, month_from_time;
    get_utc_seconds, false, sec_from_time;
}

/// `Date.prototype.getTime ( )` and `valueOf ( )`, §21.4.4.10 and §21.4.4.44:
/// 1. Return ? thisTimeValue(this value).
fn get_time(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(number(this_time_value(vm, this)?))
}

/// `Date.prototype.getTimezoneOffset ( )`, §21.4.4.11:
/// 1 to 3. As the getters. 4. If t is NaN, return NaN.
/// 5. Return (t - LocalTime(t)) / msPerMinute.
fn get_timezone_offset(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let t = this_time_value(vm, this)?;
    if t.is_nan() {
        return Ok(number(f64::NAN));
    }
    let l = local(vm, t);
    Ok(number((t - l) / MS_PER_MINUTE))
}

/// `Date.prototype.getYear ( )`, Annex B §B.2.3.1:
/// 4. If t is NaN, return NaN. 5. Return YearFromTime(LocalTime(t)) - 1900.
fn get_year(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let t = this_time_value(vm, this)?;
    if t.is_nan() {
        return Ok(number(f64::NAN));
    }
    let l = local(vm, t);
    Ok(number(year_from_time(l) - 1900.0))
}

// ----- setters -------------------------------------------------------

/// Which field a setter starts at: the time fields are hours (0), minutes
/// (1), seconds (2), ms (3); the date fields year (0), month (1), date (2).
#[derive(Clone, Copy)]
enum Setter {
    Time(usize),
    Date(usize),
}

/// The shape of `setMilliseconds`, `setSeconds`, `setMinutes`, `setHours`
/// (§21.4.4.23, .26, .24, .22, and the UTC ones .31, .34, .32, .30), for example `setSeconds (
/// sec [ , ms ] )`:
/// 1. Let dateObject be the this value.
/// 2. Perform ? RequireInternalSlot(dateObject, [[DateValue]]).
/// 3. Let t be dateObject.[[DateValue]].
/// 4. Let s be ? ToNumber(sec).
/// 5. If ms is present, let milli be ? ToNumber(ms).
/// 6. If t is NaN, return NaN.
/// 7. Set t to LocalTime(t).
/// 8. If ms is not present, let milli be 𝔽(msFromTime(t)).
/// 9. Let date be MakeDate(Day(t), MakeTime(𝔽(HourFromTime(t)),
///    𝔽(MinFromTime(t)), s, milli)).
/// 10. Let u be TimeClip(UTC(date)).
/// 11. Set dateObject.[[DateValue]] to u.
/// 12. Return u.
///
/// and of `setDate`, `setMonth`, `setFullYear` (§21.4.4.20, .25, .21, and the UTC ones .28, .33, .29), for
/// example `setFullYear ( year [ , month [ , date ] ] )`:
/// 3. Let t be dateObject.[[DateValue]].
/// 4. Let y be ? ToNumber(year).
/// 5. If t is NaN, set t to +0𝔽; otherwise, set t to LocalTime(t).
/// 6. If month is not present, let m be 𝔽(MonthFromTime(t)); otherwise, let m
///    be ? ToNumber(month).
/// 7. If date is not present, let dt be 𝔽(DateFromTime(t)); otherwise, let dt
///    be ? ToNumber(date).
/// 8. Let newDate be MakeDate(MakeDay(y, m, dt), TimeWithinDay(t)).
/// 9. Let u be TimeClip(UTC(newDate)).
/// 10. Set dateObject.[[DateValue]] to u.
/// 11. Return u.
///
/// (`setMonth` and `setDate` return NaN for a NaN `t` after the conversions,
/// as `setSeconds` does; the UTC forms leave out LocalTime and UTC.)
fn set_fields(
    vm: &mut Vm,
    this: Value,
    args: &[Value],
    kind: Setter,
    is_local: bool,
) -> Result<Value, Abrupt> {
    let t = this_time_value(vm, this)?;
    let (start, count) = match kind {
        Setter::Time(s) => (s, 4usize.saturating_sub(s)),
        Setter::Date(s) => (s, 3usize.saturating_sub(s)),
    };
    // The first argument is always converted, `undefined` giving NaN; the
    // others only if present.
    let mut given: [Option<f64>; 4] = [None; 4];
    for (i, slot) in given.iter_mut().enumerate().take(count) {
        if i == 0 || i < args.len() {
            *slot = Some(vm.to_number(arg(args, i))?);
        }
    }
    let field = |i: usize, default: f64| -> f64 {
        i.checked_sub(start)
            .and_then(|k| given.get(k).copied().flatten())
            .unwrap_or(default)
    };
    let new_date = match kind {
        Setter::Time(_) => {
            if t.is_nan() {
                return Ok(number(f64::NAN));
            }
            let t = if is_local { local(vm, t) } else { t };
            let time = make_time(
                field(0, hour_from_time(t)),
                field(1, min_from_time(t)),
                field(2, sec_from_time(t)),
                field(3, ms_from_time(t)),
            );
            make_date(day(t), time)
        }
        Setter::Date(_) => {
            let t = if t.is_nan() {
                if start != 0 {
                    return Ok(number(f64::NAN));
                }
                0.0
            } else if is_local {
                local(vm, t)
            } else {
                t
            };
            let d = make_day(
                field(0, year_from_time(t)),
                field(1, month_from_time(t)),
                field(2, date_from_time(t)),
            );
            make_date(d, time_within_day(t))
        }
    };
    let u = time_clip(if is_local {
        to_utc(vm, new_date)
    } else {
        new_date
    });
    set_slot(vm, this, u);
    Ok(number(u))
}

macro_rules! setters {
    ($($name:ident, $kind:expr, $local:expr;)*) => {$(
        fn $name(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
            set_fields(vm, this, args, $kind, $local)
        }
    )*};
}

setters! {
    set_date, Setter::Date(2), true;
    set_full_year, Setter::Date(0), true;
    set_hours, Setter::Time(0), true;
    set_milliseconds, Setter::Time(3), true;
    set_minutes, Setter::Time(1), true;
    set_month, Setter::Date(1), true;
    set_seconds, Setter::Time(2), true;
    set_utc_date, Setter::Date(2), false;
    set_utc_full_year, Setter::Date(0), false;
    set_utc_hours, Setter::Time(0), false;
    set_utc_milliseconds, Setter::Time(3), false;
    set_utc_minutes, Setter::Time(1), false;
    set_utc_month, Setter::Date(1), false;
    set_utc_seconds, Setter::Time(2), false;
}

/// `Date.prototype.setTime ( time )`, §21.4.4.27:
/// 1. Let dateObject be the this value.
/// 2. Perform ? RequireInternalSlot(dateObject, [[DateValue]]).
/// 3. Let t be ? ToNumber(time).
/// 4. Let v be TimeClip(t).
/// 5. Set dateObject.[[DateValue]] to v.
/// 6. Return v.
fn set_time(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    this_time_value(vm, this)?;
    let t = vm.to_number(arg(args, 0))?;
    let v = time_clip(t);
    set_slot(vm, this, v);
    Ok(number(v))
}

/// `Date.prototype.setYear ( year )`, Annex B §B.2.3.2:
/// 3. Let t be dateObject.[[DateValue]].
/// 4. Let y be ? ToNumber(year).
/// 5. If t is NaN, set t to +0𝔽; otherwise, set t to LocalTime(t).
/// 6. Let yyyy be MakeFullYear(y).
/// 7. Let d be MakeDay(yyyy, 𝔽(MonthFromTime(t)), 𝔽(DateFromTime(t))).
/// 8. Let date be MakeDate(d, TimeWithinDay(t)).
/// 9. Let u be TimeClip(UTC(date)).
/// 10. Set dateObject.[[DateValue]] to u.
/// 11. Return u.
fn set_year(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let t = this_time_value(vm, this)?;
    let y = vm.to_number(arg(args, 0))?;
    let t = if t.is_nan() { 0.0 } else { local(vm, t) };
    let d = make_day(make_full_year(y), month_from_time(t), date_from_time(t));
    let date = make_date(d, time_within_day(t));
    let u = time_clip(to_utc(vm, date));
    set_slot(vm, this, u);
    Ok(number(u))
}

// ----- strings -------------------------------------------------------

/// `Date.prototype.toString ( )`, §21.4.4.41:
/// 1. Let dateObject be the this value.
/// 2. Perform ? RequireInternalSlot(dateObject, [[DateValue]]).
/// 3. Let tv be dateObject.[[DateValue]].
/// 4. Return ToDateString(tv).
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    let s = with_tza(vm, |z| to_date_string(tv, z));
    string(vm, &s)
}

/// `Date.prototype.toDateString ( )`, §21.4.4.35:
/// 4. If tv is NaN, return "Invalid Date". 5. Let t be LocalTime(tv).
/// 6. Return DateString(t).
fn to_date_string_method(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    if tv.is_nan() {
        return string(vm, "Invalid Date");
    }
    let t = local(vm, tv);
    string(vm, &date_string(t))
}

/// `Date.prototype.toTimeString ( )`, §21.4.4.42:
/// 4. If tv is NaN, return "Invalid Date". 5. Let t be LocalTime(tv).
/// 6. Return the string-concatenation of TimeString(t) and
///    TimeZoneString(tv).
fn to_time_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    if tv.is_nan() {
        return string(vm, "Invalid Date");
    }
    let off = with_tza(vm, |z| offset(z(tv, true)));
    string(
        vm,
        &format!("{}{}", time_string(tv + off), time_zone_string(off)),
    )
}

/// `Date.prototype.toUTCString ( )`, §21.4.4.43 (and Annex B's `toGMTString`).
fn to_utc_string_method(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    string(vm, &to_utc_string(tv))
}

/// `Date.prototype.toISOString ( )`, §21.4.4.36:
/// 3. Let tv be dateObject.[[DateValue]].
/// 4. If tv is not finite, throw a RangeError exception.
/// 5. ... Return the ISO 8601 format.
fn to_iso_string_method(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    if !tv.is_finite() {
        return Err(vm.range_error("Invalid time value"));
    }
    string(vm, &to_iso_string(tv))
}

/// `Date.prototype.toJSON ( key )`, §21.4.4.37:
/// 1. Let O be ? ToObject(this value).
/// 2. Let tv be ? ToPrimitive(O, number).
/// 3. If tv is a Number and tv is not finite, return null.
/// 4. Return ? Invoke(O, "toISOString").
fn to_json(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let o = vm.to_object(this)?;
    let tv = vm.to_primitive(o, Hint::Number)?;
    if let Some(n) = crate::util::as_number(tv)
        && !n.is_finite()
    {
        return Ok(Value::NULL);
    }
    crate::util::invoke(vm, o, "toISOString", &[])
}

/// `Date.prototype.toLocaleDateString ( [ reserved1 [ , reserved2 ] ] )`,
/// §21.4.4.38, with the `en-US` form (module header).
fn to_locale_date_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    locale(vm, this, locale_date)
}

/// `Date.prototype.toLocaleString`, §21.4.4.39, `en-US`.
fn to_locale_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    locale(vm, this, |t| {
        format!("{}, {}", locale_date(t), locale_time(t))
    })
}

/// `Date.prototype.toLocaleTimeString`, §21.4.4.40, `en-US`.
fn to_locale_time_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    locale(vm, this, locale_time)
}

/// The steps of the three `toLocale*String`: "Let x be thisTimeValue(this
/// value). If x is NaN, return "Invalid Date"", else the local time's text.
fn locale(vm: &mut Vm, this: Value, f: fn(f64) -> String) -> Result<Value, Abrupt> {
    let tv = this_time_value(vm, this)?;
    if tv.is_nan() {
        return string(vm, "Invalid Date");
    }
    let t = local(vm, tv);
    string(vm, &f(t))
}

/// `Date.prototype [ @@toPrimitive ] ( hint )`, §21.4.4.45:
/// 1. Let O be the this value.
/// 2. If O is not an Object, throw a TypeError exception.
/// 3. If hint is either "string" or "default", then a. Let tryFirst be string.
/// 4. Else if hint is "number", then a. Let tryFirst be number.
/// 5. Else, throw a TypeError exception.
/// 6. Return ? OrdinaryToPrimitive(O, tryFirst).
fn to_primitive(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_object(this) {
        return Err(vm.type_error("Date.prototype[Symbol.toPrimitive] called on non-object"));
    }
    let hint = vm
        .heap()
        .is_string(arg(args, 0))
        .then(|| vm.string_text(arg(args, 0)))
        .flatten();
    let names = match hint.as_deref() {
        Some("string" | "default") => ["toString", "valueOf"],
        Some("number") => ["valueOf", "toString"],
        _ => return Err(vm.type_error("Invalid hint")),
    };
    // OrdinaryToPrimitive, §7.1.1.1: the first callable method that returns
    // a non-Object wins.
    for n in names {
        let m = vm.get_named(this, n)?;
        if vm.heap().is_callable(m) {
            let result = vm.call(m, this, &[])?;
            if !vm.heap().is_object(result) {
                return Ok(result);
            }
        }
    }
    Err(vm.type_error("Cannot convert object to primitive value"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn utc0(_: f64, _: bool) -> f64 {
        0.0
    }

    /// A fixed offset of +01:00 that treats a local time and a UTC time alike.
    fn plus1(_: f64, _: bool) -> f64 {
        MS_PER_HOUR
    }

    fn p(s: &str) -> f64 {
        parse(s, &mut utc0)
    }

    #[test]
    fn day_and_year_arithmetic() {
        assert_eq!(day(0.0), 0.0);
        assert_eq!(day(-1.0), -1.0);
        assert_eq!(time_within_day(-1.0), MS_PER_DAY - 1.0);
        assert_eq!(days_in_year(1900.0), 365.0);
        assert_eq!(days_in_year(2000.0), 366.0);
        assert_eq!(days_in_year(2024.0), 366.0);
        assert_eq!(days_in_year(-1.0), 365.0);
        assert_eq!(day_from_year(1970.0), 0.0);
        assert_eq!(day_from_year(1971.0), 365.0);
        assert_eq!(year_from_time(0.0), 1970.0);
        assert_eq!(year_from_time(-1.0), 1969.0);
        assert_eq!(year_from_time(MAX_TIME), 275_760.0);
        assert_eq!(year_from_time(-MAX_TIME), -271_821.0);
        assert_eq!(week_day(0.0), 4.0);
        assert_eq!(week_day(-MS_PER_DAY), 3.0);
    }

    #[test]
    fn month_and_date_fields() {
        // 2000-02-29T12:34:56.789Z
        let t = 951_827_696_789.0;
        assert_eq!(year_from_time(t), 2000.0);
        assert_eq!(month_from_time(t), 1.0);
        assert_eq!(date_from_time(t), 29.0);
        assert_eq!(hour_from_time(t), 12.0);
        assert_eq!(min_from_time(t), 34.0);
        assert_eq!(sec_from_time(t), 56.0);
        assert_eq!(ms_from_time(t), 789.0);
        // The last millisecond of 1969 and of a leap year.
        assert_eq!(month_from_time(-1.0), 11.0);
        assert_eq!(date_from_time(-1.0), 31.0);
        assert_eq!(ms_from_time(-1.0), 999.0);
        assert_eq!(
            month_from_time(make_date(make_day(2000.0, 11.0, 31.0), 0.0)),
            11.0
        );
    }

    #[test]
    fn make_operations() {
        assert_eq!(make_time(1.0, 2.0, 3.0, 4.0), 3_723_004.0);
        assert!(make_time(f64::NAN, 0.0, 0.0, 0.0).is_nan());
        assert!(make_time(0.0, f64::INFINITY, 0.0, 0.0).is_nan());
        assert_eq!(make_time(0.0, 0.0, 0.0, 1.9), 1.0);
        assert_eq!(make_time(0.0, 0.0, 0.0, -1.9), -1.0);
        assert_eq!(make_day(1970.0, 0.0, 1.0), 0.0);
        assert_eq!(make_day(1970.0, 12.0, 1.0), 365.0);
        assert_eq!(make_day(1970.0, -1.0, 1.0), -31.0);
        assert_eq!(make_day(1970.0, 0.0, 0.0), -1.0);
        assert!(make_day(f64::INFINITY, 0.0, 1.0).is_nan());
        assert!(make_day(2.0e9, 0.0, 1.0).is_nan());
        assert!(make_day(1970.0, f64::NAN, 1.0).is_nan());
        assert!(make_date(f64::INFINITY, 0.0).is_nan());
        assert!(make_date(1.0e305, 0.0).is_nan());
        assert_eq!(make_full_year(99.9), 1999.0);
        assert_eq!(make_full_year(100.0), 100.0);
        assert_eq!(make_full_year(-0.5), 1900.0);
        assert!(make_full_year(f64::NAN).is_nan());
    }

    #[test]
    fn time_clip_limits() {
        assert_eq!(time_clip(MAX_TIME), MAX_TIME);
        assert!(time_clip(MAX_TIME + 1.0).is_nan());
        assert!(time_clip(f64::INFINITY).is_nan());
        assert_eq!(time_clip(1.9), 1.0);
        assert_eq!(time_clip(-1.9), -1.0);
        assert!(time_clip(-0.0).is_sign_positive());
    }

    #[test]
    fn local_time_and_utc_use_the_host_offset() {
        assert_eq!(local_time(0.0, &mut plus1), MS_PER_HOUR);
        assert_eq!(utc(MS_PER_HOUR, &mut plus1), 0.0);
        assert!(utc(f64::NAN, &mut plus1).is_nan());
        // A host that answers NaN has no offset.
        assert_eq!(local_time(5.0, &mut |_, _| f64::NAN), 5.0);
    }

    #[test]
    fn formats() {
        let t = 951_827_696_789.0;
        assert_eq!(to_iso_string(t), "2000-02-29T12:34:56.789Z");
        assert_eq!(to_iso_string(MAX_TIME), "+275760-09-13T00:00:00.000Z");
        assert_eq!(to_iso_string(-MAX_TIME), "-271821-04-20T00:00:00.000Z");
        assert_eq!(
            to_iso_string(-62_198_755_200_000.0),
            "-000001-01-01T00:00:00.000Z"
        );
        assert_eq!(to_utc_string(t), "Tue, 29 Feb 2000 12:34:56 GMT");
        assert_eq!(
            to_date_string(t, &mut utc0),
            "Tue Feb 29 2000 12:34:56 GMT+0000"
        );
        assert_eq!(
            to_date_string(t, &mut plus1),
            "Tue Feb 29 2000 13:34:56 GMT+0100"
        );
        assert_eq!(to_date_string(f64::NAN, &mut utc0), "Invalid Date");
        assert_eq!(time_zone_string(-5.5 * MS_PER_HOUR), "-0530");
        assert_eq!(year_string(-1.0), "-0001");
        assert_eq!(locale_date(t), "2/29/2000");
        assert_eq!(locale_time(t), "12:34:56 PM");
        assert_eq!(locale_time(0.0), "12:00:00 AM");
    }

    #[test]
    fn parses_the_date_time_string_format() {
        assert_eq!(p("1970"), 0.0);
        assert_eq!(p("1970-01"), 0.0);
        assert_eq!(p("1970-01-01"), 0.0);
        assert_eq!(p("1970-01-01T00:00Z"), 0.0);
        assert_eq!(p("1970-01-01T00:00:00.000Z"), 0.0);
        assert_eq!(p("2000-02-29T12:34:56.789Z"), 951_827_696_789.0);
        assert_eq!(p("2000-02-29T12:34:56.7Z"), 951_827_696_700.0);
        assert_eq!(p("2000-02-29T12:34:56.789123Z"), 951_827_696_789.0);
        assert_eq!(p("1970-01-01T01:00:00+01:00"), 0.0);
        assert_eq!(p("1970-01-01T00:00:00-01:30"), 5_400_000.0);
        assert_eq!(p("+275760-09-13T00:00:00.000Z"), MAX_TIME);
        assert_eq!(p("-000001-01-01T00:00:00Z"), -62_198_755_200_000.0);
        assert_eq!(p("1970-01-01T24:00:00Z"), MS_PER_DAY);
        // A date-time without an offset is local time; a date alone is UTC.
        assert_eq!(parse("1970-01-01T01:00:00", &mut plus1), 0.0);
        assert_eq!(parse("1970-01-01", &mut plus1), 0.0);
    }

    #[test]
    fn rejects_what_is_not_the_format() {
        for s in [
            "",
            "x",
            "-000000-01-01T00:00:00Z",
            "+275760-09-13T00:00:00.001Z",
            "1970-13-01",
            "1970-00-01",
            "1970-01-32",
            "1970-02-29",
            "1970-01-01T25:00Z",
            "1970-01-01T24:00:01Z",
            "1970-01-01T24:00:00.001Z",
            "1970-01-01T00:60Z",
            "1970-01-01T00:00:60Z",
            "1970-01-01T00Z",
            "1970-01-01T00:00:00.Z",
            "1970-01-01T00:00:00+0100",
            "1970-01-01T00:00:00+24:00",
            "1970-01-01 00:00:00Z extra",
            "197",
            "19700",
            "1970-1-1",
        ] {
            assert!(p(s).is_nan(), "{s:?} should be NaN");
        }
        // Not a leap year.
        assert!(p("1900-02-29").is_nan());
        assert_eq!(p("2000-02-29"), 951_782_400_000.0);
    }

    #[test]
    fn parses_what_to_string_prints() {
        let t = 951_827_696_000.0;
        assert_eq!(p("Tue Feb 29 2000 12:34:56 GMT+0000 (UTC)"), t);
        assert_eq!(p("Tue Feb 29 2000 13:34:56 GMT+0100"), t);
        assert_eq!(p("Tue Feb 29 2000 13:34:56 GMT+01:00"), t);
        assert_eq!(p("Tue, 29 Feb 2000 12:34:56 GMT"), t);
        assert_eq!(p("29 Feb 2000 12:34:56 GMT"), t);
        assert_eq!(p("Feb 29 2000"), 951_782_400_000.0);
        assert_eq!(
            p("Sat Jan 01 -0001 00:00:00 GMT+0000"),
            -62_198_755_200_000.0
        );
        // Without a zone it is local time.
        assert_eq!(parse("Thu Jan 01 1970 01:00:00", &mut plus1), 0.0);
        for s in [
            "Tue Feb 30 2000",
            "Tue Feb 29 2000 12:34:56 GMT+25:00",
            "Tue Feb 29 2000 12:34:56 PST",
            "Tue Feb 29 2000 12:34:56 GMT (unclosed",
            "Tue Feb 29 2000 junk",
            "Xyz 29 2000",
            "Tue Feb 2000",
        ] {
            assert!(p(s).is_nan(), "{s:?} should be NaN");
        }
    }

    #[test]
    fn to_string_round_trips_through_parse() {
        for t in [
            0.0,
            -1.0,
            951_827_696_000.0,
            MAX_TIME,
            -MAX_TIME,
            -62_198_755_200_000.0,
        ] {
            let tv = time_clip(t - t.rem_euclid(1000.0));
            assert_eq!(parse(&to_date_string(tv, &mut plus1), &mut plus1), tv);
            assert_eq!(p(&to_utc_string(tv)), tv);
            assert_eq!(p(&to_iso_string(tv)), tv);
        }
    }
}
