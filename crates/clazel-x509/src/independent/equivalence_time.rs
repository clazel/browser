//! `independent/der.rs`'s times and `Time` against `time/spec.rs` and
//! `tbs/spec.rs`'s `time_tlv`. UTCTime agrees with no condition at all
//! ([`lemma_utc_time`]). GeneralizedTime agrees except for a fraction, the year
//! 0000 and a leap second ([`lemma_generalized_time`]).

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::time::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// A `Moment` as the calendar fields of `time/spec.rs`.
pub open spec fn moment_time(m: i::Moment) -> t::CertificateTime {
    t::CertificateTime {
        year: m.year as u16,
        month: m.month as u8,
        day: m.day as u8,
        hour: m.hour as u8,
        minute: m.minute as u8,
        second: m.second as u8,
    }
}

/// The `Moment` of either alternative of `Time`.
pub open spec fn time_moment(y: s::Time) -> i::Moment {
    match y {
        s::Time::UtcTime(m) => m,
        s::Time::GeneralizedTime(m) => m,
    }
}

/// A `Time` `time/spec.rs` reads: no fraction and not the year 0000.
pub open spec fn time_in_domain(y: s::Time) -> bool {
    time_moment(y).fraction.len() == 0 && time_moment(y).year >= 1
}

/// Two ways to say `n` digits follow.
pub proof fn lemma_digits_at(s: Seq<u8>, at: nat, n: nat)
    requires
        at <= s.len(),
    ensures
        i::digits_at(s, at, n) == (at + n <= s.len() && t::digits_only(s, at as int, n as int)),
    decreases n,
{
    if n > 0 && at < s.len() {
        lemma_digits_at(s, at + 1, (n - 1) as nat);
        if at + n <= s.len() {
            if t::digits_only(s, at as int, n as int) {
                assert(b'0' <= s[at as int] && s[at as int] <= b'9');
                assert forall|k: int| (at + 1) <= k < (at + 1) + (n - 1) implies b'0' <= #[trigger] s[k]
                    && s[k] <= b'9' by {
                    assert(at <= k < at + n);
                }
            }
            if i::is_digit(s[at as int]) && t::digits_only(s, (at + 1) as int, n - 1) {
                assert forall|k: int| at <= k < at + n implies b'0' <= #[trigger] s[k] && s[k] <= b'9' by {
                    if k > at {
                        assert((at + 1) <= k < (at + 1) + (n - 1));
                    }
                }
            }
        }
    }
}

/// Two digits, read both ways.
pub proof fn lemma_two_digits(s: Seq<u8>, at: nat)
    requires
        at + 2 <= s.len(),
        t::digits_only(s, at as int, 2),
    ensures
        t::decimal_digits(s, at as int, 2) == i::two_digits(s, at),
        i::two_digits(s, at) < 100,
{
    let r = s.subrange(at as int, (at + 2) as int);
    let q = r.drop_last();
    assert(b'0' <= s[at as int] && s[at as int] <= b'9');
    assert(b'0' <= s[(at + 1) as int] && s[(at + 1) as int] <= b'9');
    assert(r.last() == s[(at + 1) as int]);
    assert(q.last() == s[at as int]);
    assert(q.drop_last() =~= Seq::<u8>::empty());
    assert(t::decimal_value(Seq::<u8>::empty()) == 0);
    assert(t::decimal_value(q) == (q.last() - b'0') as nat);
    assert(t::decimal_value(r) == t::decimal_value(q) * 10 + (r.last() - b'0') as nat);
}

/// Four digits, read both ways.
pub proof fn lemma_four_digits(s: Seq<u8>)
    requires
        s.len() >= 4,
        t::digits_only(s, 0, 4),
    ensures
        t::decimal_digits(s, 0, 4) == i::two_digits(s, 0) * 100 + i::two_digits(s, 2),
{
    assert forall|k: int| 0 <= k < 2 implies b'0' <= #[trigger] s[k] && s[k] <= b'9' by {
        assert(0 <= k < 4);
    }
    assert forall|k: int| 2 <= k < 4 implies b'0' <= #[trigger] s[k] && s[k] <= b'9' by {
        assert(0 <= k < 4);
    }
    lemma_two_digits(s, 0);
    lemma_two_digits(s, 2);
    let r = s.subrange(0, 4);
    let r3 = r.drop_last();
    let r2 = r3.drop_last();
    assert(r2 =~= s.subrange(0, 2));
    assert(r.last() == s[3]);
    assert(r3.last() == s[2]);
    assert(t::decimal_value(r) == t::decimal_value(r3) * 10 + (r.last() - b'0') as nat);
    assert(t::decimal_value(r3) == t::decimal_value(r2) * 10 + (r3.last() - b'0') as nat);
    assert(t::decimal_digits(s, 0, 2) == t::decimal_value(r2));
    assert(i::two_digits(s, 2) == ((s[2] - 0x30) * 10 + (s[3] - 0x30)) as nat);
}

/// Days in a month, for a month that exists.
pub proof fn lemma_days_in_month(year: nat, month: nat)
    requires
        1 <= month <= 12,
    ensures
        i::days_in_month(year, month) == t::days_in_month(year, month),
{
}

/// A digit run of `count` digits is a sub-run of a longer one.
pub proof fn lemma_digits_sub(s: Seq<u8>, n: nat, at: nat, count: nat)
    requires
        at + count <= n,
        t::digits_only(s, 0, n as int),
    ensures
        t::digits_only(s, at as int, count as int),
{
    assert forall|k: int| at <= k < at + count implies b'0' <= #[trigger] s[k] && s[k] <= b'9' by {
        assert(0 <= k < n);
    }
}

/// **UTCTime agrees everywhere.** No fraction exists, the pivots are the same
/// and both bound seconds by 59.
pub proof fn lemma_utc_time(c: Seq<u8>)
    ensures
        t::decode_time(t::TimeKind::Utc, c) == match i::utc_time_contents(c) {
            Some(m) => Some(moment_time(m)),
            None => None,
        },
        match i::utc_time_contents(c) {
            Some(m) => m.fraction.len() == 0 && m.year >= 1,
            None => true,
        },
{
    lemma_digits_at(c, 0, 12);
    if c.len() == 13 && c[12] == 0x5A && t::digits_only(c, 0, 12) {
        lemma_digits_sub(c, 12, 0, 2);
        lemma_digits_sub(c, 12, 2, 2);
        lemma_digits_sub(c, 12, 4, 2);
        lemma_digits_sub(c, 12, 6, 2);
        lemma_digits_sub(c, 12, 8, 2);
        lemma_digits_sub(c, 12, 10, 2);
        lemma_two_digits(c, 0);
        lemma_two_digits(c, 2);
        lemma_two_digits(c, 4);
        lemma_two_digits(c, 6);
        lemma_two_digits(c, 8);
        lemma_two_digits(c, 10);
        let m = i::Moment {
            year: i::rationalized_year(i::two_digits(c, 0)),
            month: i::two_digits(c, 2),
            day: i::two_digits(c, 4),
            hour: i::two_digits(c, 6),
            minute: i::two_digits(c, 8),
            second: i::two_digits(c, 10),
            fraction: Seq::<u8>::empty(),
        };
        assert(t::utc_year(i::two_digits(c, 0)) == i::rationalized_year(i::two_digits(c, 0)));
        if 1 <= m.month && m.month <= 12 {
            lemma_days_in_month(m.year, m.month);
        }
    }
}

/// **GeneralizedTime.** `time/spec.rs` reads exactly `YYYYMMDDhhmmssZ` of RFC
/// 5280 with years 1 to 9999 and second 60 at 23:59; `der.rs` reads X.690's
/// form, with a fraction, and years 0 to 9999 without second 60.
pub proof fn lemma_generalized_time(c: Seq<u8>)
    ensures
        match t::decode_time(t::TimeKind::Generalized, c) {
            Some(x) => x.second != 60 ==> {
                &&& i::generalized_time_contents(c) is Some
                &&& moment_time(i::generalized_time_contents(c)->Some_0) == x
                &&& i::generalized_time_contents(c)->Some_0.fraction.len() == 0
                &&& i::generalized_time_contents(c)->Some_0.year >= 1
            },
            None => match i::generalized_time_contents(c) {
                Some(m) => m.fraction.len() != 0 || m.year == 0,
                None => true,
            },
        },
        match i::generalized_time_contents(c) {
            Some(m) => m.fraction.len() == 0 && m.year >= 1 ==> t::decode_time(
                t::TimeKind::Generalized,
                c,
            ) == Some(moment_time(m)),
            None => true,
        },
{
    lemma_digits_at(c, 0, 14);
    if c.len() >= 15 && t::digits_only(c, 0, 14) && c[(c.len() - 1) as int] == 0x5A {
        lemma_digits_sub(c, 14, 0, 4);
        lemma_digits_sub(c, 14, 0, 2);
        lemma_digits_sub(c, 14, 2, 2);
        lemma_digits_sub(c, 14, 4, 2);
        lemma_digits_sub(c, 14, 6, 2);
        lemma_digits_sub(c, 14, 8, 2);
        lemma_digits_sub(c, 14, 10, 2);
        lemma_digits_sub(c, 14, 12, 2);
        lemma_four_digits(c);
        lemma_two_digits(c, 0);
        lemma_two_digits(c, 2);
        lemma_two_digits(c, 4);
        lemma_two_digits(c, 6);
        lemma_two_digits(c, 8);
        lemma_two_digits(c, 10);
        lemma_two_digits(c, 12);
        let year = i::two_digits(c, 0) * 100 + i::two_digits(c, 2);
        let month = i::two_digits(c, 4);
        if 1 <= month && month <= 12 {
            lemma_days_in_month(year, month);
        }
    }
}

/// `time_tlv` and `Time`.
pub proof fn lemma_time_tlv(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match crate::tbs::spec::time_tlv(b, pos, end) {
            Some((x, n)) => {
                &&& d::read_tlv(b, pos, end) is Some
                &&& d::read_tlv(b, pos, end)->Some_0.cend == n
                &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
                &&& pos < n <= end
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& x.second != 60 ==> {
                    &&& super::structures::decode_time(i::parse_tlv(sl(b, pos, end))->Some_0) is Some
                    &&& moment_time(
                        time_moment(super::structures::decode_time(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
                    ) == x
                    &&& time_in_domain(super::structures::decode_time(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0)
                }
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => match super::structures::decode_time(u) {
                    Some(y) => !time_in_domain(y),
                    None => true,
                },
                None => true,
            },
        },
        match i::parse_tlv(sl(b, pos, end)) {
            Some(u) => match super::structures::decode_time(u) {
                Some(y) => time_in_domain(y) ==> {
                    &&& crate::tbs::spec::time_tlv(b, pos, end) is Some
                    &&& crate::tbs::spec::time_tlv(b, pos, end)->Some_0.0 == moment_time(time_moment(y))
                },
                None => true,
            },
            None => true,
        },
{
    lemma_tlv(b, pos, end);
    if let Some(r) = d::read_tlv(b, pos, end) {
        let c = sl(b, r.cstart, r.cend);
        lemma_utc_time(c);
        lemma_generalized_time(c);
        if !tag_is_reserved(r.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, r, u, d::UTC_TIME, false);
            lemma_has_universal_tag(b, pos, r, u, d::GENERALIZED_TIME, false);
        }
    }
}

} // verus!
