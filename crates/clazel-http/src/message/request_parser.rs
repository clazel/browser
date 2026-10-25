//! The executable request parser (RFC 9112 §3, §2.1), proven to meet
//! [`super::contract::parse_request_ensures`]. It exists for the tests of
//! the serializer; the browser never parses requests.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::line::{LineExec, SectionExec, range, read_line_exec, read_section_exec, sub};
use super::types::{RequestBuf, RequestParseBuf};
use crate::field::string::{at, copy, run_len_exec, slice_eq};

verus! {

/// `vchar_run_len`, executable.
fn vchar_run_exec(s: &[u8]) -> (n: usize)
    ensures
        n == super::request::vchar_run_len(s@),
        n <= s.len(),
{
    assert(s@.skip(0) =~= s@);
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            super::request::vchar_run_len(s@) == i + super::request::vchar_run_len(s@.skip(i as int)),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => return i,
        };
        assert(s@.skip(i as int)[0] == s@[i as int]);
        assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
        if !(0x21..=0x7E).contains(&c) {
            return i;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    i
}

/// `parse_request_line` (§3): the method and the target.
fn parse_request_line_exec(line: &[u8]) -> (out: Option<(Vec<u8>, Vec<u8>)>)
    ensures
        match out {
            Some((method, target)) => super::request::parse_request_line(line@) == Some((method@, target@)),
            None => super::request::parse_request_line(line@) is None,
        },
{
    let n = run_len_exec(&crate::field::spec::Class::Tchar, line);
    if n == 0 || at(line, n) != Some(0x20u8) {
        return None;
    }
    // Never saturates: n < line.len().
    let after = sub(line, n.saturating_add(1));
    let m = vchar_run_exec(after);
    // Never saturates: m <= after.len().
    if m == 0 || after.len().saturating_sub(m) != 9 || at(after, m) != Some(0x20u8) {
        return None;
    }
    // Never saturates: m < after.len().
    let version = sub(after, m.saturating_add(1));
    let http_1_1: [u8; 8] = [0x48, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31];
    let ok = slice_eq(version, http_1_1.as_slice());
    assert(http_1_1@ =~= lit_http_1_1());
    if !ok {
        return None;
    }
    let method = copy(range(line, 0, n));
    let target = copy(range(after, 0, m));
    assert(method@ =~= line@.take(n as int));
    assert(target@ =~= after@.take(m as int));
    Some((method, target))
}

/// `parse_request` (§2.1, §3, §5) over all of `s`.
pub fn parse_request_exec(s: &[u8]) -> (out: RequestParseBuf)
    ensures
        super::contract::parse_request_ensures(s@, out@),
{
    match read_line_exec(s) {
        LineExec::Incomplete => RequestParseBuf::Incomplete,
        LineExec::TooLong => RequestParseBuf::Invalid,
        LineExec::Line { end } => {
            let line = range(s, 0, end);
            assert(line@ =~= s@.take(end as int));
            match parse_request_line_exec(line) {
                None => RequestParseBuf::Invalid,
                Some((method, target)) => {
                    // Never saturates: end + 2 <= s.len().
                    let after = sub(s, end.saturating_add(2));
                    match read_section_exec(after) {
                        SectionExec::Done { fields, next } => {
                            let rest = copy(sub(after, next));
                            RequestParseBuf::Done { request: RequestBuf { method, target, fields }, rest }
                        },
                        SectionExec::Incomplete => RequestParseBuf::Incomplete,
                        SectionExec::Invalid => RequestParseBuf::Invalid,
                    }
                },
            }
        },
    }
}

} // verus!
