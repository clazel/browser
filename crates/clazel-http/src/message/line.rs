//! Executable line reading (RFC 9112 §2.1, §2.2), the status line (§4) and
//! field sections (§5, §5.2). Each function is proven to equal its spec
//! function in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::types::StatusLineBuf;
use crate::field::string::{
    append, at, copy, is_field_value, run_len_exec, strip_ows, strip_trailing_ows_exec,
};
use crate::field::types::FieldLineBuf;

verus! {

/// [`max_line`], executable.
pub const MAX_LINE: usize = 8192;

/// [`max_lines`], executable.
pub const MAX_LINES: usize = 256;

/// What follows the first `k` octets of `s`.
pub fn sub(s: &[u8], k: usize) -> (r: &[u8])
    requires
        k <= s.len(),
    ensures
        r@ == s@.skip(k as int),
{
    vstd::slice::slice_subrange(s, k, s.len())
}

/// The octets of `s` from `i` to `j`.
pub fn range(s: &[u8], i: usize, j: usize) -> (r: &[u8])
    requires
        i <= j <= s.len(),
    ensures
        r@ == s@.subrange(i as int, j as int),
{
    vstd::slice::slice_subrange(s, i, j)
}

/// Is there a CRLF at `i`?
fn crlf_at_exec(s: &[u8], i: usize) -> (r: bool)
    ensures
        r == crlf_at(s@, i as int),
{
    match (at(s, i), at(s, i.wrapping_add(1))) {
        (Some(a), Some(b)) => i < usize::MAX && a == 0x0D && b == 0x0A,
        _ => false,
    }
}

/// The result of [`read_line_exec`]: positions into its input.
pub enum LineExec {
    /// The line is `s[..end]`; what follows its CRLF is `s[end + 2..]`.
    Line {
        /// where the CRLF starts
        end: usize,
    },
    /// No CRLF yet.
    Incomplete,
    /// Past [`max_line`].
    TooLong,
}

/// `read_line` (§2.1, §2.2). Looks at no more than the first
/// `MAX_LINE + 2` octets.
pub fn read_line_exec(s: &[u8]) -> (out: LineExec)
    ensures
        match out {
            LineExec::Line { end } => end + 2 <= s.len()
                && read_line(s@) == (LineRead::Line { line: s@.take(end as int), rest: s@.skip(end + 2) }),
            LineExec::Incomplete => read_line(s@) is Incomplete,
            LineExec::TooLong => read_line(s@) is TooLong,
        },
{
    let mut i: usize = 0;
    while i < s.len().saturating_sub(1) && i <= MAX_LINE
        invariant
            i <= MAX_LINE + 1,
            i == 0 || i < s.len(),
            find_crlf_from(s@, 0) == find_crlf_from(s@, i as nat),
        decreases s.len() - i,
    {
        if crlf_at_exec(s, i) {
            proof {
                super::termination::lemma_find_crlf_from(s@, i as nat);
            }
            return LineExec::Line { end: i };
        }
        // Never saturates: i <= MAX_LINE.
        i = i.saturating_add(1);
    }
    proof {
        super::termination::lemma_find_crlf_from(s@, i as nat);
        if i + 1 >= s.len() {
            assert(find_crlf_from(s@, i as nat) is None);
        }
    }
    if i > MAX_LINE {
        // A CRLF at or after `i` is past the limit; with none, the input is
        // already longer than a line can be.
        LineExec::TooLong
    } else if s.len() > MAX_LINE + 1 {
        LineExec::TooLong
    } else {
        LineExec::Incomplete
    }
}

/// `parse_status_line` (§4, §2.3).
pub fn parse_status_line_exec(line: &[u8]) -> (out: Option<StatusLineBuf>)
    ensures
        match out {
            Some(sl) => parse_status_line(line@) == Some(sl@),
            None => parse_status_line(line@) is None,
        },
{
    if line.len() < 12 {
        return None;
    }
    let b = |i: usize| -> (c: u8)
        requires
            i < line.len(),
        ensures
            c == line@[i as int],
    {
        match line.get(i) {
            Some(c) => *c,
            None => 0,
        }
    };
    let digit = |c: u8| -> (r: bool)
        ensures
            r == crate::field::spec::is_digit(c),
    {
        (0x30..=0x39).contains(&c)
    };
    let name_ok = b(0) == 0x48 && b(1) == 0x54 && b(2) == 0x54 && b(3) == 0x50 && b(4) == 0x2F;
    assert(name_ok == (line@.take(5) == lit_http_slash())) by {
        if name_ok {
            assert(line@.take(5) =~= lit_http_slash());
        }
        if line@.take(5) == lit_http_slash() {
            assert(line@.take(5)[0] == line@[0]);
            assert(line@.take(5)[1] == line@[1]);
            assert(line@.take(5)[2] == line@[2]);
            assert(line@.take(5)[3] == line@[3]);
            assert(line@.take(5)[4] == line@[4]);
        }
    }
    let head_ok = name_ok && digit(b(5)) && b(6) == 0x2E && digit(b(7)) && b(5) == 0x31 && b(8) == 0x20
        && digit(b(9)) && digit(b(10)) && digit(b(11));
    // The line ends after the status code, or SP and a reason phrase follow.
    let tail_ok = line.len() == 12 || (b(12) == 0x20
        && crate::field::string::all_in_exec(sub(line, 13), &crate::field::spec::Class::FieldContent));
    if head_ok && tail_ok {
        // None of these saturates: each octet is a digit, so at least 0x30,
        // and the status is at most 999.
        let major = b(5).saturating_sub(0x30);
        let minor = b(7).saturating_sub(0x30);
        let status = (b(9).saturating_sub(0x30) as u16).saturating_mul(100)
            .saturating_add((b(10).saturating_sub(0x30) as u16).saturating_mul(10))
            .saturating_add(b(11).saturating_sub(0x30) as u16);
        let reason = if line.len() == 12 {
            Vec::new()
        } else {
            copy(sub(line, 13))
        };
        assert(reason@ =~= (if line@.len() == 12 { seq![] } else { line@.skip(13) }));
        Some(StatusLineBuf { major, minor, status, reason })
    } else {
        None
    }
}

/// `parse_field_line_start` (§5, §5.1).
pub fn parse_field_line_start_exec(line: &[u8]) -> (out: Option<FieldLineBuf>)
    ensures
        match out {
            Some(f) => parse_field_line_start(line@) == Some(f@),
            None => parse_field_line_start(line@) is None,
        },
{
    let n = run_len_exec(&crate::field::spec::Class::Tchar, line);
    if n > 0 && at(line, n) == Some(0x3Au8) {
        let name = copy(range(line, 0, n));
        // Never saturates: n < line.len().
        let value = copy(sub(line, n.saturating_add(1)));
        assert(name@ =~= line@.take(n as int));
        Some(FieldLineBuf { name, value })
    } else {
        None
    }
}

/// `finish_field_line` (§5.1, RFC 9110 §5.5).
fn finish_field_line_exec(raw: FieldLineBuf) -> (out: Option<FieldLineBuf>)
    ensures
        match out {
            Some(f) => finish_field_line(raw@) == Some(f@),
            None => finish_field_line(raw@) is None,
        },
{
    let value = strip_ows(raw.value.as_slice());
    if is_field_value(value.as_slice()) {
        Some(FieldLineBuf { name: raw.name, value })
    } else {
        None
    }
}

/// `flush_pending`: appends the pending line, finished, to `acc`; `false`
/// if it is not a valid field line.
pub fn flush_pending_exec(acc: &mut Vec<FieldLineBuf>, pending: Option<FieldLineBuf>) -> (ok: bool)
    ensures
        match flush_pending(crate::field::types::lines_view(old(acc)@), super::types::opt_line_view(pending)) {
            Some(fields) => ok && crate::field::types::lines_view(final(acc)@) == fields,
            None => !ok,
        },
{
    match pending {
        None => true,
        Some(raw) => match finish_field_line_exec(raw) {
            Some(line) => {
                let ghost before = crate::field::types::lines_view(acc@);
                let ghost l = line@;
                acc.push(line);
                assert(crate::field::types::lines_view(acc@) =~= before.push(l));
                true
            },
            None => false,
        },
    }
}

/// The result of [`read_section_exec`].
pub enum SectionExec {
    /// The field lines; what follows the empty line is `s[next..]`.
    Done {
        /// the field lines, values finished
        fields: Vec<FieldLineBuf>,
        /// where what follows the section starts
        next: usize,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a field section.
    Invalid,
}

/// `read_section(s, [], None, 0)` (§2.1, §5, §5.2).
pub fn read_section_exec(s: &[u8]) -> (out: SectionExec)
    ensures
        match out {
            SectionExec::Done { fields, next } => next <= s.len()
                && read_section(s@, seq![], None, 0) == (SectionRead::Done { fields: crate::field::types::lines_view(fields@), rest: s@.skip(next as int) }),
            SectionExec::Incomplete => read_section(s@, seq![], None, 0) is Incomplete,
            SectionExec::Invalid => read_section(s@, seq![], None, 0) is Invalid,
        },
{
    let mut acc: Vec<FieldLineBuf> = Vec::new();
    let mut pending: Option<FieldLineBuf> = None;
    let mut count: usize = 0;
    let mut pos: usize = 0;
    assert(s@.skip(0) =~= s@);
    assert(crate::field::types::lines_view(acc@) =~= Seq::<crate::field::spec::FieldLine>::empty());
    loop
        invariant
            pos <= s.len(),
            count <= MAX_LINES,
            read_section(s@, seq![], None, 0) == read_section(s@.skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(pending), count as nat),
        decreases s.len() - pos,
    {
        let rest = sub(s, pos);
        match read_line_exec(rest) {
            LineExec::Incomplete => return SectionExec::Incomplete,
            LineExec::TooLong => return SectionExec::Invalid,
            LineExec::Line { end } => {
                let line = range(rest, 0, end);
                assert(line@ =~= rest@.take(end as int));
                // Never saturates: end + 2 <= rest.len().
                let next = pos.saturating_add(end).saturating_add(2);
                assert(rest@.skip(end + 2) =~= s@.skip(next as int));
                if end == 0 {
                    let ok = flush_pending_exec(&mut acc, pending);
                    if ok {
                        return SectionExec::Done { fields: acc, next };
                    } else {
                        return SectionExec::Invalid;
                    }
                } else if count >= MAX_LINES {
                    return SectionExec::Invalid;
                } else {
                    let first = at(line, 0);
                    if first == Some(0x20u8) || first == Some(0x09u8) {
                        match pending {
                            None => return SectionExec::Invalid,
                            Some(raw) => {
                                let mut value = strip_trailing_ows_exec(raw.value.as_slice());
                                value.push(0x20);
                                let k = run_len_exec(&crate::field::spec::Class::Ows, line);
                                append(&mut value, sub(line, k));
                                let ghost v = strip_trailing_ows(raw.value@) + seq![0x20u8] + strip_leading_ows(line@);
                                assert(value@ =~= v);
                                pending = Some(FieldLineBuf { name: raw.name, value });
                            },
                        }
                    } else {
                        match parse_field_line_start_exec(line) {
                            None => return SectionExec::Invalid,
                            Some(raw) => {
                                let ok = flush_pending_exec(&mut acc, pending);
                                if !ok {
                                    return SectionExec::Invalid;
                                }
                                pending = Some(raw);
                            },
                        }
                    }
                    // Never saturates: count < MAX_LINES.
                    count = count.saturating_add(1);
                    pos = next;
                }
            },
        }
    }
}

} // verus!
