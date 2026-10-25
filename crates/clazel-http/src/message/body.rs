//! Executable message body length (RFC 9112 §6.3), chunked decoding
//! (§7.1) and the response (§2.1). Each function is proven to equal its
//! spec function in [`super::spec`]. The parser that is fed bytes as they
//! arrive is in [`super::incremental`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::line::{
    LineExec, SectionExec, parse_status_line_exec, range, read_line_exec, read_section_exec, sub,
};
use super::types::{HeadBuf, ParseBuf, ResponseBuf};
use crate::field::content_length::parse_content_length_lines;
use crate::field::contract::ContentLengthError;
use crate::field::params::{parse_parameter_value_exec, parse_transfer_encoding};
use crate::field::section::{combine, field_values_named};
use crate::field::string::{append, at, copy, field_name_eq, run_len_exec};

verus! {

/// [`max_body`], executable.
pub const MAX_BODY: u64 = 0x400_0000;

/// The result of [`read_head_exec`].
pub enum HeadExec {
    /// The head; what follows it is `s[next..]`.
    Done {
        /// the head
        head: HeadBuf,
        /// where what follows the head starts
        next: usize,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a response head.
    Invalid,
}

/// `read_head` (§2.1, §2.2, §4).
pub fn read_head_exec(s: &[u8]) -> (out: HeadExec)
    ensures
        match out {
            HeadExec::Done { head, next } => next <= s.len()
                && read_head(s@) == (HeadRead::Done { head: head@, rest: s@.skip(next as int) }),
            HeadExec::Incomplete => read_head(s@) is Incomplete,
            HeadExec::Invalid => read_head(s@) is Invalid,
        },
{
    match read_line_exec(s) {
        LineExec::Incomplete => HeadExec::Incomplete,
        LineExec::TooLong => HeadExec::Invalid,
        LineExec::Line { end } => {
            let line = range(s, 0, end);
            assert(line@ =~= s@.take(end as int));
            match parse_status_line_exec(line) {
                None => HeadExec::Invalid,
                Some(status_line) => {
                    // Never saturates: end + 2 <= s.len().
                    let after = sub(s, end.saturating_add(2));
                    match read_section_exec(after) {
                        SectionExec::Done { fields, next } => {
                            // Never saturates: end + 2 + next <= s.len().
                            let total = end.saturating_add(2).saturating_add(next);
                            assert(after@.skip(next as int) =~= s@.skip(total as int));
                            HeadExec::Done { head: HeadBuf { status_line, fields }, next: total }
                        },
                        SectionExec::Incomplete => HeadExec::Incomplete,
                        SectionExec::Invalid => HeadExec::Invalid,
                    }
                },
            }
        },
    }
}

/// How the body is delimited, viewed as [`BodyLength`].
pub enum BodyLengthExec {
    /// No body.
    NoBody,
    /// Exactly this many octets (at most [`MAX_BODY`]).
    Length(u64),
    /// Chunked.
    Chunked,
    /// Until the connection closes.
    Close,
    /// Invalid framing.
    Invalid,
    /// A coding we cannot decode.
    Unsupported,
}

/// The view of a [`BodyLengthExec`].
pub open spec fn body_length_view(b: BodyLengthExec) -> BodyLength {
    match b {
        BodyLengthExec::NoBody => BodyLength::NoBody,
        BodyLengthExec::Length(n) => BodyLength::Length(n as nat),
        BodyLengthExec::Chunked => BodyLength::Chunked,
        BodyLengthExec::Close => BodyLength::Close,
        BodyLengthExec::Invalid => BodyLength::Invalid,
        BodyLengthExec::Unsupported => BodyLength::Unsupported,
    }
}

/// `body_length` (§6.3, as a client).
pub fn body_length_exec(head: &HeadBuf, request_is_head: bool) -> (out: BodyLengthExec)
    ensures
        body_length_view(out) == body_length(head@, request_is_head),
        match out {
            BodyLengthExec::Length(n) => n <= MAX_BODY,
            _ => true,
        },
{
    let status = head.status_line.status;
    let te = field_values_named(head.fields.as_slice(),
        &[0x74, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67]);
    let cl = field_values_named(head.fields.as_slice(),
        &[0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68]);
    assert(crate::field::types::strings_view(te@).len() == te@.len());
    assert(crate::field::types::strings_view(cl@).len() == cl@.len());
    // 1.
    if request_is_head || (100..=199).contains(&status) || status == 204 || status == 304 {
        return BodyLengthExec::NoBody;
    }
    // 3.
    if !te.is_empty() && !cl.is_empty() {
        return BodyLengthExec::Invalid;
    }
    // 4.
    if !te.is_empty() {
        if head.status_line.major == 1 && head.status_line.minor == 0 {
            return BodyLengthExec::Invalid;
        }
        let combined = combine(te.as_slice());
        match parse_transfer_encoding(combined.as_slice()) {
            None => return BodyLengthExec::Invalid,
            Some(codings) => {
                let ghost view = crate::field::types::codings_view(codings@);
                match codings.last() {
                    None => return BodyLengthExec::Invalid,
                    Some(last) => {
                        assert(view.last() == last@);
                        if field_name_eq(last.name.as_slice(), &[0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64]) {
                            if !last.parameters.is_empty() {
                                return BodyLengthExec::Invalid;
                            } else if codings.len() == 1 {
                                return BodyLengthExec::Chunked;
                            } else {
                                return BodyLengthExec::Unsupported;
                            }
                        } else {
                            return BodyLengthExec::Unsupported;
                        }
                    },
                }
            },
        }
    }
    // 5., 6.
    if !cl.is_empty() {
        match parse_content_length_lines(cl.as_slice()) {
            Ok(n) => if n > MAX_BODY {
                BodyLengthExec::Invalid
            } else {
                BodyLengthExec::Length(n)
            },
            Err(ContentLengthError::TooLarge) => BodyLengthExec::Invalid,
            Err(ContentLengthError::Invalid) => BodyLengthExec::Invalid,
        }
    } else {
        // 8.
        BodyLengthExec::Close
    }
}

/// `is_hexdig` (RFC 5234 B.1).
fn is_hexdig_exec(c: u8) -> (r: bool)
    ensures
        r == is_hexdig(c),
{
    (0x30..=0x39).contains(&c) || (0x41..=0x46).contains(&c) || (0x61..=0x66).contains(&c)
}

/// Is `s[i]` a hex digit?
fn hex_at(s: &[u8], i: usize) -> (r: bool)
    ensures
        r == (i < s.len() && is_hexdig(s@[i as int])),
{
    match s.get(i) {
        Some(c) => is_hexdig_exec(*c),
        None => false,
    }
}

/// `hexdig_value`.
fn hexdig_value_exec(c: u8) -> (r: u64)
    requires
        is_hexdig(c),
    ensures
        r as nat == hexdig_value(c),
        r < 16,
{
    // None of these saturates: c is in the range its branch tests.
    if (0x30..=0x39).contains(&c) {
        c.saturating_sub(0x30) as u64
    } else if (0x41..=0x46).contains(&c) {
        c.saturating_sub(0x41).saturating_add(10) as u64
    } else {
        c.saturating_sub(0x61).saturating_add(10) as u64
    }
}

/// One round of `is_chunk_ext` on `t`.
enum ExtStep {
    /// The answer for all of `t`.
    Answer(bool),
    /// The answer for `t` is the answer for `t[k..]`, with `k > 0`.
    Next(usize),
}

/// One round of `is_chunk_ext` (§7.1.1): `BWS ";" BWS chunk-ext-name [ BWS
/// "=" BWS chunk-ext-val ]` at the start of `t`.
fn chunk_ext_step(t: &[u8]) -> (out: ExtStep)
    ensures
        match out {
            ExtStep::Answer(r) => r == is_chunk_ext(t@),
            ExtStep::Next(k) => 0 < k <= t.len() && is_chunk_ext(t@) == is_chunk_ext(t@.skip(k as int)),
        },
{
    if t.is_empty() {
        return ExtStep::Answer(true);
    }
    let ak = run_len_exec(&crate::field::spec::Class::Ows, t);
    let a = sub(t, ak);
    if at(a, 0) != Some(0x3Bu8) {
        return ExtStep::Answer(false);
    }
    let a1 = sub(a, 1);
    assert(a1@ =~= a@.drop_first());
    let bk = run_len_exec(&crate::field::spec::Class::Ows, a1);
    let b = sub(a1, bk);
    let n = run_len_exec(&crate::field::spec::Class::Tchar, b);
    if n == 0 {
        return ExtStep::Answer(false);
    }
    // Never saturates: at most t.len().
    let c = sub(b, n);
    let c_pos = ak.saturating_add(1).saturating_add(bk).saturating_add(n);
    assert(c@ =~= t@.skip(c_pos as int));
    chunk_ext_value_step(t, c_pos)
}

/// [`is_chunk_ext`]'s answer once the chunk-ext-name has been read and `c`
/// follows it: `[ BWS "=" BWS chunk-ext-val ]`, then the next round.
spec fn chunk_ext_after_name(c: Seq<u8>) -> bool {
    let d = strip_leading_ows(c);
    if d.len() > 0 && d[0] == 0x3D {
        match parse_parameter_value(strip_leading_ows(d.drop_first())) {
            Some((_, rest)) => is_chunk_ext(rest),
            None => false,
        }
    } else {
        is_chunk_ext(c)
    }
}

/// The rest of [`chunk_ext_step`], from `c_pos`, just past the
/// chunk-ext-name: `[ BWS "=" BWS chunk-ext-val ]`.
fn chunk_ext_value_step(t: &[u8], c_pos: usize) -> (out: ExtStep)
    requires
        0 < c_pos <= t.len(),
        is_chunk_ext(t@) == chunk_ext_after_name(t@.skip(c_pos as int)),
    ensures
        match out {
            ExtStep::Answer(r) => r == is_chunk_ext(t@),
            ExtStep::Next(k) => 0 < k <= t.len() && is_chunk_ext(t@) == is_chunk_ext(t@.skip(k as int)),
        },
{
    let c = sub(t, c_pos);
    let dk = run_len_exec(&crate::field::spec::Class::Ows, c);
    let d = sub(c, dk);
    if at(d, 0) == Some(0x3Du8) {
        let d1 = sub(d, 1);
        assert(d1@ =~= d@.drop_first());
        let ek = run_len_exec(&crate::field::spec::Class::Ows, d1);
        let e = sub(d1, ek);
        match parse_parameter_value_exec(e) {
            None => ExtStep::Answer(false),
            Some((_, k)) => {
                let next = c_pos.saturating_add(dk).saturating_add(1).saturating_add(ek).saturating_add(k);
                assert(e@.skip(k as int) =~= t@.skip(next as int));
                ExtStep::Next(next)
            },
        }
    } else {
        ExtStep::Next(c_pos)
    }
}

/// `is_chunk_ext` (§7.1.1).
fn is_chunk_ext_exec(s: &[u8]) -> (r: bool)
    ensures
        r == is_chunk_ext(s@),
{
    let mut pos: usize = 0;
    assert(s@.skip(0) =~= s@);
    loop
        invariant
            pos <= s.len(),
            is_chunk_ext(s@) == is_chunk_ext(s@.skip(pos as int)),
        decreases s.len() - pos,
    {
        let t = sub(s, pos);
        match chunk_ext_step(t) {
            ExtStep::Answer(r) => return r,
            ExtStep::Next(k) => {
                assert(t@.skip(k as int) =~= s@.skip((pos + k) as int));
                // Never saturates: pos + k <= s.len().
                pos = pos.saturating_add(k);
            },
        }
    }
}

/// The result of [`parse_chunk_size_line_exec`].
pub enum ChunkSize {
    /// A size of at most [`MAX_BODY`].
    Size(u64),
    /// A valid size line whose size is greater than [`MAX_BODY`].
    TooBig,
    /// Not a size line.
    Invalid,
}

/// `parse_chunk_size_line` (§7.1, §7.1.1), with sizes above the body
/// limit reported without their value.
pub fn parse_chunk_size_line_exec(line: &[u8]) -> (out: ChunkSize)
    ensures
        match out {
            ChunkSize::Size(v) => v <= MAX_BODY && parse_chunk_size_line(line@) == Some(v as nat),
            ChunkSize::TooBig => parse_chunk_size_line(line@) is Some
                && parse_chunk_size_line(line@)->Some_0 > max_body(),
            ChunkSize::Invalid => parse_chunk_size_line(line@) is None,
        },
{
    let mut i: usize = 0;
    let mut v: u64 = 0;
    let mut big = false;
    assert(line@.skip(0) =~= line@);
    assert(line@.take(0) =~= Seq::<u8>::empty());
    while hex_at(line, i)
        invariant
            i <= line.len(),
            hex_run_len(line@) == i + hex_run_len(line@.skip(i as int)),
            big ==> hex_value(line@.take(i as int)) > max_body(),
            !big ==> v as nat == hex_value(line@.take(i as int)) && v <= MAX_BODY,
        decreases line.len() - i,
    {
        let c = match line.get(i) {
            Some(c) => *c,
            None => 0x30,
        };
        let d = hexdig_value_exec(c);
        let ghost before = hex_value(line@.take(i as int));
        assert(line@.take(i + 1).drop_last() =~= line@.take(i as int));
        assert(line@.take(i + 1).last() == c);
        assert(hex_value(line@.take(i + 1)) == before * 16 + d as nat);
        assert(line@.skip(i as int)[0] == c);
        assert(line@.skip(i as int).drop_first() =~= line@.skip(i + 1));
        if big {
            assert(before * 16 + d as nat > max_body()) by (nonlinear_arith)
                requires before > max_body();
        } else {
            // Never saturates: v <= MAX_BODY and d < 16.
            let w = v.saturating_mul(16).saturating_add(d);
            if w > MAX_BODY {
                big = true;
            } else {
                v = w;
            }
        }
        // Never saturates: i < line.len().
        i = i.saturating_add(1);
    }
    assert(hex_run_len(line@.skip(i as int)) == 0) by {
        if i < line.len() {
            assert(line@.skip(i as int)[0] == line@[i as int]);
        }
    }
    if i == 0 || !is_chunk_ext_exec(sub(line, i)) {
        return ChunkSize::Invalid;
    }
    if big {
        ChunkSize::TooBig
    } else {
        ChunkSize::Size(v)
    }
}

/// Is there a CRLF at `i`?
pub fn crlf_at_exec(s: &[u8], i: usize) -> (r: bool)
    ensures
        r == crlf_at(s@, i as int),
{
    match (at(s, i), at(s, i.wrapping_add(1))) {
        (Some(a), Some(b)) => i < usize::MAX && a == 0x0D && b == 0x0A,
        _ => false,
    }
}

/// The result of [`read_chunks_exec`].
pub enum BodyExec {
    /// The decoded body; what follows the message is `s[next..]`.
    Done {
        /// the decoded content
        body: Vec<u8>,
        /// where what follows the message starts
        next: usize,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a chunked body.
    Invalid,
}

/// `read_chunks(s, [])` (§7.1, §7.1.3).
pub fn read_chunks_exec(s: &[u8]) -> (out: BodyExec)
    ensures
        match out {
            BodyExec::Done { body, next } => next <= s.len()
                && read_chunks(s@, seq![]) == (BodyRead::Done { body: body@, rest: s@.skip(next as int) }),
            BodyExec::Incomplete => read_chunks(s@, seq![]) is Incomplete,
            BodyExec::Invalid => read_chunks(s@, seq![]) is Invalid,
        },
{
    let mut body: Vec<u8> = Vec::new();
    let mut pos: usize = 0;
    assert(s@.skip(0) =~= s@);
    assert(body@ =~= Seq::<u8>::empty());
    loop
        invariant
            pos <= s.len(),
            body.len() <= MAX_BODY,
            read_chunks(s@, seq![]) == read_chunks(s@.skip(pos as int), body@),
        decreases s.len() - pos,
    {
        let rest = sub(s, pos);
        match read_line_exec(rest) {
            LineExec::Incomplete => return BodyExec::Incomplete,
            LineExec::TooLong => return BodyExec::Invalid,
            LineExec::Line { end } => {
                let line = range(rest, 0, end);
                assert(line@ =~= rest@.take(end as int));
                // Never saturates: end + 2 <= rest.len().
                let data = sub(rest, end.saturating_add(2));
                match parse_chunk_size_line_exec(line) {
                    ChunkSize::Invalid => return BodyExec::Invalid,
                    ChunkSize::TooBig => return BodyExec::Invalid,
                    ChunkSize::Size(size) => {
                        if size == 0 {
                            match read_section_exec(data) {
                                SectionExec::Done { fields: _, next } => {
                                    // Never saturates: this is a position in s.
                                    let after = pos.saturating_add(end).saturating_add(2).saturating_add(next);
                                    assert(data@.skip(next as int) =~= s@.skip(after as int));
                                    return BodyExec::Done { body, next: after };
                                },
                                SectionExec::Incomplete => return BodyExec::Incomplete,
                                SectionExec::Invalid => return BodyExec::Invalid,
                            }
                        }
                        // Never saturates: both are at most MAX_BODY.
                        if (body.len() as u64).saturating_add(size) > MAX_BODY {
                            return BodyExec::Invalid;
                        }
                        let size = size as usize;
                        // Never saturates: size <= MAX_BODY.
                        if data.len() < size.saturating_add(2) {
                            return BodyExec::Incomplete;
                        }
                        if !crlf_at_exec(data, size) {
                            return BodyExec::Invalid;
                        }
                        let ghost before = body@;
                        append(&mut body, range(data, 0, size));
                        assert(body@ =~= before + data@.take(size as int));
                        // Never saturates: this is a position in s.
                        let next = pos.saturating_add(end).saturating_add(2).saturating_add(size).saturating_add(2);
                        assert(data@.skip(size + 2) =~= s@.skip(next as int));
                        pos = next;
                    },
                }
            },
        }
    }
}

/// `parse_response` (§2.1, §6.3, §7.1) over all of `s`.
pub fn parse_response_exec(s: &[u8], request_is_head: bool) -> (out: ParseBuf)
    ensures
        out@ == parse_response(s@, request_is_head),
{
    match read_head_exec(s) {
        HeadExec::Incomplete => ParseBuf::Incomplete,
        HeadExec::Invalid => ParseBuf::Invalid,
        HeadExec::Done { head, next } => {
            let rest = sub(s, next);
            match body_length_exec(&head, request_is_head) {
                BodyLengthExec::NoBody => {
                    let r = ResponseBuf { status_line: head.status_line, fields: head.fields, body: Vec::new() };
                    assert(r.body@ =~= Seq::<u8>::empty());
                    ParseBuf::Done { response: r, rest: copy(rest) }
                },
                BodyLengthExec::Length(n) => {
                    let n = n as usize;
                    if rest.len() >= n {
                        let body = copy(range(rest, 0, n));
                        assert(body@ =~= rest@.take(n as int));
                        ParseBuf::Done { response: ResponseBuf { status_line: head.status_line, fields: head.fields, body }, rest: copy(sub(rest, n)) }
                    } else {
                        ParseBuf::Incomplete
                    }
                },
                BodyLengthExec::Chunked => match read_chunks_exec(rest) {
                    BodyExec::Done { body, next: after } => {
                        ParseBuf::Done { response: ResponseBuf { status_line: head.status_line, fields: head.fields, body }, rest: copy(sub(rest, after)) }
                    },
                    BodyExec::Incomplete => ParseBuf::Incomplete,
                    BodyExec::Invalid => ParseBuf::Invalid,
                },
                BodyLengthExec::Close => if rest.len() as u64 > MAX_BODY {
                    ParseBuf::Invalid
                } else {
                    ParseBuf::Incomplete
                },
                BodyLengthExec::Invalid => ParseBuf::Invalid,
                BodyLengthExec::Unsupported => ParseBuf::Unsupported,
            }
        },
    }
}

/// `parse_response_at_close` (§6.3 steps 6 and 8) over all of `s`.
pub fn parse_response_at_close_exec(s: &[u8], request_is_head: bool) -> (out: ParseBuf)
    ensures
        out@ == parse_response_at_close(s@, request_is_head),
{
    let first = parse_response_exec(s, request_is_head);
    match first {
        ParseBuf::Incomplete => match read_head_exec(s) {
            HeadExec::Done { head, next } => match body_length_exec(&head, request_is_head) {
                BodyLengthExec::Close => {
                    let body = copy(sub(s, next));
                    let ghost h = head@;
                    let r = ParseBuf::Done { response: ResponseBuf { status_line: head.status_line, fields: head.fields, body }, rest: Vec::new() };
                    assert(r@ == (Parse::Done { response: response_of(h, s@.skip(next as int)), rest: Seq::<u8>::empty() }));
                    r
                },
                _ => ParseBuf::Invalid,
            },
            _ => ParseBuf::Invalid,
        },
        decided => decided,
    }
}

} // verus!

/// The parser fed bytes as they arrive lives in [`super::incremental`].
pub use super::incremental::ResponseParser;
