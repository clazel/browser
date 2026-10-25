//! The response parser that is fed bytes as they arrive (RFC 9112 §2.1,
//! §6.3, §7.1), proven to meet [`super::contract`]'s `feed_ensures`: each
//! answer is [`parse_response`]'s for everything received.
//!
//! It is incremental: it keeps where it is (the status line, the field
//! lines read so far, the body length, the chunks decoded so far) and on
//! each feed reads only from there. A line not yet ended by its CRLF is
//! scanned again from its start on the next feed, but a line is at most
//! [`max_line`] octets, so a response costs time linear in its size
//! (times at most that bound) however it is split, where re-parsing
//! everything on each feed was quadratic. What makes that sound is the fact
//! `super::lemmas` proves for every reader: appending bytes keeps a
//! finished step finished, with the same result. The parser's invariant
//! ([`ResponseParser::wf`]) says exactly that, for every continuation of
//! the bytes received: parsing everything from the start equals resuming
//! from the saved state.
//!
//! After it has answered anything but `Incomplete`, the state is dropped,
//! and a later `feed` (which the contract does not forbid) re-parses
//! everything from the start with [`parse_response_exec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::body::{
    BodyLengthExec, ChunkSize, MAX_BODY, body_length_exec, crlf_at_exec,
    parse_chunk_size_line_exec, parse_response_at_close_exec, parse_response_exec,
};
use super::line::{
    LineExec, MAX_LINES, SectionExec, flush_pending_exec, parse_field_line_start_exec,
    parse_status_line_exec, range, read_line_exec, read_section_exec, sub,
};
use super::types::{HeadBuf, ParseBuf, ResponseBuf, StatusLineBuf};
use crate::field::string::{append, at, copy, run_len_exec, strip_trailing_ows_exec};
use crate::field::types::FieldLineBuf;

verus! {

/// The head that `read_head` gives once the status line was `status_line`
/// and the field section reads as `r`.
pub open spec fn head_from(status_line: StatusLine, r: SectionRead) -> HeadRead {
    match r {
        SectionRead::Done { fields, rest } => HeadRead::Done {
            head: Head { status_line: status_line, fields: fields },
            rest: rest,
        },
        SectionRead::Incomplete => HeadRead::Incomplete,
        SectionRead::Invalid => HeadRead::Invalid,
    }
}

/// One chunk, read whole from `s`, is read the same from `s + more`: the
/// decoding resumes after it with its data appended.
pub proof fn lemma_chunk_step(s: Seq<u8>, more: Seq<u8>, body: Seq<u8>, end: int, size: nat)
    requires
        0 <= end,
        end + 2 <= s.len(),
        read_line(s) == (LineRead::Line { line: s.take(end), rest: s.skip(end + 2) }),
        parse_chunk_size_line(s.take(end)) == Some(size),
        size > 0,
        body.len() + size <= max_body(),
        s.skip(end + 2).len() >= size + 2,
        crlf_at(s.skip(end + 2), size as int),
    ensures
        read_chunks(s + more, body) == read_chunks((s + more).skip(end + 2 + size + 2), body + s.skip(end + 2).take(size as int)),
{
    super::lemmas::lemma_read_line_append(s, more);
    let r = s.skip(end + 2);
    assert(crlf_at(r + more, size as int));
    assert((r + more).take(size as int) =~= r.take(size as int));
    assert((r + more).skip((size + 2) as int) =~= (s + more).skip(end + 2 + size + 2));
}

/// One field line `line` (not empty) applied to the finished lines `acc`
/// and the pending line `pending`, as [`read_section`] applies it: the new
/// `acc` and `pending`, or `None` where [`read_section`] is `Invalid`.
pub open spec fn section_step(line: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>) -> Option<(Seq<FieldLine>, Option<FieldLine>)> {
    if is_ows_octet(line[0]) {
        match pending {
            None => None,
            Some(raw) => Some((acc, Some(FieldLine {
                name: raw.name,
                value: strip_trailing_ows(raw.value) + seq![0x20u8] + strip_leading_ows(line),
            }))),
        }
    } else {
        match parse_field_line_start(line) {
            None => None,
            Some(raw) => match flush_pending(acc, pending) {
                Some(acc2) => Some((acc2, Some(raw))),
                None => None,
            },
        }
    }
}

/// A field line, read whole from `s`, is read the same from `s + more`
/// ([`section_step`] says how).
pub proof fn lemma_section_line(s: Seq<u8>, more: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat, end: int)
    requires
        0 <= end,
        end + 2 <= s.len(),
        read_line(s) == (LineRead::Line { line: s.take(end), rest: s.skip(end + 2) }),
    ensures
        end == 0 ==> read_section(s + more, acc, pending, count) == match flush_pending(acc, pending) {
            Some(fields) => SectionRead::Done { fields: fields, rest: (s + more).skip(end + 2) },
            None => SectionRead::Invalid,
        },
        end > 0 && count >= max_lines() ==> read_section(s + more, acc, pending, count) is Invalid,
        end > 0 && count < max_lines() ==> read_section(s + more, acc, pending, count) == match section_step(s.take(end), acc, pending) {
            Some((acc2, pending2)) => read_section((s + more).skip(end + 2), acc2, pending2, count + 1),
            None => SectionRead::Invalid,
        },
{
    super::lemmas::lemma_read_line_append(s, more);
    assert(s.skip(end + 2) + more =~= (s + more).skip(end + 2));
}

/// The result of [`field_line_exec`].
enum FieldStep {
    /// A field line was read; the section continues at `next`.
    Next { next: usize },
    /// The empty line ending the section was read; what follows is `next`.
    End { next: usize },
    /// More bytes are needed; nothing was changed.
    Incomplete,
    /// Not a field section.
    Invalid,
}

/// Reads one line of a field section from `s[pos..]`, with `acc`,
/// `pending` and `count` as [`read_section`]'s.
fn field_line_exec(s: &[u8], pos: usize, acc: &mut Vec<FieldLineBuf>, pending: &mut Option<FieldLineBuf>, count: &mut usize) -> (out: FieldStep)
    requires
        pos <= s.len(),
        *old(count) <= MAX_LINES,
    ensures
        *final(count) <= MAX_LINES,
        match out {
            FieldStep::Next { next } => pos < next <= s.len()
                && forall|more: Seq<u8>| #[trigger] read_section((s@ + more).skip(pos as int), crate::field::types::lines_view(old(acc)@), super::types::opt_line_view(*old(pending)), *old(count) as nat)
                    == read_section((s@ + more).skip(next as int), crate::field::types::lines_view(final(acc)@), super::types::opt_line_view(*final(pending)), *final(count) as nat),
            FieldStep::End { next } => pos < next <= s.len()
                && forall|more: Seq<u8>| #[trigger] read_section((s@ + more).skip(pos as int), crate::field::types::lines_view(old(acc)@), super::types::opt_line_view(*old(pending)), *old(count) as nat)
                    == (SectionRead::Done { fields: crate::field::types::lines_view(final(acc)@), rest: (s@ + more).skip(next as int) }),
            FieldStep::Incomplete => read_section(s@.skip(pos as int), crate::field::types::lines_view(old(acc)@), super::types::opt_line_view(*old(pending)), *old(count) as nat) is Incomplete
                && final(acc)@ == old(acc)@ && *final(pending) == *old(pending) && *final(count) == *old(count),
            FieldStep::Invalid => read_section(s@.skip(pos as int), crate::field::types::lines_view(old(acc)@), super::types::opt_line_view(*old(pending)), *old(count) as nat) is Invalid,
        },
{
    let ghost a0 = crate::field::types::lines_view(acc@);
    let ghost p0 = super::types::opt_line_view(*pending);
    let ghost c0 = *count as nat;
    let rest = sub(s, pos);
    proof {
        assert(s@ + Seq::<u8>::empty() =~= s@);
        assert(rest@ + Seq::<u8>::empty() =~= rest@);
        assert forall|more: Seq<u8>| #[trigger] (s@ + more).skip(pos as int) == rest@ + more by {
            assert((s@ + more).skip(pos as int) =~= rest@ + more);
        }
    }
    match read_line_exec(rest) {
        LineExec::Incomplete => FieldStep::Incomplete,
        LineExec::TooLong => FieldStep::Invalid,
        LineExec::Line { end } => {
            let line = range(rest, 0, end);
            assert(line@ =~= rest@.take(end as int));
            // Never saturates: pos + end + 2 <= s.len().
            let next = pos.saturating_add(end).saturating_add(2);
            proof {
                assert forall|more: Seq<u8>| #[trigger] (rest@ + more).skip(end + 2) == (s@ + more).skip(next as int) by {
                    assert((rest@ + more).skip(end + 2) =~= (s@ + more).skip(next as int));
                }
                lemma_section_line(rest@, Seq::<u8>::empty(), a0, p0, c0, end as int);
            }
            let mut p: Option<FieldLineBuf> = None;
            core::mem::swap(&mut p, pending);
            if end == 0 {
                let ok = flush_pending_exec(acc, p);
                if !ok {
                    return FieldStep::Invalid;
                }
                proof {
                    assert forall|more: Seq<u8>| #[trigger] read_section((s@ + more).skip(pos as int), a0, p0, c0)
                        == (SectionRead::Done { fields: crate::field::types::lines_view(acc@), rest: (s@ + more).skip(next as int) }) by {
                        lemma_section_line(rest@, more, a0, p0, c0, end as int);
                    }
                }
                return FieldStep::End { next };
            }
            if *count >= MAX_LINES {
                return FieldStep::Invalid;
            }
            let first = at(line, 0);
            if first == Some(0x20u8) || first == Some(0x09u8) {
                match p {
                    None => return FieldStep::Invalid,
                    Some(raw) => {
                        let mut value = strip_trailing_ows_exec(raw.value.as_slice());
                        value.push(0x20);
                        let k = run_len_exec(&crate::field::spec::Class::Ows, line);
                        append(&mut value, sub(line, k));
                        let ghost v = strip_trailing_ows(raw.value@) + seq![0x20u8] + strip_leading_ows(line@);
                        assert(value@ =~= v);
                        *pending = Some(FieldLineBuf { name: raw.name, value });
                    },
                }
            } else {
                match parse_field_line_start_exec(line) {
                    None => return FieldStep::Invalid,
                    Some(raw) => {
                        let ok = flush_pending_exec(acc, p);
                        if !ok {
                            return FieldStep::Invalid;
                        }
                        *pending = Some(raw);
                    },
                }
            }
            // Never saturates: count < MAX_LINES.
            *count = (*count).saturating_add(1);
            proof {
                assert(section_step(line@, a0, p0) == Some((crate::field::types::lines_view(acc@), super::types::opt_line_view(*pending))));
                assert forall|more: Seq<u8>| #[trigger] read_section((s@ + more).skip(pos as int), a0, p0, c0)
                    == read_section((s@ + more).skip(next as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(*pending), *count as nat) by {
                    lemma_section_line(rest@, more, a0, p0, c0, end as int);
                }
            }
            FieldStep::Next { next }
        },
    }
}

/// The result of [`chunk_exec`].
enum ChunkStep {
    /// A chunk was decoded; the next starts at `next`.
    Next { next: usize },
    /// The last chunk and the trailer section were read; what follows the
    /// message starts at `next`.
    End { next: usize },
    /// More bytes are needed; nothing was changed.
    Incomplete,
    /// Not a chunked body.
    Invalid,
}

/// Reads one chunk from `s[pos..]`, `body` being the content so far.
fn chunk_exec(s: &[u8], pos: usize, body: &mut Vec<u8>) -> (out: ChunkStep)
    requires
        pos <= s.len(),
        old(body).len() <= MAX_BODY,
    ensures
        final(body).len() <= MAX_BODY,
        match out {
            ChunkStep::Next { next } => pos < next <= s.len()
                && forall|more: Seq<u8>| #[trigger] read_chunks((s@ + more).skip(pos as int), old(body)@)
                    == read_chunks((s@ + more).skip(next as int), final(body)@),
            ChunkStep::End { next } => next <= s.len() && final(body)@ == old(body)@
                && read_chunks(s@.skip(pos as int), old(body)@) == (BodyRead::Done { body: old(body)@, rest: s@.skip(next as int) }),
            ChunkStep::Incomplete => final(body)@ == old(body)@ && read_chunks(s@.skip(pos as int), old(body)@) is Incomplete,
            ChunkStep::Invalid => read_chunks(s@.skip(pos as int), old(body)@) is Invalid,
        },
{
    let ghost before = body@;
    let rest = sub(s, pos);
    match read_line_exec(rest) {
        LineExec::Incomplete => ChunkStep::Incomplete,
        LineExec::TooLong => ChunkStep::Invalid,
        LineExec::Line { end } => {
            let line = range(rest, 0, end);
            assert(line@ =~= rest@.take(end as int));
            // Never saturates: end + 2 <= rest.len().
            let data = sub(rest, end.saturating_add(2));
            match parse_chunk_size_line_exec(line) {
                ChunkSize::Invalid => ChunkStep::Invalid,
                ChunkSize::TooBig => ChunkStep::Invalid,
                ChunkSize::Size(size) => {
                    if size == 0 {
                        return match read_section_exec(data) {
                            SectionExec::Done { fields: _, next } => {
                                // Never saturates: this is a position in s.
                                let after = pos.saturating_add(end).saturating_add(2).saturating_add(next);
                                assert(data@.skip(next as int) =~= s@.skip(after as int));
                                ChunkStep::End { next: after }
                            },
                            SectionExec::Incomplete => ChunkStep::Incomplete,
                            SectionExec::Invalid => ChunkStep::Invalid,
                        };
                    }
                    // Never saturates: both are at most MAX_BODY.
                    if (body.len() as u64).saturating_add(size) > MAX_BODY {
                        return ChunkStep::Invalid;
                    }
                    let size = size as usize;
                    // Never saturates: size <= MAX_BODY.
                    if data.len() < size.saturating_add(2) {
                        return ChunkStep::Incomplete;
                    }
                    if !crlf_at_exec(data, size) {
                        return ChunkStep::Invalid;
                    }
                    append(body, range(data, 0, size));
                    assert(body@ =~= before + data@.take(size as int));
                    // Never saturates: this is a position in s.
                    let next = pos.saturating_add(end).saturating_add(2).saturating_add(size).saturating_add(2);
                    proof {
                        assert(rest@.take(end as int) =~= line@);
                        assert(rest@.skip(end + 2) =~= data@);
                        lemma_chunk_next(s@, pos as int, end as int, size as nat, before);
                    }
                    ChunkStep::Next { next }
                },
            }
        },
    }
}

/// [`lemma_chunk_step`] at position `pos` of `s`, for every continuation.
pub proof fn lemma_chunk_next(s: Seq<u8>, pos: int, end: int, size: nat, body: Seq<u8>)
    requires
        0 <= pos <= s.len(),
        0 <= end,
        end + 2 <= s.skip(pos).len(),
        read_line(s.skip(pos)) == (LineRead::Line { line: s.skip(pos).take(end), rest: s.skip(pos).skip(end + 2) }),
        parse_chunk_size_line(s.skip(pos).take(end)) == Some(size),
        size > 0,
        body.len() + size <= max_body(),
        s.skip(pos).skip(end + 2).len() >= size + 2,
        crlf_at(s.skip(pos).skip(end + 2), size as int),
    ensures
        forall|more: Seq<u8>| #[trigger] read_chunks((s + more).skip(pos), body)
            == read_chunks((s + more).skip(pos + end + 2 + size + 2), body + s.skip(pos).skip(end + 2).take(size as int)),
{
    let t = s.skip(pos);
    assert forall|more: Seq<u8>| #[trigger] read_chunks((s + more).skip(pos), body)
        == read_chunks((s + more).skip(pos + end + 2 + size + 2), body + t.skip(end + 2).take(size as int)) by {
        lemma_chunk_step(t, more, body, end, size);
        assert((s + more).skip(pos) =~= t + more);
        assert((t + more).skip(end + 2 + size + 2) =~= (s + more).skip(pos + end + 2 + size + 2));
    }
}

/// Where the parser is.
enum Stage {
    /// Nothing read yet.
    StatusLine,
    /// The status line is read; the field section is read up to `pos`.
    Fields {
        status_line: StatusLineBuf,
        pos: usize,
        acc: Vec<FieldLineBuf>,
        pending: Option<FieldLineBuf>,
        count: usize,
    },
    /// The head is read and the body starts at `start`; for a chunked body,
    /// the chunks before `pos` are decoded into `body`.
    Body {
        head: HeadBuf,
        start: usize,
        length: BodyLengthExec,
        pos: usize,
        body: Vec<u8>,
    },
    /// An answer other than `Incomplete` was given; nothing is kept.
    Spent,
}

/// A response parser, given the bytes of one connection as they arrive.
/// Its view is everything it has been given and whether the request was
/// `HEAD`; each answer is [`parse_response`]'s for all of it
/// ([`super::contract::feed_ensures`]).
pub struct ResponseParser {
    buf: Vec<u8>,
    request_is_head: bool,
    stage: Stage,
}

impl ResponseParser {
    /// Everything received so far.
    pub closed spec fn received(&self) -> Seq<u8> {
        self.buf@
    }

    /// Whether the request was `HEAD`.
    pub closed spec fn head(&self) -> bool {
        self.request_is_head
    }

    /// The saved state is what parsing everything received would reach,
    /// for every continuation `more` of the bytes received.
    pub closed spec fn wf(&self) -> bool {
        let b = self.buf@;
        match self.stage {
            Stage::StatusLine => true,
            Stage::Spent => true,
            Stage::Fields { status_line, pos, acc, pending, count } => pos <= b.len() && count <= MAX_LINES
                && forall|more: Seq<u8>| #[trigger] read_head(b + more) == head_from(status_line@,
                    read_section((b + more).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(pending), count as nat)),
            Stage::Body { head, start, length, pos, body } => start <= pos <= b.len() && body.len() <= MAX_BODY
                && super::body::body_length_view(length) == body_length(head@, self.request_is_head)
                && (match length {
                    BodyLengthExec::Length(n) => n <= MAX_BODY,
                    _ => true,
                })
                && (forall|more: Seq<u8>| #[trigger] read_head(b + more) == (HeadRead::Done { head: head@, rest: (b + more).skip(start as int) }))
                && (forall|more: Seq<u8>| #[trigger] read_chunks((b + more).skip(start as int), seq![])
                    == read_chunks((b + more).skip(pos as int), body@)),
        }
    }

    /// A parser for the response to a request that was `HEAD` exactly when
    /// `request_is_head`.
    pub fn new(request_is_head: bool) -> (p: Self)
        ensures
            super::contract::new_ensures(request_is_head, p.received(), p.head()),
            p.wf(),
    {
        let p = ResponseParser { buf: Vec::new(), request_is_head, stage: Stage::StatusLine };
        assert(p.buf@ =~= Seq::<u8>::empty());
        p
    }

    /// The next bytes from the connection. The contract's precondition
    /// (`feed_requires`: nothing decided yet) is not required: the answer
    /// is the spec's for everything received in any case.
    pub fn feed(&mut self, bytes: &[u8]) -> (out: ParseBuf)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).head() == old(self).head(),
            super::contract::feed_ensures(old(self).received(), bytes@, final(self).received(), final(self).head(), out@),
    {
        let ghost b0 = self.buf@;
        append(&mut self.buf, bytes);
        proof {
            let b = self.buf@;
            assert forall|more: Seq<u8>| #[trigger] (b + more) == b0 + (bytes@ + more) by {
                assert(b + more =~= b0 + (bytes@ + more));
            }
            match &self.stage {
                Stage::Fields { status_line, pos, acc, pending, count } => {
                    let (pos, count) = (*pos, *count);
                    assert forall|more: Seq<u8>| #[trigger] read_head(b + more) == head_from(status_line@,
                        read_section((b + more).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(*pending), count as nat)) by {
                        assert(read_head(b0 + (bytes@ + more)) == head_from(status_line@,
                            read_section((b0 + (bytes@ + more)).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(*pending), count as nat)));
                    }
                },
                Stage::Body { head, start, length: _, pos, body } => {
                    let (start, pos) = (*start, *pos);
                    assert forall|more: Seq<u8>| #[trigger] read_head(b + more) == (HeadRead::Done { head: head@, rest: (b + more).skip(start as int) }) by {
                        assert(read_head(b0 + (bytes@ + more)) == (HeadRead::Done { head: head@, rest: (b0 + (bytes@ + more)).skip(start as int) }));
                    }
                    assert forall|more: Seq<u8>| #[trigger] read_chunks((b + more).skip(start as int), seq![])
                        == read_chunks((b + more).skip(pos as int), body@) by {
                        assert(read_chunks((b0 + (bytes@ + more)).skip(start as int), seq![])
                            == read_chunks((b0 + (bytes@ + more)).skip(pos as int), body@));
                    }
                },
                _ => {},
            }
        }
        if let Some(out) = self.status_step() {
            return out;
        }
        if let Some(out) = self.fields_run() {
            return out;
        }
        self.body_run()
    }

    /// Everything received so far
    /// ([`super::contract::received_bytes_ensures`]).
    pub fn received_bytes(&self) -> (out: &[u8])
        ensures
            super::contract::received_bytes_ensures(self.received(), out@),
    {
        self.buf.as_slice()
    }

    /// The server closed the connection.
    pub fn close(self) -> (out: ParseBuf)
        requires
            self.wf(),
        ensures
            super::contract::close_ensures(self.received(), self.head(), out@),
    {
        parse_response_at_close_exec(self.buf.as_slice(), self.request_is_head)
    }

    /// Reads the status line, if that is where the parser is.
    fn status_step(&mut self) -> (out: Option<ParseBuf>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).buf@ == old(self).buf@,
            final(self).request_is_head == old(self).request_is_head,
            match out {
                Some(o) => o@ == parse_response(old(self).buf@, old(self).request_is_head),
                None => !(final(self).stage is StatusLine),
            },
    {
        match &self.stage {
            Stage::StatusLine => {},
            _ => return None,
        }
        let ghost b = self.buf@;
        let s = self.buf.as_slice();
        match read_line_exec(s) {
            LineExec::Incomplete => Some(ParseBuf::Incomplete),
            LineExec::TooLong => Some(ParseBuf::Invalid),
            LineExec::Line { end } => {
                let line = range(s, 0, end);
                assert(line@ =~= b.take(end as int));
                match parse_status_line_exec(line) {
                    None => Some(ParseBuf::Invalid),
                    Some(status_line) => {
                        // Never saturates: end + 2 <= s.len().
                        let pos = end.saturating_add(2);
                        proof {
                            assert forall|more: Seq<u8>| #[trigger] read_head(b + more) == head_from(status_line@,
                                read_section((b + more).skip(pos as int), Seq::<FieldLine>::empty(), None, 0)) by {
                                super::lemmas::lemma_read_line_append(b, more);
                                assert(b.skip(pos as int) + more =~= (b + more).skip(pos as int));
                            }
                        }
                        let acc: Vec<FieldLineBuf> = Vec::new();
                        assert(crate::field::types::lines_view(acc@) =~= Seq::<FieldLine>::empty());
                        self.stage = Stage::Fields { status_line, pos, acc, pending: None, count: 0 };
                        None
                    },
                }
            },
        }
    }

    /// Reads field lines, if that is where the parser is, until the
    /// section ends or more bytes are needed.
    fn fields_run(&mut self) -> (out: Option<ParseBuf>)
        requires
            old(self).wf(),
            !(old(self).stage is StatusLine),
        ensures
            final(self).wf(),
            final(self).buf@ == old(self).buf@,
            final(self).request_is_head == old(self).request_is_head,
            match out {
                Some(o) => o@ == parse_response(old(self).buf@, old(self).request_is_head),
                None => !(final(self).stage is StatusLine) && !(final(self).stage is Fields),
            },
    {
        match &self.stage {
            Stage::Fields { .. } => {},
            _ => return None,
        }
        let ghost b = self.buf@;
        let ghost h = self.request_is_head;
        let mut stage = Stage::Spent;
        core::mem::swap(&mut stage, &mut self.stage);
        let (status_line, mut pos, mut acc, mut pending, mut count) = match stage {
            Stage::Fields { status_line, pos, acc, pending, count } => (status_line, pos, acc, pending, count),
            _ => return None,
        };
        proof {
            assert(b + Seq::<u8>::empty() =~= b);
        }
        loop
            invariant
                self.stage is Spent,
                self.buf@ == b,
                self.request_is_head == h,
                pos <= b.len(),
                count <= MAX_LINES,
                forall|more: Seq<u8>| #[trigger] read_head(b + more) == head_from(status_line@,
                    read_section((b + more).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(pending), count as nat)),
            decreases b.len() - pos,
        {
            let ghost p0 = pos;
            let ghost acc0 = crate::field::types::lines_view(acc@);
            let ghost pend0 = super::types::opt_line_view(pending);
            let ghost c0 = count as nat;
            proof {
                assert(b + Seq::<u8>::empty() =~= b);
                assert(read_head(b + Seq::<u8>::empty()) == head_from(status_line@,
                    read_section(b.skip(p0 as int), acc0, pend0, c0)));
            }
            match field_line_exec(self.buf.as_slice(), pos, &mut acc, &mut pending, &mut count) {
                FieldStep::Incomplete => {
                    self.stage = Stage::Fields { status_line, pos, acc, pending, count };
                    return Some(ParseBuf::Incomplete);
                },
                FieldStep::Invalid => return Some(ParseBuf::Invalid),
                FieldStep::End { next } => {
                    let head = HeadBuf { status_line, fields: acc };
                    let length = body_length_exec(&head, self.request_is_head);
                    proof {
                        assert forall|more: Seq<u8>| #[trigger] read_head(b + more) == (HeadRead::Done { head: head@, rest: (b + more).skip(next as int) }) by {
                            assert(read_section((b + more).skip(p0 as int), acc0, pend0, c0)
                                == (SectionRead::Done { fields: head@.fields, rest: (b + more).skip(next as int) }));
                        }
                    }
                    let body: Vec<u8> = Vec::new();
                    assert(body@ =~= Seq::<u8>::empty());
                    self.stage = Stage::Body { head, start: next, length, pos: next, body };
                    return None;
                },
                FieldStep::Next { next } => {
                    pos = next;
                    proof {
                        assert forall|more: Seq<u8>| #[trigger] read_head(b + more) == head_from(status_line@,
                            read_section((b + more).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(pending), count as nat)) by {
                            assert(read_section((b + more).skip(p0 as int), acc0, pend0, c0)
                                == read_section((b + more).skip(pos as int), crate::field::types::lines_view(acc@), super::types::opt_line_view(pending), count as nat));
                        }
                    }
                },
            }
        }
    }

    /// Reads the body, once the head is read.
    fn body_run(&mut self) -> (out: ParseBuf)
        requires
            old(self).wf(),
            !(old(self).stage is StatusLine),
            !(old(self).stage is Fields),
        ensures
            final(self).wf(),
            final(self).buf@ == old(self).buf@,
            final(self).request_is_head == old(self).request_is_head,
            out@ == parse_response(old(self).buf@, old(self).request_is_head),
    {
        let ghost b = self.buf@;
        let ghost h = self.request_is_head;
        let mut stage = Stage::Spent;
        core::mem::swap(&mut stage, &mut self.stage);
        let (head, start, length, pos, body) = match stage {
            Stage::Body { head, start, length, pos, body } => (head, start, length, pos, body),
            _ => return parse_response_exec(self.buf.as_slice(), self.request_is_head),
        };
        proof {
            assert(b + Seq::<u8>::empty() =~= b);
            assert(read_head(b + Seq::<u8>::empty()) == (HeadRead::Done { head: head@, rest: (b + Seq::<u8>::empty()).skip(start as int) }));
            assert(read_chunks((b + Seq::<u8>::empty()).skip(start as int), seq![])
                == read_chunks((b + Seq::<u8>::empty()).skip(pos as int), body@));
        }
        let s = self.buf.as_slice();
        match length {
            BodyLengthExec::NoBody => {
                let r = ResponseBuf { status_line: head.status_line, fields: head.fields, body: Vec::new() };
                assert(r.body@ =~= Seq::<u8>::empty());
                ParseBuf::Done { response: r, rest: copy(sub(s, start)) }
            },
            BodyLengthExec::Length(n) => {
                let n = n as usize;
                // Never saturates: start <= s.len().
                if s.len().saturating_sub(start) >= n {
                    // Never saturates: start + n <= s.len().
                    let end = start.saturating_add(n);
                    let content = copy(range(s, start, end));
                    assert(content@ =~= b.skip(start as int).take(n as int));
                    let after = copy(sub(s, end));
                    assert(after@ =~= b.skip(start as int).skip(n as int));
                    ParseBuf::Done {
                        response: ResponseBuf { status_line: head.status_line, fields: head.fields, body: content },
                        rest: after,
                    }
                } else {
                    self.stage = Stage::Body { head, start, length: BodyLengthExec::Length(n as u64), pos, body };
                    ParseBuf::Incomplete
                }
            },
            BodyLengthExec::Close => {
                // Never saturates: start <= s.len().
                let big = s.len().saturating_sub(start) as u64 > MAX_BODY;
                self.stage = Stage::Body { head, start, length: BodyLengthExec::Close, pos, body };
                if big {
                    ParseBuf::Invalid
                } else {
                    ParseBuf::Incomplete
                }
            },
            BodyLengthExec::Invalid => ParseBuf::Invalid,
            BodyLengthExec::Unsupported => ParseBuf::Unsupported,
            BodyLengthExec::Chunked => self.chunks_run(head, start, pos, body),
        }
    }

    /// Decodes chunks from `pos`, the head being `head` and the body
    /// starting at `start`.
    fn chunks_run(&mut self, head: HeadBuf, start: usize, pos: usize, body: Vec<u8>) -> (out: ParseBuf)
        requires
            old(self).stage is Spent,
            start <= pos <= old(self).buf@.len(),
            body.len() <= MAX_BODY,
            body_length(head@, old(self).request_is_head) == BodyLength::Chunked,
            forall|more: Seq<u8>| #[trigger] read_head(old(self).buf@ + more) == (HeadRead::Done { head: head@, rest: (old(self).buf@ + more).skip(start as int) }),
            forall|more: Seq<u8>| #[trigger] read_chunks((old(self).buf@ + more).skip(start as int), seq![])
                == read_chunks((old(self).buf@ + more).skip(pos as int), body@),
        ensures
            final(self).wf(),
            final(self).buf@ == old(self).buf@,
            final(self).request_is_head == old(self).request_is_head,
            out@ == parse_response(old(self).buf@, old(self).request_is_head),
    {
        let ghost b = self.buf@;
        let ghost h = self.request_is_head;
        let mut pos = pos;
        let mut body = body;
        proof {
            assert(b + Seq::<u8>::empty() =~= b);
            assert(read_head(b + Seq::<u8>::empty()) == (HeadRead::Done { head: head@, rest: (b + Seq::<u8>::empty()).skip(start as int) }));
        }
        loop
            invariant
                self.stage is Spent,
                self.buf@ == b,
                self.request_is_head == h,
                start <= pos <= b.len(),
                body.len() <= MAX_BODY,
                body_length(head@, h) == BodyLength::Chunked,
                read_head(b) == (HeadRead::Done { head: head@, rest: b.skip(start as int) }),
                forall|more: Seq<u8>| #[trigger] read_head(b + more) == (HeadRead::Done { head: head@, rest: (b + more).skip(start as int) }),
                forall|more: Seq<u8>| #[trigger] read_chunks((b + more).skip(start as int), seq![])
                    == read_chunks((b + more).skip(pos as int), body@),
            decreases b.len() - pos,
        {
            let ghost p0 = pos;
            let ghost body0 = body@;
            proof {
                assert(b + Seq::<u8>::empty() =~= b);
                assert(read_chunks((b + Seq::<u8>::empty()).skip(start as int), seq![])
                    == read_chunks((b + Seq::<u8>::empty()).skip(pos as int), body@));
            }
            match chunk_exec(self.buf.as_slice(), pos, &mut body) {
                ChunkStep::Incomplete => {
                    self.stage = Stage::Body { head, start, length: BodyLengthExec::Chunked, pos, body };
                    return ParseBuf::Incomplete;
                },
                ChunkStep::Invalid => return ParseBuf::Invalid,
                ChunkStep::End { next } => {
                    let r = ResponseBuf { status_line: head.status_line, fields: head.fields, body };
                    return ParseBuf::Done { response: r, rest: copy(sub(self.buf.as_slice(), next)) };
                },
                ChunkStep::Next { next } => {
                    pos = next;
                    proof {
                        assert forall|more: Seq<u8>| #[trigger] read_chunks((b + more).skip(start as int), seq![])
                            == read_chunks((b + more).skip(pos as int), body@) by {
                            assert(read_chunks((b + more).skip(start as int), seq![])
                                == read_chunks((b + more).skip(p0 as int), body0));
                        }
                    }
                },
            }
        }
    }
}

} // verus!
