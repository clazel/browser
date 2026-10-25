//! Facts proven about the message spec. They are evidence that the
//! transcription is right (docs/SPEC-STYLE.md), and the two properties
//! [`super::contract`] states for an incremental parser:
//!
//! - [`theorem_monotone`]: more bytes never take back a decision, and a
//!   finished response stays the same response with the extra bytes after
//!   it ([`super::contract::monotone`]).
//! - [`theorem_no_early_decision`]: every proper prefix of the octets a
//!   response was parsed from is `Incomplete`
//!   ([`super::contract::no_early_decision`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Appending bytes: each reader keeps its decision.
// ===========================================================================

/// A CRLF found in `s` is found at the same place in `s + more`; one found
/// only in `s + more` starts at the last octet of `s` or after.
pub proof fn lemma_find_crlf_append(s: Seq<u8>, more: Seq<u8>, i: nat)
    ensures
        match find_crlf_from(s, i) {
            Some(j) => find_crlf_from(s + more, i) == Some(j),
            None => match find_crlf_from(s + more, i) {
                Some(j) => j + 1 >= s.len(),
                None => true,
            },
        },
    decreases s.len() - i
{
    super::termination::lemma_find_crlf_from(s + more, i);
    if i + 1 < s.len() {
        assert(crlf_at(s, i as int) == crlf_at(s + more, i as int));
        if !crlf_at(s, i as int) {
            lemma_find_crlf_append(s, more, i + 1);
        }
    }
}

/// [`read_line`] on `s + more` keeps the line read from `s`, and its
/// verdict that the line is too long.
pub proof fn lemma_read_line_append(s: Seq<u8>, more: Seq<u8>)
    ensures
        match read_line(s) {
            LineRead::Line { line, rest } => read_line(s + more) == (LineRead::Line { line: line, rest: rest + more }),
            LineRead::TooLong => read_line(s + more) is TooLong,
            LineRead::Incomplete => true,
        },
{
    lemma_find_crlf_append(s, more, 0);
    super::termination::lemma_find_crlf_from(s, 0);
    if let Some(i) = find_crlf_from(s, 0) {
        if i <= max_line() {
            assert((s + more).take(i as int) =~= s.take(i as int));
            assert((s + more).skip((i + 2) as int) =~= s.skip((i + 2) as int) + more);
        }
    }
}

/// [`read_section`] on `s + more` keeps a finished section (with `more`
/// after it) and an invalid one.
pub proof fn lemma_read_section_append(s: Seq<u8>, more: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat)
    ensures
        match read_section(s, acc, pending, count) {
            SectionRead::Done { fields, rest } => read_section(s + more, acc, pending, count)
                == (SectionRead::Done { fields: fields, rest: rest + more }),
            SectionRead::Invalid => read_section(s + more, acc, pending, count) is Invalid,
            SectionRead::Incomplete => true,
        },
    decreases s.len()
{
    lemma_read_line_append(s, more);
    super::termination::lemma_read_line_rest(s);
    if let LineRead::Line { line, rest } = read_line(s) {
        if line.len() == 0 {
        } else if count >= max_lines() {
        } else if is_ows_octet(line[0]) {
            if let Some(raw) = pending {
                lemma_read_section_append(rest, more, acc, Some(FieldLine {
                    name: raw.name,
                    value: strip_trailing_ows(raw.value) + seq![0x20u8] + strip_leading_ows(line),
                }), count + 1);
            }
        } else {
            if let Some(raw) = parse_field_line_start(line) {
                if let Some(acc2) = flush_pending(acc, pending) {
                    lemma_read_section_append(rest, more, acc2, Some(raw), count + 1);
                }
            }
        }
    }
}

/// [`read_head`] on `s + more` keeps a finished head and an invalid one.
pub proof fn lemma_read_head_append(s: Seq<u8>, more: Seq<u8>)
    ensures
        match read_head(s) {
            HeadRead::Done { head, rest } => read_head(s + more) == (HeadRead::Done { head: head, rest: rest + more }),
            HeadRead::Invalid => read_head(s + more) is Invalid,
            HeadRead::Incomplete => true,
        },
{
    lemma_read_line_append(s, more);
    if let LineRead::Line { line, rest } = read_line(s) {
        lemma_read_section_append(rest, more, seq![], None, 0);
    }
}

/// [`read_chunks`] on `s + more` keeps a finished body (with `more` after
/// it) and an invalid one.
pub proof fn lemma_read_chunks_append(s: Seq<u8>, more: Seq<u8>, body: Seq<u8>)
    ensures
        match read_chunks(s, body) {
            BodyRead::Done { body: b, rest } => read_chunks(s + more, body) == (BodyRead::Done { body: b, rest: rest + more }),
            BodyRead::Invalid => read_chunks(s + more, body) is Invalid,
            BodyRead::Incomplete => true,
        },
    decreases s.len()
{
    lemma_read_line_append(s, more);
    super::termination::lemma_read_line_rest(s);
    if let LineRead::Line { line, rest } = read_line(s) {
        if let Some(size) = parse_chunk_size_line(line) {
            if size == 0 {
                lemma_read_section_append(rest, more, seq![], None, 0);
            } else if body.len() + size > max_body() {
            } else if rest.len() < size + 2 {
            } else {
                assert(crlf_at(rest, size as int) == crlf_at(rest + more, size as int));
                if crlf_at(rest, size as int) {
                    assert((rest + more).take(size as int) =~= rest.take(size as int));
                    assert((rest + more).skip((size + 2) as int) =~= rest.skip((size + 2) as int) + more);
                    lemma_read_chunks_append(rest.skip((size + 2) as int), more, body + rest.take(size as int));
                }
            }
        }
    }
}

/// [`parse_response`] on `input + more` keeps every decision made on
/// `input`; a finished response is the same, with `more` after it.
pub proof fn lemma_parse_response_append(input: Seq<u8>, more: Seq<u8>, request_is_head: bool)
    ensures
        match parse_response(input, request_is_head) {
            Parse::Done { response, rest } => parse_response(input + more, request_is_head)
                == (Parse::Done { response: response, rest: rest + more }),
            Parse::Invalid => parse_response(input + more, request_is_head) is Invalid,
            Parse::Unsupported => parse_response(input + more, request_is_head) is Unsupported,
            Parse::Incomplete => true,
        },
{
    lemma_read_head_append(input, more);
    if let HeadRead::Done { head, rest } = read_head(input) {
        match body_length(head, request_is_head) {
            BodyLength::Length(n) => {
                if rest.len() >= n {
                    assert((rest + more).take(n as int) =~= rest.take(n as int));
                    assert((rest + more).skip(n as int) =~= rest.skip(n as int) + more);
                }
            },
            BodyLength::Chunked => {
                lemma_read_chunks_append(rest, more, seq![]);
            },
            _ => {},
        }
    }
}

// ===========================================================================
// The theorems of `contract.rs`.
// ===========================================================================

/// Monotonicity of [`parse_response`] (`super::contract::monotone`).
pub proof fn theorem_monotone(input: Seq<u8>, more: Seq<u8>, request_is_head: bool)
    ensures
        super::contract::monotone(input, more, request_is_head),
{
    lemma_parse_response_append(input, more, request_is_head);
    if let Parse::Done { response, rest } = parse_response(input, request_is_head) {
        assert((rest + more).take(rest.len() as int) =~= rest);
    }
}

/// No decision before the data (`super::contract::no_early_decision`):
/// a prefix that decided anything would, by monotonicity, decide the same
/// for the whole input, which ends the response no earlier than the prefix.
pub proof fn theorem_no_early_decision(input: Seq<u8>, request_is_head: bool)
    ensures
        super::contract::no_early_decision(input, request_is_head),
{
    if let Parse::Done { response, rest } = parse_response(input, request_is_head) {
        assert forall|k: int| 0 <= k < input.len() - rest.len()
            implies parse_response(#[trigger] input.take(k), request_is_head) is Incomplete by {
            let t = input.take(k);
            let u = input.skip(k);
            assert(t + u =~= input);
            lemma_parse_response_append(t, u, request_is_head);
            if let Parse::Done { response: r1, rest: rest1 } = parse_response(t, request_is_head) {
                assert(rest == rest1 + u);
                assert(rest.len() == rest1.len() + u.len());
            }
        }
    }
}

} // verus!
