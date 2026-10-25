//! The request parser, RFC 9112 §3 and §2.1, as a spec only: it exists for
//! [`theorem_request_round_trip`], that what [`serialize_request`] writes
//! parses back as the same request. The browser never parses requests.
//!
//! Modelling choices, beyond those of [`super::spec`] (whose line and
//! field-section readers, and limits, this uses):
//! - The version must be exactly `HTTP/1.1`, the only one the serializer
//!   writes; a [`Request`] has no version to carry another.
//! - `request-target` (§3.2) is read as the run of `VCHAR` octets after
//!   the method's SP: §3 "No whitespace is allowed in the three
//!   components", and the forms of §3.2 are all made of `VCHAR`s.
//! - The empty lines §2.2 lets a server ignore before a request-line are
//!   not ignored (the serializer writes none).
//! - Only the head is parsed: the requests the serializer writes have no
//!   body, so §6.3 step 7 is not modelled; what follows the empty line is
//!   returned as the rest.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of the longest prefix of `s` made of `VCHAR`s.
pub open spec fn vchar_run_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && is_vchar(s[0]) {
        1 + vchar_run_len(s.drop_first())
    } else {
        0
    }
}

/// §3: `request-line = method SP request-target SP HTTP-version`, over
/// the whole of `line`, with `method = token` (§3.1) and `HTTP-version`
/// `HTTP/1.1` (see the modelling choices): the method and the target.
pub open spec fn parse_request_line(line: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    // method = token
    let n = run_len(Class::Tchar, line);
    if n > 0 && line.len() > n && line[n as int] == 0x20 {
        // SP request-target
        let after = line.skip((n + 1) as int);
        let m = vchar_run_len(after);
        // SP HTTP-version
        if m > 0 && after.len() == m + 1 + 8 && after[m as int] == 0x20
            && after.skip((m + 1) as int) == lit_http_1_1()
        {
            Some((line.take(n as int), after.take(m as int)))
        } else {
            None
        }
    } else {
        None
    }
}

/// The result of parsing a request.
pub enum RequestParse {
    /// The request, and what follows its head.
    Done {
        /// the request
        request: Request,
        /// what follows the empty line ending its head
        rest: Seq<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a request this parser reads.
    Invalid,
}

/// §2.1 `HTTP-message = start-line CRLF *( field-line CRLF ) CRLF`, with
/// `start-line = request-line`, at the start of `input`.
pub open spec fn parse_request(input: Seq<u8>) -> RequestParse {
    match read_line(input) {
        LineRead::Incomplete => RequestParse::Incomplete,
        LineRead::TooLong => RequestParse::Invalid,
        LineRead::Line { line, rest } => match parse_request_line(line) {
            None => RequestParse::Invalid,
            Some((method, target)) => match read_section(rest, seq![], None, 0) {
                SectionRead::Done { fields, rest: after } => RequestParse::Done {
                    request: Request { method: method, target: target, fields: fields },
                    rest: after,
                },
                SectionRead::Incomplete => RequestParse::Incomplete,
                SectionRead::Invalid => RequestParse::Invalid,
            },
        },
    }
}

/// Every field line of `fields`, written `name: value`, fits in
/// [`max_line`].
pub open spec fn field_lines_fit(fields: Seq<FieldLine>) -> bool
    decreases fields.len()
{
    fields.len() == 0 || (fields[0].name.len() + 2 + fields[0].value.len() <= max_line()
        && field_lines_fit(fields.drop_first()))
}

/// `r`, serialized, is within the parser's limits: its request line and
/// every field line fit in [`max_line`], and it has at most [`max_lines`]
/// field lines.
pub open spec fn within_limits(r: Request) -> bool {
    r.method.len() + 1 + r.target.len() + 1 + 8 <= max_line()
        && r.fields.len() <= max_lines()
        && field_lines_fit(r.fields)
}

/// Round trip: a valid request within the limits, serialized, parses back
/// as the same request, whatever follows it.
pub proof fn theorem_request_round_trip(r: Request, more: Seq<u8>)
    requires
        is_valid_request(r),
        within_limits(r),
    ensures
        parse_request(serialize_request(r) + more) == (RequestParse::Done { request: r, rest: more }),
{
}

} // verus!
