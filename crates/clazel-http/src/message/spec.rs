//! Executable-style specification of HTTP/1.1 message framing, as a client
//! sees it, transcribed from RFC 9112 "HTTP/1.1". Nothing here runs; it
//! defines what "correct" means. Every definition cites its section and
//! quotes the grammar or step it transcribes; each `// N.` comment is a
//! step of §6.3.
//!
//! Source (pinned; an RFC never changes after publication): RFC 9112, June
//! 2022, <https://www.rfc-editor.org/rfc/rfc9112>:
//! - §2.1 message format; §2.2 message parsing (line terminators, bare CR,
//!   whitespace after the start-line); §2.3 `HTTP-version`;
//! - §3 the request line, for the serializer only;
//! - §4 the status line; §5 field lines; §5.1 no whitespace before the
//!   colon; §5.2 obsolete line folding;
//! - §6.1 `Transfer-Encoding`; §6.2 `Content-Length`; §6.3 message body
//!   length, steps 1 to 8, as a client;
//! - §7.1 chunked transfer coding, §7.1.1 chunk extensions, §7.1.2 the
//!   trailer section, §7.1.3 decoding chunked.
//!
//! Field syntax (names, values, OWS, tokens, lists, `Content-Length` and
//! `Transfer-Encoding` values) is RFC 9110's, from [`crate::field::spec`].
//!
//! Modelling choices (each a deliberate deviation in form, never in
//! meaning, or a choice the RFC leaves to the recipient):
//! - The received bytes are one `Seq<u8>`, everything the connection has
//!   delivered so far. [`parse_response`] maps them to `Incomplete` (more
//!   bytes are needed before anything is decided), `Invalid`,
//!   `Unsupported`, or the response plus the bytes after it.
//!   [`parse_response_at_close`] is the same once the server has closed
//!   the connection, which is when a close-delimited body (§6.3 step 8)
//!   ends and when an `Incomplete` message becomes an error (step 6:
//!   "the recipient MUST consider the message to be incomplete").
//! - Lines end only at CRLF. §2.2 lets a recipient "recognize a single LF
//!   as a line terminator"; we do not, so a bare LF is an octet inside a
//!   line, and no grammar below accepts one.
//! - A bare CR (§2.2: "a CR character not immediately followed by LF")
//!   makes its element invalid, the first of the two options §2.2 gives;
//!   no grammar below accepts a CR either.
//! - A whitespace-preceded line straight after the status line (§2.2) is
//!   rejected, the first of the two options §2.2 gives ("reject the
//!   message as invalid or consume each whitespace-preceded line").
//! - Whitespace between a field name and the colon (§5.1) is rejected:
//!   the field-line grammar has none, and §5.1 gives a user agent no other
//!   instruction.
//! - An obs-fold (§5.2: `obs-fold = OWS CRLF RWS`) is replaced by a single
//!   SP, as "A user agent ... MUST replace each received obs-fold with one
//!   or more SP octets" allows: the trailing OWS of the line before, the
//!   CRLF and the leading RWS of the continuation line become one SP. The
//!   field value is then checked against RFC 9110 §5.5.
//! - A field value that does not match RFC 9110 §5.5 (a NUL, CR, LF or
//!   other control in it) makes the message invalid, the first of the
//!   options RFC 9110 §5.5 gives.
//! - A status line may end right after its status code (`HTTP/1.1 301`),
//!   without the SP the grammar requires there. §4: "A server MUST send the
//!   space that separates the status-code from the reason-phrase even when
//!   the reason-phrase is absent", but servers that omit it are common and
//!   every major client accepts them, and §4 lets a recipient "parse on
//!   whitespace-delimited word boundaries". We take only that omission:
//!   every other separator is still exactly one SP.
//! - Only HTTP/1.x responses are parsed: the major version digit must be
//!   `1` (§2.3 allows any `DIGIT "." DIGIT`). This parser frames HTTP/1.1
//!   messages to a request sent as HTTP/1.1; a response claiming another
//!   major version is not one it can frame by these rules, so it is
//!   `Invalid` rather than read to close.
//! - An empty line before the status line is rejected. §2.2 asks a server
//!   to ignore one before a request-line; nothing allows it before a
//!   status-line, and a client sends one request per connection, so there
//!   is no earlier response for it to follow.
//! - A request is never `CONNECT` (§6.3 step 2 is omitted) and never
//!   expects a response to be anything but HTTP/1.x; whether it was `HEAD`
//!   is the parameter `request_is_head` (step 1).
//! - §6.3 step 3 (both `Transfer-Encoding` and `Content-Length`) "ought to
//!   be handled as an error": `Invalid`, never resolved in favour of
//!   either.
//! - §6.1: an HTTP/1.0 response with `Transfer-Encoding` is treated "as if
//!   the framing is faulty": `Invalid`. HTTP/1.0 is the version `1.0`
//!   exactly.
//! - §6.3 step 4 for codings: `chunked` alone is decoded. Codings before a
//!   final `chunked`, or a final coding that is not `chunked` (which step 4
//!   would read until close), are content we cannot decode: `Unsupported`.
//!   `chunked` with parameters is `Invalid` (§7.1: "Their presence SHOULD
//!   be treated as an error"), and so is a `Transfer-Encoding` with no
//!   codings at all (an empty list), so that no two readings of it exist.
//! - The trailer section (§7.1.2) is parsed with the same field-line
//!   grammar and dropped ("MAY selectively retain or discard").
//! - `HEXDIG` (RFC 5234 B.1) is `DIGIT / "A" / ... / "F"`; RFC 5234 §2.3
//!   matches the letters case-insensitively, so `a`-`f` are hex digits too.
//! - Limits, each a choice of ours: a line (status line, field line, chunk
//!   size line, trailer line) is at most [`max_line`] octets before its
//!   CRLF; a field section (or trailer section) is at most [`max_lines`]
//!   lines before the empty line; a body (decoded) is at most
//!   [`max_body`] octets, whatever its framing. Going past any limit is
//!   `Invalid`, and is decided as soon as the bytes received show it.
//! - A chunk size or `Content-Length` is a `nat` here; the limit on the
//!   body bounds it, which is how we meet §7.1's "recipients MUST
//!   anticipate potentially large hexadecimal numerals".
//! - A response is kept with its version digits, status code, reason
//!   phrase (kept, never interpreted: §4 "A client SHOULD ignore the
//!   reason-phrase content"), field lines in order, and body.
//!
//! The request side is a serializer only (the browser never parses
//! requests): RFC 9112 §3's `request-line` and §5's field lines, with
//! "HTTP/1.1" as the version.

/// The field syntax this spec is written in (RFC 9110), re-exported so the
/// sibling modules need only `use super::spec::*`.
pub use crate::field::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Limits (modelling choices).
// ===========================================================================

/// The longest line accepted, in octets before its CRLF.
pub open spec fn max_line() -> nat {
    8192
}

/// The most lines a field section or trailer section may have, the empty
/// line that ends it not counted.
pub open spec fn max_lines() -> nat {
    256
}

/// The largest body accepted, in octets (64 MiB), after chunked decoding.
pub open spec fn max_body() -> nat {
    0x400_0000
}

// ===========================================================================
// §2.1, §2.2 lines.
// ===========================================================================

/// RFC 5234 B.1: `CR = %x0D`, `LF = %x0A`; is there a CRLF at `i`?
pub open spec fn crlf_at(s: Seq<u8>, i: int) -> bool {
    0 <= i && i + 1 < s.len() && s[i] == 0x0D && s[i + 1] == 0x0A
}

/// The position of the first CRLF in `s` at or after `i`.
pub open spec fn find_crlf_from(s: Seq<u8>, i: nat) -> Option<nat>
    decreases s.len() - i
{
    if i + 1 >= s.len() {
        None
    } else if crlf_at(s, i as int) {
        Some(i)
    } else {
        find_crlf_from(s, i + 1)
    }
}

/// The result of reading one line.
pub enum LineRead {
    /// The octets before the first CRLF, and what follows the CRLF.
    Line {
        /// the octets before the CRLF
        line: Seq<u8>,
        /// what follows the CRLF
        rest: Seq<u8>,
    },
    /// No CRLF yet, and the line is not yet too long.
    Incomplete,
    /// The line is longer than [`max_line`] (or will be, whatever arrives).
    TooLong,
}

/// One line at the start of `s` (§2.1: each of the start-line and the field
/// lines is followed by CRLF; §2.2: "the line terminator for the start-line
/// and fields is the sequence CRLF").
pub open spec fn read_line(s: Seq<u8>) -> LineRead {
    match find_crlf_from(s, 0) {
        Some(i) => if i <= max_line() {
            LineRead::Line { line: s.take(i as int), rest: s.skip((i + 2) as int) }
        } else {
            LineRead::TooLong
        },
        // A CRLF that arrives later starts at s.len() - 1 or after.
        None => if s.len() > max_line() + 1 {
            LineRead::TooLong
        } else {
            LineRead::Incomplete
        },
    }
}

// ===========================================================================
// §2.3 HTTP-version, §4 status line.
// ===========================================================================

/// A parsed status line (§4).
pub struct StatusLine {
    /// the first `DIGIT` of `HTTP-version`, as a number
    pub major: nat,
    /// the second
    pub minor: nat,
    /// `status-code`, as a number from 0 to 999
    pub status: nat,
    /// `reason-phrase`, possibly empty, kept and never interpreted
    pub reason: Seq<u8>,
}

/// The value of a decimal digit.
pub open spec fn digit_value(c: u8) -> nat {
    (c - 0x30) as nat
}

/// "HTTP/" (§2.3: `HTTP-name = %s"HTTP"`, case-sensitive, then "/").
pub open spec fn lit_http_slash() -> Seq<u8> {
    seq![0x48u8, 0x54, 0x54, 0x50, 0x2F]
}

/// §4: `status-line = HTTP-version SP status-code SP [ reason-phrase ]`,
/// with the SP after the status code optional at the end of the line and
/// the version 1.x (see the modelling choices), over the whole of `line`, with §2.3 `HTTP-version = HTTP-name "/" DIGIT
/// "." DIGIT`, `status-code = 3DIGIT` and `reason-phrase = 1*( HTAB / SP /
/// VCHAR / obs-text )`.
pub open spec fn parse_status_line(line: Seq<u8>) -> Option<StatusLine> {
    if line.len() >= 12
        // HTTP-name "/"
        && line.take(5) == lit_http_slash()
        // DIGIT "." DIGIT
        && is_digit(line[5]) && line[6] == 0x2E && is_digit(line[7])
        // HTTP/1.x only (modelling choice).
        && line[5] == 0x31
        // SP
        && line[8] == 0x20
        // status-code = 3DIGIT
        && is_digit(line[9]) && is_digit(line[10]) && is_digit(line[11])
        // The line may end after the status code (modelling choice, §4's
        // leniency); otherwise SP, then [ reason-phrase ].
        && (line.len() == 12 || (line[12] == 0x20
        // [ reason-phrase ]: the octets of `reason-phrase` are exactly
        // those of `field-content` (SP / HTAB / VCHAR / obs-text).
        && all_in(line.skip(13), Class::FieldContent)))
    {
        Some(StatusLine {
            major: digit_value(line[5]),
            minor: digit_value(line[7]),
            status: digit_value(line[9]) * 100 + digit_value(line[10]) * 10 + digit_value(line[11]),
            reason: if line.len() == 12 { seq![] } else { line.skip(13) },
        })
    } else {
        None
    }
}

// ===========================================================================
// §5 field lines, §5.2 obsolete line folding.
// ===========================================================================

/// §5: `field-line = field-name ":" OWS field-value OWS`, the start of one:
/// the name and the raw rest after the colon (OWS not yet removed).
/// §5.1: "No whitespace is allowed between the field name and colon."
pub open spec fn parse_field_line_start(line: Seq<u8>) -> Option<FieldLine> {
    let n = run_len(Class::Tchar, line);
    if n > 0 && line.len() > n && line[n as int] == 0x3A {
        Some(FieldLine { name: line.take(n as int), value: line.skip((n + 1) as int) })
    } else {
        None
    }
}

/// The field line `raw` with its value finished: §5.1 "OWS occurring
/// before the first non-whitespace octet of the field line value, or after
/// the last non-whitespace octet of the field line value, is excluded",
/// and the value must then be a `field-value` (RFC 9110 §5.5).
pub open spec fn finish_field_line(raw: FieldLine) -> Option<FieldLine> {
    let value = strip_ows(raw.value);
    if is_field_value(value) {
        Some(FieldLine { name: raw.name, value: value })
    } else {
        None
    }
}

/// `acc` with the pending field line, if any, finished and appended.
pub open spec fn flush_pending(acc: Seq<FieldLine>, pending: Option<FieldLine>) -> Option<Seq<FieldLine>> {
    match pending {
        None => Some(acc),
        Some(raw) => match finish_field_line(raw) {
            Some(line) => Some(acc.push(line)),
            None => None,
        },
    }
}

/// The result of reading a field section.
pub enum SectionRead {
    /// The field lines in order, and what follows the empty line.
    Done {
        /// the field lines, values finished
        fields: Seq<FieldLine>,
        /// what follows the empty line
        rest: Seq<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a field section (or past a limit).
    Invalid,
}

/// §2.1 `*( field-line CRLF ) CRLF`, read line by line from `s`: `acc` are
/// the finished field lines, `pending` the last field line read, which an
/// obs-fold may still continue, and `count` the lines read so far.
pub open spec fn read_section(s: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat) -> SectionRead
    decreases s.len() via read_section_decreases
{
    match read_line(s) {
        LineRead::Incomplete => SectionRead::Incomplete,
        LineRead::TooLong => SectionRead::Invalid,
        LineRead::Line { line, rest } => {
            if line.len() == 0 {
                // The empty line "indicating the end of the header section"
                // (§2.1).
                match flush_pending(acc, pending) {
                    Some(fields) => SectionRead::Done { fields: fields, rest: rest },
                    None => SectionRead::Invalid,
                }
            } else if count >= max_lines() {
                // Past the limit on lines.
                SectionRead::Invalid
            } else if is_ows_octet(line[0]) {
                match pending {
                    // §2.2: whitespace between the start-line and the first
                    // header field: rejected (modelling choice).
                    None => SectionRead::Invalid,
                    // §5.2: an obs-fold, replaced by one SP.
                    Some(raw) => read_section(rest, acc, Some(FieldLine {
                        name: raw.name,
                        value: strip_trailing_ows(raw.value) + seq![0x20u8] + strip_leading_ows(line),
                    }), count + 1),
                }
            } else {
                match parse_field_line_start(line) {
                    None => SectionRead::Invalid,
                    Some(raw) => match flush_pending(acc, pending) {
                        Some(acc2) => read_section(rest, acc2, Some(raw), count + 1),
                        None => SectionRead::Invalid,
                    },
                }
            }
        },
    }
}

/// Termination of [`read_section`]: every line read consumes its CRLF.
#[via_fn]
pub proof fn read_section_decreases(s: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat) {
    super::termination::lemma_read_line_rest(s);
}

// ===========================================================================
// §2.1 the head of a response.
// ===========================================================================

/// The start-line and field section of a response.
pub struct Head {
    /// the status line
    pub status_line: StatusLine,
    /// the field lines, values finished, in order
    pub fields: Seq<FieldLine>,
}

/// The result of reading a head.
pub enum HeadRead {
    /// The head, and what follows its empty line.
    Done {
        /// the head
        head: Head,
        /// what follows its empty line
        rest: Seq<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a response head.
    Invalid,
}

/// §2.1 `start-line CRLF *( field-line CRLF ) CRLF` at the start of `s`,
/// with `start-line = status-line` (a client expects a response). §2.2
/// "read the start-line into a structure, read each header field line ...
/// until the empty line".
pub open spec fn read_head(s: Seq<u8>) -> HeadRead {
    match read_line(s) {
        LineRead::Incomplete => HeadRead::Incomplete,
        LineRead::TooLong => HeadRead::Invalid,
        LineRead::Line { line, rest } => match parse_status_line(line) {
            None => HeadRead::Invalid,
            Some(status_line) => match read_section(rest, seq![], None, 0) {
                SectionRead::Done { fields, rest } => HeadRead::Done {
                    head: Head { status_line: status_line, fields: fields },
                    rest: rest,
                },
                SectionRead::Incomplete => HeadRead::Incomplete,
                SectionRead::Invalid => HeadRead::Invalid,
            },
        },
    }
}

// ===========================================================================
// §6.1, §6.2, §6.3 message body length.
// ===========================================================================

/// "transfer-encoding".
pub open spec fn lit_transfer_encoding() -> Seq<u8> {
    seq![0x74u8, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67]
}

/// "content-length".
pub open spec fn lit_content_length() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68]
}

/// "chunked".
pub open spec fn lit_chunked() -> Seq<u8> {
    seq![0x63u8, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64]
}

/// How the body of a response is delimited (§6.3).
pub enum BodyLength {
    /// No body: the message ends with its head (step 1).
    NoBody,
    /// Exactly this many octets (step 6).
    Length(nat),
    /// The chunked transfer coding (step 4).
    Chunked,
    /// Until the server closes the connection (step 8).
    Close,
    /// The framing is invalid (steps 3 and 5, §6.1, §7.1, the limits).
    Invalid,
    /// A transfer coding we cannot decode (step 4, modelling choice).
    Unsupported,
}

/// §6.3 "Message Body Length", as a client, for the response `head` to a
/// request that was `HEAD` exactly when `request_is_head`.
pub open spec fn body_length(head: Head, request_is_head: bool) -> BodyLength {
    let status = head.status_line.status;
    let te = field_values_named(head.fields, lit_transfer_encoding());
    let cl = field_values_named(head.fields, lit_content_length());
    if request_is_head || (100 <= status && status <= 199) || status == 204 || status == 304 {
        // 1. "Any response to a HEAD request and any response with a 1xx
        // (Informational), 204 (No Content), or 304 (Not Modified) status
        // code is always terminated by the first empty line after the
        // header fields".
        BodyLength::NoBody
    }
    // 2. "Any 2xx (Successful) response to a CONNECT request": we never
    // send CONNECT (modelling choice).
    else if te.len() > 0 && cl.len() > 0 {
        // 3. "both a Transfer-Encoding and a Content-Length header field
        // ... ought to be handled as an error."
        BodyLength::Invalid
    } else if te.len() > 0 {
        // 4. "If a Transfer-Encoding header field is present".
        if head.status_line.major == 1 && head.status_line.minor == 0 {
            // §6.1: "A server or client that receives an HTTP/1.0 message
            // containing a Transfer-Encoding header field MUST treat the
            // message as if the framing is faulty".
            BodyLength::Invalid
        } else {
            match parse_transfer_encoding(combine(te)) {
                None => BodyLength::Invalid,
                Some(codings) => if codings.len() == 0 {
                    // No codings at all (modelling choice).
                    BodyLength::Invalid
                } else if field_name_eq(codings.last().name, lit_chunked()) {
                    // "the chunked transfer coding (Section 7.1) is the
                    // final encoding".
                    if codings.last().parameters.len() > 0 {
                        // §7.1: "The chunked coding does not define any
                        // parameters. Their presence SHOULD be treated as
                        // an error."
                        BodyLength::Invalid
                    } else if codings.len() == 1 {
                        BodyLength::Chunked
                    } else {
                        // Other codings under chunked (modelling choice).
                        BodyLength::Unsupported
                    }
                } else {
                    // "If a Transfer-Encoding header field is present in a
                    // response and the chunked transfer coding is not the
                    // final encoding, the message body length is determined
                    // by reading the connection until it is closed": its
                    // content is in a coding we cannot decode (modelling
                    // choice).
                    BodyLength::Unsupported
                }
            }
        }
    } else if cl.len() > 0 {
        match parse_content_length_lines(cl) {
            // 5. "If a message is received without Transfer-Encoding and
            // with an invalid Content-Length header field, then the message
            // framing is invalid" (the repeated-value list is handled by
            // `parse_content_length`).
            None => BodyLength::Invalid,
            // 6. "its decimal value defines the expected message body
            // length in octets", up to the limit.
            Some(n) => if n > max_body() {
                BodyLength::Invalid
            } else {
                BodyLength::Length(n)
            },
        }
    }
    // 7. "If this is a request message": not for a client.
    else {
        // 8. "Otherwise, this is a response message without a declared
        // message body length, so the message body length is determined by
        // the number of octets received prior to the server closing the
        // connection."
        BodyLength::Close
    }
}

// ===========================================================================
// §7.1 chunked transfer coding.
// ===========================================================================

/// RFC 5234 B.1: `HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"`,
/// letters case-insensitive (RFC 5234 §2.3).
pub open spec fn is_hexdig(c: u8) -> bool {
    is_digit(c) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

/// The value of a hex digit.
pub open spec fn hexdig_value(c: u8) -> nat {
    if is_digit(c) {
        (c - 0x30) as nat
    } else if 0x41 <= c && c <= 0x46 {
        (c - 0x41 + 10) as nat
    } else {
        (c - 0x61 + 10) as nat
    }
}

/// The length of the longest prefix of `s` made of hex digits.
pub open spec fn hex_run_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && is_hexdig(s[0]) {
        1 + hex_run_len(s.drop_first())
    } else {
        0
    }
}

/// The number written by the hex digits `s` (empty is 0).
pub open spec fn hex_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        hex_value(s.drop_last()) * 16 + hexdig_value(s.last())
    }
}

/// §7.1.1: `chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS
/// chunk-ext-val ] )`, `chunk-ext-name = token`, `chunk-ext-val = token /
/// quoted-string`, over the whole of `s`. The extensions are checked and
/// then ignored ("A recipient MUST ignore unrecognized chunk extensions").
pub open spec fn is_chunk_ext(s: Seq<u8>) -> bool
    decreases s.len() via is_chunk_ext_decreases
{
    if s.len() == 0 {
        // The repetition ends here.
        true
    } else {
        // BWS ";"
        let a = strip_leading_ows(s);
        if a.len() == 0 || a[0] != 0x3B {
            false
        } else {
            // BWS chunk-ext-name
            let b = strip_leading_ows(a.drop_first());
            let n = run_len(Class::Tchar, b);
            if n == 0 {
                false
            } else {
                let c = b.skip(n as int);
                // [ BWS "=" BWS chunk-ext-val ]: present exactly when "="
                // follows the BWS, since otherwise only BWS ";" or the end
                // can follow.
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
        }
    }
}

/// Termination of [`is_chunk_ext`]: every round consumes the ";" and a name.
#[via_fn]
pub proof fn is_chunk_ext_decreases(s: Seq<u8>) {
    super::termination::lemma_chunk_ext_rest(s);
}

/// The size of a `chunk-size [ chunk-ext ]` line (§7.1: `chunk-size =
/// 1*HEXDIG`; `last-chunk = 1*("0") [ chunk-ext ] CRLF` is the case of size
/// zero), or `None` if `line` is not one.
pub open spec fn parse_chunk_size_line(line: Seq<u8>) -> Option<nat> {
    let n = hex_run_len(line);
    if n > 0 && is_chunk_ext(line.skip(n as int)) {
        Some(hex_value(line.take(n as int)))
    } else {
        None
    }
}

/// The result of reading a body.
pub enum BodyRead {
    /// The decoded body, and what follows the message.
    Done {
        /// the decoded content
        body: Seq<u8>,
        /// what follows the message
        rest: Seq<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a chunked body (or past a limit).
    Invalid,
}

/// §7.1 `chunked-body = *chunk last-chunk trailer-section CRLF`, `chunk =
/// chunk-size [ chunk-ext ] CRLF chunk-data CRLF`, decoded as §7.1.3 does
/// from `s`, with `body` the content decoded so far.
pub open spec fn read_chunks(s: Seq<u8>, body: Seq<u8>) -> BodyRead
    decreases s.len() via read_chunks_decreases
{
    // "read chunk-size, chunk-ext (if any), and CRLF"
    match read_line(s) {
        LineRead::Incomplete => BodyRead::Incomplete,
        LineRead::TooLong => BodyRead::Invalid,
        LineRead::Line { line, rest } => match parse_chunk_size_line(line) {
            None => BodyRead::Invalid,
            Some(size) => if size == 0 {
                // "while (chunk-size > 0)" ends; "read trailer field ...
                // while (trailer field is not empty)": §7.1.2
                // `trailer-section = *( field-line CRLF )` and the final
                // CRLF. The trailer fields are discarded.
                match read_section(rest, seq![], None, 0) {
                    SectionRead::Done { fields: _, rest: after } => BodyRead::Done { body: body, rest: after },
                    SectionRead::Incomplete => BodyRead::Incomplete,
                    SectionRead::Invalid => BodyRead::Invalid,
                }
            } else if body.len() + size > max_body() {
                // Past the limit on the body.
                BodyRead::Invalid
            } else if rest.len() < size + 2 {
                // "read chunk-data and CRLF": not all here yet.
                BodyRead::Incomplete
            } else if crlf_at(rest, size as int) {
                // "append chunk-data to content"
                read_chunks(rest.skip((size + 2) as int), body + rest.take(size as int))
            } else {
                // chunk-data is exactly chunk-size octets, then CRLF.
                BodyRead::Invalid
            },
        },
    }
}

/// Termination of [`read_chunks`]: every chunk consumes its size line.
#[via_fn]
pub proof fn read_chunks_decreases(s: Seq<u8>, body: Seq<u8>) {
    super::termination::lemma_read_line_rest(s);
}

// ===========================================================================
// The response.
// ===========================================================================

/// A response (§2.1, §4, §6).
pub struct Response {
    /// the status line
    pub status_line: StatusLine,
    /// the field lines of the header section, in order
    pub fields: Seq<FieldLine>,
    /// the content: the message body with the chunked coding removed
    pub body: Seq<u8>,
}

/// The result of parsing a response.
pub enum Parse {
    /// The response, and the octets received after it (§6.3: "A client
    /// MUST NOT process, cache, or forward such extra data as a separate
    /// response").
    Done {
        /// the response
        response: Response,
        /// the octets received after it
        rest: Seq<u8>,
    },
    /// Nothing is decided yet: more bytes are needed.
    Incomplete,
    /// Not a valid response, or past a limit.
    Invalid,
    /// A valid response head whose body is in a transfer coding we cannot
    /// decode.
    Unsupported,
}

/// The response with head `head` and content `body`.
pub open spec fn response_of(head: Head, body: Seq<u8>) -> Response {
    Response { status_line: head.status_line, fields: head.fields, body: body }
}

/// The response at the start of `input`, everything received so far on a
/// connection that is still open, to a request that was `HEAD` exactly
/// when `request_is_head`.
pub open spec fn parse_response(input: Seq<u8>, request_is_head: bool) -> Parse {
    match read_head(input) {
        HeadRead::Incomplete => Parse::Incomplete,
        HeadRead::Invalid => Parse::Invalid,
        HeadRead::Done { head, rest } => match body_length(head, request_is_head) {
            BodyLength::NoBody => Parse::Done { response: response_of(head, seq![]), rest: rest },
            BodyLength::Length(n) => if rest.len() >= n {
                Parse::Done { response: response_of(head, rest.take(n as int)), rest: rest.skip(n as int) }
            } else {
                Parse::Incomplete
            },
            BodyLength::Chunked => match read_chunks(rest, seq![]) {
                BodyRead::Done { body, rest: after } => Parse::Done { response: response_of(head, body), rest: after },
                BodyRead::Incomplete => Parse::Incomplete,
                BodyRead::Invalid => Parse::Invalid,
            },
            // §6.3 step 8: the body ends only when the connection closes;
            // past the limit, it is invalid already.
            BodyLength::Close => if rest.len() > max_body() {
                Parse::Invalid
            } else {
                Parse::Incomplete
            },
            BodyLength::Invalid => Parse::Invalid,
            BodyLength::Unsupported => Parse::Unsupported,
        },
    }
}

/// The response in `input`, everything received on a connection the
/// server has now closed. A close-delimited body (§6.3 step 8) is
/// everything after the head; any other message that is still incomplete
/// is an error (§6.3 step 6: "If the sender closes the connection ...
/// before the indicated number of octets are received, the recipient MUST
/// consider the message to be incomplete and close the connection"; the
/// same holds for an unfinished head or chunked body).
pub open spec fn parse_response_at_close(input: Seq<u8>, request_is_head: bool) -> Parse {
    match parse_response(input, request_is_head) {
        Parse::Incomplete => match read_head(input) {
            HeadRead::Done { head, rest } => match body_length(head, request_is_head) {
                BodyLength::Close => Parse::Done { response: response_of(head, rest), rest: seq![] },
                _ => Parse::Invalid,
            },
            _ => Parse::Invalid,
        },
        decided => decided,
    }
}

// ===========================================================================
// §3 request line and §5 field lines: the serializer.
// ===========================================================================

/// A request to send: its method, its request target (already in origin
/// form, §3.2.1), and its field lines in order.
pub struct Request {
    /// `method = token` (§3.1)
    pub method: Seq<u8>,
    /// `request-target` (§3.2)
    pub target: Seq<u8>,
    /// the header field lines, values without surrounding whitespace
    pub fields: Seq<FieldLine>,
}

/// Every octet of `s` is a `VCHAR`.
pub open spec fn all_vchar(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (is_vchar(s[0]) && all_vchar(s.drop_first()))
}

/// A request target the serializer writes: non-empty visible ASCII, so it
/// holds no SP, CR or LF and the request line stays one line. (Every form
/// of §3.2 is made of such octets; which form is the caller's choice.)
pub open spec fn is_request_target(t: Seq<u8>) -> bool {
    t.len() > 0 && all_vchar(t)
}

/// Every field line of `fields` has a `field-name` and a `field-value`.
pub open spec fn all_valid_fields(fields: Seq<FieldLine>) -> bool
    decreases fields.len()
{
    fields.len() == 0 || (is_field_name(fields[0].name) && is_field_value(fields[0].value)
        && all_valid_fields(fields.drop_first()))
}

/// A request the serializer can write.
pub open spec fn is_valid_request(r: Request) -> bool {
    is_token(r.method) && is_request_target(r.target) && all_valid_fields(r.fields)
}

/// RFC 5234 B.1: `CRLF = CR LF`.
pub open spec fn lit_crlf() -> Seq<u8> {
    seq![0x0Du8, 0x0A]
}

/// "HTTP/1.1" (§2.3).
pub open spec fn lit_http_1_1() -> Seq<u8> {
    seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31]
}

/// `*( field-line CRLF )` for `fields`, each written `field-name ":" SP
/// field-value` (§5.1: "a single SP preceding the field line value is
/// preferred").
pub open spec fn serialize_fields(fields: Seq<FieldLine>) -> Seq<u8>
    decreases fields.len()
{
    if fields.len() == 0 {
        seq![]
    } else {
        fields[0].name + seq![0x3Au8, 0x20u8] + fields[0].value + lit_crlf()
            + serialize_fields(fields.drop_first())
    }
}

/// §2.1 `HTTP-message` for a request with no body: §3 `request-line =
/// method SP request-target SP HTTP-version`, CRLF, the field lines, and
/// the empty line.
pub open spec fn serialize_request(r: Request) -> Seq<u8> {
    r.method + seq![0x20u8] + r.target + seq![0x20u8] + lit_http_1_1() + lit_crlf()
        + serialize_fields(r.fields) + lit_crlf()
}

} // verus!
