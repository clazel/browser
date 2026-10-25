//! An independent transcription of HTTP/1.1 message framing from a
//! different RFC than [`super::spec`]: RFC 7230 "HTTP/1.1: Message Syntax
//! and Routing" (June 2014), §3 (message format) and §4.1 (chunked
//! transfer coding), the text RFC 9112 obsoleted (docs/VERIFICATION.md,
//! "Trust without reviewers", item 2). The transcription section uses
//! nothing from `spec.rs` but three plain data carriers (`FieldLine`,
//! `StatusLine`, `Response`), so that the two sides can be compared; only
//! the proof section after it uses the spec's functions. Unlike
//! `field/independent.rs`, it was not written without having read
//! `spec.rs`: its author had read it, so what makes it independent is the
//! other RFC's text and grammar it follows (and the differences between the
//! two, listed below), not isolation from the spec.
//!
//! Source (pinned; an RFC never changes after publication): RFC 7230, June
//! 2014, <https://www.rfc-editor.org/rfc/rfc7230>: §3 `HTTP-message`; §3.1.2
//! `status-line` (with §2.6 `HTTP-version`); §3.2 `header-field`,
//! `field-value`, `obs-fold`; §3.2.3 `OWS`; §3.2.6 `token`, `quoted-string`;
//! §3.3.2 `Content-Length`; §3.3.3 message body length; §4.1 chunked
//! transfer coding, §4.1.1 chunk extensions, §4.1.2 trailer, §4.1.3
//! decoding. RFC 5234 for `DIGIT`, `HEXDIG`, `VCHAR`.
//!
//! # What is proven
//!
//! [`r_parse`] reads the response at the start of an input as RFC 7230
//! describes, and says `Done` (the response and the octets after it), `No`
//! (not a valid response, or not all of it is here) or `Out` (see below).
//! [`theorem_independent_framing`] proves, for **every** input and both
//! values of "the request was HEAD":
//!
//! - `r_parse` says `Done { response, rest }`: then `parse_response` says
//!   `Done` with that same response and rest;
//! - `r_parse` says `No`: then `parse_response` is not `Done` (it is
//!   `Incomplete`, `Invalid` or `Unsupported`);
//! - `r_parse` says `Out`: nothing is claimed.
//!
//! So the two never disagree about a response they both decide, and a
//! response the spec finishes is one RFC 7230 finishes the same way, or an
//! `Out` input. [`corollary_independent_framing`] states that last half.
//! The same equalities hold part by part: the status line
//! ([`lemma_r_status_line`]), the field section and trailer
//! ([`lemma_r_section`], for any state the spec was in), the chunk
//! extension ([`lemma_r_chunk_ext`]), the chunked body
//! ([`lemma_r_chunked`]) and the body length ([`lemma_r_body_length`]).
//! `example_*` show each case by evaluation, including one input per `Out`
//! class, so the theorem is not vacuous.
//!
//! # Where RFC 7230 and RFC 9112 differ: the `Out` inputs
//!
//! Each is a place where reading RFC 7230 literally gives another answer
//! than `spec.rs` (RFC 9112 plus a stated modelling choice). The
//! transcription returns `Out` there and the theorem claims nothing.
//!
//! - **Obs-fold.** RFC 7230 §3.2.4: a user agent replaces each `obs-fold`
//!   (`CRLF 1*( SP / HTAB )`) "with one or more SP octets"; RFC 9112 §5.2
//!   gives `obs-fold = OWS CRLF RWS`. The spec replaces the whitespace
//!   before the CRLF, the CRLF and the whitespace after with one SP; the
//!   RFC 7230 text leaves the whitespace before the CRLF in place. They
//!   give different values for `a  ` fold `b`. Every line that begins with
//!   `SP` or `HTAB` after the start-line (an obs-fold, or a
//!   whitespace-preceded line right after the start-line, which both RFCs
//!   say to reject or consume) is `Out`, and so is a field line that is not
//!   a field value when the next line is one.
//! - **`Transfer-Encoding` with `Content-Length`.** RFC 7230 §3.3.3 item
//!   3: "Transfer-Encoding overrides the Content-Length"; RFC 9112 §6.3 item
//!   3 makes it an error, and so does the spec.
//! - **Codings.** Anything but exactly one `Transfer-Encoding` field line
//!   whose value is `chunked` in any case: other codings, `chunked` with
//!   parameters, several lines, an empty list. RFC 7230 would decode a
//!   coding before `chunked` or read to the close if `chunked` is not last;
//!   the spec calls them `Unsupported` or `Invalid`.
//! - **HTTP/1.0 with `Transfer-Encoding`.** An error in RFC 9112 §6.1, not
//!   in RFC 7230.
//! - **`Content-Length` that is not exactly one line of digits.** The
//!   repeated-value and list cases are worded differently ("same decimal
//!   value" against the spec's "same digits": `42, 042`), and the
//!   transcription does not cover them.
//! - **Chunk extension whitespace.** RFC 9112 §7.1.1 allows `BWS` around
//!   `;` and `=`; RFC 7230 §4.1.1 does not. A chunk-size line that is not a
//!   `chunk-ext` in RFC 7230 and has an `SP` or `HTAB` is `Out`; one
//!   without is `No`, proven rejected by the spec too.
//! - **Status line.** RFC 7230 §3.1.2 requires the SP after the status
//!   code even with no reason phrase; the spec accepts `HTTP/1.1 301` (a
//!   modelling choice listed in `spec.rs`). A major version other than 1 is
//!   a valid `HTTP-version` in both RFCs but the spec rejects it. Both
//!   `Out`.
//!
//! # Modelling choices and limits of the claim
//!
//! - The transcription decides whether a response is there, not *why* it
//!   is not: `No` covers both "not all here yet" and "not valid", which
//!   RFC 7230 does not distinguish (RFC 7230 says nothing of incremental
//!   parsing). The spec's `Incomplete`, `Invalid` and `Unsupported` are
//!   therefore compared only as "not `Done`". **Not covered:**
//!   `parse_response_at_close` (a body that ends when the server closes
//!   the connection: `r_parse` says `No` for it, as the spec's
//!   `parse_response` is not `Done` for it); the executable parser (proven
//!   equal to the spec in `line.rs` and `body.rs`, so equal to this through
//!   the spec); and the request serializer (RFC 7230 §3.1.1 is not
//!   transcribed).
//! - The limits are the spec's numbers (`r_max_line`, `r_max_lines`,
//!   `r_max_body`): a limit is a choice of the implementation, not of the
//!   RFC, and a message past one is `No`, as it is `Invalid` in the spec.
//! - A chunk size and a `Content-Length` are numbers of unbounded size
//!   here; the body limit bounds them. The digit values use the same
//!   left-to-right arithmetic as the spec (`r_hex_value`, `r_dec_value`).
//! - Lines end only at CRLF, and no grammar here accepts a CR or LF inside
//!   a line (RFC 7230 §3.5 lets a recipient accept a bare LF as a line
//!   terminator; the spec chose not to, and so does this).
//! - RFC 7230 §3.2's `field-content` cannot match a value with two inner
//!   whitespace runs (`a b c`). The transcription uses RFC 9110 §5.5's
//!   reading, the evident intent: see `docs/ERRATA.md`.
//! - The same-looking helpers (`r_first_crlf`, `r_token_len`, `r_hex_len`,
//!   `r_ltrim`) are the obvious loops over octets; the transcription's
//!   independence is in the grammar it follows, the order in which it
//!   decides (the whole message in one pass, a section as a list that is
//!   built from the end, `Out` where the RFCs differ), and the body-length
//!   rules, not in these.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Transcription: RFC 7230 §3 (uses nothing from spec.rs but the data
// carriers FieldLine, StatusLine and Response).
// ===========================================================================

/// RFC 5234 B.1: `DIGIT = %x30-39`.
pub open spec fn r_is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// RFC 5234 B.1: `ALPHA = %x41-5A / %x61-7A`.
pub open spec fn r_is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// RFC 5234 B.1: `VCHAR = %x21-7E`.
pub open spec fn r_is_vchar(c: u8) -> bool {
    0x21 <= c <= 0x7E
}

/// RFC 7230 §3.2.6: `obs-text = %x80-FF`.
pub open spec fn r_is_obs_text(c: u8) -> bool {
    0x80 <= c
}

/// RFC 7230 §3.2.3: `OWS = *( SP / HTAB )`: an octet of it.
pub open spec fn r_is_wsp(c: u8) -> bool {
    c == 0x20 || c == 0x09
}

/// RFC 7230 §3.2.6: `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+"
/// / "-" / "." / "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA`.
pub open spec fn r_is_tchar(c: u8) -> bool {
    c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27 || c == 0x2A
        || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F || c == 0x60
        || c == 0x7C || c == 0x7E || r_is_digit(c) || r_is_alpha(c)
}

/// RFC 7230 §3.2: `field-vchar = VCHAR / obs-text`.
pub open spec fn r_is_field_vchar(c: u8) -> bool {
    r_is_vchar(c) || r_is_obs_text(c)
}

/// RFC 7230 §3.1.2: an octet of `reason-phrase = *( HTAB / SP / VCHAR /
/// obs-text )`.
pub open spec fn r_is_reason_octet(c: u8) -> bool {
    c == 0x09 || c == 0x20 || r_is_vchar(c) || r_is_obs_text(c)
}

/// RFC 5234 B.1: `HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"`, the
/// letters matching either case (RFC 5234 §2.3).
pub open spec fn r_is_hexdig(c: u8) -> bool {
    r_is_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

/// RFC 7230 §3.2.6: an octet of the body of a `quoted-string`: `qdtext =
/// HTAB / SP /%x21 / %x23-5B / %x5D-7E / obs-text`.
pub open spec fn r_is_qdtext(c: u8) -> bool {
    c == 0x09 || c == 0x20 || c == 0x21 || (0x23 <= c <= 0x5B) || (0x5D <= c <= 0x7E)
        || r_is_obs_text(c)
}

/// RFC 7230 §3.2.6: the octet after the backslash of `quoted-pair = "\" (
/// HTAB / SP / VCHAR / obs-text )`.
pub open spec fn r_is_quoted_pair_octet(c: u8) -> bool {
    c == 0x09 || c == 0x20 || r_is_vchar(c) || r_is_obs_text(c)
}

/// The longest line accepted, in octets before its CRLF (the same number
/// as `max_line()`: a limit is a choice of the implementation, not of the
/// RFC).
pub open spec fn r_max_line() -> nat {
    8192
}

/// The most lines a header section or trailer may have (as `max_lines()`).
pub open spec fn r_max_lines() -> nat {
    256
}

/// The largest decoded body accepted (as `max_body()`).
pub open spec fn r_max_body() -> nat {
    0x400_0000
}

/// The position of the first CRLF at or after `p` in `s`.
pub open spec fn r_first_crlf(s: Seq<u8>, p: nat) -> Option<nat>
    decreases s.len() - p
{
    if p + 1 >= s.len() {
        None
    } else if s[p as int] == 0x0D && s[(p + 1) as int] == 0x0A {
        Some(p)
    } else {
        r_first_crlf(s, p + 1)
    }
}

/// The length of the longest prefix of `s` that is a `token`.
pub open spec fn r_token_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && r_is_tchar(s[0]) {
        1 + r_token_len(s.drop_first())
    } else {
        0
    }
}

/// `s` without leading `OWS`.
pub open spec fn r_ltrim(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && r_is_wsp(s[0]) {
        r_ltrim(s.drop_first())
    } else {
        s
    }
}

/// `s` without trailing `OWS`.
pub open spec fn r_rtrim(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && r_is_wsp(s.last()) {
        r_rtrim(s.drop_last())
    } else {
        s
    }
}

/// Every octet of `s` is one of `SP`, `HTAB` and `field-vchar`.
pub open spec fn r_all_field_content(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || ((r_is_wsp(s[0]) || r_is_field_vchar(s[0])) && r_all_field_content(s.drop_first()))
}

/// Every octet of `s` is a `reason-phrase` octet.
pub open spec fn r_all_reason(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (r_is_reason_octet(s[0]) && r_all_reason(s.drop_first()))
}

/// RFC 7230 §3.2: `field-value = *( field-content / obs-fold )`, with
/// `field-content` read as RFC 9110 §5.5 writes it: `field-vchar [ 1*( SP
/// / HTAB / field-vchar ) field-vchar ]` (RFC 7230's own `field-vchar [
/// 1*( SP / HTAB ) field-vchar ]` cannot match "a b c": see the header).
/// With no obs-fold: empty, or beginning and ending with a `field-vchar`
/// with only `SP`, `HTAB` and `field-vchar` between.
pub open spec fn r_is_field_value(v: Seq<u8>) -> bool {
    v.len() == 0 || (r_is_field_vchar(v[0]) && r_is_field_vchar(v.last()) && r_all_field_content(v))
}

/// RFC 7230 §3.2: how a line fares as `header-field = field-name ":" OWS
/// field-value OWS`.
pub enum RField {
    /// A header field: its name and its value, without surrounding `OWS`.
    Ok(FieldLine),
    /// There is no `field-name ":"` at the start.
    NameBad,
    /// The name is there, the value is not a `field-value`.
    ValueBad,
}

/// The line `line` (without its CRLF) as a `header-field`.
pub open spec fn r_header_field(line: Seq<u8>) -> RField {
    let n = r_token_len(line);
    if !(n > 0 && line.len() > n && line[n as int] == 0x3A) {
        RField::NameBad
    } else {
        let v = r_rtrim(r_ltrim(line.skip((n + 1) as int)));
        if r_is_field_value(v) {
            RField::Ok(FieldLine { name: line.take(n as int), value: v })
        } else {
            RField::ValueBad
        }
    }
}

/// What the RFC's rules say of a header section (or a trailer): `Ok` for a
/// match of `*( header-field CRLF ) CRLF`, `No` for anything that is not
/// one (or is not complete yet), `Out` when the input is outside what this
/// transcription covers (see the header: an obs-fold).
pub enum RSection {
    /// The fields in order, and what follows the empty line.
    Ok {
        /// the header fields
        fields: Seq<FieldLine>,
        /// what follows the empty line
        rest: Seq<u8>,
    },
    /// Not a header section, or not all here.
    No,
    /// Outside the covered inputs.
    Out,
}

/// `*( header-field CRLF ) CRLF` at the start of `s`, with `count` header
/// fields already read.
pub open spec fn r_header_section(s: Seq<u8>, count: nat) -> RSection
    decreases s.len() via r_header_section_decreases
{
    match r_first_crlf(s, 0) {
        None => RSection::No,
        Some(n) => if n > r_max_line() {
            RSection::No
        } else if n == 0 {
            // The empty line that ends the section.
            RSection::Ok { fields: seq![], rest: s.skip(2) }
        } else if count >= r_max_lines() {
            RSection::No
        } else if r_is_wsp(s[0]) {
            // `obs-fold = CRLF 1*( SP / HTAB )`, or a line of whitespace
            // after the start-line: outside (see the header).
            RSection::Out
        } else {
            let line = s.take(n as int);
            let rest = s.skip((n + 2) as int);
            match r_header_field(line) {
                RField::NameBad => RSection::No,
                // The line is not a field value; the RFC ends it here, so
                // does this, unless an obs-fold would continue it.
                RField::ValueBad => if rest.len() > 0 && r_is_wsp(rest[0]) {
                    RSection::Out
                } else {
                    RSection::No
                },
                RField::Ok(f) => match r_header_section(rest, count + 1) {
                    RSection::Ok { fields, rest: after } => RSection::Ok { fields: seq![f] + fields, rest: after },
                    RSection::No => RSection::No,
                    RSection::Out => RSection::Out,
                },
            }
        },
    }
}

/// A CRLF found by [`r_first_crlf`] leaves room for itself.
pub proof fn lemma_r_first_crlf_some(s: Seq<u8>, p: nat)
    ensures
        match r_first_crlf(s, p) {
            Some(n) => p <= n && n + 2 <= s.len() && s[n as int] == 0x0D && s[(n + 1) as int] == 0x0A,
            None => true,
        },
    decreases s.len() - p
{
    if p + 1 < s.len() && !(s[p as int] == 0x0D && s[(p + 1) as int] == 0x0A) {
        lemma_r_first_crlf_some(s, p + 1);
    }
}

/// Termination of [`r_header_section`].
#[via_fn]
pub proof fn r_header_section_decreases(s: Seq<u8>, count: nat) {
    lemma_r_first_crlf_some(s, 0);
}

/// What the RFC's rules say of a status line.
pub enum RStatus {
    /// A `status-line`: its version digits, status code and reason phrase.
    Ok(StatusLine),
    /// Not a `status-line`.
    No,
    /// Outside the covered inputs (see the header: a line with no SP after
    /// the status code, or a major version other than 1).
    Out,
}

/// RFC 7230 §3.1.2: `status-line = HTTP-version SP status-code SP
/// reason-phrase`, with RFC 7230 §2.6 `HTTP-version = HTTP-name "/" DIGIT
/// "." DIGIT`, `HTTP-name = %x48.54.54.50` and `status-code = 3DIGIT`,
/// over the whole of `line` (the octets before the CRLF).
pub open spec fn r_status_line(line: Seq<u8>) -> RStatus {
    let n = line.len();
    // HTTP-version SP status-code
    let prefix = n >= 12 && line[0] == 0x48 && line[1] == 0x54 && line[2] == 0x54 && line[3] == 0x50
        && line[4] == 0x2F && r_is_digit(line[5]) && line[6] == 0x2E && r_is_digit(line[7])
        && line[8] == 0x20 && r_is_digit(line[9]) && r_is_digit(line[10]) && r_is_digit(line[11]);
    if !prefix {
        RStatus::No
    } else if n == 12 {
        // The grammar's second SP is missing: outside.
        RStatus::Out
    } else if !(line[12] == 0x20 && r_all_reason(line.skip(13))) {
        RStatus::No
    } else if line[5] != 0x31 {
        // A major version other than 1: outside.
        RStatus::Out
    } else {
        RStatus::Ok(StatusLine {
            major: (line[5] - 0x30) as nat,
            minor: (line[7] - 0x30) as nat,
            status: ((line[9] - 0x30) * 100 + (line[10] - 0x30) * 10 + (line[11] - 0x30)) as nat,
            reason: line.skip(13),
        })
    }
}

/// The value of the hex digits `s`, most significant first.
pub open spec fn r_hex_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        r_hex_value(s.drop_last()) * 16 + (if r_is_digit(s.last()) {
            (s.last() - 0x30) as nat
        } else if 0x41 <= s.last() <= 0x46 {
            (s.last() - 0x41 + 10) as nat
        } else {
            (s.last() - 0x61 + 10) as nat
        })
    }
}

/// The length of the longest prefix of `s` that is `1*HEXDIG` (or less).
pub open spec fn r_hex_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && r_is_hexdig(s[0]) {
        1 + r_hex_len(s.drop_first())
    } else {
        0
    }
}

/// `s` has no `SP` or `HTAB` anywhere.
pub open spec fn r_no_wsp(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (!r_is_wsp(s[0]) && r_no_wsp(s.drop_first()))
}

/// RFC 7230 §3.2.6: the rest of `quoted-string = DQUOTE *( qdtext /
/// quoted-pair ) DQUOTE` after its opening DQUOTE: what follows the closing
/// one, if there is one.
pub open spec fn r_quoted_rest(v: Seq<u8>) -> Option<Seq<u8>>
    decreases v.len()
{
    if v.len() == 0 {
        None
    } else if v[0] == 0x22 {
        Some(v.drop_first())
    } else if v[0] == 0x5C {
        if v.len() >= 2 && r_is_quoted_pair_octet(v[1]) {
            r_quoted_rest(v.skip(2))
        } else {
            None
        }
    } else if r_is_qdtext(v[0]) {
        r_quoted_rest(v.drop_first())
    } else {
        None
    }
}

/// RFC 7230 §4.1.1: `chunk-ext-val = token / quoted-string` at the start
/// of `v`: what follows it.
pub open spec fn r_ext_val_rest(v: Seq<u8>) -> Option<Seq<u8>> {
    if v.len() > 0 && v[0] == 0x22 {
        r_quoted_rest(v.drop_first())
    } else if r_token_len(v) > 0 {
        Some(v.skip(r_token_len(v) as int))
    } else {
        None
    }
}

/// RFC 7230 §4.1.1: `chunk-ext = *( ";" chunk-ext-name [ "=" chunk-ext-val
/// ] )`, `chunk-ext-name = token`, over the whole of `s`. There is no
/// whitespace in this grammar (RFC 9112 §7.1.1 added `BWS`).
pub open spec fn r_chunk_ext(s: Seq<u8>) -> bool
    decreases s.len() via r_chunk_ext_decreases
{
    if s.len() == 0 {
        true
    } else if s[0] != 0x3B {
        false
    } else {
        let after = s.drop_first();
        let n = r_token_len(after);
        if n == 0 {
            false
        } else {
            let c = after.skip(n as int);
            if c.len() > 0 && c[0] == 0x3D {
                match r_ext_val_rest(c.drop_first()) {
                    Some(rest) => r_chunk_ext(rest),
                    None => false,
                }
            } else {
                r_chunk_ext(c)
            }
        }
    }
}

/// What the RFC's rules say of the part of a chunk-size line after the
/// digits.
pub enum RExt {
    /// A `chunk-ext`.
    Ok,
    /// Not one.
    No,
    /// Not one, but it has `SP` or `HTAB`, which RFC 9112's grammar allows
    /// where this one does not: outside.
    Out,
}

/// The classification of `s` as a `chunk-ext`.
pub open spec fn r_ext_class(s: Seq<u8>) -> RExt {
    if r_chunk_ext(s) {
        RExt::Ok
    } else if r_no_wsp(s) {
        RExt::No
    } else {
        RExt::Out
    }
}

/// What the RFC's rules say of a chunked body.
pub enum RChunked {
    /// The decoded content and what follows the body.
    Ok {
        /// the content
        body: Seq<u8>,
        /// what follows the last CRLF
        rest: Seq<u8>,
    },
    /// Not a chunked body, or not all here.
    No,
    /// Outside the covered inputs.
    Out,
}

/// RFC 7230 §4.1 `chunked-body = *chunk last-chunk trailer-part CRLF`,
/// decoded as §4.1.3 does, from `s`, with `total` octets of content decoded
/// so far. Returns the content of the rest.
pub open spec fn r_chunked(s: Seq<u8>, total: nat) -> RChunked
    decreases s.len() via r_chunked_decreases
{
    match r_first_crlf(s, 0) {
        None => RChunked::No,
        Some(n) => if n > r_max_line() {
            RChunked::No
        } else {
            // "read chunk-size, chunk-ext (if any) and CRLF"
            let line = s.take(n as int);
            let rest = s.skip((n + 2) as int);
            let k = r_hex_len(line);
            if k == 0 {
                RChunked::No
            } else {
                match r_ext_class(line.skip(k as int)) {
                    RExt::No => RChunked::No,
                    RExt::Out => RChunked::Out,
                    RExt::Ok => {
                        let size = r_hex_value(line.take(k as int));
                        if size == 0 {
                            // `last-chunk`, then `trailer-part CRLF`: "read
                            // trailer field ... while (trailer field is not
                            // empty)".
                            match r_header_section(rest, 0) {
                                RSection::Ok { fields: _, rest: after } => RChunked::Ok { body: seq![], rest: after },
                                RSection::No => RChunked::No,
                                RSection::Out => RChunked::Out,
                            }
                        } else if total + size > r_max_body() {
                            RChunked::No
                        } else if rest.len() < size + 2 {
                            RChunked::No
                        } else if !(rest[size as int] == 0x0D && rest[(size + 1) as int] == 0x0A) {
                            RChunked::No
                        } else {
                            // "read chunk-data and CRLF; append chunk-data to
                            // decoded-body"
                            match r_chunked(rest.skip((size + 2) as int), total + size) {
                                RChunked::Ok { body, rest: after } => RChunked::Ok {
                                    body: rest.take(size as int) + body,
                                    rest: after,
                                },
                                RChunked::No => RChunked::No,
                                RChunked::Out => RChunked::Out,
                            }
                        }
                    },
                }
            }
        },
    }
}

/// A token prefix is at most the string.
pub proof fn lemma_r_token_len_le(s: Seq<u8>)
    ensures
        r_token_len(s) <= s.len(),
    decreases s.len()
{
    if s.len() > 0 && r_is_tchar(s[0]) {
        lemma_r_token_len_le(s.drop_first());
    }
}

/// A quoted string's rest is shorter than it.
pub proof fn lemma_r_quoted_rest_len(v: Seq<u8>)
    ensures
        match r_quoted_rest(v) {
            Some(rest) => rest.len() < v.len(),
            None => true,
        },
    decreases v.len()
{
    if v.len() > 0 && v[0] != 0x22 {
        if v[0] == 0x5C {
            if v.len() >= 2 && r_is_quoted_pair_octet(v[1]) {
                lemma_r_quoted_rest_len(v.skip(2));
            }
        } else if r_is_qdtext(v[0]) {
            lemma_r_quoted_rest_len(v.drop_first());
        }
    }
}

/// A `chunk-ext-val`'s rest is shorter than the input (the value is never
/// empty).
pub proof fn lemma_r_ext_val_rest_len(v: Seq<u8>)
    ensures
        match r_ext_val_rest(v) {
            Some(rest) => rest.len() < v.len(),
            None => true,
        },
{
    lemma_r_token_len_le(v);
    if v.len() > 0 && v[0] == 0x22 {
        lemma_r_quoted_rest_len(v.drop_first());
    }
}

/// Termination of [`r_chunk_ext`]: every round consumes a ";" and a name.
#[via_fn]
pub proof fn r_chunk_ext_decreases(s: Seq<u8>) {
    if s.len() > 0 && s[0] == 0x3B {
        let after = s.drop_first();
        lemma_r_token_len_le(after);
        let n = r_token_len(after);
        if n > 0 {
            let c = after.skip(n as int);
            if c.len() > 0 && c[0] == 0x3D {
                lemma_r_ext_val_rest_len(c.drop_first());
            }
        }
    }
}

/// Termination of [`r_chunked`].
#[via_fn]
pub proof fn r_chunked_decreases(s: Seq<u8>, total: nat) {
    lemma_r_first_crlf_some(s, 0);
    match r_first_crlf(s, 0) {
        Some(n) => {
            let line = s.take(n as int);
            let k = r_hex_len(line);
            if n <= r_max_line() && k > 0 && r_hex_value(line.take(k as int)) > 0 {
                let rest = s.skip((n + 2) as int);
                let size = r_hex_value(line.take(k as int));
                if rest.len() >= size + 2 {
                    assert(rest.skip((size + 2) as int).len() < s.len());
                }
            }
        }
        None => {}
    }
}

/// RFC 5234 §2.3: letters in a quoted string match either case; the
/// lowercase of an octet.
pub open spec fn r_lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u8
    } else {
        c
    }
}

/// RFC 7230 §3.2: "Each header field consists of a case-insensitive field
/// name": `a` and `b` are the same name.
pub open spec fn r_ci_eq(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases a.len()
{
    a.len() == b.len() && (a.len() == 0 || (r_lower(a[0]) == r_lower(b[0])
        && r_ci_eq(a.drop_first(), b.drop_first())))
}

/// "Transfer-Encoding" (RFC 7230 §3.3.1), in lowercase.
pub open spec fn r_lit_transfer_encoding() -> Seq<u8> {
    seq![0x74u8, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67]
}

/// "Content-Length" (RFC 7230 §3.3.2), in lowercase.
pub open spec fn r_lit_content_length() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68]
}

/// "chunked" (RFC 7230 §4.1), in lowercase.
pub open spec fn r_lit_chunked() -> Seq<u8> {
    seq![0x63u8, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64]
}

/// The values of the header fields named `name` (compared
/// case-insensitively), in the order received.
pub open spec fn r_values_named(fields: Seq<FieldLine>, name: Seq<u8>) -> Seq<Seq<u8>>
    decreases fields.len()
{
    if fields.len() == 0 {
        seq![]
    } else if r_ci_eq(fields[0].name, name) {
        seq![fields[0].value] + r_values_named(fields.drop_first(), name)
    } else {
        r_values_named(fields.drop_first(), name)
    }
}

/// Every octet of `s` is a `DIGIT`.
pub open spec fn r_all_digit(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (r_is_digit(s[0]) && r_all_digit(s.drop_first()))
}

/// RFC 7230 §3.3.2: `Content-Length = 1*DIGIT`.
pub open spec fn r_is_digits(s: Seq<u8>) -> bool {
    s.len() > 0 && r_all_digit(s)
}

/// The number written by the digits `s`, most significant first.
pub open spec fn r_dec_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        r_dec_value(s.drop_last()) * 10 + ((s.last() - 0x30) as nat)
    }
}

/// How a response's body is delimited, by RFC 7230 §3.3.3.
pub enum RLen {
    /// No body (item 1).
    NoBody,
    /// This many octets (item 5).
    Length(nat),
    /// The chunked coding, the final and only one (item 3).
    Chunked,
    /// Until the server closes the connection (item 7).
    Close,
    /// A length past the limit.
    Over,
    /// Outside the covered inputs (see the header).
    Out,
}

/// RFC 7230 §3.3.3 for a response whose request was `HEAD` exactly when
/// `is_head`, items 1, 3, 5 and 7 (item 2 is CONNECT, item 6 a request).
pub open spec fn r_body_length(sl: StatusLine, fields: Seq<FieldLine>, is_head: bool) -> RLen {
    let status = sl.status;
    if is_head || (100 <= status && status <= 199) || status == 204 || status == 304 {
        // 1. "Any response to a HEAD request and any response with a 1xx
        // (Informational), 204 (No Content), or 304 (Not Modified) status
        // code is always terminated by the first empty line after the
        // header fields".
        RLen::NoBody
    } else {
        let te = r_values_named(fields, r_lit_transfer_encoding());
        let cl = r_values_named(fields, r_lit_content_length());
        if te.len() > 0 {
            // 3. "If a Transfer-Encoding header field is present and the
            // chunked transfer coding is the final encoding".
            if cl.len() > 0 {
                // RFC 7230 lets Transfer-Encoding override Content-Length;
                // RFC 9112 makes it an error: outside.
                RLen::Out
            } else if sl.major == 1 && sl.minor == 0 {
                // RFC 9112 §6.1 makes it an error in an HTTP/1.0 message;
                // RFC 7230 does not: outside.
                RLen::Out
            } else if te.len() == 1 && r_ci_eq(te[0], r_lit_chunked()) {
                RLen::Chunked
            } else {
                // Other codings: outside.
                RLen::Out
            }
        } else if cl.len() > 0 {
            // 5. "If a valid Content-Length header field is present without
            // Transfer-Encoding, its decimal value defines the expected
            // message body length in octets."
            if cl.len() == 1 && r_is_digits(cl[0]) {
                if r_dec_value(cl[0]) > r_max_body() {
                    RLen::Over
                } else {
                    RLen::Length(r_dec_value(cl[0]))
                }
            } else {
                // Repeated or invalid values: outside.
                RLen::Out
            }
        } else {
            // 7. "Otherwise, this is a response message without a declared
            // message body length, so the message body length is determined
            // by the number of octets received prior to the server closing
            // the connection."
            RLen::Close
        }
    }
}

/// What the RFC's rules say of the response at the start of `input`.
pub enum RParse {
    /// The response, and what follows it.
    Done {
        /// the response
        response: Response,
        /// the octets after it
        rest: Seq<u8>,
    },
    /// Not (yet) a complete response, or not a valid one.
    No,
    /// Outside the covered inputs.
    Out,
}

/// RFC 7230 §3 `HTTP-message = start-line *( header-field CRLF ) CRLF [
/// message-body ]` with `start-line = status-line`, for a response to a
/// request that was `HEAD` exactly when `is_head`, on a connection that is
/// still open (a body that ends at the close is not decided, as in the
/// spec).
pub open spec fn r_parse(input: Seq<u8>, is_head: bool) -> RParse {
    match r_first_crlf(input, 0) {
        None => RParse::No,
        Some(n) => if n > r_max_line() {
            RParse::No
        } else {
            let line = input.take(n as int);
            let after_line = input.skip((n + 2) as int);
            match r_status_line(line) {
                RStatus::No => RParse::No,
                RStatus::Out => RParse::Out,
                RStatus::Ok(sl) => match r_header_section(after_line, 0) {
                    RSection::No => RParse::No,
                    RSection::Out => RParse::Out,
                    RSection::Ok { fields, rest } => match r_body_length(sl, fields, is_head) {
                        RLen::NoBody => RParse::Done {
                            response: Response { status_line: sl, fields: fields, body: seq![] },
                            rest: rest,
                        },
                        RLen::Length(len) => if rest.len() >= len {
                            RParse::Done {
                                response: Response { status_line: sl, fields: fields, body: rest.take(len as int) },
                                rest: rest.skip(len as int),
                            }
                        } else {
                            RParse::No
                        },
                        RLen::Chunked => match r_chunked(rest, 0) {
                            RChunked::Ok { body, rest: after } => RParse::Done {
                                response: Response { status_line: sl, fields: fields, body: body },
                                rest: after,
                            },
                            RChunked::No => RParse::No,
                            RChunked::Out => RParse::Out,
                        },
                        RLen::Close => RParse::No,
                        RLen::Over => RParse::No,
                        RLen::Out => RParse::Out,
                    },
                },
            }
        },
    }
}

// ===========================================================================
// Proofs: the transcription equals `spec.rs` wherever it decides.
// ===========================================================================

/// Each octet class of the transcription is the spec's.
pub proof fn lemma_r_classes(c: u8)
    ensures
        r_is_digit(c) == is_digit(c),
        r_is_tchar(c) == is_tchar(c),
        r_is_field_vchar(c) == is_field_vchar(c),
        r_is_wsp(c) == is_ows_octet(c),
        r_is_reason_octet(c) == is_field_content_octet(c),
        r_is_hexdig(c) == is_hexdig(c),
        r_is_qdtext(c) == is_qdtext(c),
        r_is_quoted_pair_octet(c) == is_quoted_pair_octet(c),
{
}

/// The first CRLF is the spec's.
pub proof fn lemma_r_first_crlf(s: Seq<u8>, p: nat)
    ensures
        r_first_crlf(s, p) == find_crlf_from(s, p),
    decreases s.len() - p
{
    if p + 1 < s.len() && !(s[p as int] == 0x0D && s[(p + 1) as int] == 0x0A) {
        lemma_r_first_crlf(s, p + 1);
    }
}

/// A token prefix is a run of `tchar`.
pub proof fn lemma_r_token_len(s: Seq<u8>)
    ensures
        r_token_len(s) == run_len(Class::Tchar, s),
    decreases s.len()
{
    if s.len() > 0 && r_is_tchar(s[0]) {
        lemma_r_classes(s[0]);
        lemma_r_token_len(s.drop_first());
    }
}

/// Trimming leading `OWS` is the spec's.
pub proof fn lemma_r_ltrim(s: Seq<u8>)
    ensures
        r_ltrim(s) == strip_leading_ows(s),
    decreases s.len()
{
    if s.len() > 0 && r_is_wsp(s[0]) {
        lemma_r_classes(s[0]);
        lemma_r_ltrim(s.drop_first());
        assert(in_class(Class::Ows, s[0]));
        assert(run_len(Class::Ows, s) == 1 + run_len(Class::Ows, s.drop_first()));
        crate::field::termination::lemma_run_len_le(Class::Ows, s.drop_first());
        let k = run_len(Class::Ows, s.drop_first());
        assert(s.skip((1 + k) as int) =~= s.drop_first().skip(k as int));
    } else {
        if s.len() > 0 {
            lemma_r_classes(s[0]);
        }
        assert(s.skip(0) =~= s);
    }
}

/// Trimming trailing `OWS` is the spec's.
pub proof fn lemma_r_rtrim(s: Seq<u8>)
    ensures
        r_rtrim(s) == strip_trailing_ows(s),
    decreases s.len()
{
    if s.len() > 0 && r_is_wsp(s.last()) {
        lemma_r_classes(s.last());
        lemma_r_rtrim(s.drop_last());
    } else if s.len() > 0 {
        lemma_r_classes(s.last());
    }
}

/// `r_all_field_content` is the spec's `all_in` for `FieldContent`, and
/// `r_all_reason` the same for `reason-phrase` (the same octets).
pub proof fn lemma_r_all_content(s: Seq<u8>)
    ensures
        r_all_field_content(s) == all_in(s, Class::FieldContent),
        r_all_reason(s) == all_in(s, Class::FieldContent),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_r_classes(s[0]);
        lemma_r_all_content(s.drop_first());
    }
}

/// The transcription's `field-value` is the spec's.
pub proof fn lemma_r_field_value(v: Seq<u8>)
    ensures
        r_is_field_value(v) == is_field_value(v),
{
    lemma_r_all_content(v);
    if v.len() > 0 {
        lemma_r_classes(v[0]);
        lemma_r_classes(v.last());
    }
}

/// A line as a `header-field` against the spec's two steps for a field
/// line: its start, and its finishing.
pub proof fn lemma_r_header_field(line: Seq<u8>)
    ensures
        match r_header_field(line) {
            RField::Ok(f) => match parse_field_line_start(line) {
                Some(raw) => finish_field_line(raw) == Some(f),
                None => false,
            },
            RField::NameBad => parse_field_line_start(line) is None,
            RField::ValueBad => match parse_field_line_start(line) {
                Some(raw) => finish_field_line(raw) is None,
                None => false,
            },
        },
{
    lemma_r_token_len(line);
    let n = r_token_len(line);
    if n > 0 && line.len() > n && line[n as int] == 0x3A {
        let raw_value = line.skip((n + 1) as int);
        lemma_r_ltrim(raw_value);
        let lt = strip_leading_ows(raw_value);
        lemma_r_rtrim(lt);
        lemma_r_field_value(strip_trailing_ows(lt));
    }
}

/// A line that fails as a field value, followed by no obs-fold, makes the
/// spec's reading of the rest of the section not finish.
pub proof fn lemma_r_bad_pending(s: Seq<u8>, acc: Seq<FieldLine>, raw: FieldLine, count: nat)
    requires
        finish_field_line(raw) is None,
        !(s.len() > 0 && is_ows_octet(s[0])),
    ensures
        !(read_section(s, acc, Some(raw), count) is Done),
{
    super::termination::lemma_find_crlf_from(s, 0);
    match read_line(s) {
        LineRead::Line { line, rest: _ } => {
            if line.len() > 0 {
                assert(line[0] == s[0]);
            }
        }
        _ => {}
    }
}

/// The transcription's header section is the spec's reading of it, for any
/// state the spec was in before it.
pub proof fn lemma_r_section(s: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat)
    ensures
        match r_header_section(s, count) {
            RSection::Ok { fields, rest } => read_section(s, acc, pending, count) == match flush_pending(acc, pending) {
                Some(a) => SectionRead::Done { fields: a + fields, rest: rest },
                None => SectionRead::Invalid,
            },
            RSection::No => !(read_section(s, acc, pending, count) is Done),
            RSection::Out => true,
        },
    decreases s.len()
{
    lemma_r_first_crlf(s, 0);
    lemma_r_first_crlf_some(s, 0);
    match r_first_crlf(s, 0) {
        None => {}
        Some(n) => {
            if n > r_max_line() {
            } else if n == 0 {
                assert(s.take(0) =~= Seq::<u8>::empty());
            } else if count >= r_max_lines() {
            } else if r_is_wsp(s[0]) {
            } else {
                let line = s.take(n as int);
                let rest = s.skip((n + 2) as int);
                assert(line[0] == s[0]);
                lemma_r_classes(s[0]);
                lemma_r_header_field(line);
                match r_header_field(line) {
                    RField::NameBad => {}
                    RField::ValueBad => {
                        if !(rest.len() > 0 && r_is_wsp(rest[0])) {
                            match parse_field_line_start(line) {
                                Some(raw) => match flush_pending(acc, pending) {
                                    Some(acc2) => {
                                        if rest.len() > 0 {
                                            lemma_r_classes(rest[0]);
                                        }
                                        lemma_r_bad_pending(rest, acc2, raw, count + 1);
                                    }
                                    None => {}
                                },
                                None => {}
                            }
                        }
                    }
                    RField::Ok(f) => match parse_field_line_start(line) {
                        Some(raw) => match flush_pending(acc, pending) {
                            Some(acc2) => {
                                lemma_r_section(rest, acc2, Some(raw), count + 1);
                                if let RSection::Ok { fields, rest: after } = r_header_section(rest, count + 1) {
                                    assert(acc2.push(f) + fields =~= acc2 + (seq![f] + fields));
                                }
                            }
                            None => {}
                        },
                        None => {}
                    },
                }
            }
        }
    }
}

/// A status line as the transcription reads it is what the spec reads, or
/// is outside, or is rejected by both.
pub proof fn lemma_r_status_line(line: Seq<u8>)
    ensures
        match r_status_line(line) {
            RStatus::Ok(sl) => parse_status_line(line) == Some(sl),
            RStatus::No => parse_status_line(line) is None,
            RStatus::Out => true,
        },
{
    let n = line.len();
    if n >= 12 {
        lemma_r_classes(line[5]);
        lemma_r_classes(line[7]);
        lemma_r_classes(line[9]);
        lemma_r_classes(line[10]);
        lemma_r_classes(line[11]);
        if line[0] == 0x48 && line[1] == 0x54 && line[2] == 0x54 && line[3] == 0x50 && line[4] == 0x2F {
            assert(line.take(5) =~= lit_http_slash());
        }
        if n > 12 {
            lemma_r_all_content(line.skip(13));
        }
    }
}

/// The octet-wise rest of a quoted string is the spec's.
pub proof fn lemma_r_quoted_rest(v: Seq<u8>, value: Seq<u8>)
    ensures
        r_quoted_rest(v) == match quoted_body(v, value) {
            Some((_, rest)) => Some(rest),
            None => None,
        },
    decreases v.len()
{
    if v.len() > 0 && v[0] != 0x22 {
        lemma_r_classes(v[0]);
        if v[0] == 0x5C {
            if v.len() >= 2 && r_is_quoted_pair_octet(v[1]) {
                lemma_r_classes(v[1]);
                assert(v.drop_first().drop_first() =~= v.skip(2));
                lemma_r_quoted_rest(v.skip(2), value.push(v[1]));
            }
        } else if r_is_qdtext(v[0]) {
            lemma_r_quoted_rest(v.drop_first(), value.push(v[0]));
        }
    }
}

/// A `chunk-ext-val`'s rest is the spec's `parameter-value`'s.
pub proof fn lemma_r_ext_val_rest(v: Seq<u8>)
    ensures
        r_ext_val_rest(v) == match parse_parameter_value(v) {
            Some((_, rest)) => Some(rest),
            None => None,
        },
{
    lemma_r_token_len(v);
    if v.len() > 0 && v[0] == 0x22 {
        lemma_r_quoted_rest(v.drop_first(), seq![]);
    }
}

/// A string that is empty or does not start with OWS is its own
/// `strip_leading_ows`.
pub proof fn lemma_r_strip_id(x: Seq<u8>)
    requires
        x.len() == 0 || !r_is_wsp(x[0]),
    ensures
        strip_leading_ows(x) == x,
{
    if x.len() > 0 {
        lemma_r_classes(x[0]);
    }
    assert(x.skip(0) =~= x);
}

/// A string with no OWS octet has none at its start either.
pub proof fn lemma_r_no_wsp_tail(x: Seq<u8>)
    requires
        r_no_wsp(x),
    ensures
        x.len() == 0 || !r_is_wsp(x[0]),
        x.len() > 0 ==> r_no_wsp(x.drop_first()),
{
}

/// A token prefix of a string with a token start is not OWS.
pub proof fn lemma_r_tchar_not_wsp(c: u8)
    requires
        r_is_tchar(c),
    ensures
        !r_is_wsp(c),
{
}

/// The chunk extension of the transcription is the spec's: whatever it
/// accepts the spec accepts, and whatever it rejects the spec rejects when
/// there is no OWS at all in the string.
pub proof fn lemma_r_chunk_ext(s: Seq<u8>)
    ensures
        r_chunk_ext(s) ==> is_chunk_ext(s),
        (!r_chunk_ext(s) && r_no_wsp(s)) ==> !is_chunk_ext(s),
    decreases s.len()
{
    if s.len() > 0 {
        if s[0] == 0x3B {
            let after = s.drop_first();
            lemma_r_token_len(after);
            lemma_r_token_len_le(after);
            let n = r_token_len(after);
            // ";" is not OWS: the spec's `strip_leading_ows(s)` is `s`.
            lemma_r_strip_id(s);
            if n > 0 {
                // A name starts with a tchar, not OWS.
                lemma_r_classes(after[0]);
                lemma_r_strip_id(after);
                let c = after.skip(n as int);
                if c.len() > 0 && c[0] == 0x3D {
                    // "=" is not OWS.
                    lemma_r_strip_id(c);
                    let v = c.drop_first();
                    lemma_r_ext_val_rest(v);
                    lemma_r_ext_val_rest_len(v);
                    if r_no_wsp(s) {
                        assert(r_no_wsp(after));
                        assert(r_no_wsp(c)) by {
                            lemma_r_no_wsp_skip(after, n as int);
                        }
                        assert(r_no_wsp(v));
                        if v.len() > 0 {
                            lemma_r_no_wsp_tail(v);
                        }
                    }
                    match r_ext_val_rest(v) {
                        Some(rest) => {
                            // The value starts with `"` or a tchar, not OWS.
                            if v[0] != 0x22 {
                                lemma_r_classes(v[0]);
                            }
                            lemma_r_strip_id(v);
                            lemma_r_chunk_ext(rest);
                            if r_no_wsp(s) {
                                lemma_r_no_wsp_skip(v, 0);
                                lemma_r_no_wsp_after_value(v, rest);
                            }
                        }
                        None => {
                            if r_no_wsp(s) {
                                if v.len() > 0 {
                                    lemma_r_strip_id(v);
                                } else {
                                    assert(v.skip(0) =~= v);
                                }
                            }
                        }
                    }
                } else {
                    if c.len() > 0 {
                        // c[0] is not "=": whether it is OWS matters only
                        // for the second claim, where there is none.
                    }
                    lemma_r_chunk_ext(c);
                    if r_chunk_ext(c) {
                        // c is empty or starts with ";": no OWS first.
                        if c.len() > 0 {
                            lemma_r_strip_id(c);
                        }
                        assert(strip_leading_ows(c).len() == 0 || strip_leading_ows(c)[0] != 0x3D) by {
                            if c.len() > 0 {
                                lemma_r_strip_id(c);
                            } else {
                                assert(c.skip(0) =~= c);
                            }
                        }
                    }
                    if r_no_wsp(s) {
                        assert(r_no_wsp(after));
                        lemma_r_no_wsp_skip(after, n as int);
                        if c.len() > 0 {
                            lemma_r_no_wsp_tail(c);
                            lemma_r_strip_id(c);
                        } else {
                            assert(c.skip(0) =~= c);
                        }
                    }
                }
            } else {
                if r_no_wsp(s) {
                    assert(r_no_wsp(after));
                    if after.len() > 0 {
                        lemma_r_no_wsp_tail(after);
                        lemma_r_strip_id(after);
                    } else {
                        assert(after.skip(0) =~= after);
                    }
                }
            }
        } else {
            if r_no_wsp(s) {
                lemma_r_no_wsp_tail(s);
                lemma_r_strip_id(s);
            }
        }
    }
}

/// No OWS in a string means none in what follows a prefix of it.
pub proof fn lemma_r_no_wsp_skip(x: Seq<u8>, k: int)
    requires
        r_no_wsp(x),
        0 <= k <= x.len(),
    ensures
        r_no_wsp(x.skip(k)),
    decreases k
{
    if k > 0 {
        lemma_r_no_wsp_tail(x);
        lemma_r_no_wsp_skip(x.drop_first(), k - 1);
        assert(x.drop_first().skip(k - 1) =~= x.skip(k));
    } else {
        assert(x.skip(0) =~= x);
    }
}

/// What follows a value in a string with no OWS has no OWS.
pub proof fn lemma_r_no_wsp_after_value(v: Seq<u8>, rest: Seq<u8>)
    requires
        r_no_wsp(v),
        r_ext_val_rest(v) == Some(rest),
    ensures
        r_no_wsp(rest),
    decreases v.len()
{
    lemma_r_token_len_le(v);
    if v.len() > 0 && v[0] == 0x22 {
        lemma_r_no_wsp_quoted(v.drop_first(), rest);
        lemma_r_no_wsp_tail(v);
    } else if r_token_len(v) > 0 {
        lemma_r_no_wsp_skip(v, r_token_len(v) as int);
    }
}

/// What follows a quoted string in a string with no OWS has no OWS.
pub proof fn lemma_r_no_wsp_quoted(v: Seq<u8>, rest: Seq<u8>)
    requires
        r_no_wsp(v),
        r_quoted_rest(v) == Some(rest),
    ensures
        r_no_wsp(rest),
    decreases v.len()
{
    if v.len() > 0 && v[0] != 0x22 {
        lemma_r_no_wsp_tail(v);
        if v[0] == 0x5C {
            if v.len() >= 2 && r_is_quoted_pair_octet(v[1]) {
                lemma_r_no_wsp_skip(v, 2);
                lemma_r_no_wsp_quoted(v.skip(2), rest);
            }
        } else if r_is_qdtext(v[0]) {
            lemma_r_no_wsp_quoted(v.drop_first(), rest);
        }
    } else if v.len() > 0 {
        lemma_r_no_wsp_tail(v);
    }
}

/// The extension classes against the spec's `is_chunk_ext`.
pub proof fn lemma_r_ext_class(s: Seq<u8>)
    ensures
        match r_ext_class(s) {
            RExt::Ok => is_chunk_ext(s),
            RExt::No => !is_chunk_ext(s),
            RExt::Out => true,
        },
{
    lemma_r_chunk_ext(s);
}

/// The hex digits are the spec's: their run and their value.
pub proof fn lemma_r_hex(s: Seq<u8>)
    ensures
        r_hex_len(s) == hex_run_len(s),
        r_hex_value(s) == hex_value(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_r_classes(s[0]);
        lemma_r_classes(s.last());
        lemma_r_hex(s.drop_last());
        if r_is_hexdig(s[0]) {
            lemma_r_hex(s.drop_first());
        }
    }
}

/// The chunked decoding of the transcription is the spec's.
pub proof fn lemma_r_chunked(s: Seq<u8>, body: Seq<u8>)
    ensures
        match r_chunked(s, body.len()) {
            RChunked::Ok { body: b, rest } => read_chunks(s, body) == BodyRead::Done { body: body + b, rest: rest },
            RChunked::No => !(read_chunks(s, body) is Done),
            RChunked::Out => true,
        },
    decreases s.len()
{
    lemma_r_first_crlf(s, 0);
    lemma_r_first_crlf_some(s, 0);
    match r_first_crlf(s, 0) {
        None => {}
        Some(n) => {
            if n <= r_max_line() {
                let line = s.take(n as int);
                let rest = s.skip((n + 2) as int);
                lemma_r_hex(line);
                let k = r_hex_len(line);
                if k > 0 {
                    lemma_r_hex(line.take(k as int));
                    lemma_r_ext_class(line.skip(k as int));
                    match r_ext_class(line.skip(k as int)) {
                        RExt::No => {}
                        RExt::Out => {}
                        RExt::Ok => {
                            let size = r_hex_value(line.take(k as int));
                            if size == 0 {
                                lemma_r_section(rest, seq![], None, 0);
                                if let RSection::Ok { fields, rest: after } = r_header_section(rest, 0) {
                                    assert(seq![] + fields =~= fields);
                                    assert(body + Seq::<u8>::empty() =~= body);
                                }
                            } else if body.len() + size > r_max_body() {
                            } else if rest.len() < size + 2 {
                            } else if !(rest[size as int] == 0x0D && rest[(size + 1) as int] == 0x0A) {
                            } else {
                                let body2 = body + rest.take(size as int);
                                assert(body2.len() == body.len() + size);
                                lemma_r_chunked(rest.skip((size + 2) as int), body2);
                                if let RChunked::Ok { body: b, rest: after } = r_chunked(
                                    rest.skip((size + 2) as int),
                                    body.len() + size,
                                ) {
                                    assert(body2 + b =~= body + (rest.take(size as int) + b));
                                }
                            }
                        },
                    }
                }
            }
        }
    }
}

/// The case-insensitive comparison is the spec's `field_name_eq`.
pub proof fn lemma_r_ci_eq(a: Seq<u8>, b: Seq<u8>)
    ensures
        r_ci_eq(a, b) == field_name_eq(a, b),
    decreases a.len()
{
    let la = ascii_lowercase(a);
    let lb = ascii_lowercase(b);
    assert(la.len() == a.len());
    assert(lb.len() == b.len());
    if a.len() == b.len() && a.len() > 0 {
        assert(la.drop_first() =~= ascii_lowercase(a.drop_first()));
        assert(lb.drop_first() =~= ascii_lowercase(b.drop_first()));
        assert(la[0] == r_lower(a[0]));
        assert(lb[0] == r_lower(b[0]));
        lemma_r_ci_eq(a.drop_first(), b.drop_first());
        if la == lb {
            assert(la.drop_first() == lb.drop_first());
        }
        if r_lower(a[0]) == r_lower(b[0]) && field_name_eq(a.drop_first(), b.drop_first()) {
            assert(la =~= lb) by {
                assert(la.drop_first() == lb.drop_first());
                assert forall|i: int| 0 <= i < la.len() implies la[i] == lb[i] by {
                    if i == 0 {
                    } else {
                        assert(la.drop_first()[i - 1] == la[i]);
                        assert(lb.drop_first()[i - 1] == lb[i]);
                    }
                }
            }
        }
    } else if a.len() == 0 && b.len() == 0 {
        assert(la =~= lb);
    }
}

/// The values of the fields of a name are the spec's.
pub proof fn lemma_r_values_named(fields: Seq<FieldLine>, name: Seq<u8>)
    ensures
        r_values_named(fields, name) == field_values_named(fields, name),
    decreases fields.len()
{
    if fields.len() > 0 {
        lemma_r_ci_eq(fields[0].name, name);
        lemma_r_values_named(fields.drop_first(), name);
    }
}

/// The literal names are the spec's.
pub proof fn lemma_r_literals()
    ensures
        r_lit_transfer_encoding() == lit_transfer_encoding(),
        r_lit_content_length() == lit_content_length(),
        r_lit_chunked() == lit_chunked(),
{
}

/// The index form of the case-insensitive comparison.
pub proof fn lemma_r_ci_eq_index(a: Seq<u8>, b: Seq<u8>)
    requires
        r_ci_eq(a, b),
    ensures
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> r_lower(#[trigger] a[i]) == r_lower(b[i]),
    decreases a.len()
{
    if a.len() > 0 {
        lemma_r_ci_eq_index(a.drop_first(), b.drop_first());
        assert forall|i: int| 0 <= i < a.len() implies r_lower(#[trigger] a[i]) == r_lower(b[i]) by {
            if i > 0 {
                assert(a.drop_first()[i - 1] == a[i]);
                assert(b.drop_first()[i - 1] == b[i]);
            }
        }
    }
}

/// The digits are the spec's: all of them, and their value.
pub proof fn lemma_r_digits(s: Seq<u8>)
    ensures
        r_all_digit(s) == all_in(s, Class::Digit),
        r_is_digits(s) == is_digits(s),
        r_dec_value(s) == decimal_value(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_r_classes(s[0]);
        lemma_r_digits(s.drop_first());
        lemma_r_digits(s.drop_last());
    }
}

/// A string whose octets are letters has no OWS at either end, so
/// stripping leaves it as it is.
pub proof fn lemma_r_strip_ows_id(x: Seq<u8>)
    requires
        x.len() == 0 || (!r_is_wsp(x[0]) && !r_is_wsp(x.last())),
    ensures
        strip_ows(x) == x,
{
    lemma_r_strip_id(x);
    if x.len() > 0 {
        lemma_r_classes(x.last());
    }
}

/// A single `chunked` (in any letter case) is the one coding of the
/// spec's `Transfer-Encoding`.
pub proof fn lemma_r_te_chunked(v: Seq<u8>)
    requires
        r_ci_eq(v, r_lit_chunked()),
    ensures
        parse_transfer_encoding(combine(seq![v])) == Some(
            seq![TransferCoding { name: v, parameters: seq![] }],
        ),
{
    lemma_r_ci_eq_index(v, r_lit_chunked());
    assert(v.len() == 7);
    // Every octet is a letter.
    assert forall|i: int| 0 <= i < v.len() implies r_is_alpha(#[trigger] v[i]) by {
        assert(r_lower(v[i]) == r_lit_chunked()[i]);
    }
    assert(combine(seq![v]) == v);
    assert(crate::field::lemmas::no_comma_or_quote(v)) by {
        assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]) != 0x2C && v[i] != 0x22 by {
            assert(r_is_alpha(v[i]));
        }
    }
    crate::field::lemmas::lemma_scan_plain_run(v, Seq::<u8>::empty(), Seq::<u8>::empty(), Seq::<Seq<u8>>::empty());
    assert(v + Seq::<u8>::empty() =~= v);
    assert(Seq::<u8>::empty() + v =~= v);
    assert(!r_is_wsp(v[0]) && !r_is_wsp(v.last())) by {
        assert(r_is_alpha(v[0]));
        assert(r_is_alpha(v.last()));
    }
    lemma_r_strip_ows_id(v);
    assert(split_values(v) =~= seq![v]);
    assert(seq![v].drop_first() =~= Seq::<Seq<u8>>::empty());
    assert(drop_empty(Seq::<Seq<u8>>::empty()) =~= Seq::<Seq<u8>>::empty());
    assert(seq![v][0] == v);
    assert(drop_empty(seq![v]) =~= seq![v]);
    assert(list_elements(v) =~= seq![v]);
    // The coding: a run of tchars, no parameters.
    assert(all_in(v, Class::Tchar)) by {
        crate::field::lemmas::lemma_all_in_index(v, Class::Tchar);
        assert forall|i: int| 0 <= i < v.len() implies in_class(Class::Tchar, #[trigger] v[i]) by {
            assert(r_is_alpha(v[i]));
            lemma_r_classes(v[i]);
        }
    }
    crate::field::lemmas::lemma_all_in_run_len(v, Class::Tchar);
    assert(v.skip(7).len() == 0);
    assert(v.take(7) =~= v);
    assert(parse_transfer_codings(Seq::<Seq<u8>>::empty()) == Some(Seq::<TransferCoding>::empty()));
    assert(seq![v].drop_first() =~= Seq::<Seq<u8>>::empty());
    assert(seq![TransferCoding { name: v, parameters: seq![] }] + Seq::<TransferCoding>::empty() =~= seq![
        TransferCoding { name: v, parameters: seq![] },
    ]);
}

/// A single `Content-Length` of digits is the spec's.
pub proof fn lemma_r_cl_single(v: Seq<u8>)
    requires
        r_is_digits(v),
    ensures
        parse_content_length_lines(seq![v]) == Some(r_dec_value(v)),
{
    lemma_r_digits(v);
    assert(combine(seq![v]) == v);
    crate::field::lemmas::lemma_all_in_index(v, Class::Digit);
    assert(crate::field::lemmas::no_comma_or_quote(v)) by {
        assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]) != 0x2C && v[i] != 0x22 by {
            assert(in_class(Class::Digit, v[i]));
        }
    }
    crate::field::lemmas::lemma_scan_plain_run(v, Seq::<u8>::empty(), Seq::<u8>::empty(), Seq::<Seq<u8>>::empty());
    assert(v + Seq::<u8>::empty() =~= v);
    assert(Seq::<u8>::empty() + v =~= v);
    assert(!r_is_wsp(v[0]) && !r_is_wsp(v.last())) by {
        assert(in_class(Class::Digit, v[0]));
        assert(in_class(Class::Digit, v[v.len() - 1]));
    }
    lemma_r_strip_ows_id(v);
    assert(split_values(v) =~= seq![v]);
    assert(seq![v].drop_first() =~= Seq::<Seq<u8>>::empty());
    assert(seq![v][0] == v);
    reveal_with_fuel(all_equal, 2);
    assert(all_equal(Seq::<Seq<u8>>::empty(), v));
    assert(all_equal(seq![v], v));
    assert(parse_content_length(v) == Some(decimal_value(v)));
}

/// The body length of the transcription is the spec's.
pub proof fn lemma_r_body_length(sl: StatusLine, fields: Seq<FieldLine>, is_head: bool)
    ensures
        match r_body_length(sl, fields, is_head) {
            RLen::NoBody => body_length(Head { status_line: sl, fields: fields }, is_head) is NoBody,
            RLen::Length(n) => body_length(Head { status_line: sl, fields: fields }, is_head) == BodyLength::Length(n),
            RLen::Chunked => body_length(Head { status_line: sl, fields: fields }, is_head) is Chunked,
            RLen::Close => body_length(Head { status_line: sl, fields: fields }, is_head) is Close,
            RLen::Over => body_length(Head { status_line: sl, fields: fields }, is_head) is Invalid,
            RLen::Out => true,
        },
{
    lemma_r_literals();
    lemma_r_values_named(fields, r_lit_transfer_encoding());
    lemma_r_values_named(fields, r_lit_content_length());
    let te = r_values_named(fields, r_lit_transfer_encoding());
    let cl = r_values_named(fields, r_lit_content_length());
    if te.len() > 0 && cl.len() == 0 && !(sl.major == 1 && sl.minor == 0) && te.len() == 1
        && r_ci_eq(te[0], r_lit_chunked()) {
        lemma_r_te_chunked(te[0]);
        lemma_r_ci_eq(te[0], r_lit_chunked());
        assert(te =~= seq![te[0]]);
        assert(combine(te) == te[0]);
    }
    if te.len() == 0 && cl.len() == 1 && r_is_digits(cl[0]) {
        lemma_r_cl_single(cl[0]);
        assert(cl =~= seq![cl[0]]);
    }
}

/// **The theorem.** Wherever the transcription of RFC 7230 §3 decides, it
/// decides as the spec does: if it finds a response, `parse_response`
/// finds that response with the same octets after it; if it says there is
/// none (the octets are not a valid response, or not all here), then
/// `parse_response` does not finish one. `Out` is the inputs where the two
/// RFCs differ (see the header), for which nothing is claimed.
pub proof fn theorem_independent_framing(input: Seq<u8>, is_head: bool)
    ensures
        match r_parse(input, is_head) {
            RParse::Done { response, rest } => parse_response(input, is_head) == Parse::Done {
                response: response,
                rest: rest,
            },
            RParse::No => !(parse_response(input, is_head) is Done),
            RParse::Out => true,
        },
{
    lemma_r_first_crlf(input, 0);
    lemma_r_first_crlf_some(input, 0);
    match r_first_crlf(input, 0) {
        None => {}
        Some(n) => {
            if n <= r_max_line() {
                let line = input.take(n as int);
                let after_line = input.skip((n + 2) as int);
                lemma_r_status_line(line);
                match r_status_line(line) {
                    RStatus::No => {}
                    RStatus::Out => {}
                    RStatus::Ok(sl) => {
                        lemma_r_section(after_line, seq![], None, 0);
                        match r_header_section(after_line, 0) {
                            RSection::No => {}
                            RSection::Out => {}
                            RSection::Ok { fields, rest } => {
                                assert(Seq::<FieldLine>::empty() + fields =~= fields);
                                lemma_r_body_length(sl, fields, is_head);
                                match r_body_length(sl, fields, is_head) {
                                    RLen::Chunked => {
                                        assert(Seq::<u8>::empty().len() == 0);
                                        lemma_r_chunked(rest, Seq::<u8>::empty());
                                        if let RChunked::Ok { body, rest: after } = r_chunked(rest, 0) {
                                            assert(Seq::<u8>::empty() + body =~= body);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// A response with a `Content-Length`: both finish it, the same way.
pub proof fn example_agree_length()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F], false) is Done,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F], false) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F], false) is Done) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F], false) is Done) by (compute_only);
}

/// A chunked response with an extension and a trailer: both finish it, the same way.
pub proof fn example_agree_chunked()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x35, 0x3B, 0x61, 0x3D, 0x62, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x54, 0x3A, 0x20, 0x76, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x35, 0x3B, 0x61, 0x3D, 0x62, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x54, 0x3A, 0x20, 0x76, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x35, 0x3B, 0x61, 0x3D, 0x62, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x54, 0x3A, 0x20, 0x76, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x35, 0x3B, 0x61, 0x3D, 0x62, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x54, 0x3A, 0x20, 0x76, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done) by (compute_only);
}

/// A response to HEAD has no body: both finish it at the empty line.
pub proof fn example_agree_head()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A], true) is Done,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A], true) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A], true) is Done) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A], true) is Done) by (compute_only);
}

/// A body one octet short: neither finishes it.
pub proof fn example_agree_incomplete()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C], false) is No,
        !(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C], false) is Done),
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C], false) is No) by (compute_only);
    assert(!(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x68, 0x65, 0x6C, 0x6C], false) is Done)) by (compute_only);
}

/// Difference: `Transfer-Encoding` with `Content-Length`. RFC 7230 §3.3.3 lets the first override the second; RFC 9112 §6.3 makes it an error.
pub proof fn example_out_te_and_cl()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Invalid,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x35, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Invalid) by (compute_only);
}

/// Difference: an obs-fold. The two RFCs word its replacement differently.
pub proof fn example_out_obs_fold()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x58, 0x3A, 0x20, 0x61, 0x0D, 0x0A, 0x20, 0x62, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x58, 0x3A, 0x20, 0x61, 0x0D, 0x0A, 0x20, 0x62, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x58, 0x3A, 0x20, 0x61, 0x0D, 0x0A, 0x20, 0x62, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x58, 0x3A, 0x20, 0x61, 0x0D, 0x0A, 0x20, 0x62, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done) by (compute_only);
}

/// Difference: no SP after the status code. RFC 7230 §3.1.2 requires it; the spec accepts it (modelling choice).
pub proof fn example_out_missing_sp()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x33, 0x30, 0x31, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x33, 0x30, 0x31, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x33, 0x30, 0x31, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x33, 0x30, 0x31, 0x0D, 0x0A, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done) by (compute_only);
}

/// Difference: whitespace in a chunk extension. RFC 9112 §7.1.1 allows `BWS`; RFC 7230 §4.1.1 does not.
pub proof fn example_out_chunk_bws()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x20, 0x3B, 0x20, 0x61, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x20, 0x3B, 0x20, 0x61, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x20, 0x3B, 0x20, 0x61, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x20, 0x3B, 0x20, 0x61, 0x0D, 0x0A, 0x0D, 0x0A], false) is Done) by (compute_only);
}

/// Difference: `Transfer-Encoding` in an HTTP/1.0 response. RFC 9112 §6.1 makes it an error.
pub proof fn example_out_http10_te()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x30, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x30, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Invalid,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x30, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x30, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Invalid) by (compute_only);
}

/// Difference: codings other than a lone `chunked`. The spec calls them unsupported; RFC 7230 would decode or read to close.
pub proof fn example_out_other_coding()
    ensures
        r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x67, 0x7A, 0x69, 0x70, 0x2C, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out,
        parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x67, 0x7A, 0x69, 0x70, 0x2C, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Unsupported,
{
    assert(r_parse(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x67, 0x7A, 0x69, 0x70, 0x2C, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Out) by (compute_only);
    assert(parse_response(seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x30, 0x20, 0x4F, 0x4B, 0x0D, 0x0A, 0x54, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x45, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67, 0x3A, 0x20, 0x67, 0x7A, 0x69, 0x70, 0x2C, 0x20, 0x63, 0x68, 0x75, 0x6E, 0x6B, 0x65, 0x64, 0x0D, 0x0A, 0x0D, 0x0A, 0x30, 0x0D, 0x0A, 0x0D, 0x0A], false) is Unsupported) by (compute_only);
}

/// The other half of the theorem: a response the spec finishes is one the
/// transcription finishes the same way, unless the input is one where the
/// two RFCs differ.
pub proof fn corollary_independent_framing(input: Seq<u8>, is_head: bool)
    ensures
        match parse_response(input, is_head) {
            Parse::Done { response, rest } => r_parse(input, is_head) is Out || r_parse(input, is_head) == RParse::Done {
                response: response,
                rest: rest,
            },
            _ => true,
        },
{
    theorem_independent_framing(input, is_head);
}

} // verus!
