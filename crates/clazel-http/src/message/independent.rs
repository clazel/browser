//! PLACEHOLDER HEADER (rewritten when the module is complete).

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

} // verus!
