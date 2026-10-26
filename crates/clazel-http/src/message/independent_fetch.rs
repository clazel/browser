//! An independent transcription of what the WHATWG Fetch Standard says
//! about the length of a response body, from a different standard than
//! [`super::spec`] (docs/VERIFICATION.md, "Trust without reviewers", item
//! 2), beside [`super::independent`]'s RFC 7230 transcription. The
//! transcription section below uses nothing from `spec.rs` but the data
//! carriers `FieldLine`, `Head`'s fields and `StatusLine`; the statement
//! and proof after it use the spec.
//!
//! Source (pinned): Fetch Standard, Living Standard, last updated 19 October
//! 2026, commit `59afe349913d56898c947576216f1c2579308be7`,
//! <https://fetch.spec.whatwg.org/>: "Headers" (header list "contains",
//! "get", "get, decode, and split";
//! <https://fetch.spec.whatwg.org/#concept-header-list-get>), "`Content-Length`
//! header" ("extract a length";
//! <https://fetch.spec.whatwg.org/#concept-header-extract-length>), "HTTP-network
//! fetch"
//! (<https://fetch.spec.whatwg.org/#concept-http-network-fetch>). Infra for
//! "byte-lowercase", "byte-case-insensitive" and "ASCII digit".
//!
//! # What Fetch says about where a body ends, and what it does not
//!
//! **Fetch does not define HTTP/1.1 framing.** Its "HTTP-network fetch"
//! makes the request "following the relevant requirements from HTTP"
//! (the first caveat of its "making an HTTP request" step), and its note says "the exact layering
//! between Fetch and HTTP still needs to be sorted through". After that it
//! only reacts to what the HTTP layer reports: "if one or more bytes have
//! been transmitted from response's message body" it appends them to a
//! buffer (after "handle content codings"); "if the bytes transmission for
//! response's message body is done normally" it closes the stream; if the
//! fetch is aborted it errors the stream with a `TypeError` and closes the
//! connection. When a message body is *done normally* (its length from
//! `Content-Length`, the chunked coding, or the close), what a body
//! truncated by a close is, and what a network error is, are all HTTP's
//! (RFC 9112 §6.3, §7.1), not Fetch's. The word "chunked" does not
//! occur in Fetch, and "Transfer-Encoding" only in its list of forbidden
//! request-header names. So there is **no second text for** the chunked
//! coding, the read-until-close rule, or the truncation rule, and this
//! module invents none: those parts of `spec.rs` have no Fetch counterpart
//! and rest on the RFC 7230 transcription alone. The loop that moves
//! transmitted bytes into the stream is not transcribed either, because it
//! decides nothing about length: the body Fetch hands on is the bytes HTTP
//! transmitted (content codings aside, which this client does not decode).
//!
//! What Fetch does define is how to read the one framing field a web client
//! sees, `Content-Length`: [`f_extract_a_length`] on top of the
//! header list functions of "Headers". That is what is transcribed here.
//!
//! # What is proven
//!
//! [`fetch_agrees`] is the statement; [`theorem_fetch_extract_length`]
//! proves it for **every** field section and both values of "the request
//! was HEAD", for a response whose framing reaches `Content-Length`
//! (not a HEAD response, 1xx, 204 or 304, and no `Transfer-Encoding`):
//!
//! - Fetch's "extract a length" gives a number `n` exactly when the spec's
//!   `Content-Length` is valid with value `n` (they read the same digits,
//!   from the same combined field value, and require the same repeated
//!   value), and then `body_length` is `Length(n)`, or `Invalid` only past
//!   the body limit (a limit is the implementation's choice, not Fetch's);
//! - Fetch's "extract a length" gives *failure* only when `body_length` is
//!   `Invalid` (differing values);
//! - with no `Content-Length` line both say there is no length (Fetch
//!   null; `body_length` `Close`);
//! - Fetch says *null* for a present but non-numeric `Content-Length`
//!   (empty, or a non-digit), where `body_length` is `Invalid`: the
//!   difference below.
//!
//! The supporting lemmas are part by part: [`lemma_f_values_named`] (Fetch's
//! "get" collects the lines the spec's `field_values_named` does),
//! [`lemma_f_get_is_combine`] (", " is the combined value, §5.3),
//! [`lemma_f_decimal`] (the same number) and
//! [`lemma_f_extract_values`] (Fetch's loop over the split values).
//!
//! # Where Fetch and RFC 9112 differ
//!
//! - **An invalid `Content-Length` is null, not an error.** Fetch's step 5
//!   returns null for an empty or non-digit candidate, which its callers
//!   treat as no `Content-Length`; RFC 9112 §6.3 item 5 makes the framing
//!   invalid. The theorem states it (`Null` with a `Content-Length` line
//!   gives `Invalid`), so it is exhibited, not hidden. Fetch's model is a
//!   web client that must carry on; ours rejects.
//! - **Repeated values are compared as strings.** Fetch step 3.2.1 returns
//!   failure for a value that "is not candidateValue", a string comparison,
//!   so `42, 042` is a failure, as it is in the spec ("the same digits"). The
//!   RFC's "same decimal value" would allow it; this is not a difference
//!   between Fetch and the spec, but between Fetch and the RFC wording
//!   (`independent.rs` lists it as `Out` for RFC 7230).
//! - **Empty list members.** Fetch's "get, decode, and split" keeps empty
//!   members, so `42,` has the members `42` and the empty string and is a
//!   failure; the spec's `split_values` also keeps them
//!   (`field/independent.rs`, `lemma_get_decode_split_equals_split_values`).
//! - **No size limit.** Fetch's number is unbounded; the spec rejects a
//!   length over `max_body` (stated in the theorem).
//! - **Transfer-Encoding, status and method.** Fetch's "extract a length"
//!   looks at `Content-Length` alone. RFC 9112 §6.3 items 1 to 4 decide
//!   first (HEAD, 1xx, 204, 304; `Transfer-Encoding` overrides or conflicts
//!   with `Content-Length`). The theorem's precondition is exactly those
//!   items not applying; outside it nothing is claimed (`Out`), and Fetch
//!   has no text to compare with.
//!
//! # Modelling choices
//!
//! - A header list is the section's `Seq<FieldLine>` (Fetch's headers are a
//!   list of name-value pairs, in order). Fetch's header values are
//!   already isomorphic-decoded byte sequences, the same as the spec's
//!   octets.
//! - "Byte-lowercase" and "byte-case-insensitive match" are Infra's: ASCII
//!   upper case letters become lower case.
//! - Iteration ("for each") is a recursive function over the list with the
//!   loop variable (`candidateValue`) passed along; "return failure"
//!   returns [`Candidate::Failed`] out of the whole recursion.
//! - Fetch's "interpreted as decimal number" is read left to right
//!   ([`f_interpret_decimal`]).
//! - If the split list were empty, `candidateValue` would still be null at
//!   step 5, which the text does not cover; it is modelled as null. It
//!   cannot happen: "get, decode, and split" always gives a member.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Transcription: Fetch "Headers" and "Content-Length header" (uses nothing from spec.rs but the
// carrier FieldLine).
// ===========================================================================

/// Infra "byte-lowercase" of one byte: "to byte-lowercase a byte sequence,
/// replace all bytes in the range 0x41 (A) to 0x5A (Z), inclusive, with the
/// byte that is 0x20 greater".
pub open spec fn f_byte_lowercase_byte(b: u8) -> u8 {
    if 0x41 <= b && b <= 0x5A { (b + 0x20) as u8 } else { b }
}

/// Infra "byte-lowercase" of a byte sequence.
pub open spec fn f_byte_lowercase(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![f_byte_lowercase_byte(s[0])] + f_byte_lowercase(s.drop_first())
    }
}

/// Infra "byte-case-insensitive match": "two byte sequences A and B are a
/// byte-case-insensitive match if the byte-lowercase of A is the
/// byte-lowercase of B".
pub open spec fn f_byte_case_insensitive_match(a: Seq<u8>, b: Seq<u8>) -> bool {
    f_byte_lowercase(a) == f_byte_lowercase(b)
}

/// The header name `Content-Length`.
pub open spec fn f_content_length_name() -> Seq<u8> {
    seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68]
}

/// Header list "contains" (<https://fetch.spec.whatwg.org/#header-list-contains>):
/// "a header list list contains a header name name if list contains a
/// header whose name is a byte-case-insensitive match for name".
pub open spec fn f_header_list_contains(list: Seq<FieldLine>, name: Seq<u8>) -> bool {
    exists|i: int| 0 <= i < list.len() && f_byte_case_insensitive_match(#[trigger] list[i].name, name)
}

/// The values of all headers in `list` whose name is a
/// byte-case-insensitive match for `name`, in order (the list that step 2
/// of "get" joins).
pub open spec fn f_matching_values(list: Seq<FieldLine>, name: Seq<u8>) -> Seq<Seq<u8>>
    decreases list.len()
{
    if list.len() == 0 {
        seq![]
    } else if f_byte_case_insensitive_match(list[0].name, name) {
        seq![list[0].value] + f_matching_values(list.drop_first(), name)
    } else {
        f_matching_values(list.drop_first(), name)
    }
}

/// The `values` "separated from each other by 0x2C 0x20".
pub open spec fn f_separated(values: Seq<Seq<u8>>) -> Seq<u8>
    decreases values.len()
{
    if values.len() == 0 {
        seq![]
    } else if values.len() == 1 {
        values[0]
    } else {
        values[0] + seq![0x2Cu8, 0x20u8] + f_separated(values.drop_first())
    }
}

/// Header list "get" (<https://fetch.spec.whatwg.org/#concept-header-list-get>).
pub open spec fn f_header_list_get(list: Seq<FieldLine>, name: Seq<u8>) -> Option<Seq<u8>> {
    // 1. "If list does not contain name, then return null."
    if !f_header_list_contains(list, name) {
        None
    } else {
        // 2. "Return the values of all headers in list whose name is a
        //    byte-case-insensitive match for name, separated from each
        //    other by 0x2C 0x20, in order."
        Some(f_separated(f_matching_values(list, name)))
    }
}

/// Header list "get, decode, and split"
/// (<https://fetch.spec.whatwg.org/#concept-header-list-get-decode-split>).
pub open spec fn f_header_list_get_decode_split(list: Seq<FieldLine>, name: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    // 1. "Let value be the result of getting name from list."
    match f_header_list_get(list, name) {
        // 2. "If value is null, then return null."
        None => None,
        // 3. "Return the result of getting, decoding, and splitting value."
        Some(value) => Some(crate::field::independent::f_get_decode_split(value)),
    }
}

/// An ASCII digit: "a code point in the range U+0030 (0) to U+0039 (9),
/// inclusive" (Infra).
pub open spec fn f_is_ascii_digit(b: u8) -> bool {
    0x30 <= b && b <= 0x39
}

/// Every code point of `s` is an ASCII digit.
pub open spec fn f_all_ascii_digits(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (f_is_ascii_digit(s[0]) && f_all_ascii_digits(s.drop_first()))
}

/// `s` "interpreted as decimal number", read left to right from
/// `accumulated` (the number of the digits already read).
pub open spec fn f_interpret_decimal(s: Seq<u8>, accumulated: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        accumulated
    } else {
        f_interpret_decimal(s.drop_first(), accumulated * 10 + ((s[0] - 0x30) as nat))
    }
}

/// The result of "extract a length": null, failure, or a number.
pub enum ExtractedLength {
    /// "return null": there is no usable length.
    Null,
    /// "return failure": the values differ.
    Failure,
    /// A number.
    Length(nat),
}

/// What step 3's loop leaves: failure was returned, or the value of
/// `candidateValue` (null or a string).
pub enum Candidate {
    /// Step 4.2 returned failure.
    Failed,
    /// The loop ended with this `candidateValue`.
    Is(Option<Seq<u8>>),
}

/// Step 4: "For each value of values", from the front of `values`, with
/// `candidate` as `candidateValue`.
pub open spec fn f_for_each_value(values: Seq<Seq<u8>>, candidate: Option<Seq<u8>>) -> Candidate
    decreases values.len()
{
    if values.len() == 0 {
        Candidate::Is(candidate)
    } else {
        let value = values[0];
        match candidate {
            // 4.1 "If candidateValue is null, then set candidateValue to value."
            None => f_for_each_value(values.drop_first(), Some(value)),
            // 4.2 "Otherwise, if value is not candidateValue, return failure."
            Some(c) => if value != c {
                Candidate::Failed
            } else {
                f_for_each_value(values.drop_first(), candidate)
            },
        }
    }
}

/// Steps 3 to 6 of "extract a length" once the list `values` is known.
pub open spec fn f_extract_a_length_of(values: Seq<Seq<u8>>) -> ExtractedLength {
    // 3. "Let candidateValue be null." 4. the loop.
    match f_for_each_value(values, None) {
        Candidate::Failed => ExtractedLength::Failure,
        Candidate::Is(candidate_value) => match candidate_value {
            // (Not reachable: see the modelling choices.)
            None => ExtractedLength::Null,
            Some(c) => if c.len() == 0 || !f_all_ascii_digits(c) {
                // 5. "If candidateValue is the empty string or has a code
                //    point that is not an ASCII digit, then return null."
                ExtractedLength::Null
            } else {
                // 6. "Return candidateValue, interpreted as decimal number."
                ExtractedLength::Length(f_interpret_decimal(c, 0))
            },
        },
    }
}

/// "Extract a length" from a header list
/// (<https://fetch.spec.whatwg.org/#concept-header-extract-length>).
pub open spec fn f_extract_a_length(headers: Seq<FieldLine>) -> ExtractedLength {
    // 1. "Let values be the result of getting, decoding, and splitting
    //    `Content-Length` from headers."
    match f_header_list_get_decode_split(headers, f_content_length_name()) {
        // 2. "If values is null, then return null."
        None => ExtractedLength::Null,
        Some(values) => f_extract_a_length_of(values),
    }
}

// ===========================================================================
// The statement (uses spec.rs).
// ===========================================================================

/// Fetch's "extract a length" and the spec's `body_length` agree on `head`
/// for a request that was `HEAD` exactly when `request_is_head`, in the
/// cases the module header lists (RFC 9112 §6.3 items 1 to 4 do not
/// apply).
pub open spec fn fetch_agrees(head: Head, request_is_head: bool) -> bool {
    let status = head.status_line.status;
    let cl = field_values_named(head.fields, lit_content_length());
    let te = field_values_named(head.fields, lit_transfer_encoding());
    let reaches = !(request_is_head || (100 <= status && status <= 199) || status == 204 || status == 304)
        && te.len() == 0;
    reaches ==> match f_extract_a_length(head.fields) {
        ExtractedLength::Length(n) => body_length(head, request_is_head)
            == (if n > max_body() { BodyLength::Invalid } else { BodyLength::Length(n) }),
        ExtractedLength::Failure => body_length(head, request_is_head) == BodyLength::Invalid,
        ExtractedLength::Null => body_length(head, request_is_head)
            == (if cl.len() == 0 { BodyLength::Close } else { BodyLength::Invalid }),
    }
}

// ===========================================================================
// Proofs: what the transcription and the spec agree on (uses spec.rs).
// ===========================================================================

/// Infra's byte-lowercase is `ascii_lowercase`.
pub proof fn lemma_f_lowercase(s: Seq<u8>)
    ensures
        f_byte_lowercase(s) == ascii_lowercase(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_f_lowercase(s.drop_first());
        assert(ascii_lowercase(s) =~= seq![f_byte_lowercase_byte(s[0])] + ascii_lowercase(s.drop_first()));
    } else {
        assert(ascii_lowercase(s) =~= Seq::<u8>::empty());
    }
}

/// `Content-Length` is `content-length` for both matches.
pub proof fn lemma_f_name_match(a: Seq<u8>)
    ensures
        f_byte_case_insensitive_match(a, f_content_length_name()) == field_name_eq(a, lit_content_length()),
{
    lemma_f_lowercase(a);
    lemma_f_lowercase(f_content_length_name());
    lemma_f_lowercase(lit_content_length());
    assert(f_byte_lowercase(f_content_length_name()) == lit_content_length()) by (compute_only);
    assert(f_byte_lowercase(lit_content_length()) == lit_content_length()) by (compute_only);
}

/// Fetch's "get" collects the lines the spec's `field_values_named` does,
/// and "contains" is "there is one".
pub proof fn lemma_f_values_named(list: Seq<FieldLine>)
    ensures
        f_matching_values(list, f_content_length_name()) == field_values_named(list, lit_content_length()),
        f_header_list_contains(list, f_content_length_name()) == (field_values_named(list, lit_content_length()).len() > 0),
    decreases list.len(),
{
    if list.len() > 0 {
        lemma_f_values_named(list.drop_first());
        lemma_f_name_match(list[0].name);
        let tail = list.drop_first();
        if f_byte_case_insensitive_match(list[0].name, f_content_length_name()) {
            assert(f_header_list_contains(list, f_content_length_name())) by {
                assert(f_byte_case_insensitive_match(list[0].name, f_content_length_name()));
            }
        } else {
            if f_header_list_contains(list, f_content_length_name()) {
                let i = choose|i: int| 0 <= i < list.len() && f_byte_case_insensitive_match(#[trigger] list[i].name, f_content_length_name());
                assert(i > 0);
                assert(tail[i - 1] == list[i]);
                assert(f_header_list_contains(tail, f_content_length_name()));
            }
            if f_header_list_contains(tail, f_content_length_name()) {
                let j = choose|j: int| 0 <= j < tail.len() && f_byte_case_insensitive_match(#[trigger] tail[j].name, f_content_length_name());
                assert(list[j + 1] == tail[j]);
            }
        }
    } else {
        assert(!f_header_list_contains(list, f_content_length_name()));
    }
}

/// ", " between the values is the spec's combined value (§5.3).
pub proof fn lemma_f_get_is_combine(values: Seq<Seq<u8>>)
    ensures
        f_separated(values) == combine(values),
    decreases values.len(),
{
    if values.len() > 1 {
        lemma_f_get_is_combine(values.drop_first());
    }
}

/// Fetch's "ASCII digit" is the spec's `DIGIT`.
pub proof fn lemma_f_digits(s: Seq<u8>)
    ensures
        f_all_ascii_digits(s) == all_in(s, Class::Digit),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_f_digits(s.drop_first());
    }
}

/// Appending a digit multiplies by ten and adds it, whatever was
/// accumulated.
proof fn lemma_f_decimal_push(s: Seq<u8>, c: u8, accumulated: nat)
    requires
        f_all_ascii_digits(s),
        f_is_ascii_digit(c),
    ensures
        f_interpret_decimal(s.push(c), accumulated) == f_interpret_decimal(s, accumulated) * 10 + ((c - 0x30) as nat),
    decreases s.len(),
{
    let t = s.push(c);
    assert(t.len() > 0);
    if s.len() > 0 {
        let d = ((s[0] - 0x30) as nat);
        assert(t[0] == s[0]);
        assert(f_is_ascii_digit(s[0]) && f_all_ascii_digits(s.drop_first()));
        lemma_f_decimal_push(s.drop_first(), c, accumulated * 10 + d);
        assert(t.drop_first() =~= s.drop_first().push(c));
        assert(f_interpret_decimal(t, accumulated) == f_interpret_decimal(t.drop_first(), accumulated * 10 + d));
        assert(f_interpret_decimal(s, accumulated) == f_interpret_decimal(s.drop_first(), accumulated * 10 + d));
    } else {
        assert(t[0] == c);
        assert(t.drop_first() =~= Seq::<u8>::empty());
        assert(f_interpret_decimal(t, accumulated) == f_interpret_decimal(Seq::<u8>::empty(), accumulated * 10 + ((c - 0x30) as nat)));
    }
}

/// Reading the digits left to right is the spec's `decimal_value`.
pub proof fn lemma_f_decimal(s: Seq<u8>)
    requires
        all_in(s, Class::Digit),
    ensures
        f_interpret_decimal(s, 0) == decimal_value(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let dl = s.drop_last();
        assert(all_in(dl, Class::Digit)) by {
            lemma_all_in_drop_last(s);
        }
        lemma_f_decimal(dl);
        assert(s =~= dl.push(s.last()));
        lemma_f_digits(dl);
        lemma_f_digits(s);
        lemma_all_in_last(s);
        assert(f_is_ascii_digit(s.last()));
        lemma_f_decimal_push(dl, s.last(), 0);
        assert(f_interpret_decimal(s, 0) == f_interpret_decimal(dl.push(s.last()), 0));
    }
}

/// The last member of an `all_in` string is in the class.
proof fn lemma_all_in_last(s: Seq<u8>)
    requires
        s.len() > 0,
        all_in(s, Class::Digit),
    ensures
        in_class(Class::Digit, s.last()),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_all_in_last(s.drop_first());
        assert(s.drop_first().last() == s.last());
    }
}

/// If every member of a string sequence is a digit string, so is each
/// prefix: `drop_last` keeps `all_in`.
proof fn lemma_all_in_drop_last(s: Seq<u8>)
    requires
        s.len() > 0,
        all_in(s, Class::Digit),
    ensures
        all_in(s.drop_last(), Class::Digit),
    decreases s.len(),
{
    if s.len() > 1 {
        lemma_all_in_drop_last(s.drop_first());
        assert(s.drop_last().drop_first() =~= s.drop_first().drop_last());
        assert(in_class(Class::Digit, s.drop_last()[0]));
    }
}

/// Step 4's loop against `all_equal`.
pub proof fn lemma_f_for_each(values: Seq<Seq<u8>>, c: Seq<u8>)
    ensures
        f_for_each_value(values, Some(c)) == (if all_equal(values, c) { Candidate::Is(Some(c)) } else { Candidate::Failed }),
    decreases values.len(),
{
    if values.len() > 0 && values[0] == c {
        lemma_f_for_each(values.drop_first(), c);
    }
}

/// Fetch's loop over the split values against the spec's reading of the
/// same list (`parse_content_length`): a number exactly when the spec has
/// one (the same one); failure only for differing members; null when the
/// spec says invalid for another reason.
pub proof fn lemma_f_extract_values(values: Seq<Seq<u8>>)
    ensures
        ({
            let valid = values.len() > 0 && is_digits(values[0]) && all_equal(values, values[0]);
            &&& valid ==> f_extract_a_length_of(values) == ExtractedLength::Length(decimal_value(values[0]))
            &&& (f_extract_a_length_of(values) is Length) ==> valid
            &&& (f_extract_a_length_of(values) is Failure) ==> (values.len() > 0 && !all_equal(values, values[0]))
            &&& (f_extract_a_length_of(values) is Null) ==> !valid
        }),
{
    if values.len() > 0 {
        let c = values[0];
        assert(f_for_each_value(values, None) == f_for_each_value(values.drop_first(), Some(c)));
        lemma_f_for_each(values.drop_first(), c);
        assert(all_equal(values, c) == all_equal(values.drop_first(), c));
        lemma_f_digits(c);
        if is_digits(c) && all_equal(values, c) {
            lemma_f_decimal(c);
        }
    }
}

/// The statement, proven: [`fetch_agrees`] for every head.
pub proof fn theorem_fetch_extract_length(head: Head, request_is_head: bool)
    ensures
        fetch_agrees(head, request_is_head),
{
    let cl = field_values_named(head.fields, lit_content_length());
    lemma_f_values_named(head.fields);
    if cl.len() > 0 {
        lemma_f_get_is_combine(cl);
        let combined = combine(cl);
        crate::field::independent::lemma_get_decode_split_equals_split_values(combined);
        let m = split_values(combined);
        lemma_f_extract_values(m);
        assert(f_header_list_get(head.fields, f_content_length_name()) == Some(combined));
        assert(parse_content_length_lines(cl) == parse_content_length(combined));
    } else {
        assert(f_header_list_get(head.fields, f_content_length_name()) is None);
    }
}


/// One case per result of steps 3 to 6 of "extract a length", so the
/// statement is not vacuous: a number, repeated equal values, differing
/// values (failure), `042` against `42` (failure: a string comparison), a
/// non-digit (null) and an empty value (null).
pub proof fn example_extract_a_length()
    ensures
        f_extract_a_length_of(seq![seq![0x34u8, 0x32]]) == ExtractedLength::Length(42),
        f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x34u8, 0x32]]) == ExtractedLength::Length(42),
        f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x34u8, 0x33]]) == ExtractedLength::Failure,
        f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x30u8, 0x34, 0x32]]) == ExtractedLength::Failure,
        f_extract_a_length_of(seq![seq![0x34u8, 0x78]]) == ExtractedLength::Null,
        f_extract_a_length_of(seq![seq![]]) == ExtractedLength::Null,
{
    assert(f_extract_a_length_of(seq![seq![0x34u8, 0x32]]) == ExtractedLength::Length(42)) by (compute_only);
    assert(f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x34u8, 0x32]]) == ExtractedLength::Length(42)) by (compute_only);
    assert(f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x34u8, 0x33]]) == ExtractedLength::Failure) by (compute_only);
    assert(f_extract_a_length_of(seq![seq![0x34u8, 0x32], seq![0x30u8, 0x34, 0x32]]) == ExtractedLength::Failure) by (compute_only);
    assert(f_extract_a_length_of(seq![seq![0x34u8, 0x78]]) == ExtractedLength::Null) by (compute_only);
    assert(f_extract_a_length_of(seq![seq![]]) == ExtractedLength::Null) by (compute_only);
}

} // verus!
