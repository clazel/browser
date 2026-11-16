//! Executable-style specification of the form encodings and the form
//! submission algorithm (Phase 6 item 6.14): URL's
//! `application/x-www-form-urlencoded` serializer, HTML's "convert to a
//! list of name-value pairs", the `text/plain` and `multipart/form-data`
//! encoding algorithms, "picking an encoding for the form", and the form
//! submission algorithm's steps that turn a form, a submitter and an entry
//! list into a navigation request. Nothing here runs; it defines what
//! "correct" means. Every function cites its algorithm, and each `// N.`
//! comment is the step number in it.
//!
//! Sources (pinned; a review is against exactly these texts):
//! - HTML Standard, Living Standard, commit
//!   `0793d3d8544eee95a862e6637130a8106c3d11ca` (14 November 2026), the same
//!   commit as item 6.13's `src/spec.rs`. Section numbers are those of the
//!   multipage build: §4.10.22.3 "Form submission algorithm" (steps 1 to
//!   the end, "plan to navigate", "mutate action URL", "submit as entity
//!   body", "get action URL", "mail with headers", "mail as body"),
//!   §4.10.22.5 "Selecting a form submission encoding", §4.10.22.6
//!   "Converting an entry list to a list of name-value pairs", §4.10.22.7
//!   "URL-encoded form data", §4.10.22.8 "Multipart form data", §4.10.22.9
//!   "Plain text form data", §4.10.19.6 "Form submission attributes" (the
//!   `action`, `method`, `enctype`, `target`, `formaction`, `formmethod`,
//!   `formenctype` and `formtarget` attributes), §4.2.3 "The base element"
//!   ("get an element's target"), §4.6.5 "Following hyperlinks" ("cannot
//!   navigate", "get an element's noopener"), §7.3.1.7 "Navigable target
//!   names" ("valid navigable target name or keyword", "the rules for
//!   choosing a navigable").
//! - URL Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026; the commit
//!   `clazel-url` and `clazel-percent` pin): §5 "application/x-www-form-urlencoded",
//!   §5.2 "application/x-www-form-urlencoded serializing" (the serializer,
//!   steps 1 to 4), §1.3 "percent-encode after encoding" (steps 1 to 8,
//!   transcribed by `clazel-percent` for UTF-8 and here for the single-byte
//!   encodings), "the application/x-www-form-urlencoded percent-encode set".
//! - Encoding Standard, commit `dd7943441a861a60a073bffa55869d91cb6a8288`
//!   (the commit `clazel-encoding` pins): "get an output encoding" (§4.2),
//!   "encode" and "UTF-8 encode" (§6), "get an encoder" and the single-byte
//!   encoder (§4.1, §9).
//! - RFC 7578 §4.1 and §4.2 (`multipart/form-data` parts), RFC 2046 §5.1.1
//!   (the boundary's grammar).
//! - Infra "split a string on ASCII whitespace", "ASCII case-insensitive".
//!
//! Modelling choices (each a deliberate difference in form, never in
//! meaning, or a stated restriction):
//! - **Strings are code points as `u32`** (`Seq<u32>`), byte strings `Seq<u8>`,
//!   as in the rest of the crate. A "scalar value string" is one whose every
//!   element is a scalar value; [`to_scalar`] is the conversion ("convert to
//!   a scalar value string": replace each surrogate with U+FFFD), here also
//!   applied to code points above U+10FFFF, which the arena's `u32` can hold
//!   but Infra's "code point" cannot. Item 6.13's "create an entry" took
//!   its steps 1 and 2 (convert the name and the value to scalar value
//!   strings) as already satisfied; [`scalar_entries`] makes them explicit
//!   at the start of the submission, so no precondition about scalar values
//!   reaches the caller. The attribute values that become the URL are
//!   converted the same way ("`action` getter steps" convert too).
//! - **Encodings are the Encoding Standard's [`Encoding`]**. The encoders
//!   exist for UTF-8 and the single-byte encodings only ([`encodable`]).
//!   `replacement`, UTF-16BE and UTF-16LE never reach an encoder because
//!   "get an output encoding" ([`output_encoding`]) maps them to UTF-8. The
//!   multi-byte legacy encodings (Big5, EUC-JP, ISO-2022-JP, Shift_JIS,
//!   EUC-KR, GBK, gb18030) and x-user-defined have no encoder yet (Phase 8
//!   for the first seven): a submission that needs an encoder for one of them
//!   is **refused** ([`Refusal::UnsupportedEncoding`]), not guessed. Listed.
//! - **"percent-encode after encoding" for a single-byte encoder** is
//!   transcribed as one step per code point ([`percent_encode_after_encoding_sb`]):
//!   a single-byte encoder is stateless, so "encode or fail" returns at each
//!   unencodable code point and the `while potentialError is non-null` loop
//!   (step 7) resumes at the next one; each code point is therefore either
//!   one byte (step 7.3) or an error (step 7.4: `%26%23`, the code point in
//!   decimal, `%3B`). For UTF-8 the loop runs once and `clazel-percent`'s
//!   transcription is used.
//! - **A list is a `Seq`**; "for each" is recursion on the first element,
//!   and "let output be ... append" is an accumulator argument where the
//!   standard tests `output` ([`serialize_loop`]).
//! - **The form document, the entry list's flags and the events are
//!   parameters or skipped**: steps 3 and 4 ("form document", the sandboxed
//!   forms flag), the `submitted from submit()` branch (user validity,
//!   interactive constraint validation, the `submit` event, `firing
//!   submission events`) and step 2 (`constructing entry list`) need script,
//!   a sandbox or UI the engine does not have at this point; the caller
//!   (item 6.15's validation, item 6.16's kernel) runs them before it calls
//!   this algorithm, so [`submit`] begins at step 9 for a connected form.
//!   "Cannot navigate" (the form is not connected; the document is always
//!   fully active) is step 1 and is also the standard's re-check at steps
//!   12 and after, which cannot change here (no script ran in between).
//! - **The submitter is a node**: the submit button, or the form itself
//!   when the standard's "submitter" is the form (implicit submission with
//!   no default button, `requestSubmit()`). The "form owner" of the
//!   submitter is the `form` parameter (the caller passes a button that is a
//!   control of `form`). A submitter that is the form is not a "submit
//!   button", so only the form's attributes are read.
//! - **`dialog` is refused** ([`Refusal::Dialog`]): closing a `dialog`
//!   needs script-free dialog support the engine lacks; the standard either
//!   returns (no ancestor `dialog`) or closes it. Listed.
//! - **The scheme table**: `http`, `https`, `ftp`, `data` follow the table;
//!   `javascript` ([`Refusal::JavascriptScheme`]) and `mailto`
//!   ([`Refusal::MailtoScheme`]) are refused (no script; no mail client);
//!   every other scheme is "not defined by this specification" and is
//!   refused ([`Refusal::UnlistedScheme`]). Listed.
//! - **"Plan to navigate" is its result**: the queued task's navigation
//!   becomes the output [`Navigation`] value (URL, method, body, target). The
//!   planned-navigation bookkeeping (removing a prior task) is the kernel's.
//!   `historyHandling` ("replace" while the form's document has not
//!   completely loaded) is the kernel's too: it knows the load state.
//! - **"Encoding-parsing a URL" uses UTF-8 for the query**: `clazel-url`'s
//!   basic URL parser encodes a query in UTF-8 only. For a document in a
//!   single-byte encoding the standard percent-encodes the action URL's own
//!   query in that encoding. Only a POST (and `data:` POST, `ftp:`) action's
//!   own query is affected (a GET replaces it). Listed.
//! - **The document's base URL and URL are parameters**: the document base
//!   URL as a parsed URL ([`Url`]), the document URL as a string (the
//!   standard says "let action be the URL of form document", then parses it,
//!   which is a parse of its serialization).
//! - **The target** ("get an element's target", "the rules for choosing a
//!   navigable") is classified to [`Target`]: `_self`, `_parent`, `_top`, an
//!   empty target and no target all mean this tab (no nested browsing
//!   contexts yet); `_blank` and any other name mean a new tab (there are no
//!   other named tabs to find). Listed in phase-6.md 6.14 as a choice the
//!   maintainer may reverse. `noopener` is then irrelevant: a new tab never
//!   gets an opener.
//! - **`rel`**: "link types include `noreferrer`" is the ASCII
//!   case-insensitive presence of that token in the `rel` attribute split on
//!   ASCII whitespace.
//! - **The multipart boundary is a parameter**, and a precondition of
//!   [`multipart_encode`] ([`wf_boundary`]: 1 to 70 characters of RFC 2046's
//!   `bchars` without space, so no trailing space). The standard says only
//!   that the algorithm generates one; the kernel generates it from random
//!   bytes. A boundary that is not well formed is refused
//!   ([`Refusal::BadBoundary`]). That the boundary does not occur in the
//!   body is not checked (a 128-bit random boundary makes it negligible);
//!   listed.
//! - **`multipart/form-data` field syntax** follows RFC 7578 as browsers
//!   emit it: each part is `--boundary CRLF Content-Disposition: form-data;
//!   name="NAME" CRLF CRLF VALUE CRLF`, the end is `--boundary-- CRLF`; no
//!   `Content-Type` for non-file parts; no `filename` (no `File` entries
//!   exist, phase-6.md 6.0).
//! - **No `File` entries**: "convert to a list of name-value pairs" step
//!   2's `File` branch and multipart's `File` branches are out; entry
//!   values are strings.

#[cfg(verus_only)]
use crate::spec::*;
pub use crate::spec::Entry;
#[cfg(verus_only)]
use clazel_encoding::labels::spec::get_an_encoding;
pub use clazel_encoding::labels::spec::Encoding;
#[cfg(verus_only)]
use clazel_encoding::single_byte::spec::{encoder_handler, is_single_byte};
pub use clazel_encoding::single_byte::spec::EncoderResult;
#[cfg(verus_only)]
use clazel_encoding::utf8::spec::{is_scalar_value, utf8_encode};
pub use clazel_encoding::utf8::spec::ScalarItem;
#[cfg(verus_only)]
use clazel_percent::spec::{encode_output_byte, percent_encode_after_encoding_utf8};
pub use clazel_percent::spec::PercentEncodeSet;
pub use clazel_url::url::spec::Url;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Strings

/// "Convert to a scalar value string" (Infra §4.6): each surrogate (and
/// each `u32` that is not a code point) becomes U+FFFD.
pub open spec fn to_scalar(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| if is_scalar_value(c) { c } else { 0xFFFDu32 })
}

/// "Create an entry" steps 1 and 2 for every entry: the name and the value
/// are converted to scalar value strings.
pub open spec fn scalar_entries(es: Seq<Entry>) -> Seq<Entry>
    decreases es.len(),
{
    if es.len() == 0 {
        Seq::empty()
    } else {
        seq![Entry { name: to_scalar(es[0].name), value: to_scalar(es[0].value) }] + scalar_entries(es.drop_first())
    }
}

/// "Replace every occurrence of U+000D (CR) not followed by U+000A (LF),
/// and every occurrence of U+000A (LF) not preceded by U+000D (CR), by a
/// string consisting of U+000D (CR) and U+000A (LF)" (§4.10.22.6 steps 1.1
/// and 1.3; §4.10.22.8 step 1). One pass: a CR followed by LF is kept as the
/// pair (the LF is preceded by CR, so it is not replaced), any other CR
/// becomes CR LF, and an LF not consumed with a CR before it becomes CR LF.
pub open spec fn crlf_newlines(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 0x0D {
        if s.len() > 1 && s[1] == 0x0A {
            seq![0x0Du32, 0x0Au32] + crlf_newlines(s.skip(2))
        } else {
            seq![0x0Du32, 0x0Au32] + crlf_newlines(s.drop_first())
        }
    } else if s[0] == 0x0A {
        seq![0x0Du32, 0x0Au32] + crlf_newlines(s.drop_first())
    } else {
        seq![s[0]] + crlf_newlines(s.drop_first())
    }
}

/// Infra "split a string on ASCII whitespace": the tokens are the maximal
/// runs of code points that are not ASCII whitespace, in order. `cur` is
/// the token being collected, so the standard's "skip ASCII whitespace;
/// collect a sequence of code points that are not ASCII whitespace" is
/// written as one pass.
pub open spec fn split_ws_acc(s: Seq<u32>, cur: Seq<u32>) -> Seq<Seq<u32>>
    decreases s.len(),
{
    if s.len() == 0 {
        if cur.len() > 0 {
            seq![cur]
        } else {
            Seq::empty()
        }
    } else if is_ascii_whitespace(s[0]) {
        (if cur.len() > 0 {
            seq![cur]
        } else {
            Seq::empty()
        }) + split_ws_acc(s.drop_first(), Seq::empty())
    } else {
        split_ws_acc(s.drop_first(), cur.push(s[0]))
    }
}

/// Infra "split a string on ASCII whitespace".
pub open spec fn split_ws(s: Seq<u32>) -> Seq<Seq<u32>> {
    split_ws_acc(s, Seq::empty())
}

/// Some token of `toks` is an ASCII case-insensitive match for the
/// lowercase ASCII keyword `k`.
pub open spec fn any_ci(toks: Seq<Seq<u32>>, k: Seq<u8>) -> bool
    decreases toks.len(),
{
    toks.len() > 0 && (ci_eq(toks[0], k) || any_ci(toks.drop_first(), k))
}

// ---------------------------------------------------------------------
// Encodings

/// Encoding "get an output encoding" (§4.2): "1. If encoding is replacement
/// or UTF-16BE/LE, then return UTF-8. 2. Return encoding."
pub open spec fn output_encoding(e: Encoding) -> Encoding {
    match e {
        Encoding::Replacement | Encoding::Utf16Be | Encoding::Utf16Le => Encoding::Utf8,
        _ => e,
    }
}

/// The encodings that have an encoder here: UTF-8 and the single-byte
/// encodings (see the modelling choices).
pub open spec fn encodable(e: Encoding) -> bool {
    e is Utf8 || is_single_byte(e)
}

/// Encoding "encode" (§6), UTF-8 or a single-byte `e`, on a scalar value
/// string, with the "html" error mode ("UTF-8 encode" for UTF-8).
pub open spec fn encode_with(e: Encoding, s: Seq<u32>) -> Seq<u8> {
    if e is Utf8 {
        utf8_encode(s)
    } else {
        clazel_encoding::single_byte::spec::encode(e, s)
    }
}

/// HTML §4.10.22.5 "picking an encoding for the form", given the
/// document's character encoding and the form's `accept-charset` attribute.
pub open spec fn pick_encoding(document_encoding: Encoding, accept_charset: Option<Seq<u32>>) -> Encoding {
    // 1. "Let encoding be the document's character encoding."
    // 2. "If the form element has an accept-charset attribute, set encoding
    //    to the return value of running these substeps:"
    let encoding = match accept_charset {
        Some(input) => {
            // 2.1 "Let input be the value of the form element's
            //     accept-charset attribute." 2.2 "Let candidate encoding
            //     labels be the result of splitting input on ASCII
            //     whitespace."
            let labels = split_ws(input);
            // 2.3 and 2.4 "Let candidate encodings be an empty list ... For
            //     each token ... get an encoding for the token and, if this
            //     does not result in failure, append the encoding."
            let candidates = candidate_encodings(labels);
            // 2.5 "If candidate encodings is empty, return UTF-8."
            if candidates.len() == 0 {
                Encoding::Utf8
            } else {
                // 2.6 "Return the first encoding in candidate encodings."
                candidates[0]
            }
        },
        None => document_encoding,
    };
    // 3. "Return the result of getting an output encoding from encoding."
    output_encoding(encoding)
}

/// Step 2.3 and 2.4: the encodings that "get an encoding" finds for the
/// tokens, in order.
pub open spec fn candidate_encodings(labels: Seq<Seq<u32>>) -> Seq<Encoding>
    decreases labels.len(),
{
    if labels.len() == 0 {
        Seq::empty()
    } else {
        (match get_an_encoding(labels[0]) {
            Some(e) => seq![e],
            None => Seq::empty(),
        }) + candidate_encodings(labels.drop_first())
    }
}

// ---------------------------------------------------------------------
// URL §5.2: the application/x-www-form-urlencoded serializer

/// URL §1.3 "percent-encode after encoding" with a single-byte encoder `e`
/// and `percentEncodeSet` (see the modelling choices): from the code points
/// of `input`, each either one encoded byte (step 7.3) or the error
/// (step 7.4).
pub open spec fn percent_encode_after_encoding_sb(e: Encoding, input: Seq<u32>, set: PercentEncodeSet) -> Seq<u32>
    decreases input.len(),
{
    if input.len() == 0 {
        Seq::empty()
    } else {
        // 2. "Let spaceAsPlus be true if percentEncodeSet is
        //    application/x-www-form-urlencoded percent-encode set;
        //    otherwise false."
        let space_as_plus = set == PercentEncodeSet::ApplicationXWwwFormUrlencoded;
        (match encoder_handler(e, ScalarItem::ScalarValue(input[0])) {
            // 7.3 "For each byte of encodeOutput": the one byte.
            EncoderResult::Byte(b) => encode_output_byte(set, space_as_plus, b),
            // 7.4 "If potentialError is non-null, then append "%26%23",
            //     followed by the shortest sequence of ASCII digits
            //     representing potentialError in base ten, followed by
            //     "%3B", to output."
            EncoderResult::Error(c) => ascii(b"%26%23"@) + decimal(c as nat) + ascii(b"%3B"@),
            EncoderResult::Finished => Seq::empty(),
        }) + percent_encode_after_encoding_sb(e, input.drop_first(), set)
    }
}

/// URL §1.3 "percent-encode after encoding" with encoding `e` (UTF-8 or a
/// single-byte encoding), a scalar value string `input` and `set`.
pub open spec fn percent_encode_after_encoding(e: Encoding, input: Seq<u32>, set: PercentEncodeSet) -> Seq<u32> {
    if e is Utf8 {
        percent_encode_after_encoding_utf8(input, set)
    } else {
        percent_encode_after_encoding_sb(e, input, set)
    }
}

/// The serializer's loop, step 3, from the tuples `tuples` still to do, with
/// `output` the string built so far.
pub open spec fn serialize_loop(tuples: Seq<Entry>, encoding: Encoding, output: Seq<u32>) -> Seq<u32>
    decreases tuples.len(),
{
    if tuples.len() == 0 {
        output
    } else {
        // 3.1 "Assert: tuple's name and tuple's value are scalar value
        //     strings." (The caller's, [`scalar_entries`].)
        // 3.2 "Let name be the result of running percent-encode after
        //     encoding with encoding, tuple's name, and the
        //     application/x-www-form-urlencoded percent-encode set."
        let name = percent_encode_after_encoding(
            encoding,
            tuples[0].name,
            PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        );
        // 3.3 "Let value be the result of running percent-encode after
        //     encoding with encoding, tuple's value, and the
        //     application/x-www-form-urlencoded percent-encode set."
        let value = percent_encode_after_encoding(
            encoding,
            tuples[0].value,
            PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        );
        // 3.4 "If output is not the empty string, then append U+0026 (&) to
        //     output."
        let output = if output.len() != 0 {
            output.push(0x26u32)
        } else {
            output
        };
        // 3.5 "Append name, followed by U+003D (=), followed by value, to
        //     output."
        serialize_loop(tuples.drop_first(), encoding, output + name + seq![0x3Du32] + value)
    }
}

/// URL §5.2 "application/x-www-form-urlencoded serializer", given a list of
/// name-value tuples and an encoding (UTF-8 or single-byte after step 1).
pub open spec fn urlencoded_serialize(tuples: Seq<Entry>, encoding: Encoding) -> Seq<u32> {
    // 1. "Set encoding to the result of getting an output encoding from
    //    encoding."
    let encoding = output_encoding(encoding);
    // 2. "Let output be the empty string." 3. the loop. 4. "Return output."
    serialize_loop(tuples, encoding, Seq::empty())
}

// ---------------------------------------------------------------------
// HTML §4.10.22.6 Converting an entry list to a list of name-value pairs

/// The entry list's pairs, from the entries still to do.
pub open spec fn convert_to_pairs(entry_list: Seq<Entry>) -> Seq<Entry>
    decreases entry_list.len(),
{
    if entry_list.len() == 0 {
        Seq::empty()
    } else {
        // 2.1 "Let name be entry's name, with every occurrence of U+000D
        //     (CR) not followed by U+000A (LF), and every occurrence of
        //     U+000A (LF) not preceded by U+000D (CR), replaced by a string
        //     consisting of U+000D (CR) and U+000A (LF)."
        // 2.2 "If entry's value is a File object ... Otherwise, let value
        //     be entry's value." (no File)
        // 2.3 "Replace every occurrence of U+000D (CR) not followed by
        //     U+000A (LF), and every occurrence of U+000A (LF) not preceded
        //     by U+000D (CR), in value, by a string consisting of U+000D
        //     (CR) and U+000A (LF)."
        // 2.4 "Append to list a new name-value pair whose name is name and
        //     whose value is value."
        seq![Entry {
            name: crlf_newlines(entry_list[0].name),
            value: crlf_newlines(entry_list[0].value),
        }] + convert_to_pairs(entry_list.drop_first())
    }
}

// ---------------------------------------------------------------------
// HTML §4.10.22.9 Plain text form data

/// The `text/plain` encoding algorithm's loop (step 2), from the pairs
/// still to do and the `result` so far.
pub open spec fn text_plain_loop(pairs: Seq<Entry>, result: Seq<u32>) -> Seq<u32>
    decreases pairs.len(),
{
    if pairs.len() == 0 {
        result
    } else {
        // 2.1 "Append pair's name to result." 2.2 "Append a single U+003D
        // EQUALS SIGN character (=) to result." 2.3 "Append pair's value to
        // result." 2.4 "Append a U+000D CARRIAGE RETURN (CR) U+000A LINE
        // FEED (LF) character pair to result."
        text_plain_loop(
            pairs.drop_first(),
            result + pairs[0].name + seq![0x3Du32] + pairs[0].value + seq![0x0Du32, 0x0Au32],
        )
    }
}

/// HTML §4.10.22.9 "text/plain encoding algorithm", given a list of
/// name-value pairs.
pub open spec fn text_plain_encode(pairs: Seq<Entry>) -> Seq<u32> {
    // 1. "Let result be the empty string." 2. the loop. 3. "Return result."
    text_plain_loop(pairs, Seq::empty())
}

// ---------------------------------------------------------------------
// HTML §4.10.22.8 Multipart form data

/// RFC 2046 §5.1.1 `bchars` without the space: DIGIT, ALPHA and
/// `'()+_,-./:=?`.
pub open spec fn is_bchar(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x5A) || (0x61 <= b <= 0x7A) || b == 0x27 || b == 0x28 || b == 0x29
        || b == 0x2B || b == 0x5F || b == 0x2C || b == 0x2D || b == 0x2E || b == 0x2F || b == 0x3A || b == 0x3D
        || b == 0x3F
}

/// A boundary RFC 2046 §5.1.1 allows, restricted to the characters without
/// the space: 1 to 70 `bchars`.
pub open spec fn wf_boundary(b: Seq<u8>) -> bool {
    1 <= b.len() <= 70 && forall|k: int| 0 <= k < b.len() ==> is_bchar(#[trigger] b[k])
}

/// "For field names and filenames for file fields, the result of the
/// encoding ... must be escaped by replacing any 0x0A (LF) bytes with the
/// byte sequence `%0A`, 0x0D (CR) with `%0D` and 0x22 (") with `%22`. The
/// user agent must not perform any other escapes."
pub open spec fn escape_name(b: Seq<u8>) -> Seq<u8>
    decreases b.len(),
{
    if b.len() == 0 {
        Seq::empty()
    } else {
        (if b[0] == 0x0A {
            b"%0A"@
        } else if b[0] == 0x0D {
            b"%0D"@
        } else if b[0] == 0x22 {
            b"%22"@
        } else {
            seq![b[0]]
        }) + escape_name(b.drop_first())
    }
}

/// The part of the `multipart/form-data` resource for one `entry` (RFC 7578
/// §4.1, §4.2): the delimiter line, the `Content-Disposition` header with
/// the field name, the empty line, the field value, and a CRLF.
pub open spec fn multipart_part(entry: Entry, encoding: Encoding, boundary: Seq<u8>) -> Seq<u8> {
    // 1.1 "Replace every occurrence of U+000D (CR) not followed by U+000A
    //     (LF), and every occurrence of U+000A (LF) not preceded by U+000D
    //     (CR), in entry's name, by a string consisting of a U+000D (CR) and
    //     U+000A (LF)."
    // 1.2 "If entry's value is not a File object, then replace every
    //     occurrence of U+000D (CR) not followed by U+000A (LF), and every
    //     occurrence of U+000A (LF) not preceded by U+000D (CR), in entry's
    //     value, by a string consisting of a U+000D (CR) and U+000A (LF)."
    let name = crlf_newlines(entry.name);
    let value = crlf_newlines(entry.value);
    // 2. the conditions: field names and field values "set to the result of
    //    encoding the corresponding entry's name or value with encoding,
    //    converted to a byte sequence"; the name escaped.
    b"--"@ + boundary + b"\r\nContent-Disposition: form-data; name=\""@ + escape_name(encode_with(encoding, name))
        + b"\"\r\n\r\n"@ + encode_with(encoding, value) + b"\r\n"@
}

/// The parts of the entries `entries`, in order ("The order of parts must be
/// the same as the order of fields in entry list. Multiple entries with the
/// same name must be treated as distinct fields.").
pub open spec fn multipart_parts(entries: Seq<Entry>, encoding: Encoding, boundary: Seq<u8>) -> Seq<u8>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Seq::empty()
    } else {
        multipart_part(entries[0], encoding, boundary) + multipart_parts(entries.drop_first(), encoding, boundary)
    }
}

/// HTML §4.10.22.8 "multipart/form-data encoding algorithm", given an entry
/// list, an encoding and the boundary string: the parts, then the closing
/// delimiter `--boundary--` and a CRLF (RFC 7578 §4.1; RFC 2046 §5.1.1).
pub open spec fn multipart_encode(entries: Seq<Entry>, encoding: Encoding, boundary: Seq<u8>) -> Seq<u8> {
    multipart_parts(entries, encoding, boundary) + b"--"@ + boundary + b"--\r\n"@
}

// ---------------------------------------------------------------------
// HTML §4.10.19.6 Form submission attributes

/// The states of the `method` and `formmethod` attributes.
pub enum MethodState {
    /// "GET"
    Get,
    /// "POST"
    Post,
    /// "Dialog"
    Dialog,
}

/// The state of a `method` or `formmethod` attribute value: an enumerated
/// attribute (keywords matched ASCII case-insensitively), the invalid value
/// default GET.
pub open spec fn method_of_value(v: Seq<u32>) -> MethodState {
    if ci_eq(v, b"get"@) {
        MethodState::Get
    } else if ci_eq(v, b"post"@) {
        MethodState::Post
    } else if ci_eq(v, b"dialog"@) {
        MethodState::Dialog
    } else {
        MethodState::Get
    }
}

/// The states of the `enctype` and `formenctype` attributes.
pub enum EnctypeState {
    /// `application/x-www-form-urlencoded`
    UrlEncoded,
    /// `multipart/form-data`
    FormData,
    /// `text/plain`
    Text,
}

/// The state of an `enctype` or `formenctype` attribute value; the invalid
/// value default is `application/x-www-form-urlencoded`.
pub open spec fn enctype_of_value(v: Seq<u32>) -> EnctypeState {
    if ci_eq(v, b"application/x-www-form-urlencoded"@) {
        EnctypeState::UrlEncoded
    } else if ci_eq(v, b"multipart/form-data"@) {
        EnctypeState::FormData
    } else if ci_eq(v, b"text/plain"@) {
        EnctypeState::Text
    } else {
        EnctypeState::UrlEncoded
    }
}

/// HTML §4.10.2 "submit button" (concept-submit-button): a `button`
/// element whose `type` is in the Submit Button state (`submit`, and the
/// missing and invalid value default), or an `input` element whose `type`
/// is in the Submit Button or Image Button state.
pub open spec fn is_submit_button(doc: Document, n: NodeId) -> bool {
    if is_html(doc, n, b"button"@) {
        match attr(doc, n, b"type"@) {
            None => true,
            Some(v) => !(ci_eq(v, b"reset"@) || ci_eq(v, b"button"@)),
        }
    } else {
        is_html(doc, n, b"input"@) && (input_type(doc, n) is Submit || input_type(doc, n) is Image)
    }
}

/// The `submitter` element's action: "the value of the element's
/// `formaction` attribute, if the element is a submit button and has such an
/// attribute, or the value of its form owner's `action` attribute, if it has
/// one, or else the empty string."
pub open spec fn submitter_action(doc: Document, form: NodeId, submitter: NodeId) -> Seq<u32> {
    match (is_submit_button(doc, submitter), attr(doc, submitter, b"formaction"@), attr(doc, form, b"action"@)) {
        (true, Some(v), _) => v,
        (_, _, Some(v)) => v,
        _ => Seq::empty(),
    }
}

/// The `submitter` element's method: "If the element is a submit button and
/// has a `formmethod` attribute, then the element's method is that
/// attribute's state; otherwise, it is the form owner's `method`
/// attribute's state" (missing value default GET).
pub open spec fn submitter_method(doc: Document, form: NodeId, submitter: NodeId) -> MethodState {
    match (is_submit_button(doc, submitter), attr(doc, submitter, b"formmethod"@), attr(doc, form, b"method"@)) {
        (true, Some(v), _) => method_of_value(v),
        (_, _, Some(v)) => method_of_value(v),
        _ => MethodState::Get,
    }
}

/// The `submitter` element's enctype, likewise.
pub open spec fn submitter_enctype(doc: Document, form: NodeId, submitter: NodeId) -> EnctypeState {
    match (is_submit_button(doc, submitter), attr(doc, submitter, b"formenctype"@), attr(doc, form, b"enctype"@)) {
        (true, Some(v), _) => enctype_of_value(v),
        (_, _, Some(v)) => enctype_of_value(v),
        _ => EnctypeState::UrlEncoded,
    }
}

// ---------------------------------------------------------------------
// Targets

/// The first `base` element with a `target` attribute among `order`
/// ("contains a base element with a target attribute ... the first such
/// base element"), in tree order.
pub open spec fn first_base_target(doc: Document, order: Seq<NodeId>) -> Option<Seq<u32>>
    decreases order.len(),
{
    if order.len() == 0 {
        None
    } else if is_html(doc, order[0], b"base"@) && has_attr(doc, order[0], b"target"@) {
        attr(doc, order[0], b"target"@)
    } else {
        first_base_target(doc, order.drop_first())
    }
}

/// "An ASCII tab or newline" (Infra): U+0009 TAB, U+000A LF, U+000D CR.
pub open spec fn is_ascii_tab_or_newline(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0D
}

/// `s` contains an ASCII tab or newline.
pub open spec fn has_tab_newline(s: Seq<u32>) -> bool
    decreases s.len(),
{
    s.len() > 0 && (is_ascii_tab_or_newline(s[0]) || has_tab_newline(s.drop_first()))
}

/// `s` contains a U+003C (<).
pub open spec fn has_lt(s: Seq<u32>) -> bool
    decreases s.len(),
{
    s.len() > 0 && (s[0] == 0x3C || has_lt(s.drop_first()))
}

/// `s` contains an ASCII tab or newline and a U+003C (<).
pub open spec fn has_tab_newline_and_lt(s: Seq<u32>) -> bool {
    has_tab_newline(s) && has_lt(s)
}

/// HTML "get an element's target", given the `form` element, the optional
/// `target` (the submitter's `formtarget`) and the document's `base`
/// target ([`first_base_target`] over the form's tree).
pub open spec fn get_an_elements_target(
    doc: Document,
    form: NodeId,
    target: Option<Seq<u32>>,
    base_target: Option<Seq<u32>>,
) -> Option<Seq<u32>> {
    // 1. "If target is null:"
    let target = if target is None {
        // 1.1 "If element has a target attribute, then set target to that
        //     attribute's value."
        if has_attr(doc, form, b"target"@) {
            attr(doc, form, b"target"@)
        } else {
            // 1.2 "Otherwise, if element's node document contains a base
            //     element with a target attribute, set target to the value
            //     of the target attribute of the first such base element."
            base_target
        }
    } else {
        target
    };
    // 2. "If target is not null, and contains an ASCII tab or newline and a
    //    U+003C (<), then set target to "_blank"."
    // 3. "Return target."
    match target {
        Some(t) => if has_tab_newline_and_lt(t) {
            Some(ascii(b"_blank"@))
        } else {
            Some(t)
        },
        None => None,
    }
}

/// Which tab the navigation is for (see the modelling choices).
pub enum Target {
    /// This tab: no target, an empty target, `_self`, `_parent`, `_top`.
    ThisTab,
    /// A new tab: `_blank` and every other name.
    NewTab,
}

/// "The rules for choosing a navigable" given the target name, as far as a
/// browser of one tab and no nested browsing contexts can follow them.
pub open spec fn choose_navigable(target: Option<Seq<u32>>) -> Target {
    match target {
        None => Target::ThisTab,
        Some(t) => if t.len() == 0 || ci_eq(t, b"_self"@) || ci_eq(t, b"_parent"@) || ci_eq(t, b"_top"@) {
            Target::ThisTab
        } else {
            Target::NewTab
        },
    }
}

// ---------------------------------------------------------------------
// §4.10.22.3 The form submission algorithm

/// A request body and its content type.
pub struct Body {
    /// The request body, bytes.
    pub bytes: Seq<u8>,
    /// The request content type (a header value, ASCII).
    pub content_type: Seq<u8>,
}

/// The HTTP method of the navigation: GET, or POST when there is a body.
pub enum NavMethod {
    /// GET
    Get,
    /// POST
    Post,
}

/// What "plan to navigate" would queue: the URL to navigate to, the POST
/// resource (a body and content type) or none, the tab, and whether the
/// referrer policy is `no-referrer` (the `form`'s link types include
/// `noreferrer`).
pub struct Navigation {
    /// The URL to navigate to ("parsed action", possibly with its query
    /// set).
    pub url: Url,
    /// GET, or POST with a body.
    pub method: NavMethod,
    /// The POST resource: present exactly for POST.
    pub body: Option<Body>,
    /// This tab or a new one.
    pub target: Target,
    /// "If the form element's link types include the noreferrer keyword,
    /// then set referrerPolicy to "no-referrer"".
    pub no_referrer: bool,
}

/// Why a submission is not carried out, beyond what the standard itself
/// returns on (see the modelling choices).
pub enum Refusal {
    /// `method` is `dialog`.
    Dialog,
    /// The scheme is `mailto`.
    MailtoScheme,
    /// The scheme is `javascript`.
    JavascriptScheme,
    /// The scheme is none of the table's rows.
    UnlistedScheme,
    /// The encoding has no encoder yet (multi-byte legacy, x-user-defined).
    UnsupportedEncoding,
    /// The multipart boundary is not a well-formed boundary.
    BadBoundary,
}

/// The result of the form submission algorithm.
pub enum Outcome {
    /// The standard "return"s: nothing happens.
    Ignored,
    /// Not supported here, with the reason.
    Refused(Refusal),
    /// "Plan to navigate" with this.
    Navigate(Navigation),
}

/// "Mutate action URL" (steps with `pairs`, `query`): the action with its
/// query set to the serialization of the pairs.
pub open spec fn mutate_action_url(parsed: Url, pairs: Seq<Entry>, encoding: Encoding) -> Url {
    // "Let query be the result of running the application/x-www-form-urlencoded
    // serializer with pairs and encoding."
    let query = urlencoded_serialize(pairs, encoding);
    // "Set parsed action's query component to query."
    Url { query: Some(query), ..parsed }
}

/// "Submit as entity body", given the enctype, the entry list (scalar
/// value strings), the encoding and the boundary: the body and its content
/// type.
pub open spec fn entity_body(enctype: EnctypeState, entry_list: Seq<Entry>, encoding: Encoding, boundary: Seq<u8>) -> Body {
    match enctype {
        // "application/x-www-form-urlencoded": "Let pairs be the result of
        // converting to a list of name-value pairs with entry list. Let body
        // be the result of running the application/x-www-form-urlencoded
        // serializer with pairs and encoding. Set body to the result of
        // encoding body. Let mimeType be `application/x-www-form-urlencoded`."
        EnctypeState::UrlEncoded => Body {
            bytes: utf8_encode(urlencoded_serialize(convert_to_pairs(entry_list), encoding)),
            content_type: b"application/x-www-form-urlencoded"@,
        },
        // "multipart/form-data": "Let body be the result of running the
        // multipart/form-data encoding algorithm with entry list and
        // encoding. Let mimeType be the isomorphic encoding of the
        // concatenation of "multipart/form-data; boundary=" and the
        // multipart/form-data boundary string".
        EnctypeState::FormData => Body {
            bytes: multipart_encode(entry_list, encoding, boundary),
            content_type: b"multipart/form-data; boundary="@ + boundary,
        },
        // "text/plain": "Let pairs be the result of converting to a list of
        // name-value pairs with entry list. Let body be the result of running
        // the text/plain encoding algorithm with pairs. Set body to the
        // result of encoding body using encoding. Let mimeType be
        // `text/plain`."
        EnctypeState::Text => Body {
            bytes: encode_with(encoding, text_plain_encode(convert_to_pairs(entry_list))),
            content_type: b"text/plain"@,
        },
    }
}

/// Steps from "Let method be the submitter element's method" on, for a
/// submission whose entry list is `entry_list` (already built, with
/// "create an entry"'s steps 1 and 2 applied by [`scalar_entries`]).
pub open spec fn submit_from_method(
    doc: Document,
    form: NodeId,
    submitter: NodeId,
    encoding: Encoding,
    entry_list: Seq<Entry>,
    document_url: Seq<u32>,
    base_url: Url,
    boundary: Seq<u8>,
) -> Outcome {
    // 13. "Let method be the submitter element's method."
    let method = submitter_method(doc, form, submitter);
    // 14. "If method is dialog: ..." (refused)
    if method is Dialog {
        Outcome::Refused(Refusal::Dialog)
    } else {
        // 15. "Let action be the submitter element's action."
        let action = submitter_action(doc, form, submitter);
        // 16. "If action is the empty string, let action be the URL of form
        //     document."
        let action = if action.len() == 0 {
            document_url
        } else {
            action
        };
        // 17. "Let parsed action be the result of encoding-parsing a URL
        //     given action, relative to submitter's node document." (the
        //     arguments are scalar value strings, see the modelling choices)
        // 18. "If parsed action is failure, then return."
        match clazel_url::url::spec::basic_url_parser(
            to_scalar(action),
            Some(base_url),
            clazel_url::url::contract::url_domain_parser(),
        ) {
            None => Outcome::Ignored,
            Some(parsed) => {
                // 19. "Let scheme be the scheme of parsed action."
                let scheme = parsed.scheme;
                // 20. "Let enctype be the submitter element's enctype."
                let enctype = submitter_enctype(doc, form, submitter);
                // 21. "Let formTarget be null." 22. "If the submitter element
                //     is a submit button and it has a formtarget attribute,
                //     then set formTarget to the formtarget attribute
                //     value."
                let form_target = if is_submit_button(doc, submitter) {
                    attr(doc, submitter, b"formtarget"@)
                } else {
                    None
                };
                // 23. "Let target be the result of getting an element's
                //     target given submitter's form owner and formTarget."
                let base_target = first_base_target(doc, tree_order(doc, root(doc, form), doc.nodes.len()));
                let target = get_an_elements_target(doc, form, form_target, base_target);
                // 24. "Let noopener be ..." 25. "Let targetNavigable be the
                //     first return value of applying the rules for choosing
                //     a navigable ..." 26. "If targetNavigable is null, then
                //     return." 27., 28. historyHandling (see the modelling
                //     choices).
                let chosen = choose_navigable(target);
                // "plan to navigate" step 1 and 2: referrerPolicy.
                let no_referrer = match attr(doc, form, b"rel"@) {
                    Some(rel) => any_ci(split_ws(rel), b"noreferrer"@),
                    None => false,
                };
                // 29. "Select the appropriate row in the table below based
                //     on scheme ... Then, select the appropriate cell on
                //     that row based on method".
                let is_get = method is Get;
                if scheme == ascii(b"http"@) || scheme == ascii(b"https"@) {
                    if !encodable(encoding) {
                        Outcome::Refused(Refusal::UnsupportedEncoding)
                    } else if is_get {
                        // "Mutate action URL"
                        Outcome::Navigate(
                            Navigation {
                                url: mutate_action_url(parsed, convert_to_pairs(entry_list), encoding),
                                method: NavMethod::Get,
                                body: None,
                                target: chosen,
                                no_referrer,
                            },
                        )
                    } else if enctype is FormData && !wf_boundary(boundary) {
                        Outcome::Refused(Refusal::BadBoundary)
                    } else {
                        // "Submit as entity body"
                        Outcome::Navigate(
                            Navigation {
                                url: parsed,
                                method: NavMethod::Post,
                                body: Some(entity_body(enctype, entry_list, encoding, boundary)),
                                target: chosen,
                                no_referrer,
                            },
                        )
                    }
                } else if scheme == ascii(b"data"@) && is_get {
                    if !encodable(encoding) {
                        Outcome::Refused(Refusal::UnsupportedEncoding)
                    } else {
                        // "Mutate action URL"
                        Outcome::Navigate(
                            Navigation {
                                url: mutate_action_url(parsed, convert_to_pairs(entry_list), encoding),
                                method: NavMethod::Get,
                                body: None,
                                target: chosen,
                                no_referrer,
                            },
                        )
                    }
                } else if scheme == ascii(b"data"@) || scheme == ascii(b"ftp"@) {
                    // "Get action URL": "Plan to navigate to parsed action."
                    // The entry list is discarded.
                    Outcome::Navigate(
                        Navigation { url: parsed, method: NavMethod::Get, body: None, target: chosen, no_referrer },
                    )
                } else if scheme == ascii(b"javascript"@) {
                    Outcome::Refused(Refusal::JavascriptScheme)
                } else if scheme == ascii(b"mailto"@) {
                    Outcome::Refused(Refusal::MailtoScheme)
                } else {
                    Outcome::Refused(Refusal::UnlistedScheme)
                }
            },
        }
    }
}

/// HTML §4.10.22.3 "submit", for a form `form` and a submitter
/// `submitter` (the form itself or a submit button that is a control of
/// `form`), beginning at the standard's step 9 (see the modelling choices):
/// the document's character encoding, the document's URL and base URL, and
/// the multipart boundary are parameters; `st` is the control state.
pub open spec fn submit(
    doc: Document,
    st: FormState,
    form: NodeId,
    submitter: NodeId,
    document_encoding: Encoding,
    document_url: Seq<u32>,
    base_url: Url,
    boundary: Seq<u8>,
) -> Outcome {
    // 1. "If form cannot navigate, then return." ("form is not an a element
    //    and is not connected")
    if !(root(doc, form) < doc.nodes.len() && doc.nodes[root(doc, form) as int].kind is Document) {
        Outcome::Ignored
    } else {
        // 9. "Let encoding be the result of picking an encoding for the form."
        let encoding = pick_encoding(document_encoding, attr(doc, form, b"accept-charset"@));
        // 10. "Let entry list be the result of constructing the entry list
        //     with form, submitter, and encoding." 11. "Assert: entry list
        //     is not null." 12. "If form cannot navigate, then return."
        match construct_entry_list(doc, st, form, Some(submitter), encoding_name(encoding), false) {
            None => Outcome::Ignored,
            Some(entry_list) => submit_from_method(
                doc,
                form,
                submitter,
                encoding,
                scalar_entries(entry_list),
                document_url,
                base_url,
                boundary,
            ),
        }
    }
}

/// The encoding's name, the `_charset_` entry's value ("name of encoding").
pub open spec fn encoding_name(e: Encoding) -> Seq<u32> {
    clazel_encoding::labels::spec::name(e)
}

} // verus!
