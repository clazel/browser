//! Opaque-response blocking (ORB), transcribed from the Fetch Standard's
//! pull request #1755, "2.11 Opaque-response blocking" (§2.11.1 "The
//! opaque-response-safelist check", §2.11.2 "Opaque-response MIME type
//! sets"). Phase 6 item 6.17, decision 6.0(i) B. Nothing here runs; it
//! defines what "correct" means.
//!
//! Source: Fetch Standard, PR preview of
//! <https://whatpr.org/fetch/1755.html>, last updated 6 November 2026,
//! commit `730d67a37d7f3d802e96396d00280768773813fb`. The living standard
//! (commit `d7fc0fdb1bdc25bec9c3699b57d4bb042f88098e`, 20 November 2026) does
//! not have the section yet: when it lands, re-transcribe against its commit
//! and update this header. Used from it: the algorithm's steps 1 to 15 below,
//! "obtain a copy of the first bytes of response", the two MIME type sets,
//! and, from Main fetch, the step that returns a network error when the check
//! is false for a request whose response tainting is "opaque" and whose
//! initiator type is not "fetch", "beacon" or "ping" (an image or style
//! request). From other standards: MIME Sniffing §4.6 (HTML, XML, JSON and
//! JavaScript MIME types), §6.1 and §6.2 (the image and the audio or video
//! type pattern matching algorithms), both through `clazel-mime`; Fetch
//! "extract a MIME type", "get, decode, and split" and "determine nosniff"
//! (§3.6), through `clazel-http`'s list splitting.
//!
//! Modelling choices (each listed, with why the meaning is unchanged or how
//! it differs; every difference makes the check refuse more, never less,
//! except where stated):
//! - **A response is its status, its field lines and its whole body.** The
//!   kernel buffers a sub-fetch's response before it forwards anything, so
//!   "obtain a copy of the first bytes" is the first [`first_bytes_len`]
//!   (8096) octets of the body, or all of it if shorter, and cannot fail
//!   (step 7 is never taken). The plan for 6.17 proposed 1,024 octets; the
//!   standard says 8096 and its note says some signatures need more than 1445,
//!   so the standard's number is used.
//! - **The request is the kernel's sub-fetch request**: "no-cors media request
//!   state" is "none" (an image or style request is never a media request),
//!   so steps 4 and 10 and the "initial" branch of step 8 cannot be taken;
//!   they are kept as comments where they would be. The fetch group's "ORB
//!   media URLs" is not kept.
//! - **Step 5, partial responses.** The kernel never sends a `Range` field, so
//!   a status 206 response answers no range request. The standard continues
//!   for a *valid* partial response; this spec returns false for every 206
//!   (a valid one is blocked, which only makes ORB refuse more), so
//!   "validate a partial response" and "parse a single byte content-range
//!   value" are not transcribed.
//! - **Steps 13 and 15 are decided by the model [`Model`].** The standard
//!   returns true for a response whose MIME type is failure (13) and the
//!   result of parsing the body as JavaScript and then as JSON (15). The
//!   kernel has no JavaScript parser (Phase 7), and an image or style request
//!   cannot use a response that is neither. [`spec_model`] is the standard
//!   (step 15's answer is an input, `js_not_json`); [`kernel_model`] returns
//!   false at both, so the kernel forwards a response only if its declared
//!   type is safelisted or its bytes sniff as an image, audio or video
//!   (`lemma_kernel_allows_only_typed`). This is the one place the kernel
//!   refuses more than the standard on purpose.
//! - **"Extract a MIME type"** keeps the last value that parses and is not
//!   `*/*`; its charset bookkeeping (carrying a `charset` parameter to later
//!   values of the same essence) is not transcribed, since ORB reads only the
//!   essence and the type.
//! - **"Get, decode, and split"** is `clazel-http`'s `combined_field_value`
//!   followed by its `split_values` (RFC 9110 §5.6.1 reading: commas outside
//!   quoted strings, each piece stripped of whitespace, empty pieces kept);
//!   Fetch's text (collect an HTTP quoted string, remove HTTP tab or space)
//!   splits at the same commas. Isomorphic decoding of the pieces is done by
//!   `parse_a_mime_type_from_bytes`.
//! - **A MIME type is a [`clazel_mime::mime_type::spec::MimeTypeRecord`]**, whose parser has already
//!   lowercased its type and subtype, so "essence is one of" is code point
//!   equality, and "essence starts with `audio/`" is "type is `audio`".
//! - **"Is a JavaScript MIME type"** is MIME Sniffing §4.6's, through
//!   `clazel-mime`; "HTML, JSON or XML MIME type" likewise.
//! - **Where the check applies** ([`orb_applies`]): the standard applies it
//!   when the request's response tainting is "opaque": a "no-cors" request
//!   whose URL is not same origin with the document's. The kernel decides on
//!   the *final* URL of the fetch (after redirects): ORB applies whenever the
//!   origin of that URL is not the renderer's lock. A cross-origin start that
//!   redirects back to the lock's origin is not checked (its body is the
//!   lock's own content); a same-origin start that redirects away is.
//! - **Not transcribed:** the Cross-Origin Resource Policy check that follows
//!   in Main fetch (the kernel does not implement it yet), and everything for
//!   `fetch()` initiators (the renderer's sub-fetches are image and style
//!   requests; Phase 7 adds `script`).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// The model: what the standard leaves to a JavaScript parser.
// ===========================================================================

/// How steps 13 and 15 are decided (see the modelling choices).
pub struct Model {
    /// Step 13: "If mimeType is failure, then return true."
    pub allow_unknown_type: bool,
    /// Step 15: "Return the result of determining if response is JavaScript
    /// and not JSON".
    pub js_not_json: bool,
}

/// The standard's, given the answer of its step 15.
pub open spec fn spec_model(js_not_json: bool) -> Model {
    Model { allow_unknown_type: true, js_not_json }
}

/// The kernel's: refuse at steps 13 and 15.
pub open spec fn kernel_model() -> Model {
    Model { allow_unknown_type: false, js_not_json: false }
}

/// "Truncate bytes from the end so that it only contains 8096 bytes."
pub open spec fn first_bytes_len() -> nat {
    8096
}

// ===========================================================================
// Header access (Fetch §3.5 "extract a MIME type", §3.6 "determine nosniff").
// ===========================================================================

/// "get, decode, and split" `name` from the header list: the combined value
/// split at commas; `None` is "null".
pub open spec fn get_decode_split(fields: Seq<clazel_http::field::spec::FieldLine>, name: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match clazel_http::field::spec::combined_field_value(fields, name) {
        Some(v) => Some(clazel_http::field::spec::split_values(v)),
        None => None,
    }
}

/// The octets of `content-type`.
pub open spec fn content_type_name() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65]
}

/// The octets of `x-content-type-options`.
pub open spec fn x_content_type_options_name() -> Seq<u8> {
    seq![0x78u8, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65, 0x2D, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73]
}

/// The loop of "extract a MIME type" over `values` from `mime_type` on:
/// "For each value of values: Let temporaryMimeType be the result of parsing
/// value. If temporaryMimeType is failure or its essence is "*/*", then
/// continue. Set mimeType to temporaryMimeType." (the charset steps are not
/// transcribed.)
pub open spec fn extract_from(values: Seq<Seq<u8>>, mime_type: Option<clazel_mime::mime_type::spec::MimeTypeRecord>) -> Option<clazel_mime::mime_type::spec::MimeTypeRecord>
    decreases values.len(),
{
    if values.len() == 0 {
        mime_type
    } else {
        let temporary = clazel_mime::mime_type::spec::parse_a_mime_type_from_bytes(values[0]);
        let next = match temporary {
            Some(t) => if clazel_mime::mime_type::spec::essence(t) == lit_star_slash_star() { mime_type } else { temporary },
            None => mime_type,
        };
        extract_from(values.drop_first(), next)
    }
}

/// "Extract a MIME type" from the header list: "Let values be the result of
/// getting, decoding, and splitting `Content-Type`. If values is null, then
/// return failure." (`None` is failure; "If mimeType is null, then return
/// failure" is `extract_from`'s `None`.)
pub open spec fn extract_mime_type(fields: Seq<clazel_http::field::spec::FieldLine>) -> Option<clazel_mime::mime_type::spec::MimeTypeRecord> {
    match get_decode_split(fields, content_type_name()) {
        Some(values) => extract_from(values, None),
        None => None,
    }
}

/// "Determine nosniff": "Let values be the result of getting, decoding, and
/// splitting `X-Content-Type-Options` from list. If values is null, then
/// return false. If values[0] is an ASCII case-insensitive match for
/// "nosniff", then return true. Return false." (`split_values` always has a
/// first piece.)
pub open spec fn determine_nosniff(fields: Seq<clazel_http::field::spec::FieldLine>) -> bool {
    match get_decode_split(fields, x_content_type_options_name()) {
        Some(values) => values.len() > 0 && clazel_mime::mime_type::spec::ascii_lowercase(clazel_mime::mime_type::spec::isomorphic_decode(values[0])) == lit_nosniff(),
        None => false,
    }
}

// ===========================================================================
// §2.11.2 Opaque-response MIME type sets.
// ===========================================================================

/// "An opaque-response-safelisted MIME type is a JavaScript MIME type or a
/// MIME type whose essence is one of" the list.
pub open spec fn is_opaque_response_safelisted(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_javascript_mime_type(m) || clazel_mime::mime_type::spec::is_one_of(clazel_mime::mime_type::spec::essence(m), opaque_response_safelisted_essences())
}

/// "An opaque-response-blocklisted MIME type is an HTML MIME type, JSON MIME
/// type, or XML MIME type."
pub open spec fn is_opaque_response_blocklisted(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_html_mime_type(m) || clazel_mime::mime_type::spec::is_json_mime_type(m) || clazel_mime::mime_type::spec::is_xml_mime_type(m)
}

/// "An opaque-response-blocklisted-never-sniffed MIME type is a MIME type
/// whose essence is one of" the list.
pub open spec fn is_opaque_response_blocklisted_never_sniffed(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_one_of(clazel_mime::mime_type::spec::essence(m), opaque_response_blocklisted_never_sniffed_essences())
}

// ===========================================================================
// §2.11.1 The opaque-response-safelist check.
// ===========================================================================

/// "Obtain a copy of the first bytes of response" (see the modelling choices).
pub open spec fn first_bytes(body: Seq<u8>) -> Seq<u8> {
    if body.len() <= first_bytes_len() { body } else { body.take(first_bytes_len() as int) }
}

/// "An ok status": "a status in the range 200 to 299, inclusive."
pub open spec fn is_ok_status(status: nat) -> bool {
    200 <= status <= 299
}

/// The opaque-response-safelist check, given a request (an image or style
/// request: see the modelling choices) and a response, as `model` decides
/// steps 13 and 15.
pub open spec fn opaque_response_safelist_check(model: Model, status: nat, fields: Seq<clazel_http::field::spec::FieldLine>, body: Seq<u8>) -> bool {
    // 1. "Let mimeType be the result of extracting a MIME type from
    //    response's header list."
    let mime_type = extract_mime_type(fields);
    // 2. "Let nosniff be the result of determining nosniff given response's
    //    header list."
    let nosniff = determine_nosniff(fields);
    // 3. "If mimeType is not failure, then:"
    if mime_type is Some && is_opaque_response_safelisted(mime_type->Some_0) {
        // 3.1. "If mimeType is an opaque-response-safelisted MIME type, then
        //       return true."
        true
    } else if mime_type is Some && is_opaque_response_blocklisted_never_sniffed(mime_type->Some_0) {
        // 3.2. "... opaque-response-blocklisted-never-sniffed MIME type, then
        //       return false."
        false
    } else if mime_type is Some && status == 206 && is_opaque_response_blocklisted(mime_type->Some_0) {
        // 3.3. "If response's status is 206 and mimeType is an
        //       opaque-response-blocklisted MIME type, then return false."
        false
    } else if mime_type is Some && nosniff && (is_opaque_response_blocklisted(mime_type->Some_0) || clazel_mime::mime_type::spec::essence(mime_type->Some_0) == lit_text_plain()) {
        // 3.4. "If nosniff is true and mimeType is an
        //       opaque-response-blocklisted MIME type or its essence is
        //       "text/plain", then return false."
        false
    }
    // 4. "If request's no-cors media request state is "subsequent", ..." is
    //    not taken: the state is "none".
    else if status == 206 {
        // 5. "If response's status is 206 and validate a partial response
        //    given 0 and response returns invalid, then return false." (Every
        //    206 is refused; see the modelling choices.)
        false
    } else {
        // 6. "Let bytes be the result of running obtain a copy of the first
        //    bytes of response given response."
        let bytes = first_bytes(body);
        // 7. "If bytes is failure, then return false." (Never: see the
        //    modelling choices.)
        if clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(bytes) is Some {
            // 8. "If the audio or video type pattern matching algorithm given
            //    bytes does not return undefined, then: ... Return true." (The
            //    "initial" branch, 8.1, is not taken: the state is "none".)
            true
        } else if clazel_mime::sniff::spec::image_type_pattern_matching(bytes) is Some {
            // 9. "If the image type pattern matching algorithm given bytes
            //    does not return undefined, then return true."
            true
        }
        // 10. "If request's no-cors media request state is not "none", then
        //     return false." is not taken.
        else if nosniff {
            // 11. "If nosniff is true, then return false."
            false
        } else if !is_ok_status(status) {
            // 12. "If response's status is not an ok status, then return false."
            false
        } else if mime_type is None {
            // 13. "If mimeType is failure, then return true."
            model.allow_unknown_type
        } else if mime_type->Some_0.type_ == lit_audio() || mime_type->Some_0.type_ == lit_image() || mime_type->Some_0.type_ == lit_video() {
            // 14. "If mimeType's essence starts with "audio/", "image/", or
            //     "video/", then return false."
            false
        } else {
            // 15. "Return the result of determining if response is JavaScript
            //     and not JSON given request and response."
            model.js_not_json
        }
    }
}

/// Where the check applies: the response's URL has an origin other than the
/// renderer's lock (see the modelling choices).
pub open spec fn orb_applies(lock: clazel_origin::spec::Origin, response_origin: clazel_origin::spec::Origin) -> bool {
    response_origin != lock
}

/// The kernel's decision on a fetched response: forwarded to the renderer if
/// ORB does not apply or the check (with [`kernel_model`]) returns true. A
/// response for which this is false is a network error (Main fetch: "return
/// a network error").
pub open spec fn orb_allows(lock: clazel_origin::spec::Origin, response_origin: clazel_origin::spec::Origin, response: clazel_http::message::spec::Response) -> bool {
    orb_allows_given(orb_applies(lock, response_origin), response)
}

/// [`orb_allows`], given whether ORB applies.
pub open spec fn orb_allows_given(applies: bool, response: clazel_http::message::spec::Response) -> bool {
    !applies || opaque_response_safelist_check(kernel_model(), response.status_line.status, response.fields, response.body)
}

// ===========================================================================
// String literals and the two sets (generated from the standard's lists; each
// is the text in its doc comment, as code points).
// ===========================================================================

/// "`application/dash+xml`"
pub open spec fn lit_application_dash_xml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x64, 0x61, 0x73, 0x68, 0x2B, 0x78, 0x6D, 0x6C]
}

/// "`application/vnd.apple.mpegurl`"
pub open spec fn lit_application_vnd_apple_mpegurl() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x61, 0x70, 0x70, 0x6C, 0x65, 0x2E, 0x6D, 0x70, 0x65, 0x67, 0x75, 0x72, 0x6C]
}

/// "`audio/aac`"
pub open spec fn lit_audio_aac() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F, 0x2F, 0x61, 0x61, 0x63]
}

/// "`audio/aacp`"
pub open spec fn lit_audio_aacp() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F, 0x2F, 0x61, 0x61, 0x63, 0x70]
}

/// "`audio/mpeg`"
pub open spec fn lit_audio_mpeg() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F, 0x2F, 0x6D, 0x70, 0x65, 0x67]
}

/// "`audio/mpegurl`"
pub open spec fn lit_audio_mpegurl() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F, 0x2F, 0x6D, 0x70, 0x65, 0x67, 0x75, 0x72, 0x6C]
}

/// "`image/svg+xml`"
pub open spec fn lit_image_svg_xml() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x61, 0x67, 0x65, 0x2F, 0x73, 0x76, 0x67, 0x2B, 0x78, 0x6D, 0x6C]
}

/// "`multipart/x-mixed-replace`"
pub open spec fn lit_multipart_x_mixed_replace() -> Seq<u32> {
    seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x78, 0x2D, 0x6D, 0x69, 0x78, 0x65, 0x64, 0x2D, 0x72, 0x65, 0x70, 0x6C, 0x61, 0x63, 0x65]
}

/// "`text/css`"
pub open spec fn lit_text_css() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x73]
}

/// "`text/vtt`"
pub open spec fn lit_text_vtt() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x76, 0x74, 0x74]
}

/// "`application/gzip`"
pub open spec fn lit_application_gzip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x67, 0x7A, 0x69, 0x70]
}

/// "`application/msexcel`"
pub open spec fn lit_application_msexcel() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x65, 0x78, 0x63, 0x65, 0x6C]
}

/// "`application/mspowerpoint`"
pub open spec fn lit_application_mspowerpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/msword`"
pub open spec fn lit_application_msword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/msword-template`"
pub open spec fn lit_application_msword_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64, 0x2D, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/pdf`"
pub open spec fn lit_application_pdf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66]
}

/// "`application/vnd.ces-quickpoint`"
pub open spec fn lit_application_vnd_ces_quickpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/vnd.ces-quicksheet`"
pub open spec fn lit_application_vnd_ces_quicksheet() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x73, 0x68, 0x65, 0x65, 0x74]
}

/// "`application/vnd.ces-quickword`"
pub open spec fn lit_application_vnd_ces_quickword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.ms-excel`"
pub open spec fn lit_application_vnd_ms_excel() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C]
}

/// "`application/vnd.ms-excel.sheet.macroenabled.12`"
pub open spec fn lit_application_vnd_ms_excel_sheet_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-powerpoint`"
pub open spec fn lit_application_vnd_ms_powerpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/vnd.ms-powerpoint.presentation.macroenabled.12`"
pub open spec fn lit_application_vnd_ms_powerpoint_presentation_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-word`"
pub open spec fn lit_application_vnd_ms_word() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.ms-word.document.12`"
pub open spec fn lit_application_vnd_ms_word_document_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-word.document.macroenabled.12`"
pub open spec fn lit_application_vnd_ms_word_document_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.msword`"
pub open spec fn lit_application_vnd_msword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.openxmlformats-officedocument.presentationml.presentation`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_presentationml_presentation() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E]
}

/// "`application/vnd.openxmlformats-officedocument.presentationml.template`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_presentationml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.openxmlformats-officedocument.spreadsheetml.sheet`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74]
}

/// "`application/vnd.openxmlformats-officedocument.spreadsheetml.template`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_spreadsheetml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.openxmlformats-officedocument.wordprocessingml.document`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_wordprocessingml_document() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74]
}

/// "`application/vnd.openxmlformats-officedocument.wordprocessingml.template`"
pub open spec fn lit_application_vnd_openxmlformats_officedocument_wordprocessingml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.presentation-openxml`"
pub open spec fn lit_application_vnd_presentation_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/vnd.presentation-openxmlm`"
pub open spec fn lit_application_vnd_presentation_openxmlm() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x6D]
}

/// "`application/vnd.spreadsheet-openxml`"
pub open spec fn lit_application_vnd_spreadsheet_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/vnd.wordprocessing-openxml`"
pub open spec fn lit_application_vnd_wordprocessing_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/x-gzip`"
pub open spec fn lit_application_x_gzip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x67, 0x7A, 0x69, 0x70]
}

/// "`application/x-protobuf`"
pub open spec fn lit_application_x_protobuf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66]
}

/// "`application/x-protobuffer`"
pub open spec fn lit_application_x_protobuffer() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66, 0x66, 0x65, 0x72]
}

/// "`application/zip`"
pub open spec fn lit_application_zip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x7A, 0x69, 0x70]
}

/// "`multipart/byteranges`"
pub open spec fn lit_multipart_byteranges() -> Seq<u32> {
    seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x62, 0x79, 0x74, 0x65, 0x72, 0x61, 0x6E, 0x67, 0x65, 0x73]
}

/// "`multipart/signed`"
pub open spec fn lit_multipart_signed() -> Seq<u32> {
    seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x73, 0x69, 0x67, 0x6E, 0x65, 0x64]
}

/// "`text/csv`"
pub open spec fn lit_text_csv() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x76]
}

/// "`text/event-stream`"
pub open spec fn lit_text_event_stream() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x65, 0x76, 0x65, 0x6E, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D]
}

/// "`text/plain`"
pub open spec fn lit_text_plain() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E]
}

/// "`audio`"
pub open spec fn lit_audio() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F]
}

/// "`image`"
pub open spec fn lit_image() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x61, 0x67, 0x65]
}

/// "`video`"
pub open spec fn lit_video() -> Seq<u32> {
    seq![0x76u32, 0x69, 0x64, 0x65, 0x6F]
}

/// "`nosniff`"
pub open spec fn lit_nosniff() -> Seq<u32> {
    seq![0x6Eu32, 0x6F, 0x73, 0x6E, 0x69, 0x66, 0x66]
}

/// "`content-type`"
pub open spec fn lit_content_type() -> Seq<u32> {
    seq![0x63u32, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65]
}

/// "`x-content-type-options`"
pub open spec fn lit_x_content_type_options() -> Seq<u32> {
    seq![0x78u32, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65, 0x2D, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73]
}

/// "`*/*`"
pub open spec fn lit_star_slash_star() -> Seq<u32> {
    seq![0x2Au32, 0x2F, 0x2A]
}

pub open spec fn opaque_response_safelisted_essences() -> Seq<Seq<u32>> {
    seq![lit_application_dash_xml(), lit_application_vnd_apple_mpegurl(), lit_audio_aac(), lit_audio_aacp(), lit_audio_mpeg(), lit_audio_mpegurl(), lit_image_svg_xml(), lit_multipart_x_mixed_replace(), lit_text_css(), lit_text_vtt()]
}

pub open spec fn opaque_response_blocklisted_never_sniffed_essences() -> Seq<Seq<u32>> {
    seq![lit_application_gzip(), lit_application_msexcel(), lit_application_mspowerpoint(), lit_application_msword(), lit_application_msword_template(), lit_application_pdf(), lit_application_vnd_ces_quickpoint(), lit_application_vnd_ces_quicksheet(), lit_application_vnd_ces_quickword(), lit_application_vnd_ms_excel(), lit_application_vnd_ms_excel_sheet_macroenabled_12(), lit_application_vnd_ms_powerpoint(), lit_application_vnd_ms_powerpoint_presentation_macroenabled_12(), lit_application_vnd_ms_word(), lit_application_vnd_ms_word_document_12(), lit_application_vnd_ms_word_document_macroenabled_12(), lit_application_vnd_msword(), lit_application_vnd_openxmlformats_officedocument_presentationml_presentation(), lit_application_vnd_openxmlformats_officedocument_presentationml_template(), lit_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet(), lit_application_vnd_openxmlformats_officedocument_spreadsheetml_template(), lit_application_vnd_openxmlformats_officedocument_wordprocessingml_document(), lit_application_vnd_openxmlformats_officedocument_wordprocessingml_template(), lit_application_vnd_presentation_openxml(), lit_application_vnd_presentation_openxmlm(), lit_application_vnd_spreadsheet_openxml(), lit_application_vnd_wordprocessing_openxml(), lit_application_x_gzip(), lit_application_x_protobuf(), lit_application_x_protobuffer(), lit_application_zip(), lit_multipart_byteranges(), lit_multipart_signed(), lit_text_csv(), lit_text_event_stream()]
}

}
