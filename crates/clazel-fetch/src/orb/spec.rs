//! Executable-style specification of opaque-response blocking (ORB): which
//! responses to a "no-cors" request whose response tainting is "opaque" a
//! client may hand to the page. Nothing here runs.
//!
//! Sources (pinned):
//! - **ORB**: the Fetch Standard as amended by whatwg/fetch pull request
//!   #1442 "Add opaque-response blocking" (open, not merged), `fetch.bs` at
//!   the pull request's head commit
//!   `c58393bf0b9e2a86abee916c3cef3361f2741567`: §2.11.1 "The
//!   opaque-response-safelist check" (`#orb-algorithm`) and §2.11.2 "New
//!   MIME type sets" (`#orb-mime-type-sets`). ORB is not in the Fetch
//!   Standard at the commit the transducer pins (below); this pull
//!   request is WHATWG Fetch's ORB algorithm, and the repository it grew in
//!   (annevk/orb, `61c1be761fca35288b6c90249da66ab563f1074c`) names it "the
//!   starting point for implementers". Step numbers below are the pull
//!   request's.
//! - The Fetch Standard at `59afe349913d56898c947576216f1c2579308be7` (the
//!   commit `clazel_fetch::transducer::spec` pins): §2.2.2 "get, decode,
//!   and split" (`#concept-header-list-get-decode-split`), §2.2.3 "ok
//!   status", §3.5 "extract a MIME type"
//!   (`#concept-header-extract-mime-type`) and §3.6 "determine nosniff".
//! - MIME types, the §4.6 groups and the §6.1 and §6.2 pattern matching
//!   algorithms of the MIME Sniffing Standard, through `clazel_mime` (which
//!   pins its commit).
//!
//! # Modelling choices
//!
//! Each is a deviation in form, never in meaning, unless it says otherwise.
//!
//! - **The check's result** is a [`Verdict`]: `Allowed` (the check returns
//!   true), `Blocked` (it returns false), or `JavaScriptCheck`, which stands
//!   for step 15, "Return determine if response is JavaScript and not JSON
//!   given response". That step parses the whole body as a JavaScript
//!   `Script` and as JSON, which is the caller's to decide; this spec stops
//!   where the check would run them. (`clazel-kernel` treats
//!   `JavaScriptCheck` as blocked, a listed choice of its own.)
//! - **No-cors media request state** is "N/A" for every request this client
//!   makes (scripts, style sheets and `fetch()`: there are no media
//!   elements), so step 4 ("subsequent") never returns, step 8.1 always
//!   returns false, and step 9 never returns. They are written out with the
//!   state fixed.
//! - **Step 5, a 206 response.** "validate a partial response given 0 and
//!   response" (Background Fetch) is not transcribed: no request of this
//!   client carries `Range`, so a 206 answers a range request nobody made
//!   (RFC 9110 §15.3.7). Every 206 counts as invalid here, so step 5
//!   returns false for it. This blocks more than the standard does
//!   (a 206 whose `Content-Range` starts at 0 passes the standard's step 5);
//!   it is a deviation in meaning, in the blocking direction.
//! - **Steps 6 and 7, the first 1024 bytes.** The response here is complete
//!   (the transducer reads it whole before `Done`), so "obtain a copy of
//!   the first 1024 bytes of response" is the body's first
//!   `min(1024, len)` octets and is never failure; step 7 never returns.
//! - **Extract a MIME type (§3.5)** keeps the standard's loop but not its
//!   `charset` bookkeeping (steps 1, 2, 6.4 and 6.5): those steps change
//!   only the result's `charset` parameter, and the check reads only the
//!   type, subtype and essence of the result. Which values are skipped
//!   (failure or essence `*/*`) and which one is the result (the last other
//!   one) are as the standard says.
//! - **Header names** are matched ASCII case-insensitively (RFC 9110 §5.1),
//!   so a lowercase literal names them. "Getting" a header is the combined
//!   field value (`clazel_http`'s `combined_field_value`, values joined
//!   with ", " as Fetch's "get" says), and "get, decode, and split" of a
//!   value is `clazel_http`'s `split_values`, which `clazel_http` proves
//!   equal to Fetch's algorithm on every byte sequence
//!   (`lemma_get_decode_split_equals_split_values`). The pieces stay octets:
//!   isomorphic decoding keeps each byte's value, and "parse a MIME type"
//!   of the decoded piece is `clazel_mime`'s `parse_a_mime_type_from_bytes`
//!   of the octets (MIME Sniffing §4.4, which is that decoding then
//!   parsing).
//! - **String literals** are `Seq<u32>` (MIME types are code points) or
//!   `Seq<u8>` (header names and values), written in hex with the text in
//!   the doc comment.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The result of the opaque-response-safelist check (see the modelling
/// choices).
pub enum Verdict {
    /// The check returns true: the response may reach the page.
    Allowed,
    /// The check returns false: the fetch is a network error.
    Blocked,
    /// The check reached step 15, "Return determine if response is
    /// JavaScript and not JSON given response".
    JavaScriptCheck,
}

// ===========================================================================
// Fetch §2.2.2, §3.5 and §3.6: the response's headers.
// ===========================================================================

/// "get, decode, and split" `name` from `fields` (Fetch §2.2.2): "1. Let
/// value be the result of getting name from list. 2. If value is null, then
/// return null. 3. Return the result of getting, decoding, and splitting
/// value." `name` is lowercase.
pub open spec fn get_decode_split(fields: Seq<clazel_http::field::spec::FieldLine>, name: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    // 1.
    match clazel_http::field::spec::combined_field_value(fields, name) {
        // 2.
        None => None,
        // 3.
        Some(value) => Some(clazel_http::field::spec::split_values(value)),
    }
}

/// Extract a MIME type (Fetch §3.5), step 6 from value `i` of `values` on,
/// with `mime_type` the result so far (`None` is null).
pub open spec fn extract_loop(values: Seq<Seq<u8>>, i: nat, mime_type: Option<clazel_mime::mime_type::spec::MimeTypeRecord>) -> Option<
    clazel_mime::mime_type::spec::MimeTypeRecord,
>
    decreases values.len() - i,
{
    if i >= values.len() {
        mime_type
    } else {
        // 6.1. "Let temporaryMimeType be the result of parsing value."
        match clazel_mime::mime_type::spec::parse_a_mime_type_from_bytes(values[i as int]) {
            // 6.2. "If temporaryMimeType is failure ..., then continue."
            None => extract_loop(values, i + 1, mime_type),
            Some(t) => if clazel_mime::mime_type::spec::essence(t) == lit_any_any() {
                // 6.2. "... or its essence is "*/*", then continue."
                extract_loop(values, i + 1, mime_type)
            } else {
                // 6.3. "Set mimeType to temporaryMimeType." (6.4 and 6.5
                // touch only its charset parameter: see the modelling
                // choices.)
                extract_loop(values, i + 1, Some(t))
            },
        }
    }
}

/// Extract a MIME type from `fields` (Fetch §3.5); `None` is failure.
pub open spec fn extract_a_mime_type(fields: Seq<clazel_http::field::spec::FieldLine>) -> Option<clazel_mime::mime_type::spec::MimeTypeRecord> {
    // 3. "Let mimeType be null." 4. "Let values be the result of getting,
    // decoding, and splitting `Content-Type` from headers."
    match get_decode_split(fields, lit_content_type()) {
        // 5. "If values is null, then return failure."
        None => None,
        // 6. the loop; 7. "If mimeType is null, then return failure."
        // 8. "Return mimeType."
        Some(values) => extract_loop(values, 0, None),
    }
}

/// Determine nosniff (Fetch §3.6).
pub open spec fn determine_nosniff(fields: Seq<clazel_http::field::spec::FieldLine>) -> bool {
    // 1. "Let values be the result of getting, decoding, and splitting
    //    `X-Content-Type-Options` from list."
    match get_decode_split(fields, lit_x_content_type_options()) {
        // 2. "If values is null, then return false."
        None => false,
        // 3. "If values[0] is an ASCII case-insensitive match for
        //    "nosniff", then return true." 4. "Return false."
        // (`split_values` always gives at least one value.)
        Some(values) => values.len() > 0 && clazel_http::field::spec::ascii_lowercase(values[0]) == lit_nosniff(),
    }
}

/// An ok status (Fetch §2.2.3): "any status in the range 200 to 299,
/// inclusive".
pub open spec fn is_ok_status(status: nat) -> bool {
    200 <= status <= 299
}

/// `s` starts with `p` (Infra "starts with").
pub open spec fn starts_with(s: Seq<u32>, p: Seq<u32>) -> bool {
    p.len() <= s.len() && s.take(p.len() as int) == p
}

// ===========================================================================
// ORB §2.11.2: the MIME type sets.
// ===========================================================================

/// "An opaque-response-safelisted MIME type is a JavaScript MIME type or a
/// MIME type whose essence is "text/css" or "image/svg+xml"."
pub open spec fn is_opaque_response_safelisted(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_javascript_mime_type(m) || clazel_mime::mime_type::spec::essence(m) == lit_text_css()
        || clazel_mime::mime_type::spec::essence(m) == lit_image_svg_xml()
}

/// "An opaque-response-blocklisted MIME type is an HTML MIME type, JSON MIME
/// type, or XML MIME type."
pub open spec fn is_opaque_response_blocklisted(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_html_mime_type(m) || clazel_mime::mime_type::spec::is_json_mime_type(m)
        || clazel_mime::mime_type::spec::is_xml_mime_type(m)
}

/// "An opaque-response-blocklisted-never-sniffed MIME type is a MIME type
/// whose essence is one of:" [`never_sniffed_essences`].
pub open spec fn is_opaque_response_blocklisted_never_sniffed(m: clazel_mime::mime_type::spec::MimeTypeRecord) -> bool {
    clazel_mime::mime_type::spec::is_one_of(clazel_mime::mime_type::spec::essence(m), never_sniffed_essences())
}

// ===========================================================================
// ORB §2.11.1: the opaque-response-safelist check.
// ===========================================================================

/// The first 1024 octets of `body` (steps 6 and 7; see the modelling
/// choices).
pub open spec fn first_1024_bytes(body: Seq<u8>) -> Seq<u8> {
    if body.len() <= 1024 {
        body
    } else {
        body.take(1024)
    }
}

/// The opaque-response-safelist check (ORB §2.11.1), for a request whose
/// no-cors media request state is "N/A" (see the modelling choices).
pub open spec fn opaque_response_safelist_check(response: clazel_http::message::spec::Response) -> Verdict {
    // 1. "Let mimeType be the result of extracting a MIME type from
    //    response's header list."
    let mime_type = extract_a_mime_type(response.fields);
    // 2. "Let nosniff be the result of determining nosniff given response's
    //    header list."
    let nosniff = determine_nosniff(response.fields);
    match mime_type {
        // 3. "If mimeType is not failure, then:"
        Some(m) => if is_opaque_response_safelisted(m) {
            // 3.1. "If mimeType is an opaque-response-safelisted MIME type,
            //      then return true."
            Verdict::Allowed
        } else if is_opaque_response_blocklisted_never_sniffed(m) {
            // 3.2. "If mimeType is an opaque-response-blocklisted-never-sniffed
            //      MIME type, then return false."
            Verdict::Blocked
        } else if response.status_line.status == 206 && is_opaque_response_blocklisted(m) {
            // 3.3. "If response's status is 206 and mimeType is an
            //      opaque-response-blocklisted MIME type, then return false."
            Verdict::Blocked
        } else if nosniff && (is_opaque_response_blocklisted(m) || clazel_mime::mime_type::spec::essence(m) == lit_text_plain()) {
            // 3.4. "If nosniff is true and mimeType is an
            //      opaque-response-blocklisted MIME type or its essence is
            //      "text/plain", then return false."
            Verdict::Blocked
        } else {
            check_from_step_4(response, mime_type, nosniff)
        },
        None => check_from_step_4(response, mime_type, nosniff),
    }
}

/// Steps 4 to 15 of the opaque-response-safelist check, with `mime_type`
/// and `nosniff` from steps 1 and 2.
pub open spec fn check_from_step_4(
    response: clazel_http::message::spec::Response,
    mime_type: Option<clazel_mime::mime_type::spec::MimeTypeRecord>,
    nosniff: bool,
) -> Verdict {
    let status = response.status_line.status;
    // 4. "If request's no-cors media request state is "subsequent", then
    //    return true." It is "N/A".
    if status == 206 {
        // 5. "If response's status is 206 and validate a partial response
        //    given 0 and response returns invalid, then return false." (Every
        //    206 is invalid here: see the modelling choices.)
        Verdict::Blocked
    } else {
        // 6. "Let bytes be the result of running obtain a copy of the first
        //    1024 bytes of response given response." 7. "If bytes is
        //    failure, then return false." (Never failure.)
        let bytes = first_1024_bytes(response.body);
        if clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(bytes) is Some {
            // 8. "If the audio or video type pattern matching algorithm
            //    given bytes does not return undefined, then:" 8.1. "If
            //    requests's no-cors media request state is not "initial",
            //    then return false." It is "N/A".
            Verdict::Blocked
        }
        // 9. "If requests's no-cors media request state is not "N/A", then
        //    return false." It is "N/A".
        else if clazel_mime::sniff::spec::image_type_pattern_matching(bytes) is Some {
            // 10. "If the image type pattern matching algorithm given bytes
            //     does not return undefined, then return true."
            Verdict::Allowed
        } else if nosniff {
            // 11. "If nosniff is true, then return false."
            Verdict::Blocked
        } else if !is_ok_status(status) {
            // 12. "If response's status is not an ok status, then return
            //     false."
            Verdict::Blocked
        } else {
            match mime_type {
                // 13. "If mimeType is failure, then return true."
                None => Verdict::Allowed,
                Some(m) => if starts_with(clazel_mime::mime_type::spec::essence(m), lit_audio_slash()) || starts_with(
                    clazel_mime::mime_type::spec::essence(m),
                    lit_image_slash(),
                ) || starts_with(clazel_mime::mime_type::spec::essence(m), lit_video_slash()) {
                    // 14. "If mimeType's essence starts with "audio/",
                    //     "image/", or "video/", then return false."
                    Verdict::Blocked
                } else {
                    // 15. "Return determine if response is JavaScript and not
                    //     JSON given response."
                    Verdict::JavaScriptCheck
                },
            }
        }
    }
}

// ===========================================================================
// Literals.
// ===========================================================================

/// "`content-type`".
pub open spec fn lit_content_type() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65]
}

/// "`x-content-type-options`".
pub open spec fn lit_x_content_type_options() -> Seq<u8> {
    seq![0x78u8, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65, 0x2D, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73]
}

/// "`nosniff`".
pub open spec fn lit_nosniff() -> Seq<u8> {
    seq![0x6Eu8, 0x6F, 0x73, 0x6E, 0x69, 0x66, 0x66]
}

/// "`*/*`".
pub open spec fn lit_any_any() -> Seq<u32> {
    seq![0x2Au32, 0x2F, 0x2A]
}

/// "`text/css`".
pub open spec fn lit_text_css() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x73]
}

/// "`image/svg+xml`".
pub open spec fn lit_image_svg_xml() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x61, 0x67, 0x65, 0x2F, 0x73, 0x76, 0x67, 0x2B, 0x78, 0x6D, 0x6C]
}

/// "`text/plain`".
pub open spec fn lit_text_plain() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E]
}

/// "`audio/`".
pub open spec fn lit_audio_slash() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F, 0x2F]
}

/// "`image/`".
pub open spec fn lit_image_slash() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x61, 0x67, 0x65, 0x2F]
}

/// "`video/`".
pub open spec fn lit_video_slash() -> Seq<u32> {
    seq![0x76u32, 0x69, 0x64, 0x65, 0x6F, 0x2F]
}

/// "`application/gzip`".
pub open spec fn lit_ns_application_gzip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x67, 0x7A, 0x69, 0x70]
}

/// "`application/msexcel`".
pub open spec fn lit_ns_application_msexcel() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x65, 0x78, 0x63, 0x65, 0x6C]
}

/// "`application/mspowerpoint`".
pub open spec fn lit_ns_application_mspowerpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/msword`".
pub open spec fn lit_ns_application_msword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/msword-template`".
pub open spec fn lit_ns_application_msword_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64, 0x2D, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/pdf`".
pub open spec fn lit_ns_application_pdf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66]
}

/// "`application/vnd.ces-quickpoint`".
pub open spec fn lit_ns_application_vnd_ces_quickpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/vnd.ces-quicksheet`".
pub open spec fn lit_ns_application_vnd_ces_quicksheet() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x73, 0x68, 0x65, 0x65, 0x74]
}

/// "`application/vnd.ces-quickword`".
pub open spec fn lit_ns_application_vnd_ces_quickword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.ms-excel`".
pub open spec fn lit_ns_application_vnd_ms_excel() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C]
}

/// "`application/vnd.ms-excel.sheet.macroenabled.12`".
pub open spec fn lit_ns_application_vnd_ms_excel_sheet_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-powerpoint`".
pub open spec fn lit_ns_application_vnd_ms_powerpoint() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74]
}

/// "`application/vnd.ms-powerpoint.presentation.macroenabled.12`".
pub open spec fn lit_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-word`".
pub open spec fn lit_ns_application_vnd_ms_word() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.ms-word.document.12`".
pub open spec fn lit_ns_application_vnd_ms_word_document_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.ms-word.document.macroenabled.12`".
pub open spec fn lit_ns_application_vnd_ms_word_document_macroenabled_12() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32]
}

/// "`application/vnd.msword`".
pub open spec fn lit_ns_application_vnd_msword() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64]
}

/// "`application/vnd.openxmlformats-officedocument.presentationml.presentation`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E]
}

/// "`application/vnd.openxmlformats-officedocument.presentationml.template`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_presentationml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.openxmlformats-officedocument.spreadsheetml.sheet`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74]
}

/// "`application/vnd.openxmlformats-officedocument.spreadsheetml.template`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.openxmlformats-officedocument.wordprocessingml.document`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74]
}

/// "`application/vnd.openxmlformats-officedocument.wordprocessingml.template`".
pub open spec fn lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65]
}

/// "`application/vnd.presentation-openxml`".
pub open spec fn lit_ns_application_vnd_presentation_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/vnd.presentation-openxmlm`".
pub open spec fn lit_ns_application_vnd_presentation_openxmlm() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x6D]
}

/// "`application/vnd.spreadsheet-openxml`".
pub open spec fn lit_ns_application_vnd_spreadsheet_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/vnd.wordprocessing-openxml`".
pub open spec fn lit_ns_application_vnd_wordprocessing_openxml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C]
}

/// "`application/x-gzip`".
pub open spec fn lit_ns_application_x_gzip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x67, 0x7A, 0x69, 0x70]
}

/// "`application/x-protobuf`".
pub open spec fn lit_ns_application_x_protobuf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66]
}

/// "`application/x-protobuffer`".
pub open spec fn lit_ns_application_x_protobuffer() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66, 0x66, 0x65, 0x72]
}

/// "`application/zip`".
pub open spec fn lit_ns_application_zip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x7A, 0x69, 0x70]
}

/// "`multipart/byteranges`".
pub open spec fn lit_ns_multipart_byteranges() -> Seq<u32> {
    seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x62, 0x79, 0x74, 0x65, 0x72, 0x61, 0x6E, 0x67, 0x65, 0x73]
}

/// "`multipart/signed`".
pub open spec fn lit_ns_multipart_signed() -> Seq<u32> {
    seq![0x6Du32, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x73, 0x69, 0x67, 0x6E, 0x65, 0x64]
}

/// "`text/event-stream`".
pub open spec fn lit_ns_text_event_stream() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x65, 0x76, 0x65, 0x6E, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D]
}

/// "`text/csv`".
pub open spec fn lit_ns_text_csv() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x76]
}

/// The essences of an opaque-response-blocklisted-never-sniffed MIME type
/// (§2.11.2), in the standard's order.
pub open spec fn never_sniffed_essences() -> Seq<Seq<u32>> {
    seq![
        lit_ns_application_gzip(),
        lit_ns_application_msexcel(),
        lit_ns_application_mspowerpoint(),
        lit_ns_application_msword(),
        lit_ns_application_msword_template(),
        lit_ns_application_pdf(),
        lit_ns_application_vnd_ces_quickpoint(),
        lit_ns_application_vnd_ces_quicksheet(),
        lit_ns_application_vnd_ces_quickword(),
        lit_ns_application_vnd_ms_excel(),
        lit_ns_application_vnd_ms_excel_sheet_macroenabled_12(),
        lit_ns_application_vnd_ms_powerpoint(),
        lit_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12(),
        lit_ns_application_vnd_ms_word(),
        lit_ns_application_vnd_ms_word_document_12(),
        lit_ns_application_vnd_ms_word_document_macroenabled_12(),
        lit_ns_application_vnd_msword(),
        lit_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation(),
        lit_ns_application_vnd_openxmlformats_officedocument_presentationml_template(),
        lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet(),
        lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template(),
        lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document(),
        lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template(),
        lit_ns_application_vnd_presentation_openxml(),
        lit_ns_application_vnd_presentation_openxmlm(),
        lit_ns_application_vnd_spreadsheet_openxml(),
        lit_ns_application_vnd_wordprocessing_openxml(),
        lit_ns_application_x_gzip(),
        lit_ns_application_x_protobuf(),
        lit_ns_application_x_protobuffer(),
        lit_ns_application_zip(),
        lit_ns_multipart_byteranges(),
        lit_ns_multipart_signed(),
        lit_ns_text_event_stream(),
        lit_ns_text_csv(),
    ]
}

} // verus!
