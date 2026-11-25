//! Facts about the opaque-response-safelist check that the standard states
//! or that its design rests on. They are evidence that [`super::spec`] is
//! the check its notes describe, and the mutations in `mutations.json` are
//! certified against them. Each is a statement about every response.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// ORB's note: "CSS, JavaScript, images, and media (audio and video) can be
/// requested across origins without the CORS protocol". A response whose
/// MIME type is opaque-response-safelisted (JavaScript, `text/css`,
/// `image/svg+xml`) is allowed whatever else it says (step 3.1).
pub proof fn lemma_safelisted_allowed(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is Some && is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0))
            ==> opaque_response_safelist_check(r) is Allowed,
{
}

/// A response whose MIME type is opaque-response-blocklisted-never-sniffed
/// (and not safelisted) is blocked, whatever its bytes are (step 3.2).
pub proof fn lemma_never_sniffed_blocked(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is Some && !is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0)
            && is_opaque_response_blocklisted_never_sniffed(extract_a_mime_type(r.fields)->Some_0)) ==> opaque_response_safelist_check(r) is Blocked,
{
}

/// The intranet case ORB exists for: an HTML, JSON or XML response (that is
/// not `image/svg+xml`, which is both XML and safelisted) never reaches the
/// page unless its first bytes sniff as an image. At best it reaches step
/// 15, the JavaScript check.
pub proof fn lemma_blocklisted_not_allowed(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is Some && !is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0)
            && is_opaque_response_blocklisted(extract_a_mime_type(r.fields)->Some_0) && clazel_mime::sniff::spec::image_type_pattern_matching(
            first_1024_bytes(r.body),
        ) is None) ==> !(opaque_response_safelist_check(r) is Allowed),
{
}

/// With `X-Content-Type-Options: nosniff`, an HTML, JSON or XML response
/// that is not safelisted is blocked outright, even if its bytes sniff as
/// an image (step 3.4, before the image sniffing of step 10).
pub proof fn lemma_nosniff_blocklisted_blocked(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is Some && !is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0)
            && is_opaque_response_blocklisted(extract_a_mime_type(r.fields)->Some_0) && determine_nosniff(r.fields))
            ==> opaque_response_safelist_check(r) is Blocked,
{
}

/// A 206 is blocked unless its MIME type is safelisted: no request here
/// carries `Range`, so no 206 is valid (steps 3.3 and 5, with the modelling
/// choice).
pub proof fn lemma_partial_blocked(r: clazel_http::message::spec::Response)
    ensures
        (r.status_line.status == 206 && !(extract_a_mime_type(r.fields) is Some && is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0)))
            ==> opaque_response_safelist_check(r) is Blocked,
{
}

/// Bytes that sniff as audio or video are blocked when the type does not
/// decide first: this client makes no media requests, so the no-cors media
/// request state is never "initial" (step 8.1).
pub proof fn lemma_media_bytes_blocked(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is None && clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(first_1024_bytes(r.body)) is Some)
            ==> opaque_response_safelist_check(r) is Blocked,
{
}

/// Bytes that sniff as an image are allowed when the type does not decide
/// first and the response is not a 206 (step 10): images are sniffed
/// whatever their type and `nosniff`, ORB's note on step 11.
pub proof fn lemma_image_bytes_allowed(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is None && r.status_line.status != 206 && clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(
            first_1024_bytes(r.body),
        ) is None && clazel_mime::sniff::spec::image_type_pattern_matching(first_1024_bytes(r.body)) is Some) ==> opaque_response_safelist_check(
            r,
        ) is Allowed,
{
}

/// A response with no usable MIME type, an ok status and no `nosniff`, whose
/// bytes do not sniff as media, is allowed (step 13: the case ORB leaves
/// open so that style sheets without a type keep working).
pub proof fn lemma_untyped_allowed(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is None && !determine_nosniff(r.fields) && is_ok_status(r.status_line.status) && r.status_line.status != 206
            && clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(first_1024_bytes(r.body)) is None) ==> opaque_response_safelist_check(
            r,
        ) is Allowed,
{
}

/// The check never allows a response with a usable MIME type that is not
/// safelisted and does not sniff as an image: anything else that is not
/// blocked waits for step 15, the JavaScript check.
pub proof fn lemma_typed_needs_js_check(r: clazel_http::message::spec::Response)
    ensures
        (extract_a_mime_type(r.fields) is Some && !is_opaque_response_safelisted(extract_a_mime_type(r.fields)->Some_0)
            && clazel_mime::sniff::spec::image_type_pattern_matching(first_1024_bytes(r.body)) is None) ==> !(opaque_response_safelist_check(
            r,
        ) is Allowed),
{
}

} // verus!
