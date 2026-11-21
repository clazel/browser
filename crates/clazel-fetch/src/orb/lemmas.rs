//! Facts proven about [`super::spec`]: `theorem_orb` and the lemmas that show
//! the kernel's model refuses at least what the standard refuses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a response that ORB lets through to a renderer must be: its declared
/// type is an opaque-response-safelisted MIME type, or it is not a partial
/// response and its first bytes sniff as audio, video or an image.
pub open spec fn typed_allowed(response: clazel_http::message::spec::Response) -> bool {
    let mime_type = extract_mime_type(response.fields);
    (mime_type is Some && is_opaque_response_safelisted(mime_type->Some_0)) || (response.status_line.status != 206 && (
    clazel_mime::sniff::spec::audio_or_video_type_pattern_matching(first_bytes(response.body)) is Some
        || clazel_mime::sniff::spec::image_type_pattern_matching(first_bytes(response.body)) is Some))
}

/// **`theorem_orb`** (decision 6.0(i) B; Fetch's opaque-response-safelist
/// check, which Main fetch applies to a "no-cors" response with response
/// tainting "opaque"): a response to which ORB applies, that the kernel lets
/// through, has a safelisted declared type or sniffs as an image or as audio
/// or video. Every other cross-origin response (an HTML, JSON or XML page,
/// text, a type that is none of these, a response with no type whose bytes
/// are not an image) is refused, and the kernel turns a refused response into
/// a failure that carries no body octet (`clazel-kernel`'s `theorem_orb`
/// states that for the frames).
pub proof fn theorem_orb(lock: clazel_origin::spec::Origin, response_origin: clazel_origin::spec::Origin, response: clazel_http::message::spec::Response)
    requires
        orb_applies(lock, response_origin),
        orb_allows(lock, response_origin, response),
    ensures
        typed_allowed(response),
{
}

/// A response ORB does not apply to is let through.
pub proof fn lemma_same_origin_allowed(lock: clazel_origin::spec::Origin, response_origin: clazel_origin::spec::Origin, response: clazel_http::message::spec::Response)
    requires
        !orb_applies(lock, response_origin),
    ensures
        orb_allows(lock, response_origin, response),
{
}

/// The kernel's model refuses at least what the standard refuses: if the
/// kernel's check returns true, so does the standard's, whatever its step 15
/// (JavaScript and not JSON) answers.
pub proof fn lemma_kernel_refines_standard(js_not_json: bool, status: nat, fields: Seq<clazel_http::field::spec::FieldLine>, body: Seq<u8>)
    requires
        opaque_response_safelist_check(kernel_model(), status, fields, body),
    ensures
        opaque_response_safelist_check(spec_model(js_not_json), status, fields, body),
{
}

/// The octets the check reads are a prefix of the body, of at most
/// [`first_bytes_len`].
pub proof fn lemma_first_bytes(body: Seq<u8>)
    ensures
        first_bytes(body).len() <= first_bytes_len(),
        first_bytes(body) =~= body.subrange(0, first_bytes(body).len() as int),
{
}

/// A partial response is never let through on its bytes.
pub proof fn lemma_partial_needs_declared_type(lock: clazel_origin::spec::Origin, response_origin: clazel_origin::spec::Origin, response: clazel_http::message::spec::Response)
    requires
        orb_applies(lock, response_origin),
        response.status_line.status == 206,
        orb_allows(lock, response_origin, response),
    ensures
        extract_mime_type(response.fields) is Some,
        is_opaque_response_safelisted(extract_mime_type(response.fields)->Some_0),
{
}

} // verus!
