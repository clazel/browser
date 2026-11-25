//! Concrete responses, and what the check says of them, evaluated by Verus
//! (`compute_only`). The mutations' certificates use these responses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A field line.
pub open spec fn ex_line(name: Seq<u8>, value: Seq<u8>) -> clazel_http::field::spec::FieldLine {
    clazel_http::field::spec::FieldLine { name, value }
}

/// A response with status `status`, the given fields and body.
pub open spec fn ex_response(status: nat, fields: Seq<clazel_http::field::spec::FieldLine>, body: Seq<u8>) -> clazel_http::message::spec::Response {
    clazel_http::message::spec::Response {
        status_line: clazel_http::message::spec::StatusLine { major: 1, minor: 1, status, reason: Seq::<u8>::empty() },
        fields,
        body,
    }
}

/// `Content-Type: text/javascript`.
pub open spec fn ex_ct_javascript() -> clazel_http::field::spec::FieldLine {
    ex_line(
        seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65],
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74],
    )
}

/// `Content-Type: application/pdf`.
pub open spec fn ex_ct_pdf() -> clazel_http::field::spec::FieldLine {
    ex_line(
        seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65],
        seq![0x61u8, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66],
    )
}

/// `Content-Type: text/html`.
pub open spec fn ex_ct_html() -> clazel_http::field::spec::FieldLine {
    ex_line(seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65], seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x68, 0x74, 0x6D, 0x6C])
}

/// `Content-Type: text/html, text/plain`: two values, the last one wins.
pub open spec fn ex_ct_html_then_plain() -> clazel_http::field::spec::FieldLine {
    ex_line(
        seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65],
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x68, 0x74, 0x6D, 0x6C, 0x2C, 0x20, 0x74, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E],
    )
}

/// `X-Content-Type-Options: nosniff`.
pub open spec fn ex_nosniff() -> clazel_http::field::spec::FieldLine {
    ex_line(
        seq![0x58u8, 0x2D, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65, 0x2D, 0x4F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73],
        seq![0x4Eu8, 0x6F, 0x53, 0x6E, 0x69, 0x66, 0x66],
    )
}

/// `GIF89a`: the image type pattern for `image/gif`.
pub open spec fn ex_gif() -> Seq<u8> {
    seq![0x47u8, 0x49, 0x46, 0x38, 0x39, 0x61]
}

/// `ID3`: the audio type pattern for `audio/mpeg`.
pub open spec fn ex_id3() -> Seq<u8> {
    seq![0x49u8, 0x44, 0x33]
}

/// `x`: one byte that sniffs as nothing.
pub open spec fn ex_x() -> Seq<u8> {
    seq![0x78u8]
}

/// A script with a JavaScript type is allowed.
pub proof fn example_javascript_allowed()
    ensures
        opaque_response_safelist_check(ex_response(200, seq![ex_ct_javascript()], ex_x())) is Allowed,
{
    assert(opaque_response_safelist_check(ex_response(200, seq![ex_ct_javascript()], ex_x())) is Allowed) by (compute_only);
}

/// A PDF is blocked, even with a body that sniffs as an image.
pub proof fn example_pdf_blocked()
    ensures
        opaque_response_safelist_check(ex_response(200, seq![ex_ct_pdf()], ex_gif())) is Blocked,
{
    assert(opaque_response_safelist_check(ex_response(200, seq![ex_ct_pdf()], ex_gif())) is Blocked) by (compute_only);
}

/// HTML with `nosniff` is blocked, even with a body that sniffs as an
/// image.
pub proof fn example_html_nosniff_blocked()
    ensures
        opaque_response_safelist_check(ex_response(200, seq![ex_ct_html(), ex_nosniff()], ex_gif())) is Blocked,
{
    assert(opaque_response_safelist_check(ex_response(200, seq![ex_ct_html(), ex_nosniff()], ex_gif())) is Blocked) by (compute_only);
}

/// HTML without `nosniff` waits for the JavaScript check.
pub proof fn example_html_js_check()
    ensures
        opaque_response_safelist_check(ex_response(200, seq![ex_ct_html()], ex_x())) is JavaScriptCheck,
{
    assert(opaque_response_safelist_check(ex_response(200, seq![ex_ct_html()], ex_x())) is JavaScriptCheck) by (compute_only);
}

/// No type and image bytes: allowed.
pub proof fn example_untyped_gif_allowed()
    ensures
        opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_gif())) is Allowed,
{
    assert(opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_gif())) is Allowed)
        by (compute_only);
}

/// No type and audio bytes: blocked.
pub proof fn example_untyped_audio_blocked()
    ensures
        opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_id3())) is Blocked,
{
    assert(opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_id3())) is Blocked)
        by (compute_only);
}

/// A 206 without a type: blocked.
pub proof fn example_partial_blocked()
    ensures
        opaque_response_safelist_check(ex_response(206, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_x())) is Blocked,
{
    assert(opaque_response_safelist_check(ex_response(206, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_x())) is Blocked)
        by (compute_only);
}

/// No type, 200, no `nosniff`: allowed (step 13).
pub proof fn example_untyped_allowed()
    ensures
        opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_x())) is Allowed,
{
    assert(opaque_response_safelist_check(ex_response(200, Seq::<clazel_http::field::spec::FieldLine>::empty(), ex_x())) is Allowed)
        by (compute_only);
}

/// `X-Content-Type-Options: foo`.
pub open spec fn ex_options_foo() -> clazel_http::field::spec::FieldLine {
    ex_line(
        seq![0x58u8, 0x2D, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65, 0x2D, 0x4F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73],
        seq![0x66u8, 0x6F, 0x6F],
    )
}

/// `nosniff` is a value, not the header's presence (Fetch §3.6 step 3):
/// `X-Content-Type-Options: foo` is not nosniff, `NoSniff` is.
pub proof fn example_nosniff_value()
    ensures
        !determine_nosniff(seq![ex_options_foo()]),
        determine_nosniff(seq![ex_nosniff()]),
{
    assert(!determine_nosniff(seq![ex_options_foo()])) by (compute_only);
    assert(determine_nosniff(seq![ex_nosniff()])) by (compute_only);
}

/// Of `text/html, text/plain` the last value is the MIME type (Fetch
/// §3.5's loop sets mimeType on every valid value).
pub proof fn example_extract_last_wins()
    ensures
        extract_a_mime_type(seq![ex_ct_html_then_plain()]) is Some && clazel_mime::mime_type::spec::essence(
            extract_a_mime_type(seq![ex_ct_html_then_plain()])->Some_0,
        ) == lit_text_plain(),
{
    assert(extract_a_mime_type(seq![ex_ct_html_then_plain()]) is Some && clazel_mime::mime_type::spec::essence(
        extract_a_mime_type(seq![ex_ct_html_then_plain()])->Some_0,
    ) == lit_text_plain()) by (compute_only);
}

} // verus!
