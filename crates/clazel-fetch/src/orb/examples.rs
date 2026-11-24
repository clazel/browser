//! Concrete responses the check is evaluated on (each is also a certificate
//! for a mutation in `mutations.json`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The eight octets of a PNG signature, which the image type pattern
/// matching algorithm (MIME Sniffing §6.1) recognises.
pub open spec fn png() -> Seq<u8> {
    seq![0x89u8, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]
}

/// "nosniff".
pub open spec fn nosniff_value() -> Seq<u8> {
    seq![0x6Eu8, 0x6F, 0x73, 0x6E, 0x69, 0x66, 0x66]
}

/// "text/css".
pub open spec fn text_css() -> Seq<u8> {
    seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x73]
}

/// "text/html".
pub open spec fn text_html() -> Seq<u8> {
    seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x68, 0x74, 0x6D, 0x6C]
}

/// "application/pdf".
pub open spec fn application_pdf() -> Seq<u8> {
    seq![0x61u8, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66]
}

/// "image/png".
pub open spec fn image_png() -> Seq<u8> {
    seq![0x69u8, 0x6D, 0x61, 0x67, 0x65, 0x2F, 0x70, 0x6E, 0x67]
}

/// A `Content-Type` field line.
pub open spec fn content_type(value: Seq<u8>) -> clazel_http::field::spec::FieldLine {
    clazel_http::field::spec::FieldLine { name: content_type_name(), value }
}

/// An `X-Content-Type-Options: nosniff` field line.
pub open spec fn nosniff_line() -> clazel_http::field::spec::FieldLine {
    clazel_http::field::spec::FieldLine { name: x_content_type_options_name(), value: nosniff_value() }
}

/// What the kernel's check says of a response with this status, these field
/// lines and this body.
pub open spec fn kernel_says(status: nat, fields: Seq<clazel_http::field::spec::FieldLine>, body: Seq<u8>) -> bool {
    opaque_response_safelist_check(kernel_model(), status, fields, body)
}

/// Step 3.1: a style sheet type is let through, whatever the body.
pub proof fn lemma_example_safelisted()
    ensures
        kernel_says(200, seq![content_type(text_css())], seq![]),
{
    assert(kernel_says(200, seq![content_type(text_css())], seq![])) by (compute_only);
}

/// Step 3.2: a PDF is refused although its bytes are those of a PNG.
pub proof fn lemma_example_never_sniffed()
    ensures
        !kernel_says(200, seq![content_type(application_pdf())], png()),
{
    assert(!kernel_says(200, seq![content_type(application_pdf())], png())) by (compute_only);
}

/// Step 3.4: an HTML page with `nosniff` is refused although its bytes are
/// those of a PNG.
pub proof fn lemma_example_nosniff_html()
    ensures
        !kernel_says(200, seq![content_type(text_html()), nosniff_line()], png()),
{
    assert(!kernel_says(200, seq![content_type(text_html()), nosniff_line()], png())) by (compute_only);
}

/// Step 9: a mislabeled PNG, without `nosniff`, is let through (WPT
/// `img-png-mislabeled-as-html`), and so is an unlabeled one (WPT
/// `img-png-unlabeled`).
pub proof fn lemma_example_sniffed_image()
    ensures
        kernel_says(200, seq![content_type(text_html())], png()),
        kernel_says(200, seq![], png()),
{
    assert(kernel_says(200, seq![content_type(text_html())], png())) by (compute_only);
    assert(kernel_says(200, seq![], png())) by (compute_only);
}

/// Step 5 (as modelled): a partial response with a PNG's bytes and no
/// safelisted type is refused.
pub proof fn lemma_example_partial()
    ensures
        !kernel_says(206, seq![content_type(image_png())], png()),
{
    assert(!kernel_says(206, seq![content_type(image_png())], png())) by (compute_only);
}

/// Steps 13 and 15 (the kernel's model): a response with no type whose bytes
/// are not an image is refused; the standard would let it through.
pub proof fn lemma_example_unknown_refused()
    ensures
        !kernel_says(200, seq![], seq![0x3Cu8, 0x68, 0x74, 0x6D, 0x6C, 0x3E]),
        opaque_response_safelist_check(spec_model(false), 200, seq![], seq![0x3Cu8, 0x68, 0x74, 0x6D, 0x6C, 0x3E]),
{
    assert(!kernel_says(200, seq![], seq![0x3Cu8, 0x68, 0x74, 0x6D, 0x6C, 0x3E])) by (compute_only);
    assert(opaque_response_safelist_check(spec_model(false), 200, seq![], seq![0x3Cu8, 0x68, 0x74, 0x6D, 0x6C, 0x3E])) by (compute_only);
}

} // verus!
