//! The executable opaque-response-safelist check, proven to meet
//! [`super::contract`]. Each function's `ensures` says it equals its spec
//! function on the views.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::field::types::FieldLineBuf;
use clazel_mime::mime_type::record::{MimeType, slice_eq};

verus! {

/// The view of an optional list of byte strings.
pub open spec fn values_view(v: Option<Vec<Vec<u8>>>) -> Option<Seq<Seq<u8>>> {
    match v {
        Some(v) => Some(clazel_http::field::types::strings_view(v@)),
        None => None,
    }
}

/// [`get_decode_split`].
pub fn get_decode_split_exec(fields: &[FieldLineBuf], name: &[u8]) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        values_view(r) == get_decode_split(clazel_http::field::types::lines_view(fields@), name@),
{
    let combined = clazel_http::field::section::combined_field_value(fields, name);
    if let Some(v) = combined {
        return Some(clazel_http::field::list::split_values(v.as_slice()));
    }
    None
}

/// Extract a MIME type (Fetch §3.5); `None` is failure.
pub fn extract_a_mime_type(fields: &[FieldLineBuf]) -> (r: Option<MimeType>)
    ensures
        super::contract::extract_ensures(clazel_http::field::types::lines_view(fields@), clazel_mime::mime_type::record::option_view(r)),
{
    let name: [u8; 12] = [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65];
    assert(name@ =~= lit_content_type());
    match get_decode_split_exec(fields, &name) {
        None => None,
        Some(values) => extract_from_values(values),
    }
}

/// Extract a MIME type (Fetch §3.5), steps 6 to 8, over the values of
/// `Content-Type`.
fn extract_from_values(values: Vec<Vec<u8>>) -> (r: Option<MimeType>)
    ensures
        clazel_mime::mime_type::record::option_view(r) == extract_loop(clazel_http::field::types::strings_view(values@), 0, None),
{
    let ghost vs = clazel_http::field::types::strings_view(values@);
    let any: [u32; 3] = [0x2A, 0x2F, 0x2A];
    assert(any@ =~= lit_any_any());
    let mut mime_type: Option<MimeType> = None;
    let mut i: usize = 0;
    while i < values.len()
        invariant
            i <= values.len(),
            vs == clazel_http::field::types::strings_view(values@),
            any@ == lit_any_any(),
            extract_loop(vs, 0, None) == extract_loop(vs, i as nat, clazel_mime::mime_type::record::option_view(mime_type)),
        decreases values.len() - i,
    {
        if let Some(v) = values.get(i) {
            proof {
                assert(vs[i as int] == v@);
            }
            match clazel_mime::mime_type::parse::parse_from_bytes(v.as_slice()) {
                None => {},
                Some(t) => {
                    let e = t.essence();
                    if !slice_eq(e.as_slice(), any.as_slice()) {
                        mime_type = Some(t);
                    }
                },
            }
        }
        // Never saturates: i < values.len().
        i = i.saturating_add(1);
    }
    mime_type
}

/// Determine nosniff (Fetch §3.6).
pub fn determine_nosniff(fields: &[FieldLineBuf]) -> (r: bool)
    ensures
        super::contract::nosniff_ensures(clazel_http::field::types::lines_view(fields@), r),
{
    let name: [u8; 22] = [
        0x78, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65, 0x2D, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73,
    ];
    assert(name@ =~= lit_x_content_type_options());
    match get_decode_split_exec(fields, &name) {
        None => false,
        Some(values) => {
            let lit: [u8; 7] = [0x6E, 0x6F, 0x73, 0x6E, 0x69, 0x66, 0x66];
            assert(lit@ =~= lit_nosniff());
            proof {
                assert(clazel_http::field::spec::ascii_lowercase(lit_nosniff()) =~= lit_nosniff());
            }
            match values.first() {
                None => false,
                Some(first) => {
                    proof {
                        assert(clazel_http::field::types::strings_view(values@)[0] == first@);
                    }
                    clazel_http::field::string::field_name_eq(first.as_slice(), &lit)
                },
            }
        },
    }
}

/// Infra "starts with".
fn starts_with_exec(s: &[u32], p: &[u32]) -> (r: bool)
    ensures
        r == starts_with(s@, p@),
{
    if p.len() > s.len() {
        return false;
    }
    let head = vstd::slice::slice_subrange(s, 0, p.len());
    assert(head@ =~= s@.take(p.len() as int));
    slice_eq(head, p)
}

/// An opaque-response-safelisted MIME type (§2.11.2).
fn is_safelisted_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_safelisted(m@),
{
    let e = m.essence();
    let css: [u32; 8] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x73];
    assert(css@ =~= lit_text_css());
    let svg: [u32; 13] = [0x69, 0x6D, 0x61, 0x67, 0x65, 0x2F, 0x73, 0x76, 0x67, 0x2B, 0x78, 0x6D, 0x6C];
    assert(svg@ =~= lit_image_svg_xml());
    clazel_mime::mime_type::groups::is_javascript_mime_type(m) || slice_eq(e.as_slice(), css.as_slice()) || slice_eq(e.as_slice(), svg.as_slice())
}

/// An opaque-response-blocklisted MIME type (§2.11.2).
fn is_blocklisted_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_blocklisted(m@),
{
    clazel_mime::mime_type::groups::is_html_mime_type(m) || clazel_mime::mime_type::groups::is_json_mime_type(m)
        || clazel_mime::mime_type::groups::is_xml_mime_type(m)
}

/// Is `m`'s essence "text/plain"?
fn is_text_plain_exec(m: &MimeType) -> (r: bool)
    ensures
        r == (clazel_mime::mime_type::spec::essence(m@) == lit_text_plain()),
{
    let e = m.essence();
    let lit: [u32; 10] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E];
    assert(lit@ =~= lit_text_plain());
    slice_eq(e.as_slice(), lit.as_slice())
}

/// Does `m`'s essence start with "audio/", "image/" or "video/" (step 14)?
fn is_media_essence_exec(m: &MimeType) -> (r: bool)
    ensures
        r == (starts_with(clazel_mime::mime_type::spec::essence(m@), lit_audio_slash()) || starts_with(
            clazel_mime::mime_type::spec::essence(m@),
            lit_image_slash(),
        ) || starts_with(clazel_mime::mime_type::spec::essence(m@), lit_video_slash())),
{
    let e = m.essence();
    let audio: [u32; 6] = [0x61, 0x75, 0x64, 0x69, 0x6F, 0x2F];
    assert(audio@ =~= lit_audio_slash());
    let image: [u32; 6] = [0x69, 0x6D, 0x61, 0x67, 0x65, 0x2F];
    assert(image@ =~= lit_image_slash());
    let video: [u32; 6] = [0x76, 0x69, 0x64, 0x65, 0x6F, 0x2F];
    assert(video@ =~= lit_video_slash());
    starts_with_exec(e.as_slice(), audio.as_slice()) || starts_with_exec(e.as_slice(), image.as_slice()) || starts_with_exec(e.as_slice(), video.as_slice())
}

/// The opaque-response-safelist check (ORB §2.11.1).
pub fn opaque_response_safelist_check(response: &clazel_http::message::types::ResponseBuf) -> (r: Verdict)
    ensures
        super::contract::safelist_check_ensures(response@, r),
{
    let mime_type = extract_a_mime_type(response.fields.as_slice());
    let nosniff = determine_nosniff(response.fields.as_slice());
    let status = response.status_line.status;
    if let Some(m) = &mime_type {
        if is_safelisted_exec(m) {
            return Verdict::Allowed;
        }
        if is_never_sniffed_exec(m) {
            return Verdict::Blocked;
        }
        if status == 206 && is_blocklisted_exec(m) {
            return Verdict::Blocked;
        }
        if nosniff && (is_blocklisted_exec(m) || is_text_plain_exec(m)) {
            return Verdict::Blocked;
        }
    }
    check_from_step_4_exec(response, &mime_type, nosniff)
}

/// Steps 4 to 15 of the check.
fn check_from_step_4_exec(response: &clazel_http::message::types::ResponseBuf, mime_type: &Option<MimeType>, nosniff: bool) -> (r: Verdict)
    ensures
        r == check_from_step_4(response@, clazel_mime::mime_type::record::option_view(*mime_type), nosniff),
{
    let status = response.status_line.status;
    if status == 206 {
        return Verdict::Blocked;
    }
    let n = if response.body.len() <= 1024 {
        response.body.len()
    } else {
        1024
    };
    let bytes = vstd::slice::slice_subrange(response.body.as_slice(), 0, n);
    assert(bytes@ =~= first_1024_bytes(response.body@));
    if clazel_mime::sniff::algorithms::match_audio_or_video_type_pattern(bytes).is_some() {
        return Verdict::Blocked;
    }
    if clazel_mime::sniff::algorithms::match_image_type_pattern(bytes).is_some() {
        return Verdict::Allowed;
    }
    if nosniff {
        return Verdict::Blocked;
    }
    // 12. Not an ok status (200 to 299).
    if status < 200 {
        return Verdict::Blocked;
    }
    if status > 299 {
        return Verdict::Blocked;
    }
    match mime_type {
        None => Verdict::Allowed,
        Some(m) => if is_media_essence_exec(m) {
            Verdict::Blocked
        } else {
            Verdict::JavaScriptCheck
        },
    }
}

/// An opaque-response-blocklisted-never-sniffed MIME type (§2.11.2).
fn is_never_sniffed_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_blocklisted_never_sniffed(m@),
{
    let e = m.essence();
    let e = e.as_slice();
    proof {
        reveal_with_fuel(clazel_mime::mime_type::spec::is_one_of, 36);
    }
    eq_ns_application_gzip(e)
        || eq_ns_application_msexcel(e)
        || eq_ns_application_mspowerpoint(e)
        || eq_ns_application_msword(e)
        || eq_ns_application_msword_template(e)
        || eq_ns_application_pdf(e)
        || eq_ns_application_vnd_ces_quickpoint(e)
        || eq_ns_application_vnd_ces_quicksheet(e)
        || eq_ns_application_vnd_ces_quickword(e)
        || eq_ns_application_vnd_ms_excel(e)
        || eq_ns_application_vnd_ms_excel_sheet_macroenabled_12(e)
        || eq_ns_application_vnd_ms_powerpoint(e)
        || eq_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12(e)
        || eq_ns_application_vnd_ms_word(e)
        || eq_ns_application_vnd_ms_word_document_12(e)
        || eq_ns_application_vnd_ms_word_document_macroenabled_12(e)
        || eq_ns_application_vnd_msword(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_presentationml_template(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document(e)
        || eq_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template(e)
        || eq_ns_application_vnd_presentation_openxml(e)
        || eq_ns_application_vnd_presentation_openxmlm(e)
        || eq_ns_application_vnd_spreadsheet_openxml(e)
        || eq_ns_application_vnd_wordprocessing_openxml(e)
        || eq_ns_application_x_gzip(e)
        || eq_ns_application_x_protobuf(e)
        || eq_ns_application_x_protobuffer(e)
        || eq_ns_application_zip(e)
        || eq_ns_multipart_byteranges(e)
        || eq_ns_multipart_signed(e)
        || eq_ns_text_event_stream(e)
        || eq_ns_text_csv(e)
}

// The never-sniffed essences, as exec comparisons (one per `lit_ns_*`).

/// Is `s` "`application/gzip`"?
fn eq_ns_application_gzip(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_gzip()),
{
    let lit: [u32; 16] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x67, 0x7A, 0x69, 0x70];
    assert(lit@ =~= lit_ns_application_gzip());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/msexcel`"?
fn eq_ns_application_msexcel(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_msexcel()),
{
    let lit: [u32; 19] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x65, 0x78, 0x63, 0x65, 0x6C];
    assert(lit@ =~= lit_ns_application_msexcel());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/mspowerpoint`"?
fn eq_ns_application_mspowerpoint(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_mspowerpoint()),
{
    let lit: [u32; 24] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74];
    assert(lit@ =~= lit_ns_application_mspowerpoint());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/msword`"?
fn eq_ns_application_msword(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_msword()),
{
    let lit: [u32; 18] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64];
    assert(lit@ =~= lit_ns_application_msword());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/msword-template`"?
fn eq_ns_application_msword_template(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_msword_template()),
{
    let lit: [u32; 27] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64, 0x2D, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65];
    assert(lit@ =~= lit_ns_application_msword_template());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/pdf`"?
fn eq_ns_application_pdf(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_pdf()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66];
    assert(lit@ =~= lit_ns_application_pdf());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ces-quickpoint`"?
fn eq_ns_application_vnd_ces_quickpoint(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ces_quickpoint()),
{
    let lit: [u32; 30] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x70, 0x6F, 0x69, 0x6E, 0x74];
    assert(lit@ =~= lit_ns_application_vnd_ces_quickpoint());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ces-quicksheet`"?
fn eq_ns_application_vnd_ces_quicksheet(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ces_quicksheet()),
{
    let lit: [u32; 30] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x73, 0x68, 0x65, 0x65, 0x74];
    assert(lit@ =~= lit_ns_application_vnd_ces_quicksheet());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ces-quickword`"?
fn eq_ns_application_vnd_ces_quickword(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ces_quickword()),
{
    let lit: [u32; 29] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x63, 0x65, 0x73, 0x2D, 0x71, 0x75, 0x69, 0x63, 0x6B, 0x77, 0x6F, 0x72, 0x64];
    assert(lit@ =~= lit_ns_application_vnd_ces_quickword());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-excel`"?
fn eq_ns_application_vnd_ms_excel(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_excel()),
{
    let lit: [u32; 24] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C];
    assert(lit@ =~= lit_ns_application_vnd_ms_excel());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-excel.sheet.macroenabled.12`"?
fn eq_ns_application_vnd_ms_excel_sheet_macroenabled_12(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_excel_sheet_macroenabled_12()),
{
    let lit: [u32; 46] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x65, 0x78, 0x63, 0x65, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32];
    assert(lit@ =~= lit_ns_application_vnd_ms_excel_sheet_macroenabled_12());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-powerpoint`"?
fn eq_ns_application_vnd_ms_powerpoint(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_powerpoint()),
{
    let lit: [u32; 29] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74];
    assert(lit@ =~= lit_ns_application_vnd_ms_powerpoint());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-powerpoint.presentation.macroenabled.12`"?
fn eq_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12()),
{
    let lit: [u32; 58] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x70, 0x6F, 0x77, 0x65, 0x72, 0x70, 0x6F, 0x69, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32];
    assert(lit@ =~= lit_ns_application_vnd_ms_powerpoint_presentation_macroenabled_12());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-word`"?
fn eq_ns_application_vnd_ms_word(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_word()),
{
    let lit: [u32; 23] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64];
    assert(lit@ =~= lit_ns_application_vnd_ms_word());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-word.document.12`"?
fn eq_ns_application_vnd_ms_word_document_12(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_word_document_12()),
{
    let lit: [u32; 35] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x31, 0x32];
    assert(lit@ =~= lit_ns_application_vnd_ms_word_document_12());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-word.document.macroenabled.12`"?
fn eq_ns_application_vnd_ms_word_document_macroenabled_12(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_ms_word_document_macroenabled_12()),
{
    let lit: [u32; 48] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x77, 0x6F, 0x72, 0x64, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x6D, 0x61, 0x63, 0x72, 0x6F, 0x65, 0x6E, 0x61, 0x62, 0x6C, 0x65, 0x64, 0x2E, 0x31, 0x32];
    assert(lit@ =~= lit_ns_application_vnd_ms_word_document_macroenabled_12());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.msword`"?
fn eq_ns_application_vnd_msword(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_msword()),
{
    let lit: [u32; 22] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x77, 0x6F, 0x72, 0x64];
    assert(lit@ =~= lit_ns_application_vnd_msword());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.presentationml.presentation`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation()),
{
    let lit: [u32; 73] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_presentationml_presentation());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.presentationml.template`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_presentationml_template(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_presentationml_template()),
{
    let lit: [u32; 69] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_presentationml_template());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.spreadsheetml.sheet`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet()),
{
    let lit: [u32; 65] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x73, 0x68, 0x65, 0x65, 0x74];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_sheet());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.spreadsheetml.template`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template()),
{
    let lit: [u32; 68] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_spreadsheetml_template());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.wordprocessingml.document`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document()),
{
    let lit: [u32; 71] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_document());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.openxmlformats-officedocument.wordprocessingml.template`"?
fn eq_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template()),
{
    let lit: [u32; 71] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x66, 0x6F, 0x72, 0x6D, 0x61, 0x74, 0x73, 0x2D, 0x6F, 0x66, 0x66, 0x69, 0x63, 0x65, 0x64, 0x6F, 0x63, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x6D, 0x6C, 0x2E, 0x74, 0x65, 0x6D, 0x70, 0x6C, 0x61, 0x74, 0x65];
    assert(lit@ =~= lit_ns_application_vnd_openxmlformats_officedocument_wordprocessingml_template());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.presentation-openxml`"?
fn eq_ns_application_vnd_presentation_openxml(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_presentation_openxml()),
{
    let lit: [u32; 36] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C];
    assert(lit@ =~= lit_ns_application_vnd_presentation_openxml());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.presentation-openxmlm`"?
fn eq_ns_application_vnd_presentation_openxmlm(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_presentation_openxmlm()),
{
    let lit: [u32; 37] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x70, 0x72, 0x65, 0x73, 0x65, 0x6E, 0x74, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C, 0x6D];
    assert(lit@ =~= lit_ns_application_vnd_presentation_openxmlm());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.spreadsheet-openxml`"?
fn eq_ns_application_vnd_spreadsheet_openxml(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_spreadsheet_openxml()),
{
    let lit: [u32; 35] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x73, 0x70, 0x72, 0x65, 0x61, 0x64, 0x73, 0x68, 0x65, 0x65, 0x74, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C];
    assert(lit@ =~= lit_ns_application_vnd_spreadsheet_openxml());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.wordprocessing-openxml`"?
fn eq_ns_application_vnd_wordprocessing_openxml(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_vnd_wordprocessing_openxml()),
{
    let lit: [u32; 38] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x77, 0x6F, 0x72, 0x64, 0x70, 0x72, 0x6F, 0x63, 0x65, 0x73, 0x73, 0x69, 0x6E, 0x67, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x78, 0x6D, 0x6C];
    assert(lit@ =~= lit_ns_application_vnd_wordprocessing_openxml());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-gzip`"?
fn eq_ns_application_x_gzip(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_x_gzip()),
{
    let lit: [u32; 18] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x67, 0x7A, 0x69, 0x70];
    assert(lit@ =~= lit_ns_application_x_gzip());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-protobuf`"?
fn eq_ns_application_x_protobuf(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_x_protobuf()),
{
    let lit: [u32; 22] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66];
    assert(lit@ =~= lit_ns_application_x_protobuf());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-protobuffer`"?
fn eq_ns_application_x_protobuffer(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_x_protobuffer()),
{
    let lit: [u32; 25] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x70, 0x72, 0x6F, 0x74, 0x6F, 0x62, 0x75, 0x66, 0x66, 0x65, 0x72];
    assert(lit@ =~= lit_ns_application_x_protobuffer());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/zip`"?
fn eq_ns_application_zip(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_application_zip()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x7A, 0x69, 0x70];
    assert(lit@ =~= lit_ns_application_zip());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`multipart/byteranges`"?
fn eq_ns_multipart_byteranges(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_multipart_byteranges()),
{
    let lit: [u32; 20] = [0x6D, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x62, 0x79, 0x74, 0x65, 0x72, 0x61, 0x6E, 0x67, 0x65, 0x73];
    assert(lit@ =~= lit_ns_multipart_byteranges());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`multipart/signed`"?
fn eq_ns_multipart_signed(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_multipart_signed()),
{
    let lit: [u32; 16] = [0x6D, 0x75, 0x6C, 0x74, 0x69, 0x70, 0x61, 0x72, 0x74, 0x2F, 0x73, 0x69, 0x67, 0x6E, 0x65, 0x64];
    assert(lit@ =~= lit_ns_multipart_signed());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/event-stream`"?
fn eq_ns_text_event_stream(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_text_event_stream()),
{
    let lit: [u32; 17] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x65, 0x76, 0x65, 0x6E, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D];
    assert(lit@ =~= lit_ns_text_event_stream());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/csv`"?
fn eq_ns_text_csv(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_ns_text_csv()),
{
    let lit: [u32; 8] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x63, 0x73, 0x76];
    assert(lit@ =~= lit_ns_text_csv());
    slice_eq(s, lit.as_slice())
}

} // verus!
