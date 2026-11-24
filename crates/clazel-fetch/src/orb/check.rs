//! The executable opaque-response-safelist check, proven equal to
//! [`super::spec`] (with [`super::spec::kernel_model`]).

#[allow(unused_imports)]
use super::spec::*;
use super::tables::*;
use clazel_http::field::list::split_values;
use clazel_http::field::section::combined_field_value;
use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::types::ResponseBuf;
use clazel_mime::mime_type::groups;
use clazel_mime::mime_type::parse::parse_from_bytes;
use clazel_mime::mime_type::record::{MimeType, ascii_lowercase_exec};
use clazel_mime::sniff::algorithms::{match_audio_or_video_type_pattern, match_image_type_pattern};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Get, decode, and split" `name` from the header list.
pub fn get_decode_split_exec(fields: &[FieldLineBuf], name: &[u8]) -> (out: Option<Vec<Vec<u8>>>)
    ensures
        match out {
            Some(v) => get_decode_split(clazel_http::field::types::lines_view(fields@), name@) == Some(clazel_http::field::types::strings_view(v@)),
            None => get_decode_split(clazel_http::field::types::lines_view(fields@), name@) is None,
        },
{
    let v = combined_field_value(fields, name)?;
    Some(split_values(v.as_slice()))
}

/// "Extract a MIME type" from the header list (`None` is failure).
pub fn extract_mime_type_exec(fields: &[FieldLineBuf]) -> (out: Option<MimeType>)
    ensures
        super::contract::extract_mime_type_ensures(clazel_http::field::types::lines_view(fields@), clazel_mime::mime_type::record::option_view(out)),
{
    let name: [u8; 12] = [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65];
    assert(name@ =~= content_type_name());
    match get_decode_split_exec(fields, name.as_slice()) {
        None => None,
        Some(values) => {
            let ghost vs = clazel_http::field::types::strings_view(values@);
            let mut mime_type: Option<MimeType> = None;
            let mut i: usize = 0;
            proof {
                assert(vs.skip(0) =~= vs);
            }
            while i < values.len()
                invariant
                    i <= values.len(),
                    vs == clazel_http::field::types::strings_view(values@),
                    extract_from(vs, None) == extract_from(vs.skip(i as int), clazel_mime::mime_type::record::option_view(mime_type)),
                decreases values.len() - i,
            {
                if let Some(value) = values.get(i) {
                    let temporary = parse_from_bytes(value.as_slice());
                    proof {
                        assert(vs[i as int] == value@);
                        assert(vs.skip(i as int)[0] == vs[i as int]);
                        assert(vs.skip(i as int).drop_first() =~= vs.skip(i as int + 1));
                    }
                    if let Some(t) = temporary {
                        let e = t.essence();
                        if !eq_star_slash_star(e.as_slice()) {
                            mime_type = Some(t);
                        }
                    }
                }
                // Never saturates: i < values.len().
                i = i.saturating_add(1);
            }
            proof {
                assert(vs.skip(values.len() as int) =~= Seq::<Seq<u8>>::empty());
            }
            mime_type
        },
    }
}

/// The code points of `input`, as Isomorphic decode (Infra §4.5) gives them.
fn isomorphic_decode_exec(input: &[u8]) -> (out: Vec<u32>)
    ensures
        out@ == clazel_mime::mime_type::spec::isomorphic_decode(input@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            out@ == clazel_mime::mime_type::spec::isomorphic_decode(input@).subrange(0, i as int),
        decreases input.len() - i,
    {
        if let Some(b) = input.get(i) {
            out.push(*b as u32);
        }
        assert(out@ =~= clazel_mime::mime_type::spec::isomorphic_decode(input@).subrange(0, i as int + 1));
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    assert(out@ =~= clazel_mime::mime_type::spec::isomorphic_decode(input@));
    out
}

/// "Determine nosniff" of the header list.
pub fn determine_nosniff_exec(fields: &[FieldLineBuf]) -> (out: bool)
    ensures
        super::contract::determine_nosniff_ensures(clazel_http::field::types::lines_view(fields@), out),
{
    let name: [u8; 22] = [0x78, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65, 0x2D, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73];
    assert(name@ =~= x_content_type_options_name());
    match get_decode_split_exec(fields, name.as_slice()) {
        None => false,
        Some(values) => match values.first() {
            Some(first) => {
                let decoded = isomorphic_decode_exec(first.as_slice());
                let lower = ascii_lowercase_exec(decoded.as_slice());
                eq_nosniff(lower.as_slice())
            },
            None => false,
        },
    }
}

/// [`is_opaque_response_safelisted`].
fn is_safelisted_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_safelisted(m@),
{
    let e = m.essence();
    groups::is_javascript_mime_type(m) || is_safelisted_essence(e.as_slice())
}

/// [`is_opaque_response_blocklisted`].
fn is_blocklisted_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_blocklisted(m@),
{
    groups::is_html_mime_type(m) || groups::is_json_mime_type(m) || groups::is_xml_mime_type(m)
}

/// [`is_opaque_response_blocklisted_never_sniffed`].
fn is_never_sniffed_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_opaque_response_blocklisted_never_sniffed(m@),
{
    let e = m.essence();
    is_never_sniffed_essence(e.as_slice())
}

/// The opaque-response-safelist check with [`kernel_model`]: steps 1 to 15,
/// whose steps 13 and 15 refuse.
pub fn safelist_check_exec(response: &ResponseBuf) -> (r: bool)
    ensures
        super::contract::safelist_check_ensures(response@, r),
{
    let fields = response.fields.as_slice();
    // 1.
    let mime_type = extract_mime_type_exec(fields);
    // 2.
    let nosniff = determine_nosniff_exec(fields);
    let status = response.status_line.status;
    // 3.
    if let Some(m) = &mime_type {
        // 3.1.
        if is_safelisted_exec(m) {
            return true;
        }
        // 3.2.
        if is_never_sniffed_exec(m) {
            return false;
        }
        let blocklisted = is_blocklisted_exec(m);
        // 3.3.
        if status == 206 && blocklisted {
            return false;
        }
        // 3.4.
        if nosniff {
            let e = m.essence();
            if blocklisted || eq_text_plain(e.as_slice()) {
                return false;
            }
        }
    }
    // 5.
    if status == 206 {
        return false;
    }
    // 6.
    let body = response.body.as_slice();
    let bytes = if body.len() <= 8096 {
        body
    } else {
        vstd::slice::slice_subrange(body, 0, 8096)
    };
    proof {
        assert(bytes@ =~= first_bytes(response@.body));
    }
    // 8.
    if match_audio_or_video_type_pattern(bytes).is_some() {
        return true;
    }
    // 9.
    if match_image_type_pattern(bytes).is_some() {
        return true;
    }
    // 11. 12. 13. 14. 15.: with the kernel's model every remaining case is
    // false.
    false
}

/// [`orb_allows_given`].
pub fn orb_allows_exec(applies: bool, response: &ResponseBuf) -> (r: bool)
    ensures
        super::contract::orb_allows_ensures(applies, response@, r),
{
    !applies || safelist_check_exec(response)
}

} // verus!
