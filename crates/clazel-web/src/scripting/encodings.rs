//! The encoding functions the tree builder takes from other standards (its
//! `EncFnsExec`), and the decoding of a classic script's body.

use clazel_encoding::labels::exec::{get_an_encoding, number};
use clazel_encoding::labels::spec::Encoding;
use clazel_html::sniff::exec::extract_label_exec;
use clazel_mime::mime_type::parse::parse_from_bytes;
use clazel_treebuilder::exec::types::EncFnsExec;

/// Encoding §4.2 "get an encoding" (an encoding's id being its number in the
/// table) and HTML's "extracting a character encoding from a meta element",
/// as the renderer's pipeline gives them to the parser.
pub(crate) struct Encodings;

impl EncFnsExec for Encodings {
    fn get_an_encoding(&self, label: &[u32]) -> Option<u64> {
        get_an_encoding(label).map(|e| u64::from(number(e)))
    }

    fn extract_from_meta(&self, content: &[u32]) -> Option<Vec<u32>> {
        let bytes: Vec<u8> = content
            .iter()
            .map(|c| {
                u8::try_from(*c)
                    .ok()
                    .filter(|b| b.is_ascii())
                    .unwrap_or(0xFF)
            })
            .collect();
        extract_label_exec(&bytes).map(|l| l.into_iter().map(u32::from).collect())
    }
}

/// HTML §8.1.4.2† "fetch a classic script", processResponseConsumeBody
/// steps 3 to 5: "Let potentialMIMETypeForEncoding be the result of
/// extracting a MIME type given response's header list. Set encoding to the
/// result of legacy extracting an encoding given potentialMIMETypeForEncoding
/// and encoding. Let sourceText be the result of decoding bodyBytes to
/// Unicode, using encoding as the fallback encoding."
///
/// The header list is the one `Content-Type` value the kernel passes on.
/// "Legacy extracting an encoding" (Fetch §3.?†): the MIME type's `charset`
/// parameter, if "get an encoding" gives one for it, else the fallback.
/// "Decode" (Encoding §6†): a byte order mark wins. `None` if the encoding
/// has no decoder here.
pub(crate) fn decode_script(
    body: &[u8],
    content_type: &[u8],
    fallback: Encoding,
) -> Option<Vec<u32>> {
    let encoding = parse_from_bytes(content_type)
        .and_then(|mime| {
            mime.parameters
                .iter()
                .find(|(name, _)| name.iter().copied().eq("charset".chars().map(u32::from)))
                .and_then(|(_, value)| get_an_encoding(value))
        })
        .unwrap_or(fallback);
    clazel_encoding::hooks::decode::decode(body, encoding)
}

/// Whether the response's MIME type is a JavaScript MIME type (HTML §8.1.4.2†
/// "fetch a single module script" step: "If ... mimeType is a JavaScript MIME
/// type ...").
pub(crate) fn is_javascript_response(content_type: &[u8]) -> bool {
    parse_from_bytes(content_type).is_some_and(|mime| {
        let mut essence = mime.type_.clone();
        essence.push(u32::from('/'));
        essence.extend_from_slice(&mime.subtype);
        clazel_mime::mime_type::groups::is_javascript_mime_type_essence_match(&essence)
    })
}
