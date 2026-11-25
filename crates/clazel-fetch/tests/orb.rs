//! The executable opaque-response-safelist check on responses written out
//! by hand: one per step of the check that can decide, and every
//! opaque-response-blocklisted-never-sniffed essence (the list typed here
//! from whatwg/fetch pull request #1442, independently of the spec's hex
//! literals).

use clazel_fetch::orb::check::opaque_response_safelist_check;
use clazel_fetch::orb::spec::Verdict;
use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::types::{ResponseBuf, StatusLineBuf};

fn response(status: u16, fields: &[(&str, &str)], body: &[u8]) -> ResponseBuf {
    ResponseBuf {
        status_line: StatusLineBuf {
            major: 1,
            minor: 1,
            status,
            reason: Vec::new(),
        },
        fields: fields
            .iter()
            .map(|(n, v)| FieldLineBuf {
                name: n.as_bytes().to_vec(),
                value: v.as_bytes().to_vec(),
            })
            .collect(),
        body: body.to_vec(),
    }
}

fn check(status: u16, fields: &[(&str, &str)], body: &[u8]) -> Verdict {
    opaque_response_safelist_check(&response(status, fields, body))
}

const GIF: &[u8] = b"GIF89a\x01\x00\x01\x00";
const ID3: &[u8] = b"ID3\x03\x00";

#[test]
fn safelisted_types_are_allowed() {
    // Step 3.1, whatever the bytes, status or nosniff.
    for t in [
        "text/javascript",
        "application/javascript; charset=utf-8",
        "TEXT/CSS",
        "image/svg+xml",
        "text/ecmascript",
    ] {
        assert_eq!(
            check(200, &[("Content-Type", t)], b"<html>"),
            Verdict::Allowed,
            "{t}"
        );
        assert_eq!(
            check(
                404,
                &[("content-type", t), ("X-Content-Type-Options", "nosniff")],
                ID3
            ),
            Verdict::Allowed,
            "{t}"
        );
        assert_eq!(
            check(206, &[("Content-Type", t)], b""),
            Verdict::Allowed,
            "{t}"
        );
    }
}

#[test]
fn never_sniffed_types_are_blocked() {
    // Step 3.2, even when the bytes are an image.
    let list = [
        "application/gzip",
        "application/msexcel",
        "application/mspowerpoint",
        "application/msword",
        "application/msword-template",
        "application/pdf",
        "application/vnd.ces-quickpoint",
        "application/vnd.ces-quicksheet",
        "application/vnd.ces-quickword",
        "application/vnd.ms-excel",
        "application/vnd.ms-excel.sheet.macroenabled.12",
        "application/vnd.ms-powerpoint",
        "application/vnd.ms-powerpoint.presentation.macroenabled.12",
        "application/vnd.ms-word",
        "application/vnd.ms-word.document.12",
        "application/vnd.ms-word.document.macroenabled.12",
        "application/vnd.msword",
        "application/vnd.openxmlformats-officedocument.presentationml.presentation",
        "application/vnd.openxmlformats-officedocument.presentationml.template",
        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        "application/vnd.openxmlformats-officedocument.spreadsheetml.template",
        "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
        "application/vnd.openxmlformats-officedocument.wordprocessingml.template",
        "application/vnd.presentation-openxml",
        "application/vnd.presentation-openxmlm",
        "application/vnd.spreadsheet-openxml",
        "application/vnd.wordprocessing-openxml",
        "application/x-gzip",
        "application/x-protobuf",
        "application/x-protobuffer",
        "application/zip",
        "multipart/byteranges",
        "multipart/signed",
        "text/event-stream",
        "text/csv",
    ];
    assert_eq!(list.len(), 35);
    for t in list {
        assert_eq!(
            check(200, &[("Content-Type", t)], GIF),
            Verdict::Blocked,
            "{t}"
        );
        // MIME type parsing lowercases the type and subtype.
        assert_eq!(
            check(200, &[("Content-Type", &t.to_ascii_uppercase())], GIF),
            Verdict::Blocked,
            "{t}"
        );
    }
    // Not on the list: a type that merely starts like one.
    assert_eq!(
        check(200, &[("Content-Type", "application/pdfx")], b"x"),
        Verdict::JavaScriptCheck
    );
}

#[test]
fn blocklisted_types() {
    // Step 3.3: a 206 of an HTML, JSON or XML type.
    for t in [
        "text/html",
        "application/json",
        "text/json",
        "application/ld+json",
        "text/xml",
        "application/atom+xml",
    ] {
        assert_eq!(
            check(206, &[("Content-Type", t)], GIF),
            Verdict::Blocked,
            "{t}"
        );
        // Step 3.4: with nosniff, even image bytes.
        assert_eq!(
            check(
                200,
                &[("Content-Type", t), ("x-content-type-options", "NoSniff")],
                GIF
            ),
            Verdict::Blocked,
            "{t}"
        );
        // Without nosniff the image bytes win (step 10) ...
        assert_eq!(
            check(200, &[("Content-Type", t)], GIF),
            Verdict::Allowed,
            "{t}"
        );
        // ... and anything else waits for the JavaScript check (step 15).
        assert_eq!(
            check(200, &[("Content-Type", t)], b"{\"a\": 1}"),
            Verdict::JavaScriptCheck,
            "{t}"
        );
    }
    // text/plain with nosniff (step 3.4).
    assert_eq!(
        check(
            200,
            &[
                ("Content-Type", "text/plain"),
                ("X-Content-Type-Options", "nosniff")
            ],
            GIF
        ),
        Verdict::Blocked
    );
}

#[test]
fn partial_responses_are_blocked() {
    // Step 5: no request here carries Range.
    assert_eq!(check(206, &[], b"x"), Verdict::Blocked);
    assert_eq!(
        check(206, &[("Content-Type", "image/png")], GIF),
        Verdict::Blocked
    );
}

#[test]
fn sniffed_bytes() {
    // Step 8: audio or video bytes, never a media request here.
    assert_eq!(check(200, &[], ID3), Verdict::Blocked);
    assert_eq!(
        check(200, &[("Content-Type", "audio/mpeg")], ID3),
        Verdict::Blocked
    );
    // Step 10: image bytes, whatever the type, status or nosniff.
    assert_eq!(check(200, &[], GIF), Verdict::Allowed);
    assert_eq!(
        check(500, &[("Content-Type", "text/plain")], GIF),
        Verdict::Allowed
    );
    assert_eq!(
        check(200, &[("X-Content-Type-Options", "nosniff")], GIF),
        Verdict::Allowed
    );
    // Only the first 1024 bytes are sniffed.
    let mut late = vec![b' '; 1024];
    late.extend_from_slice(GIF);
    assert_eq!(
        check(200, &[("X-Content-Type-Options", "nosniff")], &late),
        Verdict::Blocked
    );
}

#[test]
fn late_steps() {
    // Step 11: nosniff.
    assert_eq!(
        check(200, &[("X-Content-Type-Options", "nosniff")], b"x"),
        Verdict::Blocked
    );
    // Only the first value counts, ASCII case-insensitively.
    assert_eq!(
        check(200, &[("X-Content-Type-Options", "foo, nosniff")], b"x"),
        Verdict::Allowed
    );
    assert_eq!(
        check(200, &[("X-Content-Type-Options", "NOSNIFF, foo")], b"x"),
        Verdict::Blocked
    );
    // Step 12: not an ok status.
    assert_eq!(check(404, &[], b"x"), Verdict::Blocked);
    assert_eq!(check(302, &[], b"x"), Verdict::Blocked);
    // Step 13: no usable type.
    assert_eq!(check(200, &[], b"x"), Verdict::Allowed);
    assert_eq!(
        check(200, &[("Content-Type", "nonsense")], b"x"),
        Verdict::Allowed
    );
    assert_eq!(
        check(200, &[("Content-Type", "*/*")], b"x"),
        Verdict::Allowed
    );
    // Step 14: a media type that did not sniff as media.
    for t in ["audio/ogg", "image/png", "video/mp4"] {
        assert_eq!(
            check(200, &[("Content-Type", t)], b"x"),
            Verdict::Blocked,
            "{t}"
        );
    }
    // Step 15.
    assert_eq!(
        check(200, &[("Content-Type", "application/octet-stream")], b"x"),
        Verdict::JavaScriptCheck
    );
}

#[test]
fn extract_a_mime_type_takes_the_last_valid_value() {
    // `*/*` and failures are skipped; the last other value is the type.
    assert_eq!(
        check(200, &[("Content-Type", "text/javascript, */*")], b"x"),
        Verdict::Allowed
    );
    assert_eq!(
        check(
            200,
            &[
                ("Content-Type", "text/javascript"),
                ("Content-Type", "text/html")
            ],
            b"x"
        ),
        Verdict::JavaScriptCheck
    );
    assert_eq!(
        check(200, &[("Content-Type", "text/html, nonsense")], b"x"),
        Verdict::JavaScriptCheck
    );
    assert_eq!(
        check(200, &[("Content-Type", "text/html, text/css")], b"x"),
        Verdict::Allowed
    );
    // A comma inside a quoted parameter does not split.
    assert_eq!(
        check(
            200,
            &[("Content-Type", "text/css; a=\"x,text/html\"")],
            b"x"
        ),
        Verdict::Allowed
    );
}
