//! ORB against WPT `fetch/orb` (item 6.17): the cases that need no script, as
//! rows of the proven check (`safelist_check_exec`, the kernel's model).
//!
//! The vendored files (`tests/data/wpt-orb/`, WPT commit
//! `b64e5b477fe8ddd8c4f94dd27a4de88ab9006ec9`, see `SOURCE.md`) are read, not
//! copied into the test:
//!
//! - `img-mime-types-coverage.tentative.sub.html`: a cross-origin PNG served
//!   by `image.py` with `X-Content-Type-Options: nosniff` and every
//!   `Content-Type` of its two lists. Its `passes` are let through, its
//!   `fails` blocked. **Four of its `fails` differ from the standard's current
//!   text** (Fetch PR 1755 safelists `application/dash+xml`,
//!   `application/vnd.apple.mpegurl`, `audio/mpegurl` and `text/vtt`, which the
//!   older ORB draft the test follows blocked): the rows say so and expect the
//!   standard's answer.
//! - `img-png-mislabeled-as-html.sub.html` (`Content-Type: text/html`, from
//!   `png-mislabeled-as-html.png.headers`) and `img-png-unlabeled.sub.html`
//!   (no type): a PNG is let through after sniffing.
//!
//! Not run, and why: `status.sub.html` (a media request, whose "no-cors media
//! request state" the kernel's image and style requests never have),
//! `compressed-image-sniffing.sub.html` (a gzip response: the kernel sends no
//! `Accept-Encoding`, decision 6.0(h) A), and the `*.any.js` files (`fetch()`
//! with script).
//!
//! Prints `clazel-conformance:` with the number of rows that agree.

use clazel_fetch::orb::check::{orb_allows_exec, safelist_check_exec};
use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::types::{ResponseBuf, StatusLineBuf};

/// The signature of a PNG, then some more octets.
const PNG: &[u8] = &[
    0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0, 0, 0, 0x0D,
];

fn line(name: &str, value: &str) -> FieldLineBuf {
    FieldLineBuf {
        name: name.as_bytes().to_vec(),
        value: value.as_bytes().to_vec(),
    }
}

fn response(status: u16, fields: Vec<FieldLineBuf>, body: &[u8]) -> ResponseBuf {
    ResponseBuf {
        status_line: StatusLineBuf {
            major: 1,
            minor: 1,
            status,
            reason: Vec::new(),
        },
        fields,
        body: body.to_vec(),
    }
}

include!("generated/wpt_orb.rs");

const DIFFERS: [&str; 4] = [
    "application/dash+xml",
    "application/vnd.apple.mpegurl",
    "audio/mpegurl",
    "text/vtt",
];

#[test]
fn the_image_mime_type_coverage_page_blocks_and_allows_as_orb_says() {
    let passes: Vec<String> = PASSES.iter().map(|s| (*s).to_owned()).collect();
    let fails: Vec<String> = FAILS.iter().map(|s| (*s).to_owned()).collect();
    assert!(passes.len() >= 18, "{passes:?}");
    assert!(fails.len() >= 40, "{fails:?}");
    let mut agree = 0usize;
    let mut differs = 0usize;
    for (mime, expected) in passes
        .iter()
        .map(|m| (m, true))
        .chain(fails.iter().map(|m| (m, false)))
    {
        let r = response(
            200,
            vec![
                line("content-type", mime),
                line("x-content-type-options", "nosniff"),
            ],
            PNG,
        );
        let got = safelist_check_exec(&r);
        let expected = if DIFFERS.contains(&mime.as_str()) {
            differs += 1;
            true
        } else {
            expected
        };
        assert_eq!(got, expected, "Content-Type: {mime}");
        // Cross-origin, so ORB applies.
        assert_eq!(orb_allows_exec(true, &r), got, "{mime}");
        // Same-origin: not subject to ORB, whatever it says.
        assert!(orb_allows_exec(false, &r), "{mime}");
        agree += 1;
    }
    assert_eq!(differs, DIFFERS.len());
    println!(
        "clazel-conformance: wpt fetch/orb img-mime-types-coverage {agree} of {} rows agree ({differs} follow the current standard, not the test)",
        passes.len() + fails.len()
    );
}

#[test]
fn a_png_mislabeled_as_html_or_unlabeled_is_allowed_after_sniffing() {
    // img-png-mislabeled-as-html.sub.html
    let mislabeled = response(
        200,
        vec![line("Content-Type", MISLABELED_CONTENT_TYPE)],
        PNG,
    );
    assert!(safelist_check_exec(&mislabeled));
    // img-png-unlabeled.sub.html
    let unlabeled = response(200, vec![], PNG);
    assert!(safelist_check_exec(&unlabeled));
    println!(
        "clazel-conformance: wpt fetch/orb img-png-mislabeled-as-html, img-png-unlabeled 2 of 2 rows agree"
    );
}

#[test]
fn rows_of_the_standards_steps_that_the_wpt_pages_do_not_reach() {
    let html = b"<html><body>secret</body></html>";
    // 3.2: never sniffed, though the bytes are a PNG.
    assert!(!safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "application/pdf")],
        PNG
    )));
    // 3.3 and 5: a partial response.
    assert!(!safelist_check_exec(&response(
        206,
        vec![line("Content-Type", "text/html")],
        PNG
    )));
    assert!(!safelist_check_exec(&response(206, vec![], PNG)));
    assert!(safelist_check_exec(&response(
        206,
        vec![line("Content-Type", "text/css")],
        b""
    )));
    // 11: nosniff, an unsniffable body.
    assert!(!safelist_check_exec(&response(
        200,
        vec![
            line("Content-Type", "application/octet-stream"),
            line("X-Content-Type-Options", "NoSniff")
        ],
        b"abc"
    )));
    // 13 and 15 (the kernel refuses where the standard lets through): no
    // type, or a type that is none of the lists, and not an image.
    assert!(!safelist_check_exec(&response(200, vec![], html)));
    assert!(!safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "application/octet-stream")],
        html
    )));
    assert!(!safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "text/plain")],
        html
    )));
    // A list value: the last one that parses is the type (Fetch "extract a
    // MIME type"), so `text/html, text/css` is a style sheet and
    // `text/css, text/html` is HTML; `*/*` is skipped.
    assert!(safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "text/html, text/css")],
        html
    )));
    assert!(!safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "text/css, text/html")],
        html
    )));
    assert!(safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "text/css, */*")],
        html
    )));
    // Two field lines are one list.
    assert!(!safelist_check_exec(&response(
        200,
        vec![
            line("Content-Type", "text/css"),
            line("Content-Type", "text/html")
        ],
        html
    )));
    // A comma inside a quoted parameter does not split.
    assert!(safelist_check_exec(&response(
        200,
        vec![line("Content-Type", "text/css; a=\"x, text/html\"")],
        html
    )));
    // Only the first 8096 octets are sniffed: a PNG signature after them is
    // not seen.
    let mut late = vec![b' '; 8096];
    late.extend_from_slice(PNG);
    assert!(!safelist_check_exec(&response(200, vec![], &late)));
    // Image and audio signatures at the start are seen.
    assert!(safelist_check_exec(&response(
        200,
        vec![],
        b"GIF89a\x01\x00\x01\x00"
    )));
    assert!(safelist_check_exec(&response(
        200,
        vec![],
        b"OggS\x00\x01\x02\x03\x04"
    )));
    // A 404 with an image's bytes is still sniffed as an image (step 9
    // precedes the status check).
    assert!(safelist_check_exec(&response(404, vec![], PNG)));
    println!("clazel-conformance: orb step rows (all assertions of this test) agree");
}
