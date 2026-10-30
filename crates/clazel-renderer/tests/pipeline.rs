//! The document pipeline (phase-4.md item 4.13), one test per rule of
//! `clazel_renderer::pipeline`: tier 0 glue, so these tests are its
//! evidence.

use clazel_encoding::labels::spec::Encoding;
use clazel_ipc::frame::spec::MAX_FRAME;
use clazel_ipc::message::codec::{Msg, encode_framed};
use clazel_renderer::pipeline::{Encodings, MAX_TITLE, NotParsed, Shown, fit, parse_html, render};
use clazel_treebuilder::exec::types::EncFnsExec;

const URL: &[u8] = b"http://a.test/dir/page.html";

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn html(body: &str) -> Shown {
    render(URL, b"text/html", body.as_bytes(), 80)
}

#[test]
fn an_html_page_gives_its_title_text_and_resolved_links() {
    let shown = html(
        "<title> The  title </title><h1>Head</h1><p>See <a href=other>this</a> and \
         <a href='https://b.test/x?y#z'>that</a>.</p><iframe src=/frame></iframe>",
    );
    assert_eq!(shown.title, "The title");
    assert_eq!(shown.text, "Head\n\nSee this[1] and that[2].\n\n[3]");
    assert_eq!(
        shown.links,
        [
            "http://a.test/dir/other",
            "https://b.test/x?y#z",
            "http://a.test/frame"
        ]
    );
}

#[test]
fn the_first_base_with_an_href_is_the_base_url() {
    let shown = html(
        "<base target=_top><base href='http://c.test/base/'><base href='http://d.test/'>\
         <a href=x>x</a>",
    );
    assert_eq!(shown.links, ["http://c.test/base/x"]);
    // A base href that does not parse leaves the document's URL.
    let shown = html("<base href='http://['><a href=x>x</a>");
    assert_eq!(shown.links, ["http://a.test/dir/x"]);
    // A base element in another namespace is not the base.
    let shown = html("<svg><base href='http://e.test/'></base></svg><a href=x>x</a>");
    assert_eq!(shown.links, ["http://a.test/dir/x"]);
}

#[test]
fn an_href_that_does_not_parse_is_not_a_link() {
    let shown = html("<a href='http://['>bad</a> <a href=good>good</a>");
    assert_eq!(shown.text, "bad good[1]");
    assert_eq!(shown.links, ["http://a.test/dir/good"]);
}

#[test]
fn the_content_type_is_sniffed_when_absent_or_unknown() {
    for supplied in [&b""[..], b"unknown/unknown", b"*/*", b"not a type"] {
        let shown = render(URL, supplied, b"<!DOCTYPE html><p>hi", 80);
        assert_eq!(shown.text, "hi", "{:?}", String::from_utf8_lossy(supplied));
    }
    // A supplied HTML type is not sniffed: these bytes are HTML text.
    let shown = render(URL, b"text/html", b"%PDF-1.4 <b>x</b>", 80);
    assert_eq!(shown.text, "%PDF-1.4 x");
}

#[test]
fn text_plain_is_one_preformatted_block() {
    let shown = render(
        URL,
        b"text/plain",
        b"a  b\r\n<p>c</p>\rd\te\n\nlong line here",
        6,
    );
    assert_eq!(shown.title, "");
    assert_eq!(shown.text, "a  b\n<p>c</\np>\nd e\n\nlong l\nine he\nre");
    assert!(shown.links.is_empty());
}

#[test]
fn other_types_are_not_shown() {
    let shown = render(URL, b"image/png", b"\x89PNG\r\n\x1a\n", 80);
    assert_eq!(
        shown.text,
        "image/png is not shown: http://a.test/dir/page.html"
    );
    assert!(shown.links.is_empty());
    let shown = render(URL, b"application/json; charset=utf-8", b"{}", 80);
    assert_eq!(
        shown.text,
        "application/json;charset=utf-8 is not shown: http://a.test/dir/page.html"
    );
}

#[test]
fn the_transport_encoding_and_a_bom_win_over_the_prescan() {
    // é in windows-1252 is 0xE9; in UTF-8 it is 0xC3 0xA9.
    let latin = b"<meta charset=utf-8><p>caf\xE9";
    assert_eq!(
        render(URL, b"text/html; charset=windows-1252", latin, 80).text,
        "caf\u{e9}"
    );
    // Without the transport encoding, the prescan's UTF-8 decodes 0xE9 as an error.
    assert_eq!(render(URL, b"text/html", latin, 80).text, "caf\u{FFFD}");
    // A byte order mark wins over both.
    let bom = b"\xEF\xBB\xBF<p>caf\xC3\xA9";
    assert_eq!(
        render(URL, b"text/html; charset=windows-1252", bom, 80).text,
        "caf\u{e9}"
    );
}

#[test]
fn a_meta_after_the_prescan_restarts_the_parser_once() -> Result<(), NotParsed> {
    let mut page = String::from("<!DOCTYPE html><!--");
    page.push_str(&"x".repeat(2000));
    page.push_str("--><meta charset=iso-8859-2><title>\u{0}</title><p>");
    let mut body = page.into_bytes();
    // 0xB1 is U+0105 in ISO-8859-2 and U+00B1 in windows-1252.
    body.push(0xB1);
    let parsed = parse_html(&body, None, &cps("http://a.test/"))?;
    assert!(parsed.restarted);
    assert_eq!(parsed.encoding, Encoding::Iso8859_2);
    assert_eq!(render(URL, b"text/html", &body, 80).text, "\u{105}");
    // A meta naming the encoding already in use changes nothing.
    let same =
        b"<!--................................................--><meta charset=windows-1252><p>x";
    let parsed = parse_html(same, None, &cps("http://a.test/"))?;
    assert!(!parsed.restarted);
    // A certain encoding (from the transport layer) is never changed.
    let parsed = parse_html(&body, Some(Encoding::Windows1252), &cps("http://a.test/"))?;
    assert!(!parsed.restarted);
    assert_eq!(parsed.encoding, Encoding::Windows1252);
    Ok(())
}

#[test]
fn an_encoding_without_a_decoder_is_not_rendered() {
    let body = b"<meta charset=shift_jis><p><a href=x>\x82\xA0</a>";
    assert!(matches!(
        parse_html(body, None, &cps("http://a.test/")),
        Err(NotParsed::Unsupported(Encoding::ShiftJis))
    ));
    let shown = render(URL, b"text/html", body, 80);
    assert_eq!(shown.text, "encoding Shift_JIS is not supported");
    assert!(shown.links.is_empty());
    let shown = render(URL, b"text/plain; charset=euc-kr", b"x", 80);
    assert_eq!(shown.text, "encoding EUC-KR is not supported");
}

#[test]
fn a_meta_content_value_is_extracted_with_its_non_ascii() {
    let enc = Encodings;
    assert_eq!(
        enc.extract_from_meta(&cps("text/html; charset=iso-8859-2")),
        Some(cps("iso-8859-2"))
    );
    // A label with a non-ASCII character is no encoding, before and after
    // the mapping.
    let odd = enc.extract_from_meta(&cps("text/html; charset=utf\u{2010}8"));
    assert!(odd.is_some());
    assert_eq!(odd.and_then(|l| enc.get_an_encoding(&l)), None);
    assert_eq!(enc.extract_from_meta(&cps("\u{e9}charset")), None);
    assert_eq!(enc.get_an_encoding(&cps(" UTF8 ")), Some(0));
}

#[test]
#[cfg_attr(
    miri,
    ignore = "megabytes of text through the CBOR encoder; the same code runs at any size"
)]
fn a_display_always_fits_one_frame() -> Result<(), String> {
    // A small page is sent whole.
    let small = Shown {
        title: "t".to_owned(),
        text: "a\nb".to_owned(),
        links: vec!["http://a.test/".to_owned()],
    };
    assert_eq!(
        fit(small),
        Msg::Display {
            title: b"t".to_vec(),
            text: b"a\nb".to_vec(),
            links: vec![b"http://a.test/".to_vec()],
        }
    );
    // A page over the frame: cut, and it says so.
    let line = "y".repeat(99);
    let big = Shown {
        title: "T".repeat(5000),
        text: vec![line.as_str(); 20_000].join("\n"),
        links: vec!["http://a.test/".repeat(10); 5000],
    };
    let msg = fit(big);
    let frame = encode_framed(&msg);
    assert!(
        frame
            .as_ref()
            .is_some_and(|f| f.len() <= MAX_FRAME.saturating_add(4))
    );
    let Msg::Display { title, text, links } = msg else {
        return Err(format!("not a Display: {msg:?}"));
    };
    assert_eq!(title.len(), MAX_TITLE);
    assert!(links.len() < 5000 && !links.is_empty());
    let text = String::from_utf8_lossy(&text).into_owned();
    assert!(
        text.ends_with(" links]"),
        "{}",
        text.lines().last().unwrap_or_default()
    );
    // Every kept line is whole.
    let lines: Vec<&str> = text.lines().collect();
    assert!(lines.iter().rev().skip(1).all(|l| *l == line));
    Ok(())
}

#[test]
fn hostile_bytes_never_panic() {
    // Smaller under Miri, which interprets every step.
    let n = if cfg!(miri) { 50 } else { 5000 };
    // Bytes valid in no encoding, a page that is one `<plaintext>`, nested
    // elements, and references without semicolons.
    let mut cases: Vec<Vec<u8>> = vec![
        (0u8..=255).cycle().take(n).collect(),
        b"<plaintext><a href=x>not a link".to_vec(),
        "<div>".repeat(n).into_bytes(),
        "&amp&lt&gt&#x41&#65".repeat(n / 10).into_bytes(),
        b"<title>URL: http://bank.test/</title><base href='javascript:alert(1)'><a href=x>x</a>"
            .to_vec(),
    ];
    cases.push(b"\xFE\xFF\xD8\x00<\x00p".to_vec());
    for body in &cases {
        for t in [
            &b""[..],
            b"text/html",
            b"text/plain",
            b"text/html; charset=utf-16le",
        ] {
            let shown = render(URL, t, body, 40);
            assert!(encode_framed(&fit(shown)).is_some());
        }
    }
    let shown = render(
        URL,
        b"text/html",
        cases.get(1).map_or(&[][..], Vec::as_slice),
        80,
    );
    // PLAINTEXT: the rest of the page is text, so the tag is too.
    assert_eq!(shown.text, "<a href=x>not a link");
    assert!(shown.links.is_empty());
}

#[test]
fn the_memory_bound_terms_are_as_the_readme_states() {
    // README.md, "Memory": the record of one node, and of one attribute.
    let node = std::mem::size_of::<clazel_dom::exec::ExecNode>();
    let attr = std::mem::size_of::<clazel_dom::exec::ExecAttr>();
    println!("ExecNode {node} bytes, ExecAttr {attr} bytes");
    assert!(node <= 168, "ExecNode is {node} bytes");
    assert!(attr <= 80, "ExecAttr is {attr} bytes");
}
