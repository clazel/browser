//! Hand-made cases of the form submission algorithm (HTML §4.10.22.3), one
//! or two per branch of the algorithm, through the tree builder and the
//! proven `submit_exec`. The expected values are written out from the
//! standard's steps and tables, not from the implementation.

mod support;

use clazel_encoding::labels::spec::Encoding;
use clazel_forms::submit::exec::submit::{ExecOutcome, submit_exec};
use clazel_forms::submit::spec::{NavMethod, Refusal, Target};
use clazel_url::url::parse::basic_url_parser;
use support::*;

/// What a submission did, as one line.
fn run(html: &str, submitter: Option<&str>, encoding: Encoding, boundary: &[u8]) -> String {
    let arena = parse(html);
    let rows = clean_rows(&arena);
    let form = node(&arena, "f");
    let s = submitter.map_or(form, |id| node(&arena, id));
    let page = "http://example.com/dir/page?old#top";
    let Some(base) = basic_url_parser(&u32s("http://example.com/dir/"), None) else {
        return "no base".to_owned();
    };
    match submit_exec(&arena, &rows, (form, s), encoding, &u32s(page), &base, boundary) {
        ExecOutcome::Ignored => "ignored".to_owned(),
        ExecOutcome::Refused(r) => format!(
            "refused {}",
            match r {
                Refusal::Dialog => "dialog",
                Refusal::MailtoScheme => "mailto",
                Refusal::JavascriptScheme => "javascript",
                Refusal::UnlistedScheme => "unlisted",
                Refusal::UnsupportedEncoding => "encoding",
                Refusal::BadBoundary => "boundary",
            }
        ),
        ExecOutcome::Navigate(n) => {
            let url = text(&n.url.serialize(false));
            let method = match n.method {
                NavMethod::Get => "GET",
                NavMethod::Post => "POST",
            };
            let target = match n.target {
                Target::ThisTab => "this",
                Target::NewTab => "new",
            };
            let body = n.body.as_ref().map_or(String::new(), |b| {
                format!(
                    " [{}] {:?}",
                    String::from_utf8_lossy(&b.content_type),
                    String::from_utf8_lossy(&b.bytes)
                )
            });
            let nr = if n.no_referrer { " noreferrer" } else { "" };
            format!("{method} {url} {target}{nr}{body}")
        }
    }
}

fn go(html: &str) -> String {
    run(html, None, Encoding::Utf8, b"BND")
}

#[test]
fn get_replaces_the_query_and_keeps_the_fragment() {
    assert_eq!(
        go("<form id=f action='/search?x=1#frag'><input name=q value='a b'></form>"),
        "GET http://example.com/search?q=a+b#frag this"
    );
}

#[test]
fn post_urlencoded_is_the_default_and_keeps_the_action_query() {
    assert_eq!(
        go("<form id=f method=POST action='go?k=v'><input name=q value='a b'><input name=r value=1></form>"),
        "POST http://example.com/dir/go?k=v this [application/x-www-form-urlencoded] \"q=a+b&r=1\""
    );
}

#[test]
fn empty_action_is_the_document_url() {
    assert_eq!(
        go("<form id=f method=post action=''><input name=a value=b></form>"),
        "POST http://example.com/dir/page?old#top this [application/x-www-form-urlencoded] \"a=b\""
    );
    // No action attribute: the same.
    assert_eq!(
        go("<form id=f><input name=a value=b></form>"),
        "GET http://example.com/dir/page?a=b#top this"
    );
}

#[test]
fn text_plain_and_multipart() {
    assert_eq!(
        go("<form id=f method=post enctype=text/plain action=/x><input name=a value=b><input name=c value=d></form>"),
        "POST http://example.com/x this [text/plain] \"a=b\\r\\nc=d\\r\\n\""
    );
    assert_eq!(
        go("<form id=f method=post enctype=MULTIPART/form-data action=/x><input name='a\"' value=b></form>"),
        "POST http://example.com/x this [multipart/form-data; boundary=BND] \
         \"--BND\\r\\nContent-Disposition: form-data; name=\\\"a%22\\\"\\r\\n\\r\\nb\\r\\n--BND--\\r\\n\""
    );
}

#[test]
fn an_unknown_enctype_and_method_use_the_defaults() {
    assert_eq!(
        go("<form id=f method=put enctype=x action=/x><input name=a value=b></form>"),
        "GET http://example.com/x?a=b this"
    );
    assert_eq!(
        go("<form id=f method=post enctype=x action=/x><input name=a value=b></form>"),
        "POST http://example.com/x this [application/x-www-form-urlencoded] \"a=b\""
    );
}

#[test]
fn a_submit_buttons_attributes_win() {
    let html = "<form id=f action=/form><input name=a value=b>\
        <button id=s name=go value=1 formaction=/other formmethod=post formenctype=text/plain formtarget=_blank>x</button></form>";
    assert_eq!(
        run(html, Some("s"), Encoding::Utf8, b"B"),
        "POST http://example.com/other new [text/plain] \"a=b\\r\\ngo=1\\r\\n\""
    );
    // Submitted from the form (no submitter): the button is not in the list.
    assert_eq!(go(html), "GET http://example.com/form?a=b this");
}

#[test]
fn a_button_that_is_not_a_submit_button_keeps_the_forms_attributes() {
    let html = "<form id=f method=post action=/form><button id=s type=button formaction=/other>x</button></form>";
    assert_eq!(
        run(html, Some("s"), Encoding::Utf8, b"B"),
        "POST http://example.com/form this [application/x-www-form-urlencoded] \"\""
    );
}

#[test]
fn targets() {
    let t = |attrs: &str, head: &str| {
        go(&format!(
            "{head}<form id=f action=/x {attrs}><input name=a value=b></form>"
        ))
    };
    assert_eq!(t("", ""), "GET http://example.com/x?a=b this");
    assert_eq!(t("target=_self", ""), "GET http://example.com/x?a=b this");
    assert_eq!(t("target=_PARENT", ""), "GET http://example.com/x?a=b this");
    assert_eq!(t("target=_top", ""), "GET http://example.com/x?a=b this");
    assert_eq!(t("target=_blank", ""), "GET http://example.com/x?a=b new");
    assert_eq!(t("target=somewhere", ""), "GET http://example.com/x?a=b new");
    // A base target applies when the form has none; the form's wins.
    assert_eq!(
        t("", "<base target=_blank>"),
        "GET http://example.com/x?a=b new"
    );
    assert_eq!(
        t("target=_self", "<base target=_blank>"),
        "GET http://example.com/x?a=b this"
    );
    // A tab or newline with a "<" makes the target "_blank".
    assert_eq!(
        t("target='a&#9;<b'", ""),
        "GET http://example.com/x?a=b new"
    );
}

#[test]
fn noreferrer() {
    assert_eq!(
        go("<form id=f action=/x rel='Opener NoReferrer'><input name=a value=b></form>"),
        "GET http://example.com/x?a=b this noreferrer"
    );
    assert_eq!(
        go("<form id=f action=/x rel='noreferrers'><input name=a value=b></form>"),
        "GET http://example.com/x?a=b this"
    );
}

#[test]
fn the_scheme_table() {
    let f = |action: &str, method: &str| {
        go(&format!(
            "<form id=f action='{action}' method={method}><input name=a value=b></form>"
        ))
    };
    assert_eq!(f("https://h/p", "get"), "GET https://h/p?a=b this");
    assert_eq!(
        f("data:text/html,hi", "get"),
        "GET data:text/html,hi?a=b this"
    );
    // data: with POST, and ftp: either way, "get action URL".
    assert_eq!(f("data:text/html,hi", "post"), "GET data:text/html,hi this");
    assert_eq!(f("ftp://h/p?q", "post"), "GET ftp://h/p?q this");
    assert_eq!(f("ftp://h/p?q", "get"), "GET ftp://h/p?q this");
    assert_eq!(f("mailto:a@b", "get"), "refused mailto");
    assert_eq!(f("mailto:a@b", "post"), "refused mailto");
    assert_eq!(f("javascript:1", "get"), "refused javascript");
    assert_eq!(f("file:///x", "get"), "refused unlisted");
    assert_eq!(f("http://", "get"), "ignored");
    assert_eq!(
        go("<form id=f method=dialog><input name=a value=b></form>"),
        "refused dialog"
    );
}

#[test]
fn a_form_not_in_a_document_does_not_navigate() {
    let mut arena = parse("<form id=f action=/x><input name=a value=b></form>");
    let form = node(&arena, "f");
    arena.remove(form);
    let rows = clean_rows(&arena);
    let Some(base) = basic_url_parser(&u32s("http://example.com/"), None) else {
        return;
    };
    let out = submit_exec(
        &arena,
        &rows,
        (form, form),
        Encoding::Utf8,
        &u32s("http://example.com/"),
        &base,
        b"B",
    );
    assert!(matches!(out, ExecOutcome::Ignored));
}

#[test]
fn encodings() {
    let html = |cs: &str| {
        format!(
            "<form id=f action=/x accept-charset='{cs}'><input name=a value='\u{e9}\u{259}'></form>"
        )
    };
    // windows-1252 has e-acute (0xE9) but not schwa: HTML's "&#601;", percent-encoded.
    assert_eq!(
        run(&html("windows-1252"), None, Encoding::Utf8, b"B"),
        "GET http://example.com/x?a=%E9%26%23601%3B this"
    );
    // The first label that is an encoding counts; "bogus" is skipped.
    assert_eq!(
        run(&html(" bogus  iso-8859-1 utf-8"), None, Encoding::Utf8, b"B"),
        "GET http://example.com/x?a=%E9%26%23601%3B this"
    );
    // None found: UTF-8. UTF-16 is replaced by UTF-8 as an output encoding.
    assert_eq!(
        run(&html("bogus"), None, Encoding::Windows1252, b"B"),
        "GET http://example.com/x?a=%C3%A9%C9%99 this"
    );
    assert_eq!(
        run(&html("utf-16le"), None, Encoding::Windows1252, b"B"),
        "GET http://example.com/x?a=%C3%A9%C9%99 this"
    );
    // No accept-charset: the document's encoding.
    assert_eq!(
        run(
            "<form id=f action=/x><input name=a value='\u{e9}'></form>",
            None,
            Encoding::Windows1252,
            b"B"
        ),
        "GET http://example.com/x?a=%E9 this"
    );
    // A multi-byte legacy encoding has no encoder yet: refused.
    assert_eq!(
        run(&html("shift_jis"), None, Encoding::Utf8, b"B"),
        "refused encoding"
    );
    // ... but a form that does not need the encoder is not refused.
    assert_eq!(
        run(
            "<form id=f action=ftp://h/ accept-charset=shift_jis></form>",
            None,
            Encoding::Utf8,
            b"B"
        ),
        "GET ftp://h/ this"
    );
}

#[test]
fn the_charset_control_gets_the_encodings_name() {
    let html = "<form id=f action=/x accept-charset=iso-8859-1><input type=hidden name=_charset_></form>";
    assert_eq!(
        go(html),
        "GET http://example.com/x?_charset_=windows-1252 this"
    );
}

#[test]
fn the_boundary_must_be_well_formed() {
    let html = "<form id=f method=post enctype=multipart/form-data action=/x><input name=a value=b></form>";
    assert_eq!(run(html, None, Encoding::Utf8, b""), "refused boundary");
    assert_eq!(run(html, None, Encoding::Utf8, b"a b"), "refused boundary");
    assert_eq!(run(html, None, Encoding::Utf8, &[b'a'; 71]), "refused boundary");
    assert!(run(html, None, Encoding::Utf8, &[b'a'; 70]).starts_with("POST "));
}

#[test]
fn the_body_is_the_serialized_entry_list() {
    let html = "<form id=f method=post action=/x><input name=a value=1><input type=checkbox name=c>\
        <input type=hidden name=h value=z></form>";
    let list = entries_of(html, "f", None);
    assert_eq!(
        list,
        vec![
            ("a".to_owned(), "1".to_owned()),
            ("h".to_owned(), "z".to_owned())
        ]
    );
    let arena = parse(html);
    let rows = clean_rows(&arena);
    let form = node(&arena, "f");
    assert_eq!(
        entry_list(&arena, &rows, form, None, "UTF-8", false).map(|l| l.len()),
        Some(2)
    );
    assert_eq!(
        go(html),
        "POST http://example.com/x this [application/x-www-form-urlencoded] \"a=1&h=z\""
    );
}
