//! Conformance of "constructing the entry list" against WPT
//! `html/semantics/forms/form-submission-0/` (vendored by item 6.1 in
//! `crates/clazel/tests/wpt-phase6/`, WPT commit
//! `4ad507b28db0a636f528def9161d109fe11b93a3`), through the tree builder and
//! the proven executable functions.
//!
//! **All 32 pages of that directory need script** (testharness.js, or
//! scripts that build the form and click). So no page runs as a browser
//! would run it; instead this test reads the **markup and the data tables
//! out of three pages** (compiled in with `include_str!`) and runs the
//! script-free part: build the form the page builds, with the submitter the
//! page clicks, and compare the entry list with what the page asserts.
//!
//! - `constructing-form-data-set.html`: its two `<form>`s and the three
//!   assertions about entry lists that need no `FormData`, events or frames:
//!   the `_charset_` entry (UTF-8 for the FormData constructor,
//!   `windows-1252` for the form with `accept-charset="iso-8859-1"`, whose
//!   encoding selection is item 6.14's and is passed in), and that a button
//!   is in the list only as the submitter (`foo=&submit=true`). 3 checks.
//! - `url-encoded.html`: its `simple_tests` table: `input` markup in a
//!   form, the page's `output` query string. 3 checks. The serializer here
//!   is a small stand-in for the `application/x-www-form-urlencoded`
//!   serializer of item 6.14.
//! - `submit-entity-body.html`: its `simple_tests` table: `input` and
//!   `submitelement` markup and the clicked element; the page's `expected_body`
//!   where it has one (the two image cases, clicked at (0, 0)). The other 11
//!   rows are only checked by that page's server (`query=1`, "OK"), whose
//!   code is not vendored, so their expected entry lists are written out
//!   here from the algorithm's steps (a named submitter and the named
//!   non-button controls). 13 checks.
//!
//! Units: checks. The pages' remaining assertions (`FormData` objects,
//! `formdata` events, files, `submit()`, frames, entries added by handlers)
//! need script and are not counted.

mod support;

use support::*;

const CONSTRUCTING: &str = include_str!(
    "../../clazel/tests/wpt-phase6/html/semantics/forms/form-submission-0/constructing-form-data-set.html"
);
const URL_ENCODED: &str = include_str!(
    "../../clazel/tests/wpt-phase6/html/semantics/forms/form-submission-0/url-encoded.html"
);
const ENTITY_BODY: &str = include_str!(
    "../../clazel/tests/wpt-phase6/html/semantics/forms/form-submission-0/submit-entity-body.html"
);

/// The JavaScript string literal that follows `key: ` in `src` at or after
/// `from`, unescaped (`\"` and `\\` only: the pages use no others), and the
/// position after it.
fn js_string(src: &str, key: &str, from: usize) -> Option<(String, usize)> {
    let tail = src.get(from..)?;
    let at = tail.find(&format!("{key}: \""))?;
    let start = at.checked_add(key.len())?.checked_add(3)?;
    let mut out = String::new();
    let mut escaped = false;
    for (i, c) in tail.get(start..)?.char_indices() {
        if escaped {
            out.push(c);
            escaped = false;
        } else if c == '\\' {
            escaped = true;
        } else if c == '"' {
            return Some((
                out,
                from.checked_add(start)?.checked_add(i)?.checked_add(1)?,
            ));
        } else {
            out.push(c);
        }
    }
    None
}

/// The rest of the line after `key: ` in `src` (for `submitaction: function …`).
fn raw_line(src: &str, key: &str) -> String {
    src.find(&format!("{key}: "))
        .and_then(|at| src.get(at.saturating_add(key.len()).saturating_add(2)..))
        .and_then(|t| t.lines().next())
        .unwrap_or("")
        .to_owned()
}

/// The rows of a page's `simple_tests` table: for each row, its `name` and
/// then the values of `keys` (a key starting with `raw:` is read to the end
/// of its line; a missing key gives an empty string).
fn rows(src: &str, keys: &[&str]) -> Vec<Vec<String>> {
    let start = src.find("simple_tests = [").unwrap_or(0);
    let table = src.get(start..).unwrap_or("");
    let table = table
        .get(..table.find("];").unwrap_or(table.len()))
        .unwrap_or("");
    let starts: Vec<usize> = table.match_indices("name: \"").map(|(i, _)| i).collect();
    let mut out = Vec::new();
    for (k, &from) in starts.iter().enumerate() {
        let to = starts
            .get(k.saturating_add(1))
            .copied()
            .unwrap_or(table.len());
        let slice = table.get(from..to).unwrap_or("");
        let mut row = vec![
            js_string(slice, "name", 0)
                .map(|(v, _)| v)
                .unwrap_or_default(),
        ];
        for key in keys {
            row.push(match key.strip_prefix("raw:") {
                Some(k) => raw_line(slice, k),
                None => js_string(slice, key, 0).map(|(v, _)| v).unwrap_or_default(),
            });
        }
        out.push(row);
    }
    out
}

/// A stand-in for the `application/x-www-form-urlencoded` serializer
/// (item 6.14): the byte serializer of URL §5.2 over UTF-8.
fn urlencode(entries: &[(String, String)]) -> String {
    fn enc(s: &str) -> String {
        let mut out = String::new();
        for b in s.bytes() {
            match b {
                b' ' => out.push('+'),
                b'*' | b'-' | b'.' | b'_' => out.push(b as char),
                b if b.is_ascii_alphanumeric() => out.push(b as char),
                b => out.push_str(&format!("%{b:02X}")),
            }
        }
        out
    }
    entries
        .iter()
        .map(|(n, v)| format!("{}={}", enc(n), enc(v)))
        .collect::<Vec<_>>()
        .join("&")
}

/// The element id of `getElementById("…")` in a row's `submitaction`, other
/// than the form itself.
fn clicked(action: &str) -> Option<String> {
    let at = action.find("getElementById(\"")?;
    let rest = action.get(at.checked_add("getElementById(\"".len())?..)?;
    let id = rest.split('"').next()?;
    (id != "testform").then(|| id.to_owned())
}

#[test]
fn wpt_form_submission_0() {
    let mut pass = 0usize;
    let mut failed: Vec<String> = Vec::new();
    let mut total = 0usize;
    let mut check = |name: &str, got: String, want: &str| {
        total = total.saturating_add(1);
        if got == want {
            pass = pass.saturating_add(1);
        } else {
            failed.push(format!("{name}: got {got:?}, want {want:?}"));
        }
    };

    // constructing-form-data-set.html: the markup of its two forms.
    let page = parse(CONSTRUCTING);
    let rows_state = clean_rows(&page);
    let form1 = node(&page, "form1");
    let form2 = node(&page, "form2");
    check(
        "FormData constructor always produces UTF-8 _charset_ value",
        urlencode(&entry_list(&page, &rows_state, form1, None, "UTF-8", false).unwrap_or_default()),
        "_charset_=UTF-8",
    );
    check(
        "_charset_ control sets the expected encoding name (windows-1252, from accept-charset iso-8859-1)",
        urlencode(
            &entry_list(&page, &rows_state, form1, None, "windows-1252", false).unwrap_or_default(),
        ),
        "_charset_=windows-1252",
    );
    let submit = by_id(&page, "form2")
        .and_then(|_| {
            // `form2.submit.click()`: the element named "submit".
            let mut stack = vec![form2];
            let mut found = None;
            while let Some(n) = stack.pop() {
                if let clazel_dom::exec::ExecKind::Element { attributes, .. } = page.kind(n)
                    && attributes
                        .iter()
                        .any(|a| a.local_name == u32s("name") && a.value == u32s("submit"))
                {
                    found = Some(n);
                }
                stack.extend(page.children(n).iter().rev());
            }
            found
        })
        .unwrap_or(0);
    check(
        "The button cannot be setted if it is not a submitter",
        urlencode(
            &entry_list(&page, &rows_state, form2, Some(submit), "UTF-8", false)
                .unwrap_or_default(),
        ),
        "foo=&submit=true",
    );

    // url-encoded.html: the page's table.
    for row in rows(URL_ENCODED, &["input", "output"]) {
        let html = format!(
            "<form id=testform action=\"/common/blank.html\">{}</form>",
            row.get(1).map_or("", |s| s)
        );
        let got = urlencode(&entries_of(&html, "testform", None));
        check(
            row.first().map_or("", |s| s),
            got,
            row.get(2).map_or("", |s| s),
        );
    }

    // submit-entity-body.html: the page's table.
    let hand_made: [(&str, &str); 11] = [
        (
            "form submission from form should navigate to url with x-www-form-urlencoded",
            "foo=bara",
        ),
        (
            "form submission from form should navigate to url with multipart/form-data",
            "foo=bar",
        ),
        (
            "form submission from form should navigate to url with text/plain",
            "qux=baz",
        ),
        (
            "form submission from button should navigate to url with x-www-form-urlencoded",
            "foo=bara",
        ),
        (
            "form submission from button should navigate to url with multipart/form-data",
            "foo=bar",
        ),
        (
            "form submission from button should navigate to url with text/plain",
            "qux=baz",
        ),
        (
            "form submission from input should navigate to url with x-www-form-urlencoded",
            "foo=bara",
        ),
        (
            "form submission from input should navigate to url with multipart/form-data",
            "foo=bar",
        ),
        (
            "form submission from input should navigate to url with text/plain",
            "qux=baz",
        ),
        (
            "form submission from submit input should contain submit button value",
            "foo=bara",
        ),
        (
            "form submission from submit button should contain submit button value",
            "foo=bara",
        ),
    ];
    for row in rows(
        ENTITY_BODY,
        &[
            "input",
            "submitelement",
            "raw:submitaction",
            "expected_body",
        ],
    ) {
        let name = row.first().map_or("", |s| s);
        let input = row.get(1).map_or("", |s| s);
        let element = row.get(2).map_or("", |s| s);
        let action = row.get(3).map_or("", |s| s);
        let expected_body = row.get(4).map_or("", |s| s);
        let html = format!("<form id=testform method=post>{input}{element}</form>");
        let arena = parse(&html);
        let rows_state = clean_rows(&arena);
        let form = node(&arena, "testform");
        let submitter = clicked(action).map(|id| node(&arena, &id));
        let got = urlencode(
            &entry_list(&arena, &rows_state, form, submitter, "UTF-8", false).unwrap_or_default(),
        );
        let want = if expected_body.is_empty() {
            hand_made
                .iter()
                .find(|(n, _)| *n == name)
                .map_or("(no expectation written)", |(_, w)| *w)
        } else {
            expected_body
        };
        check(name, got, want);
    }

    const EXPECTED_TOTAL: usize = 3 + 3 + 13;
    println!(
        "clazel-conformance: suite=\"WPT form-submission-0 (script-free markup and tables)\" pass={pass} xfail=0 fail={} total={EXPECTED_TOTAL}",
        failed.len()
    );
    for f in &failed {
        println!("MISMATCH {f}");
    }
    assert!(failed.is_empty(), "{} mismatches", failed.len());
    assert_eq!(total, EXPECTED_TOTAL, "the pages' tables changed size");
    assert_eq!(pass, EXPECTED_TOTAL);
}
