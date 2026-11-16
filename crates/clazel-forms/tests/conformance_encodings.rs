//! Conformance of the form encodings and the submission algorithm: WPT's
//! form encoding tests (vendored under `tests/data/wpt-form-encodings/`,
//! converted by `cargo xtask testdata`), and a differential test of the
//! `application/x-www-form-urlencoded` serializer against the
//! `form_urlencoded` crate (test-only, class `test` in
//! docs/DEPENDENCIES.md) on random inputs.
//!
//! - `url/urlencoded-parser.any.js`: parsed pairs. The test has no parser to
//!   test (the urlencoded parser is not part of this item), so it uses a
//!   small parser of URL §5.1 written here: each case is checked as
//!   `parse(input) == pairs` (the parser agrees with WPT) and then as a
//!   round trip `parse(serialize(pairs)) == pairs` (the serializer is
//!   inverted by it). Units: cases (two checks each).
//! - `form-submission-0/urlencoded2`, `text-plain`, `multipart-formdata`:
//!   each `formTest` call that needs no file, through a form with one hidden
//!   control submitted by `submit_exec`; the body is compared with the page's
//!   `expected`. The calls with a `File` value are counted and skipped
//!   (`type=file` is out). Units: calls.

mod support;

use clazel_dom::exec::{Arena, ExecAttr};
use clazel_encoding::labels::spec::Encoding;
use clazel_forms::exec::entry::ExecEntry;
use clazel_forms::submit::exec::encode::urlencoded_serialize_exec;
use clazel_forms::submit::exec::strings::scalar_entries_exec;
use clazel_forms::submit::exec::submit::{ExecOutcome, submit_exec};
use clazel_url::url::parse::basic_url_parser;
use support::*;

struct ParserCase {
    input: &'static [u32],
    pairs: &'static [(&'static [u32], &'static [u32])],
}

struct FormCase {
    line: usize,
    name: &'static [u32],
    value: &'static [u32],
    encoding: &'static str,
    a: &'static [u32],
    b: &'static [u32],
    description: &'static [u32],
}

// `PARSER`, `URLENCODED`, `TEXT_PLAIN`, `MULTIPART` and the skipped counts,
// generated from the vendored WPT files.
include!("generated/wpt_form_encodings.rs");

fn string(cps: &[u32]) -> String {
    cps.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// URL §5.1 "application/x-www-form-urlencoded parsing" on a UTF-8 byte
/// sequence (steps 1 to 3, written for this test).
fn parse_urlencoded(input: &str) -> Vec<(String, String)> {
    fn percent_decode(s: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        let mut i = 0usize;
        while let Some(&b) = s.get(i) {
            let hex = |k: usize| {
                s.get(k)
                    .and_then(|&c| char::from(c).to_digit(16))
                    .and_then(|d| u8::try_from(d).ok())
            };
            if b == b'%'
                && let (Some(h), Some(l)) = (hex(i.saturating_add(1)), hex(i.saturating_add(2)))
            {
                out.push(h.saturating_mul(16).saturating_add(l));
                i = i.saturating_add(3);
            } else {
                out.push(b);
                i = i.saturating_add(1);
            }
        }
        out
    }
    let decode = |s: &[u8]| {
        let plus: Vec<u8> = s
            .iter()
            .map(|&b| if b == b'+' { b' ' } else { b })
            .collect();
        String::from_utf8_lossy(&percent_decode(&plus)).into_owned()
    };
    input
        .as_bytes()
        .split(|&b| b == b'&')
        .filter(|seq| !seq.is_empty())
        .map(|seq| {
            let (n, v) = match seq.iter().position(|&b| b == b'=') {
                Some(p) => (
                    seq.get(..p).unwrap_or(&[]),
                    seq.get(p.saturating_add(1)..).unwrap_or(&[]),
                ),
                None => (seq, &[][..]),
            };
            (decode(n), decode(v))
        })
        .collect()
}

fn entries(pairs: &[(Vec<u32>, Vec<u32>)]) -> Vec<ExecEntry> {
    pairs
        .iter()
        .map(|(n, v)| ExecEntry {
            name: n.clone(),
            value: v.clone(),
        })
        .collect()
}

/// The serializer on `pairs` with `encoding`, as a string.
fn serialize(pairs: &[(Vec<u32>, Vec<u32>)], encoding: Encoding) -> String {
    let scalar = scalar_entries_exec(&entries(pairs));
    string(&urlencoded_serialize_exec(&scalar, encoding))
}

fn count_line(suite: &str, pass: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail=0 fail={fail} total={total}"
    );
}

#[test]
fn wpt_urlencoded_parser_round_trips() {
    let mut pass = 0usize;
    let mut failed = Vec::new();
    for c in PARSER {
        let input = string(c.input);
        let pairs: Vec<(String, String)> = c
            .pairs
            .iter()
            .map(|(n, v)| (string(n), string(v)))
            .collect();
        let name = format!("input {input:?}");
        let mut ok = true;
        if parse_urlencoded(&input) != pairs {
            failed.push(format!("{name}: the test's parser disagrees with WPT"));
            ok = false;
        }
        let tuples: Vec<(Vec<u32>, Vec<u32>)> = c
            .pairs
            .iter()
            .map(|(n, v)| (n.to_vec(), v.to_vec()))
            .collect();
        let serialized = serialize(&tuples, Encoding::Utf8);
        if parse_urlencoded(&serialized) != pairs {
            failed.push(format!(
                "{name}: serialize gave {serialized:?}, which parses differently"
            ));
            ok = false;
        }
        if ok {
            pass = pass.saturating_add(1);
        }
    }
    count_line(
        "WPT url/urlencoded-parser (serialize then parse)",
        pass,
        failed.len(),
        PARSER.len(),
    );
    for f in &failed {
        println!("MISMATCH {f}");
    }
    assert!(failed.is_empty());
    assert_eq!(PARSER.len(), 35);
}

/// A form with one hidden control named `name` with value `value`, submitted
/// from the form itself (as `form.submit()` does).
fn submit_one(enctype: &str, case: &FormCase) -> Option<Vec<u8>> {
    let html = format!(
        "<form id=f method=post action=\"http://example.com/echo\" enctype=\"{enctype}\" \
         accept-charset=\"{}\"><input id=i type=hidden></form>",
        case.encoding
    );
    let mut arena: Arena = parse(&html);
    let input = node(&arena, "i");
    for (k, v) in [("name", case.name), ("value", case.value)] {
        arena.append_attribute(
            input,
            ExecAttr {
                namespace: None,
                prefix: None,
                local_name: u32s(k),
                value: v.to_vec(),
            },
        );
    }
    let rows = clean_rows(&arena);
    let form = node(&arena, "f");
    let base = basic_url_parser(&u32s("http://example.com/page"), None)?;
    let out = submit_exec(
        &arena,
        &rows,
        (form, form),
        Encoding::Utf8,
        &u32s("http://example.com/page"),
        &base,
        b"BOUNDARY",
    );
    match out {
        ExecOutcome::Navigate(n) => n.body.map(|b| b.bytes),
        _ => None,
    }
}

fn isomorphic(cps: &[u32]) -> Vec<u8> {
    cps.iter()
        .map(|&c| u8::try_from(c).unwrap_or(b'?'))
        .collect()
}

fn run_form_table(suite: &str, enctype: &str, table: &[FormCase], skipped: usize, total: usize) {
    let mut pass = 0usize;
    let mut failed = Vec::new();
    for c in table {
        let want = if enctype == "multipart/form-data" {
            let mut w = b"--BOUNDARY\r\nContent-Disposition: form-data; name=\"".to_vec();
            w.extend(isomorphic(c.a));
            w.extend(b"\"\r\n\r\n");
            w.extend(isomorphic(c.b));
            w.extend(b"\r\n--BOUNDARY--\r\n");
            w
        } else {
            isomorphic(c.a)
        };
        let got = submit_one(enctype, c);
        if got.as_deref() == Some(want.as_slice()) {
            pass = pass.saturating_add(1);
        } else {
            failed.push(format!(
                "line {} ({}): got {:?}, want {:?}",
                c.line,
                string(c.description),
                got.as_deref().map(String::from_utf8_lossy),
                String::from_utf8_lossy(&want)
            ));
        }
    }
    count_line(suite, pass, failed.len(), total);
    println!("{suite}: {skipped} calls with a File value skipped (type=file is out)");
    for f in &failed {
        println!("MISMATCH {f}");
    }
    assert!(failed.is_empty());
    assert_eq!(table.len(), total);
}

#[test]
fn wpt_urlencoded2_submission() {
    run_form_table(
        "WPT form-submission-0/urlencoded2 (no File)",
        "application/x-www-form-urlencoded",
        URLENCODED,
        URLENCODED_FILE_CASES_SKIPPED,
        URLENCODED.len(),
    );
}

#[test]
fn wpt_text_plain_submission() {
    run_form_table(
        "WPT form-submission-0/text-plain (no File)",
        "text/plain",
        TEXT_PLAIN,
        TEXT_PLAIN_FILE_CASES_SKIPPED,
        TEXT_PLAIN.len(),
    );
}

#[test]
fn wpt_multipart_submission() {
    run_form_table(
        "WPT form-submission-0/multipart-formdata (no File)",
        "multipart/form-data",
        MULTIPART,
        MULTIPART_FILE_CASES_SKIPPED,
        MULTIPART.len(),
    );
}

/// A xorshift generator with a fixed seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }
}

/// Random strings, weighted to the characters the format treats specially.
fn random_string(rng: &mut Rng) -> String {
    const SPECIAL: &[char] = &[
        ' ', '&', '=', '+', '%', '*', '-', '.', '_', '~', '!', '\'', '(', ')', '\r', '\n', '\0', '#', ';',
        '/', '?', '\u{7F}', '\u{FFFD}', '\u{FEFF}', 'é', 'ə', '†', '💩', '\u{10FFFF}',
    ];
    let len = rng.below(12);
    (0..len)
        .map(|_| match rng.below(3) {
            0 => {
                let i = usize::try_from(rng.below(SPECIAL.len() as u64)).unwrap_or(0);
                SPECIAL.get(i).copied().unwrap_or('a')
            }
            1 => char::from_u32(u32::try_from(rng.below(0x80)).unwrap_or(0x61)).unwrap_or('a'),
            _ => char::from_u32(u32::try_from(rng.below(0x3000)).unwrap_or(0x61)).unwrap_or('b'),
        })
        .collect()
}

#[test]
fn differential_against_form_urlencoded() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let total = 5000usize;
    let mut pass = 0usize;
    let mut failed = Vec::new();
    for _ in 0..total {
        let n = rng.below(5);
        let strings: Vec<(String, String)> = (0..n)
            .map(|_| (random_string(&mut rng), random_string(&mut rng)))
            .collect();
        let tuples: Vec<(Vec<u32>, Vec<u32>)> = strings
            .iter()
            .map(|(a, b)| (u32s(a), u32s(b)))
            .collect();
        let want = {
            let mut s = form_urlencoded::Serializer::new(String::new());
            for (a, b) in &strings {
                s.append_pair(a, b);
            }
            s.finish()
        };
        let got = serialize(&tuples, Encoding::Utf8);
        if got == want {
            pass = pass.saturating_add(1);
        } else {
            failed.push(format!("{strings:?}: got {got:?}, want {want:?}"));
        }
    }
    count_line(
        "differential: urlencoded serializer vs form_urlencoded 1.2.2 (random)",
        pass,
        failed.len(),
        total,
    );
    for f in failed.iter().take(5) {
        println!("MISMATCH {f}");
    }
    assert!(failed.is_empty());
}

#[test]
fn entry_list_of_a_parsed_form_serializes() {
    // The pieces compose: HTML's entry list, then URL's serializer.
    let html = "<form id=f><input name=q value='a b&c'><input name=n value=\u{e9}></form>";
    let list = entries_of(html, "f", None);
    assert_eq!(
        list,
        vec![
            ("q".to_owned(), "a b&c".to_owned()),
            ("n".to_owned(), "\u{e9}".to_owned())
        ]
    );
    let arena = parse(html);
    let rows = clean_rows(&arena);
    let form = node(&arena, "f");
    let got = entry_list(&arena, &rows, form, None, "UTF-8", false).unwrap_or_default();
    let tuples: Vec<(Vec<u32>, Vec<u32>)> = got.iter().map(|(a, b)| (u32s(a), u32s(b))).collect();
    let s = serialize(&tuples, Encoding::Utf8);
    assert_eq!(s, "q=a+b%26c&n=%C3%A9");
    assert_eq!(text(&u32s(&s)), s);
}
