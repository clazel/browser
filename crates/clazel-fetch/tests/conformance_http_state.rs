//! `http-state` cookie parser corpus through the client state machine
//! (docs/phases/phase-3.md item 3.6).
//!
//! The 222 rows of the RFC 6265 interoperability corpus (the same rows
//! `clazel-cookie`'s `conformance_http_state` runs against the jar, vendored
//! there under `tests/data/http-state-parser/` and converted by `cargo xtask
//! testdata` into the generated file included below) are each a response to
//! `http://home.example.org:8888/cookie-parser?<test>` with some `Set-Cookie`
//! header values and a `Location` to `/cookie-parser-result?<test>` (or the
//! row's `sent-to`), whose request's `Cookie` header must be the `sent`
//! cookies. Here the whole fetch is run on the proven transducer, in
//! memory, with the real HTTP and URL functions: `start`, `Connected`, the
//! bytes of that response as the server would write them, `Connected` for the
//! redirect's connection, and the `Cookie` field of the request that
//! `Send` carries is compared with the row's. So the parser of the response,
//! the storage of each field line, the redirect, the retrieval and the
//! serialization of the request are all in the loop.
//!
//! The clock is 1 January 2010, when the corpus was written. The corpus is
//! for RFC 6265: rows where RFC 6265bis draft 22 differs on purpose, or
//! that the HTTP layer rejects, are in `XFAIL` with the reason. Under Miri
//! every 111th row is run.

use clazel_cookie::storage::exec::CookieRecord;
use clazel_fetch::transducer::real::step_real;
use clazel_fetch::transducer::step::start;
use clazel_fetch::transducer::types::{ActionBuf, InputBuf};
use clazel_url::url::parse::basic_url_parser;

/// One converted row.
struct Case {
    name: &'static str,
    received: &'static [&'static [u8]],
    sent_to: Option<&'static str>,
    sent: &'static [(&'static [u8], &'static [u8])],
}

// `const PARSER: &[Case]`, generated from the vendored `parser.json` (by
// `cargo xtask testdata`, into `clazel-cookie`, whose conformance test runs
// the same rows against the jar).
include!("../../clazel-cookie/tests/generated/http_state_parser.rs");

/// 1 January 2010, 00:00:00 UTC.
const NOW_UNIX: u64 = 1_262_304_000;

/// Seconds from 1601-01-01 to 1970-01-01.
const UNIX_EPOCH_1601: u64 = 11_644_473_600;

/// RFC 6265bis §5.6 step 3 makes a name-value pair without "=" a cookie with
/// an empty name and that value, and "=value" a cookie with an empty name;
/// RFC 6265 §5.2 ignored both, which these rows expect.
const NAMELESS: &str = "nameless cookies (RFC 6265bis \u{a7}5.6 step 3; RFC 6265 ignored them)";

/// The row sends a NUL or a carriage return inside a header value: the
/// response is not a valid HTTP message, so the fetch fails (RFC 9110
/// \u{a7}5.5), which is the behaviour of the HTTP layer; Chromium disables
/// the rows too.
const HTTP_LAYER: &str = "a NUL or CR inside the header value: an invalid HTTP message, the fetch fails (RFC 9110 \u{a7}5.5); Chromium disables the row";

/// The row's cookie has Path=/cookie-parser-result/foo/bar and the request is
/// for /cookie-parser-result/f%6Fo/bar: the row expects the percent-encoded
/// path to be decoded before path-matching, which \u{a7}5.1.4 does not do.
const PERCENT_PATH: &str =
    "path-match compares octets, without percent-decoding (\u{a7}5.1.4); Chromium disables the row";

/// RFC 6265 \u{a7}5.2.3 ignored a Domain attribute with an empty value;
/// draft 22 \u{a7}5.6.3 does not.
const EMPTY_DOMAIN: &str = "an empty Domain attribute is not ignored (RFC 6265bis \u{a7}5.6.3)";

/// Rows that are expected to fail: (name, reason). The jar-level rows of
/// `clazel-cookie`'s test, which has the same RFC 6265 differences.
const XFAIL: &[(&str, &str)] = &[
    ("0004", NAMELESS),
    ("0021", NAMELESS),
    ("0023", NAMELESS),
    ("0024", NAMELESS),
    ("0025", NAMELESS),
    ("0026", NAMELESS),
    ("0027", NAMELESS),
    ("0028", NAMELESS),
    ("CHROMIUM0009", NAMELESS),
    ("CHROMIUM0010", NAMELESS),
    ("CHROMIUM0012", NAMELESS),
    ("MOZILLA0012", NAMELESS),
    ("MOZILLA0014", NAMELESS),
    ("MOZILLA0015", NAMELESS),
    ("MOZILLA0016", NAMELESS),
    ("MOZILLA0017", NAMELESS),
    ("NAME0017", NAMELESS),
    ("NAME0023", NAMELESS),
    ("NAME0025", NAMELESS),
    ("NAME0028", NAMELESS),
    ("NAME0031", NAMELESS),
    ("NAME0032", NAMELESS),
    ("NAME0033", NAMELESS),
    ("DISABLED_CHROMIUM0022", HTTP_LAYER),
    ("DISABLED_CHROMIUM0023", HTTP_LAYER),
    ("DISABLED_PATH0029", PERCENT_PATH),
    ("OPTIONAL_DOMAIN0042", EMPTY_DOMAIN),
];

/// The cookie-string the row expects.
fn expected(c: &Case) -> Vec<u8> {
    let mut out = Vec::new();
    for (i, (name, value)) in c.sent.iter().enumerate() {
        if i > 0 {
            out.extend_from_slice(b"; ");
        }
        if !name.is_empty() {
            out.extend_from_slice(name);
            out.push(b'=');
        }
        out.extend_from_slice(value);
    }
    out
}

/// The server's response to the first request: a 302 with the row's
/// `Set-Cookie` lines and its `Location`.
fn response(c: &Case) -> Vec<u8> {
    let target = match c.sent_to {
        None => format!("/cookie-parser-result?{}", c.name),
        Some(url) => url.to_owned(),
    };
    let mut out = b"HTTP/1.1 302 Found\r\n".to_vec();
    for header in c.received {
        out.extend_from_slice(b"Set-Cookie: ");
        out.extend_from_slice(header);
        out.extend_from_slice(b"\r\n");
    }
    out.extend_from_slice(format!("Location: {target}\r\nContent-Length: 0\r\n\r\n").as_bytes());
    out
}

/// The value of the `Cookie` field of a request (empty if it has none).
fn cookie_field(request: &[u8]) -> Vec<u8> {
    for line in request.split(|b| *b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if let Some(value) = line.strip_prefix(b"Cookie: ") {
            return value.to_vec();
        }
    }
    Vec::new()
}

/// Runs the fetch of the row; the `Cookie` field of the request after the
/// redirect, or `None` if the fetch did not get that far.
fn run(c: &Case) -> Option<Vec<u8>> {
    let url = format!("http://home.example.org:8888/cookie-parser?{}", c.name);
    let input: Vec<u32> = url.chars().map(u32::from).collect();
    let parsed = basic_url_parser(&input, None)?;
    let jar: Vec<CookieRecord> = Vec::new();
    let now = NOW_UNIX.saturating_add(UNIX_EPOCH_1601);
    let (state, actions) = start(&parsed, jar, now);
    if !matches!(actions.as_slice(), [ActionBuf::Connect { .. }]) {
        return None;
    }
    let (state, actions) = step_real(state, &InputBuf::Connected);
    if !matches!(actions.as_slice(), [ActionBuf::Send(_)]) {
        return None;
    }
    let (state, actions) = step_real(state, &InputBuf::Bytes(response(c)));
    if !matches!(
        actions.as_slice(),
        [ActionBuf::Close, ActionBuf::Connect { .. }]
    ) {
        return None;
    }
    let (_state, actions) = step_real(state, &InputBuf::Connected);
    match actions.into_iter().next() {
        Some(ActionBuf::Send(bytes)) => Some(cookie_field(&bytes)),
        _ => None,
    }
}

#[test]
fn http_state_parser_through_the_client() {
    let step = if cfg!(miri) { 111 } else { 1 };
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in PARSER.iter().step_by(step) {
        total = total.saturating_add(1);
        let got = run(c);
        let ok = got.as_deref() == Some(expected(c).as_slice());
        let expected_failure = XFAIL.iter().find(|(n, _)| *n == c.name);
        match (ok, expected_failure) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, reason))) => {
                failed = failed.saturating_add(1);
                println!("FAIL (expected to fail, but passes: {reason}) {}", c.name);
            }
            (false, None) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL {} {:?}: got {:?}, expected {:?}",
                    c.name,
                    c.received
                        .iter()
                        .map(|r| String::from_utf8_lossy(r))
                        .collect::<Vec<_>>(),
                    got.as_deref().map(String::from_utf8_lossy),
                    String::from_utf8_lossy(&expected(c))
                );
            }
        }
    }
    if !cfg!(miri) {
        assert_eq!(total, u64::try_from(PARSER.len()).unwrap_or(u64::MAX));
    }
    println!(
        "clazel-conformance: suite=\"http-state parser corpus (through the client)\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}
