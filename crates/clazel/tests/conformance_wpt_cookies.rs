//! WPT `cookies/` conformance end to end through real processes
//! (docs/phases/phase-2.md item 2.16): the converted tables that `clazel-cookie`
//! vendors, the same cases `clazel-kernel`'s `conformance_wpt_cookies.rs` runs
//! with fake renderers, here run with the host shell and a real sandboxed
//! `clazel-renderer` process per case. The renderer's script (the case's
//! `document.cookie` assignments and a read, JavaScript) is the case's own;
//! the answer is read from what the host logged the kernel sending the
//! renderer, which is the frame the renderer received.
//!
//! - **`domCookieTest` cases** (11): the kernel opens a tab on the page and the
//!   renderer sets the cookies and reads `document.cookie`.
//! - **`httpCookieTest` cases** (167): the kernel cannot receive a
//!   `Set-Cookie` header (Phase 3), so, as the kernel's test does, the jar the
//!   HTTP path of `clazel-cookie` builds is preloaded into the host's kernel
//!   state, and the renderer, in a tab on the page that reads, runs
//!   `document.cookie`.
//!
//! Each case has a fresh host (a fresh kernel) and the clock fixed at 23
//! October 2026, as in the kernel's test. The expected failures are the
//! kernel test's `XFAIL`. Cases
//! run on 8 threads; each is one process.

use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use clazel::Host;
use clazel_cookie::matching::exec::canonicalize_a_host_name;
use clazel_cookie::storage::exec::{
    CookieRecord, HttpRequestRecord, RequestContextRecord, RequestUrlRecord,
    store_a_set_cookie_string_exec,
};
use clazel_origin::exec::url_origin_exec;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;
use clazel_url::url::serialize::url_path_serializer;

mod support;

/// One converted case.
struct Case {
    file: &'static str,
    index: usize,
    name: &'static str,
    page: &'static str,
    https: bool,
    http: bool,
    default_path: bool,
    cookies: &'static [&'static [u8]],
    expected: &'static [u8],
}

// `const WPT_COOKIES: &[Case]`, generated from the pages vendored by
// `clazel-cookie`.
include!("../../clazel-cookie/tests/generated/wpt_cookies.rs");

/// Seconds from 1601-01-01T00:00:00Z to 1970-01-01T00:00:00Z.
const UNIX_EPOCH_1601: u64 = 11_644_473_600;

/// 23 October 2026, 00:00:00 UTC, as a time of the cookie model.
const NOW: u64 = 1_792_713_600 + UNIX_EPOCH_1601;

const WORKERS: usize = 8;

/// Cases that are expected to fail: (file, name, reason). The kernel test's.
const XFAIL: &[(&str, &str, &str)] = &[(
    "value.html",
    "Set cookie but ignore value after LF",
    "the string is `test=13\\nZYX`, a Set-Cookie value with a line feed: the HTTP layer (Phase 3) ends the header value at the LF, so the cookie parser sees `test=13`; \u{a7}5.6 step 1 ignores a string with a CTL character, so given the raw string it ignores it",
)];

fn parse(s: &str) -> Option<ParsedUrl> {
    let points: Vec<u32> = s.chars().map(u32::from).collect();
    basic_url_parser(&points, None)
}

/// The request URL of a parsed URL, as far as cookies read it.
fn request_url(url: &ParsedUrl) -> Option<RequestUrlRecord> {
    let narrow = |units: &[u32]| -> Option<Vec<u8>> {
        units.iter().map(|c| u8::try_from(*c).ok()).collect()
    };
    Some(RequestUrlRecord {
        scheme: narrow(&url.scheme)?,
        host: canonicalize_a_host_name(&url.host),
        path: narrow(&url_path_serializer(&url.path))?,
    })
}

/// A response to an HTTP request from a client with no "site for cookies".
fn http_context(url: &ParsedUrl) -> RequestContextRecord {
    RequestContextRecord::Http(HttpRequestRecord {
        url_origin: url_origin_exec(url, 0),
        site_for_cookies: None,
        is_reload_navigation: false,
        reloaded_document_was_same_site: false,
        navigates_top_level_traversable: false,
        method_is_safe: true,
        target_is_active_or_top_level: true,
    })
}

/// The origin of the server a case runs on.
fn base(c: &Case) -> &'static str {
    if c.https {
        "https://web-platform.test:8443"
    } else {
        "http://web-platform.test:8000"
    }
}

/// The statement of a script that sets `cookie` as `document.cookie`: the
/// text is a JavaScript string literal (every character outside printable
/// ASCII, and the quote and the backslash, as `\uXXXX` escapes of UTF-16
/// code units), so any cookie string can be written, a line feed included.
fn script_statement(cookie: &[u8]) -> Result<String, String> {
    let text = std::str::from_utf8(cookie).map_err(|_| "not UTF-8".to_owned())?;
    let mut literal = String::from("\"");
    for c in text.chars() {
        if c.is_ascii_graphic() && c != '"' && c != '\\' || c == ' ' {
            literal.push(c);
        } else {
            let mut units = [0u16; 2];
            for unit in c.encode_utf16(&mut units) {
                literal.push_str(&format!("\\u{unit:04x}"));
            }
        }
    }
    literal.push('"');
    Ok(format!("document.cookie = {literal};"))
}

/// What the kernel answered the renderer's last `document.cookie` read, as
/// the host logged it (a quoted string).
fn answer(host: &Host) -> Result<String, String> {
    let line = host
        .log
        .iter()
        .rev()
        .find_map(|l| l.strip_prefix("renderer 0 <- result "));
    line.map(str::to_owned)
        .ok_or_else(|| format!("no answer; host log: {:#?}", host.log))
}

/// Run one case through the host and a real renderer process.
fn run(c: &Case) -> Result<String, String> {
    let mut host = Host::new({
        let renderer = support::binary("clazel-renderer");
        move |_| std::process::Command::new(&renderer)
    });
    host.clock = Some(NOW);
    let (url, script) = if c.http {
        let source = parse(&format!("{}/cookies/resources/cookie.py", base(c)))
            .ok_or("cannot parse the source URL")?;
        let mut jar: Vec<CookieRecord> = Vec::new();
        for cookie in c.cookies {
            jar = store_a_set_cookie_string_exec(
                &jar,
                cookie,
                &request_url(&source).ok_or("no request URL")?,
                &http_context(&source),
                NOW,
            );
        }
        host.state.jar = jar;
        let reader = if c.default_path {
            "/cookies/resources/echo-cookie.html"
        } else {
            c.page
        };
        (
            format!("{}{reader}", base(c)),
            "document.cookie;".to_owned(),
        )
    } else {
        let mut lines = Vec::new();
        for cookie in c.cookies {
            lines.push(script_statement(cookie)?);
        }
        lines.push("document.cookie;".to_owned());
        (format!("{}{}", base(c), c.page), lines.join("\n"))
    };
    host.open_tab(&url, &script);
    if !host.run(std::time::Duration::from_secs(60)) {
        return Err(format!("renderer still running; host log: {:#?}", host.log));
    }
    answer(&host)
}

/// Run every case with `http == http` on `WORKERS` threads and print the
/// suite line.
fn suite(name: &str, http: bool) {
    let cases: Vec<&Case> = WPT_COOKIES.iter().filter(|c| c.http == http).collect();
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, Result<String, String>)>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..WORKERS {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Ordering::SeqCst);
                    let Some(c) = cases.get(i) else { break };
                    let got = run(c);
                    if let Ok(mut r) = results.lock() {
                        r.push((i, got));
                    }
                }
            });
        }
    });
    let results = results.into_inner().unwrap_or_default();
    let (mut pass, mut xfail, mut failed) = (0u64, 0u64, 0u64);
    for (i, got) in &results {
        let Some(c) = cases.get(*i) else { continue };
        let want = format!("{:?}", String::from_utf8_lossy(c.expected));
        let ok = got.as_ref().is_ok_and(|g| *g == want);
        let expected_failure = XFAIL.iter().find(|(f, n, _)| *f == c.file && *n == c.name);
        match (ok, expected_failure) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, _, reason))) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL (expected to fail, but passes: {reason}) {}[{}] {:?}",
                    c.file, c.index, c.name
                );
            }
            (false, None) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL {}[{}] {:?}: got {got:?}, expected {want}",
                    c.file, c.index, c.name
                );
            }
        }
    }
    let total = u64::try_from(cases.len()).unwrap_or(u64::MAX);
    assert_eq!(
        u64::try_from(results.len()).unwrap_or(u64::MAX),
        total,
        "a case did not report"
    );
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}

#[test]
#[cfg_attr(miri, ignore = "spawns a process per case and calls the OS sandbox")]
fn wpt_cookies_dom_through_processes() {
    suite(
        "WPT cookies/ domCookieTest, document.cookie set and get through real processes",
        false,
    );
}

#[test]
#[cfg_attr(miri, ignore = "spawns a process per case and calls the OS sandbox")]
fn wpt_cookies_http_read_through_processes() {
    suite(
        "WPT cookies/ httpCookieTest, document.cookie read through real processes",
        true,
    );
}
