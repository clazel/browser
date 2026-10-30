//! `clazel browse` through real processes against an in-process server
//! (phase-4.md item 4.16, "Through real processes"): the kernel fetches
//! every page from the server (`support/server.rs`), a real sandboxed
//! `clazel-renderer` parses it, and the loop of `cli/browse.rs` prints it.
//!
//! - **html5lib tree-construction inputs**: every document case of the
//!   suite `clazel-treebuilder` vendors (1,761; the fragment cases are not
//!   documents, the scripted ones are only counted) is served as
//!   `text/html; charset=utf-8` and visited with `g URL` in one tab. Each
//!   page printed must be exactly what the same pipeline gives in this
//!   process (`clazel_renderer::pipeline::render` at the renderer's width,
//!   through `fit`): the kernel's URL as the address line, the title, the
//!   text and the numbered links. The layout itself is checked against
//!   its golden fixtures by `clazel-text`; this checks that what the
//!   renderer process sends is what reaches the user, under the kernel's
//!   URL, and that a same-origin navigation commits into the same renderer.
//! - **A page with links**: link numbers follow the links, the address line
//!   is the kernel's committed URL at every step, a same-origin link commits
//!   into the same renderer, a cross-origin one kills it and spawns a new
//!   one, and the page's `Set-Cookie` reaches the kernel's jar and comes
//!   back on the next same-origin request and on no other origin's.
//! - **WPT `cookies/` through the kernel's `Set-Cookie` path**: the
//!   `httpCookieTest` rows Phase 3 could run only with a preloaded jar (see
//!   `conformance_wpt_cookies.rs`) or without the kernel (`clazel-net`'s
//!   `wpt_cookies.rs`). Here a tab navigates to the case's page, the server
//!   answers with a redirect carrying the case's `Set-Cookie` values, the
//!   kernel stores them and follows the redirect, and the `Cookie` field the
//!   server receives must be the case's expected cookies; then a script tab
//!   on the reading page (a real renderer, kind 1) reads `document.cookie`
//!   from the same kernel, which must be the same string.
//!
//! Every test spawns processes and enters the OS sandbox, so none runs
//! under Miri.
#![cfg(unix)]

mod support;

#[path = "support/server.rs"]
mod server;

#[path = "../cli/browse.rs"]
mod browse;

use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::OutputRecord;
use clazel_renderer::pipeline::{fit, render};
use server::{Reply, Request, Server, field, serve};

// `CASES`, the html5lib tree-construction cases, as `clazel-text`'s golden
// test reads them.
include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

/// The width `browse` prints at: wide enough that no address line, title
/// or link of these pages wraps. The renderer lays out at its default.
const WIDE: usize = 4096;

/// A `200` reply of `body` with the content type `ct` and extra fields.
fn page(ct: &str, extra: &str, body: &[u8]) -> Reply {
    Reply {
        head: format!("HTTP/1.1 200 OK\r\nContent-Type: {ct}\r\n{extra}"),
        piece: body.to_vec(),
        times: 1,
    }
}

/// A host whose renderers are the real one and whose connections all go
/// to `server`.
fn real_host(server: &Server) -> Host {
    let renderer = support::binary("clazel-renderer");
    let mut host = Host::new(move |_| Command::new(&renderer));
    host.route = Some(server.addr);
    host
}

/// Run `browse` at `url` with these commands, `width` wide; its output.
fn browse_with(host: &mut Host, url: &str, commands: &[String], width: usize) -> String {
    let input = commands.join("\n");
    let mut out = Vec::new();
    let result = browse::browse(host, url, input.as_bytes(), &mut out, width);
    assert!(result.is_ok(), "{result:?}");
    String::from_utf8_lossy(&out).into_owned()
}

/// What `browse` printed for each page, from its address line to the
/// prompt after it: the pieces between the rules.
fn pages_of(out: &str, width: usize) -> Vec<&str> {
    let rule = format!("{}\n", "-".repeat(width));
    out.split(rule.as_str()).skip(1).collect()
}

/// `s` with every control character but those in `keep` replaced by
/// U+FFFD, as `browse` prints what a renderer sent.
fn clean(s: &str, keep: &[char]) -> String {
    s.chars()
        .map(|c| {
            if c.is_control() && !keep.contains(&c) {
                '\u{FFFD}'
            } else {
                c
            }
        })
        .collect()
}

/// What `browse` prints for the page the pipeline makes of `body` at
/// `url`, followed by the prompt.
fn expected_print(url: &str, ct: &str, body: &[u8]) -> String {
    let shown = render(
        url.as_bytes(),
        ct.as_bytes(),
        body,
        clazel_renderer::DEFAULT_WIDTH,
    );
    let Msg::Display { title, text, links } = fit(shown) else {
        return String::new();
    };
    let lossy = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
    let mut s = format!(
        "URL: {url}\n{}\n\n{}\nLinks:\n",
        clean(&lossy(&title), &[]),
        clean(&lossy(&text), &['\n'])
    );
    for (n, l) in links.iter().enumerate() {
        s.push_str(&format!(
            "[{}] {}\n",
            n.saturating_add(1),
            clean(&lossy(l), &[])
        ));
    }
    s.push_str("> ");
    s
}

const HTML_UTF8: &str = "text/html; charset=utf-8";

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn html5lib_tree_construction_inputs_through_browse() {
    let cases: Vec<&'static Case> = CASES.iter().filter(|c| c.fragment.is_none()).collect();
    let served = cases.clone();
    let server = serve(move |r: &Request| {
        let i = r
            .path
            .strip_prefix("/tc/")
            .and_then(|n| n.parse::<usize>().ok());
        match i.and_then(|i| served.get(i)) {
            Some(c) => page(HTML_UTF8, "", c.data.as_bytes()),
            None => page("text/plain", "", b"no such case"),
        }
    });
    let mut host = real_host(&server);
    let url = |i: usize| format!("http://t.test/tc/{i}");
    let mut commands: Vec<String> = (1..cases.len()).map(|i| format!("g {}", url(i))).collect();
    commands.push("q".to_owned());
    let start = Instant::now();
    let out = browse_with(&mut host, &url(0), &commands, WIDE);
    let printed = pages_of(&out, WIDE);
    let mut differ = Vec::new();
    for (i, c) in cases.iter().enumerate() {
        let want = expected_print(&url(i), HTML_UTF8, c.data.as_bytes());
        match printed.get(i) {
            Some(got) if *got == want => {}
            got => differ.push(format!(
                "{}[{}] {:?}:\n got {got:?}\nwant {want:?}",
                c.file, c.index, c.data
            )),
        }
    }
    println!(
        "clazel-conformance: suite=\"html5lib tree-construction inputs through clazel browse and a real renderer\" pass={} xfail=0 fail={} total={} ({:?})",
        cases.len().saturating_sub(differ.len()),
        differ.len(),
        cases.len(),
        start.elapsed()
    );
    assert!(differ.is_empty(), "{differ:#?}");
    // One origin: every page was committed into the first renderer.
    assert!(
        !host.log.iter().any(|l| l.starts_with("renderer 1 ")),
        "a second renderer was started"
    );
    let requests = server.seen.lock().map(|s| s.len()).unwrap_or(0);
    assert_eq!(requests, cases.len());
}

#[test]
#[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
fn link_numbers_the_address_line_another_origin_and_set_cookie() {
    let server = serve(|r: &Request| {
        match (r.host.as_str(), r.path.as_str()) {
        ("a.test", "/") => page(
            "text/html",
            "Set-Cookie: k=v; Path=/\r\n",
            b"<title>Links</title><p>Start <a href=\"/two\">two</a> <a href=\"http://b.test/x\">b</a></p><iframe src=\"frame\"></iframe>",
        ),
        ("a.test", "/two") => page(
            "text/html",
            "",
            b"<title>Two</title><p>second <a href=\"/\">home</a></p>",
        ),
        ("b.test", "/x") => page("text/html", "", b"<title>B</title><p>other origin</p>"),
        _ => page("text/html", "", b"<title>404</title>"),
    }
    });
    let mut host = real_host(&server);
    let commands: Vec<String> = ["1", "1", "2", "q"].map(str::to_owned).to_vec();
    let out = browse_with(&mut host, "http://a.test/", &commands, 60);
    let pages = pages_of(&out, 60);
    let want = [
        "URL: http://a.test/\nLinks\n\nStart two[1] b[2]\n\n[3]\nLinks:\n[1] http://a.test/two\n[2] http://b.test/x\n[3] http://a.test/frame\n> ",
        "URL: http://a.test/two\nTwo\n\nsecond home[1]\nLinks:\n[1] http://a.test/\n> ",
        "URL: http://a.test/\nLinks\n\nStart two[1] b[2]\n\n[3]\nLinks:\n[1] http://a.test/two\n[2] http://b.test/x\n[3] http://a.test/frame\n> ",
        "URL: http://b.test/x\nB\n\nother origin\nLinks:\n> ",
    ];
    assert_eq!(pages, want, "{out}");
    // Same origin: committed into renderer 0; another origin: renderer 0
    // killed and renderer 1 spawned for it.
    let log = host.log.join("\n");
    for line in [
        "renderer 0 <- commit \"http://a.test/two\" (kind 0)",
        "renderer 0 <- commit \"http://a.test/\" (kind 0)",
        "renderer 0 exited: killed by the kernel",
        "renderer 1 <- commit \"http://b.test/x\" (kind 0)",
    ] {
        assert!(log.contains(line), "missing {line:?} in:\n{log}");
    }
    // The page's `Set-Cookie` reached the jar, and went back to its origin
    // only.
    assert!(
        host.state
            .jar
            .iter()
            .any(|c| c.name == b"k" && c.value == b"v"),
        "jar: {:?}",
        host.state.jar.len()
    );
    let seen = server.seen.lock().map(|s| s.clone()).unwrap_or_default();
    let cookie_of: Vec<(String, String, String)> = seen
        .iter()
        .map(|r| (r.host.clone(), r.path.clone(), field(&r.head, "cookie")))
        .collect();
    assert_eq!(
        cookie_of,
        [
            ("a.test", "/", ""),
            ("a.test", "/two", "k=v"),
            ("a.test", "/", "k=v"),
            ("b.test", "/x", ""),
        ]
        .map(|(h, p, c)| (h.to_owned(), p.to_owned(), c.to_owned()))
        .to_vec()
    );
}

/// WPT `cookies/` through the kernel's `Set-Cookie` path (see the module
/// docs).
mod wpt {
    use super::*;

    /// One WPT `cookies/` case, as `conformance_wpt_cookies.rs` reads them.
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

    /// 23 October 2026, 00:00:00 UTC, the clock of the other cookie tests.
    const NOW: u64 = 1_792_713_600 + UNIX_EPOCH_1601;

    /// The reason of the `secure.https.html` cases (`clazel-net`'s).
    const SECURE: &str = "the case is served over https and reads the cookie over https; this branch has no TLS in the kernel's fetch (3.5), so the page is fetched over http: and a Secure cookie is not stored from an insecure connection";

    /// Cases expected to fail: (file, name, reason), `clazel-net`'s list.
    const XFAIL: &[(&str, &str, &str)] = &[
        (
            "value.html",
            "Set cookie but ignore value after LF",
            "the Set-Cookie value is `test=13\\nZYX`; the case expects a server that ends the header value at the LF, but the kernel's HTTP parser rejects the whole response (the `ZYX` line is not a field line), so there is no redirect and no second request",
        ),
        (
            "secure.https.html",
            "Set cookie for Secure attribute",
            SECURE,
        ),
        (
            "secure.https.html",
            "Set cookie for seCURe attribute",
            SECURE,
        ),
        (
            "secure.https.html",
            "Set cookie for for Secure= attribute",
            SECURE,
        ),
        ("secure.https.html", "Set cookie for Secure=aaaa", SECURE),
        (
            "secure.https.html",
            "Set cookie for Secure space equals",
            SECURE,
        ),
        (
            "secure.https.html",
            "Set cookie for Secure equals space",
            SECURE,
        ),
        ("secure.https.html", "Set cookie for spaced Secure", SECURE),
        (
            "secure.https.html",
            "Set cookie for space Secure with ;",
            SECURE,
        ),
        (
            "secure.https.html",
            "Ignore name- and value-less `Set-Cookie: ; secure`",
            SECURE,
        ),
    ];

    /// The reading page's path, as the other cookie tests choose it.
    fn reader_path(c: &Case) -> &'static str {
        if c.default_path {
            "/cookies/resources/echo-cookie.html"
        } else {
            c.page
        }
    }

    /// Pump `host` until `done` holds or 20 s pass; whether it held.
    fn pump_until(host: &mut Host, mut done: impl FnMut(&Host) -> bool) -> bool {
        let end = Instant::now()
            .checked_add(Duration::from_secs(20))
            .unwrap_or_else(Instant::now);
        while !done(host) {
            if Instant::now() >= end {
                return false;
            }
            host.pump(Duration::from_millis(20));
        }
        true
    }

    /// A case's `Cookie` field and `document.cookie`, or why there are none.
    type Outcome = Result<(String, String), String>;

    /// One case through the kernel: the `Cookie` field of the request for the
    /// reading page, and `document.cookie` read there by a script tab.
    fn cookie_case(c: &'static Case) -> Outcome {
        let reader = reader_path(c);
        let server = serve(move |r: &Request| {
            if r.path == "/cookies/resources/cookie.py" {
                let mut head = "HTTP/1.1 302 Found\r\n".to_owned();
                for v in c.cookies {
                    head.push_str("Set-Cookie: ");
                    head.push_str(&String::from_utf8_lossy(v));
                    head.push_str("\r\n");
                }
                head.push_str(&format!(
                    "Location: http://web-platform.test:8000{reader}\r\n"
                ));
                Reply {
                    head,
                    piece: Vec::new(),
                    times: 0,
                }
            } else {
                page("text/html", "", b"")
            }
        });
        let mut host = real_host(&server);
        host.clock = Some(NOW);
        let tab = host.open("http://web-platform.test:8000/cookies/resources/cookie.py");
        let shown = pump_until(&mut host, |h| {
            h.shown
                .iter()
                .any(|o| matches!(o, OutputRecord::Show { tab: t, .. } if *t == tab))
                || h.log.iter().any(|l| l.contains("<- Error"))
        });
        if !shown {
            return Err(format!("no page; host log: {:#?}", host.log));
        }
        let seen = server.seen.lock().map(|s| s.clone()).unwrap_or_default();
        let header = seen
            .iter()
            .find(|r| r.path == reader)
            .map(|r| field(&r.head, "cookie"))
            .ok_or_else(|| format!("the reading page was not requested: {seen:?}"))?;
        let reader_tab = host.state.next_id;
        host.open_tab(
            &format!("http://web-platform.test:8000{reader}"),
            "cookie-get",
        );
        let prefix = format!("renderer {reader_tab} <- result ");
        let mut answer = None;
        let read = pump_until(&mut host, |h| {
            answer = h
                .log
                .iter()
                .find_map(|l| l.strip_prefix(prefix.as_str()).map(str::to_owned));
            answer.is_some()
        });
        match (read, answer) {
            (true, Some(a)) => Ok((header, a)),
            _ => Err(format!("no document.cookie; host log: {:#?}", host.log)),
        }
    }

    #[test]
    #[cfg_attr(miri, ignore = "spawns processes and calls the OS sandbox")]
    fn wpt_cookies_http_through_the_kernels_set_cookie_path() {
        let cases: Vec<&'static Case> = WPT_COOKIES.iter().filter(|c| c.http).collect();
        let next = AtomicUsize::new(0);
        let results: Mutex<Vec<(usize, Outcome)>> = Mutex::new(Vec::new());
        std::thread::scope(|s| {
            for _ in 0..8 {
                s.spawn(|| {
                    loop {
                        let i = next.fetch_add(1, Ordering::SeqCst);
                        let Some(c) = cases.get(i) else { break };
                        let got = cookie_case(c);
                        if let Ok(mut r) = results.lock() {
                            r.push((i, got));
                        }
                    }
                });
            }
        });
        let results = results.into_inner().unwrap_or_default();
        let (mut pass, mut xfail, mut failed) = (0usize, 0usize, Vec::new());
        for (k, c) in cases.iter().enumerate() {
            let want = String::from_utf8_lossy(c.expected).into_owned();
            let mine = results.iter().find(|(i, _)| *i == k).map(|(_, g)| g);
            let ok = matches!(mine, Some(Ok((h, d))) if *h == want && *d == format!("{want:?}"));
            let expected_failure = XFAIL.iter().find(|(f, n, _)| *f == c.file && *n == c.name);
            match (ok, expected_failure) {
                (true, None) => pass = pass.saturating_add(1),
                (false, Some(_)) => {
                    xfail = xfail.saturating_add(1);
                    let got = mine.map(|g| g.as_ref().map_err(|_| "no page or no answer"));
                    println!(
                        "XFAIL {}[{}] {:?}: got {got:?}, expected {want:?}",
                        c.file, c.index, c.name
                    );
                }
                (true, Some((_, _, reason))) => failed.push(format!(
                    "expected to fail, but passes ({reason}): {}[{}] {:?}",
                    c.file, c.index, c.name
                )),
                (false, None) => failed.push(format!(
                    "{}[{}] {:?} (https={}): got {mine:?}, expected {want:?}",
                    c.file, c.index, c.name, c.https
                )),
            }
        }
        println!(
            "clazel-conformance: suite=\"WPT cookies/ httpCookieTest through the kernel's Set-Cookie path and real processes\" pass={pass} xfail={xfail} fail={} total={}",
            failed.len(),
            cases.len()
        );
        assert_eq!(results.len(), cases.len(), "a case did not report");
        assert!(failed.is_empty(), "{failed:#?}");
    }
}
