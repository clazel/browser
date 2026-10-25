//! WPT `cookies/` `httpCookieTest` cases over a real socket (Phase 3 item
//! 3.8). The converted tables that `clazel-cookie` vendors
//! (`../../clazel-cookie/tests/generated/wpt_cookies.rs`, included, not
//! copied) are run through `clazel_net::fetch_jar`: an in-process
//! `TcpListener` on 127.0.0.1 answers the first request with a redirect that
//! carries the case's `Set-Cookie` values, and the second with a plain
//! response, recording its `Cookie` header. That header must be the case's
//! expected cookies. The resolver maps the case's host to 127.0.0.1.
//!
//! The kernel's `conformance_wpt_cookies.rs` runs the same cases without
//! HTTP (the jar is built by calling the cookie store directly and read
//! through `document.cookie`); the counts are meant to be compared with it.
//! The expected failures are listed in `XFAIL`, each with its reason.
//!
//! Under Miri every case is skipped: it opens sockets, and a cookie call
//! runs the Public Suffix List scan (about ten seconds a call).

use clazel_net::{NetError, Timeouts, fetch_jar};
use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

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

/// 23 October 2026, 00:00:00 UTC, as a time of the cookie model (the
/// kernel test's clock).
const NOW: u64 = 1_792_713_600 + UNIX_EPOCH_1601;

/// The reason of the `secure.https.html` cases.
const SECURE: &str = "the case is served over https (web-platform.test:8443) and reads the cookie over https; there is no TLS yet, so the fetch is http: and a Secure cookie is not stored from, or sent over, an insecure connection";

/// Cases that are expected to fail: (file, name, reason).
const XFAIL: &[(&str, &str, &str)] = &[
    (
        "value.html",
        "Set cookie but ignore value after LF",
        "the Set-Cookie value is `test=13\\nZYX`; the case expects a server that ends the header value at the LF, but this client rejects the whole response as invalid (the `ZYX` line is not a header field), so there is no redirect and no second request",
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

fn local(_: &[u8]) -> Result<Vec<IpAddr>, NetError> {
    Ok(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
}

fn short() -> Timeouts {
    Timeouts {
        connect: Duration::from_secs(1),
        idle: Duration::from_millis(400),
    }
}

/// The reading page's path, as the kernel test chooses it.
fn reader_path(c: &Case) -> String {
    if c.default_path {
        "/cookies/resources/echo-cookie.html".to_string()
    } else {
        c.page.to_string()
    }
}

/// Reads one request head; returns it, or what was read when the peer
/// stops (or 2 s pass).
fn read_head(s: &mut TcpStream) -> Vec<u8> {
    let _ = s.set_read_timeout(Some(Duration::from_secs(2)));
    let mut got = Vec::new();
    let mut buf = [0u8; 1024];
    while !got.ends_with(b"\r\n\r\n") {
        match s.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => got.extend_from_slice(buf.get(..n).unwrap_or_default()),
        }
    }
    got
}

/// The value of the `Cookie` header lines of a request head, joined by
/// `; ` when there are several; empty when there is none.
fn cookie_header(head: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    for line in head.split(|b| *b == b'\n').skip(1) {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let Some(colon) = line.iter().position(|b| *b == b':') else {
            continue;
        };
        let (name, value) = line.split_at(colon);
        if name.eq_ignore_ascii_case(b"cookie") {
            if !out.is_empty() {
                out.extend_from_slice(b"; ");
            }
            out.extend_from_slice(value.get(1..).unwrap_or_default().trim_ascii());
        }
    }
    out
}

/// Runs one case; the `Cookie` header of the second request, or why not.
fn run(c: &Case) -> Result<Vec<u8>, String> {
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let host = "web-platform.test";
    let set_cookies: Vec<Vec<u8>> = c.cookies.iter().map(|v| v.to_vec()).collect();
    let location = format!("http://{host}:{port}{}", reader_path(c));
    let server = thread::spawn(move || -> Vec<u8> {
        // First connection: the redirect with the Set-Cookie values.
        if let Ok((mut s, _)) = listener.accept() {
            read_head(&mut s);
            let mut reply = b"HTTP/1.1 302 Found\r\n".to_vec();
            for v in &set_cookies {
                reply.extend_from_slice(b"Set-Cookie: ");
                reply.extend_from_slice(v);
                reply.extend_from_slice(b"\r\n");
            }
            reply.extend_from_slice(
                format!("Location: {location}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
                    .as_bytes(),
            );
            let _ = s.write_all(&reply);
            let _ = s.flush();
        }
        // Second connection: the reading page.
        let mut seen = Vec::new();
        if let Ok((mut s, _)) = listener.accept() {
            seen = cookie_header(&read_head(&mut s));
            let _ =
                s.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n");
            let _ = s.flush();
        }
        seen
    });
    let url = format!("http://{host}:{port}/cookies/resources/cookie.py");
    // The fetch runs on its own thread so that a hang fails the case.
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let (r, _jar) = fetch_jar(&url, Vec::new(), NOW, short(), local);
        let _ = tx.send(r.map(|resp| resp.body.len()));
    });
    let fetched = rx
        .recv_timeout(Duration::from_secs(10))
        .map_err(|_| "fetch did not return: hang".to_string())?;
    // A failed fetch may leave the server waiting on `accept`; unblock it.
    if fetched.is_err() {
        let _ = TcpStream::connect((Ipv4Addr::LOCALHOST, port));
        let _ = TcpStream::connect((Ipv4Addr::LOCALHOST, port));
    }
    let seen = server.join().map_err(|_| "server panicked".to_string())?;
    fetched.map_err(|e| format!("fetch failed: {e}"))?;
    Ok(seen)
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn wpt_cookies_http_over_sockets() {
    let cases: Vec<&Case> = WPT_COOKIES.iter().filter(|c| c.http).collect();
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    for c in &cases {
        let got = run(c);
        let ok = got.as_deref() == Ok(c.expected);
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
                    "FAIL {}[{}] {:?} (https={}): got {:?}, expected {:?}",
                    c.file,
                    c.index,
                    c.name,
                    c.https,
                    got.as_ref().map(|v| String::from_utf8_lossy(v)),
                    String::from_utf8_lossy(c.expected)
                );
            }
        }
    }
    let total = u64::try_from(cases.len()).unwrap_or(u64::MAX);
    println!(
        "clazel-conformance: suite=\"WPT cookies/ httpCookieTest tables over sockets\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}
