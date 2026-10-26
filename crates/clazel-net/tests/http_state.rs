//! The `http-state` cookie parser corpus over real sockets (Phase 3 item
//! 3.8). The 222 rows that `clazel-fetch`'s `conformance_http_state` drives
//! through the transducer in memory are here fetched with
//! `clazel_net::fetch::fetch_jar` from an in-process HTTP server on
//! 127.0.0.1: the request `GET /cookie-parser?<name>` is answered with the
//! row's `Set-Cookie` lines and a redirect to the row's target (by default
//! `/cookie-parser-result?<name>`; for the rows with `sent-to`, the same URL
//! with the listener's port in place of 8888), and the `Cookie` header of
//! the request that follows the redirect, as the server read it off the
//! socket, is compared with the row's `sent` cookies. The resolver maps every
//! name in `example.org` (`home`, `sibling`, ...) to 127.0.0.1.
//!
//! The clock and the `XFAIL` rows are those of the transducer-only test: a
//! row's result here must be that row's result there. Sockets cannot be
//! opened under Miri, so the test is ignored there.

use clazel_net::{NetError, Timeouts, fetch_jar};
use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

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

/// The listener's port stands in for the corpus's 8888.
const CORPUS_PORT: &str = ":8888";

/// The `Location` of the redirect for the row, towards the listener.
fn location(c: &Case, port: u16) -> String {
    match c.sent_to {
        None => format!("/cookie-parser-result?{}", c.name),
        Some(url) => url.replacen(CORPUS_PORT, &format!(":{port}"), 1),
    }
}

/// The server's response to the first request: a 302 with the row's
/// `Set-Cookie` lines and its `Location`.
fn response(c: &Case, port: u16) -> Vec<u8> {
    let mut out = b"HTTP/1.1 302 Found\r\n".to_vec();
    for header in c.received {
        out.extend_from_slice(b"Set-Cookie: ");
        out.extend_from_slice(header);
        out.extend_from_slice(b"\r\n");
    }
    out.extend_from_slice(
        format!(
            "Location: {}\r\nContent-Length: 0\r\n\r\n",
            location(c, port)
        )
        .as_bytes(),
    );
    out
}

/// The value of the `Cookie` field of a request head (empty if it has none).
fn cookie_field(request: &[u8]) -> Vec<u8> {
    for line in request.split(|b| *b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        if let Some(value) = line.strip_prefix(b"Cookie: ") {
            return value.to_vec();
        }
    }
    Vec::new()
}

/// Reads until the end of the request head, or the peer stops (or 2 s pass).
fn read_head(s: &mut TcpStream) -> Vec<u8> {
    let _ = s.set_read_timeout(Some(Duration::from_secs(2)));
    let mut got = Vec::new();
    let mut buf = [0u8; 1024];
    while !got.ends_with(b"\r\n\r\n") && got.len() < 0x10000 {
        match s.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => got.extend_from_slice(buf.get(..n).unwrap_or_default()),
        }
    }
    got
}

/// The `Cookie` field of the last request that was not the first of a row.
type Seen = Arc<Mutex<Option<Vec<u8>>>>;

/// Serves connections one after another until `stop` is set: a request for
/// `/cookie-parser?<name>` gets the row's redirect, any other gets a 200 and
/// its `Cookie` field is recorded in `seen`.
fn serve(listener: &TcpListener, port: u16, stop: &AtomicBool, seen: &Seen) {
    while let Ok((mut s, _)) = listener.accept() {
        if stop.load(Ordering::SeqCst) {
            return;
        }
        let head = read_head(&mut s);
        let first = head
            .strip_prefix(b"GET /cookie-parser?")
            .and_then(|rest| rest.split(|b| *b == b' ').next());
        let reply = match first {
            Some(name) => match PARSER.iter().find(|c| c.name.as_bytes() == name) {
                Some(c) => response(c, port),
                None => b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n".to_vec(),
            },
            None => {
                if let Ok(mut slot) = seen.lock() {
                    *slot = Some(cookie_field(&head));
                }
                b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n".to_vec()
            }
        };
        let _ = s.write_all(&reply);
        let _ = s.flush();
    }
}

fn local(host: &[u8]) -> Result<Vec<IpAddr>, NetError> {
    if host.ends_with(b"example.org") {
        Ok(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
    } else {
        Err(NetError::Connect(std::io::ErrorKind::NotFound))
    }
}

fn short() -> Timeouts {
    Timeouts {
        connect: Duration::from_secs(1),
        idle: Duration::from_secs(2),
    }
}

/// Fetches the row; the `Cookie` field of the request after the redirect, or
/// `None` if the fetch did not get that far.
fn run(c: &Case, port: u16, seen: &Seen) -> Option<Vec<u8>> {
    if let Ok(mut slot) = seen.lock() {
        *slot = None;
    }
    let url = format!("http://home.example.org:{port}/cookie-parser?{}", c.name);
    let now = NOW_UNIX.saturating_add(UNIX_EPOCH_1601);
    let (_result, _jar) = fetch_jar(&url, Vec::new(), now, short(), local);
    seen.lock().ok().and_then(|slot| slot.clone())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn http_state_parser_over_sockets() -> Result<(), String> {
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let stop = Arc::new(AtomicBool::new(false));
    let seen: Seen = Arc::new(Mutex::new(None));
    let server = {
        let (stop, seen) = (Arc::clone(&stop), Arc::clone(&seen));
        thread::spawn(move || serve(&listener, port, &stop, &seen))
    };
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in PARSER {
        total = total.saturating_add(1);
        let got = run(c, port, &seen);
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
    // Wake the accept loop so that the server thread ends.
    stop.store(true, Ordering::SeqCst);
    let _ = TcpStream::connect((Ipv4Addr::LOCALHOST, port));
    let _ = server.join();
    assert_eq!(total, u64::try_from(PARSER.len()).unwrap_or(u64::MAX));
    println!(
        "clazel-conformance: suite=\"http-state parser corpus (over sockets)\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
    Ok(())
}
