//! Hand-written checks of item 7.16's `fetch()` and XHR (`Fetch`), through
//! the exec kernel (`step_real`), with the network played by the test. These
//! cite no official suite; `theorem_cors_read` and `theorem_forbidden_headers`
//! are what say the kernel does these things for every input.

mod support;

use clazel_fetch::transducer::types::InputBuf;
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::EventRecord;
use support::{Kernel, Out};

fn response_with(header: &str, body: &[u8]) -> Vec<u8> {
    let mut r = format!(
        "HTTP/1.1 200 OK\r\n{header}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    )
    .into_bytes();
    r.extend_from_slice(body);
    r
}

fn has(req: &[u8], what: &[u8]) -> bool {
    req.windows(what.len()).any(|w| w == what)
}

fn t(s: &str) -> Vec<u8> {
    s.as_bytes().to_vec()
}

/// A tab at `http://example.test/page` whose document has the cookie `a=b`.
fn page(k: &mut Kernel) -> u64 {
    k.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let (id, _) = k.open_tab("http://example.test/page", "");
    let id = id.unwrap_or(0);
    k.send(
        id,
        &Msg::CookieSet {
            cookie_string: t("a=b"),
        },
    );
    id
}

fn fetch(
    k: &mut Kernel,
    id: u64,
    method: &str,
    url: &str,
    mode: u64,
    headers: &[&str],
) -> Vec<Out> {
    k.send(
        id,
        &Msg::Fetch {
            request: 5,
            method: t(method),
            url: t(url),
            content_type: Vec::new(),
            body: Vec::new(),
            mode,
            headers: headers.iter().map(|h| t(h)).collect(),
        },
    )
}

fn sub_net(k: &mut Kernel, id: u64, input: InputBuf) -> Vec<Out> {
    k.event(&EventRecord::SubNet {
        renderer: id,
        serial: 0,
        hop: 1,
        input,
    })
}

/// The request the kernel sends once the connection is open.
fn sent(k: &mut Kernel, id: u64) -> Vec<u8> {
    let out = sub_net(k, id, InputBuf::Connected);
    let req = match out.as_slice() {
        [Out::SubSend(_, 0, 1, req)] => Some(req.clone()),
        _ => None,
    };
    assert!(req.is_some(), "no request: {out:?}");
    req.unwrap_or_default()
}

fn failed() -> Msg {
    Msg::FetchFailed { request: 5 }
}

#[test]
fn a_same_origin_cors_get_is_read_and_carries_cookies_and_origin() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    let out = fetch(&mut k, id, "GET", "/api", 1, &[]);
    assert_eq!(
        out,
        vec![Out::SubConnect(id, 0, 1, t("example.test"), 80, false)]
    );
    let req = sent(&mut k, id);
    assert!(req.starts_with(b"GET /api HTTP/1.1\r\n"));
    assert!(has(&req, b"Cookie: a=b"));
    assert!(has(&req, b"Origin: http://example.test"));
    let out = sub_net(
        &mut k,
        id,
        InputBuf::Bytes(response_with("Content-Type: text/plain", b"hi")),
    );
    assert_eq!(
        out,
        vec![
            Out::SubClose(id, 0, 1),
            Out::Frames(
                id,
                vec![
                    Msg::FetchResponse {
                        request: 5,
                        status: 200,
                        content_type: t("text/plain"),
                    },
                    Msg::FetchBody {
                        request: 5,
                        bytes: t("hi"),
                    },
                    Msg::FetchEnd { request: 5 },
                ]
            ),
        ]
    );
}

#[test]
fn a_cross_origin_cors_response_without_permission_is_a_network_error() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    fetch(&mut k, id, "GET", "http://other.test/x", 1, &[]);
    let req = sent(&mut k, id);
    assert!(!has(&req, b"Cookie"), "no credentials cross-origin");
    assert!(has(&req, b"Origin: http://example.test"));
    let out = sub_net(
        &mut k,
        id,
        InputBuf::Bytes(response_with("X-A: 1", b"secret")),
    );
    assert_eq!(out, vec![Out::SubClose(id, 0, 1), Out::To(id, failed())]);
}

#[test]
fn a_cross_origin_cors_response_the_server_allows_is_read() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    fetch(&mut k, id, "GET", "http://other.test/x", 1, &[]);
    sent(&mut k, id);
    let out = sub_net(
        &mut k,
        id,
        InputBuf::Bytes(response_with(
            "Access-Control-Allow-Origin: http://example.test",
            b"ok",
        )),
    );
    assert!(
        matches!(out.as_slice(), [Out::SubClose(..), Out::Frames(_, msgs)] if msgs.get(1) == Some(&Msg::FetchBody { request: 5, bytes: t("ok") })),
        "{out:?}"
    );
}

#[test]
fn a_cross_origin_no_cors_response_is_opaque() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    fetch(&mut k, id, "GET", "http://other.test/x", 2, &[]);
    sent(&mut k, id);
    let out = sub_net(
        &mut k,
        id,
        InputBuf::Bytes(response_with("Access-Control-Allow-Origin: *", b"secret")),
    );
    assert_eq!(
        out,
        vec![
            Out::SubClose(id, 0, 1),
            Out::Frames(
                id,
                vec![
                    Msg::FetchResponse {
                        request: 5,
                        status: 0,
                        content_type: Vec::new(),
                    },
                    Msg::FetchEnd { request: 5 },
                ]
            ),
        ]
    );
}

#[test]
fn a_same_origin_mode_request_to_another_origin_is_refused() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    let out = fetch(&mut k, id, "GET", "http://other.test/x", 0, &[]);
    assert_eq!(out, vec![Out::To(id, failed())]);
}

#[test]
fn forbidden_and_client_headers_are_dropped_and_others_sent() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    fetch(
        &mut k,
        id,
        "GET",
        "/api",
        1,
        &[
            "Cookie",
            "x=y",
            "Sec-Fetch-Site",
            "none",
            "Accept",
            "a/b",
            "X-A",
            "1",
        ],
    );
    let req = sent(&mut k, id);
    assert!(has(&req, b"X-A: 1"), "{}", String::from_utf8_lossy(&req));
    assert!(!has(&req, b"x=y"));
    assert!(!has(&req, b"Sec-Fetch-Site"));
    assert!(!has(&req, b"a/b"));
}

#[test]
fn a_cross_origin_request_that_needs_a_preflight_is_refused() {
    let mut k = Kernel::new();
    let id = page(&mut k);
    let out = fetch(&mut k, id, "GET", "http://other.test/x", 1, &["X-A", "1"]);
    assert_eq!(out, vec![Out::To(id, failed())]);
    let out = fetch(&mut k, id, "PUT", "/api", 1, &[]);
    assert_eq!(out, vec![Out::To(id, failed())]);
    let out = fetch(&mut k, id, "GET", "/api", 1, &["odd"]);
    assert_eq!(out, vec![Out::To(id, failed())]);
}
