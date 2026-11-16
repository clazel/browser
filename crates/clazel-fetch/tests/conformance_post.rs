//! Differential test of fetches with a method and a body (item 6.16): random
//! `POST` and `GET` requests with random redirect chains, run through the
//! proven transducer (`step_real`: the real HTTP parser, the real URL parser,
//! the real cookie jar) in memory, against a reference model written from
//! Fetch's HTTP-redirect fetch step 12 and RFC 9110 §15.4 (301 and 302 turn a
//! `POST` into a `GET` without a body, 303 does so for every method but `GET`
//! and `HEAD`, 307 and 308 keep method and body, so the body is sent again),
//! Fetch §4.6 steps 6 to 9 (`Content-Type`, `Content-Length`) and "append a
//! request `Origin` header" (`Origin` on a method that is not `GET` or
//! `HEAD`), resolving `Location` with rust-url. The two must send the same
//! octets at every hop: the head, the empty line and the body, and end the
//! same way. Bodies include CR, LF, NUL and octets above 0x7F.
//!
//! The generator is a fixed-seed linear congruential generator. Prints
//! `clazel-conformance:` with the number of runs that agree.

use clazel_cookie::storage::exec::CookieRecord;
use clazel_fetch::request::build::{PayloadBuf, ReqBuf};
use clazel_fetch::transducer::real::step_real;
use clazel_fetch::transducer::spec::Reason;
use clazel_fetch::transducer::step::{apply_ops_exec, start_req};
use clazel_fetch::transducer::types::{ActionBuf, InputBuf};
use clazel_url::url::parse::basic_url_parser;
use url::Url;

/// A fixed-seed generator (Knuth's MMIX constants).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(1).max(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
    fn pick<T: Copy>(&mut self, items: &[T], default: T) -> T {
        items
            .get(self.below(items.len()))
            .copied()
            .unwrap_or(default)
    }
}

const START_URLS: &[&str] = &[
    "http://example.test/",
    "http://example.test/a?x=1",
    "http://other.test:8080/a/b",
];
const LOCATIONS: &[&str] = &[
    "/a",
    "b",
    "../c?q=1",
    "//other.test/x",
    "http://example.test:81/y",
];
const STATUSES: &[u16] = &[301, 302, 303, 307, 308, 301, 302, 303, 307, 308, 200];
const TYPES: &[&str] = &[
    "application/x-www-form-urlencoded",
    "text/plain;charset=UTF-8",
    "multipart/form-data; boundary=----b",
];

/// The request as the model holds it.
#[derive(Clone)]
struct Model {
    method: &'static str,
    body: Option<(&'static str, Vec<u8>)>,
}

/// What a run sent and how it ended.
#[derive(Debug, PartialEq, Eq)]
struct Run {
    requests: Vec<Vec<u8>>,
    end: Option<u16>,
}

fn head_and_body(url: &Url, m: &Model) -> Vec<u8> {
    let host = match (url.host_str(), url.port()) {
        (Some(h), Some(p)) => format!("{h}:{p}"),
        (Some(h), None) => h.to_owned(),
        _ => String::new(),
    };
    let target = match url.query() {
        Some(q) => format!("{}?{q}", url.path()),
        None => url.path().to_owned(),
    };
    let mut out = format!(
        "{} {target} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: */*\r\nUser-Agent: clazel\r\n",
        m.method
    )
    .into_bytes();
    match &m.body {
        Some((ct, bytes)) => {
            out.extend_from_slice(
                format!("Content-Type: {ct}\r\nContent-Length: {}\r\n", bytes.len()).as_bytes(),
            );
        }
        None if m.method == "POST" => out.extend_from_slice(b"Content-Length: 0\r\n"),
        None => {}
    }
    if m.method != "GET" && m.method != "HEAD" {
        // The initiator is none or opaque: `null`.
        out.extend_from_slice(b"Origin: null\r\n");
    }
    out.extend_from_slice(b"\r\n");
    if let Some((_, bytes)) = &m.body {
        out.extend_from_slice(bytes);
    }
    out
}

/// HTTP-redirect fetch step 12.
fn rewrite(status: u16, m: &Model) -> Model {
    let post = m.method == "POST";
    let other = m.method != "GET" && m.method != "HEAD";
    if ((status == 301 || status == 302) && post) || (status == 303 && other) {
        Model {
            method: "GET",
            body: None,
        }
    } else {
        m.clone()
    }
}

struct Case {
    start: &'static str,
    model: Model,
    opaque_initiator: bool,
    hops: Vec<(u16, &'static str)>,
}

fn case(seed: u64) -> Case {
    let mut rng = Rng(seed);
    let start = rng.pick(START_URLS, "");
    let model = match rng.below(4) {
        0 => Model {
            method: "GET",
            body: None,
        },
        1 => Model {
            method: "POST",
            body: None,
        },
        _ => {
            let n = rng.below(40);
            let bytes: Vec<u8> = (0..n)
                .map(|_| match rng.below(6) {
                    0 => b'\r',
                    1 => b'\n',
                    2 => 0,
                    3 => 0x80 | (rng.next() as u8),
                    _ => b'a'.saturating_add(
                        u8::try_from(rng.next().checked_rem(26).unwrap_or(0)).unwrap_or(0),
                    ),
                })
                .collect();
            Model {
                method: "POST",
                body: Some((rng.pick(TYPES, ""), bytes)),
            }
        }
    };
    let n = rng.below(5).saturating_add(1);
    let hops = (0..n)
        .map(|_| (rng.pick(STATUSES, 200), rng.pick(LOCATIONS, "/")))
        .collect();
    Case {
        start,
        model,
        opaque_initiator: rng.below(2) == 0,
        hops,
    }
}

fn response(status: u16, location: &str) -> Vec<u8> {
    let loc = if is_redirect(status) {
        format!("Location: {location}\r\n")
    } else {
        String::new()
    };
    format!("HTTP/1.1 {status} X\r\n{loc}Content-Length: 0\r\n\r\n").into_bytes()
}

fn is_redirect(status: u16) -> bool {
    matches!(status, 301 | 302 | 303 | 307 | 308)
}

fn reference(c: &Case) -> Option<Run> {
    let mut url = Url::parse(c.start).ok()?;
    let mut model = c.model.clone();
    let mut requests = Vec::new();
    for (status, location) in &c.hops {
        requests.push(head_and_body(&url, &model));
        if !is_redirect(*status) {
            return Some(Run {
                requests,
                end: Some(*status),
            });
        }
        let mut next = url.join(location).ok()?;
        if next.fragment().is_none() {
            next.set_fragment(url.fragment());
        }
        model = rewrite(*status, &model);
        url = next;
    }
    // The script ran out while a redirect was pending: not a case.
    None
}

fn ours(c: &Case, now: u64) -> Option<Run> {
    let input: Vec<u32> = c.start.chars().map(u32::from).collect();
    let parsed = basic_url_parser(&input, None)?;
    let req = ReqBuf {
        method: c.model.method.as_bytes().to_vec(),
        body: c.model.body.as_ref().map(|(ct, b)| PayloadBuf {
            content_type: ct.as_bytes().to_vec(),
            bytes: b.clone(),
        }),
        initiator: if c.opaque_initiator {
            Some(clazel_origin::exec::ParsedOrigin::Opaque(7))
        } else {
            None
        },
        origin_tainted: false,
    };
    let mut jar: Vec<CookieRecord> = Vec::new();
    let (mut state, mut actions) = start_req(&parsed, req);
    let mut requests = Vec::new();
    for (status, location) in &c.hops {
        if !matches!(actions.last(), Some(ActionBuf::Connect { .. })) {
            return None;
        }
        let (next, sent, ops) = step_real(state, &InputBuf::Connected, &jar, now);
        jar = apply_ops_exec(jar, &ops);
        let [ActionBuf::Send(request)] = sent.as_slice() else {
            return None;
        };
        requests.push(request.clone());
        let (next, after, ops) = step_real(
            next,
            &InputBuf::Bytes(response(*status, location)),
            &jar,
            now,
        );
        jar = apply_ops_exec(jar, &ops);
        match after.as_slice() {
            [ActionBuf::Close, ActionBuf::Connect { .. }] => {
                state = next;
                actions = after;
            }
            [ActionBuf::Close, ActionBuf::Done { response, .. }] => {
                return Some(Run {
                    requests,
                    end: Some(response.status_line.status),
                });
            }
            _ => return None,
        }
    }
    None
}

#[test]
fn differential_methods_bodies_and_redirects() {
    let runs: u64 = 6000;
    let (mut pass, mut failed, mut resent, mut dropped, mut with_body) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut compared: u64 = 0;
    for i in 0..runs {
        let seed = i.wrapping_mul(0x9E37_79B9).wrapping_add(1);
        let c = case(seed);
        let Some(want) = reference(&c) else {
            continue;
        };
        compared = compared.saturating_add(1);
        if c.model.body.is_some() {
            with_body = with_body.saturating_add(1);
            // Did a later request carry the body again, or lose it?
            if let (true, Some(last)) = (want.requests.len() > 1, want.requests.last()) {
                if last.starts_with(b"POST ") {
                    resent = resent.saturating_add(1);
                } else if last.starts_with(b"GET ") {
                    dropped = dropped.saturating_add(1);
                }
            }
        }
        let got = ours(&c, 13_000_000_000);
        if got.as_ref() == Some(&want) {
            pass = pass.saturating_add(1);
        } else {
            failed = failed.saturating_add(1);
            if failed <= 5 {
                println!("FAIL seed {seed}: from {} {:?}", c.start, c.hops);
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"rust-url differential, POST bodies and redirect rewriting\" pass={pass} xfail=0 fail={failed} total={compared}"
    );
    println!(
        "runs with a body: {with_body}, sent again after a redirect: {resent}, dropped by one: {dropped}"
    );
    assert_eq!(failed, 0);
    assert!(compared > 1000 && with_body > 300 && resent > 20 && dropped > 20);
}

/// A method this client does not send (`PUT`) and a `GET` with a body are
/// not requests: the fetch fails before connecting.
#[test]
fn refused_requests() {
    let input: Vec<u32> = "http://example.test/".chars().map(u32::from).collect();
    let parsed = basic_url_parser(&input, None);
    assert!(parsed.is_some());
    let Some(parsed) = parsed else {
        return;
    };
    for (method, body) in [("PUT", false), ("GET", true)] {
        let req = ReqBuf {
            method: method.as_bytes().to_vec(),
            body: if body {
                Some(PayloadBuf {
                    content_type: b"text/plain".to_vec(),
                    bytes: b"x".to_vec(),
                })
            } else {
                None
            },
            initiator: None,
            origin_tainted: false,
        };
        let (_, actions) = start_req(&parsed, req);
        assert!(matches!(
            actions.as_slice(),
            [ActionBuf::Fail(Reason::NotFetched)]
        ));
    }
}
