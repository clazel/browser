//! Differential test of whole fetches, redirects and cookies together,
//! against two independent engines: the `url` crate (rust-url, the WHATWG
//! URL parser of Servo) for resolving `Location` against the request URL,
//! and `cookie_store` (the jar of reqwest's `cookie_store` feature, which
//! follows RFC 6265) for the `Set-Cookie` lines stored and the `Cookie`
//! field sent at every hop. The redirect logic around them (which statuses
//! redirect, one `Location` value, HTTP(S) schemes only, at most 20
//! redirects) is the reference loop below, written from Fetch §4.5.
//!
//! A run is a random server script (the response each connection gets, in
//! order: a status, `Set-Cookie` lines, `Location` values) and a start URL.
//! The reference runs it with the two crates; the client runs it through
//! the proven transducer (`step_real`: the real HTTP parser, the real URL
//! parser, the real cookie jar) in memory. The two must send the same
//! requests (target, `Host`, and the `Cookie` field as a multiset of
//! `name=value`, which `cookie_store` does not order) and end the same way
//! (the final status, or a failure). The generator stays inside what RFC
//! 6265 and RFC 6265bis agree on and `cookie_store` implements, as
//! `clazel-cookie`'s differential test does: no `Secure` (the client has no
//! TLS yet, and step 13 ignores it on `http`), no `SameSite`, names from
//! separate pools for host-only and domain cookies, `Max-Age` of 0, a large
//! number or a negative one (the engines read the clock separately).
//!
//! The generator is a fixed-seed linear congruential generator. Prints
//! `clazel-conformance:` with the number of runs that agree. Skipped under
//! Miri: `cookie_store` reads the system clock.

use clazel_cookie::storage::exec::CookieRecord;
use clazel_fetch::transducer::real::step_real;
use clazel_fetch::transducer::step::{apply_ops_exec, start};
use clazel_fetch::transducer::types::{ActionBuf, InputBuf};
use clazel_url::url::parse::basic_url_parser;
use cookie_store::CookieStore;
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

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items.get(self.below(items.len())).copied().unwrap_or("")
    }
}

const START_URLS: &[&str] = &[
    "http://example.test/",
    "http://example.test/a",
    "http://www.example.test/a/b?x=1",
    "http://a.www.example.test:8080/a/b/c",
    "http://other.test/ab#frag",
    "http://example.test:81/a?q",
];
const NAMES: &[&str] = &["a", "b", "c", "ab"];
const DOMAIN_NAMES: &[&str] = &["d", "e", "de"];
const VALUES: &[&str] = &["1", "2", "x", "yz", ""];
const ATTR_PATHS: &[&str] = &["/", "/a", "/a/b", "/ab", "a", ""];
const DOMAINS: &[&str] = &[
    "example.test",
    ".example.test",
    "www.example.test",
    "a.www.example.test",
    "other.test",
];
const MAX_AGES: &[&str] = &["0", "1000000", "-5", "99999999"];

/// `Location` values: relative references of every kind, absolute URLs on
/// other hosts, ports and schemes, a fragment, and the empty value.
const LOCATIONS: &[&str] = &[
    "/",
    "/a",
    "/a/b",
    "b",
    "../c",
    "./d/e",
    "?q=1",
    "#f",
    "",
    "//other.test/x",
    "//www.example.test:8080/y",
    "http://www.example.test/a",
    "http://other.test:8080/z?y#frag",
    "http://a.www.example.test/a/b",
    "mailto:x",
    "ftp://example.test/",
];

/// Statuses: the five redirect statuses, 304 (which is not one), and some
/// that are not.
const STATUSES: &[u16] = &[
    301, 302, 303, 307, 308, 301, 302, 302, 302, 307, 304, 200, 204, 404,
];

/// One connection's response.
struct Hop {
    status: u16,
    set_cookies: Vec<String>,
    locations: Vec<&'static str>,
}

/// A random Set-Cookie string for a request over `http`.
fn set_cookie_string(rng: &mut Rng) -> String {
    let domain_cookie = rng.below(3) == 0;
    let names = if domain_cookie { DOMAIN_NAMES } else { NAMES };
    let mut s = format!("{}={}", rng.pick(names), rng.pick(VALUES));
    if domain_cookie {
        s.push_str(&format!("; Domain={}", rng.pick(DOMAINS)));
    }
    for _ in 0..rng.below(4) {
        match rng.below(3) {
            0 => s.push_str(&format!("; Path={}", rng.pick(ATTR_PATHS))),
            1 => s.push_str("; HttpOnly"),
            _ => s.push_str(&format!("; Max-Age={}", rng.pick(MAX_AGES))),
        }
    }
    s
}

/// A server script: the response to each of up to 25 connections. Most
/// scripts redirect for a few hops; some redirect forever, to reach the
/// limit of 20.
fn script(rng: &mut Rng) -> Vec<Hop> {
    let forever = rng.below(12) == 0;
    let mut hops = Vec::new();
    for _ in 0..25 {
        let status = if forever {
            *STATUSES.get(rng.below(5)).unwrap_or(&302)
        } else {
            *STATUSES.get(rng.below(STATUSES.len())).unwrap_or(&302)
        };
        let mut set_cookies = Vec::new();
        for _ in 0..rng.below(3) {
            set_cookies.push(set_cookie_string(rng));
        }
        let mut locations = Vec::new();
        let location = if forever {
            // A same-site target that parses: the loop stays in the chain.
            "/a"
        } else {
            rng.pick(LOCATIONS)
        };
        match rng.below(20) {
            0 => {}
            1 => {
                locations.push(location);
                locations.push("/dup");
            }
            _ => locations.push(location),
        }
        hops.push(Hop {
            status,
            set_cookies,
            locations,
        });
    }
    hops
}

/// The bytes the server writes for `hop`.
fn response(hop: &Hop) -> Vec<u8> {
    let mut out = format!("HTTP/1.1 {} X\r\n", hop.status).into_bytes();
    for line in &hop.set_cookies {
        out.extend_from_slice(format!("Set-Cookie: {line}\r\n").as_bytes());
    }
    for location in &hop.locations {
        out.extend_from_slice(format!("Location: {location}\r\n").as_bytes());
    }
    if hop.status != 204 && hop.status != 304 {
        out.extend_from_slice(b"Content-Length: 0\r\n");
    }
    out.extend_from_slice(b"\r\n");
    out
}

/// What a run sent and how it ended.
#[derive(Debug, PartialEq, Eq)]
struct Run {
    /// per request: target, `Host`, the cookies sorted
    requests: Vec<(String, String, Vec<String>)>,
    /// the final status, or `None` for a failed fetch
    end: Option<u16>,
}

/// `name=value` pairs of a cookie-string, sorted.
fn sorted_pairs(cookie: &str) -> Vec<String> {
    let mut out: Vec<String> = cookie
        .split("; ")
        .filter(|p| !p.is_empty())
        .map(str::to_owned)
        .collect();
    out.sort();
    out
}

/// Fetch §2.2.3 "redirect status".
fn is_redirect(status: u16) -> bool {
    matches!(status, 301 | 302 | 303 | 307 | 308)
}

/// The reference: Fetch §4.5 around `url` and `cookie_store`.
fn reference(start_url: &str, hops: &[Hop]) -> Option<Run> {
    let mut store = CookieStore::default();
    let mut url = Url::parse(start_url).ok()?;
    let mut requests = Vec::new();
    let mut redirects: u32 = 0;
    let mut index: usize = 0;
    loop {
        let hop = hops.get(index)?;
        index = index.saturating_add(1);
        let host = match (url.host_str(), url.port()) {
            (Some(h), Some(p)) => format!("{h}:{p}"),
            (Some(h), None) => h.to_owned(),
            _ => return None,
        };
        let target = match url.query() {
            Some(q) => format!("{}?{q}", url.path()),
            None => url.path().to_owned(),
        };
        let mut cookies: Vec<String> = store
            .get_request_values(&url)
            .map(|(n, v)| format!("{n}={v}"))
            .collect();
        cookies.sort();
        requests.push((target, host, cookies));
        for line in &hop.set_cookies {
            let _ = store.parse(line, &url);
        }
        if !is_redirect(hop.status) {
            return Some(Run {
                requests,
                end: Some(hop.status),
            });
        }
        // Fetch §2.2.6 location URL: none is null (the response is
        // returned), several are failure.
        let location = match hop.locations.as_slice() {
            [] => {
                return Some(Run {
                    requests,
                    end: Some(hop.status),
                });
            }
            [one] => *one,
            _ => {
                return Some(Run {
                    requests,
                    end: None,
                });
            }
        };
        let Ok(mut next) = url.join(location) else {
            return Some(Run {
                requests,
                end: None,
            });
        };
        if next.fragment().is_none() {
            next.set_fragment(url.fragment());
        }
        if next.scheme() != "http" && next.scheme() != "https" {
            return Some(Run {
                requests,
                end: None,
            });
        }
        if redirects == 20 {
            return Some(Run {
                requests,
                end: None,
            });
        }
        redirects = redirects.saturating_add(1);
        url = next;
    }
}

/// The request line target, the `Host` and the `Cookie` of a request.
fn parse_request(bytes: &[u8]) -> Option<(String, String, Vec<String>)> {
    let text = String::from_utf8_lossy(bytes);
    let mut lines = text.split("\r\n");
    let target = lines
        .next()?
        .strip_prefix("GET ")?
        .strip_suffix(" HTTP/1.1")?
        .to_owned();
    let mut host = String::new();
    let mut cookie = String::new();
    for line in lines {
        if let Some(v) = line.strip_prefix("Host: ") {
            host = v.to_owned();
        }
        if let Some(v) = line.strip_prefix("Cookie: ") {
            cookie = v.to_owned();
        }
    }
    Some((target, host, sorted_pairs(&cookie)))
}

/// Ours: the same script through the transducer.
fn ours(start_url: &str, hops: &[Hop], now: u64) -> Option<Run> {
    let input: Vec<u32> = start_url.chars().map(u32::from).collect();
    let parsed = basic_url_parser(&input, None)?;
    let mut jar: Vec<CookieRecord> = Vec::new();
    let (mut state, actions) = start(&parsed);
    let mut requests = Vec::new();
    let mut actions = actions;
    for hop in hops {
        if !matches!(actions.last(), Some(ActionBuf::Connect { .. })) {
            return None;
        }
        let (next, sent, ops) = step_real(state, &InputBuf::Connected, &jar, now);
        jar = apply_ops_exec(jar, &ops);
        let [ActionBuf::Send(request)] = sent.as_slice() else {
            return None;
        };
        requests.push(parse_request(request)?);
        let (next, after, ops) = step_real(next, &InputBuf::Bytes(response(hop)), &jar, now);
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
            [ActionBuf::Close, ActionBuf::Fail(_)] => {
                return Some(Run {
                    requests,
                    end: None,
                });
            }
            _ => return None,
        }
    }
    None
}

/// The start URL and the server script of a run.
fn case(seed: u64) -> (&'static str, Vec<Hop>) {
    let mut rng = Rng(seed);
    let start_url = rng.pick(START_URLS);
    (start_url, script(&mut rng))
}

/// One run; a description of the disagreement, if any.
fn one(seed: u64, now: u64) -> Option<String> {
    let (start_url, hops) = case(seed);
    let want = reference(start_url, &hops);
    let got = ours(start_url, &hops, now);
    if want == got {
        None
    } else {
        let summary: Vec<String> = hops
            .iter()
            .take(want.as_ref().map_or(3, |r| r.requests.len()).max(3))
            .map(|h| format!("{} {:?} {:?}", h.status, h.locations, h.set_cookies))
            .collect();
        Some(format!(
            "seed {seed} from {start_url}: ours {got:?}, reference {want:?}; script {summary:?}"
        ))
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn differential_redirects_and_cookies() {
    let runs: u64 = 1500;
    let now_unix = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(1_792_713_600, |d| d.as_secs());
    // Seconds from 1601-01-01 to 1970-01-01.
    let now = now_unix.saturating_add(11_644_473_600);
    let mut pass: u64 = 0;
    let mut failed: u64 = 0;
    // What the runs cover, so that agreement means something.
    let mut with_cookies: u64 = 0;
    let mut at_limit: u64 = 0;
    let mut followed: u64 = 0;
    for i in 0..runs {
        let seed = i.wrapping_mul(0x9E37_79B9).wrapping_add(1);
        let (start_url, hops) = case(seed);
        if let Some(run) = reference(start_url, &hops) {
            if run
                .requests
                .iter()
                .any(|(_, _, cookies)| !cookies.is_empty())
            {
                with_cookies = with_cookies.saturating_add(1);
            }
            if run.requests.len() == 21 && run.end.is_none() {
                at_limit = at_limit.saturating_add(1);
            }
            if run.requests.len() > 1 {
                followed = followed.saturating_add(1);
            }
        }
        match one(seed, now) {
            None => pass = pass.saturating_add(1),
            Some(why) => {
                failed = failed.saturating_add(1);
                if failed <= 10 {
                    println!("FAIL {why}");
                }
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"url and cookie_store differential, random redirect chains\" pass={pass} xfail=0 fail={failed} total={runs}"
    );
    println!(
        "runs with a redirect followed: {followed}, a cookie sent: {with_cookies}, the limit reached: {at_limit}"
    );
    assert_eq!(failed, 0);
    assert!(followed > 500 && with_cookies > 100 && at_limit > 10);
}
