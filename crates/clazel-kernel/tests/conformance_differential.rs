//! Differential test against `cookie_store` (the cookie jar of reqwest's
//! `cookie_store` feature, which follows RFC 6265 and parses with the
//! `cookie` crate), on random multi-renderer traces through the exec kernel
//! (docs/phases/phase-2.md item 2.12).
//!
//! A trace is a few dozen operations on a fresh kernel and a fresh
//! `cookie_store`. The kernel runs several tabs, each with its own renderer
//! (a fake renderer that talks in frames through the IPC codec), on a few
//! hosts and both schemes; the operations are:
//!
//! - the user opens a tab on a URL (the kernel spawns a renderer and sends
//!   it a `Commit` of that URL);
//! - a renderer's `Navigate` to a URL (a different origin gets a new
//!   renderer, the old one is killed; the same origin keeps the renderer);
//!   or the user's `NavigateTab`;
//! - a renderer assigns a cookie string to `document.cookie` (`CookieSet`);
//! - a renderer reads `document.cookie` (`CookieGet`);
//! - a renderer exits (`RendererExited`), which closes its tab.
//!
//! The reference engine gets each assignment as a cookie string received
//! from the URL of the tab's current document, and each read as a request to
//! that URL. After every read, each renderer's `document.cookie` must hold
//! the same cookies as `cookie_store`'s, as a multiset of `name=value`
//! (`cookie_store` does not order them); the kernel's replies must also be
//! the frames the model expects (a `Commit` of the URL after each
//! navigation, a `Spawn` exactly when the origin changes, and no reply to an
//! assignment). The generator stays inside what RFC 6265 and RFC 6265bis
//! agree on and what `cookie_store` implements, as `clazel-cookie`'s own
//! differential test does (separate name pools for host-only, domain,
//! `Secure` and `Secure` domain cookies; the hosts `example.test`,
//! `www.example.test`, `a.www.example.test` and `other.test`, since `test` is
//! a public suffix under the list's default rule and `cookie_store` has no
//! list; no nameless cookies, SameSite, prefixes or control characters), and
//! leaves out `HttpOnly` (`document.cookie` cannot set it, which
//! `cookie_store` does not model) and `Expires` and small `Max-Age` (they
//! depend on the clock, which the two engines read separately).
//!
//! The generator is a fixed-seed linear congruential generator, so a run is
//! reproducible. Prints `clazel-conformance:` with the number of traces
//! whose reads all agree.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-cookie`'s
//! differential test is): `cookie_store` reads the system clock on every
//! parse and read, which Miri's isolation refuses, so the reference cannot
//! run at all; the kernel's own code is run under Miri by the other
//! conformance tests of this crate.

mod support;

use clazel_fetch::transducer::types::InputBuf;
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::EventRecord;
use cookie_store::CookieStore;
use support::{Doc, Kernel, Out, code_points};

/// Answer the network outputs among `out` as a server with an empty page
/// would: `Connected` for a `Connect`, a whole response for a `Send`, nothing
/// for a `Close`. The outputs for renderers, in order, with those that
/// answering gave after them (the document's script is the empty body).
fn settled(kernel: &mut Kernel, out: Vec<Out>) -> Vec<Out> {
    let response = b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    let mut all = Vec::new();
    let mut queue: std::collections::VecDeque<Out> = out.into();
    while let Some(o) = queue.pop_front() {
        let answer = match o {
            Out::Connect(conn, ..) => Some((conn, InputBuf::Connected)),
            Out::Send(conn, _) => Some((conn, InputBuf::Bytes(response.clone()))),
            Out::Close(_) => None,
            other => {
                all.push(other);
                None
            }
        };
        if let Some((conn, input)) = answer {
            queue.extend(kernel.event(&EventRecord::Net { conn, input }));
        }
    }
    all
}
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

const HOSTS: &[&str] = &[
    "example.test",
    "www.example.test",
    "a.www.example.test",
    "other.test",
];
const PATHS: &[&str] = &["/", "/a", "/a/b", "/a/b/c", "/ab"];
const NAMES: &[&str] = &["a", "b", "c", "ab"];
const DOMAIN_NAMES: &[&str] = &["d", "e", "de"];
const SECURE_NAMES: &[&str] = &["s", "t", "st"];
const SECURE_DOMAIN_NAMES: &[&str] = &["u", "v", "uv"];
const VALUES: &[&str] = &["1", "2", "x", "yz", ""];
const ATTR_PATHS: &[&str] = &["/", "/a", "/a/b", "/ab", "a", ""];
const DOMAINS: &[&str] = &[
    "example.test",
    ".example.test",
    "www.example.test",
    "a.www.example.test",
    "other.test",
    "EXAMPLE.test",
];
const MAX_AGES: &[&str] = &["0", "1000000", "-5", "99999999"];

/// A random document URL.
fn url(rng: &mut Rng) -> String {
    let scheme = if rng.below(3) == 0 { "http" } else { "https" };
    format!("{scheme}://{}{}", rng.pick(HOSTS), rng.pick(PATHS))
}

/// A random cookie string for a document whose URL is over `https` (or not).
fn cookie_string(rng: &mut Rng, https: bool) -> String {
    let domain_cookie = rng.below(3) == 0;
    let secure = https && rng.below(3) == 0;
    let names = match (domain_cookie, secure) {
        (false, false) => NAMES,
        (true, false) => DOMAIN_NAMES,
        (false, true) => SECURE_NAMES,
        (true, true) => SECURE_DOMAIN_NAMES,
    };
    let mut s = format!("{}={}", rng.pick(names), rng.pick(VALUES));
    if domain_cookie {
        s.push_str(&format!("; Domain={}", rng.pick(DOMAINS)));
    } else if rng.below(8) == 0 {
        s.push_str("; Domain=");
    }
    if secure {
        s.push_str("; Secure");
    }
    for _ in 0..rng.below(3) {
        if rng.below(2) == 0 {
            s.push_str(&format!("; Path={}", rng.pick(ATTR_PATHS)));
        } else {
            s.push_str(&format!("; Max-Age={}", rng.pick(MAX_AGES)));
        }
    }
    s
}

/// `name=value` pairs of a cookie-string, sorted.
fn pairs(cookie_string: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = cookie_string
        .split("; ")
        .filter(|p| !p.is_empty())
        .map(|p| match p.split_once('=') {
            Some((n, v)) => (n.to_owned(), v.to_owned()),
            None => (String::new(), p.to_owned()),
        })
        .collect();
    out.sort();
    out
}

/// The scheme, host and port of an absolute URL we generated.
fn origin_of(url: &str) -> &str {
    match url.match_indices('/').nth(2) {
        Some((i, _)) => url.get(..i).unwrap_or(url),
        None => url,
    }
}

/// A tab as the model sees it.
struct Tab {
    /// The tab id: the id of the tab's first renderer, which a navigation to
    /// another origin does not change.
    tab: u64,
    /// The tab's renderer now.
    renderer: u64,
    url: String,
}

/// Whether the outputs are exactly a spawn and the commit of `url` to the
/// spawned renderer (and, if `old` is given, the kill of that renderer first).
fn spawn_and_commit(out: &[Out], old: Option<u64>, url: &str) -> Option<u64> {
    match (old, out) {
        (
            None,
            [
                Out::Spawn(new),
                Out::Commit(to, Doc { url: committed, .. }),
            ],
        ) if new == to && committed == url.as_bytes() => Some(*new),
        (
            Some(old),
            [
                Out::Kill(killed),
                Out::Spawn(new),
                Out::Commit(to, Doc { url: committed, .. }),
            ],
        ) if *killed == old && new == to && committed == url.as_bytes() => Some(*new),
        _ => None,
    }
}

/// One trace; a description of the first disagreement, if any.
fn trace(seed: u64, now: u64) -> Option<String> {
    let mut rng = Rng(seed);
    let mut store = CookieStore::default();
    let mut kernel = Kernel::new();
    kernel.event(&EventRecord::Tick { time: now });
    let mut tabs: Vec<Tab> = Vec::new();
    let mut log: Vec<String> = Vec::new();
    for step in 0..24 {
        let fail = |what: &str, log: &[String]| {
            Some(format!("seed {seed} step {step}: {what}; after {log:?}"))
        };
        let choice = if tabs.is_empty() { 0 } else { rng.below(12) };
        match choice {
            // Open a tab.
            0 | 1 => {
                let target = url(&mut rng);
                log.push(format!("open {target}"));
                let (id, out) = kernel.open_tab(&target, "");
                let Some(id) = id else {
                    return fail("OpenTab spawned no renderer", &log);
                };
                if spawn_and_commit(&out, None, &target) != Some(id) {
                    return fail(&format!("OpenTab outputs {out:?}"), &log);
                }
                tabs.push(Tab {
                    tab: id,
                    renderer: id,
                    url: target,
                });
            }
            // Navigate a tab: by the renderer's own message, or by the user.
            2 | 3 => {
                let i = rng.below(tabs.len());
                let target = url(&mut rng);
                let Some(tab) = tabs.get_mut(i) else { continue };
                log.push(format!("navigate {} to {target}", tab.url));
                let same_origin = origin_of(&tab.url) == origin_of(&target);
                let out = if rng.below(2) == 0 {
                    kernel.send(
                        tab.renderer,
                        &Msg::Navigate {
                            url: target.as_bytes().to_vec(),
                        },
                    )
                } else {
                    kernel.event(&EventRecord::NavigateTab {
                        tab: tab.tab,
                        url: code_points(&target),
                    })
                };
                let out = settled(&mut kernel, out);
                // Only `http:` URLs are fetched (TLS is not carried out): a
                // navigation to an `https:` one fails and the renderer stays.
                if target.starts_with("https:") {
                    match out.as_slice() {
                        [Out::To(to, Msg::Error { code: 5 })] if *to == tab.renderer => {
                            continue;
                        }
                        _ => return fail(&format!("https navigation outputs {out:?}"), &log),
                    }
                }
                if same_origin {
                    match out.as_slice() {
                        [Out::Commit(to, Doc { url: committed, .. })]
                            if *to == tab.renderer && committed == target.as_bytes() => {}
                        _ => return fail(&format!("same-origin navigation outputs {out:?}"), &log),
                    }
                } else {
                    match spawn_and_commit(&out, Some(tab.renderer), &target) {
                        Some(new) => tab.renderer = new,
                        None => {
                            return fail(&format!("cross-origin navigation outputs {out:?}"), &log);
                        }
                    }
                }
                tab.url = target;
            }
            // Close a tab.
            4 => {
                let i = rng.below(tabs.len());
                let tab = tabs.remove(i);
                log.push(format!("exit {}", tab.url));
                let out = kernel.event(&EventRecord::RendererExited { id: tab.renderer });
                if !out.is_empty() {
                    return fail(&format!("RendererExited outputs {out:?}"), &log);
                }
            }
            // Assign document.cookie.
            5..=8 => {
                let i = rng.below(tabs.len());
                let Some(tab) = tabs.get(i) else { continue };
                let cookie = cookie_string(&mut rng, tab.url.starts_with("https:"));
                log.push(format!("set {} {cookie:?}", tab.url));
                let Ok(theirs) = Url::parse(&tab.url) else {
                    return fail("reference cannot parse the URL", &log);
                };
                let _ = store.parse(&cookie, &theirs);
                let out = kernel.send(
                    tab.renderer,
                    &Msg::CookieSet {
                        cookie_string: cookie.into_bytes(),
                    },
                );
                if !out.is_empty() {
                    return fail(&format!("CookieSet outputs {out:?}"), &log);
                }
            }
            // Read document.cookie.
            _ => {
                let i = rng.below(tabs.len());
                let Some(tab) = tabs.get(i) else { continue };
                log.push(format!("get {}", tab.url));
                let Ok(theirs) = Url::parse(&tab.url) else {
                    return fail("reference cannot parse the URL", &log);
                };
                let mut want: Vec<(String, String)> = store
                    .get_request_values(&theirs)
                    .map(|(n, v)| (n.to_owned(), v.to_owned()))
                    .collect();
                want.sort();
                let out = kernel.send(tab.renderer, &Msg::CookieGet);
                let got = match out.as_slice() {
                    [Out::To(to, Msg::CookieValue { cookie_string })] if *to == tab.renderer => {
                        pairs(&String::from_utf8_lossy(cookie_string))
                    }
                    _ => return fail(&format!("CookieGet outputs {out:?}"), &log),
                };
                if got != want {
                    return fail(
                        &format!("get {}: ours {got:?}, cookie_store {want:?}", tab.url),
                        &log,
                    );
                }
            }
        }
    }
    None
}

#[test]
#[cfg_attr(miri, ignore)]
fn differential_cookie_store() {
    let traces: u64 = 3000;
    let now_unix = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(1_792_713_600, |d| d.as_secs());
    // Seconds from 1601-01-01T00:00:00Z to 1970-01-01T00:00:00Z.
    let now = now_unix.saturating_add(11_644_473_600);
    let mut pass: u64 = 0;
    let mut failed: u64 = 0;
    for i in 0..traces {
        match trace(i.wrapping_mul(0x9E37_79B9).wrapping_add(1), now) {
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
        "clazel-conformance: suite=\"cookie_store differential, random multi-renderer document.cookie traces\" pass={pass} xfail=0 fail={failed} total={traces}"
    );
    assert_eq!(failed, 0);
}
