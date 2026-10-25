//! Hand-written checks of item 3.7: a navigation is a fetch. The kernel is
//! driven by `step_exec` with the real URL functions and a test fetch (the
//! kernel takes the fetch as a parameter; the shipped one is the stand-in
//! `StubFetch`, which the other tests use through `step_real`). These cite no
//! official suite; the proofs (`exec::step::fetched_exec`) are what say the
//! kernel does these things for every input.

use clazel_cookie::matching::exec::CanonicalHostName;
use clazel_cookie::storage::exec::{HttpRequestRecord, RequestContextRecord, RequestUrlRecord};
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};
use clazel_kernel::exec::fetch::{
    FetchFnsExec, FetchResultRecord, FetchRunRecord, HttpStoreRecord, NetOutcomeRecord,
};
use clazel_kernel::exec::real_urls::RealUrls;
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};
use clazel_kernel::exec::step::step_exec;
use clazel_kernel::exec::urls::UrlFnsExec;

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// What a test fetch gives for the URL it is asked for.
enum Plan {
    /// A response at the URL asked for, with the octets as the body.
    Echo,
    /// The fetch fails.
    Fail,
    /// A redirect: the response is at this URL.
    RedirectTo(&'static str),
    /// A response at this exact string of code points.
    At(Vec<u32>),
    /// The response sets this cookie, as an answer to a request for the host
    /// (an HTTPS request at `/`).
    SetsCookie(&'static str, &'static str),
}

struct TestFetch(Plan);

/// The request URL and HTTP context of an HTTPS request for `host`.
fn request_for(host: &str) -> (RequestUrlRecord, RequestContextRecord) {
    let origin = RealUrls
        .origin_of(&code_points(&format!("https://{host}/")))
        .expect("an origin");
    let other = RealUrls
        .origin_of(&code_points(&format!("https://{host}/")))
        .expect("an origin");
    (
        RequestUrlRecord {
            scheme: b"https".to_vec(),
            host: Some(CanonicalHostName {
                name: host.as_bytes().to_vec(),
                is_ip_address: false,
            }),
            path: b"/".to_vec(),
        },
        RequestContextRecord::Http(HttpRequestRecord {
            url_origin: origin,
            site_for_cookies: Some(other),
            is_reload_navigation: false,
            reloaded_document_was_same_site: false,
            navigates_top_level_traversable: true,
            method_is_safe: true,
            target_is_active_or_top_level: true,
        }),
    )
}

impl FetchFnsExec for TestFetch {
    fn run(&self, url: &[u32], net: &[u8]) -> FetchRunRecord {
        let done = |u: Vec<u32>| FetchResultRecord::Done {
            url: u,
            body: net.to_vec(),
        };
        match &self.0 {
            Plan::Echo => FetchRunRecord {
                result: done(url.to_vec()),
                stores: Vec::new(),
            },
            Plan::Fail => FetchRunRecord {
                result: FetchResultRecord::Failed,
                stores: Vec::new(),
            },
            Plan::RedirectTo(target) => FetchRunRecord {
                result: done(code_points(target)),
                stores: Vec::new(),
            },
            Plan::At(u) => FetchRunRecord {
                result: done(u.clone()),
                stores: Vec::new(),
            },
            Plan::SetsCookie(host, line) => {
                let (u, ctx) = request_for(host);
                FetchRunRecord {
                    result: done(url.to_vec()),
                    stores: vec![HttpStoreRecord {
                        line: line.as_bytes().to_vec(),
                        url: u,
                        ctx,
                    }],
                }
            }
        }
    }
}

/// What the kernel sent, decoded.
#[derive(Debug, PartialEq, Eq)]
enum Out {
    To(u64, Msg),
    Spawn(u64),
    Kill(u64),
    Fetch(u64, Vec<u32>),
}

struct Rig {
    state: Option<StateRecord>,
    fetch: TestFetch,
}

impl Rig {
    fn new(plan: Plan) -> Rig {
        Rig {
            state: Some(init_record()),
            fetch: TestFetch(plan),
        }
    }

    fn event(&mut self, e: &EventRecord) -> Vec<Out> {
        let Some(s) = self.state.take() else {
            return Vec::new();
        };
        let (next, outputs) = step_exec(&RealUrls, &self.fetch, s, e);
        self.state = Some(next);
        outputs
            .into_iter()
            .map(|o| match o {
                OutputRecord::ToRenderer { id, bytes } => {
                    Out::To(id, decode_framed(&bytes).expect("a frame"))
                }
                OutputRecord::Spawn { id } => Out::Spawn(id),
                OutputRecord::Kill { id } => Out::Kill(id),
                OutputRecord::Fetch { tab, url } => Out::Fetch(tab, url),
            })
            .collect()
    }

    fn open(&mut self, url: &str) -> u64 {
        let out = self.event(&EventRecord::OpenTab {
            url: code_points(url),
            script: Vec::new(),
        });
        match out.first() {
            Some(Out::Spawn(id)) => *id,
            other => panic!("OpenTab of {url}: {other:?}"),
        }
    }

    fn send(&mut self, id: u64, m: &Msg) -> Vec<Out> {
        let bytes = encode_framed(m).expect("encodable");
        self.event(&EventRecord::FromRenderer { id, bytes })
    }

    fn navigate(&mut self, tab: u64, url: &str) -> Vec<Out> {
        self.event(&EventRecord::NavigateTab {
            tab,
            url: code_points(url),
        })
    }

    fn fetched(&mut self, tab: u64, url: &str, net: &[u8]) -> Vec<Out> {
        self.event(&EventRecord::Fetched {
            tab,
            outcome: NetOutcomeRecord {
                url: code_points(url),
                net: net.to_vec(),
            },
        })
    }
}

fn commit(url: &str, script: &[u8]) -> Msg {
    Msg::Commit {
        url: url.as_bytes().to_vec(),
        script: script.to_vec(),
    }
}

#[test]
fn a_navigation_only_asks_for_the_fetch_and_the_fetch_commits_the_body() {
    let mut rig = Rig::new(Plan::Echo);
    let id = rig.open("https://example.test/");
    let out = rig.navigate(id, "https://example.test/next");
    assert_eq!(
        out,
        vec![Out::Fetch(id, code_points("https://example.test/next"))]
    );
    // Nothing is committed yet: the renderer is still at its old document.
    let out = rig.fetched(id, "https://example.test/next", b"page body");
    assert_eq!(
        out,
        vec![Out::To(id, commit("https://example.test/next", b"page body"))]
    );
}

#[test]
fn a_fetched_event_is_ignored_unless_it_answers_the_navigation_in_flight() {
    let mut rig = Rig::new(Plan::Echo);
    let id = rig.open("https://example.test/");
    // Unsolicited: the renderer is not navigating.
    assert!(rig.fetched(id, "https://example.test/x", b"").is_empty());
    // A tab that is not open.
    assert!(rig.fetched(99, "https://example.test/x", b"").is_empty());
    // A navigation, then another before the first's answer arrives: the first
    // answer is for a URL the tab no longer navigates to.
    rig.navigate(id, "https://example.test/first");
    rig.navigate(id, "https://example.test/second");
    assert!(rig.fetched(id, "https://example.test/first", b"old").is_empty());
    let out = rig.fetched(id, "https://example.test/second", b"new");
    assert_eq!(
        out,
        vec![Out::To(id, commit("https://example.test/second", b"new"))]
    );
    // The navigation is over: its answer, again, is ignored.
    assert!(rig.fetched(id, "https://example.test/second", b"new").is_empty());
}

#[test]
fn a_fetched_event_for_a_tab_that_closed_is_ignored() {
    let mut rig = Rig::new(Plan::Echo);
    let id = rig.open("https://example.test/");
    rig.navigate(id, "https://example.test/next");
    rig.event(&EventRecord::RendererExited { id });
    assert!(rig.fetched(id, "https://example.test/next", b"x").is_empty());
}

#[test]
fn a_failed_fetch_gives_the_renderer_an_error_and_it_stays() {
    let mut rig = Rig::new(Plan::Fail);
    let id = rig.open("https://example.test/");
    rig.navigate(id, "https://example.test/next");
    let out = rig.fetched(id, "https://example.test/next", b"");
    assert_eq!(out, vec![Out::To(id, Msg::Error { code: 5 })]);
    // The renderer is still the tab's, and still on its old document.
    assert!(rig.fetched(id, "https://example.test/next", b"").is_empty());
    let out = rig.send(id, &Msg::CookieGet);
    assert!(matches!(
        out.as_slice(),
        [Out::To(to, Msg::CookieValue { .. })] if *to == id
    ));
}

#[test]
fn a_redirect_to_another_origin_replaces_the_renderer_with_the_final_url() {
    let mut rig = Rig::new(Plan::RedirectTo("https://other.test/landed"));
    let id = rig.open("https://example.test/");
    rig.navigate(id, "https://example.test/start");
    let out = rig.fetched(id, "https://example.test/start", b"landing page");
    match out.as_slice() {
        [
            Out::Kill(old),
            Out::Spawn(new),
            Out::To(to, Msg::Commit { url, script }),
        ] => {
            assert_eq!(*old, id);
            assert_eq!(new, to);
            assert_ne!(*new, id);
            assert_eq!(url.as_slice(), b"https://other.test/landed");
            assert_eq!(script.as_slice(), b"landing page");
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_final_url_the_kernel_cannot_lock_is_an_error() {
    // Not a string of scalar values (a lone surrogate), and not a URL.
    for bad in [vec![0xD800u32], code_points("not a url"), Vec::new()] {
        let mut rig = Rig::new(Plan::At(bad));
        let id = rig.open("https://example.test/");
        rig.navigate(id, "https://example.test/next");
        let out = rig.fetched(id, "https://example.test/next", b"");
        assert_eq!(out, vec![Out::To(id, Msg::Error { code: 3 })]);
    }
}

fn cookie_string(out: &[Out], id: u64) -> Option<&[u8]> {
    match out {
        [Out::To(to, Msg::CookieValue { cookie_string })] if *to == id => {
            Some(cookie_string.as_slice())
        }
        _ => None,
    }
}

#[test]
fn a_response_sets_a_cookie_through_the_kernel_jar() {
    let mut rig = Rig::new(Plan::SetsCookie("example.test", "from=http"));
    rig.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = rig.open("https://example.test/");
    let other = rig.open("https://other.test/");
    rig.navigate(id, "https://example.test/next");
    // Nothing is stored until the answer arrives.
    assert_eq!(
        cookie_string(&rig.send(id, &Msg::CookieGet), id),
        Some(&b""[..])
    );
    rig.fetched(id, "https://example.test/next", b"");
    assert_eq!(
        cookie_string(&rig.send(id, &Msg::CookieGet), id),
        Some(&b"from=http"[..])
    );
    // Another root's document does not see it.
    assert_eq!(
        cookie_string(&rig.send(other, &Msg::CookieGet), other),
        Some(&b""[..])
    );
}

#[test]
fn a_cookie_for_a_stale_answer_is_not_stored() {
    let mut rig = Rig::new(Plan::SetsCookie("example.test", "from=http"));
    rig.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = rig.open("https://example.test/");
    rig.navigate(id, "https://example.test/first");
    rig.navigate(id, "https://example.test/second");
    assert!(rig.fetched(id, "https://example.test/first", b"").is_empty());
    assert_eq!(
        cookie_string(&rig.send(id, &Msg::CookieGet), id),
        Some(&b""[..])
    );
}

#[test]
fn a_cookie_for_a_public_suffix_host_is_not_stored() {
    // `test` is a public suffix under the list's default rule.
    let mut rig = Rig::new(Plan::SetsCookie("test", "from=http"));
    rig.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = rig.open("https://example.test/");
    rig.navigate(id, "https://example.test/next");
    rig.fetched(id, "https://example.test/next", b"");
    assert_eq!(
        cookie_string(&rig.send(id, &Msg::CookieGet), id),
        Some(&b""[..])
    );
}
