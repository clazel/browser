//! Hand-written checks of item 3.7: a navigation is a fetch the kernel steps
//! itself. The kernel is driven by `step_real`, with the network played by the
//! test: it answers `Connect` with `Connected`, a `Send` with a response, and
//! reports closes and errors. These cite no official suite; the proofs
//! (`exec::step::{begin_navigation_exec, net_exec, carry_out_exec}`) are what
//! say the kernel does these things for every input.

mod support;

use clazel_fetch::transducer::types::InputBuf;
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::EventRecord;
use support::{Kernel, Out, code_points};

/// An HTTP response with `body`, as a server that closes after it would send.
fn response(body: &[u8]) -> Vec<u8> {
    response_with("X-Test: 1", body)
}

/// The document a fetch of `url` commits: kind 0, the responses here carry
/// no `Content-Type`, and `body`.
fn commit(url: &str, body: &[u8]) -> support::Doc {
    support::Doc {
        url: url.as_bytes().to_vec(),
        content_type: Vec::new(),
        kind: 0,
        body: body.to_vec(),
    }
}

impl Kernel {
    fn navigate(&mut self, tab: u64, url: &str) -> Vec<Out> {
        self.event(&EventRecord::NavigateTab {
            tab,
            url: code_points(url),
        })
    }

    fn net(&mut self, conn: u64, input: InputBuf) -> Vec<Out> {
        self.event(&EventRecord::Net { conn, input })
    }

    fn jar_len(&self) -> usize {
        self.state.as_ref().map_or(0, |s| s.jar.len())
    }
}

/// A response with an extra header line.
fn response_with(header: &str, body: &[u8]) -> Vec<u8> {
    let mut r = format!(
        "HTTP/1.1 200 OK\r\n{header}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    )
    .into_bytes();
    r.extend_from_slice(body);
    r
}

fn connect(conn: u64, host: &str) -> Out {
    Out::Connect(conn, host.as_bytes().to_vec(), 80, false)
}

fn cookie_string(out: &[Out], id: u64) -> Option<&[u8]> {
    match out {
        [Out::To(to, Msg::CookieValue { cookie_string })] if *to == id => {
            Some(cookie_string.as_slice())
        }
        _ => None,
    }
}

fn open(k: &mut Kernel, url: &str) -> u64 {
    let (id, _) = k.open_tab(url, "");
    assert!(id.is_some(), "{url} spawned no renderer");
    id.unwrap_or(0)
}

#[test]
fn a_navigation_opens_a_connection_and_the_response_commits_its_body() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    let out = k.navigate(id, "http://example.test/next");
    assert_eq!(out, vec![connect(0, "example.test")]);
    // Nothing is committed yet: the renderer is still at its old document.
    let out = k.net(0, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::Send(0, req)] if req.starts_with(b"GET /next HTTP/1.1\r\n")
    );
    assert!(ok, "{out:?}");
    let out = k.net(0, InputBuf::Bytes(response(b"page body")));
    assert_eq!(
        out,
        vec![
            Out::Close(0),
            Out::Commit(id, commit("http://example.test/next", b"page body"))
        ]
    );
}

#[test]
fn a_net_event_is_ignored_unless_it_names_an_open_connection_of_a_navigating_tab() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    // No connection at all.
    assert!(k.net(0, InputBuf::Connected).is_empty());
    assert!(k.net(99, InputBuf::Bytes(response(b"x"))).is_empty());
    // A navigation, then another before the first's answer arrives: the
    // first connection is closed, and its answer is for a connection that no
    // longer exists.
    assert_eq!(
        k.navigate(id, "http://example.test/first"),
        vec![connect(0, "example.test")]
    );
    assert_eq!(
        k.navigate(id, "http://example.test/second"),
        vec![Out::Close(0), connect(1, "example.test")]
    );
    assert!(k.net(0, InputBuf::Bytes(response(b"old"))).is_empty());
    k.net(1, InputBuf::Connected);
    let out = k.net(1, InputBuf::Bytes(response(b"new")));
    assert_eq!(
        out,
        vec![
            Out::Close(1),
            Out::Commit(id, commit("http://example.test/second", b"new"))
        ]
    );
    // The navigation is over: its connection is gone, and its answer, again,
    // is ignored.
    assert!(k.net(1, InputBuf::Bytes(response(b"new"))).is_empty());
}

#[test]
fn a_tab_that_closed_takes_its_connections_with_it() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    k.navigate(id, "http://example.test/next");
    let out = k.event(&EventRecord::RendererExited { id });
    assert_eq!(out, vec![Out::Close(0)]);
    assert!(k.net(0, InputBuf::Connected).is_empty());
    assert!(k.net(0, InputBuf::Bytes(response(b"x"))).is_empty());
}

#[test]
fn a_renderer_that_is_killed_takes_its_connections_with_it() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    k.navigate(id, "http://example.test/next");
    let out = k.event(&EventRecord::FromRenderer {
        id,
        bytes: vec![0xFF, 0xFF, 0xFF],
    });
    assert_eq!(out, vec![Out::Kill(id), Out::Close(0)]);
}

#[test]
fn a_failed_connection_gives_the_renderer_an_error_and_it_stays() {
    for failure in [InputBuf::Error, InputBuf::Closed] {
        let mut k = Kernel::new();
        let id = open(&mut k, "http://example.test/");
        k.navigate(id, "http://example.test/next");
        let out = k.net(0, failure);
        assert_eq!(out, vec![Out::To(id, Msg::Error { code: 5 })]);
        // The connection is gone with the navigation.
        assert!(k.net(0, InputBuf::Connected).is_empty());
        // The renderer is still the tab's, and still on its old document.
        let out = k.send(id, &Msg::CookieGet);
        assert!(matches!(
            out.as_slice(),
            [Out::To(to, Msg::CookieValue { .. })] if *to == id
        ));
    }
}

#[test]
fn a_url_the_transducer_does_not_fetch_fails_at_once() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    // Userinfo is not fetched (`clazel-fetch`): no connection is opened.
    let out = k.navigate(id, "http://user:pw@example.test/");
    assert_eq!(out, vec![Out::To(id, Msg::Error { code: 5 })]);
}

#[test]
fn a_redirect_to_another_origin_replaces_the_renderer_with_the_final_url() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    k.navigate(id, "http://example.test/start");
    k.net(0, InputBuf::Connected);
    let redirect = b"HTTP/1.1 302 Found\r\nLocation: http://other.test/landed\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    // The first connection is closed and the next request needs its own.
    let out = k.net(0, InputBuf::Bytes(redirect));
    assert_eq!(out, vec![Out::Close(0), connect(1, "other.test")]);
    k.net(1, InputBuf::Connected);
    let out = k.net(1, InputBuf::Bytes(response(b"landing page")));
    let ok = matches!(
        out.as_slice(),
        [
            Out::Close(1),
            Out::Kill(old),
            Out::SpawnGpu(gpu),
            Out::Spawn(new),
            Out::Commit(to, support::Doc { url, body, kind: 0, .. }),
        ] if *old == id
            && gpu == new
            && new == to
            && *new != id
            && url.as_slice() == b"http://other.test/landed"
            && body.as_slice() == b"landing page"
    );
    assert!(ok, "{out:?}");
}

#[test]
fn a_response_sets_a_cookie_through_the_kernel_jar() {
    let mut k = Kernel::new();
    k.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = open(&mut k, "http://example.test/");
    let other = open(&mut k, "http://other.test/");
    k.navigate(id, "http://example.test/next");
    // Nothing is stored until the answer arrives.
    assert_eq!(
        cookie_string(&k.send(id, &Msg::CookieGet), id),
        Some(&b""[..])
    );
    k.net(0, InputBuf::Connected);
    k.net(
        0,
        InputBuf::Bytes(response_with("Set-Cookie: from=http", b"")),
    );
    assert_eq!(
        cookie_string(&k.send(id, &Msg::CookieGet), id),
        Some(&b"from=http"[..])
    );
    // Another root's document does not see it.
    assert_eq!(
        cookie_string(&k.send(other, &Msg::CookieGet), other),
        Some(&b""[..])
    );
}

#[test]
fn a_cookie_for_a_public_suffix_host_is_not_stored() {
    // `test` is a public suffix under the list's default rule.
    let mut k = Kernel::new();
    k.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = open(&mut k, "http://example.test/");
    assert_eq!(k.navigate(id, "http://test/"), vec![connect(0, "test")]);
    k.net(0, InputBuf::Connected);
    k.net(
        0,
        InputBuf::Bytes(response_with("Set-Cookie: from=http", b"")),
    );
    assert_eq!(k.jar_len(), 0);
}

#[test]
fn the_request_carries_the_cookies_of_the_jar_for_its_url() {
    let mut k = Kernel::new();
    k.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = open(&mut k, "http://example.test/");
    k.send(
        id,
        &Msg::CookieSet {
            cookie_string: b"a=b".to_vec(),
        },
    );
    k.navigate(id, "http://example.test/next");
    let out = k.net(0, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::Send(0, req)] if req.windows(11).any(|w| w == b"Cookie: a=b")
    );
    assert!(ok, "{out:?}");
    // Another site's request does not carry it.
    let other = open(&mut k, "http://other.test/");
    k.navigate(other, "http://other.test/next");
    let out = k.net(1, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::Send(1, req)] if !req.windows(6).any(|w| w == b"Cookie")
    );
    assert!(ok, "{out:?}");
}

#[test]
fn each_connection_belongs_to_the_tab_that_opened_it() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://a.test/");
    let b = open(&mut k, "http://b.test/");
    assert_eq!(k.navigate(a, "http://a.test/x"), vec![connect(0, "a.test")]);
    assert_eq!(k.navigate(b, "http://b.test/y"), vec![connect(1, "b.test")]);
    k.net(0, InputBuf::Connected);
    k.net(1, InputBuf::Connected);
    // B's answer commits in B and leaves A's connection alone.
    let out = k.net(1, InputBuf::Bytes(response(b"for b")));
    assert_eq!(
        out,
        vec![
            Out::Close(1),
            Out::Commit(b, commit("http://b.test/y", b"for b"))
        ]
    );
    let out = k.net(0, InputBuf::Bytes(response(b"for a")));
    assert_eq!(
        out,
        vec![
            Out::Close(0),
            Out::Commit(a, commit("http://a.test/x", b"for a"))
        ]
    );
}

// ---------------------------------------------------------------------
// Phase 4 item 4.12: a new tab fetches, a document's body arrives in
// `Body` frames with its content type, and a `Display` is shown under the
// kernel's URL.
// ---------------------------------------------------------------------

/// The user opens a tab at `url` without a script: the outputs.
fn open_fetching(k: &mut Kernel, url: &str) -> Vec<Out> {
    k.event(&EventRecord::OpenTab {
        url: code_points(url),
        script: None,
    })
}

#[test]
fn a_tab_opened_without_a_script_fetches_and_commits_the_document() {
    let mut k = Kernel::new();
    let out = open_fetching(&mut k, "http://example.test/page");
    assert_eq!(
        out,
        vec![Out::SpawnGpu(0), Out::Spawn(0), connect(0, "example.test")]
    );
    k.net(0, InputBuf::Connected);
    let body = b"<!DOCTYPE html><title>T</title><p>Hi".to_vec();
    let out = k.net(
        0,
        InputBuf::Bytes(response_with(
            "Content-Type: text/html; charset=utf-8",
            &body,
        )),
    );
    assert_eq!(
        out,
        vec![
            Out::Close(0),
            Out::Commit(
                0,
                support::Doc {
                    url: b"http://example.test/page".to_vec(),
                    content_type: b"text/html; charset=utf-8".to_vec(),
                    kind: 0,
                    body,
                }
            )
        ]
    );
}

#[test]
fn an_uncommitted_renderer_that_displays_is_killed() {
    let mut k = Kernel::new();
    open_fetching(&mut k, "http://example.test/");
    let display = Msg::Display {
        title: b"Bank".to_vec(),
        text: Vec::new(),
        links: Vec::new(),
    };
    let out = k.send(0, &display);
    assert_eq!(out, vec![Out::Kill(0), Out::Close(0)]);
}

#[test]
fn a_display_is_shown_for_the_senders_tab_under_the_kernels_url() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/a");
    // The title claims another address; the address line is the kernel's.
    let out = k.send(
        id,
        &Msg::Display {
            title: b"https://bank.test/".to_vec(),
            text: b"text".to_vec(),
            links: vec![b"http://example.test/b".to_vec()],
        },
    );
    assert_eq!(
        out,
        vec![Out::Show(
            id,
            code_points("http://example.test/a"),
            b"https://bank.test/".to_vec(),
            b"text".to_vec(),
            vec![b"http://example.test/b".to_vec()],
        )]
    );
}

#[test]
fn a_large_body_is_split_into_body_frames_and_read_back_whole() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    k.navigate(id, "http://example.test/big");
    k.net(0, InputBuf::Connected);
    // Three pieces: two of MAX_BODY_CHUNK octets and a short one. Under
    // Miri only the short one: the 2 MiB body took 1,054 s there (about
    // 500 s per MiB), and a body over one chunk cannot fit in a minute, so
    // Miri sees the framing of a single Body frame and the split itself is
    // checked by the normal test job.
    let chunk = clazel_ipc::message::codec::MAX_BODY_CHUNK;
    let full_chunks = if cfg!(miri) { 0 } else { 2 };
    let body: Vec<u8> = (0..full_chunks * chunk + 17)
        .map(|i| (i % 251) as u8)
        .collect();
    let mut raw = Vec::new();
    // The raw write, to count the frames in it.
    if let Some(s) = k.state.take() {
        let (next, outputs) = clazel_kernel::exec::real_urls::step_real(
            s,
            &EventRecord::Net {
                conn: 0,
                input: InputBuf::Bytes(response_with("X-Test: 1", &body)),
            },
        );
        k.state = Some(next);
        for o in &outputs {
            if let clazel_kernel::exec::records::OutputRecord::ToRenderer { bytes, .. } = o {
                raw = bytes.clone();
            }
        }
    }
    let out = support::split_frames(&raw);
    let msgs = out.unwrap_or_default();
    if cfg!(miri) {
        assert_eq!(msgs.len(), 3, "Commit, one Body frame, BodyEnd");
        assert!(matches!(msgs.get(1), Some(Msg::Body { bytes }) if bytes.len() == 17));
    } else {
        assert_eq!(msgs.len(), 5, "Commit, three Body frames, BodyEnd");
        assert!(matches!(msgs.get(1), Some(Msg::Body { bytes }) if bytes.len() == chunk));
        assert!(matches!(msgs.get(3), Some(Msg::Body { bytes }) if bytes.len() == 17));
    }
    let doc = support::read_doc(msgs);
    assert_eq!(doc.map(|d| d.body), Some(body));
}

// ---------------------------------------------------------------------
// Item 5.19: style sheet fetches.
// ---------------------------------------------------------------------

impl Kernel {
    fn sub_net(&mut self, renderer: u64, serial: u64, hop: u64, input: InputBuf) -> Vec<Out> {
        self.event(&EventRecord::SubNet {
            renderer,
            serial,
            hop,
            input,
        })
    }

    fn fetch_style(&mut self, id: u64, request: u64, url: &str) -> Vec<Out> {
        self.send(
            id,
            &Msg::FetchStyle {
                request,
                url: url.as_bytes().to_vec(),
            },
        )
    }
}

fn sub_connect(id: u64, serial: u64, hop: u64, host: &str) -> Out {
    Out::SubConnect(id, serial, hop, host.as_bytes().to_vec(), 80, false)
}

fn has(req: &[u8], what: &[u8]) -> bool {
    req.windows(what.len()).any(|w| w == what)
}

/// A tab at `http://example.test/page` whose document has the cookie `a=b`.
fn page_with_cookie(k: &mut Kernel) -> u64 {
    k.event(&EventRecord::Tick {
        time: 13_000_000_000,
    });
    let id = open(k, "http://example.test/page");
    k.send(
        id,
        &Msg::CookieSet {
            cookie_string: b"a=b".to_vec(),
        },
    );
    id
}

#[test]
fn a_same_origin_style_sheet_is_fetched_with_the_documents_cookies() {
    let mut k = Kernel::new();
    let id = page_with_cookie(&mut k);
    let out = k.fetch_style(id, 7, "/s.css");
    assert_eq!(out, vec![sub_connect(id, 0, 1, "example.test")]);
    let out = k.sub_net(id, 0, 1, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::SubSend(r, 0, 1, req)]
            if *r == id && req.starts_with(b"GET /s.css HTTP/1.1\r\n") && has(req, b"Cookie: a=b")
    );
    assert!(ok, "{out:?}");
    let out = k.sub_net(
        id,
        0,
        1,
        InputBuf::Bytes(response_with("Set-Cookie: c=d", b"p{}")),
    );
    assert_eq!(
        out,
        vec![
            Out::SubClose(id, 0, 1),
            Out::Frames(
                id,
                vec![
                    Msg::StyleResponse {
                        request: 7,
                        content_type: Vec::new()
                    },
                    Msg::StyleBody {
                        request: 7,
                        bytes: b"p{}".to_vec()
                    },
                    Msg::StyleEnd { request: 7 },
                ]
            )
        ]
    );
    // A credentialed response stores its cookies.
    assert_eq!(
        cookie_string(&k.send(id, &Msg::CookieGet), id),
        Some(&b"a=b; c=d"[..])
    );
    // The fetch is over: a late event about it is ignored.
    assert_eq!(k.sub_net(id, 0, 1, InputBuf::Closed), vec![]);
}

#[test]
fn a_cross_origin_style_sheet_carries_no_cookies_and_stores_none() {
    let mut k = Kernel::new();
    let id = page_with_cookie(&mut k);
    let out = k.fetch_style(id, 1, "http://other.test/s.css");
    assert_eq!(out, vec![sub_connect(id, 0, 1, "other.test")]);
    let out = k.sub_net(id, 0, 1, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::SubSend(_, 0, 1, req)] if req.starts_with(b"GET /s.css") && !has(req, b"Cookie")
    );
    assert!(ok, "{out:?}");
    k.sub_net(
        id,
        0,
        1,
        InputBuf::Bytes(response_with("Set-Cookie: x=y", b"")),
    );
    assert_eq!(k.jar_len(), 1);
}

#[test]
fn each_redirect_hop_decides_credentials_and_gets_its_own_connection() {
    let mut k = Kernel::new();
    let id = page_with_cookie(&mut k);
    k.fetch_style(id, 1, "/s.css");
    k.sub_net(id, 0, 1, InputBuf::Connected);
    let redirect = b"HTTP/1.1 302 Found\r\nLocation: http://other.test/t.css\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    let out = k.sub_net(id, 0, 1, InputBuf::Bytes(redirect));
    assert_eq!(
        out,
        vec![Out::SubClose(id, 0, 1), sub_connect(id, 0, 2, "other.test")]
    );
    // The old hop is gone.
    assert_eq!(k.sub_net(id, 0, 1, InputBuf::Connected), vec![]);
    // The second hop is cross-origin: no cookies.
    let out = k.sub_net(id, 0, 2, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::SubSend(_, 0, 2, req)] if req.starts_with(b"GET /t.css") && !has(req, b"Cookie")
    );
    assert!(ok, "{out:?}");
}

#[test]
fn a_renderer_has_at_most_eight_sub_fetches_at_once() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    for n in 0..8u64 {
        assert_eq!(
            k.fetch_style(id, n, "/s.css"),
            vec![sub_connect(id, n, 1, "example.test")]
        );
    }
    assert_eq!(
        k.fetch_style(id, 8, "/s.css"),
        vec![Out::To(id, Msg::StyleFailed { request: 8 })]
    );
    // Another renderer's limit is its own.
    let other = open(&mut k, "http://other.test/");
    assert_eq!(
        k.fetch_style(other, 0, "/s.css"),
        vec![sub_connect(other, 0, 1, "other.test")]
    );
}

#[test]
fn a_document_starts_at_most_sixty_four_sub_fetches_and_a_commit_starts_a_new_count() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    // A URL the transducer does not fetch fails at once, and counts.
    for n in 0..64u64 {
        assert_eq!(
            k.fetch_style(id, n, "ftp://example.test/s.css"),
            vec![Out::To(id, Msg::StyleFailed { request: n })]
        );
    }
    assert_eq!(
        k.fetch_style(id, 64, "/s.css"),
        vec![Out::To(id, Msg::StyleFailed { request: 64 })]
    );
    // A same-origin navigation commits a new document.
    k.navigate(id, "http://example.test/next");
    k.net(0, InputBuf::Connected);
    k.net(0, InputBuf::Bytes(response(b"next")));
    assert_eq!(
        k.fetch_style(id, 65, "/s.css"),
        vec![sub_connect(id, 64, 1, "example.test")]
    );
}

#[test]
fn a_navigation_ends_the_old_documents_sub_fetches() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    k.fetch_style(id, 1, "/s.css");
    k.navigate(id, "http://example.test/next");
    k.net(0, InputBuf::Connected);
    let out = k.net(0, InputBuf::Bytes(response(b"next")));
    assert!(
        matches!(out.last(), Some(Out::Commit(to, _)) if *to == id),
        "{out:?}"
    );
    // The old document's sub-fetch is ignored, then closed by the next tick.
    assert_eq!(k.sub_net(id, 0, 1, InputBuf::Connected), vec![]);
    assert_eq!(
        k.event(&EventRecord::Tick { time: 1 }),
        vec![Out::SubClose(id, 0, 1)]
    );
    assert_eq!(k.event(&EventRecord::Tick { time: 2 }), vec![]);
}

#[test]
fn a_sub_fetch_past_its_timeout_fails_on_a_tick() {
    let mut k = Kernel::new();
    k.event(&EventRecord::Tick { time: 1000 });
    let id = open(&mut k, "http://example.test/");
    k.fetch_style(id, 5, "/s.css");
    assert_eq!(k.event(&EventRecord::Tick { time: 1059 }), vec![]);
    assert_eq!(
        k.event(&EventRecord::Tick { time: 1060 }),
        vec![
            Out::SubClose(id, 0, 1),
            Out::To(id, Msg::StyleFailed { request: 5 })
        ]
    );
    assert_eq!(k.sub_net(id, 0, 1, InputBuf::Connected), vec![]);
}

#[test]
fn a_style_sheet_asked_for_before_the_first_commit_kills_the_renderer() {
    let mut k = Kernel::new();
    open_fetching(&mut k, "http://example.test/");
    let out = k.fetch_style(0, 1, "/s.css");
    assert_eq!(out, vec![Out::Kill(0), Out::Close(0)]);
}

#[test]
fn a_sub_fetch_event_for_another_renderer_is_ignored() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://a.test/");
    let b = open(&mut k, "http://b.test/");
    k.fetch_style(a, 1, "/s.css");
    // Serial 0 of `b` does not exist: `a`'s fetch is not reachable through `b`.
    assert_eq!(k.sub_net(b, 0, 1, InputBuf::Connected), vec![]);
}

// ---------------------------------------------------------------------
// Item 6.16: a renderer's `Submit`, a navigation with a method and a body.
// ---------------------------------------------------------------------

fn submit(url: &str, method: &str, content_type: &str, body: &[u8]) -> Msg {
    Msg::Submit {
        url: url.as_bytes().to_vec(),
        method: method.as_bytes().to_vec(),
        content_type: content_type.as_bytes().to_vec(),
        body: body.to_vec(),
    }
}

/// The octets of the single `Send` in `out`.
fn the_send(out: &[Out]) -> Option<&[u8]> {
    match out {
        [Out::Send(_, bytes)] => Some(bytes.as_slice()),
        _ => None,
    }
}

const FORM: &str = "application/x-www-form-urlencoded";

#[test]
fn a_submit_sends_its_body_once_on_the_connection_it_opens() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/form");
    let out = k.send(id, &submit("/post", "POST", FORM, b"a=1&b=2"));
    assert_eq!(out, vec![connect(0, "example.test")]);
    let out = k.net(0, InputBuf::Connected);
    let sent = the_send(&out);
    assert!(sent.is_some(), "{out:?}");
    let sent = sent.unwrap_or_default();
    let text = String::from_utf8_lossy(sent).into_owned();
    assert!(text.starts_with("POST /post HTTP/1.1\r\n"), "{text}");
    assert!(
        text.contains(&format!("Content-Type: {FORM}\r\n")),
        "{text}"
    );
    assert!(text.contains("Content-Length: 7\r\n"), "{text}");
    assert!(text.contains("Origin: http://example.test\r\n"), "{text}");
    assert!(sent.ends_with(b"\r\n\r\na=1&b=2"), "{text}");
    // The request is written once: the connection is now reading, and a second
    // `Connected` is a protocol error of the shell that sends nothing.
    let out = k.net(0, InputBuf::Connected);
    assert!(!out.iter().any(|o| matches!(o, Out::Send(..))), "{out:?}");
}

#[test]
fn a_post_without_a_body_sends_a_zero_content_length() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/form");
    k.send(id, &submit("/post", "POST", "", b""));
    let out = k.net(0, InputBuf::Connected);
    let text = String::from_utf8_lossy(the_send(&out).unwrap_or_default()).into_owned();
    assert!(text.starts_with("POST /post HTTP/1.1\r\n"), "{text}");
    assert!(text.contains("Content-Length: 0\r\n"), "{text}");
}

#[test]
fn a_submit_of_get_is_a_navigation_without_a_body() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/form");
    let out = k.send(id, &submit("/q?x=1", "GET", "", b""));
    assert_eq!(out, vec![connect(0, "example.test")]);
    let out = k.net(0, InputBuf::Connected);
    let text = String::from_utf8_lossy(the_send(&out).unwrap_or_default()).into_owned();
    assert!(text.starts_with("GET /q?x=1 HTTP/1.1\r\n"), "{text}");
    assert!(!text.contains("Content-Length"), "{text}");
    assert!(!text.contains("Origin:"), "{text}");
}

#[test]
fn a_submit_the_kernel_cannot_build_is_answered_with_an_error() {
    for bad in [
        submit("/x", "PUT", FORM, b"a=1"),
        submit("/x", "DELETE", "", b""),
        submit("/x", "GET", FORM, b"a=1"),
        submit("/x", "GET", "", b"a=1"),
        submit("http://", "POST", FORM, b"a=1"),
    ] {
        let mut k = Kernel::new();
        let id = open(&mut k, "http://example.test/form");
        let out = k.send(id, &bad);
        assert_eq!(out, vec![Out::To(id, Msg::Error { code: 3 })], "{bad:?}");
        // Nothing started: no connection to answer.
        assert!(k.net(0, InputBuf::Connected).is_empty());
    }
}

#[test]
fn a_submit_from_a_renderer_that_has_not_committed_kills_it() {
    let mut k = Kernel::new();
    let out = k.event(&EventRecord::OpenTab {
        url: code_points("http://example.test/"),
        script: None,
    });
    let id = out.iter().find_map(|o| match o {
        Out::Spawn(id) => Some(*id),
        _ => None,
    });
    let id = id.unwrap_or(u64::MAX);
    let out = k.send(id, &submit("/post", "POST", FORM, b"a=1"));
    assert!(out.contains(&Out::Kill(id)), "{out:?}");
    assert!(!out.iter().any(|o| matches!(o, Out::Send(..))), "{out:?}");
}

#[test]
fn a_post_redirected_by_301_302_or_303_becomes_a_get_without_the_body() {
    for status in if cfg!(miri) {
        vec![302]
    } else {
        vec![301, 302, 303]
    } {
        let mut k = Kernel::new();
        let id = open(&mut k, "http://example.test/form");
        k.send(id, &submit("/post", "POST", FORM, b"secret=1"));
        k.net(0, InputBuf::Connected);
        let redirect = format!(
            "HTTP/1.1 {status} X\r\nLocation: http://example.test/done\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
        );
        let out = k.net(0, InputBuf::Bytes(redirect.into_bytes()));
        assert_eq!(out, vec![Out::Close(0), connect(1, "example.test")]);
        let out = k.net(1, InputBuf::Connected);
        let text = String::from_utf8_lossy(the_send(&out).unwrap_or_default()).into_owned();
        assert!(
            text.starts_with("GET /done HTTP/1.1\r\n"),
            "{status}: {text}"
        );
        assert!(!text.contains("secret=1"), "{status}: {text}");
        assert!(!text.contains("Content-Length"), "{status}: {text}");
    }
}

#[test]
fn a_post_redirected_by_307_or_308_sends_its_body_again() {
    for status in if cfg!(miri) {
        vec![307]
    } else {
        vec![307, 308]
    } {
        let mut k = Kernel::new();
        let id = open(&mut k, "http://example.test/form");
        k.send(id, &submit("/post", "POST", FORM, b"secret=1"));
        k.net(0, InputBuf::Connected);
        let redirect = format!(
            "HTTP/1.1 {status} X\r\nLocation: http://example.test/again\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
        );
        let out = k.net(0, InputBuf::Bytes(redirect.into_bytes()));
        assert_eq!(out, vec![Out::Close(0), connect(1, "example.test")]);
        let out = k.net(1, InputBuf::Connected);
        let sent = the_send(&out).unwrap_or_default();
        let text = String::from_utf8_lossy(sent).into_owned();
        assert!(
            text.starts_with("POST /again HTTP/1.1\r\n"),
            "{status}: {text}"
        );
        assert!(sent.ends_with(b"\r\n\r\nsecret=1"), "{status}: {text}");
    }
}

#[test]
fn a_post_redirected_off_site_by_307_names_a_null_origin() {
    // A 307 from the form's site to another site keeps the body (RFC 9110
    // 15.4.8); the `Origin` is then `null` (Fetch: the redirect left the
    // origin), not the form's.
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/form");
    k.send(id, &submit("/post", "POST", FORM, b"a=1"));
    k.net(0, InputBuf::Connected);
    let redirect = b"HTTP/1.1 307 X\r\nLocation: http://other.test/in\r\nContent-Length: 0\r\nConnection: close\r\n\r\n".to_vec();
    let out = k.net(0, InputBuf::Bytes(redirect));
    assert_eq!(out, vec![Out::Close(0), connect(1, "other.test")]);
    let out = k.net(1, InputBuf::Connected);
    let text = String::from_utf8_lossy(the_send(&out).unwrap_or_default()).into_owned();
    assert!(text.starts_with("POST /in HTTP/1.1\r\n"), "{text}");
    assert!(text.contains("Origin: null\r\n"), "{text}");
}

#[test]
fn a_submit_replaces_only_its_own_tabs_navigation() {
    let mut k = Kernel::new();
    let a = open(&mut k, "http://example.test/a");
    let b = open(&mut k, "http://other.test/b");
    // Tab b has a navigation in flight.
    assert_eq!(
        k.navigate(b, "http://other.test/next"),
        vec![connect(0, "other.test")]
    );
    // A submit from tab a opens its own connection and closes nothing of b.
    let out = k.send(a, &submit("/post", "POST", FORM, b"a=1"));
    assert_eq!(out, vec![connect(1, "example.test")]);
    // The connection of b still answers b.
    k.net(0, InputBuf::Connected);
    let out = k.net(0, InputBuf::Bytes(response(b"page of b")));
    assert_eq!(
        out,
        vec![
            Out::Close(0),
            Out::Commit(b, commit("http://other.test/next", b"page of b"))
        ]
    );
    // A later submit of tab a replaces its navigation: the old connection is closed.
    let out = k.send(a, &submit("/again", "POST", FORM, b"c=2"));
    assert_eq!(out, vec![Out::Close(1), connect(2, "example.test")]);
}

#[test]
fn a_submit_of_a_large_body_is_sent_whole() {
    // One `Submit` is one frame (1 MiB): the body bound is the frame's.
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/form");
    let body = vec![b'x'; if cfg!(miri) { 1000 } else { 1_000_000 }];
    let out = k.send(id, &submit("/post", "POST", FORM, &body));
    assert_eq!(out, vec![connect(0, "example.test")]);
    let out = k.net(0, InputBuf::Connected);
    let sent = the_send(&out).unwrap_or_default();
    assert!(sent.ends_with(&body));
}

// ---------------------------------------------------------------------
// Item 6.17: image sub-fetches (`FetchSub`) and Opaque Response Blocking.
// ---------------------------------------------------------------------

/// The signature of a PNG, then a few more octets.
const PNG: &[u8] = &[
    0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0, 0, 0, 0x0D,
];

impl Kernel {
    fn fetch_sub(&mut self, id: u64, request: u64, destination: u64, url: &str) -> Vec<Out> {
        self.send(
            id,
            &Msg::FetchSub {
                request,
                destination,
                url: url.as_bytes().to_vec(),
            },
        )
    }

    /// Fetch `url` as an image (the renderer's sub-fetch number `serial`),
    /// serve `response` on its first connection and return the frames the
    /// renderer is sent.
    fn image_answer(
        &mut self,
        id: u64,
        serial: u64,
        request: u64,
        url: &str,
        response: Vec<u8>,
    ) -> Vec<Msg> {
        self.fetch_sub(id, request, 1, url);
        self.sub_net(id, serial, 1, InputBuf::Connected);
        let out = self.sub_net(id, serial, 1, InputBuf::Bytes(response));
        out.into_iter()
            .filter_map(|o| match o {
                Out::Frames(to, msgs) if to == id => Some(msgs),
                Out::To(to, m) if to == id => Some(vec![m]),
                _ => None,
            })
            .flatten()
            .collect()
    }
}

fn png_response(extra: &str) -> Vec<u8> {
    response_with(extra, PNG)
}

#[test]
fn a_same_origin_image_is_fetched_with_cookies_and_answered_in_the_sub_family() {
    let mut k = Kernel::new();
    let id = page_with_cookie(&mut k);
    let out = k.fetch_sub(id, 7, 1, "/i.png");
    assert_eq!(out, vec![sub_connect(id, 0, 1, "example.test")]);
    let out = k.sub_net(id, 0, 1, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::SubSend(_, 0, 1, req)]
            if req.starts_with(b"GET /i.png HTTP/1.1\r\n") && has(req, b"Cookie: a=b")
    );
    assert!(ok, "{out:?}");
    let out = k.sub_net(
        id,
        0,
        1,
        InputBuf::Bytes(png_response("Content-Type: image/png")),
    );
    assert_eq!(
        out,
        vec![
            Out::SubClose(id, 0, 1),
            Out::Frames(
                id,
                vec![
                    Msg::SubResponse {
                        request: 7,
                        content_type: b"image/png".to_vec()
                    },
                    Msg::SubBody {
                        request: 7,
                        bytes: PNG.to_vec()
                    },
                    Msg::SubEnd { request: 7 },
                ]
            )
        ]
    );
}

#[test]
fn a_cross_origin_image_carries_no_cookies_and_a_png_is_let_through() {
    let mut k = Kernel::new();
    let id = page_with_cookie(&mut k);
    k.fetch_sub(id, 1, 1, "http://other.test/i.png");
    let out = k.sub_net(id, 0, 1, InputBuf::Connected);
    let ok = matches!(
        out.as_slice(),
        [Out::SubSend(_, 0, 1, req)] if req.starts_with(b"GET /i.png") && !has(req, b"Cookie")
    );
    assert!(ok, "{out:?}");
    let out = k.sub_net(
        id,
        0,
        1,
        InputBuf::Bytes(png_response("Content-Type: image/png")),
    );
    let ok = matches!(
        out.last(),
        Some(Out::Frames(_, m)) if matches!(m.first(), Some(Msg::SubResponse { .. }))
    );
    assert!(ok, "{out:?}");
}

#[test]
fn orb_lets_through_a_cross_origin_png_mislabeled_as_html_and_an_unlabeled_one() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    let m = k.image_answer(
        id,
        0,
        1,
        "http://other.test/a",
        png_response("Content-Type: text/html"),
    );
    assert!(
        matches!(m.first(), Some(Msg::SubResponse { request: 1, .. })),
        "{m:?}"
    );
    let m = k.image_answer(id, 1, 2, "http://other.test/b", png_response("X-Test: 1"));
    assert!(
        matches!(m.first(), Some(Msg::SubResponse { request: 2, .. })),
        "{m:?}"
    );
}

#[test]
fn orb_blocks_cross_origin_responses_that_are_not_images_and_sends_no_body() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    let secret = b"<html>intranet secret</html>";
    let mut partial = png_response("Content-Type: image/png");
    partial.splice(9..12, b"206".iter().copied());
    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("html", response_with("Content-Type: text/html", secret)),
        (
            "html nosniff",
            response_with(
                "Content-Type: text/html\r\nX-Content-Type-Options: nosniff",
                secret,
            ),
        ),
        (
            "json",
            response_with("Content-Type: application/json", b"{\"a\":1}"),
        ),
        (
            "pdf with png bytes",
            png_response("Content-Type: application/pdf"),
        ),
        ("no type", response_with("X-Test: 1", secret)),
        ("plain", response_with("Content-Type: text/plain", secret)),
        ("partial", partial),
    ];
    for (n, (what, response)) in cases.into_iter().enumerate() {
        let serial = n as u64;
        let request = 10 + serial;
        let m = k.image_answer(id, serial, request, "http://other.test/x", response);
        assert_eq!(m, vec![Msg::SubFailed { request }], "{what}");
    }
}

#[test]
fn orb_does_not_apply_to_a_same_origin_image_whatever_it_is() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    let m = k.image_answer(
        id,
        0,
        1,
        "/x",
        response_with("Content-Type: text/html", b"<p>"),
    );
    let ok = matches!(
        m.as_slice(),
        [
            Msg::SubResponse { request: 1, .. },
            Msg::SubBody { .. },
            Msg::SubEnd { request: 1 }
        ]
    );
    assert!(ok, "{m:?}");
}

#[test]
fn orb_decides_style_sheet_fetches_too_in_either_family() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    // A cross-origin text/css is safelisted, with FetchSub (destination 0) and
    // with FetchStyle.
    k.fetch_sub(id, 1, 0, "http://other.test/s.css");
    k.sub_net(id, 0, 1, InputBuf::Connected);
    let css = response_with("Content-Type: text/css", b"p{}");
    let out = k.sub_net(id, 0, 1, InputBuf::Bytes(css.clone()));
    let ok = matches!(
        out.last(),
        Some(Out::Frames(_, m)) if matches!(m.first(), Some(Msg::SubResponse { request: 1, .. }))
    );
    assert!(ok, "{out:?}");
    k.fetch_style(id, 2, "http://other.test/t.css");
    k.sub_net(id, 1, 1, InputBuf::Connected);
    let out = k.sub_net(id, 1, 1, InputBuf::Bytes(css));
    let ok = matches!(
        out.last(),
        Some(Out::Frames(_, m)) if matches!(m.first(), Some(Msg::StyleResponse { request: 2, .. }))
    );
    assert!(ok, "{out:?}");
    // A cross-origin response of another type is a StyleFailed.
    k.fetch_style(id, 3, "http://other.test/u.css");
    k.sub_net(id, 2, 1, InputBuf::Connected);
    let out = k.sub_net(
        id,
        2,
        1,
        InputBuf::Bytes(response_with("Content-Type: text/html", b"<p>")),
    );
    assert_eq!(
        out,
        vec![
            Out::SubClose(id, 2, 1),
            Out::To(id, Msg::StyleFailed { request: 3 })
        ]
    );
}

#[test]
fn an_image_fetch_has_its_own_limits_and_an_unknown_destination_is_refused() {
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    // Sixteen images in flight; the seventeenth is refused with SubFailed.
    for n in 0..16u64 {
        assert_eq!(
            k.fetch_sub(id, n, 1, "/i.png"),
            vec![sub_connect(id, n, 1, "example.test")]
        );
    }
    assert_eq!(
        k.fetch_sub(id, 16, 1, "/i.png"),
        vec![Out::To(id, Msg::SubFailed { request: 16 })]
    );
    // A style sheet request is refused past eight in flight (all kinds count).
    assert_eq!(
        k.fetch_style(id, 17, "/s.css"),
        vec![Out::To(id, Msg::StyleFailed { request: 17 })]
    );
    assert_eq!(
        k.fetch_sub(id, 18, 0, "/s.css"),
        vec![Out::To(id, Msg::SubFailed { request: 18 })]
    );
    // Another renderer's limit is its own, and an unknown destination is
    // refused.
    let other = open(&mut k, "http://other.test/");
    assert_eq!(
        k.fetch_sub(other, 0, 2, "/i.png"),
        vec![Out::To(other, Msg::SubFailed { request: 0 })]
    );
    assert_eq!(
        k.fetch_sub(other, 1, 1, "/i.png"),
        vec![sub_connect(other, 0, 1, "other.test")]
    );
}

#[test]
fn a_document_starts_at_most_4096_image_fetches() {
    if cfg!(miri) {
        return;
    }
    let mut k = Kernel::new();
    let id = open(&mut k, "http://example.test/");
    for n in 0..4096u64 {
        assert_eq!(
            k.fetch_sub(id, n, 1, "/i.png"),
            vec![sub_connect(id, n, 1, "example.test")],
            "{n}"
        );
        // The fetch fails at once, so at most one is ever in flight.
        k.sub_net(id, n, 1, InputBuf::Closed);
    }
    assert_eq!(
        k.fetch_sub(id, 4096, 1, "/i.png"),
        vec![Out::To(id, Msg::SubFailed { request: 4096 })]
    );
}

#[test]
fn an_image_asked_for_before_the_first_commit_kills_the_renderer() {
    let mut k = Kernel::new();
    open_fetching(&mut k, "http://example.test/");
    let out = k.fetch_sub(0, 1, 1, "/i.png");
    assert_eq!(out, vec![Out::Kill(0), Out::Close(0)]);
}

#[test]
fn an_image_fetch_past_its_timeout_fails_in_the_sub_family() {
    let mut k = Kernel::new();
    k.event(&EventRecord::Tick { time: 1000 });
    let id = open(&mut k, "http://example.test/");
    k.fetch_sub(id, 5, 1, "/i.png");
    assert_eq!(
        k.event(&EventRecord::Tick { time: 1060 }),
        vec![
            Out::SubClose(id, 0, 1),
            Out::To(id, Msg::SubFailed { request: 5 })
        ]
    );
}
