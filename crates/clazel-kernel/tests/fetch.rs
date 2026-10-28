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

fn commit(url: &str, script: &[u8]) -> Msg {
    Msg::Commit {
        url: url.as_bytes().to_vec(),
        script: script.to_vec(),
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
            Out::To(id, commit("http://example.test/next", b"page body"))
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
            Out::To(id, commit("http://example.test/second", b"new"))
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
            Out::Spawn(new),
            Out::To(to, Msg::Commit { url, script }),
        ] if *old == id
            && new == to
            && *new != id
            && url.as_slice() == b"http://other.test/landed"
            && script.as_slice() == b"landing page"
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
            Out::To(b, commit("http://b.test/y", b"for b"))
        ]
    );
    let out = k.net(0, InputBuf::Bytes(response(b"for a")));
    assert_eq!(
        out,
        vec![
            Out::Close(0),
            Out::To(a, commit("http://a.test/x", b"for a"))
        ]
    );
}
