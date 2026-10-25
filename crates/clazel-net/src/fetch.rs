//! `fetch`: an `http://` GET with its redirects, driven end to end. Every
//! decision is made by `clazel-fetch`'s proven transducer
//! (`clazel_fetch::transducer`): which host and port to connect to, the
//! request bytes, when a response is complete, interim responses, which
//! redirects to follow and when to stop. The URL is parsed by
//! `clazel-url`. This module only carries out the transducer's actions on
//! sockets and reports back what happened, without looking at the bytes.

use std::collections::VecDeque;
use std::net::IpAddr;

use clazel_cookie::storage::exec::CookieRecord;
use clazel_fetch::transducer::real::step_real;
use clazel_fetch::transducer::spec::Reason;
use clazel_fetch::transducer::step::{apply_ops_exec, start};
use clazel_fetch::transducer::types::{ActionBuf, InputBuf};
use clazel_http::message::types::ResponseBuf;
use clazel_url::url::parse::basic_url_parser;

use crate::conn::{Connection, Timeouts};
use crate::error::NetError;
use crate::resolve::resolve;

/// Why a fetch gave no response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FetchError {
    /// The URL does not parse.
    Url,
    /// A URL this client does not fetch (not `http:`, userinfo, …), also
    /// as the target of a redirect.
    NotFetched,
    /// The network failed.
    Net(NetError),
    /// The server's bytes are not a valid response, or the connection
    /// closed before one was complete.
    Invalid,
    /// A transfer coding this client cannot decode.
    Unsupported,
    /// A redirect whose `Location` is missing a URL: it does not parse, or
    /// there is more than one.
    RedirectLocation,
    /// A redirect to a scheme other than `http` or `https`.
    RedirectScheme,
    /// More than 20 redirects.
    TooManyRedirects,
}

impl std::fmt::Display for FetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FetchError::Url => write!(f, "not a URL"),
            FetchError::NotFetched => write!(f, "only http: URLs without userinfo are fetched"),
            FetchError::Net(e) => write!(f, "{e}"),
            FetchError::Invalid => write!(f, "the server sent an invalid HTTP response"),
            FetchError::Unsupported => write!(
                f,
                "the response uses a transfer coding this client cannot decode"
            ),
            FetchError::RedirectLocation => {
                write!(f, "a redirect's Location is not a single valid URL")
            }
            FetchError::RedirectScheme => write!(f, "a redirect to a scheme that is not HTTP(S)"),
            FetchError::TooManyRedirects => write!(f, "more than 20 redirects"),
        }
    }
}

impl std::error::Error for FetchError {}

/// Fetches `url` with GET, following redirects, and returns the final
/// response.
pub fn fetch(url: &str) -> Result<ResponseBuf, FetchError> {
    fetch_with(url, Timeouts::default(), resolve)
}

/// The error for the transducer's `Fail`, given the last network error
/// the shell saw.
fn failure(reason: Reason, net: Option<NetError>) -> FetchError {
    match reason {
        Reason::NotFetched => FetchError::NotFetched,
        Reason::Network | Reason::Shell => {
            FetchError::Net(net.unwrap_or(NetError::Io(std::io::ErrorKind::ConnectionAborted)))
        }
        Reason::Invalid | Reason::Incomplete => FetchError::Invalid,
        Reason::Unsupported => FetchError::Unsupported,
        Reason::RedirectLocation => FetchError::RedirectLocation,
        Reason::RedirectScheme => FetchError::RedirectScheme,
        Reason::RedirectLimit => FetchError::TooManyRedirects,
    }
}

/// [`fetch`], with the timeouts and the resolver chosen by the caller (the
/// tests use a resolver that knows only `127.0.0.1`).
pub fn fetch_with(
    url: &str,
    timeouts: Timeouts,
    resolver: impl Fn(&[u8]) -> Result<Vec<IpAddr>, NetError>,
) -> Result<ResponseBuf, FetchError> {
    fetch_jar(url, Vec::new(), now_1601(), timeouts, resolver).0
}

/// The current time as `clazel-cookie` counts it: seconds since
/// 1601-01-01T00:00:00Z, kept within the range its functions accept (the
/// end of year 9999).
pub fn now_1601() -> u64 {
    // Seconds from 1601-01-01 to 1970-01-01.
    const EPOCH_GAP: u64 = 11_644_473_600;
    // The end of year 9999, `clazel_cookie::set_cookie::contract::now_in_range`'s limit.
    const LATEST: u64 = 265_046_774_399;
    let unix = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    unix.saturating_add(EPOCH_GAP).min(LATEST)
}

/// [`fetch_with`] with a cookie jar: `url` is fetched with `jar` at time
/// `now` (seconds since 1601, see [`now_1601`]), and the jar comes back
/// with the transducer's jar operations applied, whether the fetch gave a
/// response or not (every `Set-Cookie` of a final response is stored,
/// redirects and failures after it included).
pub fn fetch_jar(
    url: &str,
    jar: Vec<CookieRecord>,
    now: u64,
    timeouts: Timeouts,
    resolver: impl Fn(&[u8]) -> Result<Vec<IpAddr>, NetError>,
) -> (Result<ResponseBuf, FetchError>, Vec<CookieRecord>) {
    let input: Vec<u32> = url.chars().map(u32::from).collect();
    let Some(parsed) = basic_url_parser(&input, None) else {
        return (Err(FetchError::Url), jar);
    };
    let mut jar = jar;
    let (mut state, first) = start(&parsed);
    let mut pending: VecDeque<ActionBuf> = first.into();
    let mut conn: Option<Connection> = None;
    let mut net: Option<NetError> = None;
    let mut buf = vec![0u8; crate::conn::READ_BUF];
    loop {
        // Carry out the actions in order; when there are none, the
        // transducer is waiting for the connection.
        let input = match pending.pop_front() {
            Some(action) => match action {
                ActionBuf::Connect { host, port, tls } => {
                    conn = None;
                    let opened = if tls {
                        Err(NetError::Io(std::io::ErrorKind::Unsupported))
                    } else {
                        resolver(&host).and_then(|addrs| Connection::open(&addrs, port, timeouts))
                    };
                    match opened {
                        Ok(c) => {
                            conn = Some(c);
                            InputBuf::Connected
                        }
                        Err(e) => {
                            net = Some(e);
                            InputBuf::Error
                        }
                    }
                }
                ActionBuf::Send(bytes) => {
                    let sent = match conn.as_mut() {
                        Some(c) => c.send(&bytes),
                        None => Err(NetError::Io(std::io::ErrorKind::NotConnected)),
                    };
                    match sent {
                        Ok(()) => continue,
                        Err(e) => {
                            net = Some(e);
                            InputBuf::Error
                        }
                    }
                }
                ActionBuf::Close => {
                    conn = None;
                    continue;
                }
                ActionBuf::Done { response, .. } => return (Ok(*response), jar),
                ActionBuf::Fail(reason) => return (Err(failure(reason, net)), jar),
            },
            None => match conn.as_mut() {
                Some(c) => match c.read(&mut buf) {
                    Ok(Some(n)) => InputBuf::Bytes(buf.get(..n).unwrap_or_default().to_vec()),
                    Ok(None) => {
                        conn = None;
                        InputBuf::Closed
                    }
                    Err(e) => {
                        net = Some(e);
                        InputBuf::Error
                    }
                },
                // Waiting with no connection: a transducer that asked for
                // nothing. Report it as an error so that it ends.
                None => InputBuf::Error,
            },
        };
        // The operations come before the actions they go with, so the jar
        // is up to date when a `Done` or `Fail` returns it.
        let (s, next, ops) = step_real(state, &input, &jar, now);
        jar = apply_ops_exec(jar, &ops);
        state = s;
        pending.extend(next);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::net::{Ipv4Addr, TcpListener};
    use std::sync::mpsc;
    use std::time::Duration;

    /// Reads one request head from `s`.
    fn read_head(s: &mut std::net::TcpStream) -> Vec<u8> {
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

    /// A server on 127.0.0.1 that reads one request head, sends `reply` in
    /// pieces of `step` octets, closes, and reports the request it read.
    fn serve(reply: &'static [u8], step: usize) -> Option<(u16, mpsc::Receiver<Vec<u8>>)> {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).ok()?;
        let port = listener.local_addr().ok()?.port();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            if let Ok((mut s, _)) = listener.accept() {
                let got = read_head(&mut s);
                for piece in reply.chunks(step) {
                    let _ = s.write_all(piece);
                    let _ = s.flush();
                }
                let _ = tx.send(got);
            }
        });
        Some((port, rx))
    }

    /// A server on 127.0.0.1 for redirect chains, one request per
    /// connection: `GET /r/<n>` with n > 0 redirects to `/r/<n-1>`
    /// (alternating relative and absolute `Location`s and the five
    /// redirect statuses), `/r/0` is `200` with body `done`, `/mailto` is a
    /// redirect to `mailto:x`, `/two` has two `Location` lines. It reports
    /// each request target it reads, and serves `limit` connections.
    fn redirect_server(limit: usize) -> Option<(u16, mpsc::Receiver<String>)> {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).ok()?;
        let port = listener.local_addr().ok()?.port();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            for _ in 0..limit {
                let Ok((mut s, _)) = listener.accept() else {
                    return;
                };
                let head = String::from_utf8_lossy(&read_head(&mut s)).into_owned();
                let target = head.split(' ').nth(1).unwrap_or_default().to_owned();
                let reply = match target.strip_prefix("/r/").and_then(|n| n.parse::<u32>().ok()) {
                    Some(0) => "HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\ndone".to_owned(),
                    Some(n) => {
                        let code = [301, 302, 303, 307, 308]
                            .get((n % 5) as usize)
                            .copied()
                            .unwrap_or(302);
                        let next = n.saturating_sub(1);
                        let location = if n % 2 == 0 {
                            format!("/r/{next}")
                        } else {
                            format!("http://127.0.0.1:{port}/r/{next}")
                        };
                        format!(
                            "HTTP/1.1 {code} Moved\r\nLocation: {location}\r\nContent-Length: 0\r\n\r\n"
                        )
                    }
                    None if target == "/mailto" => {
                        "HTTP/1.1 302 Found\r\nLocation: mailto:x\r\nContent-Length: 0\r\n\r\n"
                            .to_owned()
                    }
                    None if target == "/two" => {
                        "HTTP/1.1 302 Found\r\nLocation: /r/0\r\nLocation: /r/0\r\nContent-Length: 0\r\n\r\n"
                            .to_owned()
                    }
                    None => "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n".to_owned(),
                };
                let _ = s.write_all(reply.as_bytes());
                let _ = s.flush();
                if tx.send(target).is_err() {
                    return;
                }
            }
        });
        Some((port, rx))
    }

    fn local(_: &[u8]) -> Result<Vec<IpAddr>, NetError> {
        Ok(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
    }

    fn quick() -> Timeouts {
        Timeouts {
            connect: Duration::from_secs(2),
            idle: Duration::from_secs(2),
        }
    }

    type Outcome = Result<(u16, Vec<u8>), FetchError>;

    fn outcome(r: Result<ResponseBuf, FetchError>) -> Outcome {
        r.map(|r| (r.status_line.status, r.body))
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn the_request_on_the_wire() {
        let Some((port, rx)) = serve(b"HTTP/1.1 204 No Content\r\n\r\n", 4096) else {
            return;
        };
        let r = fetch_with(
            &format!("http://LocalHost:{port}/a%20b?c=d#frag"),
            quick(),
            local,
        );
        assert_eq!(outcome(r), Ok((204, Vec::new())));
        let expected = format!(
            "GET /a%20b?c=d HTTP/1.1\r\nHost: localhost:{port}\r\nConnection: close\r\nAccept: */*\r\nUser-Agent: clazel\r\n\r\n"
        );
        assert_eq!(
            rx.recv_timeout(Duration::from_secs(2)).ok(),
            Some(expected.into_bytes())
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn framings() {
        let cases: [(&'static [u8], Outcome); 6] = [
            (
                b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello",
                Ok((200, b"hello".to_vec())),
            ),
            (
                b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n",
                Ok((200, b"abc".to_vec())),
            ),
            (
                b"HTTP/1.1 200 OK\r\n\r\nuntil close",
                Ok((200, b"until close".to_vec())),
            ),
            (
                b"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n",
                Ok((404, Vec::new())),
            ),
            (
                b"HTTP/1.1 200 OK\r\nContent-Length: 9\r\n\r\nshort",
                Err(FetchError::Invalid),
            ),
            (
                b"HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n",
                Err(FetchError::Unsupported),
            ),
        ];
        for (reply, expected) in cases {
            for step in [1, 7, 4096] {
                let Some((port, _)) = serve(reply, step) else {
                    return;
                };
                let r = fetch_with(&format!("http://localhost:{port}/"), quick(), local);
                assert_eq!(
                    outcome(r),
                    expected,
                    "{:?} step {step}",
                    String::from_utf8_lossy(reply)
                );
            }
        }
    }

    /// The targets a redirect server read, in order.
    fn targets(rx: &mpsc::Receiver<String>) -> Vec<String> {
        let mut got = Vec::new();
        while let Ok(t) = rx.recv_timeout(Duration::from_millis(500)) {
            got.push(t);
        }
        got
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_redirect_chain_is_followed() {
        let Some((port, rx)) = redirect_server(4) else {
            return;
        };
        let r = fetch_with(&format!("http://127.0.0.1:{port}/r/3"), quick(), local);
        assert_eq!(outcome(r), Ok((200, b"done".to_vec())));
        assert_eq!(targets(&rx), ["/r/3", "/r/2", "/r/1", "/r/0"]);
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn twenty_redirects_are_followed() {
        let Some((port, rx)) = redirect_server(21) else {
            return;
        };
        let r = fetch_with(&format!("http://127.0.0.1:{port}/r/20"), quick(), local);
        assert_eq!(outcome(r), Ok((200, b"done".to_vec())));
        assert_eq!(targets(&rx).len(), 21);
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn the_twenty_first_redirect_is_refused() {
        let Some((port, rx)) = redirect_server(22) else {
            return;
        };
        let r = fetch_with(&format!("http://127.0.0.1:{port}/r/21"), quick(), local);
        assert_eq!(outcome(r), Err(FetchError::TooManyRedirects));
        // 21 requests: the first and 20 redirects; the 21st redirect is
        // not followed.
        let got = targets(&rx);
        assert_eq!(got.len(), 21);
        assert_eq!(got.last().map(String::as_str), Some("/r/1"));
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn bad_redirects_fail() {
        for (path, expected) in [
            ("/mailto", FetchError::RedirectScheme),
            ("/two", FetchError::RedirectLocation),
        ] {
            let Some((port, _)) = redirect_server(1) else {
                return;
            };
            let r = fetch_with(&format!("http://127.0.0.1:{port}{path}"), quick(), local);
            assert_eq!(outcome(r), Err(expected), "{path}");
        }
    }

    #[test]
    fn not_fetched() {
        assert_eq!(
            fetch_with("https://example.com/", quick(), local).map(|_| ()),
            Err(FetchError::NotFetched)
        );
        assert_eq!(
            fetch_with("http://u:p@example.com/", quick(), local).map(|_| ()),
            Err(FetchError::NotFetched)
        );
        assert_eq!(
            fetch_with("not a url", quick(), local).map(|_| ()),
            Err(FetchError::Url)
        );
    }

    /// A server for cookies, one request per connection: `GET /set` sets
    /// two cookies in two `Set-Cookie` lines (one `Secure`) and redirects
    /// to `/echo`, which answers `200` and reports every request head it
    /// was sent.
    fn cookie_server(connections: usize) -> Option<(u16, mpsc::Receiver<Vec<u8>>)> {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).ok()?;
        let port = listener.local_addr().ok()?.port();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            for _ in 0..connections {
                let Ok((mut s, _)) = listener.accept() else {
                    return;
                };
                let head = read_head(&mut s);
                let reply: &[u8] = if head.starts_with(b"GET /set ") {
                    b"HTTP/1.1 302 Found\r\nSet-Cookie: a=1\r\nSet-Cookie: b=2; Secure\r\nSet-Cookie: c=3; Path=/echo\r\nLocation: /echo\r\nContent-Length: 0\r\n\r\n"
                } else {
                    b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\n"
                };
                let _ = s.write_all(reply);
                let _ = tx.send(head);
            }
        });
        Some((port, rx))
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn cookies_set_then_sent_on_the_redirect() {
        let Some((port, rx)) = cookie_server(2) else {
            return;
        };
        let (r, jar) = fetch_jar(
            &format!("http://127.0.0.1:{port}/set"),
            Vec::new(),
            now_1601(),
            quick(),
            local,
        );
        assert_eq!(outcome(r), Ok((200, Vec::new())));
        let first = rx.recv_timeout(Duration::from_secs(5)).unwrap_or_default();
        let second = rx.recv_timeout(Duration::from_secs(5)).unwrap_or_default();
        let text = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
        // No jar, no `Cookie` field; then the cookies that apply to /echo
        // over http: not the Secure one, the Path=/echo one included, first (longer path, §5.8.3 step 4).
        assert!(!text(&first).contains("Cookie:"), "{}", text(&first));
        assert!(
            text(&second).contains("\r\nCookie: c=3; a=1\r\n"),
            "{}",
            text(&second)
        );
        // The jar comes back with the two cookies stored: a `Secure`
        // cookie from an `http:` response is ignored (§5.7 step 17).
        assert_eq!(jar.len(), 2);
    }
}
