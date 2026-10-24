//! `fetch`: one `http://` GET, driven end to end. Every decision is a
//! proven function: the URL is parsed by `clazel-url`, the request bytes
//! and where to connect come from `clazel-fetch`, the reply is framed by
//! `clazel-http`'s `ResponseParser`, and an interim (1xx) response is
//! recognised by `clazel-fetch`. This module only moves bytes between
//! them and the socket.

use std::net::IpAddr;

use clazel_fetch::request::build::{connect_to, is_interim, request_bytes};
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::{ParseBuf, ResponseBuf};
use clazel_url::url::parse::basic_url_parser;

use crate::conn::{Finish, Flow, Timeouts, run_with};
use crate::error::NetError;
use crate::resolve::resolve;

/// Why a fetch gave no response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FetchError {
    /// The URL does not parse.
    Url,
    /// A URL this client does not fetch (not `http:`, userinfo, …).
    NotFetched,
    /// The network failed.
    Net(NetError),
    /// The server's bytes are not a valid response.
    Invalid,
    /// A transfer coding this client cannot decode.
    Unsupported,
}

impl std::fmt::Display for FetchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FetchError::Url => write!(f, "not a URL"),
            FetchError::NotFetched => write!(f, "only http: URLs without userinfo are fetched"),
            FetchError::Net(e) => write!(f, "{e}"),
            FetchError::Invalid => write!(f, "the server sent an invalid HTTP response"),
            FetchError::Unsupported => write!(f, "the response uses a transfer coding this client cannot decode"),
        }
    }
}

impl std::error::Error for FetchError {}

/// Fetches `url` with GET and returns the final response.
pub fn fetch(url: &str) -> Result<ResponseBuf, FetchError> {
    fetch_with(url, Timeouts::default(), resolve)
}

/// [`fetch`], with the timeouts and the resolver chosen by the caller (the
/// tests use a resolver that knows only `127.0.0.1`).
pub fn fetch_with(
    url: &str,
    timeouts: Timeouts,
    resolver: impl Fn(&[u8]) -> Result<Vec<IpAddr>, NetError>,
) -> Result<ResponseBuf, FetchError> {
    let input: Vec<u32> = url.chars().map(u32::from).collect();
    let parsed = basic_url_parser(&input, None).ok_or(FetchError::Url)?;
    let request = request_bytes(&parsed).ok_or(FetchError::NotFetched)?;
    let (host, port) = connect_to(&parsed).ok_or(FetchError::NotFetched)?;
    let addrs = resolver(&host).map_err(FetchError::Net)?;

    let mut parser = ResponseParser::new(false);
    let mut decided: Option<ParseBuf> = None;
    let finish = run_with(&addrs, port, &request, timeouts, |bytes| {
        let mut next = parser.feed(bytes);
        // An interim response is skipped: the bytes after it start the next
        // response (RFC 9110 §15.2).
        while let ParseBuf::Done { response, rest } = &next {
            if !is_interim(response.status_line.status) {
                break;
            }
            let rest = rest.clone();
            parser = ResponseParser::new(false);
            next = parser.feed(&rest);
        }
        match next {
            ParseBuf::Incomplete => Flow::Continue,
            other => {
                decided = Some(other);
                Flow::Stop
            }
        }
    })
    .map_err(FetchError::Net)?;
    let result = match (decided, finish) {
        (Some(r), _) => r,
        (None, Finish::Closed) => parser.close(),
        (None, Finish::Stopped) => ParseBuf::Invalid,
    };
    match result {
        ParseBuf::Done { response, .. } => Ok(response),
        ParseBuf::Incomplete | ParseBuf::Invalid => Err(FetchError::Invalid),
        ParseBuf::Unsupported => Err(FetchError::Unsupported),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::net::{Ipv4Addr, TcpListener};
    use std::sync::mpsc;
    use std::time::Duration;

    /// A server on 127.0.0.1 that reads one request head, sends `reply` in
    /// pieces of `step` octets, closes, and reports the request it read.
    fn serve(reply: &'static [u8], step: usize) -> Option<(u16, mpsc::Receiver<Vec<u8>>)> {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).ok()?;
        let port = listener.local_addr().ok()?.port();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            if let Ok((mut s, _)) = listener.accept() {
                let mut got = Vec::new();
                let mut buf = [0u8; 1024];
                while !got.ends_with(b"\r\n\r\n") {
                    match s.read(&mut buf) {
                        Ok(0) | Err(_) => break,
                        Ok(n) => got.extend_from_slice(buf.get(..n).unwrap_or_default()),
                    }
                }
                for piece in reply.chunks(step) {
                    let _ = s.write_all(piece);
                    let _ = s.flush();
                }
                let _ = tx.send(got);
            }
        });
        Some((port, rx))
    }

    fn local(_: &[u8]) -> Result<Vec<IpAddr>, NetError> {
        Ok(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
    }

    fn quick() -> Timeouts {
        Timeouts { connect: Duration::from_secs(2), idle: Duration::from_secs(2) }
    }

    type Outcome = Result<(u16, Vec<u8>), FetchError>;

    fn outcome(r: Result<ResponseBuf, FetchError>) -> Outcome {
        r.map(|r| (r.status_line.status, r.body))
    }

    #[test]
    fn the_request_on_the_wire() {
        let Some((port, rx)) = serve(b"HTTP/1.1 204 No Content\r\n\r\n", 4096) else {
            return;
        };
        let r = fetch_with(&format!("http://LocalHost:{port}/a%20b?c=d#frag"), quick(), local);
        assert_eq!(outcome(r), Ok((204, Vec::new())));
        let expected = format!(
            "GET /a%20b?c=d HTTP/1.1\r\nHost: localhost:{port}\r\nConnection: close\r\nAccept: */*\r\nUser-Agent: clazel\r\n\r\n"
        );
        assert_eq!(rx.recv_timeout(Duration::from_secs(2)).ok(), Some(expected.into_bytes()));
    }

    #[test]
    fn framings() {
        let cases: [(&'static [u8], Outcome); 6] = [
            (b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello", Ok((200, b"hello".to_vec()))),
            (b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n0\r\n\r\n", Ok((200, b"abc".to_vec()))),
            (b"HTTP/1.1 200 OK\r\n\r\nuntil close", Ok((200, b"until close".to_vec()))),
            (b"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n", Ok((404, Vec::new()))),
            (b"HTTP/1.1 200 OK\r\nContent-Length: 9\r\n\r\nshort", Err(FetchError::Invalid)),
            (b"HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n", Err(FetchError::Unsupported)),
        ];
        for (reply, expected) in cases {
            for step in [1, 7, 4096] {
                let Some((port, _)) = serve(reply, step) else {
                    return;
                };
                let r = fetch_with(&format!("http://localhost:{port}/"), quick(), local);
                assert_eq!(outcome(r), expected, "{:?} step {step}", String::from_utf8_lossy(reply));
            }
        }
    }

    #[test]
    fn not_fetched() {
        assert_eq!(fetch_with("https://example.com/", quick(), local).map(|_| ()), Err(FetchError::NotFetched));
        assert_eq!(fetch_with("http://u:p@example.com/", quick(), local).map(|_| ()), Err(FetchError::NotFetched));
        assert_eq!(fetch_with("not a url", quick(), local).map(|_| ()), Err(FetchError::Url));
    }
}
