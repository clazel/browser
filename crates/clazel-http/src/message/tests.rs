//! Unit tests of the executable framing, run natively and under Miri.

use super::body::ResponseParser;
use super::serialize::serialize_request;
use super::types::{ParseBuf, RequestBuf};
use crate::field::types::FieldLineBuf;

/// Feeds `msg` in pieces of `step` octets and returns the first decided
/// answer, or the answer at close.
fn parse_in_steps(msg: &[u8], head: bool, step: usize) -> ParseBuf {
    let mut p = ResponseParser::new(head);
    for piece in msg.chunks(step) {
        match p.feed(piece) {
            ParseBuf::Incomplete => {}
            decided => return decided,
        }
    }
    p.close()
}

fn body(r: &ParseBuf) -> Option<(u16, &[u8], &[u8])> {
    match r {
        ParseBuf::Done { response, rest } => Some((
            response.status_line.status,
            response.body.as_slice(),
            rest.as_slice(),
        )),
        _ => None,
    }
}

#[test]
fn content_length_any_split() {
    let msg = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhelloEXTRA";
    for step in 1..msg.len() + 1 {
        let r = parse_in_steps(msg, false, step);
        assert_eq!(
            body(&r).map(|(s, b, _)| (s, b)),
            Some((200, &b"hello"[..])),
            "step {step}"
        );
    }
}

#[test]
fn chunked_any_split() {
    let msg = b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n4;x=y\r\nwiki\r\n5\r\npedia\r\n0\r\nT: v\r\n\r\n";
    for step in 1..msg.len() + 1 {
        let r = parse_in_steps(msg, false, step);
        assert_eq!(
            body(&r),
            Some((200, &b"wikipedia"[..], &b""[..])),
            "step {step}"
        );
    }
}

#[test]
fn close_delimited() {
    let msg = b"HTTP/1.0 200 OK\r\nServer: x\r\n\r\nall of it";
    let r = parse_in_steps(msg, false, 3);
    assert_eq!(body(&r).map(|(_, b, _)| b), Some(&b"all of it"[..]));
}

#[test]
fn rejects() {
    for msg in [
        &b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 3\r\n\r\nabc"[..],
        b"HTTP/1.1 200 OK\r\nX : y\r\n\r\n",
        b"HTTP/1.1 200 OK\r\n X: y\r\n\r\n",
        b"HTTP/1.1 200 OK\r\nX: a\rb\r\n\r\n",
        b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nffffffffffffffffffff\r\n",
        b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nabc",
        b"garbage\r\n\r\n",
    ] {
        assert_eq!(
            parse_in_steps(msg, false, 7),
            ParseBuf::Invalid,
            "{:?}",
            String::from_utf8_lossy(msg)
        );
    }
    assert_eq!(
        parse_in_steps(
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n",
            false,
            4
        ),
        ParseBuf::Unsupported
    );
}

#[test]
fn line_limit() {
    let mut msg = b"HTTP/1.1 200 OK\r\nX: ".to_vec();
    msg.extend(std::iter::repeat_n(b'a', 9000));
    let mut p = ResponseParser::new(false);
    assert_eq!(p.feed(&msg), ParseBuf::Invalid);
}

#[test]
fn serializes() {
    let field = |n: &[u8], v: &[u8]| FieldLineBuf {
        name: n.to_vec(),
        value: v.to_vec(),
    };
    let req = RequestBuf {
        method: b"GET".to_vec(),
        target: b"/x?y=1".to_vec(),
        fields: vec![
            field(b"Host", b"example.com"),
            field(b"Connection", b"close"),
        ],
    };
    assert_eq!(
        serialize_request(&req).as_deref(),
        Some(&b"GET /x?y=1 HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"[..])
    );
    let bad = RequestBuf {
        fields: vec![field(b"X", b"a\r\nInjected: 1")],
        ..req
    };
    assert_eq!(serialize_request(&bad), None);
}

#[test]
fn request_round_trip_and_httparse() {
    use super::request_parser::parse_request_exec;
    use super::types::RequestParseBuf;
    let field = |n: &[u8], v: &[u8]| FieldLineBuf {
        name: n.to_vec(),
        value: v.to_vec(),
    };
    let reqs = [
        RequestBuf {
            method: b"GET".to_vec(),
            target: b"/x?y=1".to_vec(),
            fields: vec![field(b"Host", b"example.com"), field(b"Accept", b"")],
        },
        RequestBuf {
            method: b"OPTIONS".to_vec(),
            target: b"*".to_vec(),
            fields: vec![],
        },
        RequestBuf {
            method: b"POST".to_vec(),
            target: b"http://a.example/p%20q".to_vec(),
            fields: vec![field(b"X-A", b"1 \t 2"), field(b"x-a", b"\x80\xff")],
        },
    ];
    for req in reqs {
        let bytes = serialize_request(&req);
        assert!(bytes.is_some());
        let mut bytes = bytes.unwrap_or_default();
        bytes.extend_from_slice(b"NEXT");
        // httparse reads the same method, target and fields.
        let mut headers = [httparse::EMPTY_HEADER; 8];
        let mut theirs = httparse::Request::new(&mut headers);
        assert_eq!(
            theirs.parse(&bytes),
            Ok(httparse::Status::Complete(bytes.len() - 4))
        );
        assert_eq!(theirs.method.map(str::as_bytes), Some(&req.method[..]));
        assert_eq!(theirs.path.map(str::as_bytes), Some(&req.target[..]));
        assert_eq!(theirs.version, Some(1));
        let fields: Vec<(&[u8], &[u8])> = theirs
            .headers
            .iter()
            .map(|h| (h.name.as_bytes(), h.value))
            .collect();
        let ours: Vec<(&[u8], &[u8])> = req
            .fields
            .iter()
            .map(|f| (&f.name[..], &f.value[..]))
            .collect();
        assert_eq!(fields, ours);
        // Every proper prefix of the request is incomplete.
        for k in 0..bytes.len() - 4 {
            assert_eq!(
                parse_request_exec(bytes.get(..k).unwrap_or_default()),
                RequestParseBuf::Incomplete,
                "prefix {k}"
            );
        }
        // The proven parser gives the request back, with what follows.
        assert_eq!(
            parse_request_exec(&bytes),
            RequestParseBuf::Done {
                request: req,
                rest: b"NEXT".to_vec()
            }
        );
    }
    assert_eq!(
        parse_request_exec(b"GET /x HTTP/1.0\r\n\r\n"),
        RequestParseBuf::Invalid
    );
    assert_eq!(
        parse_request_exec(b"GET  /x HTTP/1.1\r\n\r\n"),
        RequestParseBuf::Invalid
    );
}
