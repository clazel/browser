//! Hostile servers (Phase 3 item 3.8): `fetch_with` must give an error for
//! each of these, never panic, never hang and never hold unbounded memory.
//! The server is an in-process `TcpListener` on 127.0.0.1; every case runs
//! under short timeouts, and a watchdog fails the test if the fetch has not
//! returned after a few seconds.
//!
//! Cases that currently misbehave are `#[ignore]`d with the reason; they
//! are the evidence of what the shell still gets wrong, not a claim.

use clazel_net::{FetchError, NetError, Timeouts, fetch_with};
use std::io::{Read, Write};
use std::net::{IpAddr, Ipv4Addr, TcpListener, TcpStream};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// The body limit `fetch` is expected to enforce.
const BODY_LIMIT: usize = 0x400_0000;

fn local(_: &[u8]) -> Result<Vec<IpAddr>, NetError> {
    Ok(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
}

fn short() -> Timeouts {
    Timeouts {
        connect: Duration::from_secs(1),
        idle: Duration::from_millis(400),
    }
}

/// Reads until the end of the request head, or the peer stops (or 2 s pass).
fn read_head(s: &mut TcpStream) {
    let _ = s.set_read_timeout(Some(Duration::from_secs(2)));
    let mut got = Vec::new();
    let mut buf = [0u8; 1024];
    while !got.ends_with(b"\r\n\r\n") {
        match s.read(&mut buf) {
            Ok(0) | Err(_) => return,
            Ok(n) => got.extend_from_slice(buf.get(..n).unwrap_or_default()),
        }
    }
}

/// What a fetch gave: the body length, or why not.
type Got = Result<usize, FetchError>;

/// Serves one connection with `behave`, and fetches from it. The fetch runs
/// on its own thread so that a hang fails the test instead of stalling it.
fn against(behave: impl FnOnce(TcpStream) + Send + 'static) -> Result<Got, String> {
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let server = thread::spawn(move || {
        if let Ok((s, _)) = listener.accept() {
            behave(s);
        }
    });
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let r = fetch_with(&format!("http://localhost:{port}/"), short(), local)
            .map(|resp| resp.body.len());
        let _ = tx.send(r);
    });
    let got = rx
        .recv_timeout(Duration::from_secs(20))
        .map_err(|_| "fetch did not return: hang".to_string())?;
    let _ = server.join();
    Ok(got)
}

/// A server that reads the request, sends `reply` and closes.
fn send_and_close(reply: Vec<u8>) -> impl FnOnce(TcpStream) + Send + 'static {
    move |mut s| {
        read_head(&mut s);
        let _ = s.write_all(&reply);
        let _ = s.flush();
    }
}

/// The error of a fetch that must have failed.
fn failure(r: Result<Got, String>) -> Result<FetchError, String> {
    match r? {
        Ok(n) => Err(format!("accepted, with a body of {n} octets")),
        Err(e) => Ok(e),
    }
}

/// Sends `piece` until the client closes or 4 x the body limit is out.
fn endless(s: &mut TcpStream, piece: &[u8]) {
    let mut sent = 0usize;
    while sent < BODY_LIMIT.saturating_mul(4) {
        if s.write_all(piece).is_err() {
            return;
        }
        sent = sent.saturating_add(piece.len());
    }
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn bytes_that_are_not_http() -> Result<(), String> {
    let junk: Vec<Vec<u8>> = vec![
        b"\x00\x01\x02\x03\xff\xfe garbage \x80\r\n\r\n".to_vec(),
        b"SSH-2.0-OpenSSH_9.9\r\n".to_vec(),
        b"\x16\x03\x01\x02\x00\x01\x00\x01\xfc\x03\x03".to_vec(),
        b"<html>not http</html>".to_vec(),
        vec![0xff; 5000],
    ];
    for bytes in junk {
        let r = failure(against(send_and_close(bytes.clone())))?;
        assert!(
            matches!(r, FetchError::Invalid | FetchError::Net(_)),
            "{bytes:?}: {r:?}"
        );
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_body_that_never_ends_stops_at_the_limit_or_the_timeout() -> Result<(), String> {
    // Content-Length far beyond the limit, then bytes without end.
    let r = against(|mut s| {
        read_head(&mut s);
        let _ = s.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 99999999999\r\n\r\n");
        endless(&mut s, &[b'x'; 64 * 1024]);
    })?;
    assert!(r.is_err(), "accepted a body of {r:?} octets");
    // No framing: until close, which never comes.
    let r = against(|mut s| {
        read_head(&mut s);
        let _ = s.write_all(b"HTTP/1.1 200 OK\r\n\r\n");
        endless(&mut s, &[b'x'; 64 * 1024]);
    })?;
    assert!(r.is_err(), "accepted a body of {r:?} octets");
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_chunked_body_that_never_ends_stops_at_the_limit_or_the_timeout() -> Result<(), String> {
    let r = against(|mut s| {
        read_head(&mut s);
        let _ = s.write_all(b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n");
        let mut chunk = b"10000\r\n".to_vec();
        chunk.extend(std::iter::repeat_n(b'y', 0x10000));
        chunk.extend_from_slice(b"\r\n");
        endless(&mut s, &chunk);
    })?;
    assert!(r.is_err(), "accepted a body of {r:?} octets");
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_chunk_size_of_two_to_the_64_and_one_less() -> Result<(), String> {
    for size in ["10000000000000000", "FFFFFFFFFFFFFFFF", "ffffffffffffffff1"] {
        let reply = format!(
            "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{size}\r\nabc\r\n0\r\n\r\n"
        );
        let r = failure(against(send_and_close(reply.into_bytes())))?;
        assert!(
            matches!(r, FetchError::Invalid | FetchError::Net(_)),
            "{size}: {r:?}"
        );
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_field_line_longer_than_8192_octets() -> Result<(), String> {
    for len in [8193usize, 100_000] {
        let mut reply = b"HTTP/1.1 200 OK\r\nX-Long: ".to_vec();
        reply.extend(std::iter::repeat_n(b'a', len));
        reply.extend_from_slice(b"\r\nContent-Length: 0\r\n\r\n");
        let r = failure(against(send_and_close(reply)))?;
        assert_eq!(r, FetchError::Invalid, "{len}");
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn more_than_256_field_lines() -> Result<(), String> {
    let mut reply = b"HTTP/1.1 200 OK\r\n".to_vec();
    for i in 0..300 {
        reply.extend_from_slice(format!("X-{i}: v\r\n").as_bytes());
    }
    reply.extend_from_slice(b"Content-Length: 0\r\n\r\n");
    let r = failure(against(send_and_close(reply)))?;
    assert_eq!(r, FetchError::Invalid);
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_server_that_accepts_and_closes_at_once() -> Result<(), String> {
    let r = failure(against(drop))?;
    assert!(
        matches!(r, FetchError::Invalid | FetchError::Net(_)),
        "{r:?}"
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_partial_head_and_then_close() -> Result<(), String> {
    for head in [
        &b"HTTP/1.1 200"[..],
        b"HTTP/1.1 200 OK\r\n",
        b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n",
        b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r",
    ] {
        let r = failure(against(send_and_close(head.to_vec())))?;
        assert!(
            matches!(r, FetchError::Invalid | FetchError::Net(_)),
            "{head:?}: {r:?}"
        );
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_server_that_never_sends_anything_times_out() -> Result<(), String> {
    let r = failure(against(|mut s| {
        read_head(&mut s);
        thread::sleep(Duration::from_millis(1500));
    }))?;
    assert!(matches!(r, FetchError::Net(NetError::Timeout(_))), "{r:?}");
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_head_that_stalls_part_way_times_out() -> Result<(), String> {
    let r = failure(against(|mut s| {
        read_head(&mut s);
        let _ = s.write_all(b"HTTP/1.1 200 OK\r\nContent-Le");
        let _ = s.flush();
        thread::sleep(Duration::from_millis(1500));
    }))?;
    assert!(matches!(r, FetchError::Net(NetError::Timeout(_))), "{r:?}");
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "opens sockets")]
fn a_content_length_larger_than_the_bytes_sent_then_close() -> Result<(), String> {
    for len in [
        "10",
        "4294967296",
        "18446744073709551615",
        "18446744073709551616",
    ] {
        let reply = format!("HTTP/1.1 200 OK\r\nContent-Length: {len}\r\n\r\nshort");
        let r = failure(against(send_and_close(reply.into_bytes())))?;
        assert!(
            matches!(r, FetchError::Invalid | FetchError::Net(_)),
            "{len}: {r:?}"
        );
    }
    Ok(())
}
