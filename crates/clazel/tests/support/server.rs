//! An in-process HTTP/1.1 server on loopback for the process tests of
//! phase-4.md item 4.16, after the servers of Phase 3 item 3.8
//! (`clazel-net`'s tests): a `TcpListener` on 127.0.0.1, one thread per
//! connection, one request per connection (the kernel sends
//! `Connection: close`). The host's `route` test hook sends every
//! connection here, whatever its host name, so the request's `Host` field
//! says which origin was asked for.
//!
//! A reply's body is a piece repeated a number of times, written as it is
//! generated, so a 64 MiB page is never held whole by the server.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// A request the server received.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    /// The `Host` field's value.
    pub host: String,
    /// The request target.
    pub path: String,
    /// The whole head, request line and fields.
    pub head: Vec<u8>,
}

/// A reply: the status line and fields (without `Content-Length`, which
/// the server adds), and a body of `piece` repeated `times` times.
#[derive(Clone)]
pub struct Reply {
    /// The status line and fields, each ending in CR LF.
    pub head: String,
    /// The repeated piece of the body.
    pub piece: Vec<u8>,
    /// How many times it is repeated.
    pub times: usize,
}

/// The server: its address, and every request it was sent, in order.
pub struct Server {
    /// Where it listens.
    pub addr: SocketAddr,
    /// The requests so far.
    pub seen: Arc<Mutex<Vec<Request>>>,
}

/// The value of the field `name` in a request head (the first one), or
/// empty.
pub fn field(head: &[u8], name: &str) -> String {
    let text = String::from_utf8_lossy(head);
    text.lines()
        .skip(1)
        .find_map(|l| {
            let (n, v) = l.split_once(':')?;
            n.eq_ignore_ascii_case(name).then(|| v.trim().to_owned())
        })
        .unwrap_or_default()
}

/// Read one request head, up to 64 KiB, waiting at most 10 s.
fn read_head(s: &mut TcpStream) -> Vec<u8> {
    let _ = s.set_read_timeout(Some(Duration::from_secs(10)));
    let mut got = Vec::new();
    let mut buf = [0u8; 4096];
    while !got.ends_with(b"\r\n\r\n") && got.len() < 65536 {
        match s.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => got.extend_from_slice(buf.get(..n).unwrap_or_default()),
        }
    }
    got
}

/// Write `reply` to `s`, its body generated a block at a time.
fn write_reply(s: &mut TcpStream, reply: &Reply) -> std::io::Result<()> {
    let len = reply.piece.len().saturating_mul(reply.times);
    s.write_all(
        format!(
            "{}Content-Length: {len}\r\nConnection: close\r\n\r\n",
            reply.head
        )
        .as_bytes(),
    )?;
    // Blocks of whole pieces, about 64 KiB each.
    let per_block = (65536usize.checked_div(reply.piece.len()).unwrap_or(1)).max(1);
    let block = reply.piece.repeat(per_block.min(reply.times));
    let mut left = reply.times;
    while left > 0 {
        let n = per_block.min(left);
        let bytes = block
            .get(..n.saturating_mul(reply.piece.len()))
            .unwrap_or_default();
        s.write_all(bytes)?;
        left = left.saturating_sub(n);
    }
    s.flush()
}

/// Start a server that answers each request with `route(request)`.
pub fn serve(route: impl Fn(&Request) -> Reply + Send + Sync + 'static) -> Server {
    let seen: Arc<Mutex<Vec<Request>>> = Arc::new(Mutex::new(Vec::new()));
    let dead = SocketAddr::from(([127, 0, 0, 1], 9));
    let Ok(listener) = TcpListener::bind("127.0.0.1:0") else {
        return Server { addr: dead, seen };
    };
    let addr = listener.local_addr().unwrap_or(dead);
    let route = Arc::new(route);
    let log = Arc::clone(&seen);
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let (route, log) = (Arc::clone(&route), Arc::clone(&log));
            std::thread::spawn(move || {
                let head = read_head(&mut stream);
                let line = String::from_utf8_lossy(&head)
                    .lines()
                    .next()
                    .map(str::to_owned);
                let path = line
                    .as_deref()
                    .and_then(|l| l.split(' ').nth(1))
                    .unwrap_or_default()
                    .to_owned();
                let request = Request {
                    host: field(&head, "host"),
                    path,
                    head,
                };
                let reply = route(&request);
                if let Ok(mut l) = log.lock() {
                    l.push(request);
                }
                let _ = write_reply(&mut stream, &reply);
            });
        }
    });
    Server { addr, seen }
}
