//! TCP: connect to a list of addresses, send a request, carry the response.

use crate::error::{NetError, Stage, from_io};
use std::io::{self, Read, Write};
use std::net::{IpAddr, SocketAddr, TcpStream};
use std::time::Duration;

/// Size of the read buffer, and so the largest chunk given to the callback.
const READ_BUF: usize = 16 * 1024;

/// What the caller wants after a chunk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flow {
    /// Read more.
    Continue,
    /// Stop reading and close the connection.
    Stop,
}

/// How [`run`] ended without an error. The caller's parser needs the
/// difference: only a close tells it the message is over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Finish {
    /// The peer closed the connection (end of stream).
    Closed,
    /// The callback returned [`Flow::Stop`].
    Stopped,
}

/// Timeouts for [`run_with`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Timeouts {
    /// For each connection attempt.
    pub connect: Duration,
    /// For each read and write: the longest the peer may be silent.
    pub idle: Duration,
}

impl Default for Timeouts {
    fn default() -> Self {
        Timeouts {
            connect: Duration::from_secs(10),
            idle: Duration::from_secs(30),
        }
    }
}

/// Connect to `addrs` in order, each with a timeout; the first that
/// accepts wins. There is no happy-eyeballs racing.
pub fn connect(addrs: &[IpAddr], port: u16, timeout: Duration) -> Result<TcpStream, NetError> {
    let mut last = NetError::Connect(io::ErrorKind::InvalidInput);
    for ip in addrs {
        match TcpStream::connect_timeout(&SocketAddr::new(*ip, port), timeout) {
            Ok(s) => return Ok(s),
            Err(e) => {
                last = match from_io(&e, Stage::Connect) {
                    NetError::Io(k) => NetError::Connect(k),
                    other => other,
                };
            }
        }
    }
    Err(last)
}

/// [`run_with`] with default timeouts (10 s to connect, 30 s idle).
pub fn run(
    addrs: &[IpAddr],
    port: u16,
    request: &[u8],
    on_bytes: impl FnMut(&[u8]) -> Flow,
) -> Result<Finish, NetError> {
    run_with(addrs, port, request, Timeouts::default(), on_bytes)
}

/// Connect, send `request` in full, then give every chunk read (at most 16
/// KiB, never empty) to `on_bytes` until it returns [`Flow::Stop`]
/// ([`Finish::Stopped`]) or the peer closes ([`Finish::Closed`]). The bytes
/// are not inspected.
///
/// If the peer closes or resets while the request is still being written,
/// whatever it sent before is still delivered; the write error is returned
/// only if nothing arrived.
pub fn run_with(
    addrs: &[IpAddr],
    port: u16,
    request: &[u8],
    timeouts: Timeouts,
    mut on_bytes: impl FnMut(&[u8]) -> Flow,
) -> Result<Finish, NetError> {
    let mut stream = connect(addrs, port, timeouts.connect)?;
    let io_err = |e: io::Error| NetError::Io(e.kind());
    stream
        .set_read_timeout(Some(timeouts.idle))
        .map_err(io_err)?;
    stream
        .set_write_timeout(Some(timeouts.idle))
        .map_err(io_err)?;
    stream.set_nodelay(true).map_err(io_err)?;

    let write_error = match stream.write_all(request).and_then(|()| stream.flush()) {
        Ok(()) => None,
        Err(e) => match e.kind() {
            io::ErrorKind::BrokenPipe | io::ErrorKind::ConnectionReset => {
                Some(NetError::Io(e.kind()))
            }
            _ => return Err(from_io(&e, Stage::Write)),
        },
    };

    let mut buf = vec![0u8; READ_BUF];
    let mut delivered = false;
    loop {
        match stream.read(&mut buf) {
            Ok(0) => {
                return match (write_error, delivered) {
                    (Some(e), false) => Err(e),
                    _ => Ok(Finish::Closed),
                };
            }
            Ok(n) => {
                delivered = true;
                let chunk = buf.get(..n).unwrap_or(&[]);
                if on_bytes(chunk) == Flow::Stop {
                    return Ok(Finish::Stopped);
                }
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => {
                if delivered && write_error.is_some() && e.kind() == io::ErrorKind::ConnectionReset
                {
                    return Ok(Finish::Closed);
                }
                return Err(from_io(&e, Stage::Read));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{Ipv4Addr, TcpListener};
    use std::thread::{self, JoinHandle};
    use std::time::Instant;

    type T = Result<(), Box<dyn std::error::Error>>;
    type Server = Result<(u16, JoinHandle<io::Result<()>>), Box<dyn std::error::Error>>;

    const LOCAL: [IpAddr; 1] = [IpAddr::V4(Ipv4Addr::LOCALHOST)];

    fn short() -> Timeouts {
        Timeouts {
            connect: Duration::from_millis(500),
            idle: Duration::from_millis(200),
        }
    }

    /// A server that accepts one connection and runs `f` on it.
    fn server(f: impl FnOnce(TcpStream) -> io::Result<()> + Send + 'static) -> Server {
        let l = TcpListener::bind("127.0.0.1:0")?;
        let port = l.local_addr()?.port();
        let h = thread::spawn(move || {
            let (s, _) = l.accept()?;
            f(s)
        });
        Ok((port, h))
    }

    #[test]
    fn the_request_is_sent_in_full_and_the_reply_is_carried_until_close() -> T {
        let request = vec![7u8; 100_000];
        let want = request.clone();
        let (port, h) = server(move |mut s| {
            let mut got = vec![0u8; want.len()];
            s.read_exact(&mut got)?;
            assert_eq!(got, want);
            // The reply, in pieces, then close.
            s.write_all(b"hello ")?;
            s.flush()?;
            thread::sleep(Duration::from_millis(20));
            s.write_all(b"world")
        })?;
        let mut body = Vec::new();
        let mut chunks = 0usize;
        let done = run_with(&LOCAL, port, &request, short(), |c| {
            assert!(!c.is_empty() && c.len() <= READ_BUF);
            chunks = chunks.saturating_add(1);
            body.extend_from_slice(c);
            Flow::Continue
        });
        assert_eq!(done, Ok(Finish::Closed));
        assert_eq!(body, b"hello world");
        assert!(chunks >= 1);
        h.join().map_err(|_| "server panicked")??;
        Ok(())
    }

    #[test]
    fn a_large_reply_arrives_in_bounded_chunks() -> T {
        let (port, h) = server(|mut s| s.write_all(&vec![1u8; 100_000]))?;
        let mut total = 0usize;
        let done = run_with(&LOCAL, port, b"", short(), |c| {
            assert!(c.len() <= READ_BUF);
            total = total.saturating_add(c.len());
            Flow::Continue
        });
        assert_eq!(done, Ok(Finish::Closed));
        assert_eq!(total, 100_000);
        h.join().map_err(|_| "server panicked")??;
        Ok(())
    }

    #[test]
    fn stop_ends_a_connection_that_never_closes() -> T {
        let (port, h) = server(|mut s| {
            s.write_all(b"partial")?;
            thread::sleep(Duration::from_millis(800));
            Ok(())
        })?;
        let start = Instant::now();
        let mut seen = Vec::new();
        let done = run_with(
            &LOCAL,
            port,
            b"GET",
            Timeouts {
                connect: Duration::from_millis(500),
                idle: Duration::from_secs(5),
            },
            |c| {
                seen.extend_from_slice(c);
                Flow::Stop
            },
        );
        assert_eq!(done, Ok(Finish::Stopped));
        assert_eq!(seen, b"partial");
        assert!(start.elapsed() < Duration::from_millis(600));
        h.join().map_err(|_| "server panicked")??;
        Ok(())
    }

    #[test]
    fn a_silent_server_times_out() -> T {
        let (port, h) = server(|_s| {
            thread::sleep(Duration::from_millis(600));
            Ok(())
        })?;
        let start = Instant::now();
        let done = run_with(&LOCAL, port, b"x", short(), |_| Flow::Continue);
        assert_eq!(done, Err(NetError::Timeout(Stage::Read)));
        assert!(start.elapsed() < Duration::from_millis(550));
        h.join().map_err(|_| "server panicked")??;
        Ok(())
    }

    #[test]
    fn a_refused_connection_is_a_connect_error() -> T {
        let port = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let done = run_with(&LOCAL, port, b"x", short(), |_| Flow::Continue);
        assert_eq!(
            done,
            Err(NetError::Connect(io::ErrorKind::ConnectionRefused))
        );
        assert_eq!(
            run_with(&[], port, b"x", short(), |_| Flow::Continue),
            Err(NetError::Connect(io::ErrorKind::InvalidInput))
        );
        Ok(())
    }

    #[test]
    fn addresses_are_tried_in_order() -> T {
        let dead = {
            let l = TcpListener::bind("127.0.0.1:0")?;
            l.local_addr()?.port()
        };
        let (port, h) = server(|mut s| s.write_all(b"ok"))?;
        // Same loopback address, so only the port differs: try `connect`
        // directly with the dead port first, then the live one.
        assert!(connect(&LOCAL, dead, Duration::from_millis(200)).is_err());
        let mut got = Vec::new();
        let done = run_with(&LOCAL, port, b"", short(), |c| {
            got.extend_from_slice(c);
            Flow::Continue
        });
        assert_eq!(done, Ok(Finish::Closed));
        assert_eq!(got, b"ok");
        h.join().map_err(|_| "server panicked")??;
        Ok(())
    }
}
