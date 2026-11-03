//! The connection driver (Phase 3 item 3.7): carries out what the kernel asks
//! of the network (`Connect`, `Send`, `Close`) on TCP sockets and reports what
//! happens as the transducer's inputs (`Connected`, `Bytes`, `Closed`,
//! `Error`). It decides nothing about the bytes: the kernel steps the fetch
//! transducer itself. A thread per connection resolves, connects and reads.
//!
//! - **TCP:** writes are made from the caller's thread, on a clone of the
//!   socket.
//! - **TLS** (`Connect { tls: true }`): the connection is a
//!   [`TlsConnection`], whose one state machine serves both directions, so
//!   it cannot be split into a reader and a writer. Its thread owns it: it
//!   runs the handshake (Mozilla's roots as the trust anchors, unless
//!   [`Driver::with_verifier`] gives others), reports `Connected`, waits for
//!   the request, sends it, and then reads until the end. Writes reach it
//!   over a channel. It reads only after the first write: the server says
//!   nothing before the request, so reading first would block both sides.
//!   3.6's transducer sends one request per connection, so a later write
//!   would wait until the read in progress returns.
//! - **Close:** the socket is shut down at once, for TCP and for TLS. A TLS
//!   connection the kernel closes sends no close_notify (RFC 8446 §6.1 asks
//!   for one; the thread is blocked in a read and holds the state that
//!   would seal it). The kernel closes a connection once its response is
//!   decided, or when its tab goes.
//! - Any TLS failure (a certificate that does not validate, a stream that
//!   ends without the server's close_notify) is `Error`.

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::net::{IpAddr, Shutdown, SocketAddr, TcpStream};
use std::sync::mpsc::{Receiver, Sender, TryRecvError, channel};
use std::time::Duration;

use clazel_crypto::join::exec::{ChainVerifier, mozilla};

pub use clazel_fetch::transducer::types::InputBuf;

use crate::conn::Timeouts;
use crate::tls::{TlsConnection, tls_host};

/// What a connection's thread reports.
pub enum Report {
    /// The socket is open (the driver keeps this end to write to).
    Connected(TcpStream),
    /// The TLS handshake is done; the driver keeps this end to write to.
    ConnectedTls(TlsEnd),
    /// Octets arrived.
    Bytes(Vec<u8>),
    /// The peer closed it.
    Closed,
    /// It could not be opened, or failed.
    Failed(String),
}

/// The driver's end of a TLS connection, which its thread owns.
pub struct TlsEnd {
    /// The TCP socket under it, to shut down on `Close`.
    socket: TcpStream,
    /// Writes for the thread.
    writes: Sender<Vec<u8>>,
}

/// An open connection, as the driver writes to it.
enum Open {
    Tcp(TcpStream),
    Tls(TlsEnd),
}

/// What the kernel asks of a connection.
pub enum Op {
    /// Open it to `host:port`, speaking TLS if `tls`.
    Connect {
        /// The host, as the resolver takes it.
        host: Vec<u8>,
        /// The port.
        port: u64,
        /// Whether to speak TLS.
        tls: bool,
    },
    /// Write these octets.
    Send(Vec<u8>),
    /// Close it.
    Close,
}

/// The longest a connection may be silent, and the longest to connect.
const IDLE: Duration = Duration::from_secs(30);
const CONNECT: Duration = Duration::from_secs(10);

/// The connections of one caller.
pub struct Driver<M> {
    wanted: HashSet<u64>,
    open: HashMap<u64, Open>,
    tx: Sender<M>,
    wrap: fn(u64, Report) -> M,
    verifier: fn() -> ChainVerifier<'static>,
}

impl<M: Send + 'static> Driver<M> {
    /// A driver whose threads send `wrap(conn, report)` on `tx`.
    pub fn new(tx: Sender<M>, wrap: fn(u64, Report) -> M) -> Self {
        Self::with_verifier(tx, wrap, mozilla)
    }

    /// [`Driver::new`], validating TLS certificates against the anchors of
    /// `verifier()` instead of Mozilla's (the tests use their own root).
    pub fn with_verifier(
        tx: Sender<M>,
        wrap: fn(u64, Report) -> M,
        verifier: fn() -> ChainVerifier<'static>,
    ) -> Self {
        Driver {
            wanted: HashSet::new(),
            open: HashMap::new(),
            tx,
            wrap,
            verifier,
        }
    }

    /// Carry out one operation of the kernel on `conn`: whether it worked,
    /// and the line to log, if any.
    pub fn apply(
        &mut self,
        conn: u64,
        op: Op,
        route: Option<SocketAddr>,
    ) -> (bool, Option<String>) {
        match op {
            Op::Connect { host, port, tls } => {
                self.wanted.insert(conn);
                let (tx, wrap, verifier) = (self.tx.clone(), self.wrap, self.verifier);
                let shown = String::from_utf8_lossy(&host).into_owned();
                let port = u16::try_from(port).unwrap_or(80);
                std::thread::spawn(move || {
                    let report = |r| tx.send(wrap(conn, r)).is_ok();
                    if tls {
                        run_tls(&host, port, route, verifier, report);
                    } else {
                        run(&host, port, route, report);
                    }
                });
                let over = if tls { " (TLS)" } else { "" };
                (
                    true,
                    Some(format!(
                        "network: connection {conn} to {shown}:{port}{over}"
                    )),
                )
            }
            Op::Send(bytes) => {
                let ok = match self.open.get_mut(&conn) {
                    Some(Open::Tcp(sock)) => {
                        sock.write_all(&bytes).and_then(|()| sock.flush()).is_ok()
                    }
                    // The thread writes it; a failure comes back as its report.
                    Some(Open::Tls(end)) => end.writes.send(bytes.clone()).is_ok(),
                    None => false,
                };
                let failed = if ok { "" } else { " (failed)" };
                (
                    ok,
                    Some(format!(
                        "network: connection {conn} <- {} bytes{failed}",
                        bytes.len()
                    )),
                )
            }
            Op::Close => {
                self.wanted.remove(&conn);
                let sock = self.open.remove(&conn);
                let _ = sock.as_ref().map(|s| match s {
                    Open::Tcp(s) => s.shutdown(Shutdown::Both),
                    Open::Tls(end) => end.socket.shutdown(Shutdown::Both),
                });
                (
                    true,
                    sock.map(|_| format!("network: connection {conn} closed")),
                )
            }
        }
    }

    /// A report from a connection's thread as the transducer's input, or
    /// `None` if the connection is no longer wanted. The end of a connection
    /// (closed or failed) forgets it. A failure is also a line to log.
    pub fn accept(&mut self, conn: u64, report: Report) -> (Option<InputBuf>, Option<String>) {
        if !self.wanted.contains(&conn) {
            return (None, None);
        }
        let note = match &report {
            Report::Failed(why) => Some(format!("network: connection {conn} failed: {why}")),
            _ => None,
        };
        let input = match report {
            Report::Connected(sock) => {
                self.open.insert(conn, Open::Tcp(sock));
                InputBuf::Connected
            }
            Report::ConnectedTls(end) => {
                self.open.insert(conn, Open::Tls(end));
                InputBuf::Connected
            }
            Report::Bytes(bytes) => InputBuf::Bytes(bytes),
            Report::Closed => InputBuf::Closed,
            Report::Failed(_) => InputBuf::Error,
        };
        if matches!(input, InputBuf::Closed | InputBuf::Error) {
            self.wanted.remove(&conn);
            self.open.remove(&conn);
        }
        (Some(input), note)
    }
}

/// Where to connect: `route` if the caller set one (a test hook), else the
/// resolver's addresses for `host`, at `port`.
fn target(host: &[u8], port: u16, route: Option<SocketAddr>) -> Result<(Vec<IpAddr>, u16), String> {
    match route {
        Some(addr) => Ok((vec![addr.ip()], addr.port())),
        None => crate::resolve(host)
            .map(|addrs| (addrs, port))
            .map_err(|e| e.to_string()),
    }
}

/// A TLS connection's thread: connect and run the handshake, report, send
/// the request when it comes, then read until the end (see the module
/// documentation).
fn run_tls(
    host: &[u8],
    port: u16,
    route: Option<SocketAddr>,
    verifier: fn() -> ChainVerifier<'static>,
    report: impl Fn(Report) -> bool,
) {
    let opened = target(host, port, route).and_then(|(addrs, port)| {
        let name = tls_host(host).ok_or_else(|| "not a host name TLS takes".to_owned())?;
        let unix = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_secs());
        let timeouts = Timeouts {
            connect: CONNECT,
            idle: IDLE,
        };
        let tls = TlsConnection::open(&addrs, port, timeouts, name, unix, verifier())
            .map_err(|e| e.to_string())?;
        let socket = tls.socket().map_err(|e| e.to_string())?;
        Ok((tls, socket))
    });
    let (mut tls, socket) = match opened {
        Ok(pair) => pair,
        Err(why) => {
            report(Report::Failed(why));
            return;
        }
    };
    let (writes, pending) = channel::<Vec<u8>>();
    if !report(Report::ConnectedTls(TlsEnd { socket, writes })) {
        return;
    }
    // The request first: nothing is read before it is sent. The driver
    // dropping its end (a `Close` before any write) ends the thread.
    let Ok(first) = pending.recv() else {
        return;
    };
    if let Err(e) = tls.send(&first) {
        report(Report::Failed(e.to_string()));
        return;
    }
    let mut buf = vec![0u8; 16 * 1024];
    loop {
        if !send_pending(&mut tls, &pending, &report) {
            return;
        }
        match tls.read(&mut buf) {
            Ok(Some(n)) => {
                if !report(Report::Bytes(buf.get(..n).unwrap_or_default().to_vec())) {
                    return;
                }
            }
            Ok(None) => {
                report(Report::Closed);
                return;
            }
            Err(e) => {
                report(Report::Failed(e.to_string()));
                return;
            }
        }
    }
}

/// Send the writes that are waiting, without blocking: whether the thread
/// goes on (no write failed).
fn send_pending(
    tls: &mut TlsConnection<'_>,
    pending: &Receiver<Vec<u8>>,
    report: &impl Fn(Report) -> bool,
) -> bool {
    loop {
        match pending.try_recv() {
            Ok(bytes) => {
                if let Err(e) = tls.send(&bytes) {
                    report(Report::Failed(e.to_string()));
                    return false;
                }
            }
            Err(TryRecvError::Empty | TryRecvError::Disconnected) => return true,
        }
    }
}

/// A TCP connection's thread: connect, report, then read until the end.
fn run(host: &[u8], port: u16, route: Option<SocketAddr>, report: impl Fn(Report) -> bool) {
    let sock = target(host, port, route)
        .and_then(|(addrs, port)| crate::connect(&addrs, port, CONNECT).map_err(|e| e.to_string()));
    let (sock, mut reader) = match sock.and_then(|s| {
        s.set_read_timeout(Some(IDLE)).map_err(|e| e.to_string())?;
        s.set_write_timeout(Some(IDLE)).map_err(|e| e.to_string())?;
        let reader = s.try_clone().map_err(|e| e.to_string())?;
        Ok((s, reader))
    }) {
        Ok(pair) => pair,
        Err(why) => {
            report(Report::Failed(why));
            return;
        }
    };
    if !report(Report::Connected(sock)) {
        return;
    }
    let mut buf = vec![0u8; 16 * 1024];
    loop {
        match reader.read(&mut buf) {
            Ok(0) => {
                report(Report::Closed);
                return;
            }
            Ok(n) => {
                if !report(Report::Bytes(buf.get(..n).unwrap_or_default().to_vec())) {
                    return;
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => {
                report(Report::Failed(e.to_string()));
                return;
            }
        }
    }
}
