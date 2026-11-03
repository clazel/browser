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
//! - **Close:** a TCP socket is shut down at once. A TLS connection sends
//!   close_notify first (RFC 8446 §6.1: "Each party MUST send a
//!   "close_notify" alert before closing its write side of the
//!   connection"). The thread cannot seal it then: it is blocked in a read,
//!   and on Windows shutting down only the read side does not wake that
//!   read. So the thread seals close_notify as soon as it has sent the
//!   request (the client sends nothing after it; the connection goes on
//!   reading, `Closing`) and leaves the record with the driver, unsent. A
//!   `Close` writes it and then shuts the socket down, which ends the read;
//!   if the server ends first, the thread writes it. A `Close` before the
//!   request was sent stops the thread before it sends anything, and it
//!   closes with close_notify itself.
//! - Any TLS failure (a certificate that does not validate, a stream that
//!   ends without the server's close_notify) is `Error`.

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::net::{IpAddr, Shutdown, SocketAddr, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Sender, channel};
use std::sync::{Arc, Mutex};
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
    /// The TCP socket under it: `Close` writes close_notify on it and shuts
    /// it down.
    socket: TcpStream,
    /// Writes for the thread.
    writes: Sender<Vec<u8>>,
    /// Set by `Close`: the kernel closed the connection.
    closing: Arc<AtomicBool>,
    /// Our close_notify, sealed by the thread once the request is sent and
    /// not yet written (see the module docs). Whoever closes first takes it.
    goodbye: Goodbye,
}

/// The sealed close_notify of a TLS connection, shared by the driver and
/// the connection's thread. Its lock also orders a `Close` against the
/// thread's first write.
type Goodbye = Arc<Mutex<Option<Vec<u8>>>>;

/// Take the sealed close_notify out of `goodbye`, if it is there.
fn take(goodbye: &Goodbye) -> Option<Vec<u8>> {
    goodbye.lock().ok().and_then(|mut g| g.take())
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
                    // The thread writes the request; a failure comes back as
                    // its report. Once it has sealed close_notify after the
                    // request, a second write cannot be sent: it fails here.
                    Some(Open::Tls(end)) => {
                        let sealed = end.goodbye.lock().map_or(true, |g| g.is_some());
                        !sealed && end.writes.send(bytes.clone()).is_ok()
                    }
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
                match &sock {
                    Some(Open::Tcp(s)) => {
                        let _ = s.shutdown(Shutdown::Both);
                    }
                    Some(Open::Tls(end)) => close_tls(end),
                    None => {}
                }
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
    let closing = Arc::new(AtomicBool::new(false));
    let goodbye: Goodbye = Arc::new(Mutex::new(None));
    let end = TlsEnd {
        socket,
        writes,
        closing: Arc::clone(&closing),
        goodbye: Arc::clone(&goodbye),
    };
    // A driver that no longer wants the connection drops the end at once.
    if !report(Report::ConnectedTls(end)) {
        let _ = tls.close();
        return;
    }
    // The request first: nothing is read before it is sent. The driver
    // dropping its end (a `Close` before any write) ends the thread.
    let Ok(first) = pending.recv() else {
        let _ = tls.close();
        return;
    };
    {
        // Held across the write and the seal, so that a `Close` either
        // comes first (and nothing is sent but close_notify) or finds the
        // sealed record.
        let Ok(mut sealed) = goodbye.lock() else {
            return;
        };
        if closing.load(Ordering::SeqCst) {
            drop(sealed);
            let _ = tls.close();
            return;
        }
        if let Err(e) = tls.send(&first) {
            drop(sealed);
            report(Report::Failed(e.to_string()));
            return;
        }
        *sealed = Some(tls.seal_close());
    }
    let mut buf = vec![0u8; 16 * 1024];
    loop {
        match tls.read(&mut buf) {
            Ok(Some(n)) => {
                if !report(Report::Bytes(buf.get(..n).unwrap_or_default().to_vec())) {
                    break;
                }
            }
            Ok(None) => {
                report(Report::Closed);
                break;
            }
            // After a `Close` this is the shutdown, and the driver drops it.
            Err(e) => {
                report(Report::Failed(e.to_string()));
                break;
            }
        }
    }
    // The server ended first (or the driver went away): our close_notify,
    // unless a `Close` already wrote it.
    if let Some(record) = take(&goodbye) {
        let _ = tls.send_sealed(&record);
    }
}

/// `Close` on a TLS connection: write the close_notify its thread sealed,
/// then shut the socket down, which ends the thread's read. If the thread
/// has not sent the request yet, it sees `closing` and closes by itself.
fn close_tls(end: &TlsEnd) {
    end.closing.store(true, Ordering::SeqCst);
    let Ok(mut sealed) = end.goodbye.lock() else {
        return;
    };
    if let Some(record) = sealed.take() {
        let mut socket = &end.socket;
        let _ = socket.write_all(&record).and_then(|()| socket.flush());
        let _ = end.socket.shutdown(Shutdown::Both);
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
