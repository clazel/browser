//! The connection driver (Phase 3 item 3.7): carries out what the kernel asks
//! of the network (`Connect`, `Send`, `Close`) on TCP sockets and reports what
//! happens as the transducer's inputs (`Connected`, `Bytes`, `Closed`,
//! `Error`). It decides nothing about the bytes: the kernel steps the fetch
//! transducer itself. A thread per connection resolves, connects and reads;
//! writes are made from the caller's thread. TLS is not carried out: a
//! connection that asks for it fails.

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::net::{IpAddr, Shutdown, SocketAddr, TcpStream};
use std::sync::mpsc::Sender;
use std::time::Duration;

pub use clazel_fetch::transducer::types::InputBuf;

/// What a connection's thread reports.
pub enum Report {
    /// The socket is open (the driver keeps this end to write to).
    Connected(TcpStream),
    /// Octets arrived.
    Bytes(Vec<u8>),
    /// The peer closed it.
    Closed,
    /// It could not be opened, or failed.
    Failed(String),
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
    open: HashMap<u64, TcpStream>,
    tx: Sender<M>,
    wrap: fn(u64, Report) -> M,
}

impl<M: Send + 'static> Driver<M> {
    /// A driver whose threads send `wrap(conn, report)` on `tx`.
    pub fn new(tx: Sender<M>, wrap: fn(u64, Report) -> M) -> Self {
        Driver {
            wanted: HashSet::new(),
            open: HashMap::new(),
            tx,
            wrap,
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
                let (tx, wrap) = (self.tx.clone(), self.wrap);
                let shown = String::from_utf8_lossy(&host).into_owned();
                let port = u16::try_from(port).unwrap_or(80);
                std::thread::spawn(move || {
                    run(&host, port, tls, route, |r| tx.send(wrap(conn, r)).is_ok());
                });
                (
                    true,
                    Some(format!("network: connection {conn} to {shown}:{port}")),
                )
            }
            Op::Send(bytes) => {
                let ok = match self.open.get_mut(&conn) {
                    Some(sock) => sock.write_all(&bytes).and_then(|()| sock.flush()).is_ok(),
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
                let _ = sock.as_ref().map(|s| s.shutdown(Shutdown::Both));
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
                self.open.insert(conn, sock);
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

/// A connection's thread: connect, report, then read until the end.
fn run(
    host: &[u8],
    port: u16,
    tls: bool,
    route: Option<SocketAddr>,
    report: impl Fn(Report) -> bool,
) {
    if tls {
        report(Report::Failed("TLS is not carried out".to_owned()));
        return;
    }
    let target: Result<(Vec<IpAddr>, u16), String> = match route {
        Some(addr) => Ok((vec![addr.ip()], addr.port())),
        None => crate::resolve(host)
            .map(|addrs| (addrs, port))
            .map_err(|e| e.to_string()),
    };
    let sock = target
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
