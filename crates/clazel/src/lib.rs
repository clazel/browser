//! The kernel host shell (phase-2.md item 2.15): the I/O around the proven
//! kernel `step`. Each renderer gets a socket pair (its end is the process's
//! stdin and stdout) and a thread that reads whole frames; the id of an event
//! is the id its socket was made for, never anything in a frame. A frame over
//! `MAX_FRAME` (refused from its first 4 bytes) or a closed socket becomes
//! `RendererExited`. Outputs are carried out in order, and every frame, exit
//! and stderr (which names a failed sandbox layer) is printed.
//!
//! The network (phase-3.md item 3.7) is the same kind of thing: the kernel
//! asks for connections (`Connect`), writes (`Send`) and closes (`Close`), and
//! the shell carries them out on TCP sockets with `clazel-net` (its resolver
//! and its connect) and reports what happened as `Net` events (connected,
//! bytes, closed, failed). It decides nothing about the bytes: the kernel steps
//! the fetch transducer itself. A connection thread connects and then reads;
//! writes are made from the host's thread. TLS is not carried out: a
//! `Connect` with `tls` fails.

use std::collections::HashMap;
use std::collections::HashSet;
use std::io::{Read, Write};
use std::net::{IpAddr, Shutdown, SocketAddr, TcpStream};
use std::os::{fd::OwnedFd, unix::net::UnixStream};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use clazel_fetch::transducer::types::InputBuf;
use clazel_ipc::{
    frame::codec::payload_length,
    message::codec::{Msg, decode_framed},
};
use clazel_kernel::exec::real_urls::{RealFetch, step_real};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};

/// What a connection's thread reports.
enum NetEv {
    /// The socket is open (the host keeps this end to write to).
    Connected(TcpStream),
    /// Octets arrived.
    Bytes(Vec<u8>),
    /// The peer closed it.
    Closed,
    /// It could not be opened, or failed.
    Failed(String),
}

/// What a socket's reader thread reports; the id is the socket's.
enum Ev {
    Frame(u64, Vec<u8>),
    Gone(u64, String),
    Net(u64, NetEv),
}

/// The longest a connection may be silent, and the longest to connect.
const IDLE: Duration = Duration::from_secs(30);
const CONNECT: Duration = Duration::from_secs(10);

/// The host: the kernel state and the renderers (socket and process) it runs.
pub struct Host {
    /// The kernel's state. Tests preload the cookie jar (the HTTP layer that
    /// would fill it is Phase 3); nothing else writes it but `step_real`.
    pub state: StateRecord,
    /// A test hook: every connection goes to this address, whatever host and
    /// port the kernel asked for (so a test can serve a page for any name).
    pub route: Option<SocketAddr>,
    /// The connections the kernel asked for and has not closed.
    wanted: HashSet<u64>,
    /// The write end of each connection that is open.
    open: HashMap<u64, TcpStream>,
    /// A fixed kernel clock (seconds since 1601) for tests; `None`: wall clock.
    pub clock: Option<u64>,
    table: HashMap<u64, (UnixStream, Child)>,
    tx: Sender<Ev>,
    rx: Receiver<Ev>,
    command: Box<dyn FnMut(u64) -> Command>,
    /// Every line the host has printed.
    pub log: Vec<String>,
}

/// Read whole frames until the socket closes or announces too much.
fn read_frames(id: u64, mut sock: UnixStream, tx: Sender<Ev>) {
    let why = loop {
        let mut frame = vec![0u8; 4];
        if sock.read_exact(&mut frame).is_err() {
            break "closed its socket".to_owned();
        }
        let Some(len) = payload_length(&frame) else {
            let n = frame.iter().fold(0u64, |n, b| (n << 8) | u64::from(*b));
            break format!("sent a frame over MAX_FRAME (announced {n} bytes)");
        };
        let mut payload = vec![0u8; len];
        if sock.read_exact(&mut payload).is_err() {
            break "closed its socket inside a frame".to_owned();
        }
        frame.extend_from_slice(&payload);
        if tx.send(Ev::Frame(id, frame)).is_err() {
            return;
        }
    };
    let _ = tx.send(Ev::Gone(id, why));
}

/// A connection's thread: connect, report, then read until the end.
fn net_thread(
    conn: u64,
    host: &[u8],
    port: u16,
    tls: bool,
    route: Option<SocketAddr>,
    tx: &Sender<Ev>,
) {
    let report = |ev: NetEv| tx.send(Ev::Net(conn, ev)).is_ok();
    if tls {
        report(NetEv::Failed("TLS is not carried out".to_owned()));
        return;
    }
    let target: Result<(Vec<IpAddr>, u16), String> = match route {
        Some(addr) => Ok((vec![addr.ip()], addr.port())),
        None => clazel_net::resolve(host)
            .map(|addrs| (addrs, port))
            .map_err(|e| e.to_string()),
    };
    let sock = target.and_then(|(addrs, port)| {
        clazel_net::connect(&addrs, port, CONNECT).map_err(|e| e.to_string())
    });
    let (sock, mut reader) = match sock.and_then(|s| {
        s.set_read_timeout(Some(IDLE)).map_err(|e| e.to_string())?;
        s.set_write_timeout(Some(IDLE)).map_err(|e| e.to_string())?;
        let reader = s.try_clone().map_err(|e| e.to_string())?;
        Ok((s, reader))
    }) {
        Ok(pair) => pair,
        Err(why) => {
            report(NetEv::Failed(why));
            return;
        }
    };
    if !report(NetEv::Connected(sock)) {
        return;
    }
    let mut buf = vec![0u8; 16 * 1024];
    loop {
        match reader.read(&mut buf) {
            Ok(0) => {
                report(NetEv::Closed);
                return;
            }
            Ok(n) => {
                if !report(NetEv::Bytes(buf.get(..n).unwrap_or_default().to_vec())) {
                    return;
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => {
                report(NetEv::Failed(e.to_string()));
                return;
            }
        }
    }
}

/// Seconds since 1601-01-01, the kernel's clock (far below its upper bound).
fn now() -> u64 {
    let unix = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    unix.saturating_add(11_644_473_600)
}

fn deadline(d: Duration) -> Instant {
    Instant::now().checked_add(d).unwrap_or_else(Instant::now)
}

/// A frame as the call or answer it carries.
fn describe(frame: &[u8]) -> String {
    let q = |b: &[u8]| format!("{:?}", String::from_utf8_lossy(b));
    match decode_framed(frame) {
        None => format!("undecodable frame of {} bytes", frame.len()),
        Some(Msg::CookieGet) => "document.cookie".to_owned(),
        Some(Msg::CookieSet { cookie_string }) => {
            format!("document.cookie = {}", q(&cookie_string))
        }
        Some(Msg::StorageGetItem { key }) => format!("localStorage.getItem({})", q(&key)),
        Some(Msg::StorageSetItem { key, value }) => {
            format!("localStorage.setItem({}, {})", q(&key), q(&value))
        }
        Some(Msg::StorageRemoveItem { key }) => format!("localStorage.removeItem({})", q(&key)),
        Some(Msg::Commit { url, script }) => {
            format!("commit {} and a script of {} bytes", q(&url), script.len())
        }
        Some(Msg::CookieValue { cookie_string }) => format!("result {}", q(&cookie_string)),
        Some(Msg::StorageValue { value }) => {
            format!("result {}", value.map_or("null".to_owned(), |v| q(&v)))
        }
        Some(other) => format!("{other:?}"),
    }
}

impl Host {
    /// A host whose renderers are started with `command(id)` (the host sets
    /// their stdio).
    pub fn new(command: impl FnMut(u64) -> Command + 'static) -> Host {
        let (tx, rx) = channel();
        Host {
            state: init_record::<RealFetch>(),
            route: None,
            wanted: HashSet::new(),
            open: HashMap::new(),
            clock: None,
            table: HashMap::new(),
            tx,
            rx,
            command: Box::new(command),
            log: Vec::new(),
        }
    }

    /// Live renderers.
    pub fn live(&self) -> usize {
        self.table.len()
    }

    fn say(&mut self, line: String) {
        println!("{line}");
        self.log.push(line);
    }

    /// The kernel's step, unless its ids are used up (`step_requires`).
    fn step(&mut self, e: EventRecord) -> Vec<OutputRecord> {
        // `step_requires`: room for one more renderer id and for the 21
        // connection ids a step may use.
        if self.state.next_id == u64::MAX || self.state.next_conn > u64::MAX.saturating_sub(21) {
            self.say("kernel ids exhausted; event dropped".to_owned());
            return Vec::new();
        }
        let (s, outputs) = step_real(
            std::mem::replace(&mut self.state, init_record::<RealFetch>()),
            &e,
        );
        self.state = s;
        outputs
    }

    /// Give the kernel an event, after a `Tick`, and carry out its outputs.
    pub fn event(&mut self, e: EventRecord) {
        let time = self.clock.unwrap_or_else(now);
        self.step(EventRecord::Tick { time });
        let mut dead = Vec::new();
        let mut failed = Vec::new();
        for output in self.step(e) {
            match output {
                OutputRecord::Spawn { id } => {
                    if let Err(e) = self.spawn(id) {
                        self.say(format!("renderer {id}: cannot start: {e}"));
                        dead.push((id, "cannot start"));
                    }
                }
                OutputRecord::ToRenderer { id, bytes } => {
                    if !self.send(id, &bytes) {
                        dead.push((id, "cannot write"));
                    }
                }
                OutputRecord::Kill { id } => self.reap(id, "killed by the kernel", Duration::ZERO),
                OutputRecord::Connect {
                    conn,
                    host,
                    port,
                    tls,
                } => self.connect(conn, &host, port, tls),
                OutputRecord::Send { conn, bytes } => {
                    if !self.write(conn, &bytes) {
                        failed.push(conn);
                    }
                }
                OutputRecord::Close { conn } => self.close(conn),
            }
        }
        for (id, why) in dead {
            self.exit(id, why);
        }
        for conn in failed {
            self.net_event(conn, InputBuf::Error);
        }
    }

    /// Report on a connection to the kernel, if it is still wanted.
    fn net_event(&mut self, conn: u64, input: InputBuf) {
        if self.wanted.contains(&conn) {
            self.event(EventRecord::Net { conn, input });
        }
    }

    /// Start connecting for the kernel: a thread resolves, connects, reports
    /// `Connected`, then reads until the peer closes.
    fn connect(&mut self, conn: u64, host: &[u8], port: u64, tls: bool) {
        self.wanted.insert(conn);
        let shown = String::from_utf8_lossy(host).into_owned();
        self.say(format!("network: connection {conn} to {shown}:{port}"));
        let (tx, route, host) = (self.tx.clone(), self.route, host.to_vec());
        let port = u16::try_from(port).unwrap_or(80);
        std::thread::spawn(move || net_thread(conn, &host, port, tls, route, &tx));
    }

    /// Write the kernel's octets to a connection; false if that failed.
    fn write(&mut self, conn: u64, bytes: &[u8]) -> bool {
        let Some(sock) = self.open.get_mut(&conn) else {
            return false;
        };
        let ok = sock.write_all(bytes).and_then(|()| sock.flush()).is_ok();
        self.say(format!(
            "network: connection {conn} <- {} bytes{}",
            bytes.len(),
            if ok { "" } else { " (failed)" }
        ));
        ok
    }

    /// The kernel closes a connection.
    fn close(&mut self, conn: u64) {
        self.wanted.remove(&conn);
        if let Some(sock) = self.open.remove(&conn) {
            let _ = sock.shutdown(Shutdown::Both);
            self.say(format!("network: connection {conn} closed"));
        }
    }

    /// The user opens a tab at `url`; the script's format is `clazel-renderer`'s.
    pub fn open_tab(&mut self, url: &str, script: &str) {
        let (url, script) = (
            url.chars().map(u32::from).collect(),
            script.as_bytes().to_vec(),
        );
        self.event(EventRecord::OpenTab { url, script });
    }

    /// The user navigates tab `tab` to `url`: the kernel asks for the page,
    /// and the document is what the network serves (its body is the script).
    pub fn navigate_tab(&mut self, tab: u64, url: &str) {
        let url = url.chars().map(u32::from).collect();
        self.event(EventRecord::NavigateTab { tab, url });
    }

    fn spawn(&mut self, id: u64) -> std::io::Result<()> {
        let (host_end, child_end) = UnixStream::pair()?;
        host_end.set_write_timeout(Some(Duration::from_secs(5)))?;
        let reader = host_end.try_clone()?;
        let stdin: OwnedFd = child_end.into();
        let stdout = stdin.try_clone()?;
        let child = (self.command)(id)
            .stdin(stdin)
            .stdout(stdout)
            .stderr(Stdio::piped())
            .spawn()?;
        let tx = self.tx.clone();
        std::thread::spawn(move || read_frames(id, reader, tx));
        self.table.insert(id, (host_end, child));
        Ok(())
    }

    /// Write a frame to a renderer; false if its socket failed.
    fn send(&mut self, id: u64, frame: &[u8]) -> bool {
        let Some((sock, _)) = self.table.get_mut(&id) else {
            return true;
        };
        let ok = sock.write_all(frame).is_ok();
        self.say(format!("renderer {id} <- {}", describe(frame)));
        ok
    }

    /// Close the socket, wait up to `grace` for the process to exit on its
    /// own, then kill it; report how it ended and what it wrote to stderr.
    fn reap(&mut self, id: u64, why: &str, grace: Duration) {
        let Some((sock, mut child)) = self.table.remove(&id) else {
            return;
        };
        let _ = sock.shutdown(Shutdown::Both);
        let end = deadline(grace);
        while matches!(child.try_wait(), Ok(None)) && Instant::now() < end {
            std::thread::sleep(Duration::from_millis(10));
        }
        let _ = child.kill();
        let status = child
            .wait()
            .map_or_else(|e| e.to_string(), |s| s.to_string());
        let mut stderr = String::new();
        if let Some(mut e) = child.stderr.take() {
            let _ = e.read_to_string(&mut stderr);
        }
        let note = Some(stderr.trim())
            .filter(|s| !s.is_empty())
            .map_or(String::new(), |s| format!("; stderr: {s}"));
        self.say(format!("renderer {id} exited: {why}; {status}{note}"));
    }

    /// A renderer is gone (or never started): tell the kernel.
    fn exit(&mut self, id: u64, why: &str) {
        self.reap(id, why, Duration::from_secs(1));
        self.event(EventRecord::RendererExited { id });
    }

    /// Handle one thing a renderer's socket reported, waiting up to `wait`.
    /// What a renderer the host no longer has sends is dropped.
    pub fn pump(&mut self, wait: Duration) -> bool {
        match self.rx.recv_timeout(wait) {
            Ok(Ev::Frame(id, bytes)) if self.table.contains_key(&id) => {
                self.say(format!("renderer {id} -> {}", describe(&bytes)));
                self.event(EventRecord::FromRenderer { id, bytes });
                true
            }
            Ok(Ev::Gone(id, why)) if self.table.contains_key(&id) => {
                self.exit(id, &why);
                true
            }
            Ok(Ev::Net(conn, ev)) => {
                let input = match ev {
                    NetEv::Connected(sock) => {
                        if self.wanted.contains(&conn) {
                            self.open.insert(conn, sock);
                        }
                        InputBuf::Connected
                    }
                    NetEv::Bytes(bytes) => InputBuf::Bytes(bytes),
                    NetEv::Closed => InputBuf::Closed,
                    NetEv::Failed(why) => {
                        self.say(format!("network: connection {conn} failed: {why}"));
                        InputBuf::Error
                    }
                };
                // The peer closing or a failure ends the connection.
                if matches!(input, InputBuf::Closed | InputBuf::Error) {
                    self.net_event(conn, input);
                    self.wanted.remove(&conn);
                    self.open.remove(&conn);
                } else {
                    self.net_event(conn, input);
                }
                true
            }
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// Pump until no renderer is left or `limit` passes; whether none is left.
    pub fn run(&mut self, limit: Duration) -> bool {
        let end = deadline(limit);
        while !self.table.is_empty() && Instant::now() < end {
            self.pump(Duration::from_millis(100));
        }
        self.table.is_empty()
    }
}

impl Drop for Host {
    fn drop(&mut self) {
        for id in self.table.keys().copied().collect::<Vec<_>>() {
            self.reap(id, "host shutting down", Duration::ZERO);
        }
    }
}
