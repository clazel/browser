//! The kernel host shell (phase-2.md item 2.15): the I/O around the proven
//! kernel `step`. Each renderer gets a socket pair (its end is the process's
//! stdin and stdout) and a thread that reads whole frames; the id of an event
//! is the id its socket was made for, never anything in a frame. A frame over
//! `MAX_FRAME` (refused from its first 4 bytes) or a closed socket becomes
//! `RendererExited`. Outputs are carried out in order, and every frame, exit
//! and stderr (which names a failed sandbox layer) is printed. The network
//! (item 3.7) is `clazel-net`'s `Driver`.

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::Shutdown;
use std::os::{fd::OwnedFd, unix::net::UnixStream};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

use clazel_ipc::{
    frame::codec::payload_length,
    message::codec::{Msg, decode_framed},
};
use clazel_kernel::exec::real_urls::{RealFetch, step_real};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};
use clazel_net::{Driver, Op, Report, read_frames};

/// What a socket's reader thread reports; the id is the socket's.
enum Ev {
    Frame(u64, Vec<u8>),
    Gone(u64, String),
    Net(u64, Report),
}

/// The host: the kernel state and the renderers (socket and process) it runs.
pub struct Host {
    /// The kernel's state; nothing but `step_real` writes it (tests preload the jar).
    pub state: StateRecord,
    /// Test hook: every connection goes here.
    pub route: Option<std::net::SocketAddr>,
    /// The kernel's connections, on sockets (`clazel-net`).
    net: Driver<Ev>,
    /// A fixed kernel clock (seconds since 1601) for tests; `None`: wall clock.
    pub clock: Option<u64>,
    table: HashMap<u64, (UnixStream, Child)>,
    tx: Sender<Ev>,
    rx: Receiver<Ev>,
    command: Box<dyn FnMut(u64) -> Command>,
    /// Every line the host has printed.
    pub log: Vec<String>,
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
            net: Driver::new(tx.clone(), Ev::Net),
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
        let time = self.clock.unwrap_or_else(clazel_net::now_1601);
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
                } => self.net_op(conn, Op::Connect { host, port, tls }, &mut failed),
                OutputRecord::Send { conn, bytes } => {
                    self.net_op(conn, Op::Send(bytes), &mut failed);
                }
                OutputRecord::Close { conn } => self.net_op(conn, Op::Close, &mut failed),
            }
        }
        for (id, why) in dead {
            self.exit(id, why);
        }
        for conn in failed {
            self.net_report(conn, Report::Failed("write failed".to_owned()));
        }
    }

    /// Give the driver an operation of the kernel; a failure is reported to
    /// the kernel after its outputs are carried out.
    fn net_op(&mut self, conn: u64, op: Op, failed: &mut Vec<u64>) {
        let (ok, line) = self.net.apply(conn, op, self.route);
        line.into_iter().for_each(|l| self.say(l));
        if !ok {
            failed.push(conn);
        }
    }

    /// A connection reported: hand the kernel what it means, if it still
    /// wants the connection.
    fn net_report(&mut self, conn: u64, report: Report) {
        let (input, note) = self.net.accept(conn, report);
        note.into_iter().for_each(|l| self.say(l));
        if let Some(input) = input {
            self.event(EventRecord::Net { conn, input });
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
        std::thread::spawn(move || {
            let on = |frame| tx.send(Ev::Frame(id, frame)).is_ok();
            if let Some(why) = read_frames(reader, payload_length, on) {
                let _ = tx.send(Ev::Gone(id, why));
            }
        });
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
            Ok(Ev::Net(conn, report)) => {
                self.net_report(conn, report);
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
