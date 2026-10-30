//! The kernel host shell (phase-2.md item 2.15): the I/O around the proven kernel `step`. Each
//! renderer gets a channel (a socket pair on Unix, pipes on Windows; `clazel_renderer::launch`)
//! and a thread that reads whole frames; the id of an event is the id its channel was made for,
//! never anything in a frame. A frame over `MAX_FRAME` (refused from its first 4 bytes) or a
//! closed channel becomes `RendererExited`. Outputs are carried out in order, and every frame,
//! exit and stderr (which names a failed sandbox layer) goes to stderr. The network (item 3.7) is
//! `clazel-net`'s Driver. A `Show` (item 4.12) waits in `shown` for the command loop.

use std::collections::HashMap;
use std::process::Command;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

use clazel_ipc::{
    frame::codec::payload_length,
    message::codec::{Msg, decode_framed},
};
use clazel_kernel::exec::real_urls::{RealFetch, step_real};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};
use clazel_net::{Driver, Op, Report, read_frames};
use clazel_renderer::launch::{self, Link};

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
    table: HashMap<u64, Link>,
    tx: Sender<Ev>,
    rx: Receiver<Ev>,
    command: Box<dyn FnMut(u64) -> Command>,
    /// Every line the host has printed.
    pub log: Vec<String>,
    /// The kernel's `Show` outputs not yet taken, oldest first.
    pub shown: Vec<OutputRecord>,
}

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// The first frame of one write (a document is `Commit`, `Body`s,
/// `BodyEnd`) as the call or answer it carries.
fn describe(frame: &[u8]) -> String {
    let q = |b: &[u8]| format!("{:?}", String::from_utf8_lossy(b));
    let len = frame.get(..4).and_then(payload_length);
    let first = len.and_then(|n| frame.get(..n.checked_add(4)?));
    match first.and_then(decode_framed) {
        None => format!("undecodable frame of {} bytes", frame.len()),
        Some(Msg::Commit { url, kind, .. }) => format!("commit {} (kind {kind})", q(&url)),
        Some(Msg::CookieGet) => "document.cookie".to_owned(),
        Some(Msg::CookieSet { cookie_string: c }) => format!("document.cookie = {}", q(&c)),
        Some(Msg::StorageGetItem { key }) => format!("localStorage.getItem({})", q(&key)),
        Some(Msg::StorageSetItem { key: k, value: v }) => {
            format!("localStorage.setItem({}, {})", q(&k), q(&v))
        }
        Some(Msg::StorageRemoveItem { key }) => format!("localStorage.removeItem({})", q(&key)),
        Some(Msg::CookieValue { cookie_string: c }) => format!("result {}", q(&c)),
        Some(Msg::StorageValue { value: Some(v) }) => format!("result {}", q(&v)),
        Some(Msg::StorageValue { value: None }) => "result null".to_owned(),
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
            shown: Vec::new(),
        }
    }

    /// Live renderers.
    pub fn live(&self) -> usize {
        self.table.len()
    }

    fn say(&mut self, line: String) {
        eprintln!("{line}");
        self.log.push(line);
    }

    /// The kernel's step, unless its ids are used up (`step_requires`).
    fn step(&mut self, e: EventRecord) -> Vec<OutputRecord> {
        let s = &self.state;
        if s.next_id.checked_add(2).is_none() || s.next_conn.checked_add(21).is_none() {
            self.say("kernel ids exhausted; event dropped".to_owned());
            return Vec::new();
        }
        let old = std::mem::replace(&mut self.state, init_record::<RealFetch>());
        let (s, outputs) = step_real(old, &e);
        self.state = s;
        outputs
    }

    /// Give the kernel an event, after a `Tick`, and carry out its outputs.
    pub fn event(&mut self, e: EventRecord) {
        let time = self.clock.unwrap_or_else(clazel_net::now_1601);
        self.step(EventRecord::Tick { time });
        let (mut dead, mut failed) = (Vec::new(), Vec::new());
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
                show @ OutputRecord::Show { .. } => self.shown.push(show),
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
        failed.extend((!ok).then_some(conn));
    }

    /// A connection reported: hand the kernel what it means, if it still
    /// wants the connection.
    fn net_report(&mut self, conn: u64, report: Report) {
        let (input, note) = self.net.accept(conn, report);
        note.into_iter().for_each(|l| self.say(l));
        input
            .into_iter()
            .for_each(|input| self.event(EventRecord::Net { conn, input }));
    }

    /// The user opens a tab at `url` with a script (`clazel-renderer`'s
    /// format), committed at once as a user script.
    pub fn open_tab(&mut self, url: &str, script: &str) {
        let (url, script) = (code_points(url), Some(script.as_bytes().to_vec()));
        self.event(EventRecord::OpenTab { url, script });
    }

    /// The user opens a tab at `url`, which the kernel fetches; its tab id.
    pub fn open(&mut self, url: &str) -> u64 {
        let (tab, url) = (self.state.next_id, code_points(url));
        self.event(EventRecord::OpenTab { url, script: None });
        tab
    }

    /// The user navigates tab `tab` to `url`: the kernel asks for the page,
    /// and the document is what the network serves.
    pub fn navigate_tab(&mut self, tab: u64, url: &str) {
        let url = code_points(url);
        self.event(EventRecord::NavigateTab { tab, url });
    }

    fn spawn(&mut self, id: u64) -> std::io::Result<()> {
        let (link, reader) = launch::spawn((self.command)(id))?;
        let tx = self.tx.clone();
        std::thread::spawn(move || {
            let on = |frame| tx.send(Ev::Frame(id, frame)).is_ok();
            if let Some(why) = read_frames(reader, payload_length, on) {
                let _ = tx.send(Ev::Gone(id, why));
            }
        });
        self.table.insert(id, link);
        Ok(())
    }

    /// Write a frame to a renderer; false if its socket failed.
    fn send(&mut self, id: u64, frame: &[u8]) -> bool {
        let Some(link) = self.table.get_mut(&id) else {
            return true;
        };
        let ok = link.send(frame);
        self.say(format!("renderer {id} <- {}", describe(frame)));
        ok
    }

    /// Close the socket, wait up to `grace` for the process to exit on its
    /// own, then kill it; report how it ended and what it wrote to stderr.
    fn reap(&mut self, id: u64, why: &str, grace: Duration) {
        let Some(link) = self.table.remove(&id) else {
            return;
        };
        let (status, stderr) = link.finish(grace);
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
            }
            Ok(Ev::Gone(id, why)) if self.table.contains_key(&id) => self.exit(id, &why),
            Ok(Ev::Net(conn, report)) => self.net_report(conn, report),
            Ok(_) => {}
            Err(_) => return false,
        }
        true
    }

    /// Pump until no renderer is left or `limit` passes; whether none is left.
    pub fn run(&mut self, limit: Duration) -> bool {
        let end = Instant::now()
            .checked_add(limit)
            .unwrap_or_else(Instant::now);
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
