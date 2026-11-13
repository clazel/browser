//! The kernel host shell (phase-2.md item 2.15): the I/O around the proven kernel `step`. Each
//! renderer gets a channel (a socket pair on Unix, pipes on Windows; `clazel_renderer::launch`)
//! and a thread that reads whole frames; the id of an event is the id its channel was made for,
//! never anything in a frame. A frame over `MAX_FRAME` (refused from its first 4 bytes) or a
//! closed channel becomes `RendererExited`. Outputs are carried out in order, and every frame,
//! exit and stderr (which names a failed sandbox layer) goes to stderr. The network (item 3.7) is
//! `clazel-net`'s Driver. A `Show` (item 4.12) or `Paint` (5.18) waits in `shown` for the loop.
//! Item 5.23: GPU processes are `launch::Gpus`, which `with_gpu` turns on; the shell routes.

use std::collections::HashMap;
use std::process::Command;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

use clazel_ipc::frame::codec::payload_length;
use clazel_kernel::exec::real_urls::{RealFetch, step_real};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};
use clazel_net::{ChainVerifier, Driver, Op, Report, read_frames};
use clazel_renderer::launch::{self, GpuReport, Gpus, Link, describe};

/// What a socket's reader thread reports; the id is the socket's (a GPU process's, its renderer's).
enum Ev {
    Frame(u64, Vec<u8>),
    Gone(u64, String),
    Net(u64, Report),
    Gpu(u64, GpuReport),
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
    gpus: Gpus<Ev>,
    /// Every line the host has printed.
    pub log: Vec<String>,
    /// The kernel's `Show` and `Paint` outputs not yet taken, oldest first.
    pub shown: Vec<OutputRecord>,
}

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
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
            gpus: Gpus::new(tx.clone(), Ev::Gpu),
            clock: None,
            table: HashMap::new(),
            tx,
            rx,
            command: Box::new(command),
            log: Vec::new(),
            shown: Vec::new(),
        }
    }

    /// Start GPU processes with `gpu(id)` (item 5.23); without, the host is in text mode.
    pub fn with_gpu(mut self, gpu: impl FnMut(u64) -> Command + 'static) -> Host {
        self.gpus.start_with(gpu);
        self
    }

    /// Test hook, like `route`: validate TLS certificates against the
    /// anchors of `verifier()` instead of Mozilla's. Call it before any
    /// connection is opened: it replaces the driver.
    pub fn trust(&mut self, verifier: fn() -> ChainVerifier<'static>) {
        self.net = Driver::with_verifier(self.tx.clone(), Ev::Net, verifier);
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
                OutputRecord::SpawnGpu { id } => {
                    self.gpus.spawn(id).unwrap_or_else(|e| self.say(e))
                }
                OutputRecord::ToGpu { id, bytes } => self.gpus.send(id, &bytes),
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
                paint @ OutputRecord::Paint { .. } => self.shown.push(paint),
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

    /// The pixels slot `slot` of renderer `id`'s GPU process holds, taken out (item 5.23).
    pub fn take_frame(&mut self, id: u64, slot: u32) -> Option<clazel_gpu::channel::SurfaceFrame> {
        self.gpus.take_frame(id, slot)
    }

    /// The user navigates tab `tab` to `url`: the kernel asks for the page,
    /// and the document is what the network serves.
    pub fn navigate_tab(&mut self, tab: u64, url: &str) {
        let url = code_points(url);
        self.event(EventRecord::NavigateTab { tab, url });
    }

    fn spawn(&mut self, id: u64) -> std::io::Result<()> {
        let (link, reader) = launch::spawn_paired((self.command)(id), self.gpus.take_list(id))?;
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
    /// own, then kill it; report how it ended and what it wrote to stderr. Its GPU process too.
    fn reap(&mut self, id: u64, why: &str, grace: Duration) {
        let gpu = self.gpus.finish(id, why, grace);
        gpu.into_iter().for_each(|l| self.say(l));
        let Some(link) = self.table.remove(&id) else {
            return;
        };
        let (status, stderr) = link.finish(grace);
        self.say(format!(
            "renderer {id} exited: {why}; {status}{}",
            launch::note(&stderr)
        ));
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
            Ok(Ev::Gpu(id, GpuReport::Frame(bytes))) if self.gpus.has(id) => {
                self.event(EventRecord::FromGpu { id, bytes });
            }
            Ok(Ev::Gpu(id, GpuReport::Pixels(frame))) => self.gpus.keep(id, frame),
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
