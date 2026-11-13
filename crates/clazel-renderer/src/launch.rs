//! Starting a renderer process and holding the host's end of its channel.
//!
//! On Unix the renderer's end is a socket pair that is its standard input and
//! output, and it sandboxes itself with [`crate::sandbox::enter`] as its
//! first act. On Windows nothing can confine a running process, so the host
//! starts the renderer already inside the AppContainer and Job Object of
//! `clazel_sandbox::appcontainer` (through `clazel-sys`), with three anonymous
//! pipes as its standard handles; `enter` there only checks that it is
//! confined. The host sees the same [`Link`] either way.

use std::collections::HashMap;
use std::io::{self, Read};
use std::process::Command;
use std::sync::mpsc::Sender;
use std::time::Duration;

use clazel_gpu::channel::{SurfaceFrame, read_surface};
use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed};

/// The host's end of a started renderer: write frames to it, then end it.
pub struct Link(imp::Link);

/// Start the renderer `command` describes. Its standard input and output are
/// the channel (the other [`Read`] is the renderer's output, for a reader
/// thread) and its standard error is captured for [`Link::finish`]. Other
/// settings of `command` are used only where the platform can honour them
/// (the program, its arguments and, on Unix, its environment).
pub fn spawn(command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
    let _alone = alone();
    spawn_held(command)
}

/// [`spawn`] for a caller that already holds [`alone`].
fn spawn_held(command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
    let (link, reader) = imp::spawn(command)?;
    Ok((Link(link), reader))
}

/// Held by every start in this module, for the whole of it: from clearing a
/// passed socket's close-on-exec flag to closing the host's copy.
static STARTING: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// One start at a time in this process. A descriptor whose close-on-exec flag
/// [`spawn_gpu`] or [`spawn_with_list`] has cleared is inherited by every
/// program started until its copy is closed. Another start in that window, by
/// another `Host` of the same process on another thread, would also inherit
/// it. Measured with `browse_gpu.rs`'s tests, which run several hosts at once:
/// renderers killed after commit, GPU processes whose `--list-fd` was not
/// their socket, and lost frames, in 3 of 15 runs. Serial runs had none in 15.
/// (A poisoned lock still serializes: the `()` it guards has no state to
/// break.)
///
/// Public so that other code starting programs in a process that runs hosts
/// (tests that run `clazel browse` beside in-process hosts) can start them
/// under the same lock: such a program would inherit the descriptors too.
pub fn alone() -> std::sync::MutexGuard<'static, ()> {
    STARTING
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The renderer's end of a GPU process's list socket, for [`spawn_with_list`].
pub struct ListEnd(
    #[cfg(target_os = "macos")] std::os::unix::net::UnixStream,
    #[cfg(target_os = "linux")] std::io::PipeWriter,
);

/// What the host holds of a started GPU process (items 5.18 and 5.23): its
/// channel to the kernel, as a renderer's; a reader of the surface socket; and
/// the renderer's end of the list socket.
pub struct GpuStart {
    /// The kernel's channel.
    pub link: Link,
    /// The GPU process's frames to the kernel, for a reader thread.
    pub frames: Box<dyn Read + Send>,
    /// The surface socket, for a reader thread (`clazel_gpu::channel`).
    pub surface: Box<dyn Read + Send>,
    /// The list socket's other end, for the paired renderer.
    pub list: ListEnd,
}

/// Start the GPU process `command` describes, as [`spawn`] starts a renderer,
/// with two more sockets inherited by number: the list socket's GPU end
/// (`--list-fd N`) and the surface socket's (`--surface-fd M`). On macOS and
/// Linux (clearing close-on-exec is `clazel_sys`'s `clear_close_on_exec`);
/// elsewhere it fails with `Unsupported`. On Linux the two channels are pipes,
/// not socket pairs: each carries bytes one way only, and the child opens its end
/// again through `/dev/fd/N`, which Linux refuses for a socket (`ENXIO`) and
/// allows for a pipe.
///
/// Every program started while those flags are clear inherits the two
/// descriptors. So nothing else is started between this call's clearing and
/// its return, which closes its copies: every start in this module holds one
/// process-wide lock (`alone`). Programs started outside this module
/// (`std::process::Command` elsewhere in the same process) are not covered.
pub fn spawn_gpu(command: Command) -> io::Result<GpuStart> {
    pairing::spawn_gpu(command)
}

/// [`spawn_with_list`] if there is a list socket for the renderer, else [`spawn`].
pub fn spawn_paired(
    command: Command,
    list: Option<ListEnd>,
) -> io::Result<(Link, Box<dyn Read + Send>)> {
    match list {
        Some(list) => spawn_with_list(command, list),
        None => spawn(command),
    }
}

/// Start a renderer as [`spawn`] does, with `list`, the list socket's renderer
/// end from [`spawn_gpu`], inherited by number as `--list-fd N`; the host's copy
/// is closed on return. On macOS and Linux.
pub fn spawn_with_list(
    command: Command,
    list: ListEnd,
) -> io::Result<(Link, Box<dyn Read + Send>)> {
    pairing::spawn_with_list(command, list)
}

#[cfg(target_os = "macos")]
mod pairing {
    use std::io::{self, Read};
    use std::os::unix::net::UnixStream;
    use std::process::Command;

    use super::{GpuStart, Link, ListEnd, alone, spawn_held};

    pub fn spawn_gpu(mut command: Command) -> io::Result<GpuStart> {
        let _alone = alone();
        let (list, list_gpu) = UnixStream::pair()?;
        let (surface, surface_gpu) = UnixStream::pair()?;
        let list_fd = pass(&list_gpu)?;
        let surface_fd = pass(&surface_gpu)?;
        command.args(["--list-fd", &list_fd, "--surface-fd", &surface_fd]);
        let started = spawn_held(command);
        drop((list_gpu, surface_gpu));
        let (link, frames) = started?;
        Ok(GpuStart {
            link,
            frames,
            surface: Box::new(surface),
            list: ListEnd(list),
        })
    }

    pub fn spawn_with_list(
        mut command: Command,
        list: ListEnd,
    ) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let _alone = alone();
        command.args(["--list-fd", &pass(&list.0)?]);
        let started = spawn_held(command);
        drop(list);
        started
    }

    /// Clear `socket`'s close-on-exec flag; its number, for the child's arguments.
    fn pass(socket: &UnixStream) -> io::Result<String> {
        use std::os::fd::{AsFd, AsRawFd};
        clazel_sys::macos::clear_close_on_exec(socket.as_fd())
            .map_err(|e| io::Error::from_raw_os_error(e.0))?;
        Ok(socket.as_raw_fd().to_string())
    }
}

#[cfg(target_os = "linux")]
mod pairing {
    use std::io::{self, Read};
    use std::os::fd::{AsFd, AsRawFd};
    use std::process::Command;

    use super::{GpuStart, Link, ListEnd, alone, spawn_held};

    pub fn spawn_gpu(mut command: Command) -> io::Result<GpuStart> {
        let _alone = alone();
        // The list goes renderer to GPU process, pixels GPU process to host.
        let (list_gpu, list) = io::pipe()?;
        let (surface, surface_gpu) = io::pipe()?;
        let list_fd = pass(&list_gpu)?;
        let surface_fd = pass(&surface_gpu)?;
        command.args(["--list-fd", &list_fd, "--surface-fd", &surface_fd]);
        let started = spawn_held(command);
        drop((list_gpu, surface_gpu));
        let (link, frames) = started?;
        Ok(GpuStart {
            link,
            frames,
            surface: Box::new(surface),
            list: ListEnd(list),
        })
    }

    pub fn spawn_with_list(
        mut command: Command,
        list: ListEnd,
    ) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let _alone = alone();
        command.args(["--list-fd", &pass(&list.0)?]);
        let started = spawn_held(command);
        drop(list);
        started
    }

    /// Clear `end`'s close-on-exec flag; its number, for the child's arguments.
    fn pass(end: &impl AsFd) -> io::Result<String> {
        let fd = end.as_fd();
        clazel_sys::linux::clear_close_on_exec(fd)
            .map_err(|e| io::Error::from_raw_os_error(e.0))?;
        Ok(fd.as_raw_fd().to_string())
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
mod pairing {
    use std::io::{self, Read};
    use std::process::Command;

    use super::{GpuStart, Link, ListEnd};

    fn unsupported() -> io::Error {
        io::Error::new(
            io::ErrorKind::Unsupported,
            "no GPU process on this platform yet (phase-5.md items 5.22, 5.22a)",
        )
    }

    pub fn spawn_gpu(_: Command) -> io::Result<GpuStart> {
        Err(unsupported())
    }

    pub fn spawn_with_list(_: Command, _: ListEnd) -> io::Result<(Link, Box<dyn Read + Send>)> {
        Err(unsupported())
    }
}

impl Link {
    /// Write a whole frame; false if the channel failed.
    pub fn send(&mut self, frame: &[u8]) -> bool {
        self.0.send(frame)
    }

    /// Close the channel, wait up to `grace` for the process to exit on its
    /// own, then kill it. Returns how it ended and what it wrote to stderr.
    pub fn finish(self, grace: Duration) -> (String, String) {
        self.0.finish(grace)
    }
}

#[cfg(unix)]
mod imp {
    use std::io::{self, Read, Write};
    use std::net::Shutdown;
    use std::os::{fd::OwnedFd, unix::net::UnixStream};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant};

    pub struct Link {
        sock: UnixStream,
        child: Child,
    }

    pub fn spawn(mut command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let (host_end, child_end) = UnixStream::pair()?;
        host_end.set_write_timeout(Some(Duration::from_secs(5)))?;
        let reader = host_end.try_clone()?;
        let stdin: OwnedFd = child_end.into();
        let stdout = stdin.try_clone()?;
        let child = command
            .stdin(stdin)
            .stdout(stdout)
            .stderr(Stdio::piped())
            .spawn()?;
        Ok((
            Link {
                sock: host_end,
                child,
            },
            Box::new(reader),
        ))
    }

    impl Link {
        pub fn send(&mut self, frame: &[u8]) -> bool {
            self.sock.write_all(frame).is_ok()
        }

        pub fn finish(mut self, grace: Duration) -> (String, String) {
            let _ = self.sock.shutdown(Shutdown::Both);
            let end = Instant::now()
                .checked_add(grace)
                .unwrap_or_else(Instant::now);
            while matches!(self.child.try_wait(), Ok(None)) && Instant::now() < end {
                std::thread::sleep(Duration::from_millis(10));
            }
            let _ = self.child.kill();
            let status = self
                .child
                .wait()
                .map_or_else(|e| e.to_string(), |s| s.to_string());
            let mut stderr = String::new();
            if let Some(mut e) = self.child.stderr.take() {
                let _ = e.read_to_string(&mut stderr);
            }
            (status, stderr)
        }
    }
}

#[cfg(windows)]
mod imp {
    use std::io::{self, PipeReader, PipeWriter, Read, Write};
    use std::os::windows::io::OwnedHandle;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::Mutex;
    use std::time::Duration;

    use clazel_sandbox::appcontainer as policy;
    use clazel_sys::Errno;
    use clazel_sys::windows::{self, Policy, Process, SpawnError};

    pub struct Link {
        to_child: Option<PipeWriter>,
        process: Process,
        stderr: PipeReader,
    }

    /// Binaries the AppContainer has been granted read and execute on.
    static GRANTED: Mutex<Vec<PathBuf>> = Mutex::new(Vec::new());

    /// One spawn at a time: Windows creates the AppContainer's per-user folders
    /// on first use and two `CreateProcessW` calls for the same container race
    /// (`ERROR_FILE_NOT_FOUND`), and a handle made inheritable for one spawn
    /// must not be inherited by another.
    static SPAWN: Mutex<()> = Mutex::new(());

    fn other(e: impl std::fmt::Display) -> io::Error {
        io::Error::other(e.to_string())
    }

    /// The AppContainer SID is on no file's ACL, so it cannot even start the
    /// renderer binary until it is granted read and execute on that one file
    /// (`icacls`, once per binary; the grant stays on the file).
    fn grant(program: &Path) -> io::Result<()> {
        let sid = windows::container_sid(policy::CONTAINER_NAME).map_err(other)?;
        let mut granted = GRANTED.lock().map_err(other)?;
        if granted.iter().any(|p| p == program) {
            return Ok(());
        }
        let out = Command::new("icacls")
            .arg(program)
            .arg("/grant")
            .arg(format!("*{}:(RX)", sid.text()))
            .output()?;
        if !out.status.success() {
            return Err(other(format!(
                "icacls could not grant the AppContainer access to {}: {}",
                program.display(),
                String::from_utf8_lossy(&out.stdout).trim()
            )));
        }
        granted.push(program.to_path_buf());
        Ok(())
    }

    fn env_pairs(system_root: &str) -> Vec<(&str, String)> {
        let mut v = vec![("SystemRoot", system_root.to_owned())];
        for k in ["LOCALAPPDATA", "USERPROFILE", "TEMP", "TMP", "APPDATA"] {
            if let Ok(x) = std::env::var(k) {
                v.push((k, x));
            }
        }
        v
    }

    pub fn spawn(command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let program = std::path::absolute(command.get_program())?;
        grant(&program)?;
        let mut line = windows::quote_arg(&program.to_string_lossy());
        for arg in command.get_args() {
            line.push(' ');
            line.push_str(&windows::quote_arg(&arg.to_string_lossy()));
        }
        let (stdin_r, stdin_w) = io::pipe()?;
        let (stdout_r, stdout_w) = io::pipe()?;
        let (stderr_r, stderr_w) = io::pipe()?;
        let (h_in, h_out, h_err) = (
            OwnedHandle::from(stdin_r),
            OwnedHandle::from(stdout_w),
            OwnedHandle::from(stderr_w),
        );
        let job = policy::RENDERER_JOB;
        let system_root = std::env::var("SystemRoot").unwrap_or_else(|_| r"C:\Windows".to_owned());
        let owned = env_pairs(&system_root);
        let env: Vec<(&str, &str)> = owned.iter().map(|(k, v)| (*k, v.as_str())).collect();
        let _one_at_a_time = SPAWN.lock().map_err(other)?;
        let confinement = Policy {
            container_name: policy::CONTAINER_NAME,
            capabilities: policy::CAPABILITIES,
            mitigations: policy::mitigation_mask(),
            child_process_restricted: policy::CHILD_PROCESS_RESTRICTED,
            opt_out_all_application_packages: policy::OPT_OUT_ALL_APPLICATION_PACKAGES,
            active_process_limit: job.active_process_limit,
            kill_on_close: job.kill_on_close,
            ui_restrictions: job.ui_restrictions,
            process_memory_limit: job.process_memory_limit,
        };
        // Windows sometimes answers a start with ERROR_FILE_NOT_FOUND although
        // the binary is there (seen on the CI runner for about 6 in 100
        // starts of short-lived renderers, and never on a retry), apparently
        // while the system is still tidying a container whose last process just
        // exited. ERROR_GEN_FAILURE (31) has been seen once in the same place
        // (CI run 42258642534, 1 start in 178; not reproduced in about 29,000
        // local starts), so its cause is unknown and treating it the same way
        // is a judgement. Only these errors, only while the file exists, are
        // retried; each attempt builds the whole confinement again, and one
        // that keeps failing still surfaces after the last retry.
        let mut retries = 0u32;
        let process = loop {
            let handles = windows::Handles {
                stdin: &h_in,
                stdout: &h_out,
                stderr: &h_err,
                inherit: &[],
            };
            match windows::spawn(&program, &line, &confinement, &env, &handles) {
                Ok(p) => break p,
                Err(SpawnError::Call("CreateProcessW", Errno(2 | 31)))
                    if retries < 100 && program.exists() =>
                {
                    retries = retries.saturating_add(1);
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(e) => return Err(other(e)),
            }
        };
        // The renderer holds its ends now; closing ours is what makes EOF
        // reach each side when the other dies.
        drop((h_in, h_out, h_err));
        let link = Link {
            to_child: Some(stdin_w),
            process,
            stderr: stderr_r,
        };
        Ok((link, Box::new(stdout_r)))
    }

    impl Link {
        pub fn send(&mut self, frame: &[u8]) -> bool {
            self.to_child
                .as_mut()
                .is_some_and(|w| w.write_all(frame).is_ok())
        }

        pub fn finish(mut self, grace: Duration) -> (String, String) {
            self.to_child = None;
            let ms = u32::try_from(grace.as_millis()).unwrap_or(u32::MAX);
            if !self.process.wait_timeout(ms) {
                let _ = self.process.kill();
                self.process.wait_timeout(1000);
            }
            let status = match self.process.try_wait() {
                Ok(Some(code)) => format!("exit code: {code}"),
                Ok(None) => "still running".to_owned(),
                Err(e) => e.to_string(),
            };
            let mut stderr = String::new();
            let _ = self.stderr.read_to_string(&mut stderr);
            (status, stderr)
        }
    }
}

/// What a GPU process's reader threads report to the host.
pub enum GpuReport {
    /// A whole frame for the kernel (`FromGpu`).
    Frame(Vec<u8>),
    /// A frame's pixels from the surface socket.
    Pixels(SurfaceFrame),
    /// Its kernel channel ended, and why.
    Gone(String),
}

/// The GPU processes the host runs (items 5.18 and 5.23), named by their
/// renderers' ids, and the pixels each sent last per ring slot. Reports go to the
/// host's channel as `wrap(id, report)`, the pattern of `clazel_net::Driver`.
pub struct Gpus<E> {
    tx: Sender<E>,
    wrap: fn(u64, GpuReport) -> E,
    command: Option<Box<dyn FnMut(u64) -> Command>>,
    links: HashMap<u64, Link>,
    lists: HashMap<u64, ListEnd>,
    frames: HashMap<(u64, u32), SurfaceFrame>,
}

impl<E: Send + 'static> Gpus<E> {
    /// No GPU process, and none started until [`Gpus::start_with`] (text mode).
    pub fn new(tx: Sender<E>, wrap: fn(u64, GpuReport) -> E) -> Gpus<E> {
        Gpus {
            tx,
            wrap,
            command: None,
            links: HashMap::new(),
            lists: HashMap::new(),
            frames: HashMap::new(),
        }
    }

    /// Start GPU processes with `command(id)` from now on.
    pub fn start_with(&mut self, command: impl FnMut(u64) -> Command + 'static) {
        self.command = Some(Box::new(command));
    }

    /// `SpawnGpu { id }`: start the process ([`spawn_gpu`]) and its two reader
    /// threads, and keep the list socket's renderer end for [`Gpus::take_list`].
    /// Nothing in text mode. An error is a line for the host's log.
    pub fn spawn(&mut self, id: u64) -> Result<(), String> {
        let Some(command) = self.command.as_mut() else {
            return Ok(());
        };
        let start = spawn_gpu(command(id)).map_err(|e| format!("gpu {id}: cannot start: {e}"))?;
        let (tx, wrap, mut frames) = (self.tx.clone(), self.wrap, start.frames);
        std::thread::spawn(move || {
            let why = loop {
                match read_frame(&mut frames) {
                    Ok(frame) => {
                        if tx.send(wrap(id, GpuReport::Frame(frame))).is_err() {
                            return;
                        }
                    }
                    Err(why) => break why,
                }
            };
            let _ = tx.send(wrap(id, GpuReport::Gone(why)));
        });
        let (tx, wrap, mut surface) = (self.tx.clone(), self.wrap, start.surface);
        std::thread::spawn(move || {
            while let Ok(Some(f)) = read_surface(&mut surface) {
                if tx.send(wrap(id, GpuReport::Pixels(f))).is_err() {
                    return;
                }
            }
        });
        self.links.insert(id, start.link);
        self.lists.insert(id, start.list);
        Ok(())
    }

    /// The list socket's renderer end for renderer `id`, once.
    pub fn take_list(&mut self, id: u64) -> Option<ListEnd> {
        self.lists.remove(&id)
    }

    /// Whether the GPU process of renderer `id` runs.
    pub fn has(&self, id: u64) -> bool {
        self.links.contains_key(&id)
    }

    /// The ids of every running GPU process.
    pub fn ids(&self) -> Vec<u64> {
        self.links.keys().copied().collect()
    }

    /// `ToGpu`: write a frame. A failed write is not reported here: the process
    /// is then gone, and its reader thread says so ([`GpuReport::Gone`]).
    pub fn send(&mut self, id: u64, frame: &[u8]) {
        if let Some(link) = self.links.get_mut(&id) {
            link.send(frame);
        }
    }

    /// Keep `frame` as slot `frame.slot`'s pixels of `id`'s process, if it runs.
    pub fn keep(&mut self, id: u64, frame: SurfaceFrame) {
        if self.has(id) {
            self.frames.insert((id, frame.slot), frame);
        }
    }

    /// The pixels slot `slot` of `id`'s process holds, taken out.
    pub fn take_frame(&mut self, id: u64, slot: u32) -> Option<SurfaceFrame> {
        self.frames.remove(&(id, slot))
    }

    /// End `id`'s process as [`Link::finish`] does and forget its pixels; the
    /// line for the host's log, if it ran.
    pub fn finish(&mut self, id: u64, why: &str, grace: Duration) -> Option<String> {
        self.lists.remove(&id);
        self.frames.retain(|(r, _), _| *r != id);
        let (status, stderr) = self.links.remove(&id)?.finish(grace);
        Some(format!("gpu {id} exited: {why}; {status}{}", note(&stderr)))
    }
}

impl<E> Drop for Gpus<E> {
    fn drop(&mut self) {
        for (_, link) in self.links.drain() {
            link.finish(Duration::ZERO);
        }
    }
}

/// `"; stderr: …"` for a process's log line, or nothing if it wrote nothing.
pub fn note(stderr: &str) -> String {
    Some(stderr.trim())
        .filter(|s| !s.is_empty())
        .map_or(String::new(), |s| format!("; stderr: {s}"))
}

/// For the host's log (`crates/clazel`): the first frame of one write (a document is `Commit`, `Body`s,
/// `BodyEnd`) as the call or answer it carries.
pub fn describe(frame: &[u8]) -> String {
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

/// One whole IPC frame, header included, or why the channel ended.
fn read_frame(r: &mut impl Read) -> Result<Vec<u8>, String> {
    let mut frame = vec![0u8; 4];
    r.read_exact(&mut frame)
        .map_err(|_| "closed its socket".to_owned())?;
    let n = payload_length(&frame).ok_or("sent a frame over MAX_FRAME")?;
    frame.resize(n.saturating_add(4), 0);
    r.read_exact(frame.get_mut(4..).unwrap_or_default())
        .map_err(|_| "closed its socket inside a frame".to_owned())?;
    Ok(frame)
}
