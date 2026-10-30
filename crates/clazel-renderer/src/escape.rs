//! Sandbox escape attempts (phase-2.md item 2.16): the calls a compromised
//! renderer would make to reach something other than its socket, written
//! with `std` and the two safe attempt functions of `clazel-sys` (the
//! crate has no `unsafe`).
//!
//! [`try_it`] makes one call and says whether it *succeeded*; succeeding is
//! the escape. The adversary binary runs it after entering the sandbox,
//! one attempt per process, because on Linux a forbidden call kills the
//! process (`SIGSYS`, from the seccomp filter) and that is the pass there.
//!
//! `fork` and `ptrace` of a sibling are not in `std` (`Command::spawn` is
//! `posix_spawn` on macOS and `fork`/`clone` plus `exec` on Linux, so
//! `execve` below exercises process execution, not a bare `fork`), so those
//! two go through `clazel_sys::{linux,macos}::attempt_fork` and
//! `attempt_ptrace_attach`, which return only whether the OS allowed the
//! call. A `fork` child that is created exits at once; a `ptrace` attach that
//! succeeds leaves the sibling traced, and the test kills it.

use std::fs::{File, OpenOptions};
use std::io::{self, Read};
use std::net::{TcpListener, TcpStream, UdpSocket};
use std::process::{Command, Stdio};

/// One thing a renderer must not be able to do.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Attempt {
    /// Open an existing file for reading: where the cookie jar would live.
    OpenCookieJar,
    /// Open any other existing file for reading.
    OpenFile,
    /// Create a new file.
    CreateFile,
    /// Connect to a TCP listener.
    TcpConnect,
    /// Listen on a TCP port.
    TcpListen,
    /// Bind a UDP socket.
    UdpBind,
    /// Connect to a Unix socket.
    UnixConnect,
    /// Create a Unix socket.
    UnixListen,
    /// Start another program (`execve`, through `Command`).
    Execve,
    /// Create a process with a bare `fork` (the child exits at once).
    Fork,
    /// Attach to a sibling process, whose pid is the target
    /// (`ptrace(PTRACE_ATTACH)` on Linux, `ptrace(PT_ATTACHEXC)` on macOS).
    PtraceAttach,
}

impl Attempt {
    /// Every attempt.
    pub const ALL: [Attempt; 11] = [
        Attempt::OpenCookieJar,
        Attempt::OpenFile,
        Attempt::CreateFile,
        Attempt::TcpConnect,
        Attempt::TcpListen,
        Attempt::UdpBind,
        Attempt::UnixConnect,
        Attempt::UnixListen,
        Attempt::Execve,
        Attempt::Fork,
        Attempt::PtraceAttach,
    ];

    /// The name on the command line.
    pub fn name(self) -> &'static str {
        match self {
            Attempt::OpenCookieJar => "open-cookie-jar",
            Attempt::OpenFile => "open-file",
            Attempt::CreateFile => "create-file",
            Attempt::TcpConnect => "tcp-connect",
            Attempt::TcpListen => "tcp-listen",
            Attempt::UdpBind => "udp-bind",
            Attempt::UnixConnect => "unix-connect",
            Attempt::UnixListen => "unix-listen",
            Attempt::Execve => "execve",
            Attempt::Fork => "fork",
            Attempt::PtraceAttach => "ptrace-attach",
        }
    }

    /// The attempt called `name`.
    pub fn parse(name: &str) -> Option<Attempt> {
        Attempt::ALL.into_iter().find(|a| a.name() == name)
    }
}

/// Make the call on `target` (a path, a `host:port` or a program). `Ok` is
/// what succeeded, which is an escape; `Err` is the OS refusing.
pub fn try_it(attempt: Attempt, target: &str) -> io::Result<String> {
    // In the Windows sandbox Winsock cannot start, and `std` panics on that
    // instead of returning an error: the call failed, which is a denial.
    #[cfg(windows)]
    return std::panic::catch_unwind(|| attempt_it(attempt, target)).unwrap_or_else(|_| {
        Err(io::Error::other(
            "the call panicked (Winsock cannot start in the sandbox)",
        ))
    });
    #[cfg(not(windows))]
    attempt_it(attempt, target)
}

fn attempt_it(attempt: Attempt, target: &str) -> io::Result<String> {
    match attempt {
        Attempt::OpenCookieJar | Attempt::OpenFile => {
            let mut head = String::new();
            File::open(target)?.take(32).read_to_string(&mut head)?;
            Ok(format!("read {head:?} from {target}"))
        }
        Attempt::CreateFile => {
            OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(target)?;
            Ok(format!("created {target}"))
        }
        Attempt::TcpConnect => {
            let peer = TcpStream::connect(target)?.peer_addr()?;
            Ok(format!("connected to {peer}"))
        }
        Attempt::TcpListen => {
            let addr = TcpListener::bind(target)?.local_addr()?;
            Ok(format!("listening on {addr}"))
        }
        Attempt::UdpBind => {
            let addr = UdpSocket::bind(target)?.local_addr()?;
            Ok(format!("bound {addr}"))
        }
        Attempt::UnixConnect => {
            unix_connect(target)?;
            Ok(format!("connected to {target}"))
        }
        Attempt::UnixListen => {
            unix_listen(target)?;
            Ok(format!("listening on {target}"))
        }
        Attempt::Execve => {
            let status = Command::new(target)
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()?;
            Ok(format!("ran {target}: {status}"))
        }
        Attempt::Fork => {
            fork()?;
            Ok("a child process was created".to_owned())
        }
        Attempt::PtraceAttach => {
            let pid: i32 = target
                .parse()
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "target is not a pid"))?;
            ptrace_attach(pid)?;
            Ok(format!("attached to process {pid}"))
        }
    }
}

#[cfg(unix)]
fn unix_connect(target: &str) -> io::Result<()> {
    std::os::unix::net::UnixStream::connect(target).map(drop)
}

#[cfg(unix)]
fn unix_listen(target: &str) -> io::Result<()> {
    std::os::unix::net::UnixListener::bind(target).map(drop)
}

#[cfg(not(unix))]
fn unix_connect(_target: &str) -> io::Result<()> {
    Err(io::ErrorKind::Unsupported.into())
}

#[cfg(not(unix))]
fn unix_listen(_target: &str) -> io::Result<()> {
    Err(io::ErrorKind::Unsupported.into())
}

#[cfg(target_os = "linux")]
use clazel_sys::linux as os;
#[cfg(target_os = "macos")]
use clazel_sys::macos as os;

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn fork() -> io::Result<()> {
    os::attempt_fork().map_err(|e| io::Error::from_raw_os_error(e.0))
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn ptrace_attach(pid: i32) -> io::Result<()> {
    os::attempt_ptrace_attach(pid).map_err(|e| io::Error::from_raw_os_error(e.0))
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn fork() -> io::Result<()> {
    Err(io::ErrorKind::Unsupported.into())
}

/// Windows: `OpenProcess` with read, write and operation access, the analogue
/// of a `ptrace` attach.
#[cfg(windows)]
fn ptrace_attach(pid: i32) -> io::Result<()> {
    let pid = u32::try_from(pid)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "target is not a pid"))?;
    clazel_sys::windows::attempt_open_process(pid).map_err(|e| io::Error::from_raw_os_error(e.0))
}

#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn ptrace_attach(_pid: i32) -> io::Result<()> {
    Err(io::ErrorKind::Unsupported.into())
}
