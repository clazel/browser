//! `clazel-renderer [--width N]`: enter the sandbox, then take committed
//! documents: run a user script, or display a document through the
//! pipeline of phase-4.md item 4.13, laid out N columns wide (default 80;
//! 0: no wrapping). The host passes its terminal width as the argument.
//! `--font PATH` (repeated) names font files, read before the sandbox is
//! entered (phase-5.md item 5.20). `--list-fd N` (item 5.23) is the GPU
//! process's list socket, inherited from the host, which cleared its
//! close-on-exec flag for this start: opened again through `/dev/fd/N`
//! before the sandbox, it selects the graphical pipeline (`run_graphics`).
//! Without it the text path (`Display`) runs, as item 5.18 decided for text
//! mode.
//! Exit codes: 71 a sandbox layer failed (nothing was read), 70 the socket or
//! protocol failed. The messages go to standard error, which the host
//! reports.

use std::io;
use std::process::ExitCode;

/// The `--width N` argument, or the default; any other argument is
/// ignored (the host builds the command line).
fn width() -> usize {
    let args: Vec<String> = std::env::args().collect();
    args.iter()
        .position(|a| a == "--width")
        .and_then(|i| args.get(i.saturating_add(1)))
        .and_then(|w| w.parse::<usize>().ok())
        .unwrap_or(clazel_renderer::DEFAULT_WIDTH)
}

/// The `--font PATH` arguments.
fn font_paths() -> Vec<std::path::PathBuf> {
    let args: Vec<String> = std::env::args().collect();
    args.windows(2)
        .filter(|w| w.first().is_some_and(|a| a == "--font"))
        .filter_map(|w| w.get(1).map(std::path::PathBuf::from))
        .collect()
}

/// The `--list-fd N` argument.
fn list_fd() -> Option<u32> {
    let args: Vec<String> = std::env::args().collect();
    let i = args.iter().position(|a| a == "--list-fd")?;
    args.get(i.checked_add(1)?)?.parse().ok()
}

/// The list socket, from its descriptor number: opened again through `/dev/fd`.
#[cfg(not(windows))]
fn open_list(n: u32) -> io::Result<std::fs::File> {
    std::fs::OpenOptions::new()
        .write(true)
        .open(format!("/dev/fd/{n}"))
}

/// The list pipe, from the value of the handle this process inherited
/// (`clazel_sys::windows::Inherited`, a duplicate of it).
#[cfg(windows)]
fn open_list(n: u32) -> io::Result<clazel_sys::windows::Inherited> {
    clazel_sys::windows::Inherited::open(u64::from(n)).map_err(io::Error::other)
}

/// How long a read waits before the page's timers get a turn.
#[cfg(unix)]
const POLL: std::time::Duration = std::time::Duration::from_millis(20);

/// The input socket with a read timeout, if standard input is a socket the
/// process can duplicate: the page's event loop runs between reads. The
/// descriptor is never closed (see `main`).
#[cfg(unix)]
struct Polled(Option<std::os::unix::net::UnixStream>);

#[cfg(unix)]
impl io::Read for Polled {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.0.as_mut() {
            Some(s) => io::Read::read(s, buf),
            None => Ok(0),
        }
    }
}

#[cfg(unix)]
impl Drop for Polled {
    fn drop(&mut self) {
        if let Some(s) = self.0.take() {
            core::mem::forget(s);
        }
    }
}

#[cfg(unix)]
fn polled_input() -> Option<Polled> {
    use std::os::fd::AsFd;
    let fd = io::stdin().as_fd().try_clone_to_owned().ok()?;
    let socket = std::os::unix::net::UnixStream::from(fd);
    socket.set_read_timeout(Some(POLL)).ok()?;
    Some(Polled(Some(socket)))
}

/// Windows reads from standard input as it is.
#[cfg(windows)]
fn polled_input() -> Option<io::Stdin> {
    None
}

fn main() -> ExitCode {
    let width = width();
    // Fonts and the list socket are opened before the sandbox, which forbids
    // opening any file.
    let paths = font_paths();
    let refs: Vec<&std::path::Path> = paths.iter().map(|p| p.as_path()).collect();
    let fonts = clazel_renderer::page::fonts::Fonts::read(&refs);
    let list = match list_fd() {
        None => None,
        Some(n) => match open_list(n) {
            Ok(f) => Some(f),
            Err(e) => {
                eprintln!("clazel-renderer: cannot open the list socket {n}: {e}");
                return ExitCode::from(70);
            }
        },
    };
    let polled_input = polled_input();
    // First act, before a byte is read: fail closed.
    if let Err(failure) = clazel_renderer::sandbox::enter() {
        eprintln!("clazel-renderer: {failure}");
        return ExitCode::from(71);
    }
    // The host gave this process one socket as both stdin and stdout. The
    // graphical renderer runs the page's timers, so it reads with a timeout
    // where the socket allows one (set before the sandbox: it can make no
    // thread and no `poll` call after it).
    // The list socket lives until the process exits, never dropped: a debug
    // build's std checks a descriptor it drops with `fcntl(F_GETFD)`, which the
    // seccomp filter refuses by killing the process (`SIGSYS`).
    let ran = match list {
        Some(list) => {
            let list = Box::leak(Box::new(list));
            match polled_input {
                Some(input) => clazel_renderer::run_graphics(input, io::stdout(), list, &fonts),
                None => clazel_renderer::run_graphics(io::stdin(), io::stdout(), list, &fonts),
            }
        }
        None => clazel_renderer::run_with_width(io::stdin(), io::stdout(), width),
    };
    match ran {
        Ok(_) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("clazel-renderer: {e}");
            ExitCode::from(70)
        }
    }
}
