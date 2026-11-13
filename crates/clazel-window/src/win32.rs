//! The window on Windows, over `clazel_sys::windows::window`.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
use std::thread::JoinHandle;
use std::time::Duration;

use clazel_sys::windows::SpawnError;
use clazel_sys::windows::window as sys;

use crate::Event;
use crate::messages::{Translated, translate};

/// How long the message thread sleeps before checking that the window still
/// exists, since nothing wakes it when the window is closed.
const CHECK_EVERY_MS: u32 = 50;

/// Why a window could not be opened or drawn to.
#[derive(Debug)]
pub enum Error {
    /// A call failed.
    Os(SpawnError),
    /// The message thread could not start or stopped before opening the window.
    Thread,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Os(e) => write!(f, "{e}"),
            Error::Thread => f.write_str("the window's message thread did not start"),
        }
    }
}

impl std::error::Error for Error {}

/// An open window. Dropping it closes it.
#[derive(Debug)]
pub struct Window {
    handle: sys::WindowHandle,
    events: Receiver<Event>,
    size: (u32, u32),
    closed: bool,
    stop: Arc<AtomicBool>,
    /// Set by the message thread once the window has ended, so that this handle is
    /// no longer used: the system may give its value to a later window.
    gone: Arc<AtomicBool>,
    thread: Option<JoinHandle<()>>,
}

impl Window {
    /// Open a window of the system's default size.
    pub fn open(title: &str) -> Result<Window, Error> {
        let title = title.to_owned();
        let (opened_tx, opened_rx) = channel();
        let (events_tx, events) = channel();
        let stop = Arc::new(AtomicBool::new(false));
        let thread_stop = Arc::clone(&stop);
        let gone = Arc::new(AtomicBool::new(false));
        let thread_gone = Arc::clone(&gone);
        let thread = std::thread::Builder::new()
            .name("clazel-window".to_owned())
            .spawn(move || {
                // A process's awareness can only be set once, so a second window
                // being refused here changes nothing.
                let _ = sys::set_dpi_aware();
                match sys::create_window(&title) {
                    Ok(handle) => {
                        let _ = opened_tx.send(Ok(handle));
                        pump(handle, &events_tx, &thread_stop, &thread_gone);
                    }
                    Err(e) => {
                        let _ = opened_tx.send(Err(e));
                    }
                }
            })
            .map_err(|_| Error::Thread)?;
        let handle = match opened_rx.recv() {
            Ok(Ok(handle)) => handle,
            Ok(Err(e)) => return Err(Error::Os(e)),
            Err(_) => return Err(Error::Thread),
        };
        let size = sys::client_size(handle).map_err(Error::Os)?;
        Ok(Window {
            handle,
            events,
            size,
            closed: false,
            stop,
            gone,
            thread: Some(thread),
        })
    }

    /// The client area's size in pixels, as of the last [`Event::Resized`] or
    /// [`Window::open`].
    pub fn size(&self) -> (u32, u32) {
        self.size
    }

    /// The next event, waiting up to `timeout`. `None` if nothing happened.
    /// After [`Event::Closed`] this is always `None`.
    pub fn next_event(&mut self, timeout: Duration) -> Option<Event> {
        if self.closed {
            return None;
        }
        if let Some(resized) = self.resized() {
            return Some(resized);
        }
        match self.events.recv_timeout(timeout) {
            Ok(Event::Closed) | Err(RecvTimeoutError::Disconnected) => {
                self.closed = true;
                Some(Event::Closed)
            }
            Ok(event) => Some(event),
            Err(RecvTimeoutError::Timeout) => self.resized(),
        }
    }

    /// The size, if it has changed since it was last reported. The message thread
    /// cannot report this: it never sees `WM_SIZE`, and it is blocked during a drag.
    fn resized(&mut self) -> Option<Event> {
        if !self.exists() {
            return None;
        }
        let now = sys::client_size(self.handle).ok()?;
        if now == self.size {
            return None;
        }
        self.size = now;
        Some(Event::Resized {
            width: now.0,
            height: now.1,
        })
    }

    /// Copy `width` by `height` pixels to the client area's top left corner, in
    /// rows from the top, each `0x00RRGGBB`. The length of `pixels` must match.
    /// Drawing to a window the user has just closed does nothing, since
    /// [`Event::Closed`] may still be behind other queued events.
    ///
    /// The handle is checked first, because the system may reuse an ended window's
    /// handle. A window closed in the instant between the check and the draw is the
    /// one gap left (`clazel_sys::windows::window::WindowHandle`).
    pub fn draw(&self, pixels: &[u32], width: u32, height: u32) -> Result<(), Error> {
        if !self.exists() {
            return Ok(());
        }
        let drawn = sys::draw_bgra(self.handle, pixels, width, height, (0, 0));
        ignore_if_gone(drawn, || self.exists()).map_err(Error::Os)
    }

    /// Set the title bar's text. Text with a NUL in it is an error. Like
    /// [`Window::draw`], this does nothing to a window the user has just closed.
    pub fn set_title(&self, title: &str) -> Result<(), Error> {
        if !self.exists() {
            return Ok(());
        }
        let set = sys::set_title(self.handle, title);
        ignore_if_gone(set, || self.exists()).map_err(Error::Os)
    }

    /// The dots per inch of the window's monitor now, 96 being unscaled. `None` once
    /// the window has ended. Nothing reports a change, since `WM_DPICHANGED` goes to
    /// `DefWindowProcW` as `WM_SIZE` does, so a caller asks again.
    ///
    /// [`Window::open`] asks for per-monitor awareness. If the process's awareness was
    /// already set otherwise, the answer follows that setting, and can be 96 on a
    /// scaled monitor.
    pub fn dpi(&self) -> Option<u32> {
        if !self.exists() {
            return None;
        }
        sys::window_dpi(self.handle)
    }

    /// Whether the handle still names this window.
    fn exists(&self) -> bool {
        !self.gone.load(Ordering::Relaxed) && sys::is_window(self.handle)
    }
}

impl Drop for Window {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        if let Some(thread) = self.thread.take() {
            // A panic on that thread has nothing more to report here.
            let _ = thread.join();
        }
    }
}

/// A failed draw is only an error while the window still exists. The window is
/// asked about afterwards because it can close at any moment before the call.
fn ignore_if_gone<E>(drawn: Result<(), E>, exists: impl FnOnce() -> bool) -> Result<(), E> {
    match drawn {
        Err(_) if !exists() => Ok(()),
        other => other,
    }
}

/// Read the window's messages until it is gone or `stop` is set. This thread
/// created the window, so only it can destroy it.
fn pump(handle: sys::WindowHandle, events: &Sender<Event>, stop: &AtomicBool, gone: &AtomicBool) {
    loop {
        while let Some(raw) = sys::next_message() {
            if let Some(event) = meaning(handle, raw) {
                // The receiver only goes away with the `Window`, whose drop sets
                // `stop`, so a failed send is handled below.
                let _ = events.send(event);
            }
        }
        if !sys::is_window(handle) {
            gone.store(true, Ordering::Relaxed);
            let _ = events.send(Event::Closed);
            return;
        }
        if stop.load(Ordering::Relaxed) {
            gone.store(true, Ordering::Relaxed);
            // The window existed a moment ago; if the user closed it since, there
            // is nothing left to do.
            let _ = sys::destroy_window(handle);
            return;
        }
        sys::wait_for_message(CHECK_EVERY_MS);
    }
}

fn meaning(handle: sys::WindowHandle, raw: sys::RawMessage) -> Option<Event> {
    match translate(raw.message, raw.w_param, raw.l_param)? {
        Translated::Event(event) => Some(event),
        Translated::WheelOnScreen { delta, x, y } => {
            let (x, y) = sys::screen_to_client(handle, x, y).ok()?;
            Some(Event::Wheel { delta, x, y })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_failed_draw_counts_only_while_the_window_exists() {
        assert_eq!(ignore_if_gone(Err(1400), || false), Ok(()));
        assert_eq!(ignore_if_gone(Err(1400), || true), Err(1400));
        assert_eq!(ignore_if_gone::<i32>(Ok(()), || true), Ok(()));
        assert_eq!(ignore_if_gone::<i32>(Ok(()), || false), Ok(()));
    }
}
