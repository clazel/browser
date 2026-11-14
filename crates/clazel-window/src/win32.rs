//! The window on Windows, over `clazel_sys::windows::window`.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **The page is drawn with GDI, below the strip.** [`Window::show_page_pixels`]
//!   copies the page's pixels into the client area at the place it is given
//!   (`SetDIBitsToDevice`), as [`Window::draw`] copies the strip to the top left
//!   corner. There is no child window and no DirectComposition visual (the
//!   plan's route, item 5.22a): the image's top left corner is where the host
//!   says and it only extends right and down, so a page can cover nothing above
//!   or to the left of that corner, which is where the strip is; GDI cuts it at
//!   the client area's edges.
//! - **The page's pixels are kept** and drawn again after the strip in
//!   [`Window::draw`], which the host calls on [`Event::Expose`]: the system
//!   erases what a resize uncovers, and nothing else would paint it again.
//! - **[`Window::hide_page`] forgets the kept pixels** and paints nothing: what
//!   was shown stays until the host draws over it or the system erases it.
//! - **Ctrl is the shortcut modifier** ([`Event::Key`]'s `command`), read with
//!   `GetKeyState` on the message thread as each key message is read, so it is
//!   the state at that message.
//! - **Focus is the system's to give**: a new top-level window is activated when
//!   it is created visible, so [`Window::activate`] does nothing, as on Linux.
//!
//! The page region, `close` and Ctrl were written on a Mac and compiled for
//! Windows without tests; they have never run.

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
    /// A page's pixels were not `width` by `height`, or its place does not fit.
    Page,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Os(e) => write!(f, "{e}"),
            Error::Thread => f.write_str("the window's message thread did not start"),
            Error::Page => f.write_str("a page's pixels do not match its size or place"),
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
    /// Set by [`Window::close`]: the message thread, which created the window
    /// and so is the one that can, destroys it.
    close: Arc<AtomicBool>,
    /// The page shown, kept to be drawn again.
    page: Option<Page>,
    thread: Option<JoinHandle<()>>,
}

/// A page's pixels and where they go.
#[derive(Debug)]
struct Page {
    pixels: Vec<u32>,
    at: (i32, i32),
    width: u32,
    height: u32,
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
        let close = Arc::new(AtomicBool::new(false));
        let thread_close = Arc::clone(&close);
        let thread = std::thread::Builder::new()
            .name("clazel-window".to_owned())
            .spawn(move || {
                // A process's awareness can only be set once, so a second window
                // being refused here changes nothing.
                let _ = sys::set_dpi_aware();
                match sys::create_window(&title) {
                    Ok(handle) => {
                        let _ = opened_tx.send(Ok(handle));
                        let flags = Flags {
                            stop: &thread_stop,
                            close: &thread_close,
                            gone: &thread_gone,
                        };
                        pump(handle, &events_tx, &flags);
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
            close,
            page: None,
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
    /// Then the page, if one is shown, is drawn again where it was put.
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
        ignore_if_gone(drawn, || self.exists()).map_err(Error::Os)?;
        self.draw_page()
    }

    /// Draw the kept page, if there is one.
    fn draw_page(&self) -> Result<(), Error> {
        let Some(page) = &self.page else {
            return Ok(());
        };
        if !self.exists() {
            return Ok(());
        }
        let drawn = sys::draw_bgra(self.handle, &page.pixels, page.width, page.height, page.at);
        ignore_if_gone(drawn, || self.exists()).map_err(Error::Os)
    }

    /// Show `width` by `height` pixels, each `0x00RRGGBB`, rows from the top, as
    /// the page, its top left corner at `x`, `y` from the client area's. The
    /// length of `pixels` must match. What falls outside the client area is not
    /// drawn, and nothing above or to the left of that corner is touched (see
    /// the module documentation).
    pub fn show_page_pixels(
        &mut self,
        pixels: &[u32],
        (x, y): (u32, u32),
        width: u32,
        height: u32,
    ) -> Result<(), Error> {
        let place = i32::try_from(x).ok().zip(i32::try_from(y).ok());
        let fits =
            u64::from(width).checked_mul(u64::from(height)) == u64::try_from(pixels.len()).ok();
        let (Some(at), true) = (place, fits) else {
            return Err(Error::Page);
        };
        self.page = Some(Page {
            pixels: pixels.to_vec(),
            at,
            width,
            height,
        });
        self.draw_page()
    }

    /// Show no page: the kept pixels are forgotten. Nothing is painted (see the
    /// module documentation).
    pub fn hide_page(&mut self) -> Result<(), Error> {
        self.page = None;
        Ok(())
    }

    /// Nothing: the system activates a new window itself.
    pub fn activate(&self) {}

    /// Close the window; [`Window::next_event`] then reports [`Event::Closed`],
    /// once the message thread has destroyed it (within 50 ms).
    pub fn close(&mut self) {
        self.close.store(true, Ordering::Relaxed);
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

/// What the message thread shares with its [`Window`].
struct Flags<'a> {
    /// The `Window` was dropped: destroy the window and end.
    stop: &'a AtomicBool,
    /// [`Window::close`] was called: destroy the window and report it closed.
    close: &'a AtomicBool,
    /// Set here once the window has ended.
    gone: &'a AtomicBool,
}

/// Read the window's messages until it is gone or `stop` is set. This thread
/// created the window, so only it can destroy it.
fn pump(handle: sys::WindowHandle, events: &Sender<Event>, flags: &Flags<'_>) {
    let Flags { stop, close, gone } = *flags;
    loop {
        while let Some(raw) = sys::next_message() {
            if let Some(event) = meaning(handle, raw) {
                // The receiver only goes away with the `Window`, whose drop sets
                // `stop`, so a failed send is handled below.
                let _ = events.send(event);
            }
        }
        if close.swap(false, Ordering::Relaxed) {
            // If the user closed it in the same moment there is nothing to
            // destroy, and the check below reports it either way.
            let _ = sys::destroy_window(handle);
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
        // Whether Ctrl is held is not in a key message: it is this thread's key
        // state as of the message it has just read.
        Translated::Event(Event::Key { code, .. }) => Some(Event::Key {
            code,
            command: sys::control_is_down(),
        }),
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
