//! The host's window (phase-5.md items 5.21 to 5.22a): open one, read its events
//! and show pixels in it.
//!
//! On Windows (5.22a, drawn with GDI), on macOS on Apple silicon (5.21) and on
//! Linux (5.22). The backends give the same [`Window`]: `open`, `size`,
//! `next_event`, `draw`, `show_page_pixels`, `hide_page`, `set_title`, `dpi`,
//! `activate` and `close`, reporting the same [`Event`]s. What a
//! platform's message or event means is decided here, in [`messages`] (Win32),
//! [`nsevent`] (AppKit) and [`x11proto`] (X11), as pure functions that every
//! target can test; the foreign calls of Windows and macOS are all in
//! `clazel-sys`, and Linux makes none: its X11 client is safe Rust over a Unix
//! socket.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **Windows: messages are read on a thread of their own.** A drag of the
//!   window's frame stays inside `DispatchMessageW` until it ends, so the thread
//!   that draws must be another one.
//! - **Windows: size and closing are polled.** `DefWindowProcW` is the window
//!   procedure, so `WM_SIZE` and `WM_CLOSE` never reach us. [`Window::next_event`]
//!   compares the size each time it is called, and the message thread checks that
//!   the window still exists at least every 50 ms.
//! - **macOS: everything on the main thread, polled.** AppKit allows nothing
//!   else, and no callback is defined, so a drag blocks
//!   [`Window::next_event`] until it ends. The module `appkit` lists its
//!   decisions.
//! - **Linux: an X11 client of our own**, with the server's bytes read on a
//!   thread of their own; a Wayland session is reached through XWayland. The
//!   modules `x11` and [`x11proto`] list their decisions.

pub mod event;
pub mod keys;
pub mod messages;
pub mod nsevent;
pub mod pattern;
pub mod x11proto;

pub use event::Event;

#[cfg(windows)]
mod win32;
#[cfg(windows)]
pub use win32::{Error, Window};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod appkit;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub use appkit::{Error, Surface, Window, has_window_server};

#[cfg(target_os = "linux")]
mod x11;
#[cfg(target_os = "linux")]
pub use x11::{Error, Window, has_display};
