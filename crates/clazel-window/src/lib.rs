//! The host's window (phase-5.md items 5.21 to 5.22a): open one, read its events
//! and show pixels in it.
//!
//! On Windows (5.22a, first slice) and on macOS on Apple silicon (5.21). Both
//! backends give the same [`Window`]: `open`, `size`, `next_event`, `draw`,
//! `set_title` and `dpi`, reporting the same [`Event`]s. What a platform's
//! message or event means is decided here, in [`messages`] (Win32) and
//! [`nsevent`] (AppKit), as pure functions that every target can test; the
//! foreign calls are all in `clazel-sys`.
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

pub mod event;
pub mod messages;
pub mod nsevent;
pub mod pattern;

pub use event::Event;

#[cfg(windows)]
mod win32;
#[cfg(windows)]
pub use win32::{Error, Window};

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod appkit;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub use appkit::{Error, Surface, Window, has_window_server};
