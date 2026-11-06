//! The host's window (phase-5.md items 5.21 to 5.22a): open one, read its events
//! and show pixels in it.
//!
//! Windows only so far. What a Win32 message means is decided here, in
//! [`messages`], as a pure function that every target can test; the foreign calls
//! are all in `clazel-sys`.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **Messages are read on a thread of their own.** A drag of the window's frame
//!   stays inside `DispatchMessageW` until it ends, so the thread that draws must
//!   be another one.
//! - **Size and closing are polled.** `DefWindowProcW` is the window procedure, so
//!   `WM_SIZE` and `WM_CLOSE` never reach us. [`Window::next_event`] compares the
//!   size each time it is called, and the message thread checks that the window
//!   still exists at least every 50 ms.

pub mod event;
pub mod messages;
pub mod pattern;

pub use event::Event;

#[cfg(windows)]
mod win32;
#[cfg(windows)]
pub use win32::{Error, Window};
