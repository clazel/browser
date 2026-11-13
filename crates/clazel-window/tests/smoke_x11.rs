//! Open a real window on an X server, draw in it and close it (phase-5.md item
//! 5.22). Linux only. A window briefly appears on the display `DISPLAY` names.
//!
//! **Without a display this is a skip, saying so**: when `DISPLAY` is not set or
//! names no local display, the test writes a line starting `clazel-window:
//! skipped` straight to standard error (past libtest's capture, so it is in CI's
//! log) and passes. CI's Linux job has no X server today; run it under one with
//! `xvfb-run -a cargo test -p clazel-window --test smoke_x11`. It was run that
//! way against Xvfb (X.Org 21.1.12) in an aarch64 Ubuntu 24.04 container.
//! Ignored under Miri, which has no sockets.

#![cfg(target_os = "linux")]

use std::io::Write;
use std::time::{Duration, Instant};

use clazel_window::pattern::test_pattern;
use clazel_window::{Event, Window, has_display};

/// Everything that needs a window runs in one test, as on Windows.
#[test]
#[cfg_attr(miri, ignore)]
fn a_window_opens_draws_reports_and_closes() {
    if !has_display() {
        let mut err = std::io::stderr().lock();
        let _ignored = err.write_all(b"clazel-window: skipped: DISPLAY names no local X display\n");
        return;
    }
    let opened = Window::open("clazel-window smoke test");
    assert!(opened.is_ok(), "open failed: {opened:?}");
    let Ok(mut window) = opened else { return };

    let (width, height) = window.size();
    assert!(width > 0 && height > 0, "window {width} by {height}");

    // The strip, then a page below it in the child window.
    let strip = test_pattern(width, 36, 0, None);
    let drew = window.draw(&strip, width, 36);
    assert!(drew.is_ok(), "draw failed: {drew:?}");
    let page = test_pattern(300, 200, 1, None);
    let shown = window.show_page_pixels(&page, (0, 36), 300, 200);
    assert!(shown.is_ok(), "show_page_pixels failed: {shown:?}");

    // The wrong length is refused, not sent.
    assert!(window.draw(&strip, width.saturating_add(1), 36).is_err());
    assert!(window.show_page_pixels(&page, (0, 36), 300, 201).is_err());

    // A title with characters outside Latin-1, and one with a NUL.
    let titled = window.set_title("clazel-window — smoke test, renamed");
    assert!(titled.is_ok(), "set_title failed: {titled:?}");
    assert!(window.set_title("a\0b").is_err());
    assert_eq!(window.dpi(), Some(96));

    // A mapped window is told to draw: the server answered every request before.
    let deadline = Instant::now().checked_add(Duration::from_secs(10));
    let mut exposed = false;
    while !exposed && deadline.is_some_and(|d| Instant::now() < d) {
        exposed = window.next_event(Duration::from_millis(100)) == Some(Event::Expose);
    }
    assert!(exposed, "no Expose within ten seconds");
    assert!(window.hide_page().is_ok());

    // Closing is reported, and nothing follows it.
    window.close();
    let mut closed = false;
    while !closed && deadline.is_some_and(|d| Instant::now() < d) {
        closed = window.next_event(Duration::from_millis(100)) == Some(Event::Closed);
    }
    assert!(closed, "no Closed within ten seconds");
    assert_eq!(window.next_event(Duration::from_millis(10)), None);
    assert_eq!(window.dpi(), None);
    drop(window);
}
