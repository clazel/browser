//! Open a real window, draw in it and close it (phase-5.md item 5.22a). Windows
//! only, since no other target has a window yet. A window briefly appears.

#![cfg(windows)]

use std::time::{Duration, Instant};

use clazel_window::pattern::test_pattern;
use clazel_window::{Event, Window};

/// Everything that needs a window runs in one test: two windows at once would
/// compete for focus and paint order, and the assertions do not need that.
#[test]
fn a_window_opens_draws_reports_and_closes() {
    let opened = Window::open("clazel-window smoke test");
    assert!(opened.is_ok(), "open failed: {opened:?}");
    let Ok(mut window) = opened else { return };

    let (width, height) = window.size();
    assert!(width > 0 && height > 0, "client area {width} by {height}");

    let pixels = test_pattern(width, height, 0, None);
    let drew = window.draw(&pixels, width, height);
    assert!(drew.is_ok(), "draw failed: {drew:?}");

    // The wrong length is refused, not read.
    assert!(
        window
            .draw(&pixels, width.saturating_add(1), height)
            .is_err()
    );

    // A new window is told to paint, through the real message thread.
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut exposed = false;
    while !exposed && Instant::now() < deadline {
        exposed = window.next_event(Duration::from_millis(100)) == Some(Event::Expose);
    }
    assert!(exposed, "no WM_PAINT within ten seconds");

    // Dropping closes the window and ends the thread, rather than hanging.
    drop(window);
}
