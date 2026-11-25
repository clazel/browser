//! `performance.now()` (High Resolution Time §?†, "Performance.now()"),
//! coarsened to 100 µs (phase-7.md, "What is proven, and what is assumed",
//! item 5: the defence against timing side channels inside a renderer is one
//! site per renderer, no `SharedArrayBuffer`, and `performance.now()`
//! coarsened to 100 µs).
//!
//! <https://w3c.github.io/hr-time/#dom-performance-now>: "The now() method
//! MUST return the current high resolution time given this's relevant
//! global object", which is "the relative high resolution time given
//! unsafeNow and global" with "coarsen time" applied. HR-Time leaves the
//! coarsening's resolution to the user agent (at least 100 µs without
//! cross-origin isolation, 5 µs with it); this browser has no cross-origin
//! isolated pages and uses 100 µs for every page.
//!
//! Modelling choices: the clock is the embedder's ([`Clock`], a monotonic
//! count of microseconds); the time origin is the page's creation (the
//! "time origin" of a Window is the start of its navigation, which the page
//! does not see); "coarsen time" rounds down to a multiple of the
//! resolution, with no jitter (HR-Time permits either).

use std::time::Instant;

/// The resolution `performance.now()` is coarsened to, in microseconds.
pub const RESOLUTION_US: u64 = 100;

/// A monotonic clock, in microseconds from any fixed start. The embedder's,
/// as every clock of the engine is (phase-7.md, "The engine as a library").
pub trait Clock: Send {
    /// Microseconds since the clock's start. Never smaller than a value it
    /// returned before.
    fn now_us(&mut self) -> u64;
}

/// The standard library's monotonic clock.
#[derive(Debug)]
pub struct SystemClock {
    start: Instant,
}

impl SystemClock {
    /// A clock that starts now.
    pub fn new() -> SystemClock {
        SystemClock {
            start: Instant::now(),
        }
    }
}

impl Default for SystemClock {
    fn default() -> SystemClock {
        SystemClock::new()
    }
}

impl Clock for SystemClock {
    fn now_us(&mut self) -> u64 {
        u64::try_from(self.start.elapsed().as_micros()).unwrap_or(u64::MAX)
    }
}

/// HR-Time "coarsen time" for a duration in microseconds: rounded down to a
/// multiple of [`RESOLUTION_US`].
pub fn coarsen_us(us: u64) -> u64 {
    us.saturating_sub(us.checked_rem(RESOLUTION_US).unwrap_or(0))
}

/// The value `performance.now()` returns, in milliseconds, for a clock
/// reading `now_us` and a time origin `origin_us` on the same clock: the
/// coarsened duration since the origin (zero if the clock reads earlier).
pub fn performance_now_ms(origin_us: u64, now_us: u64) -> f64 {
    let since = coarsen_us(now_us.saturating_sub(origin_us));
    // Exact up to 2^53 µs (285 years); past that it rounds, as a double
    // does.
    since as f64 / 1000.0
}
