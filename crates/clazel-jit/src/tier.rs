//! The tiering counters' policy (docs/phases/jit.md items J.10 and J.11): when
//! does a function in the interpreter loop get compiled?
//!
//! > Compile after N entries or loop back-edges ... Code that runs once stays
//! > in the interpreter loop. (J.10)
//!
//! > The estimate is 30 to 150 runs per function at the baseline tier, which
//! > is where the tiering threshold N starts. (J.11)
//!
//! The defaults below are those starting values, **not measurements**: J.11's
//! break-even measurement (compile, validation and mapping cost against the
//! interpreter's per-run cost) sets them later.
//!
//! The policy is plain functions over plain numbers, so it is tested at small
//! values and is easy to read. It has no clock and no randomness.
//!
//! # Backoff
//!
//! A function that has been evicted (or whose version changed, through
//! inline-cache churn) must earn its next compilation again, at a threshold
//! that doubles with each such *strike*, up to [`MAX_BACKOFF_SHIFT`] doublings.
//! Without this a page that cycles through more hot functions than the
//! budget holds would compile, evict and recompile for ever.

use crate::limits::Fallback;

/// Entries before a function is compiled (inside J.11's 30 to 150).
pub const DEFAULT_ENTRY_THRESHOLD: u32 = 50;

/// Loop back-edges before a function is compiled. A back-edge is cheaper than
/// a call, so the number is larger; it is what lets a function that is entered
/// once and loops for ever be compiled (J.10: entry at a loop head).
pub const DEFAULT_BACK_EDGE_THRESHOLD: u32 = 1000;

/// The threshold doubles per strike up to this many doublings (a factor of
/// 1024).
pub const MAX_BACKOFF_SHIFT: u32 = 10;

/// The thresholds that trigger a compile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Thresholds {
    /// Entries (calls) of the function.
    pub entries: u32,
    /// Loop back-edges taken in the function.
    pub back_edges: u32,
}

impl Default for Thresholds {
    fn default() -> Thresholds {
        Thresholds {
            entries: DEFAULT_ENTRY_THRESHOLD,
            back_edges: DEFAULT_BACK_EDGE_THRESHOLD,
        }
    }
}

/// One function version's counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counters {
    /// Entries so far.
    pub entries: u32,
    /// Back-edges so far.
    pub back_edges: u32,
}

impl Counters {
    /// Count an entry. Saturates.
    pub fn enter(&mut self) {
        self.entries = self.entries.saturating_add(1);
    }

    /// Count a back-edge. Saturates.
    pub fn back_edge(&mut self) {
        self.back_edges = self.back_edges.saturating_add(1);
    }
}

/// Where a function is in its life.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// In the interpreter loop, counting.
    Interpreting,
    /// A compile was requested and has not come back. No second request is
    /// made meanwhile.
    Compiling,
    /// Its blob is (or was, until an eviction says otherwise) in the cache.
    Compiled,
    /// Never to be compiled at this version, for this reason.
    Refused(Fallback),
}

/// What made the function hot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trigger {
    /// Enough entries.
    Entries,
    /// Enough loop back-edges.
    BackEdges,
}

/// What to do now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Keep interpreting.
    Stay,
    /// Compile the function.
    Compile(Trigger),
}

/// `base`, doubled once per strike, at most [`MAX_BACKOFF_SHIFT`] times, and
/// never below 1.
pub fn threshold_after(base: u32, strikes: u32) -> u32 {
    let doublings = strikes.min(MAX_BACKOFF_SHIFT);
    base.max(1).saturating_mul(2u32.saturating_pow(doublings))
}

/// Whether to compile a function with these counters and `strikes`.
///
/// Only a function that is `Interpreting` is ever compiled; entries are
/// checked before back-edges, so the trigger is the first threshold reached.
pub fn decide(c: &Counters, t: &Thresholds, strikes: u32, state: State) -> Decision {
    if state != State::Interpreting {
        return Decision::Stay;
    }
    if c.entries >= threshold_after(t.entries, strikes) {
        Decision::Compile(Trigger::Entries)
    } else if c.back_edges >= threshold_after(t.back_edges, strikes) {
        Decision::Compile(Trigger::BackEdges)
    } else {
        Decision::Stay
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_entry_threshold_is_in_the_estimated_range() {
        const { assert!(DEFAULT_ENTRY_THRESHOLD >= 30 && DEFAULT_ENTRY_THRESHOLD <= 150) };
        const { assert!(DEFAULT_BACK_EDGE_THRESHOLD > DEFAULT_ENTRY_THRESHOLD) };
    }

    #[test]
    fn code_that_runs_once_stays_interpreted() {
        let t = Thresholds::default();
        let mut c = Counters::default();
        c.enter();
        assert_eq!(decide(&c, &t, 0, State::Interpreting), Decision::Stay);
    }

    #[test]
    fn compiles_exactly_at_the_entry_threshold() {
        let t = Thresholds {
            entries: 5,
            back_edges: 100,
        };
        let mut c = Counters::default();
        for n in 1..=5u32 {
            c.enter();
            let want = if n < 5 {
                Decision::Stay
            } else {
                Decision::Compile(Trigger::Entries)
            };
            assert_eq!(
                decide(&c, &t, 0, State::Interpreting),
                want,
                "after {n} entries"
            );
        }
    }

    #[test]
    fn a_loop_entered_once_compiles_on_back_edges() {
        let t = Thresholds {
            entries: 5,
            back_edges: 7,
        };
        let mut c = Counters::default();
        c.enter();
        for _ in 0..6 {
            c.back_edge();
        }
        assert_eq!(decide(&c, &t, 0, State::Interpreting), Decision::Stay);
        c.back_edge();
        assert_eq!(
            decide(&c, &t, 0, State::Interpreting),
            Decision::Compile(Trigger::BackEdges)
        );
    }

    #[test]
    fn entries_win_when_both_are_reached() {
        let t = Thresholds {
            entries: 1,
            back_edges: 1,
        };
        let c = Counters {
            entries: 1,
            back_edges: 1,
        };
        assert_eq!(
            decide(&c, &t, 0, State::Interpreting),
            Decision::Compile(Trigger::Entries)
        );
    }

    #[test]
    fn only_an_interpreting_function_is_compiled() {
        let t = Thresholds {
            entries: 1,
            back_edges: 1,
        };
        let c = Counters {
            entries: 1_000,
            back_edges: 1_000,
        };
        for st in [
            State::Compiling,
            State::Compiled,
            State::Refused(Fallback::FunctionTooLarge),
        ] {
            assert_eq!(decide(&c, &t, 0, st), Decision::Stay);
        }
    }

    #[test]
    fn strikes_double_the_threshold_up_to_a_cap() {
        assert_eq!(threshold_after(50, 0), 50);
        assert_eq!(threshold_after(50, 1), 100);
        assert_eq!(threshold_after(50, 3), 400);
        assert_eq!(threshold_after(50, MAX_BACKOFF_SHIFT), 50 * 1024);
        assert_eq!(threshold_after(50, MAX_BACKOFF_SHIFT + 5), 50 * 1024);
        assert_eq!(threshold_after(50, u32::MAX), 50 * 1024);
    }

    #[test]
    fn threshold_never_overflows_or_reaches_zero() {
        assert_eq!(threshold_after(0, 0), 1);
        assert_eq!(threshold_after(u32::MAX, 10), u32::MAX);
        let t = Thresholds {
            entries: 0,
            back_edges: 0,
        };
        assert_eq!(
            decide(&Counters::default(), &t, 0, State::Interpreting),
            Decision::Stay
        );
    }

    #[test]
    fn a_struck_function_needs_more_entries() {
        let t = Thresholds {
            entries: 4,
            back_edges: 1000,
        };
        let mut c = Counters::default();
        for _ in 0..4 {
            c.enter();
        }
        assert_eq!(
            decide(&c, &t, 0, State::Interpreting),
            Decision::Compile(Trigger::Entries)
        );
        assert_eq!(decide(&c, &t, 1, State::Interpreting), Decision::Stay);
        for _ in 0..4 {
            c.enter();
        }
        assert_eq!(
            decide(&c, &t, 1, State::Interpreting),
            Decision::Compile(Trigger::Entries)
        );
    }

    #[test]
    fn counters_saturate() {
        let mut c = Counters {
            entries: u32::MAX,
            back_edges: u32::MAX,
        };
        c.enter();
        c.back_edge();
        assert_eq!(
            c,
            Counters {
                entries: u32::MAX,
                back_edges: u32::MAX
            }
        );
    }
}
