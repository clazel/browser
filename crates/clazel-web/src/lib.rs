//! The web platform APIs for scripts (phase-7.md items 7.13 to 7.17).
//!
//! So far the engine-independent core of item 7.13's `innerHTML` and
//! `outerHTML`: [`serialize`], the HTML serialization algorithm (HTML
//! §13.3†); and of its `querySelector`, `querySelectorAll`, `matches` and
//! `closest`: [`selectors`], over `clazel-selectors`. The fragment parsing half is `clazel-treebuilder`'s
//! `exec::driver::parse_fragment_real`. The rest arrives with items 7.13 to
//! 7.17; item 7.1 vendored the WPT `testharness.js` tests and the TodoMVC
//! implementations that later items run.
//!
//! Item 7.14's engine-independent core is [`events`]: DOM event dispatch
//! (§2.9†) with the listener lists, over the same arena.
//!
//! Tier 0 (`Cargo.toml`): safe Rust, tested, nothing proven.

pub mod events;
pub mod selectors;
pub mod serialize;
