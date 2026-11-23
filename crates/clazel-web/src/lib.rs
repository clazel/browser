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
//! Items 7.14 and 7.15's event loop is [`event_loop`]: task queues, the
//! microtask checkpoint and `setTimeout`/`setInterval` (HTML §8.1.7† and
//! §8.6†), with caps for a hostile page (7.19) and time supplied by the
//! caller.
//!
//! Item 7.15's script half is [`scripting`]: a document parsed with the
//! scripting flag on, its `script` elements prepared and run as the parser
//! reaches them, `document.write`, `document.open` and `document.close`,
//! module scripts as far as the engine goes, `javascript:` URLs and
//! `performance.now()`, through `clazel-js`'s embedding API.
//!
//! Item 7.12's platform is [`page`]: the page's platform objects (the DOM,
//! events, `Window`, `Location`, `History`, `Navigator`, `console`) exposed
//! to script through `clazel-webidl`'s generated bindings and `clazel-js`'s
//! embedding API.
//!
//! Tier 0 (`Cargo.toml`): safe Rust, tested, nothing proven.

pub mod event_loop;
pub mod events;
pub mod page;
pub mod scripting;
pub mod selectors;
pub mod serialize;
