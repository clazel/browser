//! WebIDL bindings (phase-7.md item 7.12): the glue between the JavaScript
//! engine (`clazel-js`, through its public API only) and the platform
//! objects of `clazel-web`.
//!
//! - [`generated`] holds the resolved model of the vendored IDL (the DOM,
//!   HTML, Fetch, XHR, URL and Storage standards, UI Events and CSSOM, in
//!   `tests/data/webref-idl/`) as plain data of the types in [`model`], and
//!   [`generated::bindings`], the binding glue for the interfaces the
//!   browser exposes: a trait per interface for the platform to implement,
//!   a native function per member, and the code that installs interface
//!   objects and prototypes. `cargo xtask bindings` writes both with our
//!   own IDL parser (`xtask/src/bindings/`), and `cargo xtask check` fails
//!   if they are stale.
//! - [`convert`]: the ECMAScript type mapping (WebIDL §3.2†).
//! - [`overload`]: the overload resolution algorithm (§3.6†).
//! - [`platform`]: platform objects and their wrappers (§3.7†, §3.8†), the
//!   [`platform::Platform`] trait the embedder implements, and
//!   `[SameObject]`.
//! - [`install`]: interface objects, prototypes, attributes, operations and
//!   constants (§3.7†), `[Replaceable]` and `[PutForwards]`.
//! - [`exception`]: `DOMException` (§2.8.1†, §4.3†).
//!
//! Section numbers carry the mark † of phase-7.md: WebIDL is not vendored
//! at a pinned commit, so they are from the living standard as read for
//! this item. The README lists what is not done.

pub mod convert;
pub mod exception;
pub mod install;
pub mod model;
pub mod overload;
pub mod platform;

#[rustfmt::skip]
pub mod generated;
