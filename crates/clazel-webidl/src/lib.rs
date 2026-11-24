//! WebIDL bindings (phase-7.md item 7.12), first slice: the interface model.
//!
//! [`generated`] holds the resolved model of the vendored IDL (the DOM, HTML,
//! Fetch, XHR, URL and Storage standards, UI Events and CSSOM, in
//! `tests/data/webref-idl/`) as plain data of the types in [`model`]:
//! interfaces with their inheritance, members, argument and return types and
//! extended attributes, namespaces, dictionaries with their members and
//! defaults, enums, typedefs and callbacks. `cargo xtask bindings` writes it
//! with our own IDL parser (`xtask/src/bindings/`), and `cargo xtask check`
//! fails if it is stale.
//!
//! Not here yet: the JS-engine glue (conversions, overload resolution,
//! wrappers, `DOMException`). It needs `clazel-js`'s embedding API (item 7.8)
//! and is generated from this model.

pub mod model;

#[rustfmt::skip]
pub mod generated;
