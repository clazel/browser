//! The HTTP client of the Clazel browser, formally verified with Verus.
//!
//! Phase 3 item 3.6: [`request`] builds the request for an `http:` URL (a
//! GET, one per connection, no cookies yet), and [`transducer`] is the
//! client state machine the network shell drives: from the URL and the
//! events of its connections to the actions to carry out, following
//! redirects. The response is read by `clazel_http::message`. Tier: see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod request;
pub mod transducer;
