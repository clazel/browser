//! The HTTP client of the Clazel browser, formally verified with Verus.
//!
//! Phase 3 item 3.6, first part: [`request`] builds the request for an
//! `http:` URL (a GET, one per connection, no redirects and no cookies
//! yet). The response is read by `clazel_http::message`. Tier: see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod request;
