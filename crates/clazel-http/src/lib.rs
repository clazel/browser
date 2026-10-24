//! HTTP for the Clazel browser.
//!
//! Spec: RFC 9110 "HTTP Semantics" (June 2022),
//! <https://www.rfc-editor.org/rfc/rfc9110>. Tier: see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`field`]: field syntax (RFC 9110 §5, §8.6): names, values, lists,
//!   tokens, whitespace, quoted strings, parameters, `Content-Length`,
//!   `Transfer-Encoding` and `Connection`.
//! - [`message`]: message framing (RFC 9112 "HTTP/1.1", June 2022,
//!   <https://www.rfc-editor.org/rfc/rfc9112>): status line, field lines,
//!   message body length, chunked coding, and the request serializer.
//!   Phase 3 item 3.2; the spec and contracts come first, the
//!   implementation and its proof next.
//!
//! The conformance tests are Phase 3 item 3.3 and do not exist yet.

pub mod field;
pub mod message;
