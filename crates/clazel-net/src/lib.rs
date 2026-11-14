//! The network shell (Phase 3 item 3.8): it carries bytes
//! between the right socket and its caller and decides nothing about them.
//!
//! - [`resolve`]: a host name to addresses. Every decision about the bytes
//!   (reading `resolv.conf`, building the query, accepting the reply, framing
//!   over TCP) is made by a proven function of `clazel-dns`.
//! - [`run`]: connect to the addresses in order, send the request bytes in
//!   full, and hand every chunk that arrives to a callback until it says stop
//!   or the peer closes; [`Connection`], the same one step at a time.
//!
//! - [`fetch`]: an `http://` or `https://` GET and its redirects, driven end to end by
//!   `clazel-fetch`'s proven transducer: the shell carries out its actions
//!   (connect, send, close) and reports what happened (connected, bytes,
//!   closed, error).
//! - [`TlsConnection`]: TLS 1.3 over a [`Connection`], every decision made
//!   by `clazel_crypto::client`'s driver; [`fetch`] uses it for `https:`.
//!
//! The shell never parses HTTP and never builds a request. It is Tier 0: it
//! does I/O, so tests are its only evidence (`docs/VERIFICATION.md`).

mod conn;
mod driver;
mod error;
mod fetch;
mod frames;
mod named;
mod resolve;
mod tls;

/// The certificate verifier `TlsConnection` and `Driver` take, and the
/// trust anchors it is built from.
pub use clazel_crypto::join::exec::{ChainVerifier, Root};
pub use conn::{Connection, Finish, Flow, Timeouts, connect, run, run_with};
pub use driver::{Driver, InputBuf, Op, Report, TlsEnd};
pub use error::{NetError, ResolveError, Stage};
pub use fetch::{FetchError, fetch, fetch_jar, fetch_jar_verified, fetch_with, now_1601};
pub use frames::read_frames;
pub use named::{Name, SUB_BASE, SubConns};
pub use resolve::resolve;
pub use tls::TlsConnection;
