//! The network shell (Phase 3 item 3.8), `http://` half: it carries bytes
//! between the right socket and its caller and decides nothing about them.
//!
//! - [`resolve`]: a host name to addresses. Every decision about the bytes
//!   (reading `resolv.conf`, building the query, accepting the reply, framing
//!   over TCP) is made by a proven function of `clazel-dns`.
//! - [`run`]: connect to the addresses in order, send the request bytes in
//!   full, and hand every chunk that arrives to a callback until it says stop
//!   or the peer closes.
//!
//! The shell never parses HTTP and never builds a request. It is Tier 0: it
//! does I/O, so tests are its only evidence (`docs/VERIFICATION.md`).

mod conn;
mod error;
mod resolve;

pub use conn::{Finish, Flow, Timeouts, connect, run, run_with};
pub use error::{NetError, ResolveError, Stage};
pub use resolve::resolve;
