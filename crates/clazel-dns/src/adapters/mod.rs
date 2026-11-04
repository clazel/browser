//! The DNS servers in the buffer Windows' `GetAdaptersAddresses` fills.
//!
//! - [`spec`]: the layout read and the walk of the adapter and server lists
//!   (no standard defines them: C structures of the Windows SDK) as spec
//!   functions.
//! - [`contract`]: what the executable reader is proven to satisfy.
//! - [`parse`]: the executable reader, and [`lemmas`], facts it needs.
//! - [`examples`]: the spec evaluated on small buffers.

pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod parse;
pub mod spec;
