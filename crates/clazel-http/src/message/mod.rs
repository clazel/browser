//! HTTP/1.1 message framing (RFC 9112), as a client sees it: the status
//! line, field lines, the message body length, the chunked coding, and the
//! request serializer.
//!
//! - [`spec`]: a transcription of the RFC.
//! - [`termination`]: why the spec's recursive functions terminate.
//! - [`contract`]: what the executable functions are proven to satisfy,
//!   and the properties of the spec an incremental parser relies on.
//! - [`lemmas`]: those properties, proven.
//! - [`incremental`]: the parser fed bytes as they arrive.
//! - [`request`]: the request parser (a spec) and the serializer's
//!   round trip; [`request_parser`]: the request parser, executable.

pub mod body;
pub mod contract;
pub mod examples;
pub mod incremental;
pub mod lemmas;
pub mod line;
pub mod request;
pub mod request_parser;
pub mod serialize;
pub mod spec;
pub mod termination;
#[cfg(test)]
mod tests;
pub mod types;
