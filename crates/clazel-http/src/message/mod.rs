//! HTTP/1.1 message framing (RFC 9112), as a client sees it: the status
//! line, field lines, the message body length, the chunked coding, and the
//! request serializer.
//!
//! - [`spec`]: a transcription of the RFC.
//! - [`termination`]: why the spec's recursive functions terminate.
//! - [`contract`]: what the executable functions are proven to satisfy,
//!   and the properties of the spec an incremental parser relies on.

pub mod contract;
pub mod examples;
pub mod spec;
pub mod termination;
