//! UTF-16BE and UTF-16LE decoding (Encoding §14.2 to §14.4).
//!
//! - [`spec`]: a step-by-step transcription of the shared UTF-16 decoder.
//! - [`contract`]: what the executable decoder is proven to satisfy.
//! - [`decode`]: the executable decoder, and its proof.
//! - [`lemmas`]: facts proven about the spec.
//! - [`independent`]: a second transcription, with the standard's "restore"
//!   done literally on the queue, proven equal to [`spec`].

pub mod contract;
pub mod decode;
pub mod independent;
pub mod lemmas;
pub mod spec;
