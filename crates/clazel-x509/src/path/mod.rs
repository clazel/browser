//! RFC 5280 §6.1 certification path validation, in pieces: the parsed form
//! a path is validated over (`parsed`) and the §6.1 transcription (`spec`).
//! Candidate-path enumeration is not written yet.

pub mod parsed;
pub mod spec;
