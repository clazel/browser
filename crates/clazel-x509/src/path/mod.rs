//! RFC 5280 §6.1 certification path validation, in pieces: the parsed form
//! a path is validated over (`parsed`), the §6.1 transcription (`spec`), the
//! browser profile on top of it (`profile`) and the verdict on a presented
//! chain (`verifier`). Candidate-path enumeration is not written yet.

pub mod contract;
pub mod examples;
pub mod mutation_certificates;
pub mod parsed;
pub mod profile;
pub mod spec;
pub mod theorems;
pub mod verifier;
