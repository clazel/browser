//! RFC 5280 §6.1 certification path validation, in pieces: the parsed form
//! a path is validated over (`parsed`), the §6.1 transcription (`spec`), the
//! browser profile on top of it (`profile`), the verdict on a presented
//! chain (`verifier`), the executable fold and verdict on one candidate
//! (`exec`, against `contract`) and the proofs of the stated theorems
//! (`lemmas`, of `theorems`), and the candidate search over a presented
//! chain (`search`, P9).

pub mod contract;
pub mod examples;
pub mod exec;
pub mod independent;
pub mod independent_equivalence;
pub mod lemmas;
pub mod mutation_certificates;
pub mod parsed;
pub mod profile;
pub mod search;
pub mod spec;
pub mod theorems;
pub mod verifier;
