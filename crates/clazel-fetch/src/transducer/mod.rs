//! The client state machine (phase-3.md item 3.6): a pure transducer from
//! the events of the connections it asks for to the actions the network
//! shell carries out.
//!
//! - [`spec`]: the transducer, citing RFC 9110, RFC 9112 and the Fetch
//!   Standard.
//! - [`contract`]: what the executable functions are proven to satisfy,
//!   the traits the HTTP and URL functions are passed as, and the
//!   theorems' statements.
//! - [`step`] and [`types`]: the executable transducer.
//! - [`theorems`]: the proofs of the theorems.
//! - [`real`]: the parameters joined to the real parsers.
//! - [`examples`]: concrete fetches evaluated on the spec.
//! - [`independent`]: Fetch's HTTP-redirect fetch and cookie steps,
//!   transcribed separately and proven to agree with the spec step by step.

pub mod contract;
pub mod examples;
pub mod independent;
pub mod real;
pub mod spec;
pub mod step;
pub mod theorems;
pub mod types;
