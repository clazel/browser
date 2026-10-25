//! The client state machine (phase-3.md item 3.6): a pure transducer from
//! the events of the connections it asks for to the actions the network
//! shell carries out.
//!
//! - [`spec`]: the transducer, citing RFC 9110 and RFC 9112.
//! - [`contract`]: what the executable functions are proven to satisfy,
//!   the trait the HTTP functions are passed as, and the theorems'
//!   statements.

pub mod contract;
pub mod real;
pub mod spec;
pub mod step;
pub mod theorems;
pub mod types;
pub mod examples;
