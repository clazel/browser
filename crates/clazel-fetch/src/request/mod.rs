//! From a URL to the request to send.
//!
//! - [`spec`]: what the request is, citing RFC 9112 §3.2.1 and RFC 9110
//!   §4.2.4, §7.2 and §15.2.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod build;
pub mod contract;
pub mod examples;
pub mod spec;
