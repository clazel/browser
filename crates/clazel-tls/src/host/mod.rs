//! The typed target host (path-validation design Q2): a DNS name or an IP
//! address, as the URL layer produces it. ClientHello's server_name and the
//! certificate check both read it.
pub mod certificates;
pub mod examples;
pub mod exec;
pub mod spec;
