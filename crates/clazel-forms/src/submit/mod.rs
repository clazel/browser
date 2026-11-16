//! Form encodings and the form submission algorithm (Phase 6 item 6.14).
//!
//! - [`spec`]: a step-by-step transcription of URL's
//!   `application/x-www-form-urlencoded` serializer, HTML's conversion of an
//!   entry list to name-value pairs, the `text/plain` and
//!   `multipart/form-data` encodings, "picking an encoding for the form" and
//!   the form submission algorithm's navigation steps.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod exec;
pub mod lemmas;
pub mod spec;
