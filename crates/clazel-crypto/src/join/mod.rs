//! The join (path-validation design P16): the production
//! `clazel_tls::auth::spec::ChainValidation` and the executable
//! `clazel_tls::auth::verify::Verifier` that `clazel-tls`'s authentication
//! machine runs, over `clazel_x509::path`'s chain verifier and the link
//! signatures of [`crate::chain`].

pub mod spec;

pub mod contract;
