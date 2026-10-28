//! The executable kernel (phase-2.md item 2.12): `step` over exec records,
//! proven to meet [`crate::contract`].
//!
//! - [`records`]: the exec state, event and output types and their views.
//! - [`urls`]: [`urls::UrlFnsExec`], the exec counterpart of
//!   [`crate::spec::UrlFns`].
//! - [`real_urls`]: [`real_urls::RealUrls`], the URL functions with the real
//!   parser (item 2.13), [`real_urls::RealFetch`], the transducer's real
//!   functions (item 3.7), and [`real_urls::step_real`], `step` with them.
//! - [`fetch`]: [`fetch::FetchFnsExec`], the exec counterpart of
//!   [`crate::spec::FetchFns`] (item 3.7).
//! - [`locks`]: locks, cookie-averse documents and cookie requests.
//! - [`frames`]: the frames sent to renderers.
//! - [`storage`]: Web Storage over the exec buckets.
//! - [`step`]: `step` itself.

/// The spec, under the name `super::spec` that the submodules' ghost imports
/// use (the one spelling of that import the lint check allows).
pub use crate::spec;

pub mod fetch;
pub mod frames;
pub mod locks;
pub mod real_urls;
pub mod records;
pub mod step;
pub mod storage;
pub mod urls;
