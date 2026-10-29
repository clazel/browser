//! The parts of the transcription the insertion modes share: tag names,
//! tables, parse state, insertion helpers and the dispatcher.

pub mod dispatch;
pub mod insert;
pub mod join;
pub mod state;
pub mod tables;
pub mod tags;

pub use dispatch::*;
#[cfg(verus_only)]
pub use insert::*;
pub use join::*;
pub use state::*;
#[cfg(verus_only)]
pub use tables::*;
pub use tags::*;

/// Every name of the transcription, for the ghost imports of these modules
/// (`use super::spec::*;`).
mod spec {
    pub use crate::spec::*;
}
