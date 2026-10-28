//! The HTML tokenizer (HTML §13.2.3.5, §13.2.4, §13.2.5).
//!
//! - [`spec`]: a state-by-state transcription of the standard. This is the
//!   part a human must check against the standard.
//! - [`termination`]: why the spec's state machine terminates.
//! - [`actions`]: the executable actions the states share.
//! - [`buffer`]: the executable state and tokens, and their views.
//! - [`contract`]: what the executable tokenizer is proven to satisfy.
//! - [`machine`]: the executable tokenizer's step, `next_token` and
//!   `tokenize`, and their proofs; the states are in [`states_text`],
//!   [`states_markup`] and [`states_ref`], their shared actions in
//!   [`actions`].
//! - [`lemmas`]: facts proven about the spec.
//! - [`examples`]: inputs evaluated on the spec.
//! - [`output`]: `theorem_output_bounded`.

pub mod actions;
pub mod agreement;
pub mod buffer;
pub mod contract;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod machine;
pub mod output;
pub mod spec;
pub mod states_markup;
pub mod states_ref;
pub mod states_text;
pub mod termination;
