//! The browser kernel (phase-2.md items 2.10 to 2.12): a pure step function
//! `step(State, Event) -> (State, Seq<Output>)` through which every byte a
//! renderer sends passes, and the isolation theorems about it.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: state, events, outputs and `step` (item 2.10).
//! - [`invariant`]: `kernel_wf`, the reachable-state invariant, and the
//!   facts proven about it.
//! - [`domain`]: domains, observations and the intransitive purge that
//!   item 2.11's noninterference theorem is stated with.
//! - [`contract`]: what the executable `step` (item 2.12) must satisfy.
//! - `exec`: the executable kernel (item 2.12): exec state, events and
//!   outputs with views to the spec's, and `step_exec`, proven to meet
//!   [`contract`] for any implementation of the URL functions.
//! - [`urls`]: the URL functions of the shipped kernel (item 2.13), built from
//!   the real URL parser; [`exec::real_urls`] is their executable
//!   implementation and `step_real`, the function the host shell calls;
//!   [`real_theorems`] states the isolation theorems for them.

pub mod contract;
pub mod cookie_theorems;
pub mod counterexamples;
pub mod domain;
pub mod exec;
pub mod independent;
pub mod independent_equivalence;
pub mod invariant;
pub mod lock;
pub mod mutation_lemmas;
pub mod net_rel;
pub mod net_theorems;
pub mod net_wf;
pub mod ni_theorem;
pub mod noninterference;
pub mod projection;
pub mod quark;
pub mod real_theorems;
pub mod retrieval_projection;
pub mod spec;
pub mod statements;
pub mod store_projection;
pub mod theorems;
pub mod unwind_base;
pub mod unwinding;
pub mod unwinding_b;
pub mod unwinding_d;
pub mod url_mutation_lemmas;
pub mod urls;
