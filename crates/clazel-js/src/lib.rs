//! The JavaScript engine's embedding API (phase-7.md item 7.8, "The engine as
//! a library").
//!
//! **This crate is the contract and nothing else.** Every type and signature
//! is the proposed API, and every operation that needs the engine returns
//! [`Error::NotImplemented`]. The README states the rules in prose (threads,
//! rooting, termination, what is left out) and lists the open questions; the
//! doc comments here carry examples that compile (`no_run`, since nothing
//! runs yet). The contract is for review before the bindings build on it.
//!
//! The pieces, in the order a program meets them:
//!
//! - [`Runtime`], [`Config`], [`Limits`] and [`Terminator`]: one agent, its
//!   limits, and the handle that stops it from another thread.
//! - [`Scope`]: every operation, inside [`Runtime::scope`]. Its values are
//!   [`Local`]s; [`Handle`], [`Weak`] and [`Member`] hold them longer.
//! - [`Realm`], [`Source`], [`Script`] and [`Module`]: code to run.
//! - [`Scope::function`], [`Args`] and [`HostObject`]: Rust inside JavaScript.
//! - [`Host`]: what ECMA-262 leaves to the embedder, and [`DefaultHost`].
//! - [`Error`], [`Exception`] and [`ErrorReport`]: what goes wrong.
//!
//! An embedder names this crate and no other engine crate.

mod code;
mod error;
mod host;
mod native;
mod runtime;
mod scope;
mod value;

pub use code::{
    ImportAttribute, LoadPayload, Module, ModuleRequest, ModuleStatus, Realm, RealmOptions,
    Referrer, Script, Source,
};
pub use error::{Error, ErrorKind, ErrorReport, Exception, Result, StackFrame};
pub use host::{
    CompileStrings, DefaultHost, DynamicCodeKind, Host, Job, JobCallback, RejectionOperation,
    Resize,
};
pub use native::{Args, Callable, Exotic, HostObject, NativeFn, Tracer};
pub use runtime::{Config, JitMode, Limits, Runtime, Terminator};
pub use scope::{Resolvers, Scope};
pub use value::{
    Handle, Key, Local, Member, PromiseState, PropertyDescriptor, ValueKind, Weak, WellKnownSymbol,
};
