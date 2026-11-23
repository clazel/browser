//! The JavaScript engine's embedding API (phase-7.md item 7.8, "The engine as
//! a library").
//!
//! **This is the contract, and its first implementation** (phase-7.md item
//! 7.8, first part), over `clazel-js-vm`'s interpreter and
//! `clazel-js-builtins`. Every type and signature is the reviewed contract;
//! what the VM does not have yet (arrays, promises, symbols, BigInt,
//! ArrayBuffer, modules, a second realm, a collector) returns
//! [`Error::NotImplemented`], and the README's "What is implemented" section
//! lists each item with its reason. The README also states the rules in prose
//! (threads, rooting, termination, what is left out) and lists the open
//! questions. The doc comments carry examples that run, except the few that
//! need what is not there yet, which stay `no_run` and say so.
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
mod state;
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
pub use native::{Args, Callable, Exotic, HostObject, NativeFn, SharedNativeFn, Tracer};
pub use runtime::{Config, JitMode, Limits, Runtime, Terminator};
pub use scope::{Resolvers, Scope};
pub use value::{
    Handle, Key, Local, Member, PromiseState, PropertyDescriptor, ValueKind, Weak, WellKnownSymbol,
};
