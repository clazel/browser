//! Sandbox policies as data (Phase 2 item 2.14).
//!
//! This crate generates and checks the policies that confine a renderer; it
//! makes no system calls and contains no `unsafe`. Applying them to a process
//! is item 2.15.
//!
//! - [`syscalls`]: the syscall allowlist, with the reason for each entry, and
//!   its numbers for x86-64 and aarch64.
//! - [`bpf`]: the classic BPF instruction format and opcodes.
//! - [`seccomp`]: the seccomp-BPF program generator.
//! - [`interp`]: a small classic-BPF validator and interpreter. It models the
//!   kernel, so it is part of the trusted computing base; the harnesses in
//!   `proofs.rs` run every generated program through it.
//! - [`landlock`], [`namespaces`], [`seatbelt`], [`appcontainer`]: the other
//!   policies.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod appcontainer;
pub mod bpf;
pub mod interp;
pub mod landlock;
pub mod namespaces;
pub mod seatbelt;
pub mod seccomp;
pub mod syscalls;

#[cfg(kani)]
mod proofs;
