//! The contract-only API of the back end: a trait with no implementation, so
//! Verus accepts it with no escape hatch (CLAUDE.md rule 4), the pattern of
//! `clazel-x64`'s and `clazel-codecheck`'s `api.rs`. The implementation (the
//! next commit) implements it, or replaces it with free functions whose
//! `requires` and `ensures` are the same predicates.
//!
//! The input is [`Op`]s, not `clazel_lir::spec::Instr`: LIR's own type holds
//! proof-only numbers and sequences, and the JS front end (J.10) will have its
//! own executable form. [`Op`]'s `view` says which LIR instruction each stands
//! for.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The LIR → x86-64 back end, with its contracts.
pub trait Backend {
    /// The x86-64 instructions for the straight-line program `ops`, in a
    /// function with `nl` locals, entered with an empty operand stack (see
    /// [`crate::contract::emit_body_ensures`]).
    fn emit_body(ops: &[Op], nl: usize) -> (r: Option<Vec<x64::Instr>>)
        requires
            crate::contract::emit_requires(ops@, nl),
        ensures
            crate::contract::emit_body_ensures(ops@, nl, match r {
                Some(v) => Some(v@),
                None => None,
            }),
    ;

    /// The bytes of a blob: the canonical encoding of the body, then the exit
    /// sequence for `exit_code` (see [`crate::contract::emit_blob_ensures`]).
    fn emit_blob(ops: &[Op], nl: usize, exit_code: u32) -> (r: Option<Vec<u8>>)
        requires
            crate::contract::emit_requires(ops@, nl),
        ensures
            crate::contract::emit_blob_ensures(ops@, nl, exit_code, match r {
                Some(v) => Some(v@),
                None => None,
            }),
    ;
}

} // verus!
