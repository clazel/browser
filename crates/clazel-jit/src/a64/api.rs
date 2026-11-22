//! The contract-only API of the A64 back end: a trait with no implementation,
//! so Verus accepts it with no escape hatch (CLAUDE.md rule 4), the pattern of
//! [`crate::api`]. The implementation (the next commit) implements it.
//!
//! The input is [`Op`]s, as for x86-64: LIR's own `Instr` holds proof-only
//! numbers and sequences, and the JS front end (J.10) will have its own
//! executable form. [`Op`]'s `view` says which LIR instruction each stands for.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The LIR → A64 back end, with its contracts.
pub trait Backend {
    /// The A64 instructions for the straight-line program `ops`, in a
    /// function with `nl` locals, entered with an empty operand stack (see
    /// [`crate::a64::contract::emit_body_ensures`]).
    fn emit_body(ops: &[Op], nl: usize) -> (r: Option<Vec<isa::Instr>>)
        requires
            crate::a64::contract::emit_requires(ops@, nl),
        ensures
            crate::a64::contract::emit_body_ensures(ops@, nl, match r {
                Some(v) => Some(v@),
                None => None,
            }),
    ;

    /// The bytes of a blob: the canonical encoding of the body, then the exit
    /// sequence for `exit_code` (see [`crate::a64::contract::emit_blob_ensures`]).
    fn emit_blob(ops: &[Op], nl: usize, exit_code: u16) -> (r: Option<Vec<u8>>)
        requires
            crate::a64::contract::emit_requires(ops@, nl),
        ensures
            crate::a64::contract::emit_blob_ensures(ops@, nl, exit_code, match r {
                Some(v) => Some(v@),
                None => None,
            }),
    ;
}

} // verus!
