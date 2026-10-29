//! The two transcriptions of HTML §13.2.3.2's prescan agree on every input:
//! [`super::independent_prescan::prescan`] (written from the standard's text
//! without reading `spec.rs`) equals [`super::spec::prescan`] for all bytes,
//! with no exclusions. Both read the same text, so this is a same-text
//! check: it catches a misreading made by one transcriber but not the other.
//!
//! Where the two differ in form, the proof bridges them:
//! - searches started at different bytes (the comment end from `<` + 1 or
//!   from `<!--` + 4, the tag end from `<` or from `<` + 1);
//! - "starts with" as a subrange comparison or as one test per byte;
//! - "already in attribute list" scanned from the front or from the back;
//! - *charset* as an enum or as nested options;
//! - "extracting a character encoding from a meta element", step 6
//!   "Otherwise", when "this character" is 0x3B (;): `spec.rs` takes the
//!   empty substring, the other text takes the 0x3B and what follows up to
//!   the next whitespace or 0x3B. "Get an encoding" fails on both: no label
//!   is empty and none has a 0x3B (proven from the label table).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The independent transcription of the prescan equals the spec's, on
/// every input.
pub proof fn lemma_prescan_agrees(b: Seq<u8>)
    ensures
        super::independent_prescan::prescan(b) == super::spec::prescan(b),
{
}

} // verus!
