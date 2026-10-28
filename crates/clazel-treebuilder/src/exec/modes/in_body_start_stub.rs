//! STUB, TO BE REPLACED AT MERGE: the contracts the `a` and `nobr` start
//! tag cases ([`super::in_body_start_cases`]) need from the adoption agency
//! algorithm and the "any other end tag" entry, which another change
//! writes (`exec/modes/adoption.rs`, `exec/modes/in_body_end.rs`). The
//! bodies below do NOT meet their `ensures`: Verus reports one error for
//! each of the two functions, and nothing here is verified. Delete this
//! file (and its `mod` line) once the real functions exist, keeping their
//! names, signatures and at least these `ensures`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::exec::frame::*;
use crate::exec::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// How the adoption agency algorithm ended ([`AdoptionOutcome`]), the
/// parser being the one it mutated in place.
pub enum ExecAdoptionOutcome {
    /// It returned.
    Done,
    /// Step 4.3: act as the "any other end tag" entry describes.
    AnyOtherEndTag,
}

/// The spec outcome of an exec adoption outcome whose parser is `p`.
pub open spec fn adoption_outcome_view(o: ExecAdoptionOutcome, p: Parser) -> AdoptionOutcome {
    match o {
        ExecAdoptionOutcome::Done => AdoptionOutcome::Done(p),
        ExecAdoptionOutcome::AnyOtherEndTag => AdoptionOutcome::AnyOtherEndTag(p),
    }
}

/// STUB (not verified; see the module comment): [`adoption_agency`].
pub fn adoption_agency_exec<E: EncFnsExec>(_env: &E, p: &mut ParserBuf, tt: &ExecTagTok) -> (r: ExecAdoptionOutcome)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
    ensures
        adoption_outcome_view(r, final(p)@) == adoption_agency(old(p)@, tt@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        doc_extends(old(p)@.doc, final(p)@.doc),
{
    let _ = (p.stopped, tt.self_closing);
    ExecAdoptionOutcome::Done
}

/// STUB (not verified; see the module comment):
/// [`in_body_any_other_end_tag`].
pub fn in_body_any_other_end_tag_exec(p: &mut ParserBuf, tt: &ExecTagTok)
    requires
        parser_inv(old(p)@),
        old(p)@.stopped || stack_rooted(old(p)@),
        tok_tagged(tt@),
        tt@.tag != Tag::Html,
    ensures
        final(p)@ == in_body_any_other_end_tag(old(p)@, tt@),
        parser_inv(final(p)@),
        final(p)@.stopped || stack_rooted(final(p)@),
        final(p)@.doc == old(p)@.doc,
{
    let _ = (p.stopped, tt.self_closing);
}

} // verus!
