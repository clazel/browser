//! HTML §13.2.6.4.8 the "text" insertion mode.
//! STUB: being transcribed; this body is a placeholder and is replaced
//! before the spec is committed.

#[allow(unused_imports)]
use super::super::dispatch::*;
#[allow(unused_imports)]
use super::super::insert::*;
#[allow(unused_imports)]
use super::super::state::*;
#[allow(unused_imports)]
use super::super::tags::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §13.2.6.4.8 the "text" insertion mode.
pub open spec fn mode_text(env: EncFns, p: Parser, t: Tok) -> Outcome {
    Outcome::Done(p)
}

} // verus!
