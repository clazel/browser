//! Proofs of the theorems that [`super::contract`] states and [`super::lemmas`] does not
//! prove. Each is proven for the statement as `contract.rs` has it, for every input
//! string, with no added assumption. The README of the crate says which of the
//! planned theorems are proven here.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use crate::independent::equiv_good::*;

verus! {

/// `theorem_output_preserved`: §5.2's note, "never appear in any parser output". No
/// `<function-token>`, `<{-token>`, `<(-token>` or `<[-token>` is in the list "parse a list
/// of component values" returns, however deep in functions and simple blocks.
pub proof fn theorem_output_preserved(string: Seq<u32>)
    ensures
        output_preserved(string),
{
    let (stream, index) = normalize(Input::String { string });
    lemma_string_stream_ok(filter_code_points(string), false);
    assert(stream == token_stream(filter_code_points(string), false));
    lemma_list_good(stream, 0, None, false, Seq::empty());
    let values = parse_a_list_of_component_values(Input::String { string });
    lemma_all_good_preserved(values, values.len());
}

} // verus!
