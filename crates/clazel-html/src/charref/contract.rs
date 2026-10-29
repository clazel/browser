//! Contracts the executable character reference functions must be proven
//! to meet. Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these and [`super::spec`] is enough to know
//! what the implementation guarantees.
//!
//! The exec tokenizer keeps the character reference code as a `u32` capped
//! at 0x110000 ([`capped_code`]): every check of the numeric character
//! reference end state treats all numbers above 0x10FFFF alike, so the
//! cap loses nothing ([`super::lemmas::lemma_end_code_cap`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The character reference code as the exec tokenizer keeps it.
pub open spec fn capped_code(code: nat) -> nat {
    if code > 0x110000 {
        0x110000
    } else {
        code
    }
}

/// Precondition of `longest_match(&[u32], usize) -> Option<usize>`: the
/// position is within the input or at its end (EOF).
pub open spec fn longest_match_requires(input: Seq<u32>, pos: int) -> bool {
    0 <= pos <= input.len()
}

/// Contract for `longest_match(&[u32], usize) -> Option<usize>`: the row
/// of the named character references table that the named character
/// reference state consumes, or `None` for no match.
pub open spec fn longest_match_ensures(input: Seq<u32>, pos: int, output: Option<usize>) -> bool {
    match output {
        None => longest_match(input, pos) is None,
        Some(i) => longest_match(input, pos) == Some(i as nat),
    }
}

/// Contract for `entity_name(usize) -> Vec<u32>`: row `i`'s name.
pub open spec fn entity_name_ensures(i: int, output: Seq<u32>) -> bool {
    output == entity_name(i)
}

/// Contract for `entity_code_points(usize) -> Vec<u32>`: row `i`'s code
/// points.
pub open spec fn entity_code_points_ensures(i: int, output: Seq<u32>) -> bool {
    output == entity_code_points(i)
}

/// Contract for `numeric_reference_end_code(u32) -> u32`, given the
/// capped code: the code point the numeric character reference end state
/// appends.
pub open spec fn numeric_reference_end_code_ensures(capped: nat, output: u32) -> bool {
    capped <= 0x110000 && output == numeric_reference_end_code(capped)
}

/// Contract for `hex_digit_step(u32, u32) -> u32` and
/// `decimal_digit_step(u32, u32) -> u32`: the capped code after "multiply
/// the character reference code by `base`" and "add" the digit's value,
/// from the capped code before.
pub open spec fn digit_step_ensures(capped: nat, base: nat, digit: nat, output: nat) -> bool {
    forall|code: nat| #[trigger] capped_code(code) == capped ==> output == capped_code(code * base + digit)
}

} // verus!
