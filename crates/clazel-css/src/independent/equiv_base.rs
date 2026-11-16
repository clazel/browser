//! The mapping from the spec's code points to the independent transcription's, and
//! the facts about the classes of code points that the equivalence proofs
//! broadcast. See [`super::equiv_tokenizer`].

#[cfg(verus_only)]
use super::*;
#[cfg(verus_only)]
use crate::tokenizer::spec as t;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The mapping

/// A code point of the spec as one of the independent transcription: EOF is -1.
pub open spec fn cp(c: u32) -> int {
    if c > 0x10FFFF { -1 } else { c as int }
}

/// A string of the spec as one of the independent transcription.
pub open spec fn ints(s: Seq<u32>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[i] as int)
}

/// "The input is a stream of code points": none is above U+10FFFF.
pub open spec fn valid(s: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 0x10FFFF
}

/// The next input code point agrees.
pub broadcast proof fn lemma_at(s: Seq<u32>, p: nat)
    requires
        valid(s),
    ensures
        #[trigger] i_at(ints(s), p) == cp(t::at(s, p as int)),
{
}

pub broadcast proof fn lemma_class_digit(c: u32)
    ensures
        #[trigger] i_digit(cp(c)) == t::is_digit(c),
{
}

pub broadcast proof fn lemma_class_hex(c: u32)
    ensures
        #[trigger] i_hex_digit(cp(c)) == t::is_hex_digit(c),
{
}

pub broadcast proof fn lemma_class_ident_start(c: u32)
    ensures
        #[trigger] i_ident_start(cp(c)) == t::is_ident_start_code_point(c),
{
}

pub broadcast proof fn lemma_class_ident(c: u32)
    ensures
        #[trigger] i_ident(cp(c)) == t::is_ident_code_point(c),
{
}

pub broadcast proof fn lemma_class_non_printable(c: u32)
    ensures
        #[trigger] i_non_printable(cp(c)) == t::is_non_printable_code_point(c),
{
}

pub broadcast proof fn lemma_class_newline(c: u32)
    ensures
        #[trigger] i_newline(cp(c)) == t::is_newline(c),
{
}

pub broadcast proof fn lemma_class_whitespace(c: u32)
    ensures
        #[trigger] i_whitespace(cp(c)) == t::is_whitespace(c),
{
}

pub broadcast proof fn lemma_class_valid_escape(a: u32, b: u32)
    ensures
        #[trigger] i_valid_escape(cp(a), cp(b)) == t::are_a_valid_escape(a, b),
{
}

pub broadcast proof fn lemma_class_starts_ident(a: u32, b: u32, c: u32)
    ensures
        #[trigger] i_starts_ident(cp(a), cp(b), cp(c)) == t::would_start_an_ident_sequence(a, b, c),
{
}

pub broadcast proof fn lemma_class_starts_number(a: u32, b: u32, c: u32)
    ensures
        #[trigger] i_starts_number(cp(a), cp(b), cp(c)) == t::would_start_a_number(a, b, c),
{
}

pub broadcast proof fn lemma_class_starts_unicode_range(a: u32, b: u32, c: u32)
    ensures
        #[trigger] i_starts_unicode_range(cp(a), cp(b), cp(c)) == t::would_start_a_unicode_range(a, b, c),
{
}

/// The digit values agree.
pub broadcast proof fn lemma_digit_value(c: u32)
    requires
        t::is_hex_digit(c),
    ensures
        #[trigger] i_digit_value(cp(c)) == t::hex_value(c),
{
}


} // verus!
