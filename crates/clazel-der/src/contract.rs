//! Contracts the executable DER decoder and encoder must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these predicates
//! (with its result mapped to the spec's types by the views in
//! `decode.rs`), so reviewing these and [`super::spec`] is enough to know
//! what the implementation guarantees.
//!
//! Every reader takes the input `input`, a position `pos` and an `end` with
//! `end <= input.len()`, and is proven equal to the spec reader of the same
//! name on `(input@, pos, end)`: it returns exactly what the spec returns,
//! and `None` exactly when the spec does.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of every reader: `end` is inside the input, `pos` is not
/// past it (a position beyond `end` is "nothing left", which every reader
/// answers with `None`, or `Some(None)` for an optional component).
pub open spec fn read_requires(input_len: nat, end: nat) -> bool {
    end <= input_len
}

/// Contract for `read_identifier`: the tag and the number of identifier
/// octets, as in [`read_identifier`].
pub open spec fn read_identifier_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(Tag, nat)>) -> bool {
    out == read_identifier(input, pos, end)
}

/// Contract for `read_length`: the length and the number of length octets,
/// as in [`read_length`].
pub open spec fn read_length_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(nat, nat)>) -> bool {
    out == read_length(input, pos, end)
}

/// Contract for `read_tlv`: the tag and contents range, as in [`read_tlv`].
pub open spec fn read_tlv_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<Tlv>) -> bool {
    out == read_tlv(input, pos, end)
}

/// Contract for `read_boolean`.
pub open spec fn read_boolean_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(bool, nat)>) -> bool {
    out == read_boolean(input, pos, end)
}

/// Contract for `read_integer`: sign, magnitude range, next position.
pub open spec fn read_integer_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(bool, nat, nat, nat)>) -> bool {
    out == read_integer(input, pos, end)
}

/// Contract for `read_bit_string`: unused bits, the range of the octets that
/// hold the bits, next position.
pub open spec fn read_bit_string_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(u8, nat, nat, nat)>) -> bool {
    out == read_bit_string(input, pos, end)
}

/// Contract for `read_octets` and the string readers built on it: the
/// contents range.
pub open spec fn read_octets_ensures(input: Seq<u8>, pos: nat, end: nat, number: u32, out: Option<(nat, nat)>) -> bool {
    out == read_octets(input, pos, end, number)
}

/// Contract for `read_null`: the next position.
pub open spec fn read_null_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<nat>) -> bool {
    out == read_null(input, pos, end)
}

/// Contract for `read_oid`: the components and the next position.
pub open spec fn read_oid_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<(Seq<nat>, nat)>) -> bool {
    out == read_oid(input, pos, end)
}

/// Contract on what `read_oid` allocates: it never holds more components
/// than the OBJECT IDENTIFIER has contents octets plus one, so a declared
/// length of 2^64 reserves nothing (the vector grows only by components it
/// has read).
pub open spec fn read_oid_alloc_ensures(input: Seq<u8>, pos: nat, end: nat, out: Option<nat>) -> bool {
    match out {
        Some(n) => match read_tlv(input, pos, end) {
            Some(t) => n <= t.cend - t.cstart + 1,
            None => false,
        },
        None => true,
    }
}

/// Contract for `expect_constructed`, `expect_sequence` and `expect_set`:
/// the contents range.
pub open spec fn expect_constructed_ensures(input: Seq<u8>, pos: nat, end: nat, number: u32, out: Option<(nat, nat)>) -> bool {
    out == expect_constructed(input, pos, end, number)
}

/// Contract for `read_optional_context`.
pub open spec fn read_optional_context_ensures(
    input: Seq<u8>,
    pos: nat,
    end: nat,
    number: u32,
    out: Option<Option<(bool, nat, nat)>>,
) -> bool {
    out == read_optional_context(input, pos, end, number)
}

/// Contract for `read_optional_explicit`.
pub open spec fn read_optional_explicit_ensures(
    input: Seq<u8>,
    pos: nat,
    end: nat,
    number: u32,
    out: Option<Option<(nat, nat)>>,
) -> bool {
    out == read_optional_explicit(input, pos, end, number)
}

/// Contract for `expect_end`.
pub open spec fn expect_end_ensures(pos: nat, end: nat, out: bool) -> bool {
    out == expect_end(pos, end)
}

/// Precondition of `encode_tlv`: a tag number the decoder accepts. (The
/// contents are a slice, so shorter than 2^64 octets, which is the other
/// half of [`tlv_ok`]; the function proves that itself.)
pub open spec fn encode_tlv_requires(tag: Tag) -> bool {
    tag.number <= MAX_TAG_NUMBER
}

/// Contract for `encode_tlv`: identifier, length, contents.
pub open spec fn encode_tlv_ensures(tag: Tag, contents: Seq<u8>, out: Seq<u8>) -> bool {
    out == encode_tlv(tag, contents)
}

/// Precondition of `encode_length`: the length fits at most 8 octets.
pub open spec fn encode_length_requires(len: nat) -> bool {
    len < pow256(8)
}

/// Contract for `encode_length`: the shortest form.
pub open spec fn encode_length_ensures(len: nat, out: Seq<u8>) -> bool {
    out == encode_length(len)
}

/// Contract on what the encoders allocate: the output is the contents plus
/// at most 12 octets (3 identifier octets and 9 length octets), never more.
pub open spec fn encode_alloc_ensures(contents_len: nat, out_len: nat) -> bool {
    out_len <= contents_len + 12
}

/// Precondition of `encode_oid`: components that [`oid_valid`] accepts.
pub open spec fn encode_oid_requires(arcs: Seq<nat>) -> bool {
    oid_valid(arcs)
}

/// Contract for `encode_oid`.
pub open spec fn encode_oid_ensures(arcs: Seq<nat>, out: Seq<u8>) -> bool {
    out == encode_oid(arcs)
}

/// Contract for `encode_integer_unsigned`: the INTEGER of the number the
/// magnitude octets spell.
pub open spec fn encode_integer_unsigned_ensures(magnitude: Seq<u8>, out: Seq<u8>) -> bool {
    out == encode_integer_unsigned(magnitude)
}

} // verus!
