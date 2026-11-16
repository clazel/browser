//! Contracts the executable code must meet. Each exec function's `ensures`
//! clause is exactly one of these predicates, so reviewing these (and
//! [`super::spec`]) is enough to know what the implementation guarantees.
//!
//! **What is proven today is in the README.** A predicate here is the
//! statement the item aims at, written before the code (CLAUDE.md rule 3); a
//! predicate that no proof of the exec code cites yet says so in its
//! comment.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The 2-byte input whose first 15 bits (least significant bit of byte 0
/// first) are the low 15 bits of `k`. A Huffman code is at most 15 bits, so
/// decoding from this input is decoding from any stream whose next 15 bits
/// are those.
pub open spec fn peek_input(k: nat) -> Seq<u8> {
    seq![(k % 256) as u8, (k / 256 % 256) as u8]
}

/// What the fast table holds at index `k` (0 to 32767) for the code with
/// lengths `lens`: `symbol * 16 + length` of the code that the 15 bits `k`
/// start with, or 0 if no code of length 1 to 15 is a prefix of them. (A
/// code has length at least 1, so 0 is never a real entry.)
pub open spec fn table_entry(lens: Seq<nat>, k: nat) -> nat {
    match decode_symbol(lens, peek_input(k), 0, 0, 0) {
        Sym::Found(s, p) => s * 16 + p,
        _ => 0,
    }
}

/// Contract for building the fast table of the code with lengths `lens`
/// (`huffman::build`): 32,768 entries, entry `k` being [`table_entry`].
/// This is `theorem_huffman_table`: the fast table decodes exactly the
/// canonical code of RFC 1951 §3.2.2.
pub open spec fn build_table_ensures(lens: Seq<nat>, table: Seq<u16>) -> bool {
    table.len() == 32768 && forall|k: int|
        0 <= k < 32768 ==> #[trigger] table[k] as nat == table_entry(lens, k as nat)
}

/// Contract for `adler32(&[u8]) -> u32`: RFC 1950 §8.2's checksum.
pub open spec fn adler32_ensures(data: Seq<u8>, sum: u32) -> bool {
    sum as nat == adler32(data)
}

/// Contract for the one-shot raw decoder: exactly [`inflate`], with the same
/// limit. The result's output and used-bytes count are the spec's.
pub open spec fn inflate_ensures(input: Seq<u8>, limit: nat, result: Result<(Seq<u8>, nat), Error>) -> bool {
    result == inflate(input, limit)
}

/// Contract for the one-shot zlib decoder: exactly [`zlib_decompress`].
pub open spec fn zlib_ensures(input: Seq<u8>, limit: nat, result: Result<(Seq<u8>, nat), Error>) -> bool {
    result == zlib_decompress(input, limit)
}

/// Contract for the resumable decoder (`theorem_chunking_irrelevant`): fed
/// `chunks` in order and then told the input has ended, its output (all the
/// bytes it produced over its calls, in order) and its final error are those
/// of [`zlib_decompress`] on the concatenation, **whatever the chunks are**,
/// including empty ones. Not proven by Verus (the step function is plain
/// Rust); tested in `tests/` with every chunk size.
pub open spec fn chunked_ensures(
    chunks: Seq<Seq<u8>>,
    limit: nat,
    result: Result<(Seq<u8>, nat), Error>,
) -> bool {
    result == zlib_decompress(chunks.flatten(), limit)
}

/// `theorem_output_bounded`: a successful decode never produced more than
/// `limit` bytes, so a decompression bomb stops at the limit.
pub open spec fn output_bounded_ensures(limit: nat, result: Result<(Seq<u8>, nat), Error>) -> bool {
    match result {
        Ok((out, _)) => out.len() <= limit,
        Err(_) => true,
    }
}

} // verus!
