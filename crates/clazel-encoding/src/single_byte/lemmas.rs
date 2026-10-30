//! Facts proven about the single-byte spec. They are evidence that the
//! transcription is right (§9 calls these encodings ones "where each byte
//! is either a single code point or nothing"), not part of what the
//! implementation must meet:
//!
//! - [`lemma_decode_scalar`]: a single-byte decoder never emits a
//!   surrogate (it emits only scalar values, as §4.1 process an item step
//!   6.1 asserts of every decoder);
//! - [`lemma_decode_injective`]: decoding is injective on bytes the index
//!   defines: two inputs that decode without error to the same code
//!   points are the same bytes;
//! - [`lemma_encoder_inverts_decoder`]: the encoder maps the code point a
//!   byte decodes to back to that byte;
//! - [`lemma_replacement_total`]: in "replacement" mode the decoder never
//!   fails.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code point the handler gives `byte`, if it gives one.
pub open spec fn byte_code_point(e: crate::labels::spec::Encoding, byte: u8) -> Option<u32> {
    match handler(e, crate::utf8::spec::Item::Byte(byte)) {
        crate::utf8::spec::HandlerResult::CodePoint(c) => Some(c),
        _ => None,
    }
}

/// An index code point of a single-byte encoding is a scalar value from
/// U+0080.
pub proof fn lemma_index_code_point(e: crate::labels::spec::Encoding, pointer: int)
    requires
        is_single_byte(e),
    ensures
        match index_code_point(e, pointer) {
            Some(c) => 0x80 <= c && crate::utf8::spec::is_scalar_value(c),
            None => true,
        },
{
    if 0 <= pointer < 128 {
        super::tables::lemma_entry_ok(e, pointer);
    }
}

/// The handler returns a code point or an error for a byte, and the code
/// point is a scalar value.
pub proof fn lemma_handler_byte(e: crate::labels::spec::Encoding, byte: u8)
    requires
        is_single_byte(e),
    ensures
        handler(e, crate::utf8::spec::Item::Byte(byte)) is CodePoint || handler(
            e,
            crate::utf8::spec::Item::Byte(byte),
        ) is Error,
        match byte_code_point(e, byte) {
            Some(c) => crate::utf8::spec::is_scalar_value(c),
            None => true,
        },
{
    lemma_index_code_point(e, byte - 0x80);
}

/// In "replacement" mode the decoder never fails.
pub proof fn lemma_replacement_total(e: crate::labels::spec::Encoding, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(crate::utf8::spec::ErrorMode::Replacement, e, input, i) is Some,
    decreases input.len() - i,
{
    if i < input.len() {
        lemma_replacement_total(e, input, i + 1);
    }
}

/// A single-byte decoder never emits a surrogate: every code point it
/// outputs, in either mode, is a scalar value.
pub proof fn lemma_decode_scalar(
    mode: crate::utf8::spec::ErrorMode,
    e: crate::labels::spec::Encoding,
    input: Seq<u8>,
    i: nat,
)
    requires
        is_single_byte(e),
        i <= input.len(),
    ensures
        match process_queue(mode, e, input, i) {
            Some(out) => crate::utf8::spec::all_scalar_values(out),
            None => true,
        },
    decreases input.len() - i,
{
    if i < input.len() {
        lemma_handler_byte(e, input[i as int]);
        lemma_decode_scalar(mode, e, input, i + 1);
    }
}

/// What "fatal" mode gives, byte by byte: when it succeeds, the output has
/// one code point per byte, the one the handler gives that byte.
pub proof fn lemma_fatal_shape(e: crate::labels::spec::Encoding, input: Seq<u8>, i: nat)
    requires
        is_single_byte(e),
        i <= input.len(),
        process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, i) is Some,
    ensures
        ({
            let out = process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, i)->0;
            &&& out.len() == input.len() - i
            &&& forall|k: int| 0 <= k < out.len() ==> byte_code_point(e, #[trigger] input[i + k]) == Some(out[k])
        }),
    decreases input.len() - i,
{
    if i < input.len() {
        lemma_handler_byte(e, input[i as int]);
        lemma_fatal_shape(e, input, i + 1);
        let out = process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, i)->0;
        let rest = process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, i + 1)->0;
        assert forall|k: int| 0 <= k < out.len() implies byte_code_point(e, #[trigger] input[i + k]) == Some(
            out[k],
        ) by {
            if k > 0 {
                assert(out[k] == rest[k - 1]);
                assert(input[i + k] == input[(i + 1) + (k - 1)]);
            }
        }
    }
}

/// Two bytes the handler maps to the same code point are the same byte.
pub proof fn lemma_handler_injective(e: crate::labels::spec::Encoding, a: u8, b: u8)
    requires
        is_single_byte(e),
        byte_code_point(e, a) is Some,
        byte_code_point(e, a) == byte_code_point(e, b),
    ensures
        a == b,
{
    lemma_index_code_point(e, a - 0x80);
    lemma_index_code_point(e, b - 0x80);
    if a > 0x7F && b > 0x7F && a != b {
        super::tables::lemma_entries_distinct(e, a - 0x80, b - 0x80);
    }
}

/// Decoding is injective on bytes the index defines: two inputs that
/// decode without error ("fatal" mode succeeds) to the same code points
/// are the same bytes.
pub proof fn lemma_decode_injective(e: crate::labels::spec::Encoding, x: Seq<u8>, y: Seq<u8>)
    requires
        is_single_byte(e),
        decode_or_fail(e, x) is Some,
        decode_or_fail(e, x) == decode_or_fail(e, y),
    ensures
        x == y,
{
    lemma_fatal_shape(e, x, 0);
    lemma_fatal_shape(e, y, 0);
    let out = decode_or_fail(e, x)->0;
    assert forall|k: int| 0 <= k < x.len() implies x[k] == y[k] by {
        assert(byte_code_point(e, x[0 + k]) == Some(out[k]));
        assert(byte_code_point(e, y[0 + k]) == Some(out[k]));
        lemma_handler_injective(e, x[k], y[k]);
    }
    assert(x =~= y);
}

/// The index pointer search from `start` finds `p` when `p` is the only
/// pointer at or after `start` with code point `c`.
proof fn lemma_index_pointer_finds(e: crate::labels::spec::Encoding, c: u32, start: nat, p: nat)
    requires
        is_single_byte(e),
        start <= p < 128,
        index_code_point(e, p as int) == Some(c),
    ensures
        index_pointer_from(e, c, start) == Some(p),
    decreases p - start,
{
    if start < p {
        if index_code_point(e, start as int) == Some(c) {
            super::tables::lemma_entries_distinct(e, p as int, start as int);
        }
        lemma_index_pointer_finds(e, c, start + 1, p);
    }
}

/// The encoder maps the code point a byte decodes to back to that byte.
pub proof fn lemma_encoder_inverts_decoder(e: crate::labels::spec::Encoding, b: u8)
    requires
        is_single_byte(e),
        byte_code_point(e, b) is Some,
    ensures
        encoder_handler(e, crate::utf8::spec::ScalarItem::ScalarValue(byte_code_point(e, b)->0))
            == EncoderResult::Byte(b),
{
    lemma_index_code_point(e, b - 0x80);
    if b > 0x7F {
        lemma_index_pointer_finds(e, byte_code_point(e, b)->0, 0, (b - 0x80) as nat);
    }
}

} // verus!
