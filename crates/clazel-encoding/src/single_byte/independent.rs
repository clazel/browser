//! A second, independent transcription of the single-byte decoder and
//! encoder (Encoding §9), written from the standard's text without
//! following [`super::spec`]'s queue machinery, and proven equal to it.
//!
//! The only text is the Encoding Standard's, so this is a same-text
//! transcription (Phase 4 item 4.3): the algorithms are tiny, and the
//! evidence that the *tables* are right comes from a second body instead
//! (`tests/conformance_tables.rs`, against the Unicode Consortium's
//! mapping files). Its reading of §9:
//!
//! - "An encoding where each byte is either a single code point or
//!   nothing": decoding is a map over the bytes. Byte `b` is itself when it
//!   is an ASCII byte, else entry `b − 0x80` of the index; an entry that is
//!   null is an error, which "replacement" mode turns into U+FFFD and
//!   "fatal" mode into failure of the whole input.
//! - Encoding is the concatenation, right to left, of each scalar value's
//!   bytes: itself if ASCII, else 0x80 plus the first pointer that holds
//!   it, else (the "html" error mode) `&#`, its decimal digits, `;`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What one byte decodes to: a code point, or `None` for an error.
pub open spec fn decode_one(e: crate::labels::spec::Encoding, b: u8) -> Option<u32> {
    if b < 0x80 {
        Some(b as u32)
    } else {
        let v = index_entry(e, b - 0x80);
        if v == 0xFFFF_FFFFu32 {
            None
        } else {
            Some(v)
        }
    }
}

/// Decoding with errors as U+FFFD: one code point per byte.
pub open spec fn decode_map(e: crate::labels::spec::Encoding, input: Seq<u8>) -> Seq<u32> {
    Seq::new(
        input.len(),
        |k: int|
            match decode_one(e, input[k]) {
                Some(c) => c,
                None => 0xFFFDu32,
            },
    )
}

/// Decoding that fails on any error.
pub open spec fn decode_map_or_fail(e: crate::labels::spec::Encoding, input: Seq<u8>) -> Option<Seq<u32>> {
    if forall|k: int| 0 <= k < input.len() ==> #[trigger] decode_one(e, input[k]) is Some {
        Some(decode_map(e, input))
    } else {
        None
    }
}

/// Decimal digits, most significant first.
pub open spec fn digits(n: nat) -> Seq<u8>
    decreases n,
{
    (if n >= 10 {
        digits(n / 10)
    } else {
        seq![]
    }) + seq![(0x30 + n % 10) as u8]
}

/// The first pointer, counting from `p`, that holds `c`.
pub open spec fn first_pointer(e: crate::labels::spec::Encoding, c: u32, p: nat) -> Option<nat>
    decreases 128 - p,
{
    if p < 128 {
        if index_entry(e, p as int) != 0xFFFF_FFFFu32 && index_entry(e, p as int) == c {
            Some(p)
        } else {
            first_pointer(e, c, p + 1)
        }
    } else {
        None
    }
}

/// The bytes one scalar value encodes to.
pub open spec fn encode_one(e: crate::labels::spec::Encoding, c: u32) -> Seq<u8> {
    if c < 0x80 {
        seq![c as u8]
    } else {
        match first_pointer(e, c, 0) {
            Some(p) => seq![(0x80 + p) as u8],
            None => seq![0x26u8, 0x23u8] + digits(c as nat) + seq![0x3Bu8],
        }
    }
}

/// Encoding, right to left.
pub open spec fn encode_concat(e: crate::labels::spec::Encoding, input: Seq<u32>) -> Seq<u8>
    decreases input.len(),
{
    if input.len() == 0 {
        seq![]
    } else {
        encode_concat(e, input.drop_last()) + encode_one(e, input.last())
    }
}

// ---------------------------------------------------------------------
// Equivalence with the spec.

proof fn lemma_process_queue_map(mode: crate::utf8::spec::ErrorMode, e: crate::labels::spec::Encoding, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        mode == crate::utf8::spec::ErrorMode::Replacement,
    ensures
        process_queue(mode, e, input, i) == Some(decode_map(e, input).subrange(i as int, input.len() as int)),
    decreases input.len() - i,
{
    let m = decode_map(e, input);
    if i < input.len() {
        lemma_process_queue_map(mode, e, input, i + 1);
        assert(m.subrange(i as int, input.len() as int) =~= seq![m[i as int]] + m.subrange(
            (i + 1) as int,
            input.len() as int,
        ));
    } else {
        assert(m.subrange(i as int, input.len() as int) =~= seq![]);
    }
}

/// The spec's decoder in "replacement" mode is the byte-by-byte map.
pub proof fn lemma_equals_decode(e: crate::labels::spec::Encoding, input: Seq<u8>)
    ensures
        decode(e, input) == decode_map(e, input),
{
    lemma_process_queue_map(crate::utf8::spec::ErrorMode::Replacement, e, input, 0);
    assert(decode_map(e, input).subrange(0, input.len() as int) =~= decode_map(e, input));
}

proof fn lemma_process_queue_fail(e: crate::labels::spec::Encoding, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(crate::utf8::spec::ErrorMode::Fatal, e, input, i) == if forall|k: int|
            i <= k < input.len() ==> #[trigger] decode_one(e, input[k]) is Some {
            Some(decode_map(e, input).subrange(i as int, input.len() as int))
        } else {
            None
        },
    decreases input.len() - i,
{
    let m = decode_map(e, input);
    if i < input.len() {
        lemma_process_queue_fail(e, input, i + 1);
        assert(m.subrange(i as int, input.len() as int) =~= seq![m[i as int]] + m.subrange(
            (i + 1) as int,
            input.len() as int,
        ));
        if decode_one(e, input[i as int]) is Some {
            if !(forall|k: int| i + 1 <= k < input.len() ==> #[trigger] decode_one(e, input[k]) is Some) {
                let k = choose|k: int| i + 1 <= k < input.len() && !(#[trigger] decode_one(e, input[k]) is Some);
                assert(i <= k < input.len());
            }
        }
    } else {
        assert(m.subrange(i as int, input.len() as int) =~= seq![]);
    }
}

/// The spec's decoder in "fatal" mode is the map, failing on any error.
pub proof fn lemma_equals_decode_or_fail(e: crate::labels::spec::Encoding, input: Seq<u8>)
    ensures
        decode_or_fail(e, input) == decode_map_or_fail(e, input),
{
    lemma_process_queue_fail(e, input, 0);
    assert(decode_map(e, input).subrange(0, input.len() as int) =~= decode_map(e, input));
}

proof fn lemma_digits(n: nat)
    ensures
        digits(n) == decimal(n),
    decreases n,
{
    if n >= 10 {
        lemma_digits(n / 10);
    } else {
        assert(n % 10 == n);
        assert(seq![] + seq![(0x30 + n % 10) as u8] =~= seq![(0x30 + n) as u8]);
    }
}

proof fn lemma_pointer(e: crate::labels::spec::Encoding, c: u32, p: nat)
    requires
        c >= 0x80,
    ensures
        first_pointer(e, c, p) == index_pointer_from(e, c, p),
    decreases 128 - p,
{
    if p < 128 {
        lemma_pointer(e, c, p + 1);
    }
}

proof fn lemma_one(e: crate::labels::spec::Encoding, input: Seq<u32>, i: nat)
    requires
        i < input.len(),
    ensures
        encoder_process_queue(e, input, i) == encode_one(e, input[i as int]) + encoder_process_queue(e, input, i + 1),
{
    let c = input[i as int];
    if c >= 0x80 {
        lemma_pointer(e, c, 0);
        lemma_digits(c as nat);
    }
}

proof fn lemma_concat_front(e: crate::labels::spec::Encoding, input: Seq<u32>)
    requires
        input.len() > 0,
    ensures
        encode_concat(e, input) == encode_one(e, input[0]) + encode_concat(e, input.subrange(1, input.len() as int)),
    decreases input.len(),
{
    if input.len() > 1 {
        let init = input.drop_last();
        lemma_concat_front(e, init);
        assert(init.subrange(1, init.len() as int) =~= input.subrange(1, input.len() as int).drop_last());
        assert(input.subrange(1, input.len() as int).last() == input.last());
    } else {
        assert(input.drop_last() =~= seq![]);
        assert(input.subrange(1, input.len() as int) =~= seq![]);
    }
}

proof fn lemma_encoder_queue(e: crate::labels::spec::Encoding, input: Seq<u32>, i: nat)
    requires
        i <= input.len(),
    ensures
        encoder_process_queue(e, input, i) == encode_concat(e, input.subrange(i as int, input.len() as int)),
    decreases input.len() - i,
{
    let rest = input.subrange(i as int, input.len() as int);
    if i < input.len() {
        lemma_encoder_queue(e, input, i + 1);
        lemma_one(e, input, i);
        lemma_concat_front(e, rest);
        assert(rest.subrange(1, rest.len() as int) =~= input.subrange((i + 1) as int, input.len() as int));
    } else {
        assert(rest =~= seq![]);
    }
}

/// The spec's "encode" is the concatenation of each scalar value's bytes.
pub proof fn lemma_equals_encode(e: crate::labels::spec::Encoding, input: Seq<u32>)
    ensures
        encode(e, input) == encode_concat(e, input),
{
    lemma_encoder_queue(e, input, 0);
    assert(input.subrange(0, input.len() as int) =~= input);
}

} // verus!
