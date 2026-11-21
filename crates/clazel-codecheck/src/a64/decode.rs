//! The decoding half of the A64 validator, proven: [`decode_all_a64`] reads a
//! blob into the instruction list the spec quantifies over
//! ([`crate::a64::spec::decodes_to`]). Each word is decoded by `clazel-a64`'s
//! proven decoder ([`clazel_a64::inverse::decode_bytes`]). Its `Some` result is
//! sound, and it finds **the** decomposition: if the blob decomposes as `w` at
//! all, the answer is `Some` with exactly `w`, by `clazel-a64`'s proven
//! injectivity of the encoding. The counterpart of [`crate::decode_all`]; with
//! words of a fixed size there is no prefix argument.

#[allow(unused_imports)]
use super::spec::*;
use clazel_a64::inverse::decode_bytes;
#[cfg(verus_only)]
use clazel_a64::inverse::{le_word, lemma_canonical_injective, lemma_encode_fits};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The instruction list of a [`decode_all_a64`] result.
pub open spec fn res_ins(r: Option<Vec<Instr>>) -> Seq<Instr> {
    match r {
        Some(i) => i@,
        None => Seq::empty(),
    }
}

/// Bit-vector fact: the four bytes of a word, read back little-endian, give the
/// word.
proof fn bv_le_word_roundtrip(w: u32)
    by (bit_vector)
    ensures
        w % 0x100 + 0x100 * ((w / 0x100) % 0x100) + 0x1_0000 * ((w / 0x1_0000) % 0x100)
            + 0x100_0000 * ((w / 0x100_0000) % 0x100) == w,
{
}

/// Bit-vector fact: the bytes of a little-endian word of four bytes are those
/// four bytes.
proof fn bv_word_bytes_of_le(b0: u32, b1: u32, b2: u32, b3: u32)
    by (bit_vector)
    requires
        b0 < 0x100,
        b1 < 0x100,
        b2 < 0x100,
        b3 < 0x100,
    ensures
        (b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3) % 0x100 == b0,
        ((b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3) / 0x100) % 0x100 == b1,
        ((b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3) / 0x1_0000) % 0x100 == b2,
        ((b0 + 0x100 * b1 + 0x1_0000 * b2 + 0x100_0000 * b3) / 0x100_0000) % 0x100 == b3,
{
}

/// The word of four bytes is below `2^32`.
proof fn lemma_le_word_bound(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        0 <= le_word(b0, b1, b2, b3) < 0x1_0000_0000,
{
}

/// The bytes of the word `le_word(b0, b1, b2, b3)` are `b0`, `b1`, `b2`, `b3`.
proof fn lemma_word_bytes_of_le(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        word_bytes(le_word(b0, b1, b2, b3)) =~= seq![b0, b1, b2, b3],
{
    lemma_le_word_bound(b0, b1, b2, b3);
    bv_word_bytes_of_le(b0 as u32, b1 as u32, b2 as u32, b3 as u32);
    let w = le_word(b0, b1, b2, b3);
    assert(w == (b0 as u32 + 0x100 * (b1 as u32) + 0x1_0000 * (b2 as u32) + 0x100_0000 * (
    b3 as u32)) as int);
}

/// A word of `[0, 2^32)` read back from its own bytes is itself.
proof fn lemma_le_word_of_word_bytes(w: int)
    requires
        0 <= w < 0x1_0000_0000,
    ensures
        le_word(
            word_bytes(w)[0],
            word_bytes(w)[1],
            word_bytes(w)[2],
            word_bytes(w)[3],
        ) == w,
{
    bv_le_word_roundtrip(w as u32);
    assert(w as u32 as int == w);
}

/// The four bytes at `4j` of the blob are [`word_bytes`] of the canonical
/// encoding of the valid instruction `i` if and only if the little-endian word
/// they make is that encoding.
proof fn lemma_word_matches(blob: Seq<u8>, j: int, i: Instr)
    requires
        0 <= j,
        4 * j + 4 <= blob.len(),
        valid_instr(i),
    ensures
        (blob.subrange(4 * j, 4 * j + 4) =~= word_bytes(encode(i))) <==> (le_word(
            blob[4 * j],
            blob[4 * j + 1],
            blob[4 * j + 2],
            blob[4 * j + 3],
        ) == encode(i)),
{
    lemma_encode_fits();
    let w = encode(i);
    assert(0 <= w < 0x1_0000_0000);
    let b0 = blob[4 * j];
    let b1 = blob[4 * j + 1];
    let b2 = blob[4 * j + 2];
    let b3 = blob[4 * j + 3];
    let sub = blob.subrange(4 * j, 4 * j + 4);
    assert(sub[0] == b0 && sub[1] == b1 && sub[2] == b2 && sub[3] == b3);
    if sub =~= word_bytes(w) {
        assert(word_bytes(w)[0] == b0 && word_bytes(w)[1] == b1 && word_bytes(w)[2] == b2
            && word_bytes(w)[3] == b3);
        lemma_le_word_of_word_bytes(w);
    }
    if le_word(b0, b1, b2, b3) == w {
        lemma_word_bytes_of_le(b0, b1, b2, b3);
        assert(sub =~= seq![b0, b1, b2, b3]);
    }
}

/// Decodes the whole blob into instructions. It finds **the** decomposition:
/// if the blob decomposes as `w` at all ([`decodes_to`]), the answer is `Some`
/// and the instructions are `w`.
#[verifier::spinoff_prover]
#[verifier::rlimit(2000)]
pub fn decode_all_a64(blob: &[u8]) -> (r: Option<Vec<Instr>>)
    requires
        blob@.len() < 0x8000_0000,
    ensures
        match r {
            Some(ins) => decodes_to(blob@, ins@),
            None => true,
        },
        forall|w: Seq<Instr>| #[trigger] decodes_to(blob@, w) ==> (r is Some && res_ins(r) =~= w),
{
    let words = blob.len() / 4;
    let words4 = words.saturating_add(words).saturating_add(words).saturating_add(words);
    if words4 != blob.len() {
        proof {
            assert forall|w: Seq<Instr>| decodes_to(blob@, w) implies false by {
                assert(blob@.len() == 4 * w.len());
            }
        }
        return None;
    }
    let mut ins: Vec<Instr> = Vec::new();
    let mut j: usize = 0;
    while j < words
        invariant
            j <= words,
            blob@.len() < 0x8000_0000,
            words == blob@.len() / 4,
            blob@.len() == 4 * words,
            ins@.len() == j,
            all_valid(ins@),
            forall|q: int|
                0 <= q < j ==> blob@.subrange(4 * q, 4 * q + 4) =~= word_bytes(
                    encode(#[trigger] ins@[q]),
                ),
            forall|w: Seq<Instr>|
                #[trigger] decodes_to(blob@, w) ==> (w.len() == words && forall|q: int|
                    0 <= q < j ==> #[trigger] w[q] == ins@[q]),
        decreases words - j,
    {
        proof {
            assert(4 * j + 4 <= blob@.len());
        }
        let p = j.saturating_add(j).saturating_add(j).saturating_add(j);
        proof {
            assert(p == 4 * j);
        }
        let (b0, b1, b2, b3) = match (
            blob.get(p),
            blob.get(p.saturating_add(1)),
            blob.get(p.saturating_add(2)),
            blob.get(p.saturating_add(3)),
        ) {
            (Some(b0), Some(b1), Some(b2), Some(b3)) => (*b0, *b1, *b2, *b3),
            _ => {
                return None;
            },
        };
        let r = decode_bytes(b0, b1, b2, b3);
        match r {
            None => {
                proof {
                    assert forall|w: Seq<Instr>| decodes_to(blob@, w) implies false by {
                        assert(w.len() == words);
                        assert(0 <= j < w.len());
                        assert(valid_instr(w[j as int]));
                        assert(blob@.subrange(4 * j as int, 4 * j as int + 4) =~= word_bytes(
                            encode(w[j as int]),
                        ));
                        lemma_word_matches(blob@, j as int, w[j as int]);
                        lemma_le_word_bound(b0, b1, b2, b3);
                        assert(le_word(b0, b1, b2, b3) as u32 as int == le_word(b0, b1, b2, b3));
                        assert(is_canonical_encoding(le_word(b0, b1, b2, b3) as u32, w[j as int]));
                    }
                }
                return None;
            },
            Some(i) => {
                proof {
                    lemma_le_word_bound(b0, b1, b2, b3);
                    assert(is_canonical_encoding(le_word(b0, b1, b2, b3) as u32, i));
                    assert(le_word(b0, b1, b2, b3) == encode(i));
                    assert(b0 == blob@[4 * j as int] && b1 == blob@[4 * j as int + 1] && b2
                        == blob@[4 * j as int + 2] && b3 == blob@[4 * j as int + 3]);
                    lemma_word_matches(blob@, j as int, i);
                }
                let ghost old = ins@;
                ins.push(i);
                proof {
                    assert(ins@ =~= old.push(i));
                    assert forall|q: int| 0 <= q < ins@.len() implies valid_instr(
                        #[trigger] ins@[q],
                    ) by {
                        if q < old.len() {
                            assert(ins@[q] == old[q]);
                        }
                    }
                    assert forall|q: int|
                        0 <= q < j + 1 implies blob@.subrange(4 * q, 4 * q + 4) =~= word_bytes(
                        encode(#[trigger] ins@[q]),
                    ) by {
                        if q < j as int {
                            assert(ins@[q] == old[q]);
                        }
                    }
                    lemma_canonical_injective();
                    assert forall|w: Seq<Instr>| #[trigger]
                        decodes_to(blob@, w) implies (w.len() == words && forall|q: int|
                        0 <= q < j + 1 ==> #[trigger] w[q] == ins@[q]) by {
                        assert(w.len() == words);
                        assert forall|q: int| 0 <= q < j + 1 implies #[trigger] w[q] == ins@[q] by {
                            if q < j as int {
                                assert(w[q] == old[q]);
                                assert(ins@[q] == old[q]);
                            } else {
                                assert(q == j as int);
                                assert(valid_instr(w[q]));
                                assert(blob@.subrange(4 * q, 4 * q + 4) =~= word_bytes(
                                    encode(w[q]),
                                ));
                                lemma_word_matches(blob@, q, w[q]);
                                let wd = le_word(b0, b1, b2, b3) as u32;
                                assert(is_canonical_encoding(wd, w[q]));
                                assert(is_canonical_encoding(wd, i));
                            }
                        }
                    }
                }
                j = j.saturating_add(1);
            },
        }
    }
    proof {
        assert forall|w: Seq<Instr>| decodes_to(blob@, w) implies res_ins(Some(ins)) =~= w by {
            assert(w.len() == words);
            assert forall|q: int| 0 <= q < words implies ins@[q] == w[q] by {}
        }
        assert(decodes_to(blob@, ins@)) by {
            assert(blob@.len() == 4 * ins@.len());
        }
    }
    Some(ins)
}

} // verus!
