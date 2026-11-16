//! Worked examples of the encodings' spec functions, evaluated by Verus.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies, even with
//! `--verify-function`. A mutant that breaks an example would otherwise fail
//! every kill certificate placed next to it, not only the one about the
//! example (see `crates/clazel-percent/src/examples.rs`). The examples use
//! no byte-string literals (Verus 0.2026.10.04's evaluator cannot read them).

#[cfg(verus_only)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Replace CR not followed by LF and LF not preceded by CR by CR LF",
/// `text/plain` and `application/x-www-form-urlencoded` on small inputs,
/// worked out by hand from the steps of the algorithms.
pub proof fn lemma_examples()
    ensures
        // CR LF stays; a lone LF and a lone CR each become CR LF.
        crlf_newlines(seq![0x0Du32, 0x0Au32]) == seq![0x0Du32, 0x0Au32],
        crlf_newlines(seq![0x0Au32]) == seq![0x0Du32, 0x0Au32],
        crlf_newlines(seq![0x0Du32]) == seq![0x0Du32, 0x0Au32],
        crlf_newlines(seq![0x61u32, 0x0Du32, 0x62u32]) == seq![0x61u32, 0x0Du32, 0x0Au32, 0x62u32],
        // LF CR is two lone characters: LF, then CR.
        crlf_newlines(seq![0x0Au32, 0x0Du32]) == seq![0x0Du32, 0x0Au32, 0x0Du32, 0x0Au32],
        // Splitting on ASCII whitespace: runs of whitespace separate tokens,
        // none are empty.
        split_ws(seq![0x20u32, 0x61u32, 0x09u32, 0x0Cu32, 0x62u32, 0x63u32, 0x20u32]) == seq![
            seq![0x61u32],
            seq![0x62u32, 0x63u32],
        ],
        split_ws(Seq::<u32>::empty()) == Seq::<Seq<u32>>::empty(),
        // text/plain: "name=value" CR LF per pair.
        text_plain_encode(seq![Entry { name: seq![0x61u32], value: seq![0x62u32] }]) == seq![
            0x61u32,
            0x3Du32,
            0x62u32,
            0x0Du32,
            0x0Au32,
        ],
        // application/x-www-form-urlencoded: "&" between pairs, "=" inside.
        urlencoded_serialize(
            seq![
                Entry { name: seq![0x61u32], value: seq![0x62u32] },
                Entry { name: seq![0x63u32], value: seq![0x64u32] },
            ],
            Encoding::Utf8,
        ) == seq![0x61u32, 0x3Du32, 0x62u32, 0x26u32, 0x63u32, 0x3Du32, 0x64u32],
        // A space is "+", U+00E9 is its two UTF-8 bytes, percent-encoded.
        urlencoded_serialize(seq![Entry { name: seq![0x20u32], value: seq![0xE9u32] }], Encoding::Utf8) == seq![
            0x2Bu32,
            0x3Du32,
            0x25u32,
            0x43u32,
            0x33u32,
            0x25u32,
            0x41u32,
            0x39u32,
        ],
        // No pairs: the empty string.
        urlencoded_serialize(Seq::<Entry>::empty(), Encoding::Utf8) == Seq::<u32>::empty(),
{
    assert(crlf_newlines(seq![0x0Du32, 0x0Au32]) =~= seq![0x0Du32, 0x0Au32]) by (compute_only);
    assert(crlf_newlines(seq![0x0Au32]) =~= seq![0x0Du32, 0x0Au32]) by (compute_only);
    assert(crlf_newlines(seq![0x0Du32]) =~= seq![0x0Du32, 0x0Au32]) by (compute_only);
    assert(crlf_newlines(seq![0x61u32, 0x0Du32, 0x62u32]) =~= seq![0x61u32, 0x0Du32, 0x0Au32, 0x62u32])
        by (compute_only);
    assert(crlf_newlines(seq![0x0Au32, 0x0Du32]) =~= seq![0x0Du32, 0x0Au32, 0x0Du32, 0x0Au32]) by (compute_only);
    assert(split_ws(seq![0x20u32, 0x61u32, 0x09u32, 0x0Cu32, 0x62u32, 0x63u32, 0x20u32]) =~= seq![
        seq![0x61u32],
        seq![0x62u32, 0x63u32],
    ]) by (compute_only);
    assert(split_ws(Seq::<u32>::empty()) =~= Seq::<Seq<u32>>::empty()) by (compute_only);
    assert(text_plain_encode(seq![Entry { name: seq![0x61u32], value: seq![0x62u32] }]) =~= seq![
        0x61u32,
        0x3Du32,
        0x62u32,
        0x0Du32,
        0x0Au32,
    ]) by (compute_only);
    assert(urlencoded_serialize(
        seq![
            Entry { name: seq![0x61u32], value: seq![0x62u32] },
            Entry { name: seq![0x63u32], value: seq![0x64u32] },
        ],
        Encoding::Utf8,
    ) =~= seq![0x61u32, 0x3Du32, 0x62u32, 0x26u32, 0x63u32, 0x3Du32, 0x64u32]) by (compute_only);
    assert(urlencoded_serialize(seq![Entry { name: seq![0x20u32], value: seq![0xE9u32] }], Encoding::Utf8) =~= seq![
        0x2Bu32,
        0x3Du32,
        0x25u32,
        0x43u32,
        0x33u32,
        0x25u32,
        0x41u32,
        0x39u32,
    ]) by (compute_only);
    assert(urlencoded_serialize(Seq::<Entry>::empty(), Encoding::Utf8) =~= Seq::<u32>::empty()) by (compute_only);
}

} // verus!
