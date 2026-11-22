//! The decomposition of a blob into instructions is unique: the facts about
//! `enc_all` and `start_of` that [`crate::decode_all::decode_all`] needs to
//! show it finds the decomposition the spec quantifies over.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Start offsets of a prefix are the start offsets of the whole.
pub proof fn lemma_start_of_prefix(w: Seq<Instr>, k: int, j: int)
    requires
        0 <= j <= k <= w.len(),
    ensures
        start_of(w.subrange(0, k), j) == start_of(w, j),
    decreases j,
{
    if j > 0 {
        lemma_start_of_prefix(w, k, j - 1);
        assert(w.subrange(0, k)[j - 1] == w[j - 1]);
    }
}

/// Instruction `k` of `w` is encoded at its start offset in `enc_all(w)`.
pub proof fn lemma_enc_all_index(w: Seq<Instr>, k: int)
    requires
        0 <= k < w.len(),
    ensures
        start_of(w, k) + encode(w[k]).len() <= enc_all(w).len(),
        enc_all(w).subrange(start_of(w, k), start_of(w, k) + encode(w[k]).len()) =~= encode(w[k]),
    decreases w.len(),
{
    let d = w.drop_last();
    assert(w =~= d.push(w.last()));
    super::validate::lemma_enc_all_len(d);
    if k == w.len() - 1 {
        super::decode_all::lemma_start_of_push(d, w.last(), d.len() as int);
        assert(start_of(w, k) == enc_all(d).len());
        assert(enc_all(w).subrange(start_of(w, k), start_of(w, k) + encode(w[k]).len())
            =~= encode(w[k]));
    } else {
        lemma_enc_all_index(d, k);
        super::decode_all::lemma_start_of_push(d, w.last(), k);
        assert(d[k] == w[k]);
        super::validate::lemma_start_of_ge(d, k);
        let a = start_of(d, k);
        let b = a + encode(d[k]).len();
        assert(enc_all(w) =~= enc_all(d) + encode(w.last()));
        assert(b <= enc_all(d).len());
        assert forall|i: int| 0 <= i < b - a implies enc_all(w).subrange(a, b)[i] == enc_all(
            d,
        ).subrange(a, b)[i] by {
            assert(a >= 0);
            assert(enc_all(w).subrange(a, b)[i] == enc_all(w)[a + i]);
            assert(enc_all(d).subrange(a, b)[i] == enc_all(d)[a + i]);
            assert(enc_all(w)[a + i] == enc_all(d)[a + i]);
        }
        assert(enc_all(w).subrange(a, b) =~= enc_all(d).subrange(a, b));
        assert(enc_all(w).subrange(start_of(w, k), start_of(w, k) + encode(w[k]).len())
            =~= enc_all(d).subrange(start_of(d, k), start_of(d, k) + encode(d[k]).len()));
    }
}

/// If the blob decomposes as `w`, the bytes after the first `k` instructions
/// begin with the encoding of the next one.
pub proof fn lemma_next_instr(blob: Seq<u8>, w: Seq<Instr>, k: int, pos: int)
    requires
        decodes_to(blob, w),
        0 <= k <= w.len(),
        pos == start_of(w, k),
        pos < blob.len(),
    ensures
        k < w.len(),
        starts_with_encoding(blob.subrange(pos, blob.len() as int), w[k]),
{
    super::validate::lemma_enc_all_len(w);
    assert(blob == enc_all(w));
    if k < w.len() {
        lemma_enc_all_index(w, k);
        let rest = blob.subrange(pos, blob.len() as int);
        let e = encode(w[k]);
        assert(valid_instr(w[k]));
        super::validate::lemma_start_of_ge(w, k);
        assert(pos >= 0);
        assert(pos + e.len() <= blob.len());
        assert(blob.subrange(pos, pos + e.len()) =~= e);
        assert(rest.subrange(0, e.len() as int) =~= blob.subrange(pos, pos + e.len()));
        assert(e.len() <= rest.len());
    } else {
        assert(false);
    }
}

/// If the blob decomposes as `w` and `k` instructions reach its end, they are
/// all of `w`.
pub proof fn lemma_finish(blob: Seq<u8>, w: Seq<Instr>, k: int)
    requires
        decodes_to(blob, w),
        0 <= k <= w.len(),
        start_of(w, k) == blob.len(),
    ensures
        k == w.len(),
{
    super::validate::lemma_enc_all_len(w);
    if k < w.len() {
        super::scan_exec::lemma_start_of_lt(w, k, w.len() as int);
    }
}

} // verus!
