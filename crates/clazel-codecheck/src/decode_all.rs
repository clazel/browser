//! The decoding half of the validator, proven: [`decode_all`] reads a blob
//! into the instruction list the spec quantifies over (`spec::decodes_to`),
//! with each instruction's start offset. Its `Some` result is sound by
//! `clazel-x64`'s proven executable decoder. A `None` result makes no claim
//! here (that no other decomposition exists needs the prefix-freeness of the
//! encoding, proven in `clazel-x64`, applied by induction; not done yet).

#[allow(unused_imports)]
use super::spec::*;
use clazel_x64::decoder_exec::decode_exec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every instruction's encoding has at least one byte, so decoding makes
/// progress.
pub proof fn lemma_encode_nonempty(i: Instr)
    ensures
        encode(i).len() >= 1,
{
    reveal_with_fuel(le_bytes, 1);
}

/// The start offset of an instruction does not depend on later ones.
pub proof fn lemma_start_of_push(ins: Seq<Instr>, x: Instr, j: int)
    requires
        0 <= j <= ins.len(),
    ensures
        start_of(ins.push(x), j) == start_of(ins, j),
    decreases j,
{
    if j > 0 {
        lemma_start_of_push(ins, x, j - 1);
        assert(ins.push(x)[j - 1] == ins[j - 1]);
    }
}

/// Decodes the whole blob into instructions and their start offsets.
pub fn decode_all(blob: &[u8]) -> (r: Option<(Vec<Instr>, Vec<usize>)>)
    requires
        blob@.len() < 0x8000_0000,
    ensures
        match r {
            Some((ins, st)) => {
                &&& decodes_to(blob@, ins@)
                &&& st@.len() == ins@.len()
                &&& forall|j: int| 0 <= j < ins@.len() ==> st@[j] as int == start_of(ins@, j)
            },
            None => true,
        },
{
    let mut ins: Vec<Instr> = Vec::new();
    let mut st: Vec<usize> = Vec::new();
    let mut pos: usize = 0;
    while pos < blob.len()
        invariant
            pos <= blob.len(),
            blob@.len() < 0x8000_0000,
            all_valid(ins@),
            enc_all(ins@) =~= blob@.subrange(0, pos as int),
            st@.len() == ins@.len(),
            forall|j: int| 0 <= j < ins@.len() ==> st@[j] as int == start_of(ins@, j),
            pos as int == start_of(ins@, ins@.len() as int),
        decreases blob.len() - pos,
    {
        let rest = vstd::slice::slice_subrange(blob, pos, blob.len());
        match decode_exec(rest) {
            None => {
                return None;
            },
            Some((c, n)) => {
                proof {
                    lemma_encode_nonempty(c);
                    assert(rest@.subrange(0, n as int) =~= encode(c));
                }
                if n == 0 {
                    return None;
                }
                let ghost old_ins = ins@;
                ins.push(c);
                st.push(pos);
                proof {
                    let c2 = ins@.last();
                    assert(ins@ =~= old_ins.push(c2));
                    assert(ins@.drop_last() =~= old_ins);
                    lemma_start_of_push(old_ins, c2, old_ins.len() as int);
                    assert(start_of(ins@, ins@.len() as int) == start_of(old_ins, old_ins.len() as int)
                        + instr_len(c2) as int);
                    assert(enc_all(ins@) =~= blob@.subrange(0, (pos + n) as int)) by {
                        assert(blob@.subrange(0, (pos + n) as int) =~= blob@.subrange(
                            0,
                            pos as int,
                        ) + rest@.subrange(0, n as int));
                    }
                    assert forall|j: int| 0 <= j < ins@.len() implies valid_instr(
                        #[trigger] ins@[j],
                    ) by {
                        if j < old_ins.len() {
                            assert(ins@[j] == old_ins[j]);
                        }
                    }
                    assert forall|j: int| 0 <= j < ins@.len() implies st@[j] as int == start_of(
                        ins@,
                        j,
                    ) by {
                        if j < old_ins.len() {
                            lemma_start_of_push(old_ins, c2, j);
                        } else {
                            lemma_start_of_push(old_ins, c2, j);
                        }
                    }
                }
                pos = pos.saturating_add(n);
            },
        }
    }
    proof {
        assert(blob@.subrange(0, pos as int) =~= blob@);
    }
    Some((ins, st))
}

} // verus!
