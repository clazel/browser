//! The executable log encoder, proven to meet [`super::contract`]. Every
//! function builds its octets with `clazel-der`'s proven encoders, in the
//! order [`super::spec`] writes them, so each proof only puts the pieces
//! together.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One operation, borrowing its key and value from the caller. A bottle
/// number is a `u32`, so it is always below the spec's limit of 2^32.
pub enum OpRef<'a> {
    /// Set `key` of `bottle` to `value`.
    Put {
        /// The bottle's number.
        bottle: u32,
        /// The key.
        key: &'a [u8],
        /// The new value.
        value: &'a [u8],
    },
    /// Remove `key` from `bottle`.
    Delete {
        /// The bottle's number.
        bottle: u32,
        /// The key.
        key: &'a [u8],
    },
    /// Remove every key of `bottle`.
    Clear {
        /// The bottle's number.
        bottle: u32,
    },
}

impl<'a> View for OpRef<'a> {
    type V = Op;

    open spec fn view(&self) -> Op {
        match self {
            OpRef::Put { bottle, key, value } => Op::Put { bottle: *bottle as nat, key: key@, value: value@ },
            OpRef::Delete { bottle, key } => Op::Delete { bottle: *bottle as nat, key: key@ },
            OpRef::Clear { bottle } => Op::Clear { bottle: *bottle as nat },
        }
    }
}

/// The operations the executable list stands for.
pub open spec fn ops_view(ops: Seq<OpRef>) -> Seq<Op> {
    ops.map_values(|o: OpRef| o@)
}

/// The view of an optional encoding; `None` is a refusal.
pub open spec fn option_view(out: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match out {
        Some(v) => Some(v@),
        None => None,
    }
}

/// Append the `width` octets spelling `value` base 256, most significant
/// first (`clazel_der::spec::be_bytes`'s recursion).
fn push_be(out: &mut Vec<u8>, value: u64, width: usize)
    requires
        width <= 8,
        (value as nat) < clazel_der::spec::pow256(width as nat),
    ensures
        final(out)@ =~= old(out)@ + clazel_der::spec::be_bytes(value as nat, width as nat),
    decreases width,
{
    if width == 0 {
        assert(clazel_der::spec::be_bytes(value as nat, 0) =~= Seq::<u8>::empty());
        return;
    }
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    assert(clazel_der::spec::pow256(width as nat) == 256 * clazel_der::spec::pow256(before as nat));
    push_be(out, value / 256, before);
    out.push((value % 256) as u8);
    assert(out@ =~= old(out)@ + clazel_der::spec::be_bytes(value as nat, width as nat));
}

/// [`encode_number`]: the INTEGER holding `n`.
fn number(n: u64) -> (out: Vec<u8>)
    ensures
        out@ == encode_number(n as nat),
{
    proof {
        clazel_der::lemmas::lemma_pow256_8();
    }
    let mut magnitude: Vec<u8> = Vec::new();
    push_be(&mut magnitude, n, 8);
    assert(magnitude@ =~= clazel_der::spec::be_bytes(n as nat, 8));
    clazel_der::encode::encode_integer_unsigned(magnitude.as_slice())
}

/// [`encode_header`]: the header of the log of bucket `identity`.
pub fn encode_header(identity: &[u8]) -> (out: Vec<u8>)
    requires
        identity_ok(identity@),
    ensures
        super::contract::encode_header_ensures(identity@, out@),
{
    let magic_octets: [u8; 12] = [0x63, 0x6c, 0x61, 0x7a, 0x65, 0x6c, 0x2d, 0x73, 0x74, 0x6f, 0x72, 0x65];
    assert(magic_octets@ =~= magic());
    let mut contents = clazel_der::encode::encode_octet_string(magic_octets.as_slice());
    let version_octets = number(1);
    contents.extend_from_slice(version_octets.as_slice());
    let id = clazel_der::encode::encode_octet_string(identity);
    contents.extend_from_slice(id.as_slice());
    assert(contents@ =~= clazel_der::spec::encode_octet_string(magic()) + encode_number(version())
        + clazel_der::spec::encode_octet_string(identity@));
    clazel_der::encode::encode_sequence(contents.as_slice())
}

/// [`encode_op`]: one operation.
fn encode_op_exec(op: &OpRef) -> (out: Vec<u8>)
    ensures
        out@ == encode_op(op@),
{
    match op {
        OpRef::Put { bottle, key, value } => {
            let mut c = number(*bottle as u64);
            let k = clazel_der::encode::encode_octet_string(key);
            c.extend_from_slice(k.as_slice());
            let v = clazel_der::encode::encode_octet_string(value);
            c.extend_from_slice(v.as_slice());
            assert(c@ =~= encode_number(*bottle as nat) + clazel_der::spec::encode_octet_string(key@)
                + clazel_der::spec::encode_octet_string(value@));
            clazel_der::encode::encode_context(0, true, c.as_slice())
        },
        OpRef::Delete { bottle, key } => {
            let mut c = number(*bottle as u64);
            let k = clazel_der::encode::encode_octet_string(key);
            c.extend_from_slice(k.as_slice());
            assert(c@ =~= encode_number(*bottle as nat) + clazel_der::spec::encode_octet_string(key@));
            clazel_der::encode::encode_context(1, true, c.as_slice())
        },
        OpRef::Clear { bottle } => {
            let c = number(*bottle as u64);
            clazel_der::encode::encode_context(2, true, c.as_slice())
        },
    }
}

/// [`encode_record`]: the record of transaction `ops` with commit number
/// `commit`, or `None` when [`transaction_ok`] refuses it (commit 0, or a
/// record over [`max_record_len`] octets). The record is built before its
/// length is checked, so refusing an oversized one costs its memory once.
pub fn encode_record(commit: u64, ops: &[OpRef]) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::encode_record_ensures(commit as nat, ops_view(ops@), option_view(out)),
{
    let ghost view = ops_view(ops@);
    proof {
        clazel_der::lemmas::lemma_pow256_8();
        assert forall|i: int| 0 <= i < view.len() implies op_bottle(#[trigger] view[i]) < clazel_der::spec::pow256(4) by {
            assert(view[i] == ops@[i]@);
        }
    }
    if commit == 0 {
        return None;
    }
    let mut list: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(view.take(0) =~= Seq::<Op>::empty());
    while i < ops.len()
        invariant
            i <= ops.len(),
            view == ops_view(ops@),
            list@ == encode_ops(view.take(i as int)),
        ensures
            i == ops.len(),
            list@ == encode_ops(view.take(i as int)),
        decreases ops.len() - i,
    {
        let op = match ops.get(i) {
            Some(op) => op,
            None => break,
        };
        let e = encode_op_exec(op);
        proof {
            let t = view.take(i as int + 1);
            assert(t.drop_last() =~= view.take(i as int));
            assert(t.last() == op@);
        }
        list.extend_from_slice(e.as_slice());
        // Never saturates: i < ops.len().
        i = i.saturating_add(1);
    }
    assert(view.take(ops.len() as int) =~= view);
    let mut body = number(commit);
    let sequence = clazel_der::encode::encode_sequence(list.as_slice());
    body.extend_from_slice(sequence.as_slice());
    assert(body@ =~= record_body(commit as nat, view));
    let check = crate::crc32c::exec::crc32c(body.as_slice());
    let check_octets = clazel_der::encode::encode_octet_string(check.as_slice());
    body.extend_from_slice(check_octets.as_slice());
    let record = clazel_der::encode::encode_sequence(body.as_slice());
    assert(record@ =~= super::spec::encode_record(commit as nat, view));
    if record.len() > 67_108_864 {
        return None;
    }
    Some(record)
}

} // verus!
