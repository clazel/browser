//! Specification of one bucket's log file: the format and the recovery rule
//! of the 3.10a.0 design note in docs/phases/phase-3.md (accepted
//! 2026-11-03). That note is this project's own, not an outside standard,
//! so there are no step numbers. Each definition cites the bullet of the
//! note it writes down. The records are DER (ITU-T X.690) built from
//! `clazel-der`'s spec encoders, and the check is [`crate::crc32c`].
//! Nothing here runs; it defines what "correct" means.
//!
//! The format, in ASN.1 terms:
//!
//! ```text
//! Header ::= SEQUENCE { magic OCTET STRING ("clazel-store"),
//!                       version INTEGER (1), identity OCTET STRING }
//! Record ::= SEQUENCE { commit INTEGER, ops SEQUENCE OF Op,
//!                       check OCTET STRING (SIZE (4)) }
//! Op ::= CHOICE { put    [0] IMPLICIT SEQUENCE { bottle INTEGER,
//!                                                key OCTET STRING,
//!                                                value OCTET STRING },
//!                 delete [1] IMPLICIT SEQUENCE { bottle INTEGER,
//!                                                key OCTET STRING },
//!                 clear  [2] IMPLICIT SEQUENCE { bottle INTEGER } }
//! ```
//!
//! A file is a header followed by records whose commits are 1, 2, 3, ...,
//! and `check` is the CRC32C of the record's encoded `commit` and `ops`.
//!
//! Modelling choices (each one is a deliberate, reviewable choice, listed so
//! it can be checked once):
//! - **A transaction** is the `Seq<Op>` of one record, applied in order.
//!   Its commit number is its position in the log, counting from 1, so it
//!   is not stored in the spec's transaction list.
//! - **Recovery is defined by encoding, not by a parser.** [`recovered`]
//!   is the longest list of valid transactions whose encoded log is a
//!   prefix of the file: the design note's "longest run of records, from
//!   the header on, that decode, check correctly, and number their commits
//!   in sequence", stated without saying how a reader finds it. A record
//!   "decodes and checks correctly" exactly when its octets are the
//!   encoding of some transaction. DER has one encoding per value, so
//!   octets that only BER would accept are not a record. The list is
//!   unique: `choose` picks it, and a lemma must show there is exactly one
//!   before any implementation can meet [`super::contract`].
//! - **A missing or different header** makes the file refused (`None`): the
//!   note's "a file whose header doesn't match its name is refused". The
//!   name itself is the shell's; the spec takes the identity the name stands
//!   for.
//! - **Limits** (the note's "at most 64 MiB per record"): a record's
//!   encoding is at most [`max_record_len`] octets, a bottle number is
//!   below 2^32, a commit number below 2^64, and an identity at most
//!   [`max_identity_len`] octets. A transaction over a limit is not valid
//!   and is never encoded.
//! - **The state** is a map from (bottle, key) to value. Keys are octets,
//!   and their order ([`key_less`]) is a scan's concern, not this map's.
//! - **A scan** ([`is_scan`]) is stated by what it returns, not how it finds
//!   it: one bottle's entries with keys from `lo` up to but not including
//!   `hi` (no upper bound when `hi` is `None`), each once, in key order. An
//!   empty result is the answer when `hi` is not above `lo`. Scans do not
//!   cross bottles.
//!   `clear` removes every key of its bottle.
//! - **Compaction** (the note's theorem 3) is stated over states, not over
//!   how the new file is laid out: [`compaction_of`] accepts any file
//!   written whole from valid transactions that build the state. How many
//!   records it uses, and in what order, is the implementation's choice.
//!   The state to write is given as a list of entries, later ones replacing
//!   earlier ones with the same bottle and key ([`entries_state`]).
//! - **Usage** (Storage §6 leaves "storage usage" to the implementation)
//!   counts the octets of every key and value in the bucket, as Phase 2's
//!   `localStorage` quota does (`clazel-kernel`'s `entries_size`). Bottle
//!   numbers and the log's framing are not counted, so usage does not
//!   change when a file is compacted.
//! - **Quota** (the note's theorem 4): a transaction is admitted when the
//!   state it leads to is within the quota, and a refused one leaves the
//!   state as it was ([`commit_state`]). Only the end state is measured:
//!   a transaction that passes over the quota and comes back under it (a
//!   put, then a clear) is admitted.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The octets "clazel-store", the header's `magic`.
pub open spec fn magic() -> Seq<u8> {
    seq![0x63u8, 0x6c, 0x61, 0x7a, 0x65, 0x6c, 0x2d, 0x73, 0x74, 0x6f, 0x72, 0x65]
}

/// The header's `version`.
pub open spec fn version() -> nat {
    1
}

/// The most octets one record's encoding may take: 64 MiB.
pub open spec fn max_record_len() -> nat {
    67_108_864
}

/// The most octets a bucket identity may take.
pub open spec fn max_identity_len() -> nat {
    4096
}

/// One operation of a transaction (the note's "put", "delete" and
/// "clear").
pub enum Op {
    /// Set `key` of `bottle` to `value`.
    Put {
        /// The bottle's number.
        bottle: nat,
        /// The key.
        key: Seq<u8>,
        /// The new value.
        value: Seq<u8>,
    },
    /// Remove `key` from `bottle`.
    Delete {
        /// The bottle's number.
        bottle: nat,
        /// The key.
        key: Seq<u8>,
    },
    /// Remove every key of `bottle`.
    Clear {
        /// The bottle's number.
        bottle: nat,
    },
}

/// The bottle an operation touches.
pub open spec fn op_bottle(op: Op) -> nat {
    match op {
        Op::Put { bottle, .. } => bottle,
        Op::Delete { bottle, .. } => bottle,
        Op::Clear { bottle } => bottle,
    }
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// An INTEGER holding `n`, for `n < 2^64`: the shortest two's complement
/// contents (X.690 §8.3.2), from `clazel-der`.
pub open spec fn encode_number(n: nat) -> Seq<u8> {
    clazel_der::spec::encode_integer_unsigned(clazel_der::spec::be_bytes(n, 8))
}

/// The header: `SEQUENCE { magic, version, identity }`.
pub open spec fn encode_header(identity: Seq<u8>) -> Seq<u8> {
    clazel_der::spec::encode_sequence(
        clazel_der::spec::encode_octet_string(magic()) + encode_number(version())
            + clazel_der::spec::encode_octet_string(identity),
    )
}

/// One operation: its CHOICE alternative's context tag around the
/// components of its SEQUENCE (IMPLICIT, so constructed, X.690 §8.14.4).
pub open spec fn encode_op(op: Op) -> Seq<u8> {
    match op {
        Op::Put { bottle, key, value } => clazel_der::spec::encode_context(
            0,
            true,
            encode_number(bottle) + clazel_der::spec::encode_octet_string(key)
                + clazel_der::spec::encode_octet_string(value),
        ),
        Op::Delete { bottle, key } => clazel_der::spec::encode_context(
            1,
            true,
            encode_number(bottle) + clazel_der::spec::encode_octet_string(key),
        ),
        Op::Clear { bottle } => clazel_der::spec::encode_context(2, true, encode_number(bottle)),
    }
}

/// The contents of `SEQUENCE OF Op`: the operations' encodings in order.
pub open spec fn encode_ops(ops: Seq<Op>) -> Seq<u8>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        encode_ops(ops.drop_last()) + encode_op(ops.last())
    }
}

/// What the check covers: the encoded `commit` and `ops`.
pub open spec fn record_body(commit: nat, ops: Seq<Op>) -> Seq<u8> {
    encode_number(commit) + clazel_der::spec::encode_sequence(encode_ops(ops))
}

/// The record of transaction `ops` with commit number `commit`:
/// `SEQUENCE { commit, ops, check }`, where `check` is the CRC32C of the
/// body.
pub open spec fn encode_record(commit: nat, ops: Seq<Op>) -> Seq<u8> {
    let body = record_body(commit, ops);
    clazel_der::spec::encode_sequence(
        body + clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body)),
    )
}

/// The log written from the transactions `ts`: the header, then one record
/// per transaction, with commits 1 to `ts.len()`.
pub open spec fn encode_log(identity: Seq<u8>, ts: Seq<Seq<Op>>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        encode_header(identity)
    } else {
        encode_log(identity, ts.drop_last()) + encode_record(ts.len(), ts.last())
    }
}

// ---------------------------------------------------------------------------
// Validity
// ---------------------------------------------------------------------------

/// An identity within [`max_identity_len`].
pub open spec fn identity_ok(identity: Seq<u8>) -> bool {
    identity.len() <= max_identity_len()
}

/// A transaction that may be written with commit number `commit`: the
/// commit number is 1 to 2^64 - 1, every bottle number is below 2^32, and
/// the record fits in [`max_record_len`] octets.
pub open spec fn transaction_ok(commit: nat, ops: Seq<Op>) -> bool {
    &&& 1 <= commit
    &&& commit < clazel_der::spec::pow256(8)
    &&& forall|i: int| 0 <= i < ops.len() ==> op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(4)
    &&& encode_record(commit, ops).len() <= max_record_len()
}

/// Every transaction of `ts` valid at its position.
pub open spec fn log_ok(ts: Seq<Seq<Op>>) -> bool {
    forall|i: int| 0 <= i < ts.len() ==> transaction_ok((i + 1) as nat, #[trigger] ts[i])
}

// ---------------------------------------------------------------------------
// Recovery
// ---------------------------------------------------------------------------

/// The valid transactions `ts` whose log is a prefix of `file`.
pub open spec fn fits(identity: Seq<u8>, file: Seq<u8>, ts: Seq<Seq<Op>>) -> bool {
    log_ok(ts) && encode_log(identity, ts).is_prefix_of(file)
}

/// `ts` fits, and no list that fits is longer.
pub open spec fn longest_fit(identity: Seq<u8>, file: Seq<u8>, ts: Seq<Seq<Op>>) -> bool {
    fits(identity, file, ts) && forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) ==> u.len() <= ts.len()
}

/// What opening `file` as the log of bucket `identity` recovers (the
/// note's recovery rule): `None` when the identity is over its limit or the
/// file does not start with its header, and otherwise the longest list of
/// valid transactions whose log is a prefix of the file. Whatever follows
/// that prefix (a torn write, or octets never written) is not part of the
/// state.
pub open spec fn recovered(identity: Seq<u8>, file: Seq<u8>) -> Option<Seq<Seq<Op>>> {
    if !identity_ok(identity) || !encode_header(identity).is_prefix_of(file) {
        None
    } else {
        Some(choose|ts: Seq<Seq<Op>>| longest_fit(identity, file, ts))
    }
}

// ---------------------------------------------------------------------------
// The state
// ---------------------------------------------------------------------------

/// A bucket's contents: the value of each (bottle, key) present.
pub type State = Map<(nat, Seq<u8>), Seq<u8>>;

/// The state after one operation.
pub open spec fn apply_op(s: State, op: Op) -> State {
    match op {
        Op::Put { bottle, key, value } => s.insert((bottle, key), value),
        Op::Delete { bottle, key } => s.remove((bottle, key)),
        Op::Clear { bottle } => s.restrict(s.dom().filter(|k: (nat, Seq<u8>)| k.0 != bottle)),
    }
}

/// The state after a transaction's operations, in order.
pub open spec fn apply_transaction(s: State, ops: Seq<Op>) -> State
    decreases ops.len(),
{
    if ops.len() == 0 {
        s
    } else {
        apply_op(apply_transaction(s, ops.drop_last()), ops.last())
    }
}

/// The state a list of transactions builds from an empty bucket.
pub open spec fn apply_log(ts: Seq<Seq<Op>>) -> State
    decreases ts.len(),
{
    if ts.len() == 0 {
        Map::empty()
    } else {
        apply_transaction(apply_log(ts.drop_last()), ts.last())
    }
}


// ---------------------------------------------------------------------------
// Compaction
// ---------------------------------------------------------------------------

/// One entry of a state to write: its bottle, key and value.
pub type Entry = (nat, Seq<u8>, Seq<u8>);

/// The state holding the entries `es`, a later entry replacing an earlier
/// one with the same bottle and key.
pub open spec fn entries_state(es: Seq<Entry>) -> State
    decreases es.len(),
{
    if es.len() == 0 {
        Map::empty()
    } else {
        let e = es.last();
        entries_state(es.drop_last()).insert((e.0, e.1), e.2)
    }
}

/// The state a file holds as the log of bucket `identity`: its recovered
/// transactions applied to an empty bucket, or `None` for a refused file
/// (the note's `state(file)`).
pub open spec fn file_state(identity: Seq<u8>, file: Seq<u8>) -> Option<State> {
    match recovered(identity, file) {
        Some(ts) => Some(apply_log(ts)),
        None => None,
    }
}

/// A compaction of state `s` (the note's "compaction writes the live
/// state as a new log"): the whole log written from some valid list of
/// transactions that builds `s` from an empty bucket.
pub open spec fn compaction_of(identity: Seq<u8>, s: State, file: Seq<u8>) -> bool {
    exists|ts: Seq<Seq<Op>>| log_ok(ts) && file == #[trigger] encode_log(identity, ts) && apply_log(ts) == s
}


// ---------------------------------------------------------------------------
// Usage and quota
// ---------------------------------------------------------------------------

/// The octets one entry counts against the quota: its key and its value.
pub open spec fn entry_size(k: (nat, Seq<u8>), v: Seq<u8>) -> nat {
    k.1.len() + v.len()
}

/// A bucket's usage (Storage §6): the sum of [`entry_size`] over its
/// entries, taken one at a time in any order (the order does not change a
/// sum; `lemma_usage_remove` proves it).
pub open spec fn usage(s: State) -> nat
    decreases s.dom().len(),
    via usage_decreases
{
    if s.dom().len() == 0 {
        0
    } else {
        let k = s.dom().choose();
        entry_size(k, s[k]) + usage(s.remove(k))
    }
}

/// [`usage`] terminates: removing a key of a nonempty state shrinks its
/// domain.
#[verifier::decreases_by]
proof fn usage_decreases(s: State) {
    if s.dom().len() != 0 {
        let k = s.dom().choose();
        vstd::set::lemma_set_choose_len(s.dom());
        assert(s.remove(k).dom() =~= s.dom().remove(k));
        vstd::set::lemma_set_remove_len(s.dom(), k);
    }
}

/// Whether a bucket in state `s`, with quota `quota` octets, admits the
/// transaction `ops`: the state after it is within the quota.
pub open spec fn admits(s: State, ops: Seq<Op>, quota: nat) -> bool {
    usage(apply_transaction(s, ops)) <= quota
}

/// The state after committing `ops` under `quota` (the note's theorem 4):
/// the transaction applied whole, or refused whole.
pub open spec fn commit_state(s: State, ops: Seq<Op>, quota: nat) -> State {
    if admits(s, ops, quota) {
        apply_transaction(s, ops)
    } else {
        s
    }
}


// ---------------------------------------------------------------------------
// Key order and scans
// ---------------------------------------------------------------------------

/// The note's "keys are ordered by octets": `a` comes before `b` when, at
/// the first octet where they differ, its octet is the smaller as an
/// unsigned number, or when it is a proper prefix of `b`.
pub open spec fn key_less(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        b.len() > 0
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        key_less(a.drop_first(), b.drop_first())
    }
}

/// Key `k` is from `lo` up to but not including `hi`.
pub open spec fn in_range(k: Seq<u8>, lo: Seq<u8>, hi: Option<Seq<u8>>) -> bool {
    &&& !key_less(k, lo)
    &&& match hi {
        Some(h) => key_less(k, h),
        None => true,
    }
}

/// `out` is the scan of `bottle` in state `s` from `lo` to `hi`: its keys
/// strictly increase, each pair is an entry of the bottle within the range,
/// and every such entry is there.
pub open spec fn is_scan(s: State, bottle: nat, lo: Seq<u8>, hi: Option<Seq<u8>>, out: Seq<(Seq<u8>, Seq<u8>)>) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < out.len() ==> key_less(#[trigger] out[i].0, #[trigger] out[j].0)
    &&& forall|i: int|
        0 <= i < out.len() ==> {
            &&& in_range(#[trigger] out[i].0, lo, hi)
            &&& s.dom().contains((bottle, out[i].0))
            &&& s[(bottle, out[i].0)] == out[i].1
        }
    &&& forall|k: Seq<u8>|
        #[trigger] s.dom().contains((bottle, k)) && in_range(k, lo, hi) ==> exists|i: int|
            0 <= i < out.len() && #[trigger] out[i].0 == k
}

} // verus!
