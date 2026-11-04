//! Contracts the executable log functions must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates, so
//! reviewing these (and [`super::spec`]) is enough to know what the
//! implementation guarantees.
//!
//! The executable operation type, and its view as [`Op`], come with the
//! implementation. These predicates are about the views.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `encode_header(identity: &[u8]) -> Vec<u8>`, which
/// requires [`identity_ok`]: the header's octets.
pub open spec fn encode_header_ensures(identity: Seq<u8>, output: Seq<u8>) -> bool {
    output == encode_header(identity)
}

/// Contract for `encode_record(commit: u64, ops: &[Op]) -> Option<Vec<u8>>`:
/// the record's octets when the transaction may be written with that commit
/// number, and `None` (nothing written) when it may not.
pub open spec fn encode_record_ensures(commit: nat, ops: Seq<Op>, output: Option<Seq<u8>>) -> bool {
    if transaction_ok(commit, ops) {
        output == Some(encode_record(commit, ops))
    } else {
        output is None
    }
}

/// Contract for `recover(identity: &[u8], file: &[u8]) ->
/// Option<Vec<Vec<Op>>>`: exactly the transactions [`recovered`] names, or
/// `None` when it refuses the file.
pub open spec fn recover_ensures(identity: Seq<u8>, file: Seq<u8>, output: Option<Seq<Seq<Op>>>) -> bool {
    output == recovered(identity, file)
}


/// The put of one entry.
pub open spec fn entry_put(e: Entry) -> Op {
    Op::Put { bottle: e.0, key: e.1, value: e.2 }
}

/// Contract for `compact(identity: &[u8], entries: &[Entry]) ->
/// Option<Vec<u8>>`, which requires [`identity_ok`]: a file that is a
/// compaction of the entries' state, or `None` (nothing written) only when
/// some entry's put, alone in a record, would not be a valid transaction (a
/// record over [`max_record_len`]).
pub open spec fn compact_ensures(identity: Seq<u8>, entries: Seq<Entry>, output: Option<Seq<u8>>) -> bool {
    match output {
        Some(file) => compaction_of(identity, entries_state(entries), file),
        None => exists|i: int|
            0 <= i < entries.len() && !transaction_ok((i + 1) as nat, seq![entry_put(#[trigger] entries[i])]),
    }
}

} // verus!
