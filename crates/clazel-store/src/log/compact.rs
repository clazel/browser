//! The executable compaction, proven to meet [`super::contract`]'s
//! `compact_ensures`. It writes the header, then one record per entry, each
//! holding that entry's put. One put per record costs a few octets of
//! framing per entry and keeps the work linear; the contract allows any
//! layout that builds the same state.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One entry of the state to write, borrowing its key and value.
pub struct EntryRef<'a> {
    /// The bottle's number.
    pub bottle: u32,
    /// The key.
    pub key: &'a [u8],
    /// The value.
    pub value: &'a [u8],
}

impl<'a> View for EntryRef<'a> {
    type V = Entry;

    open spec fn view(&self) -> Entry {
        (self.bottle as nat, self.key@, self.value@)
    }
}

/// The entries the executable list stands for.
pub open spec fn entries_view(es: Seq<EntryRef>) -> Seq<Entry> {
    es.map_values(|e: EntryRef| e@)
}

/// The log of bucket `identity` holding exactly the state of `entries`, or
/// `None` when an entry's put does not fit in one record (64 MiB).
pub fn compact(identity: &[u8], entries: &[EntryRef]) -> (out: Option<Vec<u8>>)
    requires
        identity_ok(identity@),
    ensures
        super::contract::compact_ensures(identity@, entries_view(entries@), super::exec::option_view(out)),
{
    let ghost view = entries_view(entries@);
    let mut file = super::exec::encode_header(identity);
    let ghost mut ts: Seq<Seq<Op>> = Seq::empty();
    let mut i: usize = 0;
    proof {
        assert(view.take(0) =~= Seq::<Entry>::empty());
    }
    while i < entries.len()
        invariant
            i <= entries.len(),
            view == entries_view(entries@),
            ts.len() == i,
            log_ok(ts),
            file@ == encode_log(identity@, ts),
            apply_log(ts) == entries_state(view.take(i as int)),
        decreases entries.len() - i,
    {
        let e = entries.get(i)?;
        let op = [super::exec::OpRef::Put { bottle: e.bottle, key: e.key, value: e.value }];
        let ghost t = seq![super::contract::entry_put(view[i as int])];
        proof {
            assert(view[i as int] == e@);
            assert(super::exec::ops_view(op@) =~= t);
        }
        // Never saturates: i < entries.len() <= usize::MAX.
        let next = i.saturating_add(1);
        let commit = next as u64;
        let record = match super::exec::encode_record(commit, op.as_slice()) {
            Some(record) => record,
            None => {
                proof {
                    assert(!transaction_ok((i + 1) as nat, seq![super::contract::entry_put(view[i as int])]));
                }
                return None;
            },
        };
        file.extend_from_slice(record.as_slice());
        proof {
            let now = ts.push(t);
            assert(now.drop_last() =~= ts);
            assert(file@ =~= encode_log(identity@, now));
            assert forall|j: int| 0 <= j < now.len() implies transaction_ok((j + 1) as nat, #[trigger] now[j]) by {
                if j < ts.len() {
                    assert(now[j] == ts[j]);
                }
            }
            let tk = view.take(i as int + 1);
            assert(tk.drop_last() =~= view.take(i as int));
            assert(tk.last() == view[i as int]);
            assert(t.drop_last() =~= Seq::<Op>::empty());
            assert(t.last() == super::contract::entry_put(view[i as int]));
            assert(apply_transaction(apply_log(ts), t.drop_last()) == apply_log(ts));
            assert(apply_transaction(apply_log(ts), t) == apply_log(ts).insert(
                (view[i as int].0, view[i as int].1),
                view[i as int].2,
            ));
            assert(apply_log(now) == apply_transaction(apply_log(ts), t));
            ts = now;
        }
        i = next;
    }
    proof {
        assert(view.take(i as int) =~= view);
        assert(log_ok(ts) && file@ == encode_log(identity@, ts) && apply_log(ts) == entries_state(view));
    }
    Some(file)
}

} // verus!
