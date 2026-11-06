//! A bucket's log as the shell keeps it, proven to meet
//! [`super::contract`]'s `load_ensures`, `log_commit_ensures` and
//! `log_compact_ensures`.
//!
//! A [`BucketLog`] holds the bucket's state and, as a ghost, the
//! transactions `written` its file holds. The shell keeps the file equal to
//! `encode_log(identity, written)`: it cuts a loaded file to the valid
//! length `load` returns, appends each record `commit` returns, and
//! replaces the file with what `compact` returns. `theorem_shell_file`
//! then says that reopening the file gives back the state.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One bucket's log: its identity, its state, and the number of
/// transactions its file holds.
pub struct BucketLog {
    identity: Vec<u8>,
    bucket: super::bucket::Bucket,
    count: u64,
    written: Ghost<Seq<Seq<Op>>>,
}

impl BucketLog {
    /// The transactions the file holds.
    pub closed spec fn written(&self) -> Seq<Seq<Op>> {
        self.written@
    }

    /// The bucket's state.
    pub closed spec fn state(&self) -> State {
        self.bucket@
    }

    /// The bucket's identity.
    pub closed spec fn identity(&self) -> Seq<u8> {
        self.identity@
    }

    /// The invariant: the state is what the written transactions build,
    /// and they are valid.
    pub closed spec fn wf(&self) -> bool {
        &&& self.bucket.wf()
        &&& self.count as nat == self.written@.len()
        &&& log_ok(self.written@)
        &&& apply_log(self.written@) == self.bucket@
        &&& identity_ok(self.identity@)
    }

    /// Open `file` as the log of bucket `identity`: the log and the length
    /// of the file's valid prefix, where the shell cuts it.
    pub fn load(identity: &[u8], file: &[u8]) -> (out: Option<(BucketLog, usize)>)
        ensures
            match out {
                Some((l, n)) => {
                    &&& l.wf()
                    &&& l.identity() == identity@
                    &&& super::contract::load_ensures(identity@, file@, Some((l.written(), l.state(), n as nat)))
                    &&& n <= file@.len()
                    &&& file@.subrange(0, n as int) == encode_log(identity@, l.written())
                },
                None => super::contract::load_ensures(identity@, file@, None),
            },
    {
        let (ts, len) = super::read::recover(identity, file)?;
        let ghost w = super::read::log_view(ts@);
        let mut bucket = super::bucket::Bucket::new();
        let mut i: usize = 0;
        proof {
            assert(w.take(0) =~= Seq::<Seq<Op>>::empty());
        }
        while i < ts.len()
            invariant
                i <= ts.len(),
                w == super::read::log_view(ts@),
                recovered(identity@, file@) == Some(w),
                bucket.wf(),
                bucket@ == apply_log(w.take(i as int)),
            ensures
                i == ts.len(),
                bucket.wf(),
                bucket@ == apply_log(w.take(i as int)),
            decreases ts.len() - i,
        {
            let t = match ts.get(i) {
                Some(t) => t,
                None => break,
            };
            proof {
                let n = w.take(i as int + 1);
                assert(n.drop_last() =~= w.take(i as int));
                assert(n.last() == super::exec::ops_view(t@));
            }
            if !bucket.commit(t.as_slice(), u64::MAX) {
                proof {
                    assert(!super::contract::usage_fits(apply_log(w.take(i as int + 1))));
                    let k = i as int + 1;
                    assert(0 < k <= w.len());
                    assert(exists|k: int| 0 < k <= w.len() && !super::contract::usage_fits(#[trigger] apply_log(w.take(k))));
                    assert(recovered(identity@, file@) == Some(w));
                    let r = recovered(identity@, file@);
                    assert(r.unwrap() == w);
                    assert(!super::contract::usage_fits(apply_log(r.unwrap().take(k))));
                    assert(super::contract::load_ensures(identity@, file@, None));
                }
                return None;
            }
            i = i.saturating_add(1);
        }
        proof {
            assert(w.take(i as int) =~= w);
            assert(file@.subrange(0, len as int) =~= encode_log(identity@, w));
        }
        let mut id: Vec<u8> = Vec::new();
        id.extend_from_slice(identity);
        assert(id@ =~= identity@);
        let log = BucketLog { identity: id, bucket, count: i as u64, written: Ghost(w) };
        Some((log, len))
    }

    /// The bucket, to read from.
    pub fn bucket(&self) -> (b: &super::bucket::Bucket)
        requires
            self.wf(),
        ensures
            b.wf(),
            b@ == self.state(),
    {
        &self.bucket
    }

    /// Commit `ops` under a quota of `quota` octets: the record the shell
    /// appends to the file, or `None` and no change.
    pub fn commit(&mut self, ops: &[super::exec::OpRef], quota: u64) -> (out: Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).identity() == old(self).identity(),
            super::contract::log_commit_ensures(
                old(self).written(),
                old(self).state(),
                super::exec::ops_view(ops@),
                quota as nat,
                final(self).written(),
                final(self).state(),
                super::exec::option_view(out),
            ),
    {
        let ghost view = super::exec::ops_view(ops@);
        if self.count == u64::MAX {
            proof {
                clazel_der::lemmas::lemma_pow256_8();
            }
            return None;
        }
        // Never saturates: count < u64::MAX.
        let commit = self.count.saturating_add(1);
        let record = super::exec::encode_record(commit, ops)?;
        if !self.bucket.commit(ops, quota) {
            return None;
        }
        proof {
            let n = self.written@.push(view);
            assert(n.drop_last() =~= self.written@);
            assert forall|j: int| 0 <= j < n.len() implies transaction_ok((j + 1) as nat, #[trigger] n[j]) by {
                if j < self.written@.len() {
                    assert(n[j] == self.written@[j]);
                }
            }
        }
        self.written = Ghost(self.written@.push(view));
        self.count = commit;
        Some(record)
    }

    /// Compact the log: the file the shell puts in place of the old one,
    /// holding the same state, or `None` and no change.
    pub fn compact(&mut self) -> (out: Option<Vec<u8>>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).identity() == old(self).identity(),
            final(self).state() == old(self).state(),
            super::contract::log_compact_ensures(
                old(self).identity(),
                old(self).written(),
                old(self).state(),
                final(self).written(),
                super::exec::option_view(out),
            ),
    {
        let refs = self.bucket.entry_refs();
        let file = super::compact::compact(self.identity.as_slice(), refs.as_slice())?;
        let ghost ts = choose|ts: Seq<Seq<Op>>|
            log_ok(ts) && ts.len() == refs@.len() && file@ == #[trigger] encode_log(self.identity@, ts) && apply_log(ts)
                == entries_state(super::compact::entries_view(refs@));
        let n = refs.len() as u64;
        self.written = Ghost(ts);
        self.count = n;
        Some(file)
    }
}

/// What the shell relies on: a file kept equal to the log of the written
/// transactions reopens to the state, and appending the record of the next
/// transaction keeps it the log. (A loaded file cut to the length `load`
/// returns is that log, `commit` returns the next record, and `compact`
/// returns the log of its new list.)
pub proof fn theorem_shell_file(identity: Seq<u8>, written: Seq<Seq<Op>>, ops: Seq<Op>)
    requires
        identity_ok(identity),
        log_ok(written),
    ensures
        file_state(identity, encode_log(identity, written)) == Some(apply_log(written)),
        encode_log(identity, written.push(ops)) == encode_log(identity, written) + encode_record(
            written.len() + 1,
            ops,
        ),
{
    super::theorems::theorem_whole(identity, written);
    assert(written.push(ops).drop_last() =~= written);
}

} // verus!
