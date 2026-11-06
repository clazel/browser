//! The executable log encoder on hand-assembled DER. The proof already ties
//! the code to the spec; this runs the compiled code and pins the format.

use clazel_store::crc32c::exec::crc32c;
use clazel_store::log::exec::{OpRef, encode_header, encode_record};

#[test]
fn header() {
    let mut want = vec![0x30, 0x15, 0x04, 0x0c];
    want.extend_from_slice(b"clazel-store");
    want.extend_from_slice(&[0x02, 0x01, 0x01, 0x04, 0x02, 0xab, 0xcd]);
    assert_eq!(encode_header(&[0xab, 0xcd]), want);
}

#[test]
fn record() {
    let ops = [
        OpRef::Put {
            bottle: 2,
            key: b"k",
            value: b"vv",
        },
        OpRef::Delete {
            bottle: 0x80,
            key: b"",
        },
        OpRef::Clear { bottle: 0 },
    ];
    // commit 7; ops: [0] { 2, "k", "vv" }, [1] { 128, "" }, [2] { 0 }.
    let body: Vec<u8> = vec![
        0x02, 0x01, 0x07, //
        0x30, 0x19, //
        0xa0, 0x0a, 0x02, 0x01, 0x02, 0x04, 0x01, b'k', 0x04, 0x02, b'v', b'v', //
        0xa1, 0x06, 0x02, 0x02, 0x00, 0x80, 0x04, 0x00, //
        0xa2, 0x03, 0x02, 0x01, 0x00,
    ];
    let mut want = vec![0x30, 0x24];
    want.extend_from_slice(&body);
    want.extend_from_slice(&[0x04, 0x04]);
    want.extend_from_slice(&crc32c(&body));
    assert_eq!(encode_record(7, &ops), Some(want));
}

#[test]
fn refusals() {
    assert_eq!(encode_record(0, &[]), None);
    assert!(encode_record(1, &[]).is_some());
}

use clazel_store::log::read::recover;

/// Owned operations, to compare what recovery returns.
#[derive(Debug, PartialEq)]
enum Owned {
    Put(u32, Vec<u8>, Vec<u8>),
    Delete(u32, Vec<u8>),
    Clear(u32),
}

fn owned(ts: &[Vec<OpRef>]) -> Vec<Vec<Owned>> {
    ts.iter()
        .map(|ops| {
            ops.iter()
                .map(|op| match op {
                    OpRef::Put { bottle, key, value } => {
                        Owned::Put(*bottle, key.to_vec(), value.to_vec())
                    }
                    OpRef::Delete { bottle, key } => Owned::Delete(*bottle, key.to_vec()),
                    OpRef::Clear { bottle } => Owned::Clear(*bottle),
                })
                .collect()
        })
        .collect()
}

fn log(identity: &[u8], ts: &[&[OpRef]]) -> Vec<u8> {
    let mut file = encode_header(identity);
    for (i, ops) in ts.iter().enumerate() {
        let commit = u64::try_from(i).unwrap_or(0).saturating_add(1);
        file.extend_from_slice(&encode_record(commit, ops).unwrap_or_default());
    }
    file
}

#[test]
fn recovery() {
    let one: &[OpRef] = &[OpRef::Put {
        bottle: 1,
        key: b"a",
        value: b"x",
    }];
    let two: &[OpRef] = &[
        OpRef::Delete {
            bottle: 1,
            key: b"a",
        },
        OpRef::Clear { bottle: 3 },
    ];
    let file = log(b"id", &[one, two]);
    let want = vec![
        vec![Owned::Put(1, b"a".to_vec(), b"x".to_vec())],
        vec![Owned::Delete(1, b"a".to_vec()), Owned::Clear(3)],
    ];
    assert_eq!(recover(b"id", &file).map(|(ts, _)| owned(&ts)), Some(want));

    // Every torn tail recovers the records that are whole.
    let header_len = encode_header(b"id").len();
    let first_end = log(b"id", &[one]).len();
    for cut in header_len..file.len() {
        let got = recover(b"id", file.get(..cut).unwrap_or_default()).map(|(ts, _)| ts.len());
        assert_eq!(got, Some(usize::from(cut >= first_end)), "cut at {cut}");
    }

    // A flipped octet in the second record ends recovery before it.
    let mut bad = file.clone();
    if let Some(o) = bad.last_mut() {
        *o ^= 1;
    }
    assert_eq!(recover(b"id", &bad).map(|(ts, _)| ts.len()), Some(1));

    // Records out of sequence: the second numbered 1 again.
    let mut skipped = log(b"id", &[one]);
    skipped.extend_from_slice(&encode_record(1, two).unwrap_or_default());
    assert_eq!(recover(b"id", &skipped).map(|(ts, _)| ts.len()), Some(1));
}

#[test]
fn refused_files() {
    let file = log(b"id", &[]);
    assert_eq!(recover(b"other", &file).map(|(ts, _)| ts.len()), None);
    assert_eq!(
        recover(
            b"id",
            file.get(..file.len().saturating_sub(1)).unwrap_or_default()
        )
        .map(|(ts, _)| ts.len()),
        None
    );
    assert_eq!(recover(&[0u8; 4097], &file).map(|(ts, _)| ts.len()), None);
    assert_eq!(recover(b"id", &file).map(|(ts, _)| ts.len()), Some(0));
}

use clazel_store::log::compact::{EntryRef, compact};

#[test]
fn compaction() {
    let entries = [
        EntryRef {
            bottle: 1,
            key: b"a",
            value: b"x",
        },
        EntryRef {
            bottle: 2,
            key: b"a",
            value: b"y",
        },
        EntryRef {
            bottle: 1,
            key: b"a",
            value: b"z",
        },
    ];
    let file = compact(b"id", &entries).unwrap_or_default();
    let want = vec![
        vec![Owned::Put(1, b"a".to_vec(), b"x".to_vec())],
        vec![Owned::Put(2, b"a".to_vec(), b"y".to_vec())],
        vec![Owned::Put(1, b"a".to_vec(), b"z".to_vec())],
    ];
    assert_eq!(recover(b"id", &file).map(|(ts, _)| owned(&ts)), Some(want));
    assert_eq!(compact(b"id", &[]), Some(encode_header(b"id")));
}

use clazel_store::log::bucket::Bucket;

#[test]
fn bucket() {
    let mut b = Bucket::new();
    assert!(b.commit(
        &[
            OpRef::Put {
                bottle: 1,
                key: b"ab",
                value: b"xyz"
            },
            OpRef::Put {
                bottle: 2,
                key: b"ab",
                value: b"q"
            }
        ],
        100
    ));
    assert_eq!(b.usage(), 8);
    assert_eq!(b.get(1, b"ab"), Some(&b"xyz"[..]));
    assert_eq!(b.get(3, b"ab"), None);

    // Over the quota: refused whole.
    assert!(!b.commit(
        &[
            OpRef::Delete {
                bottle: 2,
                key: b"ab"
            },
            OpRef::Put {
                bottle: 1,
                key: b"c",
                value: &[0; 10]
            }
        ],
        10
    ));
    assert_eq!(b.usage(), 8);
    assert_eq!(b.get(2, b"ab"), Some(&b"q"[..]));

    // Only the end state counts: a put then a clear of its bottle is admitted.
    assert!(b.commit(
        &[
            OpRef::Put {
                bottle: 3,
                key: b"k",
                value: &[0; 50]
            },
            OpRef::Clear { bottle: 3 }
        ],
        8
    ));
    assert_eq!(b.usage(), 8);

    // Replacing a value, deleting and clearing.
    assert!(b.commit(
        &[OpRef::Put {
            bottle: 1,
            key: b"ab",
            value: b""
        }],
        100
    ));
    assert_eq!(b.usage(), 5);
    assert!(b.commit(
        &[OpRef::Delete {
            bottle: 2,
            key: b"ab"
        }],
        100
    ));
    assert_eq!(b.usage(), 2);
    assert!(b.commit(&[OpRef::Clear { bottle: 1 }], 0));
    assert_eq!(b.usage(), 0);
    assert_eq!(b.get(1, b"ab"), None);
}

use clazel_store::log::store::BucketLog;

/// The shell's part: open a file, cut it where load says, append records.
#[test]
fn shell_round_trip() -> Result<(), &'static str> {
    let mut file = encode_header(b"id");
    let (mut log, len) = BucketLog::load(b"id", &file).ok_or("fresh file")?;
    assert_eq!(len, file.len());

    let r1 = log
        .commit(
            &[OpRef::Put {
                bottle: 1,
                key: b"a",
                value: b"one",
            }],
            100,
        )
        .unwrap_or_default();
    file.extend_from_slice(&r1);
    let r2 = log
        .commit(
            &[
                OpRef::Put {
                    bottle: 1,
                    key: b"b",
                    value: b"two",
                },
                OpRef::Delete {
                    bottle: 1,
                    key: b"a",
                },
            ],
            100,
        )
        .unwrap_or_default();
    file.extend_from_slice(&r2);
    // Refused by the quota: nothing to write, nothing changes.
    assert_eq!(
        log.commit(
            &[OpRef::Put {
                bottle: 1,
                key: b"c",
                value: &[0; 200]
            }],
            100
        ),
        None
    );
    assert_eq!(log.bucket().get(1, b"b"), Some(&b"two"[..]));

    // A torn write after the last record: load cuts it off.
    let mut torn = file.clone();
    torn.extend_from_slice(r1.get(..r1.len() / 2).unwrap_or_default());
    let (again, len) = BucketLog::load(b"id", &torn).ok_or("torn file")?;
    assert_eq!(len, file.len());
    assert_eq!(again.bucket().get(1, b"a"), None);
    assert_eq!(again.bucket().get(1, b"b"), Some(&b"two"[..]));
    assert_eq!(again.bucket().usage(), 4);

    // Compaction: a new file with the same state.
    let compacted = log.compact().unwrap_or_default();
    assert!(compacted.len() < file.len());
    let (reopened, len) = BucketLog::load(b"id", &compacted).ok_or("compacted file")?;
    assert_eq!(len, compacted.len());
    assert_eq!(reopened.bucket().get(1, b"b"), Some(&b"two"[..]));
    assert_eq!(reopened.bucket().usage(), 4);

    // Commits after compaction continue its numbering.
    let mut file = compacted;
    let r3 = log
        .commit(&[OpRef::Clear { bottle: 1 }], 100)
        .unwrap_or_default();
    file.extend_from_slice(&r3);
    let (last, _) = BucketLog::load(b"id", &file).ok_or("after compaction")?;
    assert_eq!(last.bucket().usage(), 0);

    assert!(BucketLog::load(b"other", &file).is_none());
    Ok(())
}

#[test]
fn scans() {
    let mut b = Bucket::new();
    assert!(b.commit(
        &[
            OpRef::Put {
                bottle: 1,
                key: b"b",
                value: b"2"
            },
            OpRef::Put {
                bottle: 1,
                key: b"a",
                value: b"1"
            },
            OpRef::Put {
                bottle: 1,
                key: b"ab",
                value: b"3"
            },
            OpRef::Put {
                bottle: 1,
                key: &[0xff],
                value: b"4"
            },
            OpRef::Put {
                bottle: 1,
                key: b"",
                value: b"0"
            },
            OpRef::Put {
                bottle: 2,
                key: b"a",
                value: b"other"
            },
        ],
        100
    ));
    let keys = |lo: &[u8], hi: Option<&[u8]>| -> Vec<Vec<u8>> {
        b.scan(1, lo, hi).iter().map(|(k, _)| k.to_vec()).collect()
    };
    // In order by unsigned octets, a prefix first, one bottle only.
    assert_eq!(
        keys(b"", None),
        [&b""[..], b"a", b"ab", b"b", &[0xff]].map(<[u8]>::to_vec)
    );
    // From lo, up to but not including hi.
    assert_eq!(
        keys(b"a", Some(b"b")),
        [&b"a"[..], b"ab"].map(<[u8]>::to_vec)
    );
    assert_eq!(keys(b"aa", Some(b"ab")), Vec::<Vec<u8>>::new());
    assert_eq!(keys(b"b", Some(b"a")), Vec::<Vec<u8>>::new());
    assert_eq!(b.scan(2, b"", None), vec![(&b"a"[..], &b"other"[..])]);
    assert_eq!(b.scan(3, b"", None), Vec::<(&[u8], &[u8])>::new());
}

/// `Bucket` against a `BTreeMap` of the same transactions, on random
/// transactions: every get and scan agrees, and so does the usage.
#[test]
fn bucket_against_a_model() {
    use std::collections::BTreeMap;
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move |n: u64| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x.checked_rem(n).unwrap_or(0)
    };
    let mut model: BTreeMap<(u32, Vec<u8>), Vec<u8>> = BTreeMap::new();
    let mut b = Bucket::new();
    for _ in 0..300 {
        let bottle = u32::try_from(next(3)).unwrap_or(0);
        // Keys from a small alphabet, so they collide and share prefixes.
        let key: Vec<u8> = (0..next(4))
            .map(|_| {
                [0u8, 1, 0xff]
                    .get(usize::try_from(next(3)).unwrap_or(0))
                    .copied()
                    .unwrap_or(0)
            })
            .collect();
        let value = vec![0u8; usize::try_from(next(5)).unwrap_or(0)];
        match next(8) {
            0 => {
                assert!(b.commit(&[OpRef::Clear { bottle }], u64::MAX));
                model.retain(|k, _| k.0 != bottle);
            }
            1 | 2 => {
                assert!(b.commit(&[OpRef::Delete { bottle, key: &key }], u64::MAX));
                model.remove(&(bottle, key.clone()));
            }
            _ => {
                assert!(b.commit(
                    &[OpRef::Put {
                        bottle,
                        key: &key,
                        value: &value
                    }],
                    u64::MAX
                ));
                model.insert((bottle, key.clone()), value.clone());
            }
        }
        let usage: usize = model
            .iter()
            .map(|(k, v)| k.1.len().saturating_add(v.len()))
            .sum();
        assert_eq!(usize::try_from(b.usage()).unwrap_or(0), usage);
        assert_eq!(
            b.get(bottle, &key).map(<[u8]>::to_vec),
            model.get(&(bottle, key.clone())).cloned()
        );
        let got: Vec<(Vec<u8>, Vec<u8>)> = b
            .scan(bottle, &key, None)
            .iter()
            .map(|(k, v)| (k.to_vec(), v.to_vec()))
            .collect();
        let want: Vec<(Vec<u8>, Vec<u8>)> = model
            .iter()
            .filter(|(k, _)| k.0 == bottle && k.1 >= key)
            .map(|(k, v)| (k.1.clone(), v.clone()))
            .collect();
        assert_eq!(got, want);
    }
}

/// A value of 64 MiB does not fit in a record (its framing takes it over).
#[test]
#[cfg_attr(miri, ignore = "one case CRCs 64 MiB a bit at a time, days under Miri")]
fn over_the_record_limit() {
    let big = vec![0u8; 67_108_864];
    let put = OpRef::Put {
        bottle: 0,
        key: b"",
        value: &big,
    };
    assert_eq!(encode_record(1, &[put]), None);
    let entry = EntryRef {
        bottle: 0,
        key: b"",
        value: &big,
    };
    assert_eq!(compact(b"id", &[entry]), None);
}
