//! The executable log encoder on hand-assembled DER. The proof already ties
//! the code to the spec; this runs the compiled code and pins the format.

use clazel_store::crc32c::exec::crc32c;
use clazel_store::log::exec::{encode_header, encode_record, OpRef};

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
        OpRef::Put { bottle: 2, key: b"k", value: b"vv" },
        OpRef::Delete { bottle: 0x80, key: b"" },
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
    let big = vec![0u8; 67_108_864];
    assert_eq!(encode_record(1, &[OpRef::Put { bottle: 0, key: b"", value: &big }]), None);
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
                    OpRef::Put { bottle, key, value } => Owned::Put(*bottle, key.to_vec(), value.to_vec()),
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
    let one: &[OpRef] = &[OpRef::Put { bottle: 1, key: b"a", value: b"x" }];
    let two: &[OpRef] = &[OpRef::Delete { bottle: 1, key: b"a" }, OpRef::Clear { bottle: 3 }];
    let file = log(b"id", &[one, two]);
    let want = vec![
        vec![Owned::Put(1, b"a".to_vec(), b"x".to_vec())],
        vec![Owned::Delete(1, b"a".to_vec()), Owned::Clear(3)],
    ];
    assert_eq!(recover(b"id", &file).map(|ts| owned(&ts)), Some(want));

    // Every torn tail recovers the records that are whole.
    let header_len = encode_header(b"id").len();
    let first_end = log(b"id", &[one]).len();
    for cut in header_len..file.len() {
        let got = recover(b"id", file.get(..cut).unwrap_or_default()).map(|ts| ts.len());
        assert_eq!(got, Some(usize::from(cut >= first_end)), "cut at {cut}");
    }

    // A flipped octet in the second record ends recovery before it.
    let mut bad = file.clone();
    if let Some(o) = bad.last_mut() {
        *o ^= 1;
    }
    assert_eq!(recover(b"id", &bad).map(|ts| ts.len()), Some(1));

    // Records out of sequence: the second numbered 1 again.
    let mut skipped = log(b"id", &[one]);
    skipped.extend_from_slice(&encode_record(1, two).unwrap_or_default());
    assert_eq!(recover(b"id", &skipped).map(|ts| ts.len()), Some(1));
}

#[test]
fn refused_files() {
    let file = log(b"id", &[]);
    assert_eq!(recover(b"other", &file).map(|ts| ts.len()), None);
    assert_eq!(recover(b"id", file.get(..file.len().saturating_sub(1)).unwrap_or_default()).map(|ts| ts.len()), None);
    assert_eq!(recover(&[0u8; 4097], &file).map(|ts| ts.len()), None);
    assert_eq!(recover(b"id", &file).map(|ts| ts.len()), Some(0));
}

use clazel_store::log::compact::{compact, EntryRef};

#[test]
fn compaction() {
    let entries = [
        EntryRef { bottle: 1, key: b"a", value: b"x" },
        EntryRef { bottle: 2, key: b"a", value: b"y" },
        EntryRef { bottle: 1, key: b"a", value: b"z" },
    ];
    let file = compact(b"id", &entries).unwrap_or_default();
    let want = vec![
        vec![Owned::Put(1, b"a".to_vec(), b"x".to_vec())],
        vec![Owned::Put(2, b"a".to_vec(), b"y".to_vec())],
        vec![Owned::Put(1, b"a".to_vec(), b"z".to_vec())],
    ];
    assert_eq!(recover(b"id", &file).map(|ts| owned(&ts)), Some(want));
    assert_eq!(compact(b"id", &[]), Some(encode_header(b"id")));

    let big = vec![0u8; 67_108_864];
    assert_eq!(compact(b"id", &[EntryRef { bottle: 0, key: b"", value: &big }]), None);
}
