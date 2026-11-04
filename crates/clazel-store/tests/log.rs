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
