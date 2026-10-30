//! `constant_time_eq` against plain equality on Finished-sized values
//! (RFC 8446 §4.4.4). Timing is not tested here; see the module doc.

use clazel_crypto::compare::constant_time_eq;

fn sample() -> Vec<u8> {
    (0..32u8)
        .map(|i| i.wrapping_mul(7).wrapping_add(3))
        .collect()
}

#[test]
fn equal_32_bytes() {
    let a = sample();
    assert!(constant_time_eq(&a, &a.clone()));
}

#[test]
fn every_single_byte_difference() {
    let a = sample();
    for pos in 0..32 {
        for flip in [0x01u8, 0x80, 0xff] {
            let mut b = a.clone();
            if let Some(byte) = b.get_mut(pos) {
                *byte ^= flip;
            }
            assert!(!constant_time_eq(&a, &b), "position {pos}, flip {flip:#x}");
            assert!(!constant_time_eq(&b, &a), "position {pos}, flip {flip:#x}");
        }
    }
}

#[test]
fn empty_pair_is_equal() {
    assert!(constant_time_eq(&[], &[]));
}

#[test]
fn difference_in_last_byte_only() {
    let a = sample();
    let mut b = a.clone();
    if let Some(last) = b.last_mut() {
        *last = last.wrapping_add(1);
    }
    assert_eq!(a.get(..31), b.get(..31));
    assert!(!constant_time_eq(&a, &b));
}
