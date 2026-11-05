//! The executable CRC32C on RFC 7143 §A.4's examples, and on the check value
//! catalogues list for CRC-32C ("123456789" gives 0xe3069283, as the
//! digest word `83 92 06 e3`). The proof already ties the code to the spec;
//! this runs the compiled code.

use clazel_store::crc32c::exec::crc32c;

#[test]
fn rfc_7143_examples() {
    let zeros = [0u8; 32];
    let ones = [0xffu8; 32];
    let mut incrementing = [0u8; 32];
    let mut decrementing = [0u8; 32];
    for (i, (up, down)) in incrementing
        .iter_mut()
        .zip(decrementing.iter_mut())
        .enumerate()
    {
        let i = u8::try_from(i).unwrap_or(0);
        *up = i;
        *down = 31u8.saturating_sub(i);
    }
    assert_eq!(crc32c(&zeros), [0xaa, 0x36, 0x91, 0x8a]);
    assert_eq!(crc32c(&ones), [0x43, 0xab, 0xa8, 0x62]);
    assert_eq!(crc32c(&incrementing), [0x4e, 0x79, 0xdd, 0x46]);
    assert_eq!(crc32c(&decrementing), [0x5c, 0xdb, 0x3f, 0x11]);
}

#[test]
fn check_value() {
    assert_eq!(crc32c(b"123456789"), [0x83, 0x92, 0x06, 0xe3]);
}

#[test]
fn short_messages() {
    // Below four octets §13.1 says nothing; the spec gives the usual
    // CRC32C (see its modelling choices). The empty message's is 0.
    assert_eq!(crc32c(&[]), [0, 0, 0, 0]);
    assert_eq!(crc32c(b"a"), 0xc1d0_4330u32.to_le_bytes());
}
