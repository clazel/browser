//! Tests for bounded incremental accumulation of one protected TLS record.

use clazel_tls::connection::framing::{Buffer, Status};
use clazel_tls::spec::{RECORD_OVERFLOW, UNEXPECTED_MESSAGE};

fn protected_record(content: &[u8]) -> Vec<u8> {
    let mut wire = vec![23, 3, 3];
    wire.extend_from_slice(
        &u16::try_from(content.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    wire.extend_from_slice(content);
    wire
}

#[test]
fn every_fragmentation_prefix_completes_one_exact_record() -> Result<(), String> {
    let wire = protected_record(b"fragmented body");
    for split in 0..=wire.len() {
        let mut buffer = Buffer::new();
        let prefix = wire.get(..split).unwrap_or(&[]);
        let suffix = wire.get(split..).unwrap_or(&[]);
        let (first_consumed, first_status) = buffer.feed(prefix);
        if split == wire.len() {
            assert_eq!(first_consumed, wire.len());
            assert_eq!(first_status, Status::Complete);
        } else {
            assert_eq!(first_consumed, split);
            assert_eq!(first_status, Status::Pending);
        }
        let (second_consumed, second_status) = buffer.feed(suffix);
        assert_eq!(second_status, Status::Complete);
        assert_eq!(second_consumed, suffix.len());
        assert_eq!(buffer.len(), wire.len());
        assert_eq!(buffer.take(), wire);
        assert_eq!(buffer.len(), 0);
    }
    Ok(())
}

#[test]
fn concatenated_input_stops_at_first_record_and_take_clears() -> Result<(), String> {
    let first = protected_record(b"first");
    let second = protected_record(b"second");
    let mut input = first.clone();
    input.extend_from_slice(&second);
    let mut buffer = Buffer::new();
    let (consumed, status) = buffer.feed(&input);
    assert_eq!(status, Status::Complete);
    assert_eq!(consumed, first.len());
    assert_eq!(buffer.len(), first.len());
    assert_eq!(buffer.take(), first);

    let suffix = input.get(consumed..).unwrap_or(&[]);
    let (consumed, status) = buffer.feed(suffix);
    assert_eq!(status, Status::Complete);
    assert_eq!(consumed, second.len());
    assert_eq!(buffer.take(), second);
    Ok(())
}

#[test]
fn maximum_ciphertext_fits_exactly_with_its_header() -> Result<(), String> {
    let content = vec![0x5a; clazel_tls::spec::MAX_CIPHERTEXT];
    let wire = protected_record(&content);
    assert_eq!(wire.len(), 5 + clazel_tls::spec::MAX_CIPHERTEXT);
    let mut buffer = Buffer::new();
    let (consumed, status) = buffer.feed(&wire);
    assert_eq!(consumed, wire.len());
    assert_eq!(status, Status::Complete);
    assert_eq!(buffer.len(), 5 + clazel_tls::spec::MAX_CIPHERTEXT);
    assert_eq!(buffer.take(), wire);
    Ok(())
}

#[test]
fn malformed_headers_fail_as_soon_as_header_is_complete() -> Result<(), String> {
    for (header, expected) in [
        (&[22, 3, 3, 0, 1][..], UNEXPECTED_MESSAGE),
        (&[23, 3, 2, 0, 1][..], clazel_tls::spec::DECODE_ERROR),
        (&[23, 3, 3, 0x41, 1][..], RECORD_OVERFLOW),
    ] {
        let mut buffer = Buffer::new();
        let (consumed, status) = buffer.feed(header);
        assert_eq!(consumed, header.len());
        assert_eq!(status, Status::Fail(expected));
        let held = buffer.len();
        let (consumed, repeated) = buffer.feed(b"ignored suffix");
        assert_eq!(consumed, 0);
        assert_eq!(repeated, Status::Fail(expected));
        assert_eq!(buffer.len(), held);
    }
    Ok(())
}
