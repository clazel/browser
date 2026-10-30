//! Regression tests for the RFC 8446 §5.4 TLSInnerPlaintext size limit.

use clazel_tls::record::{Aead, decrypt_record, open_inner_plaintext};
use clazel_tls::spec::ErrKind;

struct TestAead;

impl Aead for TestAead {
    fn tag_len(&self) -> usize {
        16
    }

    fn nonce_len(&self) -> usize {
        12
    }

    fn seal(&self, _nonce: &[u8], _ad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let mut ciphertext = plaintext.to_vec();
        ciphertext.extend_from_slice(&[0; 16]);
        ciphertext
    }

    fn open(&self, _nonce: &[u8], _ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
        let plaintext_len = ciphertext.len().checked_sub(16)?;
        Some(ciphertext.get(..plaintext_len)?.to_vec())
    }
}

const IV: [u8; 12] = [0; 12];

#[test]
fn full_inner_plaintext_limit_is_16385_bytes() {
    let mut at_limit = vec![7; 16_384];
    at_limit.push(23);
    assert!(matches!(open_inner_plaintext(at_limit), Ok((23, content)) if content.len() == 16_384));

    let mut over_limit = vec![7; 16_384];
    over_limit.extend_from_slice(&[23, 0]);
    assert_eq!(over_limit.len(), 16_386);
    assert_eq!(
        open_inner_plaintext(over_limit),
        Err(ErrKind::RecordOverflow)
    );
}

#[test]
fn oversized_all_zero_inner_plaintext_is_record_overflow() {
    let plaintext = vec![0; 16_386];
    assert_eq!(
        open_inner_plaintext(plaintext),
        Err(ErrKind::RecordOverflow)
    );
}

#[test]
fn maximum_content_allows_no_padding_but_rejects_one_padding_byte() {
    let mut no_padding = vec![7; 16_384];
    no_padding.push(23);
    assert!(matches!(
        open_inner_plaintext(no_padding),
        Ok((23, content)) if content.len() == 16_384
    ));

    let mut one_padding = vec![7; 16_384];
    one_padding.extend_from_slice(&[23, 0]);
    assert_eq!(
        open_inner_plaintext(one_padding),
        Err(ErrKind::RecordOverflow)
    );
}

#[test]
fn decrypt_rejects_oversized_inner_plaintext_within_ciphertext_limit() {
    let mut ciphertext = vec![7; 16_384];
    ciphertext.extend_from_slice(&[23, 0]);
    ciphertext.extend_from_slice(&[0; 16]);
    assert_eq!(ciphertext.len(), 16_402);
    assert!(ciphertext.len() <= 16_640);

    assert_eq!(
        decrypt_record(&TestAead, &IV, 0, &[], &ciphertext),
        Err(ErrKind::RecordOverflow)
    );
}

#[test]
fn malformed_and_empty_inner_plaintext_errors_remain_unchanged() {
    assert_eq!(
        open_inner_plaintext(Vec::new()),
        Err(ErrKind::AllZeroInnerPlaintext)
    );
    assert_eq!(
        open_inner_plaintext(vec![1, 20]),
        Err(ErrKind::BadChangeCipherSpec)
    );
    assert_eq!(
        open_inner_plaintext(vec![1, 99]),
        Err(ErrKind::UnexpectedContentType)
    );
    assert_eq!(
        open_inner_plaintext(vec![22]),
        Err(ErrKind::ZeroLengthFragment)
    );
}
