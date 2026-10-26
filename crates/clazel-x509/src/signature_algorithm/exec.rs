//! Executable RFC 5280 signature algorithm profile selection.

#[allow(unused_imports)]
use super::spec::*;
use crate::certificate::exec::AlgorithmIdentifier;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// SHA-2 hash selection for the supported RSA PKCS #1 v1.5 signatures.
#[derive(Clone, Copy)]
pub enum RsaPkcs1v15Hash {
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
}

pub open spec fn view_hash(value: RsaPkcs1v15Hash) -> super::spec::RsaPkcs1v15Hash {
    match value {
        RsaPkcs1v15Hash::Sha256 => super::spec::RsaPkcs1v15Hash::Sha256,
        RsaPkcs1v15Hash::Sha384 => super::spec::RsaPkcs1v15Hash::Sha384,
        RsaPkcs1v15Hash::Sha512 => super::spec::RsaPkcs1v15Hash::Sha512,
    }
}

fn same_hash(first: RsaPkcs1v15Hash, second: RsaPkcs1v15Hash) -> (result: bool)
    ensures result == (view_hash(first) == view_hash(second))
{
    matches!((first, second),
        (RsaPkcs1v15Hash::Sha256, RsaPkcs1v15Hash::Sha256)
        | (RsaPkcs1v15Hash::Sha384, RsaPkcs1v15Hash::Sha384)
        | (RsaPkcs1v15Hash::Sha512, RsaPkcs1v15Hash::Sha512))
}

/// Supported profile or an explicit marker for algorithms outside this slice.
#[derive(Clone, Copy)]
pub enum AlgorithmClass {
    /// An implemented RSA PKCS #1 v1.5 SHA-2 profile.
    Supported(RsaPkcs1v15Hash),
    /// An algorithm whose profile is not implemented here.
    Unsupported,
}

pub open spec fn view_class(value: AlgorithmClass) -> super::spec::AlgorithmClass {
    match value {
        AlgorithmClass::Supported(hash) => super::spec::AlgorithmClass::Supported(view_hash(hash)),
        AlgorithmClass::Unsupported => super::spec::AlgorithmClass::Unsupported,
    }
}

pub open spec fn view_class_result(value: Option<AlgorithmClass>) -> Option<super::spec::AlgorithmClass> {
    match value { Some(class) => Some(view_class(class)), None => None }
}

/// Resulting inputs for a verifier; preparation does not verify a signature.
pub struct PreparedSignatureInput<'a> {
    /// The parsed signature AlgorithmIdentifier from TBSCertificate.
    pub tbs_algorithm: &'a AlgorithmIdentifier<'a>,
    /// The parsed outer Certificate signatureAlgorithm.
    pub outer_algorithm: &'a AlgorithmIdentifier<'a>,
    /// Supported profile, or Unsupported with both identifiers retained.
    pub class: AlgorithmClass,
    /// Exact DER bytes of the signed TBSCertificate.
    pub tbs_der: &'a [u8],
    /// Signature BIT STRING data bytes, excluding the unused-bit-count octet.
    pub signature_bits: &'a [u8],
    /// BIT STRING unused-bit count.
    pub signature_unused_bits: u8,
}

pub open spec fn view_prepared(value: &PreparedSignatureInput<'_>) -> super::spec::PreparedSignature {
    super::spec::PreparedSignature {
        tbs_algorithm: crate::certificate::contract::view_algorithm_identifier(value.tbs_algorithm),
        outer_algorithm: crate::certificate::contract::view_algorithm_identifier(value.outer_algorithm),
        class: view_class(value.class),
        tbs_der: value.tbs_der@,
        signature_bits: value.signature_bits@,
        signature_unused_bits: value.signature_unused_bits,
    }
}

pub open spec fn view_prepared_result(
    value: Option<PreparedSignatureInput<'_>>,
) -> Option<super::spec::PreparedSignature> {
    match value { Some(input) => Some(view_prepared(&input)), None => None }
}

/// RFC 4055 §5: identify the SHA-256-with-RSA PKCS #1 v1.5 OID.
fn is_sha256_oid(oid: &[u64]) -> (result: bool)
    ensures result == super::spec::is_sha256_with_rsa(clazel_der::decode::nats(oid@))
{
    oid.len() == 7
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&2)
        && oid.get(2) == Some(&840)
        && oid.get(3) == Some(&113549)
        && oid.get(4) == Some(&1)
        && oid.get(5) == Some(&1)
        && oid.get(6) == Some(&11)
}

/// RFC 4055 §5: identify the SHA-384-with-RSA PKCS #1 v1.5 OID.
fn is_sha384_oid(oid: &[u64]) -> (result: bool)
    ensures result == super::spec::is_sha384_with_rsa(clazel_der::decode::nats(oid@))
{
    oid.len() == 7
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&2)
        && oid.get(2) == Some(&840)
        && oid.get(3) == Some(&113549)
        && oid.get(4) == Some(&1)
        && oid.get(5) == Some(&1)
        && oid.get(6) == Some(&12)
}

/// RFC 4055 §5: identify the SHA-512-with-RSA PKCS #1 v1.5 OID.
fn is_sha512_oid(oid: &[u64]) -> (result: bool)
    ensures result == super::spec::is_sha512_with_rsa(clazel_der::decode::nats(oid@))
{
    oid.len() == 7
        && oid.first() == Some(&1)
        && oid.get(1) == Some(&2)
        && oid.get(2) == Some(&840)
        && oid.get(3) == Some(&113549)
        && oid.get(4) == Some(&1)
        && oid.get(5) == Some(&1)
        && oid.get(6) == Some(&13)
}

/// Read a safely bounded octet of an optional AlgorithmIdentifier parameter.
fn parameter_octet(input: &[u8], index: usize) -> (result: u8)
    ensures index < input.len() ==> result == input@[index as int]
{
    match input.get(index) { Some(&value) => value, None => 0 }
}

/// Check exact DER NULL parameters, preserving RFC 4055's absent alternative.
fn is_null_or_absent(parameters: Option<&[u8]>) -> (result: bool)
    ensures result == match parameters {
        Some(bytes) => bytes@ =~= seq![0x05u8, 0x00u8],
        None => true,
    }
{
    match parameters {
        None => true,
        Some(bytes) => {
            let first = parameter_octet(bytes, 0);
            let second = parameter_octet(bytes, 1);
            let result = bytes.len() == 2 && first == 0x05 && second == 0x00;
            proof {
                assert(bytes@.len() == bytes.len());
                if result {
                    assert(first == bytes@[0]);
                    assert(second == bytes@[1]);
                    assert(bytes@ =~= seq![0x05u8, 0x00u8]);
                }
                if bytes@ =~= seq![0x05u8, 0x00u8] {
                    assert(bytes.len() == 2);
                    assert(first == 0x05);
                    assert(second == 0x00);
                }
            }
            result
        }
    }
}

/// RFC 5280 §4.1.1.2 and RFC 4055 §5: decode a supported SHA-2 RSA profile.
pub fn classify(algorithm: &AlgorithmIdentifier) -> (result: Option<AlgorithmClass>)
    ensures super::contract::classify_ensures(
        crate::certificate::contract::view_algorithm_identifier(algorithm),
        view_class_result(result),
    )
{
    if is_sha256_oid(&algorithm.oid) {
        if is_null_or_absent(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha256))
        } else { None }
    } else if is_sha384_oid(&algorithm.oid) {
        if is_null_or_absent(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha384))
        } else { None }
    } else if is_sha512_oid(&algorithm.oid) {
        if is_null_or_absent(algorithm.parameters_der) {
            Some(AlgorithmClass::Supported(RsaPkcs1v15Hash::Sha512))
        } else { None }
    } else {
        Some(AlgorithmClass::Unsupported)
    }
}

/// Compare optional raw parameter TLVs without interpreting unknown algorithms.
fn parameters_equal(first: Option<&[u8]>, second: Option<&[u8]>) -> (result: bool)
    ensures result == match (first, second) {
        (None, None) => true,
        (Some(a), Some(b)) => a@ == b@,
        _ => false,
    }
{
    match (first, second) {
        (None, None) => true,
        (Some(a), Some(b)) => equal_bytes(a, b),
        _ => false,
    }
}

/// Compare byte slices and refine equality to their Verus sequence views.
fn equal_bytes(first: &[u8], second: &[u8]) -> (result: bool)
    ensures result == (first@ == second@)
{
    if first.len() != second.len() { return false; }
    let mut index = 0usize;
    while index < first.len()
        invariant
            index <= first.len(),
            first.len() == second.len(),
            forall|i: int| 0 <= i < index as int ==> first@[i] == second@[i],
        decreases first.len() - index
    {
        match (first.get(index), second.get(index)) {
            (Some(a), Some(b)) if *a != *b => return false,
            _ => {},
        }
        index = index.saturating_add(1);
    }
    proof { assert(first@ =~= second@); }
    true
}

/// Compare OID arcs and refine equality to their natural-number views.
fn equal_oid(first: &[u64], second: &[u64]) -> (result: bool)
    ensures result == (clazel_der::decode::nats(first@) == clazel_der::decode::nats(second@))
{
    if first.len() != second.len() {
        proof {
            reveal(clazel_der::decode::nats);
            assert(clazel_der::decode::nats(first@).len() == first.len());
            assert(clazel_der::decode::nats(second@).len() == second.len());
            assert(clazel_der::decode::nats(first@) != clazel_der::decode::nats(second@));
        }
        return false;
    }
    let mut index = 0usize;
    while index < first.len()
        invariant
            index <= first.len(),
            first.len() == second.len(),
            forall|i: int| 0 <= i < index as int ==> first@[i] == second@[i],
        decreases first.len() - index
    {
        match (first.get(index), second.get(index)) {
            (Some(a), Some(b)) if *a != *b => {
                proof {
                    assert(first@[index as int] == *a);
                    assert(second@[index as int] == *b);
                    reveal(clazel_der::decode::nats);
                    assert(clazel_der::decode::nats(first@)[index as int] == *a as nat);
                    assert(clazel_der::decode::nats(second@)[index as int] == *b as nat);
                    assert(clazel_der::decode::nats(first@) != clazel_der::decode::nats(second@));
                }
                return false;
            },
            _ => {},
        }
        index = index.saturating_add(1);
    }
    proof {
        assert(first@ =~= second@);
        assert(clazel_der::decode::nats(first@) == clazel_der::decode::nats(second@));
    }
    true
}

/// RFC 5280 §4.1.1.2: compare unsupported AlgorithmIdentifier OID and parameters.
fn unsupported_identifiers_equal(first: &AlgorithmIdentifier, second: &AlgorithmIdentifier)
    -> (result: bool)
    ensures result == super::spec::unsupported_identifiers_equal(
        crate::certificate::contract::view_algorithm_identifier(first),
        crate::certificate::contract::view_algorithm_identifier(second),
    )
{
    equal_oid(&first.oid, &second.oid) && parameters_equal(first.parameters_der, second.parameters_der)
}

/// RFC 5280 §4.1.1.2/.3: match TBS and outer algorithm identifiers and prepare
/// a verifier input. This function performs no cryptographic operation.
pub fn prepare_signature_input<'a>(
    tbs_algorithm: &'a AlgorithmIdentifier<'a>,
    outer_algorithm: &'a AlgorithmIdentifier<'a>,
    tbs_der: &'a [u8],
    signature_unused_bits: u8,
    signature_bits: &'a [u8],
) -> (result: Option<PreparedSignatureInput<'a>>)
    ensures super::contract::prepare_signature_ensures(
        crate::certificate::contract::view_algorithm_identifier(tbs_algorithm),
        crate::certificate::contract::view_algorithm_identifier(outer_algorithm),
        tbs_der@,
        signature_bits@,
        signature_unused_bits,
        view_prepared_result(result),
    )
{
    let tbs_class = classify(tbs_algorithm)?;
    let outer_class = classify(outer_algorithm)?;
    let class = match (tbs_class, outer_class) {
        (AlgorithmClass::Supported(tbs_hash), AlgorithmClass::Supported(outer_hash)) => {
            if !same_hash(tbs_hash, outer_hash) || signature_unused_bits != 0 { return None; }
            AlgorithmClass::Supported(tbs_hash)
        }
        (AlgorithmClass::Unsupported, AlgorithmClass::Unsupported) => {
            if !unsupported_identifiers_equal(tbs_algorithm, outer_algorithm) { return None; }
            AlgorithmClass::Unsupported
        }
        _ => return None,
    };
    Some(PreparedSignatureInput {
        tbs_algorithm,
        outer_algorithm,
        class,
        tbs_der,
        signature_bits,
        signature_unused_bits,
    })
}

} // verus!
