//! Certified witnesses for partial leaf-check policy mutations.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A critical extension whose semantics this leaf profile does not process
/// prevents even a matching SAN from producing partial leaf evidence.
pub proof fn lemma_unknown_critical_extension_blocks_leaf_result()
    ensures check_extensions(
        seq![
            crate::extensions::spec::Extension {
                oid: seq![2nat, 5, 29, 17], critical: false,
                value: seq![0x30u8, 0x12, 0x82, 0x10,
                    b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
            },
            crate::extensions::spec::Extension {
                oid: seq![1nat, 2, 3], critical: true, value: seq![0x05u8, 0x00],
            },
        ],
        crate::tbs::spec::TbsCertificate {
            version: 2,
            serial_number_der: seq![0x02u8, 0x01, 0x01],
            signature: crate::certificate::spec::AlgorithmIdentifier { oid: seq![1nat, 2, 3], parameters_der: None },
            issuer_der: seq![0x30u8, 0x00],
            not_before: crate::time::spec::CertificateTime { year: 2026, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            not_after: crate::time::spec::CertificateTime { year: 2027, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            subject_der: seq![0x30u8, 0x00],
            subject_public_key_info_der: seq![0x30u8, 0x00],
            issuer_unique_id_der: None, subject_unique_id_der: None,
            extensions_der: None, extensions_sequence_der: None,
            tbs_certificate_der: seq![0x30u8, 0x00],
        },
        crate::spec::ReferenceIdentity::Dns(seq![b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't']),
        crate::time::spec::CertificateTime { year: 2026, month: 6, day: 1, hour: 0, minute: 0, second: 0 },
        LeafPolicy { allow_any_extended_key_usage: false },
    ) is None
{
    assert(!supported_critical_extensions(seq![
        crate::extensions::spec::Extension {
            oid: seq![2nat, 5, 29, 17], critical: false,
            value: seq![0x30u8, 0x12, 0x82, 0x10,
                b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
        },
        crate::extensions::spec::Extension { oid: seq![1nat, 2, 3], critical: true, value: seq![0x05u8, 0x00] },
    ], 0)) by (compute_only);
    assert(check_extensions(
        seq![
            crate::extensions::spec::Extension {
                oid: seq![2nat, 5, 29, 17], critical: false,
                value: seq![0x30u8, 0x12, 0x82, 0x10,
                    b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't'],
            },
            crate::extensions::spec::Extension { oid: seq![1nat, 2, 3], critical: true, value: seq![0x05u8, 0x00] },
        ],
        crate::tbs::spec::TbsCertificate {
            version: 2,
            serial_number_der: seq![0x02u8, 0x01, 0x01],
            signature: crate::certificate::spec::AlgorithmIdentifier { oid: seq![1nat, 2, 3], parameters_der: None },
            issuer_der: seq![0x30u8, 0x00],
            not_before: crate::time::spec::CertificateTime { year: 2026, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            not_after: crate::time::spec::CertificateTime { year: 2027, month: 1, day: 1, hour: 0, minute: 0, second: 0 },
            subject_der: seq![0x30u8, 0x00], subject_public_key_info_der: seq![0x30u8, 0x00],
            issuer_unique_id_der: None, subject_unique_id_der: None,
            extensions_der: None, extensions_sequence_der: None, tbs_certificate_der: seq![0x30u8, 0x00],
        },
        crate::spec::ReferenceIdentity::Dns(seq![b'w', b'w', b'w', b'.', b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b't', b'e', b's', b't']),
        crate::time::spec::CertificateTime { year: 2026, month: 6, day: 1, hour: 0, minute: 0, second: 0 },
        LeafPolicy { allow_any_extended_key_usage: false },
    ) is None) by (compute_only);
}

} // verus!
