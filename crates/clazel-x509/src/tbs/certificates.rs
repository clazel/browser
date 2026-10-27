//! Hosts for certified RFC 5280 TBSCertificate-spec mutation witnesses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A DER DEFAULT v1 version must be omitted.
pub proof fn lemma_reject_explicit_default_v1()
    ensures parse_version(seq![0xa0u8, 0x03, 0x02, 0x01, 0x00], 0, 5) is None
{
    assert(parse_version(seq![0xa0u8, 0x03, 0x02, 0x01, 0x00], 0, 5) is None) by (compute_only);
}

/// RFC 5280 v1 certificates do not carry issuerUniqueID or subjectUniqueID.
pub proof fn lemma_reject_v1_unique_id()
    ensures optional_unique(seq![0x81u8, 0x02, 0x00, 0x80], 0, 4, 1, 0) is None
{
    assert(optional_unique(seq![0x81u8, 0x02, 0x00, 0x80], 0, 4, 1, 0) is None) by (compute_only);
}

/// RFC 5280 permits Extensions only for version 3 certificates.
pub proof fn lemma_reject_v2_extensions()
    ensures optional_extensions(seq![0xa3u8, 0x02, 0x30, 0x00], 0, 4, 1) is None
{
    assert(optional_extensions(seq![0xa3u8, 0x02, 0x30, 0x00], 0, 4, 1) is None) by (compute_only);
}

/// TBSCertificate signature input includes its complete outer SEQUENCE TLV.
pub proof fn lemma_prefix_preserves_complete_tlv()
    ensures match parse_prefix(seq![0x30u8, 0x03, 0x02, 0x01, 0x01]) {
        Some(prefix) => prefix.tbs_der =~= seq![0x30u8, 0x03, 0x02, 0x01, 0x01],
        None => false,
    }
{
    assert(match parse_prefix(seq![0x30u8, 0x03, 0x02, 0x01, 0x01]) {
        Some(prefix) => prefix.tbs_der =~= seq![0x30u8, 0x03, 0x02, 0x01, 0x01],
        None => false,
    }) by (compute_only);
}

} // verus!
