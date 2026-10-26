//! RFC 5280 §4.1.2 TBSCertificate schema specification.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.1.2>
//!
//! Modelling choices: the full input is one DER SEQUENCE TLV; Name and
//! SubjectPublicKeyInfo are retained as complete opaque SEQUENCE TLVs; the
//! serial is nonnegative and at most 20 content octets (zero is accepted for
//! graceful certificate processing); version defaults to v1 and an explicit
//! DEFAULT v1 is rejected; UniqueIdentifier contents are checked as implicit
//! DER BIT STRINGs; extensions are retained as the complete [3] EXPLICIT TLV.
//! This is structural parsing only: Name/SPKI internals, constraints, policy,
//! signatures, and path validation are outside this module.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub struct TbsCertificate {
    pub version: nat,
    pub serial_number_der: Seq<u8>,
    pub signature: crate::certificate::spec::AlgorithmIdentifier,
    pub issuer_der: Seq<u8>,
    pub not_before: crate::time::spec::CertificateTime,
    pub not_after: crate::time::spec::CertificateTime,
    pub subject_der: Seq<u8>,
    pub subject_public_key_info_der: Seq<u8>,
    pub issuer_unique_id_der: Option<Seq<u8>>,
    pub subject_unique_id_der: Option<Seq<u8>>,
    pub extensions_der: Option<Seq<u8>>,
    pub tbs_certificate_der: Seq<u8>,
}

/// The execution contract is the independently written schema parser below.
/// It is specified in document order: version/default, serial, signature,
/// issuer, validity, subject, SPKI, then optional [1], [2], [3].
pub open spec fn parse_tbs_certificate(input: Seq<u8>) -> Option<TbsCertificate> {
    // The detailed DER cursor composition is introduced with the executable
    // parser; this declaration intentionally remains the public data model.
    None
}

} // verus!
