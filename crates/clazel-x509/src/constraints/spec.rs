//! RFC 5280 BasicConstraints, KeyUsage, and ExtendedKeyUsage models.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.3>
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.9>
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.12>
//! DER rules: ITU-T X.690 (02/2021), §§8.2, 8.3, 8.6, 11.1, 11.2, 11.5.
//! <https://www.itu.int/rec/T-REC-X.690-202102-I/en>
//!
//! Modelling choices and limits:
//! - Inputs are complete DER values contained in an extension OCTET STRING.
//! - pathLenConstraint is exposed as canonical unsigned magnitude octets
//!   (`[0]` denotes zero), avoiding a machine-integer size ceiling.
//! - A present pathLenConstraint requires cA=TRUE. Cross-extension conditions
//!   involving keyCertSign are represented separately by
//!   `basic_constraints_compatible`; this is not path validation.
//! - KeyUsage retains its DER bit octets and meaningful bit count. It accepts
//!   only named bits 0..8, requires at least one set bit, and requires the
//!   final named bit to be set under X.690 §11.2.2.
//! - ExtendedKeyUsage rejects empty lists and duplicate OIDs; arbitrary OIDs
//!   are preserved. Server-auth policy takes an explicit `allow_any` input.
//! - These routines decode syntax and expose policy inputs. They do not
//!   validate paths, signatures, trust, or unknown critical extensions.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 5280 §4.2.1.9 BasicConstraints.
pub struct BasicConstraints {
    /// Whether the certified public key may verify certificate signatures.
    pub ca: bool,
    /// Canonical unsigned INTEGER magnitude; `[0]` denotes zero.
    pub path_len_constraint: Option<Seq<u8>>,
}

/// RFC 5280 §4.2.1.3 KeyUsage named bits in order (bit numbers 0 through 8).
pub struct KeyUsage {
    /// DER BIT STRING data octets, excluding the unused-bits count octet.
    pub bits: Seq<u8>,
    /// Number of named bits represented, from 1 through 9.
    pub bit_count: nat,
}

/// Bit names assigned by RFC 5280 §4.2.1.3.
pub enum KeyUsageBit {
    /// digitalSignature (0).
    DigitalSignature,
    /// nonRepudiation/contentCommitment (1).
    ContentCommitment,
    /// keyEncipherment (2).
    KeyEncipherment,
    /// dataEncipherment (3).
    DataEncipherment,
    /// keyAgreement (4).
    KeyAgreement,
    /// keyCertSign (5).
    KeyCertSign,
    /// cRLSign (6).
    CrlSign,
    /// encipherOnly (7).
    EncipherOnly,
    /// decipherOnly (8).
    DecipherOnly,
}

/// RFC 5280 §4.2.1.12 ExtKeyUsageSyntax.
pub struct ExtendedKeyUsage {
    /// Purpose OIDs in encoded order.
    pub purposes: Seq<Seq<nat>>,
}

/// Map a named KeyUsage bit to its X.509 bit number.
pub open spec fn key_usage_bit_index(bit: KeyUsageBit) -> nat {
    match bit {
        KeyUsageBit::DigitalSignature => 0,
        KeyUsageBit::ContentCommitment => 1,
        KeyUsageBit::KeyEncipherment => 2,
        KeyUsageBit::DataEncipherment => 3,
        KeyUsageBit::KeyAgreement => 4,
        KeyUsageBit::KeyCertSign => 5,
        KeyUsageBit::CrlSign => 6,
        KeyUsageBit::EncipherOnly => 7,
        KeyUsageBit::DecipherOnly => 8,
    }
}

/// Whether the named KeyUsage bit is asserted.
pub open spec fn key_usage_has(usage: KeyUsage, bit: KeyUsageBit) -> bool {
    let index = key_usage_bit_index(bit);
    index < usage.bit_count && index < usage.bits.len() * 8
        && usage.bits[index as int / 8]
            as nat / clazel_der::spec::pow2_unused((7 - index % 8) as u8) % 2 == 1
}

/// RFC 5280 §4.2.1.9: decode the complete BasicConstraints value.
pub open spec fn parse_basic_constraints(input: Seq<u8>) -> Option<BasicConstraints> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == start && outer.cend == end && end == input.len() =>
                parse_basic_constraints_fields(input, start, end),
            _ => None,
        },
    }
}

/// Parse the ordered cA DEFAULT FALSE and optional pathLenConstraint fields.
pub open spec fn parse_basic_constraints_fields(input: Seq<u8>, start: nat, end: nat)
    -> Option<BasicConstraints>
    recommends start <= end && end <= input.len()
{
    if start == end {
        Some(BasicConstraints { ca: false, path_len_constraint: None })
    } else { match clazel_der::spec::read_tlv(input, start, end) {
        None => None,
        Some(first) if first.tag == clazel_der::spec::universal_primitive(clazel_der::spec::BOOLEAN) =>
            match clazel_der::spec::read_boolean(input, start, end) {
                Some((true, after_ca)) => parse_path_len(input, after_ca, end, true),
                // DER §11.5: the DEFAULT FALSE cA field must be omitted.
                _ => None,
            },
        Some(_) => parse_path_len(input, start, end, false),
    }}
}

/// Parse an optional nonnegative pathLenConstraint and consume the SEQUENCE.
pub open spec fn parse_path_len(input: Seq<u8>, pos: nat, end: nat, ca: bool)
    -> Option<BasicConstraints>
    recommends pos <= end && end <= input.len()
{
    if pos == end {
        Some(BasicConstraints { ca, path_len_constraint: None })
    } else if !ca {
        None
    } else {
        match clazel_der::spec::read_integer(input, pos, end) {
            Some((false, magnitude_start, magnitude_end, next)) if next == end =>
                Some(BasicConstraints {
                    ca: true,
                    path_len_constraint: Some(input.subrange(magnitude_start as int, magnitude_end as int)),
                }),
            _ => None,
        }
    }
}

/// RFC 5280 §4.2.1.3 and X.690 §§8.6, 11.2: decode KeyUsage.
pub open spec fn parse_key_usage(input: Seq<u8>) -> Option<KeyUsage> {
    match clazel_der::spec::read_bit_string(input, 0, input.len()) {
        Some((unused, start, end, next)) if next == input.len() => {
            let count = ((end - start) * 8 - (unused as int)) as nat;
            if count > 0 && count <= 9
                && (input[(end - 1) as int] as nat) % clazel_der::spec::pow2_unused(unused) == 0
                && (input[(end - 1) as int] as nat)
                    / clazel_der::spec::pow2_unused(unused) % 2 == 1 {
                Some(KeyUsage { bits: input.subrange(start as int, end as int), bit_count: count })
            } else { None }
        },
        _ => None,
    }
}

/// OID membership in a purpose list.
pub open spec fn oid_in(purposes: Seq<Seq<nat>>, oid: Seq<nat>, i: int) -> bool
    recommends 0 <= i <= purposes.len()
    decreases purposes.len() as int - i
{
    i < purposes.len() && (purposes[i] =~= oid || oid_in(purposes, oid, i + 1))
}

/// RFC 5280 id-ce-extKeyUsage OID `{ 2 5 29 37 }`.
pub open spec fn extended_key_usage_oid() -> Seq<nat> { seq![2nat, 5, 29, 37] }

/// anyExtendedKeyUsage OID `{ 2 5 29 37 0 }`.
pub open spec fn any_extended_key_usage_oid() -> Seq<nat> { seq![2nat, 5, 29, 37, 0] }

/// TLS WWW server authentication OID `{ 1 3 6 1 5 5 7 3 1 }`.
pub open spec fn server_auth_oid() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 1] }

/// Parse ExtKeyUsageSyntax with nonempty, unique OIDs.
pub open spec fn parse_extended_key_usage(input: Seq<u8>) -> Option<ExtendedKeyUsage> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == start && outer.cend == end && end == input.len()
                && start < end => match parse_eku_items(input, start, end, seq![], seq![]) {
                    Some((purposes, final_pos)) if final_pos == end && purposes.len() > 0 =>
                        Some(ExtendedKeyUsage { purposes }),
                    _ => None,
                },
            _ => None,
        },
    }
}

/// Scan OID elements iteratively via an accumulator and reject duplicates.
pub open spec fn parse_eku_items(input: Seq<u8>, pos: nat, end: nat,
    seen: Seq<Seq<nat>>, acc: Seq<Seq<nat>>) -> Option<(Seq<Seq<nat>>, nat)>
    recommends pos <= end && end <= input.len()
    decreases end - pos
{
    if pos == end { Some((acc, end)) }
    else { match clazel_der::spec::read_oid(input, pos, end) {
        Some((oid, next)) if next > pos && next <= end && !oid_in(seen, oid, 0) =>
            parse_eku_items(input, next, end, seen.push(oid), acc.push(oid)),
        _ => None,
    }}
}

/// Cross-extension cA/keyCertSign and pathLen profile conditions.
pub open spec fn basic_constraints_compatible(
    basic: Option<BasicConstraints>, key_usage: Option<KeyUsage>,
) -> bool {
    let cert_sign = match key_usage {
        Some(usage) => key_usage_has(usage, KeyUsageBit::KeyCertSign),
        None => false,
    };
    match basic {
        Some(value) => (!cert_sign || value.ca)
            && (value.path_len_constraint.is_none() || value.ca && cert_sign),
        None => !cert_sign,
    }
}

/// Explicit application policy for serverAuth and anyExtendedKeyUsage.
pub open spec fn eku_allows_server_auth(eku: ExtendedKeyUsage, allow_any: bool) -> bool {
    oid_in(eku.purposes, server_auth_oid(), 0)
        || (allow_any && oid_in(eku.purposes, any_extended_key_usage_oid(), 0))
}

} // verus!
