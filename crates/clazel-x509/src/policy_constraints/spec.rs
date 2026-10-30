//! RFC 5280 §4.2.1.11 PolicyConstraints.
//! <https://www.rfc-editor.org/rfc/rfc5280.html#section-4.2.1.11>
//! DER implicit tagging: ITU-T X.690 (02/2021), §§8.3, 8.14.4 and 11.5.
//! <https://www.itu.int/rec/T-REC-X.690-202102-I/en>
//!
//! ```text
//! PolicyConstraints ::= SEQUENCE {
//!     requireExplicitPolicy   [0] SkipCerts OPTIONAL,
//!     inhibitPolicyMapping    [1] SkipCerts OPTIONAL }
//! SkipCerts ::= INTEGER (0..MAX)
//! ```
//!
//! Modelling choices and limits:
//! - The input is the complete DER value inside the policyConstraints
//!   extension's OCTET STRING (id-ce-policyConstraints, 2.5.29.36). This
//!   module does not inspect the extension's criticality, and there is no
//!   central dispatch of extension decoders by OID in this crate, so the OID
//!   is only named here (`policy_constraints_oid`), as the other decoders
//!   name theirs.
//! - Both fields are OPTIONAL and IMPLICITLY tagged INTEGERs, so each is a
//!   primitive context-specific TLV `[0]` (0x80) or `[1]` (0x81) whose contents
//!   are the INTEGER's contents octets (X.690 §8.14.4). A constructed form is
//!   refused. `[0]` must precede `[1]`; a repeated or out-of-order field
//!   leaves bytes unconsumed and is refused.
//! - Empty sequence refused. RFC 5280 §4.2.1.11: "Conforming CAs MUST NOT
//!   issue certificates where policy constraints is an empty sequence. That
//!   is, at least one of the inhibitPolicyMapping field or the
//!   requireExplicitPolicy field MUST be present." The RFC then says the
//!   behaviour of a client that meets one "is not addressed". This decoder
//!   refuses it (`None`), the stricter of the two reasonable readings, so a
//!   path containing such a certificate is refused by its caller rather than
//!   given an unspecified meaning.
//! - SkipCerts is `INTEGER (0..MAX)`, so a negative value (bit 8 of the first
//!   contents octet set) is refused, as are contents octets that are not a
//!   minimal DER INTEGER (X.690 §8.3.2). The value is exposed as canonical
//!   unsigned magnitude octets (`[0]` denotes zero), as BasicConstraints'
//!   pathLenConstraint is.
//! - Size bound: a SkipCerts is accepted only if its magnitude has at most 4
//!   octets, that is, a value below 2^32. The value only counts certificates
//!   to skip along a path that the validator bounds at a few dozen certificates
//!   (path-validation design §1.12), so every value above that behaves
//!   identically, and nobody issues one above 2^32. Refusing larger values keeps
//!   the decoder exact (nothing is saturated, so no two encodings meet) and
//!   lets a caller hold the value in a `u32`. It does refuse some
//!   syntactically valid certificates, which is the conservative direction for
//!   a validator.
//! - This is syntax and typed extraction only. It does not interpret the
//!   values (RFC 5280 §6.1.3, §6.1.4) or touch any policy tree.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Parsed PolicyConstraints. Each present field holds its SkipCerts as
/// canonical unsigned magnitude octets (`[0]` for zero), at most 4 octets.
pub struct PolicyConstraints {
    /// `requireExplicitPolicy [0] SkipCerts`, if present.
    pub require_explicit_policy: Option<Seq<u8>>,
    /// `inhibitPolicyMapping [1] SkipCerts`, if present.
    pub inhibit_policy_mapping: Option<Seq<u8>>,
}

/// The most magnitude octets of a SkipCerts this decoder accepts.
pub open spec fn max_skip_certs_octets() -> nat { 4 }

/// id-ce-policyConstraints `{ 2 5 29 36 }`.
pub open spec fn policy_constraints_oid() -> Seq<nat> { seq![2nat, 5, 29, 36] }

/// RFC 5280 §4.2.1.11, `SkipCerts ::= INTEGER (0..MAX)` as the optional
/// implicit field `[number]` at `pos`: `Some(None)` when it is absent,
/// `Some(Some((magnitude, next)))` when it is present and acceptable, and
/// `None` when it is present and refused or the bytes are not well formed.
pub open spec fn parse_skip_certs(input: Seq<u8>, pos: nat, end: nat, number: u32)
    -> Option<Option<(Seq<u8>, nat)>>
    recommends pos <= end && end <= input.len()
{
    match clazel_der::spec::read_optional_context(input, pos, end, number) {
        None => None,
        Some(None) => Some(None),
        Some(Some((constructed, content_start, content_end))) => {
            let contents = input.subrange(content_start as int, content_end as int);
            // X.690 §8.14.4: implicit, so the form is the INTEGER's: primitive.
            // §8.3.1, §8.3.2: minimal INTEGER contents. INTEGER (0..MAX):
            // bit 8 of the first octet clear means non-negative (§8.3.3).
            if !constructed && clazel_der::spec::integer_contents_ok(contents) && contents[0] < 128 {
                // A leading 0x00 only pads a value whose next octet has bit 8 set.
                let magnitude_start = if contents.len() >= 2 && contents[0] == 0 {
                    content_start + 1
                } else { content_start };
                if content_end - magnitude_start <= max_skip_certs_octets() {
                    Some(Some((input.subrange(magnitude_start as int, content_end as int), content_end)))
                } else { None }
            } else { None }
        },
    }
}

/// The two OPTIONAL fields in order, consuming the SEQUENCE contents up to
/// `end`, with at least one present.
pub open spec fn parse_policy_constraints_fields(input: Seq<u8>, pos: nat, end: nat)
    -> Option<PolicyConstraints>
    recommends pos <= end && end <= input.len()
{
    match parse_skip_certs(input, pos, end, 0) {
        None => None,
        Some(require) => {
            let after_require = match require { Some((_, next)) => next, None => pos };
            match parse_skip_certs(input, after_require, end, 1) {
                None => None,
                Some(inhibit) => {
                    let after_inhibit = match inhibit { Some((_, next)) => next, None => after_require };
                    // The fields must consume the SEQUENCE. §4.2.1.11: at
                    // least one of them MUST be present; an empty SEQUENCE is
                    // refused (see the modelling choices).
                    if after_inhibit == end && (require is Some || inhibit is Some) {
                        Some(PolicyConstraints {
                            require_explicit_policy: match require { Some((value, _)) => Some(value), None => None },
                            inhibit_policy_mapping: match inhibit { Some((value, _)) => Some(value), None => None },
                        })
                    } else { None }
                },
            }
        },
    }
}

/// RFC 5280 §4.2.1.11: decode the complete PolicyConstraints SEQUENCE, with
/// exact outer consumption.
pub open spec fn parse_policy_constraints(input: Seq<u8>) -> Option<PolicyConstraints> {
    match clazel_der::spec::expect_sequence(input, 0, input.len()) {
        None => None,
        Some((start, end)) => match clazel_der::spec::read_tlv(input, 0, input.len()) {
            Some(outer) if outer.cstart == start && outer.cend == end && end == input.len() =>
                parse_policy_constraints_fields(input, start, end),
            _ => None,
        },
    }
}

} // verus!
