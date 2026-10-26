//! RFC 9525 §6.3 and §6.4 service identity matching, as published in
//! November 2023: <https://www.rfc-editor.org/rfc/rfc9525.html>.
//!
//! Modelling choices:
//! - The URL layer supplies canonical ASCII DNS references, including
//!   A-labels; this module does not perform IDNA conversion (§6.3).
//! - Inputs are byte sequences. Non-ASCII DNS bytes are invalid and cannot
//!   match. ASCII case folding applies only to letters A through Z (§6.3).
//! - DNS references are fully qualified names without a terminal root dot.
//!   Presented DNS-IDs use the same form, except a single `*` may be the
//!   complete left-most label (§6.3). Empty labels are rejected.
//! - The caller supplies IP addresses as exactly 4 or 16 octets. Textual IP
//!   parsing and host classification are outside this matching function.
//! - A wildcard suffix is rejected when it is a Public Suffix List public
//!   suffix. This veto is additional browser policy; RFC 9525 defines the
//!   matching algorithm but does not require public-suffix filtering. The
//!   repository's complete table (ICANN and PRIVATE sections) is
//!   used after lower-casing the ASCII suffix. This prevents wildcards such
//!   as `*.co.uk`, `*.com`, and `*.github.io` from crossing a registry or
//!   hosted-service boundary while allowing a registrable suffix such as
//!   `*.example.co.uk`. PSL exception rules follow the existing PSL spec.
//! - This slice includes only DNS-ID and IP-ID. SRV-ID, URI-ID, Common Name
//!   fallback, DER decoding, certificate path validation and trust are out
//!   of scope.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A typed reference identity. `Dns` is canonical ASCII supplied by URL;
/// `Ip` is a binary IPv4 or IPv6 address.
pub enum ReferenceIdentity {
    /// A canonical ASCII DNS reference from the URL layer.
    Dns(Seq<u8>),
    /// A binary IPv4 or IPv6 reference.
    Ip(Seq<u8>),
}

/// A typed identifier extracted from subjectAltName.
pub enum PresentedIdentity {
    /// A dNSName subjectAltName value.
    Dns(Seq<u8>),
    /// An iPAddress subjectAltName value.
    Ip(Seq<u8>),
}

/// ASCII DNS-name shape used by this slice: nonempty labels of letters,
/// digits, hyphen, or A-label hyphen; no empty labels or terminal dot.
pub open spec fn dns_name_shape(name: Seq<u8>) -> bool {
    valid_name_from(name, 0)
}

/// Every DNS label is nonempty and each byte is in the RFC preferred-name
/// ASCII alphabet. `i` is the next byte to inspect.
pub open spec fn valid_name_from(name: Seq<u8>, i: int) -> bool
    recommends 0 <= i <= name.len()
    decreases name.len() as int - i
{
    if i >= name.len() as int {
        false
    } else if name[i] == b'.' {
        i > 0 && i + 1 < name.len() as int && name[i + 1] != b'.'
            && valid_name_from(name, i + 1)
    } else {
        let b = name[i];
        (b >= b'a' && b <= b'z' || b >= b'A' && b <= b'Z'
            || b >= b'0' && b <= b'9' || b == b'-')
            && (i + 1 == name.len() as int || valid_name_from(name, i + 1))
    }
}

/// RFC 9525 §6.3 compares DNS labels using case-insensitive ASCII.
/// The wildcard case is handled by `dns_match`.
pub open spec fn ascii_fold(b: u8) -> nat {
    if b >= b'A' && b <= b'Z' { (b | 0x20) as nat } else { b as nat }
}

/// Case-insensitive ASCII equality from position `i` onward.
pub open spec fn folded_equal_from(a: Seq<u8>, b: Seq<u8>, i: int) -> bool
    recommends a.len() == b.len() && 0 <= i <= a.len()
    decreases a.len() as int - i
{
    a.len() == b.len() && if i >= a.len() as int { true }
    else { ascii_fold(a[i]) == ascii_fold(b[i]) && folded_equal_from(a, b, i + 1) }
}

/// Locate the first label separator; `name.len()` means none exists.
pub open spec fn first_dot(name: Seq<u8>, i: int) -> int
    recommends 0 <= i <= name.len()
    decreases name.len() as int - i
{
    if i >= name.len() as int { name.len() as int }
    else if name[i] == b'.' { i }
    else { first_dot(name, i + 1) }
}

/// No wildcard byte occurs in a DNS suffix.
pub open spec fn no_wildcard_from(name: Seq<u8>, i: int) -> bool
    recommends 0 <= i <= name.len()
    decreases name.len() as int - i
{
    if i >= name.len() as int { true }
    else { name[i] != b'*' && no_wildcard_from(name, i + 1) }
}

/// Convert a valid DNS suffix to the lower-case code points consumed by PSL.
pub open spec fn psl_domain_from_ascii(name: Seq<u8>) -> Seq<u32> {
    name.map_values(|byte: u8| if byte >= b'A' && byte <= b'Z' {
        (byte as int + 32) as u32
    } else { byte as u32 })
}

/// True when a DNS wildcard suffix is itself a PSL public suffix.
pub open spec fn wildcard_suffix_is_public_suffix(name: Seq<u8>) -> bool {
    clazel_psl::spec::is_public_suffix(
        clazel_psl::table::psl_rules(), psl_domain_from_ascii(name))
}

/// RFC 9525 §6.3's one-label wildcard comparison after the PSL policy gate.
/// Keeping this helper independent of the PSL lookup makes its matching proof
/// transparent while `dns_match` still requires the public-suffix veto.
pub open spec fn wildcard_matches_reference(reference: Seq<u8>, suffix: Seq<u8>) -> bool {
    let dot = first_dot(reference, 0);
    dot > 0 && dot < reference.len()
        && folded_equal_from(
            reference.subrange(dot + 1, reference.len() as int), suffix, 0)
}

/// RFC 9525 §6.3 label matching; the executable algorithm and proof are
/// supplied in the implementation commit.
pub open spec fn dns_match(reference: Seq<u8>, presented: Seq<u8>) -> bool {
    if !dns_name_shape(reference) { false }
    else if dns_name_shape(presented) {
        folded_equal_from(reference, presented, 0)
    } else if presented.len() > 2 && presented[0] == b'*' && presented[1] == b'.'
        && dns_name_shape(presented.subrange(2, presented.len() as int))
        && no_wildcard_from(presented, 2)
        && !wildcard_suffix_is_public_suffix(presented.subrange(2, presented.len() as int))
    { wildcard_matches_reference(reference, presented.subrange(2, presented.len() as int)) }
    else { false }
}

/// RFC 9525 §6.4 requires octet-for-octet comparison of IP-ID values.
pub open spec fn ip_match(reference: Seq<u8>, presented: Seq<u8>) -> bool {
    (reference.len() == 4 || reference.len() == 16)
        && reference =~= presented
}

/// RFC 9525 §6.2 selects DNS comparison for DNS-ID and binary IP comparison
/// for IP-ID. Different identifier kinds never substitute for one another.
pub open spec fn service_identity_match(
    reference: ReferenceIdentity,
    presented: PresentedIdentity,
) -> bool {
    match (reference, presented) {
        (ReferenceIdentity::Dns(r), PresentedIdentity::Dns(p)) => dns_match(r, p),
        (ReferenceIdentity::Ip(r), PresentedIdentity::Ip(p)) => ip_match(r, p),
        _ => false,
    }
}

} // verus!
