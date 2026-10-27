//! Executable identity matcher, refined to the functions in `spec`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A reference identifier with an explicit DNS or binary IP type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReferenceIdentity<'a> {
    /// Canonical ASCII DNS name supplied by the URL layer.
    Dns(&'a [u8]),
    /// Four-octet IPv4 or sixteen-octet IPv6 address.
    Ip(&'a [u8]),
}

/// A typed identifier extracted from subjectAltName.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PresentedIdentity<'a> {
    /// X.509 dNSName value.
    Dns(&'a [u8]),
    /// X.509 iPAddress value.
    Ip(&'a [u8]),
}

impl View for ReferenceIdentity<'_> {
    type V = super::spec::ReferenceIdentity;
    closed spec fn view(&self) -> Self::V {
        view_reference_identity(self)
    }
}

/// Public mapping for composing certificate identity checks with parsed SANs.
pub open spec fn view_reference_identity(value: &ReferenceIdentity<'_>) -> super::spec::ReferenceIdentity {
    match value {
        ReferenceIdentity::Dns(name) => super::spec::ReferenceIdentity::Dns(name@),
        ReferenceIdentity::Ip(address) => super::spec::ReferenceIdentity::Ip(address@),
    }
}

impl View for PresentedIdentity<'_> {
    type V = super::spec::PresentedIdentity;
    closed spec fn view(&self) -> Self::V {
        view_presented_identity(self)
    }
}

/// Public mapping for composed matcher proofs.
pub open spec fn view_presented_identity(value: &PresentedIdentity<'_>) -> super::spec::PresentedIdentity {
    match value {
        PresentedIdentity::Dns(name) => super::spec::PresentedIdentity::Dns(name@),
        PresentedIdentity::Ip(address) => super::spec::PresentedIdentity::Ip(address@),
    }
}

fn valid_name_from_exec(name: &[u8], i: usize) -> (result: bool)
    requires i <= name.len()
    ensures result == valid_name_from(name@, i as int)
    decreases name.len() - i
{
    if i >= name.len() {
        false
    } else {
        let Some(byte_ref) = name.get(i) else { return false; };
        let byte = *byte_ref;
        if byte == b'.' {
            let Some(next_i) = i.checked_add(1) else { return false; };
            let next_is_dot = name.get(next_i) == Some(&b'.');
            i > 0 && next_i < name.len() && !next_is_dot
                && valid_name_from_exec(name, next_i)
        } else {
            let allowed = matches!(byte, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'-');
            let Some(next_i) = i.checked_add(1) else { return false; };
            allowed && (next_i == name.len() || valid_name_from_exec(name, next_i))
        }
    }
}

fn valid_dns_exec(name: &[u8]) -> (result: bool)
    ensures result == dns_name_shape(name@)
{
    valid_name_from_exec(name, 0)
}

fn folded_equal_from_exec(a: &[u8], b: &[u8], i: usize) -> (result: bool)
    requires a.len() == b.len(), i <= a.len()
    ensures result == folded_equal_from(a@, b@, i as int)
    decreases a.len() - i
{
    if i >= a.len() {
        true
    } else {
        let (Some(x_ref), Some(y_ref)) = (a.get(i), b.get(i)) else { return false; };
        let x = *x_ref;
        let y = *y_ref;
        let fx = match x { b'A'..=b'Z' => x | 0x20, _ => x };
        let fy = match y { b'A'..=b'Z' => y | 0x20, _ => y };
        let Some(next_i) = i.checked_add(1) else { return false; };
        fx == fy && folded_equal_from_exec(a, b, next_i)
    }
}

fn ascii_equal_exec(a: &[u8], b: &[u8]) -> (result: bool)
    ensures result == folded_equal_from(a@, b@, 0)
{
    if a.len() != b.len() { false }
    else { folded_equal_from_exec(a, b, 0) }
}

fn first_dot_exec(name: &[u8], i: usize) -> (result: usize)
    requires i <= name.len()
    ensures result as int == first_dot(name@, i as int)
    decreases name.len() - i
{
    if i >= name.len() { name.len() }
    else if name.get(i) == Some(&b'.') { i }
    else {
        let Some(next_i) = i.checked_add(1) else { return name.len(); };
        first_dot_exec(name, next_i)
    }
}

fn no_wildcard_from_exec(name: &[u8], i: usize) -> (result: bool)
    requires i <= name.len()
    ensures result == no_wildcard_from(name@, i as int)
    decreases name.len() - i
{
    if i >= name.len() { true }
    else {
        let Some(byte) = name.get(i) else { return true; };
        let Some(next_i) = i.checked_add(1) else { return true; };
        *byte != b'*' && no_wildcard_from_exec(name, next_i)
    }
}

/// Lower-case ASCII DNS suffix bytes into the code points consumed by the
/// repository PSL table.
fn psl_domain_from_ascii_exec(name: &[u8]) -> (result: Vec<u32>)
    ensures result@ == psl_domain_from_ascii(name@)
{
    let mut result: Vec<u32> = Vec::new();
    let mut index = 0;
    while index < name.len()
        invariant
            index <= name.len(),
            name@.len() == name.len(),
            result@ == psl_domain_from_ascii(name@.subrange(0, index as int)),
        decreases name.len() - index
    {
        let Some(byte_ref) = name.get(index) else { return result; };
        let byte = *byte_ref;
        let folded = match byte { b'A'..=b'Z' => byte.saturating_add(0x20) as u32, _ => byte as u32 };
        result.push(folded);
        proof {
            reveal(psl_domain_from_ascii);
            assert(result@[index as int] == if name@[index as int] >= b'A' && name@[index as int] <= b'Z' {
                (name@[index as int] as int + 32) as u32
            } else { name@[index as int] as u32 });
            assert(result@ == psl_domain_from_ascii(name@.subrange(0, (index + 1) as int)));
        }
        index = index.saturating_add(1);
    }
    result
}

/// Use the repository's full ICANN and PRIVATE suffix table.
fn wildcard_suffix_is_public_suffix_exec(name: &[u8]) -> (result: bool)
    ensures result == wildcard_suffix_is_public_suffix(name@)
{
    let domain = psl_domain_from_ascii_exec(name);
    let result = clazel_psl::exec::is_public_suffix_exec(domain.as_slice());
    proof {
        reveal(wildcard_suffix_is_public_suffix);
        assert(domain@ == psl_domain_from_ascii(name@));
    }
    result
}

/// RFC 9525 §6.3: the implementation follows DNS-name matching's ASCII
/// folding and complete-leftmost-label wildcard rules.
pub fn dns_id_matches_exec(reference: &[u8], presented: &[u8]) -> (result: bool)
    ensures result == dns_match(reference@, presented@)
{
    if !valid_dns_exec(reference) { return false; }
    if valid_dns_exec(presented) {
        return ascii_equal_exec(reference, presented);
    }
    if presented.len() <= 2 || presented.first() != Some(&b'*') || presented.get(1) != Some(&b'.') {
        return false;
    }
    let Some(suffix) = presented.get(2..) else { return false; };
    if !valid_dns_exec(suffix) || !no_wildcard_from_exec(presented, 2) { return false; }
    if wildcard_suffix_is_public_suffix_exec(suffix) { return false; }
    let dot = first_dot_exec(reference, 0);
    if dot == 0 || dot >= reference.len() { return false; }
    let Some(suffix_start) = dot.checked_add(1) else { return false; };
    let Some(ref_suffix) = reference.get(suffix_start..) else { return false; };
    ascii_equal_exec(ref_suffix, suffix)
}

/// RFC 9525 §6.4: binary IP identifiers match only by full octet equality.
pub fn ip_id_matches_exec(reference: &[u8], presented: &[u8]) -> (result: bool)
    ensures result == ip_match(reference@, presented@)
{
    (reference.len() == 4 || reference.len() == 16) && reference == presented
}

/// RFC 9525 §6.2 dispatches by identifier kind; no DNS/IP coercion occurs.
pub fn service_identity_matches_exec(
    reference: ReferenceIdentity<'_>,
    presented: PresentedIdentity<'_>,
) -> (result: bool)
    ensures result == service_identity_match(
        view_reference_identity(&reference), view_presented_identity(&presented))
{
    match (reference, presented) {
        (ReferenceIdentity::Dns(r), PresentedIdentity::Dns(p)) => dns_id_matches_exec(r, p),
        (ReferenceIdentity::Ip(r), PresentedIdentity::Ip(p)) => ip_id_matches_exec(r, p),
        _ => false,
    }
}

} // verus!
