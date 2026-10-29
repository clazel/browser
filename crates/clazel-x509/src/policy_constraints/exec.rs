//! Executable RFC 5280 §4.2.1.11 PolicyConstraints decoder.

use clazel_der::decode as der;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Borrowed PolicyConstraints value. Each SkipCerts is its canonical unsigned
/// magnitude octets (`[0]` for zero), at most four octets.
#[derive(Clone, Copy)]
pub struct PolicyConstraints<'a> {
    /// `requireExplicitPolicy [0] SkipCerts`, if present.
    pub require_explicit_policy: Option<&'a [u8]>,
    /// `inhibitPolicyMapping [1] SkipCerts`, if present.
    pub inhibit_policy_mapping: Option<&'a [u8]>,
}

pub open spec fn view_skip(value: Option<&[u8]>) -> Option<Seq<u8>> {
    match value { Some(bytes) => Some(bytes@), None => None }
}

impl View for PolicyConstraints<'_> {
    type V = super::spec::PolicyConstraints;
    open spec fn view(&self) -> Self::V {
        super::spec::PolicyConstraints {
            require_explicit_policy: view_skip(self.require_explicit_policy),
            inhibit_policy_mapping: view_skip(self.inhibit_policy_mapping),
        }
    }
}

pub open spec fn view_policy_constraints_result(result: Option<PolicyConstraints<'_>>)
    -> Option<super::spec::PolicyConstraints>
{
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn view_skip_result(result: Option<Option<(&[u8], usize)>>)
    -> Option<Option<(Seq<u8>, nat)>>
{
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some((bytes, next))) => Some(Some((bytes@, next as nat))),
    }
}

/// Read the octet at `index`, or 0 when out of range (callers check the range).
fn octet(input: &[u8], index: usize) -> (result: u8)
    ensures index < input.len() ==> result == input@[index as int]
{
    match input.get(index) { Some(&value) => value, None => 0 }
}

/// RFC 5280 §4.2.1.11 `SkipCerts` as the optional implicit field `[number]`.
fn parse_skip_certs(input: &[u8], pos: usize, end: usize, number: u32)
    -> (result: Option<Option<(&[u8], usize)>>)
    requires end <= input.len()
    ensures view_skip_result(result) == super::spec::parse_skip_certs(input@, pos as nat, end as nat, number)
{
    let field = der::read_optional_context(input, pos, end, number)?;
    let (constructed, content_start, content_end) = match field {
        None => return Some(None),
        Some(found) => found,
    };
    proof {
        clazel_der::lemmas::lemma_read_tlv_bounds(input@, pos as nat, end as nat);
        reveal(clazel_der::spec::read_optional_context);
    }
    // X.690 §8.14.4: the implicit INTEGER is primitive.
    if constructed { return None; }
    // content_start <= content_end <= end <= input.len() (lemma above).
    let length = content_end.saturating_sub(content_start);
    // §8.3.1: one or more octets.
    if length == 0 { return None; }
    let first = octet(input, content_start);
    // content_start < content_end, so this does not saturate.
    let second_index = content_start.saturating_add(1);
    if length >= 2 {
        let second = octet(input, second_index);
        // §8.3.2: no redundant leading 0xFF or 0x00.
        if (first == 255 && second >= 128) || (first == 0 && second < 128) { return None; }
    }
    // §8.3.3 and INTEGER (0..MAX): bit 8 of the first octet clear.
    if first >= 128 { return None; }
    let magnitude_start = if length >= 2 && first == 0 { second_index } else { content_start };
    let magnitude_length = content_end.saturating_sub(magnitude_start);
    // At most four magnitude octets: below 2^32.
    if magnitude_length > 4 { return None; }
    let magnitude = input.get(magnitude_start..content_end)?;
    proof {
        let contents = input@.subrange(content_start as int, content_end as int);
        assert(contents[0] == input@[content_start as int]);
        if length >= 2 { assert(contents[1] == input@[second_index as int]); }
        assert(magnitude@ == input@.subrange(magnitude_start as int, content_end as int));
        reveal(super::spec::parse_skip_certs);
    }
    Some(Some((magnitude, content_end)))
}

/// RFC 5280 §4.2.1.11: decode the complete PolicyConstraints SEQUENCE.
pub fn parse_policy_constraints(input: &[u8]) -> (result: Option<PolicyConstraints<'_>>)
    ensures super::contract::parse_policy_constraints_ensures(
        input@, view_policy_constraints_result(result))
{
    let (start, end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if outer.cstart != start || outer.cend != end || end != input.len() { return None; }
    proof {
        clazel_der::lemmas::lemma_read_tlv_bounds(input@, 0, input@.len());
        reveal(super::spec::parse_policy_constraints);
        reveal(super::spec::parse_policy_constraints_fields);
    }
    let require = parse_skip_certs(input, start, end, 0)?;
    let (require_explicit_policy, after_require) = match require {
        Some((value, next)) => (Some(value), next),
        None => (None, start),
    };
    let inhibit = parse_skip_certs(input, after_require, end, 1)?;
    let (inhibit_policy_mapping, after_inhibit) = match inhibit {
        Some((value, next)) => (Some(value), next),
        None => (None, after_require),
    };
    // Exact consumption, and at least one field (an empty SEQUENCE is refused).
    if after_inhibit != end
        || (require_explicit_policy.is_none() && inhibit_policy_mapping.is_none()) { return None; }
    Some(PolicyConstraints { require_explicit_policy, inhibit_policy_mapping })
}

} // verus!
