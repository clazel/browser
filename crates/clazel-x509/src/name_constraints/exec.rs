//! Executable RFC 5280 NameConstraints syntax decoder.

use super::spec as nc_spec;
use clazel_der::decode as der;
use clazel_der::spec::{Class, Tag};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A borrowed GeneralName subtree base.
#[derive(Clone, Copy)]
pub enum GeneralNameConstraint<'a> {
    /// dNSName constraint bytes, validated as nonempty IA5 only.
    DnsName(&'a [u8]),
    /// iPAddress subnet split into its address and mask octets.
    IpAddress {
        /// Address octets (4 or 16 bytes).
        address: &'a [u8],
        /// Network mask octets, matching the address width.
        mask: &'a [u8],
    },
    /// Other GeneralName choice, preserved as its complete DER TLV.
    Unsupported {
        /// Context-specific GeneralName tag number.
        tag: u32,
        /// Complete DER TLV retained for a later processor.
        der: &'a [u8],
    },
}

impl View for GeneralNameConstraint<'_> {
    type V = nc_spec::GeneralNameConstraint;
    closed spec fn view(&self) -> Self::V { view_general_name_constraint(self) }
}

/// Whether this decoder implements the base semantics. Callers processing a
/// critical extension must reject `false` unless another processor handles it.
pub fn general_name_constraint_supported(base: GeneralNameConstraint<'_>) -> (result: bool)
    ensures result == !nc_spec::base_is_unsupported(view_general_name_constraint(&base))
{
    match base {
        GeneralNameConstraint::DnsName(_) | GeneralNameConstraint::IpAddress { .. } => true,
        GeneralNameConstraint::Unsupported { .. } => false,
    }
}

/// Public mapping for the borrowed GeneralName representation.
pub open spec fn view_general_name_constraint(value: &GeneralNameConstraint<'_>) -> nc_spec::GeneralNameConstraint {
    match value {
        GeneralNameConstraint::DnsName(bytes) => nc_spec::GeneralNameConstraint::DnsName(bytes@),
        GeneralNameConstraint::IpAddress { address, mask } => nc_spec::GeneralNameConstraint::IpAddress {
            address: address@, mask: mask@,
        },
        GeneralNameConstraint::Unsupported { tag, der } => nc_spec::GeneralNameConstraint::Unsupported {
            tag: *tag, der: der@,
        },
    }
}

/// One decoded subtree; its absent minimum means the DER DEFAULT zero.
#[derive(Clone, Copy)]
pub struct GeneralSubtree<'a> {
    /// The base GeneralName choice.
    pub base: GeneralNameConstraint<'a>,
}

impl View for GeneralSubtree<'_> {
    type V = nc_spec::GeneralSubtree;
    closed spec fn view(&self) -> Self::V { view_general_subtree(self) }
}

/// Public mapping for a borrowed GeneralSubtree.
pub open spec fn view_general_subtree(value: &GeneralSubtree<'_>) -> nc_spec::GeneralSubtree {
    nc_spec::GeneralSubtree { base: view_general_name_constraint(&value.base) }
}

/// Decoded NameConstraints. Outer SEQUENCE input is preserved by the caller.
pub struct NameConstraints<'a> {
    /// Permitted subtrees, when present.
    pub permitted_subtrees: Option<Vec<GeneralSubtree<'a>>>,
    /// Excluded subtrees, when present.
    pub excluded_subtrees: Option<Vec<GeneralSubtree<'a>>>,
}

impl View for NameConstraints<'_> {
    type V = nc_spec::NameConstraints;
    closed spec fn view(&self) -> Self::V { view_name_constraints(self) }
}

/// Public mapping for the complete borrowed result.
pub open spec fn view_subtrees(items: Seq<GeneralSubtree<'_>>) -> Seq<nc_spec::GeneralSubtree> {
    items.map(|_i: int, item: GeneralSubtree<'_>| view_general_subtree(&item))
}

/// Public mapping for a NameConstraints result.
pub open spec fn view_name_constraints(value: &NameConstraints<'_>) -> nc_spec::NameConstraints {
    nc_spec::NameConstraints {
        permitted_subtrees: match &value.permitted_subtrees {
            Some(items) => Some(view_subtrees(items@)),
            None => None,
        },
        excluded_subtrees: match &value.excluded_subtrees {
            Some(items) => Some(view_subtrees(items@)),
            None => None,
        },
    }
}

pub open spec fn view_name_constraints_result(value: Option<NameConstraints<'_>>) -> Option<nc_spec::NameConstraints> {
    match value { Some(item) => Some(view_name_constraints(&item)), None => None }
}

pub open spec fn view_subtree_result(
    value: Option<(GeneralSubtree<'_>, usize)>,
) -> Option<(nc_spec::GeneralSubtree, nat)> {
    match value { Some((item, next)) => Some((view_general_subtree(&item), next as nat)), None => None }
}

pub open spec fn view_base_result(
    value: Option<(GeneralNameConstraint<'_>, usize)>,
) -> Option<(nc_spec::GeneralNameConstraint, nat)> {
    match value { Some((item, next)) => Some((view_general_name_constraint(&item), next as nat)), None => None }
}

pub open spec fn view_subtrees_result(
    value: Option<(Vec<GeneralSubtree<'_>>, usize)>,
) -> Option<(Seq<nc_spec::GeneralSubtree>, nat)> {
    match value { Some((items, next)) => Some((view_subtrees(items@), next as nat)), None => None }
}

pub open spec fn view_subtrees_field_result(
    value: Option<(Vec<GeneralSubtree<'_>>, usize)>,
) -> Option<(Seq<nc_spec::GeneralSubtree>, nat)> {
    view_subtrees_result(value)
}

fn is_context_tag(tag: Tag, number: u32, constructed: bool) -> (result: bool)
    ensures result == (tag == clazel_der::spec::context_specific(number, constructed))
{
    match tag.class {
        Class::ContextSpecific => tag.number == number && tag.constructed == constructed,
        _ => false,
    }
}

/// Parse a GeneralName base and preserve unsupported alternatives explicitly.
fn parse_base(input: &[u8], pos: usize, end: usize) -> (result: Option<(GeneralNameConstraint<'_>, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_base_result(result) == nc_spec::parse_base(input@, pos as nat, end as nat)
{
    let tlv = der::read_tlv(input, pos, end)?;
    let expected_constructed = tlv.tag.number == 0 || tlv.tag.number == 3
        || tlv.tag.number == 4 || tlv.tag.number == 5;
    if !matches!(tlv.tag.class, Class::ContextSpecific)
        || tlv.tag.number > 8 || tlv.tag.constructed != expected_constructed { return None; }
    let value = input.get(tlv.cstart..tlv.cend)?;
    let raw = input.get(pos..tlv.cend)?;
    let parsed = if tlv.tag.number == 2 {
        if value.is_empty() || !ia5_bytes(value, 0) { return None; }
        GeneralNameConstraint::DnsName(value)
    } else if tlv.tag.number == 7 {
        if value.len() == 8 {
            GeneralNameConstraint::IpAddress { address: value.get(0..4)?, mask: value.get(4..8)? }
        } else if value.len() == 32 {
            GeneralNameConstraint::IpAddress { address: value.get(0..16)?, mask: value.get(16..32)? }
        } else { return None; }
    } else {
        GeneralNameConstraint::Unsupported { tag: tlv.tag.number, der: raw }
    };
    proof {
        assert(tlv.tag.class == Class::ContextSpecific);
        assert(tlv.tag.constructed == crate::extensions::spec::general_name_constructed(tlv.tag.number));
        assert(value@ == input@.subrange(tlv.cstart as int, tlv.cend as int));
        assert(raw@ == input@.subrange(pos as int, tlv.cend as int));
        reveal(nc_spec::parse_base);
    }
    Some((parsed, tlv.cend))
}

fn ia5_bytes(input: &[u8], pos: usize) -> (result: bool)
    requires pos <= input.len()
    ensures result == crate::extensions::spec::ia5_bytes(input@, pos as int)
    decreases input.len() - pos
{
    if pos == input.len() { return true; }
    let Some(&first) = input.get(pos) else { return false; };
    if first >= 128 { return false; }
    let result = ia5_bytes(input, pos.saturating_add(1));
    proof {
        reveal(crate::extensions::spec::ia5_bytes);
        assert(input@[pos as int] < 128);
    }
    result
}

/// Parse one GeneralSubtree with implicit DEFAULT minimum omitted and maximum absent.
fn parse_general_subtree(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(GeneralSubtree<'_>, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_subtree_result(result) == nc_spec::parse_general_subtree(input@, pos as nat, end as nat)
{
    let (start, finish) = der::expect_sequence(input, pos, end)?;
    let outer = der::read_tlv(input, pos, end)?;
    if !matches!(outer.tag.class, Class::Universal) || outer.tag.number != 16 || !outer.tag.constructed
        || outer.cstart != start || outer.cend != finish { return None; }
    let (base, next) = parse_base(input, start, finish)?;
    if next != finish { return None; }
    proof {
        assert(der::view_tlv(Some(outer)) == clazel_der::spec::read_tlv(input@, pos as nat, end as nat));
        reveal(nc_spec::parse_general_subtree);
    }
    Some((GeneralSubtree { base }, outer.cend))
}

/// Iteratively parse a nonempty list of GeneralSubtree SEQUENCEs.
fn parse_subtrees(input: &[u8], start: usize, end: usize)
    -> (result: Option<(Vec<GeneralSubtree<'_>>, usize)>)
    requires start <= end, end <= input.len()
    ensures view_subtrees_result(result) == nc_spec::parse_subtrees_acc(input@, start as nat, end as nat, seq![])
{
    hide(nc_spec::parse_subtrees_acc);
    let mut items: Vec<GeneralSubtree<'_>> = Vec::new();
    let mut pos = start;
    let ghost expected = nc_spec::parse_subtrees_acc(input@, start as nat, end as nat, seq![]);
    proof {
        assert(view_subtrees(items@) =~= seq![]);
        assert(expected == nc_spec::parse_subtrees_acc(input@, pos as nat, end as nat, view_subtrees(items@)));
    }
    while pos < end
        invariant
            start <= pos <= end,
            end <= input.len(),
            input@.len() == input.len(),
            expected == nc_spec::parse_subtrees_acc(input@, start as nat, end as nat, seq![]),
            expected == nc_spec::parse_subtrees_acc(input@, pos as nat, end as nat, view_subtrees(items@)),
        decreases end - pos
    {
        let parsed = parse_general_subtree(input, pos, end);
        let (subtree, next) = match parsed {
            Some(value) => value,
            None => {
                proof {
                    assert(view_subtree_result(parsed)
                        == nc_spec::parse_general_subtree(input@, pos as nat, end as nat));
                    reveal(view_subtree_result);
                    assert(nc_spec::parse_general_subtree(input@, pos as nat, end as nat) is None);
                    reveal_with_fuel(nc_spec::parse_subtrees_acc, 1);
                    assert(expected is None);
                    assert(view_subtrees_result(None) == expected);
                }
                return None;
            }
        };
        if next <= pos {
            proof {
                reveal_with_fuel(nc_spec::parse_subtrees_acc, 1);
                assert(expected is None);
                assert(view_subtrees_result(None) == expected);
            }
            return None;
        }
        proof {
            reveal_with_fuel(nc_spec::parse_subtrees_acc, 1);
            assert(view_subtrees(items@).push(subtree@) == view_subtrees(items@.push(subtree)));
            assert(expected == nc_spec::parse_subtrees_acc(input@, next as nat, end as nat,
                view_subtrees(items@).push(subtree@)));
        }
        items.push(subtree);
        pos = next;
    }
    if items.is_empty() {
        proof {
            reveal_with_fuel(nc_spec::parse_subtrees_acc, 1);
            assert(expected is None);
        }
        return None;
    }
    proof {
        reveal_with_fuel(nc_spec::parse_subtrees_acc, 1);
        reveal(view_subtrees_result);
        assert(view_subtrees_result(Some((items, end))) == expected);
    }
    Some((items, end))
}

/// Decode a permitted/excluded implicit constructed GeneralSubtrees field.
fn parse_subtrees_field(input: &[u8], pos: usize, end: usize, number: u32)
    -> (result: Option<(Vec<GeneralSubtree<'_>>, usize)>)
    requires pos <= end, end <= input.len(), number == 0 || number == 1
    ensures view_subtrees_field_result(result) == nc_spec::parse_subtrees_field(input@, pos as nat, end as nat, number)
{
    let field = der::read_tlv(input, pos, end)?;
    if !is_context_tag(field.tag, number, true) { return None; }
    let result = parse_subtrees(input, field.cstart, field.cend)?;
    if result.1 != field.cend { return None; }
    proof {
        reveal(nc_spec::parse_subtrees_field);
        assert(field.tag == clazel_der::spec::context_specific(number, true));
    }
    Some((result.0, field.cend))
}

/// Parse ordered optional [0] permitted and [1] excluded fields.
fn parse_fields(input: &[u8], pos: usize, end: usize) -> (result: Option<NameConstraints<'_>>)
    requires pos <= end, end <= input.len()
    ensures view_name_constraints_result(result) == nc_spec::parse_name_constraints_fields(input@, pos as nat, end as nat)
{
    if pos == end { return Some(NameConstraints { permitted_subtrees: None, excluded_subtrees: None }); }
    let field = der::read_tlv(input, pos, end)?;
    if is_context_tag(field.tag, 0, true) {
        let (permitted, next) = parse_subtrees_field(input, pos, end, 0)?;
        let excluded = if next == end { None } else {
            let (items, final_pos) = parse_subtrees_field(input, next, end, 1)?;
            if final_pos != end { return None; }
            Some(items)
        };
        proof { reveal(nc_spec::parse_name_constraints_fields); }
        Some(NameConstraints { permitted_subtrees: Some(permitted), excluded_subtrees: excluded })
    } else if is_context_tag(field.tag, 1, true) {
        let (excluded, next) = parse_subtrees_field(input, pos, end, 1)?;
        if next != end { return None; }
        proof { reveal(nc_spec::parse_name_constraints_fields); }
        Some(NameConstraints { permitted_subtrees: None, excluded_subtrees: Some(excluded) })
    } else { None }
}

/// Parse one complete DER NameConstraints value.
pub fn parse_name_constraints(input: &[u8]) -> (result: Option<NameConstraints<'_>>)
    ensures super::contract::parse_name_constraints_ensures(input@, view_name_constraints_result(result))
{
    let (start, end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if !matches!(outer.tag.class, Class::Universal) || outer.tag.number != 16 || !outer.tag.constructed
        || outer.cstart != start || outer.cend != end || end != input.len() { return None; }
    let result = parse_fields(input, start, end)?;
    proof { reveal(nc_spec::parse_name_constraints); }
    Some(result)
}

}
