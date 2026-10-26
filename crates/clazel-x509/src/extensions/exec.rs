//! Executable RFC 5280 extension container and subjectAltName decoder.

use super::spec as x509_spec;
use clazel_der::decode as der;
use clazel_der::spec::{Class, Tag};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

fn is_universal_constructed_tag(tag: Tag, number: u32) -> (result: bool)
    ensures result == (tag == clazel_der::spec::universal_constructed(number))
{
    match tag.class {
        Class::Universal => tag.constructed && tag.number == number,
        _ => false,
    }
}

fn is_universal_primitive_tag(tag: Tag, number: u32) -> (result: bool)
    ensures result == (tag == clazel_der::spec::universal_primitive(number))
{
    match tag.class {
        Class::Universal => !tag.constructed && tag.number == number,
        _ => false,
    }
}

fn is_general_name_tag(tag: Tag) -> (result: bool)
    ensures result == (tag.class == Class::ContextSpecific && tag.number <= 8
        && tag.constructed == x509_spec::general_name_constructed(tag.number))
{
    match tag.class {
        Class::ContextSpecific => tag.number <= 8
            && tag.constructed == expected_constructed(tag.number),
        _ => false,
    }
}

/// Parsed Extension with its extnValue bytes borrowed verbatim.
pub struct Extension<'a> {
    /// OBJECT IDENTIFIER arcs.
    pub oid: Vec<u64>,
    /// Criticality; absent DER DEFAULT FALSE is represented as false.
    pub critical: bool,
    /// Opaque extnValue contents, not the OCTET STRING TLV.
    pub value: &'a [u8],
}

impl View for Extension<'_> {
    type V = x509_spec::Extension;
    closed spec fn view(&self) -> Self::V {
        x509_spec::Extension {
            oid: der::nats(self.oid@),
            critical: self.critical,
            value: self.value@,
        }
    }
}

/// Extracted subjectAltName entries. Other GeneralName choices retain their
/// complete DER encoding for a later semantics-aware processor.
pub enum GeneralName<'a> {
    /// dNSName content bytes.
    DnsName(&'a [u8]),
    /// iPAddress octets in network order.
    IpAddress(&'a [u8]),
    /// Other GeneralName tag number and complete encoded TLV.
    Other(u32, &'a [u8]),
}

impl View for GeneralName<'_> {
    type V = x509_spec::GeneralName;
    closed spec fn view(&self) -> Self::V {
        match self {
            GeneralName::DnsName(bytes) => x509_spec::GeneralName::DnsName(bytes@),
            GeneralName::IpAddress(bytes) => x509_spec::GeneralName::IpAddress(bytes@),
            GeneralName::Other(number, bytes) => x509_spec::GeneralName::Other(*number, bytes@),
        }
    }
}

/// Parsed nonempty GeneralNames list.
pub struct SubjectAltName<'a> {
    /// Names in encoded order.
    pub names: Vec<GeneralName<'a>>,
}

impl View for SubjectAltName<'_> {
    type V = x509_spec::SubjectAltName;
    closed spec fn view(&self) -> Self::V {
        x509_spec::SubjectAltName {
            names: view_general_names(self.names@),
        }
    }
}

pub open spec fn view_extensions(items: Seq<Extension<'_>>) -> Seq<x509_spec::Extension> {
    items.map(|_i: int, item: Extension<'_>| item@)
}

pub open spec fn view_general_names(items: Seq<GeneralName<'_>>) -> Seq<x509_spec::GeneralName> {
    items.map(|_i: int, item: GeneralName<'_>| item@)
}

pub open spec fn view_seen_oids(items: Seq<Vec<u64>>) -> Seq<Seq<nat>> {
    Seq::new(items.len(), |i: int| der::nats(items[i]@))
}

/// Spec view of an optional vector of parsed extensions.
pub open spec fn view_extensions_result(
    result: Option<Vec<Extension<'_>>>,
) -> Option<Seq<x509_spec::Extension>> {
    match result {
        Some(items) => Some(view_extensions(items@)),
        None => None,
    }
}

/// Spec view of an optional parsed SAN value.
pub open spec fn view_subject_alt_name_result(
    result: Option<SubjectAltName<'_>>,
) -> Option<x509_spec::SubjectAltName> {
    match result {
        Some(value) => Some(value@),
        None => None,
    }
}

pub open spec fn view_extension_parse_result(
    result: Option<(Extension<'_>, usize)>,
) -> Option<(x509_spec::Extension, nat)> {
    match result {
        Some((value, next)) => Some((value@, next as nat)),
        None => None,
    }
}

pub open spec fn view_general_name_parse_result(
    result: Option<(GeneralName<'_>, usize)>,
) -> Option<(x509_spec::GeneralName, nat)> {
    match result {
        Some((value, next)) => Some((value@, next as nat)),
        None => None,
    }
}

/// RFC 5280 §4.1.2.9: parse one Extension SEQUENCE, preserving extnValue.
fn parse_extension(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(Extension<'_>, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_extension_parse_result(result) == x509_spec::parse_extension(input@, pos as nat, end as nat)
{
    let (contents_start, contents_end) = der::expect_sequence(input, pos, end)?;
    let (oid, after_oid) = der::read_oid(input, contents_start, contents_end)?;
    let field = der::read_tlv(input, after_oid, contents_end)?;
    let (critical, value_start) = if is_universal_primitive_tag(field.tag, 1) {
        match der::read_boolean(input, after_oid, contents_end) {
            Some((true, after_critical)) => (true, after_critical),
            // X.690 §11.5: the DEFAULT FALSE value must be omitted in DER.
            Some((false, _)) | None => return None,
        }
    } else {
        (false, after_oid)
    };
    let (value_start, value_end) = der::read_octet_string(input, value_start, contents_end)?;
    if value_end != contents_end { return None; }
    Some((Extension {
        oid,
        critical,
        value: input.get(value_start..value_end)?,
    }, contents_end))
}

pub open spec fn view_extensions_from_result(
    result: Option<(Vec<Extension<'_>>, usize)>,
) -> Option<(Seq<x509_spec::Extension>, nat)> {
    match result {
        Some((items, next)) => Some((view_extensions(items@), next as nat)),
        None => None,
    }
}

fn oid_sequences_equal(left: &[u64], right: &[u64]) -> (result: bool)
    ensures result == (der::nats(left@) =~= der::nats(right@))
{
    if left.len() != right.len() {
        proof { reveal(der::nats); }
        return false;
    }
    let mut index: usize = 0;
    while index < left.len()
        invariant
            index <= left.len(),
            left.len() == right.len(),
            forall|j: int| 0 <= j < index
                ==> der::nats(left@)[j] == der::nats(right@)[j],
        decreases left.len() - index
    {
        let a = match left.get(index) { Some(value) => *value, None => return false };
        let b = match right.get(index) { Some(value) => *value, None => return false };
        if a != b {
            proof {
                assert((a as nat) != (b as nat));
                assert(der::nats(left@)[index as int] == a as nat) by { reveal(der::nats); }
                assert(der::nats(right@)[index as int] == b as nat) by { reveal(der::nats); }
                assert(der::nats(left@) !~= der::nats(right@));
            }
            return false;
        }
        proof {
            assert(der::nats(left@)[index as int] == der::nats(right@)[index as int]) by {
                reveal(der::nats);
            }
        }
        index = index.saturating_add(1);
    }
    assert(der::nats(left@) =~= der::nats(right@)) by { reveal(der::nats); }
    true
}

/// Determine whether a parsed OID prefix already contains `oid`.
proof fn lemma_nats_preserves_equality(left: Seq<u64>, right: Seq<u64>)
    requires left =~= right
    ensures der::nats(left) =~= der::nats(right)
{
    reveal(der::nats);
}

proof fn lemma_view_seen_oids_index(items: Seq<Vec<u64>>, index: int)
    requires 0 <= index < items.len()
    ensures view_seen_oids(items)[index] =~= der::nats(items[index]@)
{
    reveal(view_seen_oids);
}

fn oid_seen_exec(seen: &[Vec<u64>], oid: &[u64]) -> (result: bool)
    ensures result == x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), 0)
{
    let mut index: usize = 0;
    while index < seen.len()
        invariant
            index <= seen.len(),
            seen@.len() == seen.len(),
            view_seen_oids(seen@).len() == seen.len(),
            x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), 0)
                == x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), index as int),
        decreases seen.len() - index
    {
        let candidate = match seen.get(index) { Some(value) => value, None => return false };
        if oid_sequences_equal(candidate, oid) {
            proof {
                let ghost mapped_candidate = der::nats(candidate@);
                let ghost mapped_item = der::nats(seen@[index as int]@);
                assert(mapped_candidate =~= der::nats(oid@));
                assert(candidate@ =~= seen@[index as int]@);
                lemma_view_seen_oids_index(seen@, index as int);
                assert(view_seen_oids(seen@)[index as int] =~= mapped_item);
                lemma_nats_preserves_equality(candidate@, seen@[index as int]@);
                assert(mapped_item =~= mapped_candidate);
                assert(view_seen_oids(seen@)[index as int] =~= der::nats(oid@));
                reveal_with_fuel(x509_spec::oid_seen, 1);
                assert(x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), index as int));
                assert(x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), 0));
            }
            return true;
        }
        proof {
            let ghost mapped_candidate = der::nats(candidate@);
            let ghost mapped_item = der::nats(seen@[index as int]@);
            assert(candidate@ =~= seen@[index as int]@);
            lemma_view_seen_oids_index(seen@, index as int);
            assert(view_seen_oids(seen@)[index as int] =~= mapped_item);
            lemma_nats_preserves_equality(candidate@, seen@[index as int]@);
            assert(mapped_item =~= mapped_candidate);
            assert(!(mapped_candidate =~= der::nats(oid@)));
            assert(!(view_seen_oids(seen@)[index as int] =~= der::nats(oid@)));
            reveal_with_fuel(x509_spec::oid_seen, 1);
            assert(x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), index as int)
                == x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), index as int + 1));
        }
        index = index.saturating_add(1);
    }
    proof {
        reveal_with_fuel(x509_spec::oid_seen, 1);
        assert(!x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), index as int));
        assert(!x509_spec::oid_seen(view_seen_oids(seen@), der::nats(oid@), 0));
    }
    false
}

/// Scan Extension records iteratively with the accumulator specification.
#[verifier::rlimit(500)]
fn parse_extensions_from_exec(
    input: &[u8], start: usize, end: usize, seen: Vec<Vec<u64>>,
) -> (result: Option<(Vec<Extension<'_>>, usize)>)
    requires start <= end, end <= input.len()
    ensures view_extensions_from_result(result)
        == x509_spec::parse_extensions_acc(input@, start as nat, end as nat, view_seen_oids(seen@), seq![])
{
    let ghost initial_seen = view_seen_oids(seen@);
    let mut records: Vec<Extension<'_>> = Vec::new();
    let mut seen_oids = seen.clone();
    let ghost mut spec_seen = initial_seen;
    let mut pos = start;
    proof {
        assert(spec_seen == initial_seen);
        assert(view_seen_oids(seen_oids@) == initial_seen);
        assert(view_extensions(records@) == seq![]);
        assert(x509_spec::parse_extensions_acc(
            input@, start as nat, end as nat, initial_seen, seq![]) == x509_spec::parse_extensions_acc(
            input@, pos as nat, end as nat, spec_seen, view_extensions(records@)));
    }
    while pos < end
        invariant
            start <= pos <= end,
            end <= input.len(),
            records@.len() <= pos - start,
            initial_seen == view_seen_oids(seen@),
            view_seen_oids(seen_oids@) == spec_seen,
            x509_spec::parse_extensions_acc(
                input@, start as nat, end as nat, initial_seen, seq![]) == x509_spec::parse_extensions_acc(
                input@, pos as nat, end as nat, spec_seen, view_extensions(records@)),
        decreases end - pos
    {
        let (record, next) = match parse_extension(input, pos, end) {
            Some(pair) => pair,
            None => {
                proof {
                    assert(x509_spec::parse_extension(input@, pos as nat, end as nat) is None);
                    reveal_with_fuel(x509_spec::parse_extensions_acc, 1);
                    assert(x509_spec::parse_extensions_acc(input@, pos as nat, end as nat,
                        spec_seen, view_extensions(records@)) is None);
                    assert(x509_spec::parse_extensions_acc(
                        input@, start as nat, end as nat, initial_seen, seq![]) is None);
                }
                return None;
            }
        };
        if next <= pos || next > end {
            proof {
                reveal_with_fuel(x509_spec::parse_extensions_acc, 1);
                assert(x509_spec::parse_extensions_acc(input@, pos as nat, end as nat,
                    spec_seen, view_extensions(records@)) is None);
                assert(x509_spec::parse_extensions_acc(
                    input@, start as nat, end as nat, initial_seen, seq![]) is None);
            }
            return None;
        }
        if oid_seen_exec(&seen_oids, &record.oid) {
            proof {
                assert(x509_spec::oid_seen(spec_seen, record@.oid, 0));
                reveal_with_fuel(x509_spec::parse_extensions_acc, 1);
                assert(x509_spec::parse_extensions_acc(input@, pos as nat, end as nat,
                    spec_seen, view_extensions(records@)) is None);
                assert(x509_spec::parse_extensions_acc(
                    input@, start as nat, end as nat, initial_seen, seq![]) is None);
            }
            return None;
        }
        let ghost spec_oid = record@.oid;
        let ghost old_records = view_extensions(records@);
        let oid_copy = record.oid.clone();
        proof {
            reveal_with_fuel(x509_spec::parse_extensions_acc, 1);
            assert(x509_spec::parse_extensions_acc(
                input@, start as nat, end as nat, initial_seen, seq![]) == x509_spec::parse_extensions_acc(
                input@, next as nat, end as nat, spec_seen.push(spec_oid),
                view_extensions(records@).push(record@)));
        }
        records.push(record);
        seen_oids.push(oid_copy);
        pos = next;
        proof {
            spec_seen = spec_seen.push(spec_oid);
            assert(view_extensions(records@) == old_records.push(record@));
        }
    }
    proof {
        reveal_with_fuel(x509_spec::parse_extensions_acc, 1);
        assert(x509_spec::parse_extensions_acc(
            input@, start as nat, end as nat, initial_seen, seq![])
            == Some((view_extensions(records@), end as nat)));
    }
    Some((records, end))
}

/// RFC 5280 §4.1.2.9: parse a complete, nonempty Extensions SEQUENCE.
pub fn parse_extensions(input: &[u8]) -> (result: Option<Vec<Extension<'_>>>)
    ensures super::contract::parse_extensions_ensures(input@, view_extensions_result(result))
{
    let (contents_start, contents_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if !is_universal_constructed_tag(outer.tag, 16) || outer.cstart != contents_start
        || outer.cend != contents_end || outer.cend != input.len()
        || contents_start == contents_end { return None; }
    let seen: Vec<Vec<u64>> = Vec::new();
    let parsed = parse_extensions_from_exec(
        input, contents_start, contents_end, seen.clone());
    proof {
        reveal(view_seen_oids);
        reveal(der::nats);
        assert(view_seen_oids(seen@) == seq![]);
        assert(view_extensions_from_result(parsed)
            == x509_spec::parse_extensions_acc(
                input@, contents_start as nat, contents_end as nat, seq![], seq![]));
    }
    let (records, final_pos) = match parsed {
        Some(value) => value,
        None => {
            proof {
                reveal(x509_spec::parse_extensions);
                reveal(x509_spec::parse_extensions_from);
                assert(view_extensions_from_result(parsed) is None);
                assert(x509_spec::parse_extensions_acc(
                    input@, contents_start as nat, contents_end as nat, seq![], seq![]) is None);
                assert(x509_spec::parse_extensions_from(
                    input@, contents_start as nat, contents_end as nat, seq![]) is None);
                assert(x509_spec::parse_extensions(input@) is None);
            }
            return None;
        }
    };
    if final_pos != contents_end || records.is_empty() {
        proof {
            reveal(x509_spec::parse_extensions);
            reveal(x509_spec::parse_extensions_from);
            assert(x509_spec::parse_extensions_from(
                input@, contents_start as nat, contents_end as nat, seq![])
                == Some((view_extensions(records@), final_pos as nat)));
            assert(x509_spec::parse_extensions(input@) is None);
        }
        return None;
    }
    Some(records)
}

fn expected_constructed(number: u32) -> (result: bool)
    ensures result == x509_spec::general_name_constructed(number)
{
    number == 0 || number == 3 || number == 4 || number == 5
}

fn ia5_bytes_exec(input: &[u8], pos: usize) -> (result: bool)
    requires pos <= input.len()
    ensures result == x509_spec::ia5_bytes(input@, pos as int)
    decreases input.len() - pos
{
    if pos == input.len() { return true; }
    let byte = match input.get(pos) { Some(&byte) => byte, None => return false };
    if byte >= 128 { return false; }
    ia5_bytes_exec(input, pos.saturating_add(1))
}

/// RFC 5280 §4.2.1.6: parse one GeneralName choice.
fn parse_general_name(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(GeneralName<'_>, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_general_name_parse_result(result) == x509_spec::parse_general_name(input@, pos as nat, end as nat)
{
    let tlv = der::read_tlv(input, pos, end)?;
    if !is_general_name_tag(tlv.tag) {
        return None;
    }
    if tlv.tag.number == 2 {
        if tlv.cstart == tlv.cend { return None; }
        let bytes = input.get(tlv.cstart..tlv.cend)?;
        if !ia5_bytes_exec(bytes, 0) { return None; }
        Some((GeneralName::DnsName(bytes), tlv.cend))
    } else if tlv.tag.number == 7 {
        let bytes = input.get(tlv.cstart..tlv.cend)?;
        if bytes.len() != 4 && bytes.len() != 16 { return None; }
        Some((GeneralName::IpAddress(bytes), tlv.cend))
    } else {
        Some((GeneralName::Other(tlv.tag.number, input.get(pos..tlv.cend)?), tlv.cend))
    }
}

pub open spec fn view_general_names_result(
    result: Option<(Vec<GeneralName<'_>>, usize)>,
) -> Option<(Seq<x509_spec::GeneralName>, nat)> {
    match result {
        Some((names, next)) => Some((view_general_names(names@), next as nat)),
        None => None,
    }
}

/// Decode the ordered GeneralName suffix with the RFC 5280 recursive grammar.
fn parse_general_names_from_exec(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(Vec<GeneralName<'_>>, usize)>)
    requires pos <= end, end <= input.len()
    ensures view_general_names_result(result) == x509_spec::parse_general_names_from(input@, pos as nat, end as nat)
{
    let mut names: Vec<GeneralName<'_>> = Vec::new();
    let mut cursor = pos;
    proof {
        reveal(view_general_names);
        assert(view_general_names(names@) =~= seq![]);
        assert(x509_spec::parse_general_names_acc(
            input@, pos as nat, end as nat, seq![]) == x509_spec::parse_general_names_acc(
            input@, cursor as nat, end as nat, view_general_names(names@)));
    }
    while cursor < end
        invariant
            pos <= cursor <= end,
            end <= input.len(),
            names@.len() <= cursor - pos,
            x509_spec::parse_general_names_acc(input@, pos as nat, end as nat, seq![])
                == x509_spec::parse_general_names_acc(
                    input@, cursor as nat, end as nat, view_general_names(names@)),
        decreases end - cursor
    {
        let (name, next) = match parse_general_name(input, cursor, end) {
            Some(pair) => pair,
            None => {
                proof {
                    reveal_with_fuel(x509_spec::parse_general_names_acc, 1);
                    assert(x509_spec::parse_general_names_acc(
                        input@, cursor as nat, end as nat, view_general_names(names@)) is None);
                    assert(x509_spec::parse_general_names_acc(
                        input@, pos as nat, end as nat, seq![]) is None);
                    reveal(x509_spec::parse_general_names_from);
                    assert(x509_spec::parse_general_names_from(
                        input@, pos as nat, end as nat) is None);
                }
                return None;
            }
        };
        if next <= cursor || next > end {
            proof {
                reveal_with_fuel(x509_spec::parse_general_names_acc, 1);
                assert(x509_spec::parse_general_names_acc(
                    input@, cursor as nat, end as nat, view_general_names(names@)) is None);
                assert(x509_spec::parse_general_names_acc(
                    input@, pos as nat, end as nat, seq![]) is None);
                reveal(x509_spec::parse_general_names_from);
            }
            return None;
        }
        let ghost previous_names = view_general_names(names@);
        proof {
            reveal_with_fuel(x509_spec::parse_general_names_acc, 1);
            assert(x509_spec::parse_general_names_acc(
                input@, pos as nat, end as nat, seq![]) == x509_spec::parse_general_names_acc(
                input@, next as nat, end as nat, previous_names.push(name@)));
        }
        names.push(name);
        proof { assert(view_general_names(names@) == previous_names.push(name@)); }
        cursor = next;
    }
    proof {
        reveal_with_fuel(x509_spec::parse_general_names_acc, 1);
        assert(x509_spec::parse_general_names_acc(
            input@, pos as nat, end as nat, seq![])
            == Some((view_general_names(names@), end as nat)));
        reveal(x509_spec::parse_general_names_from);
    }
    Some((names, end))
}

/// RFC 5280 §4.2.1.6: parse the nonempty GeneralNames SEQUENCE in extnValue.
pub fn parse_subject_alt_name(input: &[u8]) -> (result: Option<SubjectAltName<'_>>)
    ensures super::contract::parse_subject_alt_name_ensures(
        input@, view_subject_alt_name_result(result))
{
    let (contents_start, contents_end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if !is_universal_constructed_tag(outer.tag, 16) || outer.cstart != contents_start
        || outer.cend != contents_end || outer.cend != input.len()
        || contents_start == contents_end { return None; }
    let (names, final_pos) = parse_general_names_from_exec(input, contents_start, contents_end)?;
    if final_pos != contents_end || names.is_empty() { return None; }
    Some(SubjectAltName { names })
}

} // verus!
