//! Executable RFC 5280 Name decoder, refined to [`super::spec`].

use clazel_der::decode as der;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Borrowed AttributeTypeAndValue preserving its complete encoded form.
pub struct AttributeTypeAndValue<'a> {
    /// Complete original SEQUENCE TLV.
    pub der: &'a [u8],
    /// OBJECT IDENTIFIER arcs.
    pub oid: Vec<u64>,
    /// Complete open-value TLV, retained without interpretation.
    pub value_der: &'a [u8],
    /// Tag of the retained value.
    pub value_tag: clazel_der::spec::Tag,
}

/// Borrowed, nonempty RelativeDistinguishedName.
pub struct RelativeDistinguishedName<'a> {
    /// Complete original SET TLV.
    pub der: &'a [u8],
    /// Attributes in DER SET OF order.
    pub attributes: Vec<AttributeTypeAndValue<'a>>,
}

/// Borrowed Name value preserving the complete original SEQUENCE TLV.
pub struct Name<'a> {
    /// Complete original Name SEQUENCE TLV.
    pub der: &'a [u8],
    /// RDNs in sequence order.
    pub rdns: Vec<RelativeDistinguishedName<'a>>,
}

/// Mapping for one borrowed attribute.
pub open spec fn view_attribute(value: &AttributeTypeAndValue<'_>) -> super::spec::AttributeTypeAndValue {
    super::spec::AttributeTypeAndValue {
        der: value.der@,
        oid: der::nats(value.oid@),
        value_der: value.value_der@,
        value_tag: value.value_tag,
    }
}

/// Sequence mapping for borrowed attributes.
pub open spec fn view_attributes(values: Seq<AttributeTypeAndValue<'_>>) -> Seq<super::spec::AttributeTypeAndValue>
{
    values.map(|_index: int, item: AttributeTypeAndValue<'_>| view_attribute(&item))
}

/// Mapping commutes with appending one parsed attribute.
pub proof fn lemma_view_attributes_push(values: Seq<AttributeTypeAndValue<'_>>, item: AttributeTypeAndValue<'_>)
    ensures view_attributes(values.push(item)) == view_attributes(values).push(view_attribute(&item))
    decreases values.len()
{
    reveal(view_attributes);
    assert(values.push(item).map(|_index: int, value: AttributeTypeAndValue<'_>| view_attribute(&value))
        =~= values.map(|_index: int, value: AttributeTypeAndValue<'_>| view_attribute(&value)).push(view_attribute(&item)));
}

/// Mapping for one borrowed RDN.
pub open spec fn view_rdn(value: &RelativeDistinguishedName<'_>) -> super::spec::RelativeDistinguishedName {
    super::spec::RelativeDistinguishedName { der: value.der@, attributes: view_attributes(value.attributes@) }
}

/// Sequence mapping for borrowed RDNs.
pub open spec fn view_rdns(values: Seq<RelativeDistinguishedName<'_>>) -> Seq<super::spec::RelativeDistinguishedName>
{
    values.map(|_index: int, item: RelativeDistinguishedName<'_>| view_rdn(&item))
}

/// Mapping commutes with appending one parsed RDN.
pub proof fn lemma_view_rdns_push(values: Seq<RelativeDistinguishedName<'_>>, item: RelativeDistinguishedName<'_>)
    ensures view_rdns(values.push(item)) == view_rdns(values).push(view_rdn(&item))
    decreases values.len()
{
    reveal(view_rdns);
    assert(values.push(item).map(|_index: int, value: RelativeDistinguishedName<'_>| view_rdn(&value))
        =~= values.map(|_index: int, value: RelativeDistinguishedName<'_>| view_rdn(&value)).push(view_rdn(&item)));
}

/// Open mapping for a borrowed Name.
pub open spec fn view_name(value: &Name<'_>) -> super::spec::Name {
    super::spec::Name { der: value.der@, rdns: view_rdns(value.rdns@) }
}

/// Mapping for an optional borrowed Name.
pub open spec fn view_name_result(value: Option<Name<'_>>) -> Option<super::spec::Name> {
    match value { Some(name) => Some(view_name(&name)), None => None }
}

/// Spec view of an optional raw borrowed DER slice.
pub open spec fn view_raw_option(value: Option<&[u8]>) -> Option<Seq<u8>> {
    match value { Some(bytes) => Some(bytes@), None => None }
}

impl View for AttributeTypeAndValue<'_> {
    type V = super::spec::AttributeTypeAndValue;
    closed spec fn view(&self) -> Self::V { view_attribute(self) }
}

impl View for RelativeDistinguishedName<'_> {
    type V = super::spec::RelativeDistinguishedName;
    closed spec fn view(&self) -> Self::V { view_rdn(self) }
}

impl View for Name<'_> {
    type V = super::spec::Name;
    closed spec fn view(&self) -> Self::V { view_name(self) }
}

/// RFC 5280 §4.1.2.6: read one AttributeTypeAndValue SEQUENCE containing
/// AttributeType OBJECT IDENTIFIER and exactly one open AttributeValue TLV.
pub fn parse_attribute(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(AttributeTypeAndValue<'_>, usize)>)
    requires end <= input.len(),
    ensures super::contract::parse_attribute_ensures(
        input@, pos as nat, end as nat, view_attribute_result(result))
{
    let (start, finish) = der::expect_sequence(input, pos, end)?;
    let sequence = der::read_tlv(input, pos, end)?;
    let (oid, after_oid) = der::read_oid(input, start, finish)?;
    let value = der::read_tlv(input, after_oid, finish)?;
    if value.cend != finish { return None; }
    let raw_attribute = input.get(pos..sequence.cend)?;
    let raw_value = input.get(after_oid..finish)?;
    Some((AttributeTypeAndValue { der: raw_attribute, oid, value_der: raw_value, value_tag: value.tag }, sequence.cend))
}

/// Mapping for the result of `parse_attribute`.
pub open spec fn view_attribute_result(
    value: Option<(AttributeTypeAndValue<'_>, usize)>,
) -> Option<(super::spec::AttributeTypeAndValue, nat)> {
    match value {
        Some((attribute, next)) => Some((view_attribute(&attribute), next as nat)),
        None => None,
    }
}

/// Compare encoded components in X.690 §11.6 order, padding the shorter
/// complete TLV with zero octets for comparison only.
pub fn der_octets_le(first: &[u8], second: &[u8]) -> (result: bool)
    ensures result == super::spec::der_octets_le(first@, second@)
{
    let extent = if first.len() > second.len() { first.len() } else { second.len() };
    let mut index: usize = 0;
    while index < extent
        invariant
            index <= extent,
            extent == if first.len() > second.len() { first.len() } else { second.len() },
            super::spec::der_octets_equal_prefix(first@, second@, index as nat),
        decreases extent - index,
    {
        let left = match first.get(index) { Some(value) => *value, None => 0 };
        let right = match second.get(index) { Some(value) => *value, None => 0 };
        let ghost at = index as nat;
        if left < right {
            proof {
                super::spec::lemma_equal_prefix_comparison(first@, second@, at);
                reveal(super::spec::der_octets_le_at);
                assert(super::spec::der_octets_le_at(first@, second@, at));
            }
            return true;
        }
        if left > right {
            proof {
                super::spec::lemma_equal_prefix_comparison(first@, second@, at);
                reveal(super::spec::der_octets_le_at);
                assert(!super::spec::der_octets_le_at(first@, second@, at));
            }
            return false;
        }
        proof {
            assert(super::spec::padded_octet(first@, at) == left as nat);
            assert(super::spec::padded_octet(second@, at) == right as nat);
            assert(left == right);
            reveal(super::spec::der_octets_equal_prefix);
            assert(super::spec::der_octets_equal_prefix(first@, second@, at + 1));
        }
        index = index.saturating_add(1);
    }
    proof {
        assert(index == extent);
        super::spec::lemma_equal_prefix_comparison(first@, second@, index as nat);
        reveal(super::spec::der_octets_le_at);
    }
    true
}

/// Result view for one parsed attribute.
pub open spec fn view_attribute_pair_result(
    value: Option<(AttributeTypeAndValue<'_>, usize)>,
) -> Option<(super::spec::AttributeTypeAndValue, nat)> {
    match value { Some((item, next)) => Some((view_attribute(&item), next as nat)), None => None }
}

/// Parse a complete nonempty RDN SET OF. The loop is bounded by the SET's
/// byte extent and rejects a descending DER encoding before storing it.
pub fn parse_rdn(input: &[u8], pos: usize, end: usize)
    -> (result: Option<(RelativeDistinguishedName<'_>, usize)>)
    requires end <= input.len(),
    ensures super::contract::parse_rdn_ensures(
        input@, pos as nat, end as nat, view_rdn_result(result))
{
    hide(super::spec::parse_attributes_acc);
    hide(super::spec::parse_attribute);
    let set_result = der::expect_set(input, pos, end);
    let (start, finish) = match set_result {
        Some(range) => range,
        None => {
            proof {
                reveal(super::spec::parse_rdn);
                assert(clazel_der::spec::expect_set(input@, pos as nat, end as nat) == None);
                assert(super::spec::parse_rdn(input@, pos as nat, end as nat) == None);
            }
            return None;
        },
    };
    let set_result = der::read_tlv(input, pos, end);
    let set = match set_result {
        Some(value) => value,
        None => {
            proof {
                reveal(super::spec::parse_rdn);
                assert(clazel_der::spec::expect_set(input@, pos as nat, end as nat) == Some((start as nat, finish as nat)));
                assert(clazel_der::spec::read_tlv(input@, pos as nat, end as nat) == None);
                assert(super::spec::parse_rdn(input@, pos as nat, end as nat) == None);
            }
            return None;
        },
    };
    proof {
        assert(clazel_der::spec::expect_set(input@, pos as nat, end as nat)
            == Some((start as nat, finish as nat)));
        assert(clazel_der::spec::read_tlv(input@, pos as nat, end as nat) == Some(set@));
    }
    let mut attributes: Vec<AttributeTypeAndValue<'_>> = Vec::new();
    let mut cursor = start;
    let mut previous: Option<&[u8]> = None;
    let ghost expected = super::spec::parse_attributes(input@, start as nat, finish as nat, None);
    let ghost mut previous_der: Option<Seq<u8>> = None;
    proof {
        reveal(view_attributes);
        super::lemmas::lemma_parse_attributes_initial(input@, start as nat, finish as nat, None);
        assert(view_attributes(attributes@) == Seq::<super::spec::AttributeTypeAndValue>::empty());
        assert(expected == super::spec::parse_attributes_acc(input@, start as nat, finish as nat, None, Seq::empty()));
    }
    while cursor < finish
        invariant
            start <= cursor <= finish,
            finish <= input.len(),
            clazel_der::spec::expect_set(input@, pos as nat, end as nat)
                == Some((start as nat, finish as nat)),
            clazel_der::spec::read_tlv(input@, pos as nat, end as nat) == Some(set@),
            attributes@.len() <= cursor - start,
            attributes@.len() != 0 || cursor == start,
            previous_der == view_raw_option(previous),
            expected == super::spec::parse_attributes_acc(
                input@, start as nat, finish as nat, None, Seq::empty()),
            expected == super::spec::parse_attributes_acc(
                input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@)),
        decreases finish - cursor,
    {
        let parsed = parse_attribute(input, cursor, finish);
        let (attribute, next) = match parsed {
            Some(pair) => pair,
            None => {
                proof {
                    super::lemmas::lemma_attributes_acc_bad_value(
                        input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@));
                    assert(expected == super::spec::parse_attributes_acc(
                        input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@)));
                    assert(expected == None);
                    super::lemmas::lemma_parse_attributes_initial(
                        input@, start as nat, finish as nat, None);
                    assert(super::spec::parse_attributes_acc(
                        input@, start as nat, finish as nat, None, Seq::empty()) == None);
                    super::lemmas::lemma_parse_attributes_none_from_acc(
                        input@, start as nat, finish as nat, None);
                    super::lemmas::lemma_parse_rdn_none_from_attributes(
                        input@, pos as nat, end as nat, start as nat, finish as nat, set@);
                }
                return None;
            },
        };
        if next <= cursor || next > finish {
            proof {
                assert(view_attribute_pair_result(Some((attribute, next)))
                    == super::spec::parse_attribute(input@, cursor as nat, finish as nat));
                super::lemmas::lemma_attributes_acc_bad_extent(
                    input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@),
                    view_attribute(&attribute), next as nat);
                assert(expected == super::spec::parse_attributes_acc(
                    input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@)));
                assert(expected == None);
                super::lemmas::lemma_parse_attributes_initial(input@, start as nat, finish as nat, None);
                assert(super::spec::parse_attributes_acc(
                    input@, start as nat, finish as nat, None, Seq::empty()) == None);
                super::lemmas::lemma_parse_attributes_none_from_acc(
                    input@, start as nat, finish as nat, None);
                super::lemmas::lemma_parse_rdn_none_from_attributes(
                    input@, pos as nat, end as nat, start as nat, finish as nat, set@);
            }
            return None;
        }
        if let Some(prior) = previous {
            let ordered = der_octets_le(prior, attribute.der);
            if !ordered {
                proof {
                    assert(view_attribute_pair_result(Some((attribute, next)))
                        == super::spec::parse_attribute(input@, cursor as nat, finish as nat));
                    super::lemmas::lemma_attributes_acc_bad_order(
                        input@, cursor as nat, finish as nat, prior@, view_attributes(attributes@),
                        view_attribute(&attribute), next as nat);
                    assert(previous_der == Some(prior@));
                    assert(expected == super::spec::parse_attributes_acc(
                        input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@)));
                    assert(expected == None);
                    super::lemmas::lemma_parse_attributes_initial(
                        input@, start as nat, finish as nat, None);
                    assert(super::spec::parse_attributes_acc(
                        input@, start as nat, finish as nat, None, Seq::empty()) == None);
                    super::lemmas::lemma_parse_attributes_none_from_acc(
                        input@, start as nat, finish as nat, None);
                    super::lemmas::lemma_parse_rdn_none_from_attributes(
                        input@, pos as nat, end as nat, start as nat, finish as nat, set@);
                }
                return None;
            }
        }
        proof {
            assert(view_attribute_pair_result(Some((attribute, next)))
                == super::spec::parse_attribute(input@, cursor as nat, finish as nat));
            super::lemmas::lemma_attributes_acc_step(
                input@, cursor as nat, finish as nat, previous_der, view_attributes(attributes@),
                view_attribute(&attribute), next as nat);
            assert(expected == super::spec::parse_attributes_acc(
                input@, next as nat, finish as nat, Some(attribute.der@),
                view_attributes(attributes@).push(view_attribute(&attribute))));
        }
        previous = Some(attribute.der);
        proof { previous_der = Some(attribute.der@); }
        proof { lemma_view_attributes_push(attributes@, attribute); }
        attributes.push(attribute);
        cursor = next;
    }
    if cursor != finish || attributes.is_empty() {
        proof {
            reveal(super::spec::parse_rdn);
            reveal(super::spec::parse_attributes);
            reveal(super::spec::parse_attributes_acc);
            assert(cursor == finish);
            assert(attributes@.len() == 0);
            assert(cursor == start);
            assert(start == finish);
            assert(super::spec::parse_attributes(input@, start as nat, finish as nat, None) == expected);
            assert(super::spec::parse_attributes(input@, start as nat, finish as nat, None)
                == Some(Seq::empty()));
            assert(super::spec::parse_rdn(input@, pos as nat, end as nat) == None);
        }
        return None;
    }
    let raw = input.get(pos..set.cend)?;
    proof {
        reveal(super::spec::parse_rdn);
        reveal(super::spec::parse_attributes);
        reveal(super::spec::parse_attributes_acc);
        assert(super::spec::parse_attributes_acc(
            input@, finish as nat, finish as nat, previous_der, view_attributes(attributes@))
            == Some(view_attributes(attributes@)));
        assert(expected == Some(view_attributes(attributes@)));
        assert(view_attributes(attributes@).len() > 0);
        assert(set.cend as nat == finish);
    }
    Some((RelativeDistinguishedName { der: raw, attributes }, set.cend))
}

/// Mapping for one RDN result.
pub open spec fn view_rdn_result(
    value: Option<(RelativeDistinguishedName<'_>, usize)>,
) -> Option<(super::spec::RelativeDistinguishedName, nat)> {
    match value { Some((item, next)) => Some((view_rdn(&item), next as nat)), None => None }
}

/// Parse exactly one Name SEQUENCE TLV. RDN traversal uses a checked cursor;
/// allocation grows only with successfully parsed RDNs.
pub fn parse_name(input: &[u8]) -> (result: Option<Name<'_>>)
    ensures super::contract::parse_name_ensures(input@, view_name_result(result))
{
    hide(super::spec::parse_rdns_acc);
    hide(super::spec::parse_rdn);
    let range = der::expect_sequence(input, 0, input.len());
    let (start, finish) = match range {
        Some(value) => value,
        None => {
            proof {
                reveal(super::spec::parse_name);
                assert(clazel_der::spec::expect_sequence(input@, 0, input.len() as nat) == None);
                assert(super::spec::parse_name(input@) == None);
            }
            return None;
        },
    };
    let tlv = der::read_tlv(input, 0, input.len());
    let sequence = match tlv {
        Some(value) => value,
        None => {
            proof {
                reveal(super::spec::parse_name);
                assert(clazel_der::spec::expect_sequence(input@, 0, input.len() as nat)
                    == Some((start as nat, finish as nat)));
                assert(clazel_der::spec::read_tlv(input@, 0, input.len() as nat) == None);
                assert(super::spec::parse_name(input@) == None);
            }
            return None;
        },
    };
    proof {
        assert(clazel_der::spec::expect_sequence(input@, 0, input.len() as nat)
            == Some((start as nat, finish as nat)));
        assert(clazel_der::spec::read_tlv(input@, 0, input.len() as nat) == Some(sequence@));
    }
    if sequence.cstart != start || sequence.cend != finish || finish != input.len() {
        proof {
            reveal(super::spec::parse_name);
            assert(super::spec::parse_name(input@) == None);
        }
        return None;
    }
    let mut rdns: Vec<RelativeDistinguishedName<'_>> = Vec::new();
    let mut cursor = start;
    let ghost expected = super::spec::parse_rdns(input@, start as nat, finish as nat);
    proof {
        reveal(view_rdns);
        super::lemmas::lemma_parse_rdns_initial(input@, start as nat, finish as nat);
        assert(view_rdns(rdns@) == Seq::<super::spec::RelativeDistinguishedName>::empty());
        assert(expected == super::spec::parse_rdns_acc(input@, start as nat, finish as nat, Seq::empty()));
    }
    while cursor < finish
        invariant
            start <= cursor <= finish,
            finish <= input.len(),
            clazel_der::spec::expect_sequence(input@, 0, input.len() as nat)
                == Some((start as nat, finish as nat)),
            clazel_der::spec::read_tlv(input@, 0, input.len() as nat) == Some(sequence@),
            sequence.cstart == start,
            sequence.cend == finish,
            finish == input.len(),
            rdns@.len() <= cursor - start,
            rdns@.len() != 0 || cursor == start,
            expected == super::spec::parse_rdns_acc(input@, start as nat, finish as nat, Seq::empty()),
            expected == super::spec::parse_rdns_acc(input@, cursor as nat, finish as nat, view_rdns(rdns@)),
        decreases finish - cursor,
    {
        let parsed = parse_rdn(input, cursor, finish);
        let (rdn, next) = match parsed {
            Some(pair) => pair,
            None => {
                proof {
                    super::lemmas::lemma_rdns_acc_bad_value(input@, cursor as nat, finish as nat, view_rdns(rdns@));
                    reveal(super::spec::parse_name);
                    assert(expected == super::spec::parse_rdns_acc(
                        input@, cursor as nat, finish as nat, view_rdns(rdns@)));
                    assert(expected == None);
                    super::lemmas::lemma_parse_rdns_initial(input@, start as nat, finish as nat);
                    assert(super::spec::parse_rdns_acc(
                        input@, start as nat, finish as nat, Seq::empty()) == None);
                    super::lemmas::lemma_parse_rdns_none_from_acc(
                        input@, start as nat, finish as nat);
                    super::lemmas::lemma_parse_name_none_from_rdns(
                        input@, start as nat, finish as nat, sequence@);
                }
                return None;
            },
        };
        if next <= cursor || next > finish {
            proof {
                assert(view_rdn_result(Some((rdn, next)))
                    == super::spec::parse_rdn(input@, cursor as nat, finish as nat));
                super::lemmas::lemma_rdns_acc_bad_extent(
                    input@, cursor as nat, finish as nat, view_rdns(rdns@), view_rdn(&rdn), next as nat);
                assert(expected == super::spec::parse_rdns_acc(
                    input@, cursor as nat, finish as nat, view_rdns(rdns@)));
                assert(expected == None);
                super::lemmas::lemma_parse_rdns_initial(input@, start as nat, finish as nat);
                assert(super::spec::parse_rdns_acc(
                    input@, start as nat, finish as nat, Seq::empty()) == None);
                super::lemmas::lemma_parse_rdns_none_from_acc(
                    input@, start as nat, finish as nat);
                super::lemmas::lemma_parse_name_none_from_rdns(
                    input@, start as nat, finish as nat, sequence@);
            }
            return None;
        }
        proof {
            assert(view_rdn_result(Some((rdn, next)))
                == super::spec::parse_rdn(input@, cursor as nat, finish as nat));
            super::lemmas::lemma_rdns_acc_step(
                input@, cursor as nat, finish as nat, view_rdns(rdns@), view_rdn(&rdn), next as nat);
            assert(expected == super::spec::parse_rdns_acc(
                input@, next as nat, finish as nat, view_rdns(rdns@).push(view_rdn(&rdn))));
        }
        proof { lemma_view_rdns_push(rdns@, rdn); }
        rdns.push(rdn);
        cursor = next;
    }
    if cursor != finish { return None; }
    proof {
        reveal(super::spec::parse_rdns);
        reveal(super::spec::parse_rdns_acc);
        reveal(super::spec::parse_name);
        assert(expected == Some(view_rdns(rdns@)));
    }
    let raw = input.get(0..sequence.cend)?;
    proof {
        assert(sequence.cend == input.len());
        assert(raw@ == input@);
        assert(super::spec::parse_rdns(input@, start as nat, finish as nat)
            == Some(view_rdns(rdns@)));
        assert(super::spec::parse_name(input@)
            == Some(super::spec::Name { der: input@, rdns: view_rdns(rdns@) }));
    }
    Some(Name { der: raw, rdns })
}

} // verus!
