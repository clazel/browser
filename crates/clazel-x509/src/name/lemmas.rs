//! Local unfolding lemmas used to prove iterative execution stages.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The non-accumulating RDN contents spec is its empty-accumulator stage.
pub proof fn lemma_parse_attributes_initial(input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>)
    ensures super::spec::parse_attributes(input, pos, end, prior)
        == super::spec::parse_attributes_acc(input, pos, end, prior, Seq::empty())
{
    reveal(super::spec::parse_attributes);
}

/// The non-accumulating RDN sequence spec is its empty-accumulator stage.
pub proof fn lemma_parse_rdns_initial(input: Seq<u8>, pos: nat, end: nat)
    ensures super::spec::parse_rdns(input, pos, end)
        == super::spec::parse_rdns_acc(input, pos, end, Seq::empty())
{
    reveal(super::spec::parse_rdns);
}

/// If the complete RDN traversal accumulator rejects, its public spec rejects.
pub proof fn lemma_parse_attributes_none_from_acc(
    input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>,
)
    requires super::spec::parse_attributes_acc(input, pos, end, prior, Seq::empty()) == None
    ensures super::spec::parse_attributes(input, pos, end, prior) == None
{
    reveal(super::spec::parse_attributes);
}

/// If the complete RDNSequence accumulator rejects, its public spec rejects.
pub proof fn lemma_parse_rdns_none_from_acc(input: Seq<u8>, pos: nat, end: nat)
    requires super::spec::parse_rdns_acc(input, pos, end, Seq::empty()) == None
    ensures super::spec::parse_rdns(input, pos, end) == None
{
    reveal(super::spec::parse_rdns);
}

/// A correctly framed SET whose attribute contents reject is not an RDN.
pub proof fn lemma_parse_rdn_none_from_attributes(
    input: Seq<u8>, pos: nat, end: nat, start: nat, finish: nat,
    set: clazel_der::spec::Tlv,
)
    requires
        clazel_der::spec::expect_set(input, pos, end) == Some((start, finish)),
        clazel_der::spec::read_tlv(input, pos, end) == Some(set),
        set.cstart == start,
        set.cend == finish,
        super::spec::parse_attributes(input, start, finish, None) == None,
    ensures super::spec::parse_rdn(input, pos, end) == None
{
    reveal(super::spec::parse_rdn);
}

/// A complete Name SEQUENCE with rejected RDN contents is not a Name.
pub proof fn lemma_parse_name_none_from_rdns(
    input: Seq<u8>, start: nat, finish: nat, sequence: clazel_der::spec::Tlv,
)
    requires
        clazel_der::spec::expect_sequence(input, 0, input.len()) == Some((start, finish)),
        clazel_der::spec::read_tlv(input, 0, input.len()) == Some(sequence),
        sequence.cstart == start,
        sequence.cend == finish,
        finish == input.len(),
        super::spec::parse_rdns(input, start, finish) == None,
    ensures super::spec::parse_name(input) == None
{
    reveal(super::spec::parse_name);
}

/// A malformed next AttributeTypeAndValue makes the remaining RDN invalid.
pub proof fn lemma_attributes_acc_bad_value(
    input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>,
    accumulated: Seq<super::spec::AttributeTypeAndValue>,
)
    requires pos < end, super::spec::parse_attribute(input, pos, end) == None
    ensures super::spec::parse_attributes_acc(input, pos, end, prior, accumulated) == None
{
    reveal(super::spec::parse_attributes_acc);
}

/// An AttributeTypeAndValue extent that does not advance inside its container
/// makes the remaining RDN invalid.
pub proof fn lemma_attributes_acc_bad_extent(
    input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>,
    accumulated: Seq<super::spec::AttributeTypeAndValue>,
    attribute: super::spec::AttributeTypeAndValue, next: nat,
)
    requires
        pos < end,
        super::spec::parse_attribute(input, pos, end) == Some((attribute, next)),
        !(next > pos && next <= end),
    ensures super::spec::parse_attributes_acc(input, pos, end, prior, accumulated) == None
{
    reveal(super::spec::parse_attributes_acc);
}

/// An out-of-order SET OF member makes the remaining RDN invalid.
pub proof fn lemma_attributes_acc_bad_order(
    input: Seq<u8>, pos: nat, end: nat, previous: Seq<u8>,
    accumulated: Seq<super::spec::AttributeTypeAndValue>,
    attribute: super::spec::AttributeTypeAndValue, next: nat,
)
    requires
        pos < end,
        super::spec::parse_attribute(input, pos, end) == Some((attribute, next)),
        next > pos && next <= end,
        !super::spec::der_octets_le(previous, attribute.der),
    ensures super::spec::parse_attributes_acc(input, pos, end, Some(previous), accumulated) == None
{
    reveal(super::spec::parse_attributes_acc);
}

/// Consume one valid ordered AttributeTypeAndValue in the accumulator spec.
pub proof fn lemma_attributes_acc_step(
    input: Seq<u8>, pos: nat, end: nat, prior: Option<Seq<u8>>,
    accumulated: Seq<super::spec::AttributeTypeAndValue>,
    attribute: super::spec::AttributeTypeAndValue, next: nat,
)
    requires
        super::spec::parse_attribute(input, pos, end) == Some((attribute, next)),
        next > pos && next <= end,
        match prior {
            None => true,
            Some(previous) => super::spec::der_octets_le(previous, attribute.der),
        },
    ensures super::spec::parse_attributes_acc(input, pos, end, prior, accumulated)
        == super::spec::parse_attributes_acc(
            input, next, end, Some(attribute.der), accumulated.push(attribute))
{
    reveal(super::spec::parse_attributes_acc);
}

/// A malformed next RDN makes the remaining Name invalid.
pub proof fn lemma_rdns_acc_bad_value(
    input: Seq<u8>, pos: nat, end: nat, accumulated: Seq<super::spec::RelativeDistinguishedName>,
)
    requires pos < end, super::spec::parse_rdn(input, pos, end) == None
    ensures super::spec::parse_rdns_acc(input, pos, end, accumulated) == None
{
    reveal(super::spec::parse_rdns_acc);
}

/// An RDN extent that does not advance inside the Name makes it invalid.
pub proof fn lemma_rdns_acc_bad_extent(
    input: Seq<u8>, pos: nat, end: nat,
    accumulated: Seq<super::spec::RelativeDistinguishedName>,
    rdn: super::spec::RelativeDistinguishedName, next: nat,
)
    requires
        pos < end,
        super::spec::parse_rdn(input, pos, end) == Some((rdn, next)),
        !(next > pos && next <= end),
    ensures super::spec::parse_rdns_acc(input, pos, end, accumulated) == None
{
    reveal(super::spec::parse_rdns_acc);
}

/// Consume one RDN in the accumulated RDNSequence spec.
pub proof fn lemma_rdns_acc_step(
    input: Seq<u8>, pos: nat, end: nat,
    accumulated: Seq<super::spec::RelativeDistinguishedName>,
    rdn: super::spec::RelativeDistinguishedName, next: nat,
)
    requires
        pos < end,
        super::spec::parse_rdn(input, pos, end) == Some((rdn, next)),
        next > pos && next <= end,
    ensures super::spec::parse_rdns_acc(input, pos, end, accumulated)
        == super::spec::parse_rdns_acc(input, next, end, accumulated.push(rdn))
{
    reveal(super::spec::parse_rdns_acc);
}

} // verus!
