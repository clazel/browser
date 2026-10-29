//! Known answers for the name-constraint matching spec, one per situation
//! of the x509-limbo survey (commit `1080e565f26e544bbe9cf99953be8a57c08e7e20`),
//! each proven by evaluation. They are also the theorems that the certified
//! mutations in `mutations.json` contradict.
//!
//! BetterTLS's chains are root -> `local_root` -> `local_ica` -> leaf, with
//! the NameConstraints on `local_ica` only, so the leaf is checked under a
//! state of that one set. The examples write that state directly. Where
//! limbo's verdict has another cause as well (a hostname mismatch, an
//! intermediate's own SAN), the comment says which part this example pins.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Names and constraints used below
// ---------------------------------------------------------------------------

/// `localhost`
pub open spec fn localhost() -> Seq<u8> {
    seq![b'l', b'o', b'c', b'a', b'l', b'h', b'o', b's', b't']
}

/// `test.localhost`
pub open spec fn test_localhost() -> Seq<u8> {
    seq![b't', b'e', b's', b't', b'.'] + localhost()
}

/// `example.com`
pub open spec fn example_com() -> Seq<u8> {
    seq![b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm']
}

/// `bad.example.com`
pub open spec fn bad_example_com() -> Seq<u8> {
    seq![b'b', b'a', b'd', b'.'] + example_com()
}

/// `foo.example.com`
pub open spec fn foo_example_com() -> Seq<u8> {
    seq![b'f', b'o', b'o', b'.'] + example_com()
}

/// `bar.example.com`
pub open spec fn bar_example_com() -> Seq<u8> {
    seq![b'b', b'a', b'r', b'.'] + example_com()
}

/// `foo.bar.example.com`
pub open spec fn foo_bar_example_com() -> Seq<u8> {
    seq![b'f', b'o', b'o', b'.'] + bar_example_com()
}

/// `not-example.com`: ends with the bytes `example.com`, but not at a label
/// boundary.
pub open spec fn not_example_com() -> Seq<u8> {
    seq![b'n', b'o', b't', b'-'] + example_com()
}

/// `WWW.Example.COM`
pub open spec fn www_example_com_mixed_case() -> Seq<u8> {
    seq![b'W', b'W', b'W', b'.', b'E', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'C', b'O', b'M']
}

/// `EXAMPLE.com`
pub open spec fn example_com_upper() -> Seq<u8> {
    seq![b'E', b'X', b'A', b'M', b'P', b'L', b'E', b'.', b'c', b'o', b'm']
}

/// `.example.com`
pub open spec fn dot_example_com() -> Seq<u8> {
    seq![b'.'] + example_com()
}

/// `*.example.com`
pub open spec fn wildcard_example_com() -> Seq<u8> {
    seq![b'*', b'.'] + example_com()
}

/// `http://test.localhost` as a dNSName (BetterTLS's smuggled names).
pub open spec fn http_test_localhost() -> Seq<u8> {
    seq![b'h', b't', b't', b'p', b':', b'/', b'/'] + test_localhost()
}

/// A dNSName subtree.
pub open spec fn dns_subtree(base: Seq<u8>) -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::DnsName(base),
    }
}

/// An iPAddress subtree.
pub open spec fn ip_subtree(address: Seq<u8>, mask: Seq<u8>) -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask },
    }
}

/// `127.0.0.0/24`
pub open spec fn loopback_24() -> crate::name_constraints::spec::GeneralSubtree {
    ip_subtree(seq![127u8, 0, 0, 0], seq![255u8, 255, 255, 0])
}

/// `1.1.1.0/24`
pub open spec fn one_one_one_24() -> crate::name_constraints::spec::GeneralSubtree {
    ip_subtree(seq![1u8, 1, 1, 0], seq![255u8, 255, 255, 0])
}

/// `::1`
pub open spec fn ipv6_loopback() -> Seq<u8> {
    seq![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
}

/// Sixteen copies of `b`.
pub open spec fn sixteen(b: u8) -> Seq<u8> {
    seq![b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b]
}

/// A directoryName base `CN=foo` (UTF8String), as limbo's
/// `rfc5280::nc::*-dn-*` cases encode it.
pub open spec fn directory_name_subtree() -> crate::name_constraints::spec::GeneralSubtree {
    dn_subtree(name_of(rdn_cn(foo(), utf8_tag())))
}

/// A NameConstraints value.
pub open spec fn constraints(
    permitted: Option<Seq<crate::name_constraints::spec::GeneralSubtree>>,
    excluded: Option<Seq<crate::name_constraints::spec::GeneralSubtree>>,
) -> crate::name_constraints::spec::NameConstraints {
    crate::name_constraints::spec::NameConstraints { permitted_subtrees: permitted, excluded_subtrees: excluded }
}

/// A dNSName subjectAltName entry.
pub open spec fn dns_entry(name: Seq<u8>) -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::DnsName(name)
}

/// An iPAddress subjectAltName entry.
pub open spec fn ip_entry(address: Seq<u8>) -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::IpAddress(address)
}

/// A uniformResourceIdentifier entry `test.localhost`, kept whole by the
/// SAN decoder.
pub open spec fn uri_entry() -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::Other(6, seq![0x86u8, 0x0e] + test_localhost())
}

/// One certificate of a path, with limbo's leaf subject `CN=example.com`.
pub open spec fn certificate(
    names: Seq<crate::extensions::spec::GeneralName>,
    name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
) -> NcCertificate {
    certificate_with_subject(name_of(rdn_cn(example_com(), utf8_tag())), names, name_constraints)
}

/// One certificate of a path with the subject Name TLV `subject`.
pub open spec fn certificate_with_subject(
    subject: Seq<u8>,
    names: Seq<crate::extensions::spec::GeneralName>,
    name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
) -> NcCertificate {
    NcCertificate { subject, subject_alt_names: names, name_constraints }
}

// ---------------------------------------------------------------------------
// Directory names, mailboxes and other forms used below
// ---------------------------------------------------------------------------

/// UTF8String's tag byte.
pub open spec fn utf8_tag() -> u8 { 0x0c }

/// PrintableString's tag byte.
pub open spec fn printable_tag() -> u8 { 0x13 }

/// BMPString's tag byte.
pub open spec fn bmp_tag() -> u8 { 0x1e }

/// `foo`
pub open spec fn foo() -> Seq<u8> { seq![b'f', b'o', b'o'] }

/// `Foo`
pub open spec fn foo_upper() -> Seq<u8> { seq![b'F', b'o', b'o'] }

/// `not-foo`
pub open spec fn not_foo() -> Seq<u8> { seq![b'n', b'o', b't', b'-'] + foo() }

/// `Example`
pub open spec fn example_org() -> Seq<u8> { seq![b'E', b'x', b'a', b'm', b'p', b'l', b'e'] }

/// One RDN holding one attribute: `oid` (DER contents) and a value of tag
/// byte `tag`.
pub open spec fn rdn_of(oid: Seq<u8>, value: Seq<u8>, tag: u8) -> Seq<u8> {
    let attribute = seq![0x06u8, oid.len() as u8] + oid + seq![tag, value.len() as u8] + value;
    let sequence = seq![0x30u8, attribute.len() as u8] + attribute;
    seq![0x31u8, sequence.len() as u8] + sequence
}

/// An RDN `CN=value`.
pub open spec fn rdn_cn(value: Seq<u8>, tag: u8) -> Seq<u8> {
    rdn_of(seq![0x55u8, 0x04, 0x03], value, tag)
}

/// An RDN `O=value`.
pub open spec fn rdn_o(value: Seq<u8>, tag: u8) -> Seq<u8> {
    rdn_of(seq![0x55u8, 0x04, 0x0a], value, tag)
}

/// An RDN `emailAddress=value` (IA5String).
pub open spec fn rdn_email(value: Seq<u8>) -> Seq<u8> {
    rdn_of(seq![0x2au8, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x01], value, 0x16)
}

/// A Name TLV holding the RDN TLVs `rdns`.
pub open spec fn name_of(rdns: Seq<u8>) -> Seq<u8> {
    seq![0x30u8, rdns.len() as u8] + rdns
}

/// A directoryName subtree whose base is the Name TLV `name`.
pub open spec fn dn_subtree(name: Seq<u8>) -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::DirectoryName(name),
    }
}

/// A directoryName subjectAltName entry holding the Name TLV `name`.
pub open spec fn dn_entry(name: Seq<u8>) -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::Other(4, seq![0xa4u8, name.len() as u8] + name)
}

/// An rfc822Name subtree.
pub open spec fn email_subtree(base: Seq<u8>) -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(base),
    }
}

/// An rfc822Name subjectAltName entry.
pub open spec fn email_entry(mailbox: Seq<u8>) -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::Other(1, seq![0x81u8, mailbox.len() as u8] + mailbox)
}

/// `local@example.com`
pub open spec fn at_example_com(local: Seq<u8>) -> Seq<u8> {
    local + seq![b'@'] + example_com()
}

/// `foo@sub.example.com`
pub open spec fn foo_at_sub_example_com() -> Seq<u8> {
    foo() + seq![b'@', b's', b'u', b'b', b'.'] + example_com()
}

/// limbo's otherName contents (`rfc5280::nc::nc-forbids-othername`).
pub open spec fn other_name_contents() -> Seq<u8> {
    seq![0x06u8, 0x0b, 0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xb3, 0x3a, 0x85, 0x1a, 0x03, 0xa0, 0x02, 0x05, 0x00]
}

/// An otherName subtree, kept whole by the decoder.
pub open spec fn other_name_subtree() -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::Unsupported {
            tag: 0,
            der: seq![0xa0u8, 0x11] + other_name_contents(),
        },
    }
}

/// An otherName subjectAltName entry.
pub open spec fn other_name_entry() -> crate::extensions::spec::GeneralName {
    crate::extensions::spec::GeneralName::Other(0, seq![0xa0u8, 0x11] + other_name_contents())
}

/// A uniformResourceIdentifier subtree `example.com`.
pub open spec fn uri_subtree() -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::Unsupported {
            tag: 6,
            der: seq![0x86u8, 0x0b] + example_com(),
        },
    }
}

// ---------------------------------------------------------------------------
// BetterTLS (`bettertls::nameconstraints::tcN`)
// ---------------------------------------------------------------------------

/// `tc0` SUCCESS: no NameConstraints anywhere, so nothing is checked.
pub proof fn lemma_bettertls_tc0_no_constraints()
    ensures certificate_names_acceptable(initial_state(), seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(initial_state(), seq![dns_entry(test_localhost())]))
        by (compute_only);
}

/// `tc1` SUCCESS: permitted `localhost` holds `test.localhost` (one label
/// added).
pub proof fn lemma_bettertls_tc1_permitted_dns_subdomain()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
        seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc304` FAILURE: permitted `example.com` does not hold `test.localhost`.
pub proof fn lemma_bettertls_tc304_outside_permitted_dns()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(test_localhost())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc253` FAILURE: excluded `localhost` holds `test.localhost`.
pub proof fn lemma_bettertls_tc253_excluded_dns()
    ensures !certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(localhost())]))],
        seq![dns_entry(test_localhost())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(localhost())]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc256` SUCCESS: excluded `bad.example.com` does not touch
/// `test.localhost`. `tc1714` is the same chain with the leaf's subject CN
/// `bad.example.com`, also SUCCESS: the subject CN is not an input here.
pub proof fn lemma_bettertls_tc256_tc1714_outside_excluded_dns()
    ensures certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc280` FAILURE: the same name permitted and excluded; excluded wins.
pub proof fn lemma_bettertls_tc280_excluded_beats_permitted()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![dns_subtree(localhost())]))],
        seq![dns_entry(test_localhost())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![dns_subtree(localhost())]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc283` SUCCESS: permitted `localhost`, excluded `bad.example.com`.
pub proof fn lemma_bettertls_tc283_permitted_with_unrelated_excluded()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc259` SUCCESS: a permittedSubtrees of iPAddress only leaves dNSName
/// entries unconstrained.
pub proof fn lemma_bettertls_tc259_permitted_ip_leaves_dns_alone()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![loopback_24()]), None)],
        seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![loopback_24()]), None)],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc251` SUCCESS: an excluded iPAddress range does not touch a dNSName.
pub proof fn lemma_bettertls_tc251_excluded_ip_leaves_dns_alone()
    ensures certificate_names_acceptable(
        seq![constraints(None, Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(None, Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

/// `tc340` SUCCESS: `127.0.0.1` is in a permitted `127.0.0.0/24`.
pub proof fn lemma_bettertls_tc340_inside_permitted_ip()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![loopback_24()]), None)],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![loopback_24()]), None)],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc349` FAILURE: `127.0.0.1` is outside a permitted `1.1.1.0/24`.
pub proof fn lemma_bettertls_tc349_outside_permitted_ip()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![one_one_one_24()]), None)],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![one_one_one_24()]), None)],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc332` FAILURE: `127.0.0.1` is in an excluded `127.0.0.0/24`.
pub proof fn lemma_bettertls_tc332_excluded_ip()
    ensures !certificate_names_acceptable(
        seq![constraints(None, Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc333` SUCCESS: `127.0.0.1` is outside an excluded `1.1.1.0/24`.
pub proof fn lemma_bettertls_tc333_outside_excluded_ip()
    ensures certificate_names_acceptable(
        seq![constraints(None, Some(seq![one_one_one_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(certificate_names_acceptable(
        seq![constraints(None, Some(seq![one_one_one_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc358` SUCCESS: a dNSName-only permittedSubtrees leaves the iPAddress
/// entry unconstrained. `tc4489` is the same with only the iPAddress entry.
pub proof fn lemma_bettertls_tc358_tc4489_permitted_dns_leaves_ip_alone()
    ensures
        certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
            seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
        certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
            seq![ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
        seq![ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc359` FAILURE: the dNSName is permitted, but the iPAddress entry is in
/// an excluded range; every entry is checked.
pub proof fn lemma_bettertls_tc359_every_entry_checked()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), Some(seq![loopback_24()]))],
        seq![dns_entry(test_localhost()), ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// `tc8839` FAILURE: a URI entry under a dNSName constraint. BetterTLS
/// fails it on the hostname (the peer `test.localhost` is not presented).
/// No set constrains URIs, so the URI entry is unconstrained here, both
/// browsers agree, and the permitted dNSName passes: the name constraints
/// accept this certificate and the hostname check refuses it. With a URI
/// constraint in force the same entry fails (`nc-permits-uri-*`).
pub proof fn lemma_bettertls_tc8839_uri_entry_refused()
    ensures
        certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
            seq![dns_entry(bad_example_com()), uri_entry()]),
        !certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(example_com()), uri_subtree()]), None)],
            seq![dns_entry(bad_example_com()), uri_entry()]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(bad_example_com()), uri_entry()])) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com()), uri_subtree()]), None)],
        seq![dns_entry(bad_example_com()), uri_entry()])) by (compute_only);
}

/// `tc8785` FAILURE: a dNSName `http://test.localhost` is not a DNS name;
/// under constraints it is refused ((R) malformed entries).
pub proof fn lemma_bettertls_tc8785_malformed_dns_entry()
    ensures
        constrained_name(dns_entry(http_test_localhost())) is None,
        !certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
            seq![dns_entry(bad_example_com()), dns_entry(http_test_localhost())]),
{
    assert(constrained_name(dns_entry(http_test_localhost())) is None) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(bad_example_com()), dns_entry(http_test_localhost())])) by (compute_only);
}

// ---------------------------------------------------------------------------
// dNSName subtrees (`rfc5280::nc::*`)
// ---------------------------------------------------------------------------

/// `rfc5280::nc::permitted-dns-match` SUCCESS: zero labels added.
pub proof fn lemma_rfc5280_permitted_dns_match()
    ensures dns_within(example_com(), example_com()),
{
    assert(dns_within(example_com(), example_com())) by (compute_only);
}

/// `rfc5280::nc::permitted-dns-match-more` SUCCESS: two labels added.
pub proof fn lemma_rfc5280_permitted_dns_match_more()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(foo_bar_example_com())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(foo_bar_example_com())])) by (compute_only);
}

/// `rfc5280::nc::permitted-dns-mismatch` FAILURE: `not-example.com` ends
/// with the bytes `example.com`, but no label was added.
pub proof fn lemma_rfc5280_permitted_dns_mismatch_label_boundary()
    ensures
        !dns_within(not_example_com(), example_com()),
        !certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
            seq![dns_entry(not_example_com())]),
{
    assert(!dns_within(not_example_com(), example_com())) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(not_example_com())])) by (compute_only);
}

/// Case-insensitivity (RFC 9549 §2.3; no limbo case): `WWW.Example.COM` is
/// within `example.com`, and `example.com` is within `EXAMPLE.com`.
pub proof fn lemma_dns_case_insensitive_example()
    ensures
        dns_within(www_example_com_mixed_case(), example_com()),
        dns_within(example_com(), example_com_upper()),
{
    assert(dns_within(www_example_com_mixed_case(), example_com())) by (compute_only);
    assert(dns_within(example_com(), example_com_upper())) by (compute_only);
}

/// `rfc5280::nc::excluded-dns-match-second` FAILURE: the second entry is
/// excluded.
pub proof fn lemma_rfc5280_excluded_dns_match_second()
    ensures !certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(example_com()), dns_entry(bad_example_com())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(example_com()), dns_entry(bad_example_com())])) by (compute_only);
}

/// `rfc5280::nc::excluded-dns-match-second` with the entries reversed, and
/// its permitted counterpart: an entry that fails is caught wherever it
/// stands in the list.
pub proof fn lemma_every_entry_checked_in_any_position()
    ensures
        !certificate_names_acceptable(
            seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
            seq![dns_entry(bad_example_com()), dns_entry(example_com())]),
        !certificate_names_acceptable(
            seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
            seq![dns_entry(bad_example_com()), dns_entry(test_localhost())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(bad_example_com())]))],
        seq![dns_entry(bad_example_com()), dns_entry(example_com())])) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(localhost())]), None)],
        seq![dns_entry(bad_example_com()), dns_entry(test_localhost())])) by (compute_only);
}

/// `rfc5280::nc::nc-permits-invalid-dns-san` FAILURE: the entry
/// `.example.com` is not a DNS name, though its bytes end in `.example.com`.
pub proof fn lemma_rfc5280_nc_permits_invalid_dns_san()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(dot_example_com()), dns_entry(foo_example_com())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(dot_example_com()), dns_entry(foo_example_com())])) by (compute_only);
}

/// `rfc5280::nc::invalid-dnsname-leading-period` and
/// `rfc5280::nc::invalid-dnsname-wildcard` FAILURE: bases `.example.com` and
/// `*.example.com` are not supported (erratum 5997), so the path is refused.
pub proof fn lemma_rfc5280_malformed_dns_bases_refused()
    ensures
        !constraints_supported(constraints(Some(seq![dns_subtree(dot_example_com())]), None)),
        !constraints_supported(constraints(Some(seq![dns_subtree(wildcard_example_com())]), None)),
{
    assert(!constraints_supported(constraints(Some(seq![dns_subtree(dot_example_com())]), None)))
        by (compute_only);
    assert(!constraints_supported(constraints(Some(seq![dns_subtree(wildcard_example_com())]), None)))
        by (compute_only);
}

/// BR §7.1.2.5.2 (no limbo case): a zero-length dNSName holds every DNS
/// name, so excluding it excludes them all.
pub proof fn lemma_br_zero_length_dns_excludes_all()
    ensures
        constraints_supported(constraints(None, Some(seq![dns_subtree(seq![])]))),
        !certificate_names_acceptable(
            seq![constraints(None, Some(seq![dns_subtree(seq![])]))],
            seq![dns_entry(test_localhost())]),
{
    assert(constraints_supported(constraints(None, Some(seq![dns_subtree(seq![])])))) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![dns_subtree(seq![])]))],
        seq![dns_entry(test_localhost())])) by (compute_only);
}

// ---------------------------------------------------------------------------
// Wildcard entries (`cve::*`, `webpki::nc::*`)
// ---------------------------------------------------------------------------

/// `cve::cve-2025-61727` and `rfc5280::nc::nc-forbids-dnsname-wildcard-san`
/// FAILURE: `*.example.com` stands for `bar.example.com`, which is excluded.
pub proof fn lemma_cve_2025_61727_wildcard_meets_excluded()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![dns_subtree(bar_example_com())]))],
        seq![dns_entry(wildcard_example_com())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![dns_subtree(bar_example_com())]))],
        seq![dns_entry(wildcard_example_com())])) by (compute_only);
}

/// `cve::cve-2025-61727-nc-permits-variant` FAILURE: `*.example.com` stands
/// for names outside a permitted `foo.example.com`.
pub proof fn lemma_cve_2025_61727_wildcard_wider_than_permitted()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(foo_example_com())]), None)],
        seq![dns_entry(wildcard_example_com())]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(foo_example_com())]), None)],
        seq![dns_entry(wildcard_example_com())])) by (compute_only);
}

/// `webpki::nc::nc-permits-dns-san-pattern` SUCCESS: every name
/// `*.example.com` stands for is within a permitted `example.com`.
pub proof fn lemma_webpki_wildcard_within_permitted()
    ensures certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(wildcard_example_com())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(wildcard_example_com())])) by (compute_only);
}

// ---------------------------------------------------------------------------
// iPAddress subtrees
// ---------------------------------------------------------------------------

/// `rfc5280::nc::permitted-ipv6-match` SUCCESS and
/// `rfc5280::nc::excluded-ipv6-match` FAILURE: `::1/128`.
pub proof fn lemma_rfc5280_ipv6_host_range()
    ensures
        certificate_names_acceptable(
            seq![constraints(Some(seq![ip_subtree(ipv6_loopback(), sixteen(0xFF))]), None)],
            seq![ip_entry(ipv6_loopback())]),
        !certificate_names_acceptable(
            seq![constraints(None, Some(seq![ip_subtree(ipv6_loopback(), sixteen(0xFF))]))],
            seq![ip_entry(ipv6_loopback())]),
{
    assert(certificate_names_acceptable(
        seq![constraints(Some(seq![ip_subtree(ipv6_loopback(), sixteen(0xFF))]), None)],
        seq![ip_entry(ipv6_loopback())])) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![ip_subtree(ipv6_loopback(), sixteen(0xFF))]))],
        seq![ip_entry(ipv6_loopback())])) by (compute_only);
}

/// An IPv4 address is not within `::/0` (no limbo case): the lengths
/// differ, so a set that permits all of IPv6 permits no IPv4 address.
pub proof fn lemma_ipv4_not_within_ipv6_range()
    ensures
        !ip_within(seq![127u8, 0, 0, 1], sixteen(0), sixteen(0)),
        !certificate_names_acceptable(
            seq![constraints(Some(seq![ip_subtree(sixteen(0), sixteen(0))]), None)],
            seq![ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(!ip_within(seq![127u8, 0, 0, 1], sixteen(0), sixteen(0))) by (compute_only);
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![ip_subtree(sixteen(0), sixteen(0))]), None)],
        seq![ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// BR §7.1.2.5.2 (no limbo case): an excluded `0.0.0.0/0` excludes every
/// IPv4 address.
pub proof fn lemma_br_zero_ipv4_excludes_all()
    ensures !certificate_names_acceptable(
        seq![constraints(None, Some(seq![ip_subtree(seq![0u8, 0, 0, 0], seq![0u8, 0, 0, 0])]))],
        seq![ip_entry(seq![127u8, 0, 0, 1])]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(None, Some(seq![ip_subtree(seq![0u8, 0, 0, 0], seq![0u8, 0, 0, 0])]))],
        seq![ip_entry(seq![127u8, 0, 0, 1])])) by (compute_only);
}

/// Modelling choice (no limbo case): a non-contiguous mask
/// `255.0.255.0` is refused; `255.255.240.0` (/20) is accepted.
pub proof fn lemma_noncontiguous_mask_example()
    ensures
        !constraints_supported(constraints(None, Some(seq![ip_subtree(seq![10u8, 0, 10, 0], seq![255u8, 0, 255, 0])]))),
        constraints_supported(constraints(None, Some(seq![ip_subtree(seq![10u8, 0, 16, 0], seq![255u8, 255, 240, 0])]))),
{
    assert(!constraints_supported(constraints(None, Some(seq![ip_subtree(seq![10u8, 0, 10, 0], seq![255u8, 0, 255, 0])]))))
        by (compute_only);
    assert(constraints_supported(constraints(None, Some(seq![ip_subtree(seq![10u8, 0, 16, 0], seq![255u8, 255, 240, 0])]))))
        by (compute_only);
}

// ---------------------------------------------------------------------------
// Refused NameConstraints
// ---------------------------------------------------------------------------

/// `rfc5280::nc::excluded-dn-match` and `excluded-dn-match-sub-mismatch`
/// FAILURE ((R) excluded directoryName): a directoryName base in
/// excludedSubtrees refuses the path at §6.1.4 (g), whatever else the
/// extension holds. In permittedSubtrees it is applied, not refused.
pub proof fn lemma_q12_unsupported_base_refuses_path()
    ensures
        constraints_supported(constraints(Some(seq![directory_name_subtree()]), None)),
        !constraints_supported(constraints(None, Some(seq![directory_name_subtree()]))),
        !constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![directory_name_subtree()]))),
        !names_constrained(
            seq![certificate(seq![], Some(constraints(None, Some(seq![directory_name_subtree()])))),
                certificate(seq![dns_entry(example_com())], None)],
            initial_state()),
{
    assert(constraints_supported(constraints(Some(seq![directory_name_subtree()]), None))) by (compute_only);
    assert(!constraints_supported(constraints(None, Some(seq![directory_name_subtree()])))) by (compute_only);
    assert(!constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![directory_name_subtree()]))))
        by (compute_only);
    assert(!names_constrained(
        seq![certificate(seq![], Some(constraints(None, Some(seq![directory_name_subtree()])))),
            certificate(seq![dns_entry(example_com())], None)],
        initial_state())) by (compute_only);
}

/// `webpki::nc::intermediate-permitted-excluded-subtrees-both-null`
/// FAILURE: a NameConstraints with neither field is refused.
pub proof fn lemma_webpki_both_fields_absent_refused()
    ensures !constraints_supported(constraints(None, None)),
{
    assert(!constraints_supported(constraints(None, None))) by (compute_only);
}

// ---------------------------------------------------------------------------
// Paths (§6.1.3 (b), (c) and §6.1.4 (g) together)
// ---------------------------------------------------------------------------

/// `rfc5280::nc::restrictive-permits-in-intermediates-widens` FAILURE: a
/// later certificate cannot widen what an earlier one permitted; the
/// permitted subtrees intersect. (In limbo the intermediates also carry the
/// SAN `example.com`; they are left out here so only the intersection
/// decides.)
pub proof fn lemma_rfc5280_permits_cannot_widen()
    ensures !names_constrained(
        seq![
            certificate(seq![], Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![], Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![], Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::restrictive-permits-in-intermediates-narrows` FAILURE: a
/// later certificate narrows the permitted subtrees.
pub proof fn lemma_rfc5280_permits_narrow()
    ensures !names_constrained(
        seq![
            certificate(seq![], Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![], Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![], Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state())) by (compute_only);
}

/// Excluded subtrees accumulate across certificates (no limbo case): a name
/// excluded by the first intermediate stays excluded after a second one
/// with its own exclusions.
pub proof fn lemma_excluded_subtrees_accumulate()
    ensures !names_constrained(
        seq![
            certificate(seq![], Some(constraints(None, Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![], Some(constraints(None, Some(seq![dns_subtree(localhost())])))),
            certificate(seq![dns_entry(bad_example_com())], None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], Some(constraints(None, Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![], Some(constraints(None, Some(seq![dns_subtree(localhost())])))),
            certificate(seq![dns_entry(bad_example_com())], None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::intermediate-with-san-rejected-by-intermediate-nc`
/// FAILURE: an intermediate's own SAN is checked against earlier
/// constraints.
pub proof fn lemma_rfc5280_intermediate_san_checked()
    ensures !names_constrained(
        seq![
            certificate(seq![dns_entry(example_com())], Some(constraints(
                Some(seq![dns_subtree(foo_example_com())]), Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![dns_entry(bad_example_com())], None),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![dns_entry(example_com())], Some(constraints(
                Some(seq![dns_subtree(foo_example_com())]), Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![dns_entry(bad_example_com())], None),
            certificate(seq![dns_entry(foo_example_com())], None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::permitted-self-issued` (SUCCESS in limbo, a listed
/// divergence; (R) self-issued intermediates are checked): a self-issued
/// intermediate whose SAN `not-example.com` is outside the anchor's
/// permitted `example.com` is checked, as Firefox checks it, and the path is
/// refused. (The anchor's constraints are the initial state here.)
pub proof fn lemma_rfc5280_self_issued_intermediate_checked()
    ensures !names_constrained(
        seq![
            certificate(seq![dns_entry(not_example_com())], None),
            certificate(seq![dns_entry(example_com())], None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)]),
{
    assert(!names_constrained(
        seq![
            certificate(seq![dns_entry(not_example_com())], None),
            certificate(seq![dns_entry(example_com())], None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)])) by (compute_only);
}

/// `rfc5280::nc::excluded-self-issued-leaf` FAILURE: a self-issued final
/// certificate is checked, as every certificate is. (In limbo the intermediate also has a SAN
/// outside the constraint; it has none here, so only the final-certificate
/// rule decides.)
pub proof fn lemma_rfc5280_self_issued_final_checked()
    ensures !names_constrained(
        seq![
            certificate(seq![], None),
            certificate(seq![dns_entry(not_example_com())], None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)]),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], None),
            certificate(seq![dns_entry(not_example_com())], None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)])) by (compute_only);
}

/// §6.1.4 is not applied to the final certificate, so this module does not
/// look at its NameConstraints extension, even one it would refuse (an
/// excluded directoryName). The path specification refuses one in an
/// end-entity certificate (`rfc5280::nc::not-allowed-in-ee-critical`).
pub proof fn lemma_final_certificate_constraints_not_processed()
    ensures names_constrained(
        seq![certificate(seq![dns_entry(example_com())],
            Some(constraints(None, Some(seq![directory_name_subtree()]))))],
        initial_state()),
{
    assert(names_constrained(
        seq![certificate(seq![dns_entry(example_com())],
            Some(constraints(None, Some(seq![directory_name_subtree()]))))],
        initial_state())) by (compute_only);
}

// ---------------------------------------------------------------------------
// directoryName subtrees (`rfc5280::nc::*-dn-*`)
// ---------------------------------------------------------------------------

/// `rfc5280::nc::permitted-dn-match` SUCCESS: the anchor permits `CN=foo`;
/// the leaf's subject and its directoryName entry are both `CN=foo`. (The
/// anchor's constraints are the initial state here.)
pub proof fn lemma_rfc5280_permitted_dn_match()
    ensures
        names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// `rfc5280::nc::permitted-dn-mismatch` FAILURE: `CN=not-foo` is not within
/// `CN=foo`, as a subject or as an entry.
pub proof fn lemma_rfc5280_permitted_dn_mismatch()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(not_foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(not_foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(not_foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(not_foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// `rfc5280::nc::permitted-dn-match-subject-san-mismatch` FAILURE: the
/// directoryName entry matches but the subject does not; the subject field
/// is checked even with a subjectAltName present (Firefox; RFC 5280
/// §4.2.1.10 "MUST be applied to the subject field").
pub proof fn lemma_rfc5280_permitted_dn_subject_checked()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(not_foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(not_foo(), utf8_tag())), seq![dn_entry(name_of(rdn_cn(foo(), utf8_tag())))], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// Firefox (no limbo case): an empty subject is checked too and fails a
/// non-empty permitted directoryName, even beside a subjectAltName. Chrome
/// skips it; this is (R) against Chrome.
pub proof fn lemma_dn_empty_subject_fails()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(seq![]), seq![dns_entry(example_com())], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(seq![]), seq![dns_entry(example_com())], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// The prefix rule (no limbo case): a permitted `O=Example` holds
/// `O=Example, CN=foo` (RDNs added after the base's), but not
/// `CN=foo, O=Example`; and an empty base holds every name.
pub proof fn lemma_dn_prefix_rule()
    ensures
        names_constrained(seq![certificate_with_subject(name_of(rdn_o(example_org(), utf8_tag()) + rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_o(example_org(), utf8_tag())))]), None)]),
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag()) + rdn_o(example_org(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_o(example_org(), utf8_tag())))]), None)]),
        names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(seq![]))]), None)]),
{
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_o(example_org(), utf8_tag()) + rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_o(example_org(), utf8_tag())))]), None)])) by (compute_only);
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag()) + rdn_o(example_org(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_o(example_org(), utf8_tag())))]), None)])) by (compute_only);
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(seq![]))]), None)])) by (compute_only);
}

/// Firefox's tag relaxation, both directions (no limbo case): a
/// UTF8String base holds a PrintableString value with the same bytes, and
/// the reverse. Chrome normalizes both to the same string.
pub proof fn lemma_dn_utf8_printable_relaxation()
    ensures
        names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), printable_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
        names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(foo(), printable_tag())))]), None)]),
{
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), printable_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(foo(), printable_tag())))]), None)])) by (compute_only);
}

/// (R) against Chrome (no limbo case): `CN=Foo` is not within `CN=foo`,
/// which Chrome's case folding would accept and Firefox refuses.
pub proof fn lemma_dn_no_normalization()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo_upper(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(foo_upper(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// (R) (no limbo case): values Chrome cannot normalize never match, even
/// byte for byte: a BMPString, and a PrintableString holding `*`, which is
/// not a PrintableString character.
pub proof fn lemma_dn_values_chrome_cannot_compare()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(seq![0u8, b'f'], bmp_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(seq![0u8, b'f'], bmp_tag())))]), None)]),
        !names_constrained(seq![certificate_with_subject(name_of(rdn_cn(seq![b'*'], printable_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(seq![b'*'], printable_tag())))]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(seq![0u8, b'f'], bmp_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(seq![0u8, b'f'], bmp_tag())))]), None)])) by (compute_only);
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_cn(seq![b'*'], printable_tag())), seq![], None)], seq![constraints(Some(seq![dn_subtree(name_of(rdn_cn(seq![b'*'], printable_tag())))]), None)])) by (compute_only);
}

/// (R) malformed bases (no limbo case): a directoryName base that is not
/// one Name refuses the path.
pub proof fn lemma_dn_malformed_base_refused()
    ensures
        !constraints_supported(constraints(Some(seq![dn_subtree(seq![0x30u8, 0x02, 0x31, 0x00])]), None)),
{
    assert(!constraints_supported(constraints(Some(seq![dn_subtree(seq![0x30u8, 0x02, 0x31, 0x00])]), None))) by (compute_only);
}

// ---------------------------------------------------------------------------
// rfc822Name subtrees (`rfc5280::nc::nc-permits-email-*`)
// ---------------------------------------------------------------------------

/// `rfc5280::nc::nc-permits-email-exact` SUCCESS: a mailbox base holds
/// that mailbox.
pub proof fn lemma_rfc5280_email_exact()
    ensures
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(foo()))]), None)], seq![email_entry(at_example_com(foo()))]),
{
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(foo()))]), None)], seq![email_entry(at_example_com(foo()))])) by (compute_only);
}

/// `rfc5280::nc::nc-permits-email-domain` SUCCESS and
/// `nc-permits-email-domain-rejects-subdomain` FAILURE: a host base holds
/// the mailboxes at exactly that host.
pub proof fn lemma_rfc5280_email_host()
    ensures
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(foo()))]),
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(foo_at_sub_example_com())]),
{
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(foo()))])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(foo_at_sub_example_com())])) by (compute_only);
}

/// `rfc5280::nc::nc-permits-email-subdomains-rejects-apex` FAILURE: a
/// domain base `.example.com` holds `foo@sub.example.com` but not
/// `foo@example.com`.
pub proof fn lemma_rfc5280_email_domain()
    ensures
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(dot_example_com())]), None)], seq![email_entry(foo_at_sub_example_com())]),
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(dot_example_com())]), None)], seq![email_entry(at_example_com(foo()))]),
{
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(dot_example_com())]), None)], seq![email_entry(foo_at_sub_example_com())])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(dot_example_com())]), None)], seq![email_entry(at_example_com(foo()))])) by (compute_only);
}

/// `rfc5280::nc::nc-permits-email-literal-*`: every character is literal.
/// `*@example.com` holds itself, not `user@example.com` and not
/// `*@sub.example.com`; `**@example.com` holds itself and not
/// `*@example.com`; `user*@example.com` holds itself.
pub proof fn lemma_rfc5280_email_literal_asterisks()
    ensures
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*']))]),
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(at_example_com(seq![b'u', b's', b'e', b'r']))]),
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(seq![b'*', b'@', b's', b'u', b'b', b'.'] + example_com())]),
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*', b'*']))]),
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*']))]),
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'u', b's', b'e', b'r', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'u', b's', b'e', b'r', b'*']))]),
{
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*']))])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(at_example_com(seq![b'u', b's', b'e', b'r']))])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*']))]), None)], seq![email_entry(seq![b'*', b'@', b's', b'u', b'b', b'.'] + example_com())])) by (compute_only);
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*', b'*']))])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'*', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'*']))])) by (compute_only);
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(seq![b'u', b's', b'e', b'r', b'*']))]), None)], seq![email_entry(at_example_com(seq![b'u', b's', b'e', b'r', b'*']))])) by (compute_only);
}

/// Local parts (no limbo case): a permitted `Foo@example.com` does not hold
/// `foo@example.com` (Chrome; (R) against Firefox); an excluded one catches
/// it (Firefox). Hosts ignore case in both.
pub proof fn lemma_email_local_part_case()
    ensures
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(foo_upper()))]), None)], seq![email_entry(at_example_com(foo()))]),
        !certificate_names_acceptable(seq![constraints(None, Some(seq![email_subtree(at_example_com(foo_upper()))]))], seq![email_entry(at_example_com(foo()))]),
        certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(foo() + seq![b'@'] + example_com_upper())]), None)], seq![email_entry(at_example_com(foo()))]),
{
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(at_example_com(foo_upper()))]), None)], seq![email_entry(at_example_com(foo()))])) by (compute_only);
    assert(!certificate_names_acceptable(seq![constraints(None, Some(seq![email_subtree(at_example_com(foo_upper()))]))], seq![email_entry(at_example_com(foo()))])) by (compute_only);
    assert(certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(foo() + seq![b'@'] + example_com_upper())]), None)], seq![email_entry(at_example_com(foo()))])) by (compute_only);
}

/// `rfc5280::nc::invalid-email-address` FAILURE: the base
/// `invalid@invalid@example.com` is not a mailbox, so the path is refused.
pub proof fn lemma_rfc5280_invalid_email_base_refused()
    ensures
        !constraints_supported(constraints(Some(seq![email_subtree(seq![b'i', b'@'] + at_example_com(seq![b'i']))]), None)),
{
    assert(!constraints_supported(constraints(Some(seq![email_subtree(seq![b'i', b'@'] + at_example_com(seq![b'i']))]), None))) by (compute_only);
}

/// `rfc5280::nc::nc-permits-invalid-email-san` FAILURE ((R) malformed
/// entries): an entry `invalid@address@example.com` beside two good
/// mailboxes is refused.
pub proof fn lemma_rfc5280_invalid_email_entry_refused()
    ensures
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(seq![b'g'])), email_entry(seq![b'i', b'@'] + at_example_com(seq![b'a']))]),
{
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(seq![b'g'])), email_entry(seq![b'i', b'@'] + at_example_com(seq![b'a']))])) by (compute_only);
}

/// (R) emailAddress (no limbo case): with an rfc822Name constraint in
/// force, a subject emailAddress attribute fails the certificate, even one
/// the constraint would permit; with only dNSName constraints it is
/// ignored.
pub proof fn lemma_subject_email_address_refused()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_email(at_example_com(foo()))), seq![email_entry(at_example_com(foo()))], None)], seq![constraints(Some(seq![email_subtree(example_com())]), None)]),
        names_constrained(seq![certificate_with_subject(name_of(rdn_email(at_example_com(foo()))), seq![dns_entry(example_com())], None)], seq![constraints(Some(seq![dns_subtree(example_com())]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_email(at_example_com(foo()))), seq![email_entry(at_example_com(foo()))], None)], seq![constraints(Some(seq![email_subtree(example_com())]), None)])) by (compute_only);
    assert(names_constrained(seq![certificate_with_subject(name_of(rdn_email(at_example_com(foo()))), seq![dns_entry(example_com())], None)], seq![constraints(Some(seq![dns_subtree(example_com())]), None)])) by (compute_only);
}

// ---------------------------------------------------------------------------
// The other forms (`rfc5280::nc::nc-forbids-othername*`, `nc-permits-uri-*`)
// ---------------------------------------------------------------------------

/// `rfc5280::nc::nc-forbids-othername` FAILURE and `nc-forbids-othername-noop`
/// SUCCESS: an excluded otherName fails a certificate with an otherName
/// entry and has no effect on one without.
pub proof fn lemma_rfc5280_othername()
    ensures
        !certificate_names_acceptable(seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()]))], seq![dns_entry(example_com()), other_name_entry()]),
        certificate_names_acceptable(seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()]))], seq![dns_entry(example_com())]),
        constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()]))),
{
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()]))], seq![dns_entry(example_com()), other_name_entry()])) by (compute_only);
    assert(certificate_names_acceptable(seq![constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()]))], seq![dns_entry(example_com())])) by (compute_only);
    assert(constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![other_name_subtree()])))) by (compute_only);
}

/// `rfc5280::nc::nc-permits-uri-host-rejects-subdomain` FAILURE: a permitted
/// URI constraint fails every URI entry, even one it would hold, since URI
/// subtrees have no meaning here (Firefox's rule).
pub proof fn lemma_rfc5280_uri_constrained()
    ensures
        !certificate_names_acceptable(seq![constraints(Some(seq![uri_subtree()]), None)], seq![dns_entry(example_com()), uri_entry()]),
{
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![uri_subtree()]), None)], seq![dns_entry(example_com()), uri_entry()])) by (compute_only);
}

/// BR §7.1.2.5.2 (no limbo case), end to end: the decoder accepts an
/// excludedSubtrees holding a zero-length dNSName, and the result excludes
/// every DNS name.
pub proof fn lemma_br_zero_length_dns_decoded()
    ensures
        match crate::name_constraints::spec::parse_name_constraints(seq![0x30u8, 0x06, 0xa1, 0x04, 0x30, 0x02, 0x82, 0x00]) { Some(value) => constraints_supported(value) && !certificate_names_acceptable(seq![value], seq![dns_entry(test_localhost())]), None => false },
{
    assert(match crate::name_constraints::spec::parse_name_constraints(seq![0x30u8, 0x06, 0xa1, 0x04, 0x30, 0x02, 0x82, 0x00]) { Some(value) => constraints_supported(value) && !certificate_names_acceptable(seq![value], seq![dns_entry(test_localhost())]), None => false }) by (compute_only);
}

/// The attribute type matters (no limbo case): `O=foo` is not within
/// `CN=foo`, though the values are equal.
pub proof fn lemma_dn_attribute_type_matters()
    ensures
        !names_constrained(seq![certificate_with_subject(name_of(rdn_o(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)]),
{
    assert(!names_constrained(seq![certificate_with_subject(name_of(rdn_o(foo(), utf8_tag())), seq![], None)], seq![constraints(Some(seq![directory_name_subtree()]), None)])) by (compute_only);
}

/// (R) malformed entries (no limbo case): `.foo@example.com` has a local
/// part with a leading dot, so it is no mailbox and is refused, though its
/// host is the permitted one.
pub proof fn lemma_email_malformed_local_refused()
    ensures
        !certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(seq![b'.'] + foo()))]),
{
    assert(!certificate_names_acceptable(seq![constraints(Some(seq![email_subtree(example_com())]), None)], seq![email_entry(at_example_com(seq![b'.'] + foo()))])) by (compute_only);
}

} // verus!
