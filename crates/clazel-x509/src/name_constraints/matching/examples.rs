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

/// A directoryName base `CN=foo`, which the decoder keeps as `Unsupported`.
pub open spec fn directory_name_subtree() -> crate::name_constraints::spec::GeneralSubtree {
    crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::Unsupported {
            tag: 4,
            der: seq![0xa4u8, 0x10, 0x30, 0x0e, 0x31, 0x0c, 0x30, 0x0a, 0x06, 0x03, 0x55, 0x04, 0x03,
                0x0c, 0x03, b'f', b'o', b'o'],
        },
    }
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

/// One certificate of a path.
pub open spec fn certificate(
    names: Seq<crate::extensions::spec::GeneralName>,
    self_issued: bool,
    name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
) -> NcCertificate {
    NcCertificate { subject_alt_names: names, self_issued, name_constraints }
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
/// fails it on the hostname; here Q12 refuses it even though the dNSName
/// `bad.example.com` is permitted.
pub proof fn lemma_bettertls_tc8839_uri_entry_refused()
    ensures !certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(bad_example_com()), uri_entry()]),
{
    assert(!certificate_names_acceptable(
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)],
        seq![dns_entry(bad_example_com()), uri_entry()])) by (compute_only);
}

/// `tc8785` FAILURE: a dNSName `http://test.localhost` is not a DNS name;
/// under constraints it is refused (Q12, names).
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
// Q12 and malformed NameConstraints
// ---------------------------------------------------------------------------

/// `rfc5280::nc::permitted-dn-match` (SUCCESS in limbo, a listed
/// divergence) and `rfc5280::nc::nc-forbids-othername-noop` (likewise): a
/// directoryName base, in either list, refuses the path at §6.1.4 (g).
pub proof fn lemma_q12_unsupported_base_refuses_path()
    ensures
        !constraints_supported(constraints(Some(seq![directory_name_subtree()]), None)),
        !constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![directory_name_subtree()]))),
        !names_constrained(
            seq![certificate(seq![], false, Some(constraints(Some(seq![directory_name_subtree()]), None))),
                certificate(seq![dns_entry(example_com())], false, None)],
            initial_state()),
{
    assert(!constraints_supported(constraints(Some(seq![directory_name_subtree()]), None))) by (compute_only);
    assert(!constraints_supported(constraints(Some(seq![dns_subtree(example_com())]), Some(seq![directory_name_subtree()]))))
        by (compute_only);
    assert(!names_constrained(
        seq![certificate(seq![], false, Some(constraints(Some(seq![directory_name_subtree()]), None))),
            certificate(seq![dns_entry(example_com())], false, None)],
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
            certificate(seq![], false, Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], false, Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::restrictive-permits-in-intermediates-narrows` FAILURE: a
/// later certificate narrows the permitted subtrees.
pub proof fn lemma_rfc5280_permits_narrow()
    ensures !names_constrained(
        seq![
            certificate(seq![], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![], false, Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com()), dns_subtree(bar_example_com())]), None))),
            certificate(seq![], false, Some(constraints(Some(seq![dns_subtree(bar_example_com())]), None))),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state())) by (compute_only);
}

/// Excluded subtrees accumulate across certificates (no limbo case): a name
/// excluded by the first intermediate stays excluded after a second one
/// with its own exclusions.
pub proof fn lemma_excluded_subtrees_accumulate()
    ensures !names_constrained(
        seq![
            certificate(seq![], false, Some(constraints(None, Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![], false, Some(constraints(None, Some(seq![dns_subtree(localhost())])))),
            certificate(seq![dns_entry(bad_example_com())], false, None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], false, Some(constraints(None, Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![], false, Some(constraints(None, Some(seq![dns_subtree(localhost())])))),
            certificate(seq![dns_entry(bad_example_com())], false, None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::intermediate-with-san-rejected-by-intermediate-nc`
/// FAILURE: an intermediate's own SAN is checked against earlier
/// constraints.
pub proof fn lemma_rfc5280_intermediate_san_checked()
    ensures !names_constrained(
        seq![
            certificate(seq![dns_entry(example_com())], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com())]), Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![dns_entry(bad_example_com())], false, None),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state()),
{
    assert(!names_constrained(
        seq![
            certificate(seq![dns_entry(example_com())], false, Some(constraints(
                Some(seq![dns_subtree(foo_example_com())]), Some(seq![dns_subtree(bad_example_com())])))),
            certificate(seq![dns_entry(bad_example_com())], false, None),
            certificate(seq![dns_entry(foo_example_com())], false, None),
        ],
        initial_state())) by (compute_only);
}

/// `rfc5280::nc::permitted-self-issued` SUCCESS: a self-issued intermediate
/// whose SAN `not-example.com` is outside the anchor's permitted
/// `example.com` is not checked. (The anchor's constraints are the initial
/// state here.)
pub proof fn lemma_rfc5280_self_issued_intermediate_skipped()
    ensures names_constrained(
        seq![
            certificate(seq![dns_entry(not_example_com())], true, None),
            certificate(seq![dns_entry(example_com())], false, None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)]),
{
    assert(names_constrained(
        seq![
            certificate(seq![dns_entry(not_example_com())], true, None),
            certificate(seq![dns_entry(example_com())], false, None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)])) by (compute_only);
}

/// `rfc5280::nc::excluded-self-issued-leaf` FAILURE: a self-issued final
/// certificate is checked. (In limbo the intermediate also has a SAN
/// outside the constraint; it has none here, so only the final-certificate
/// rule decides.)
pub proof fn lemma_rfc5280_self_issued_final_checked()
    ensures !names_constrained(
        seq![
            certificate(seq![], false, None),
            certificate(seq![dns_entry(not_example_com())], true, None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)]),
{
    assert(!names_constrained(
        seq![
            certificate(seq![], false, None),
            certificate(seq![dns_entry(not_example_com())], true, None),
        ],
        seq![constraints(Some(seq![dns_subtree(example_com())]), None)])) by (compute_only);
}

/// §6.1.4 is not applied to the final certificate, so this module does not
/// look at its NameConstraints extension, even an unsupported one. The path
/// specification refuses one in an end-entity certificate
/// (`rfc5280::nc::not-allowed-in-ee-critical`).
pub proof fn lemma_final_certificate_constraints_not_processed()
    ensures names_constrained(
        seq![certificate(seq![dns_entry(example_com())], false,
            Some(constraints(Some(seq![directory_name_subtree()]), None)))],
        initial_state()),
{
    assert(names_constrained(
        seq![certificate(seq![dns_entry(example_com())], false,
            Some(constraints(Some(seq![directory_name_subtree()]), None)))],
        initial_state())) by (compute_only);
}

} // verus!
