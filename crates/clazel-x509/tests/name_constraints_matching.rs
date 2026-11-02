//! Known answers for the executable name-constraint matcher
//! (`name_constraints::matching::exec`), mirroring `matching/examples.rs`,
//! which proves the same situations on the spec. The certificates here are
//! built as DER and run through the crate's own decoders (SubjectAltName,
//! NameConstraints, Name), so the path from bytes to verdict is the shipped
//! one. The executable code is proven equal to the spec; these tests pin the
//! spec's answers on the executable code and the comparison bound.

use clazel_x509::extensions::exec::{GeneralName, parse_subject_alt_name};
use clazel_x509::name_constraints::exec::{NameConstraints, parse_name_constraints};
use clazel_x509::name_constraints::matching::exec::{
    NcCertificate, dns_wildcard_meets, dns_within, ip_within, names_constrained, rfc822_meets,
    rfc822_within,
};

// ---------------------------------------------------------------------------
// DER builders
// ---------------------------------------------------------------------------

fn tlv(tag: u8, content: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    let length = content.len();
    if length < 0x80 {
        out.push(u8::try_from(length).unwrap_or(0));
    } else if length < 0x100 {
        out.extend_from_slice(&[0x81, u8::try_from(length).unwrap_or(0)]);
    } else if length < 0x1_0000 {
        let high = u8::try_from(length >> 8).unwrap_or(0);
        let low = u8::try_from(length & 0xff).unwrap_or(0);
        out.extend_from_slice(&[0x82, high, low]);
    } else {
        let top = u8::try_from(length >> 16).unwrap_or(0);
        let high = u8::try_from((length >> 8) & 0xff).unwrap_or(0);
        let low = u8::try_from(length & 0xff).unwrap_or(0);
        out.extend_from_slice(&[0x83, top, high, low]);
    }
    out.extend_from_slice(content);
    out
}

fn concat(items: &[Vec<u8>]) -> Vec<u8> {
    items.iter().flatten().copied().collect()
}

const UTF8: u8 = 0x0c;
const PRINTABLE: u8 = 0x13;
const BMP: u8 = 0x1e;
const CN_OID: &[u8] = &[0x55, 0x04, 0x03];
const O_OID: &[u8] = &[0x55, 0x04, 0x0a];
const EMAIL_OID: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x09, 0x01];

/// One RDN `oid = value`, the value having string tag `tag`.
fn rdn(oid: &[u8], value: &[u8], tag: u8) -> Vec<u8> {
    let attribute = concat(&[tlv(0x06, oid), tlv(tag, value)]);
    tlv(0x31, &tlv(0x30, &attribute))
}

fn rdn_cn(value: &[u8], tag: u8) -> Vec<u8> {
    rdn(CN_OID, value, tag)
}

fn rdn_o(value: &[u8], tag: u8) -> Vec<u8> {
    rdn(O_OID, value, tag)
}

fn name(rdns: &[Vec<u8>]) -> Vec<u8> {
    tlv(0x30, &concat(rdns))
}

/// limbo's leaf subject, `CN=example.com`.
fn cn_example() -> Vec<u8> {
    name(&[rdn_cn(b"example.com", UTF8)])
}

fn cn_foo() -> Vec<u8> {
    name(&[rdn_cn(b"foo", UTF8)])
}

// Subtree bases (inside a GeneralSubtree).
fn dns_base(text: &str) -> Vec<u8> {
    tlv(0x82, text.as_bytes())
}

fn ip_base(address: &[u8], mask: &[u8]) -> Vec<u8> {
    tlv(0x87, &[address, mask].concat())
}

fn email_base(text: &str) -> Vec<u8> {
    tlv(0x81, text.as_bytes())
}

fn dn_base(name_der: &[u8]) -> Vec<u8> {
    tlv(0xa4, name_der)
}

fn other_name_base() -> Vec<u8> {
    tlv(0xa0, &other_name_contents())
}

fn uri_base(text: &str) -> Vec<u8> {
    tlv(0x86, text.as_bytes())
}

fn other_name_contents() -> Vec<u8> {
    vec![
        0x06, 0x0b, 0x2b, 0x06, 0x01, 0x04, 0x01, 0x83, 0xb3, 0x3a, 0x85, 0x1a, 0x03, 0xa0, 0x02,
        0x05, 0x00,
    ]
}

/// A NameConstraints value from bases (each wrapped in a GeneralSubtree).
fn nc(permitted: Option<&[Vec<u8>]>, excluded: Option<&[Vec<u8>]>) -> Vec<u8> {
    let wrap = |bases: &[Vec<u8>], tag: u8| {
        let subtrees: Vec<Vec<u8>> = bases.iter().map(|b| tlv(0x30, b)).collect();
        tlv(tag, &concat(&subtrees))
    };
    let mut fields = Vec::new();
    if let Some(bases) = permitted {
        fields.extend(wrap(bases, 0xa0));
    }
    if let Some(bases) = excluded {
        fields.extend(wrap(bases, 0xa1));
    }
    tlv(0x30, &fields)
}

// SubjectAltName entries.
fn san_dns(text: &str) -> Vec<u8> {
    tlv(0x82, text.as_bytes())
}

fn san_ip(address: &[u8]) -> Vec<u8> {
    tlv(0x87, address)
}

fn san_email(text: &str) -> Vec<u8> {
    tlv(0x81, text.as_bytes())
}

fn san_dn(name_der: &[u8]) -> Vec<u8> {
    tlv(0xa4, name_der)
}

fn san_other_name() -> Vec<u8> {
    tlv(0xa0, &other_name_contents())
}

fn san_uri(text: &str) -> Vec<u8> {
    tlv(0x86, text.as_bytes())
}

// ---------------------------------------------------------------------------
// Running a path
// ---------------------------------------------------------------------------

/// One certificate of a path, as bytes.
struct Cert {
    subject: Vec<u8>,
    sans: Vec<Vec<u8>>,
    nc: Option<Vec<u8>>,
}

fn cert(sans: &[Vec<u8>]) -> Cert {
    Cert {
        subject: cn_example(),
        sans: sans.to_vec(),
        nc: None,
    }
}

fn ca(sans: &[Vec<u8>], nc: Vec<u8>) -> Cert {
    Cert {
        subject: cn_example(),
        sans: sans.to_vec(),
        nc: Some(nc),
    }
}

fn cert_with_subject(subject: Vec<u8>, sans: &[Vec<u8>]) -> Cert {
    Cert {
        subject,
        sans: sans.to_vec(),
        nc: None,
    }
}

/// The verdict of `names_constrained` on `certs`, first certificate first,
/// from the state holding the NameConstraints values `initial`. `None` if a
/// test input does not decode.
fn run(initial: &[Vec<u8>], certs: &[Cert]) -> Option<bool> {
    let initial_sets: Vec<NameConstraints<'_>> = initial
        .iter()
        .map(|bytes| parse_name_constraints(bytes))
        .collect::<Option<_>>()?;
    let san_values: Vec<Vec<u8>> = certs.iter().map(|c| tlv(0x30, &concat(&c.sans))).collect();
    let mut san_lists: Vec<Vec<GeneralName<'_>>> = Vec::new();
    for (c, value) in certs.iter().zip(&san_values) {
        if c.sans.is_empty() {
            san_lists.push(Vec::new());
        } else {
            san_lists.push(parse_subject_alt_name(value)?.names);
        }
    }
    let mut extensions: Vec<Option<NameConstraints<'_>>> = Vec::new();
    for c in certs {
        extensions.push(match &c.nc {
            Some(bytes) => Some(parse_name_constraints(bytes)?),
            None => None,
        });
    }
    let path: Vec<NcCertificate<'_>> = certs
        .iter()
        .zip(&san_lists)
        .zip(&extensions)
        .map(|((c, names), extension)| NcCertificate {
            subject: &c.subject,
            subject_alt_names: names,
            name_constraints: extension.as_ref(),
        })
        .collect();
    let state = initial_sets.iter().collect();
    Some(names_constrained(&path, state))
}

/// One leaf with `sans` under the one NameConstraints value `constraints`,
/// as BetterTLS's chains do (the constraints on the intermediate).
fn leaf_under(constraints: Vec<u8>, sans: &[Vec<u8>]) -> Option<bool> {
    run(&[constraints], &[cert(sans)])
}

fn accepted(verdict: Option<bool>) {
    assert_eq!(verdict, Some(true));
}

fn refused(verdict: Option<bool>) {
    assert_eq!(verdict, Some(false));
}

fn permitted(bases: &[Vec<u8>]) -> Vec<u8> {
    nc(Some(bases), None)
}

fn excluded(bases: &[Vec<u8>]) -> Vec<u8> {
    nc(None, Some(bases))
}

const LOOPBACK_24: ([u8; 4], [u8; 4]) = ([127, 0, 0, 0], [255, 255, 255, 0]);
const ONE_24: ([u8; 4], [u8; 4]) = ([1, 1, 1, 0], [255, 255, 255, 0]);

fn ip24(range: ([u8; 4], [u8; 4])) -> Vec<u8> {
    ip_base(&range.0, &range.1)
}

// ---------------------------------------------------------------------------
// Nothing in force
// ---------------------------------------------------------------------------

#[test]
fn empty_state_checks_nothing() {
    // BetterTLS tc0: no NameConstraints anywhere.
    accepted(run(&[], &[cert(&[san_dns("test.localhost")])]));
    // Not even a malformed entry: the initial state permits every name.
    accepted(run(&[], &[cert(&[san_dns("http://test.localhost")])]));
    accepted(run(&[], &[]));
}

// ---------------------------------------------------------------------------
// BetterTLS
// ---------------------------------------------------------------------------

#[test]
fn bettertls_dns() {
    let test_localhost = [san_dns("test.localhost")];
    // tc1: one label added to a permitted `localhost`.
    accepted(leaf_under(
        permitted(&[dns_base("localhost")]),
        &test_localhost,
    ));
    // tc304: outside a permitted `example.com`.
    refused(leaf_under(
        permitted(&[dns_base("example.com")]),
        &test_localhost,
    ));
    // tc253: inside an excluded `localhost`.
    refused(leaf_under(
        excluded(&[dns_base("localhost")]),
        &test_localhost,
    ));
    // tc256, tc1714: outside an excluded `bad.example.com`.
    accepted(leaf_under(
        excluded(&[dns_base("bad.example.com")]),
        &test_localhost,
    ));
    // tc280: excluded beats permitted.
    refused(leaf_under(
        nc(
            Some(&[dns_base("localhost")]),
            Some(&[dns_base("localhost")]),
        ),
        &test_localhost,
    ));
    // tc283: permitted `localhost`, excluded elsewhere.
    accepted(leaf_under(
        nc(
            Some(&[dns_base("localhost")]),
            Some(&[dns_base("bad.example.com")]),
        ),
        &test_localhost,
    ));
}

#[test]
fn bettertls_ip() {
    let dns = san_dns("test.localhost");
    let loopback = san_ip(&[127, 0, 0, 1]);
    // tc259, tc251: an iPAddress constraint leaves dNSName entries alone.
    accepted(leaf_under(
        permitted(&[ip24(LOOPBACK_24)]),
        std::slice::from_ref(&dns),
    ));
    accepted(leaf_under(
        excluded(&[ip24(LOOPBACK_24)]),
        std::slice::from_ref(&dns),
    ));
    let both = [dns.clone(), loopback.clone()];
    // tc340: inside a permitted /24.
    accepted(leaf_under(permitted(&[ip24(LOOPBACK_24)]), &both));
    // tc349: outside a permitted /24.
    refused(leaf_under(permitted(&[ip24(ONE_24)]), &both));
    // tc332, tc333: excluded range.
    refused(leaf_under(excluded(&[ip24(LOOPBACK_24)]), &both));
    accepted(leaf_under(excluded(&[ip24(ONE_24)]), &both));
    // tc358, tc4489: a dNSName constraint leaves the iPAddress alone.
    accepted(leaf_under(permitted(&[dns_base("localhost")]), &both));
    accepted(leaf_under(
        permitted(&[dns_base("localhost")]),
        std::slice::from_ref(&loopback),
    ));
    // tc359: every entry is checked.
    refused(leaf_under(
        nc(Some(&[dns_base("localhost")]), Some(&[ip24(LOOPBACK_24)])),
        &both,
    ));
}

#[test]
fn bettertls_other_forms_and_malformed_entries() {
    // tc8839: with no URI constraint a URI entry passes the name constraints
    // (the hostname check refuses it).
    let entries = [san_dns("bad.example.com"), san_uri("test.localhost")];
    accepted(leaf_under(permitted(&[dns_base("example.com")]), &entries));
    // With a URI constraint in force, the entry fails.
    refused(leaf_under(
        permitted(&[dns_base("example.com"), uri_base("example.com")]),
        &entries,
    ));
    // tc8785: `http://test.localhost` is no DNS name.
    refused(leaf_under(
        permitted(&[dns_base("example.com")]),
        &[san_dns("bad.example.com"), san_dns("http://test.localhost")],
    ));
}

// ---------------------------------------------------------------------------
// dNSName
// ---------------------------------------------------------------------------

#[test]
fn dns_within_matches_the_spec_examples() {
    assert!(dns_within(b"example.com", b"example.com"));
    assert!(dns_within(b"foo.bar.example.com", b"example.com"));
    // The label boundary.
    assert!(!dns_within(b"not-example.com", b"example.com"));
    // Case folding, both ways.
    assert!(dns_within(b"WWW.Example.COM", b"example.com"));
    assert!(dns_within(b"example.com", b"EXAMPLE.com"));
    // A shorter name, and an empty base.
    assert!(!dns_within(b"com", b"example.com"));
    assert!(dns_within(b"anything.test", b""));
    // Only `.` stands for the label boundary.
    assert!(!dns_within(b"fooxexample.com", b"example.com"));
}

#[test]
fn dns_label_boundary_and_case_through_a_path() {
    let base = permitted(&[dns_base("example.com")]);
    accepted(leaf_under(base.clone(), &[san_dns("foo.bar.example.com")]));
    refused(leaf_under(base.clone(), &[san_dns("not-example.com")]));
    // The entry `.example.com` is no DNS name, so it is refused even though
    // it ends with the permitted base.
    refused(leaf_under(
        base,
        &[san_dns(".example.com"), san_dns("foo.example.com")],
    ));
    // Every entry is checked, wherever it stands.
    let bad = excluded(&[dns_base("bad.example.com")]);
    refused(leaf_under(
        bad.clone(),
        &[san_dns("example.com"), san_dns("bad.example.com")],
    ));
    refused(leaf_under(
        bad,
        &[san_dns("bad.example.com"), san_dns("example.com")],
    ));
    refused(leaf_under(
        permitted(&[dns_base("localhost")]),
        &[san_dns("bad.example.com"), san_dns("test.localhost")],
    ));
}

#[test]
fn malformed_dns_bases_refuse_the_path() {
    // erratum 5997: a leading period; and a wildcard base.
    for base in [".example.com", "*.example.com", "example.com."] {
        refused(run(
            &[],
            &[
                ca(&[], permitted(&[dns_base(base)])),
                cert(&[san_dns("example.com")]),
            ],
        ));
    }
    // Neither field present.
    refused(run(
        &[],
        &[ca(&[], nc(None, None)), cert(&[san_dns("example.com")])],
    ));
}

#[test]
fn zero_length_dns_base_holds_every_name() {
    // BR §7.1.2.5.2: excluding the zero-length dNSName excludes every name.
    refused(leaf_under(
        excluded(&[dns_base("")]),
        &[san_dns("test.localhost")],
    ));
    accepted(leaf_under(
        permitted(&[dns_base("")]),
        &[san_dns("test.localhost")],
    ));
    // It does not touch other forms.
    accepted(leaf_under(
        excluded(&[dns_base("")]),
        &[san_ip(&[127, 0, 0, 1])],
    ));
}

// ---------------------------------------------------------------------------
// Wildcards
// ---------------------------------------------------------------------------

#[test]
fn wildcard_entries() {
    // cve-2025-61727: `*.example.com` stands for the excluded `bar.example.com`.
    refused(leaf_under(
        nc(
            Some(&[dns_base("example.com")]),
            Some(&[dns_base("bar.example.com")]),
        ),
        &[san_dns("*.example.com")],
    ));
    // ... and for names outside a permitted `foo.example.com`.
    refused(leaf_under(
        permitted(&[dns_base("foo.example.com")]),
        &[san_dns("*.example.com")],
    ));
    // webpki nc-permits-dns-san-pattern: within a permitted `example.com`.
    accepted(leaf_under(
        permitted(&[dns_base("example.com")]),
        &[san_dns("*.example.com")],
    ));
    // Directly.
    assert!(dns_wildcard_meets(b"example.com", b"bar.example.com"));
    assert!(dns_wildcard_meets(b"example.com", b"example.com"));
    assert!(!dns_wildcard_meets(b"example.com", b"bar.baz.example.com"));
    assert!(!dns_wildcard_meets(b"example.com", b"other.org"));
}

// ---------------------------------------------------------------------------
// iPAddress
// ---------------------------------------------------------------------------

#[test]
fn ip_within_is_masked_equality() {
    assert!(ip_within(
        &[192, 0, 2, 1],
        &[192, 0, 2, 0],
        &[255, 255, 255, 0]
    ));
    assert!(!ip_within(
        &[192, 0, 3, 1],
        &[192, 0, 2, 0],
        &[255, 255, 255, 0]
    ));
    // Bits of the base outside its mask are ignored.
    assert!(ip_within(
        &[192, 0, 2, 9],
        &[192, 0, 2, 77],
        &[255, 255, 255, 0]
    ));
    // Lengths must agree: IPv4 is never within an IPv6 base, and the reverse.
    assert!(!ip_within(&[127, 0, 0, 1], &[0; 16], &[0; 16]));
    assert!(!ip_within(&[0; 16], &[0; 4], &[0; 4]));
    // /0 holds every address of the length.
    assert!(ip_within(&[8, 8, 8, 8], &[0; 4], &[0; 4]));
    // A mismatched mask length.
    assert!(!ip_within(&[8, 8, 8, 8], &[0; 4], &[0; 3]));
}

#[test]
fn ipv6_host_range_and_zero_ranges() {
    let mut loopback = [0u8; 16];
    if let Some(last) = loopback.last_mut() {
        *last = 1;
    }
    let host = ip_base(&loopback, &[0xff; 16]);
    accepted(leaf_under(
        permitted(std::slice::from_ref(&host)),
        &[san_ip(&loopback)],
    ));
    refused(leaf_under(
        excluded(std::slice::from_ref(&host)),
        &[san_ip(&loopback)],
    ));
    // An IPv6-only permitted set permits no IPv4 address.
    accepted(leaf_under(
        permitted(&[ip_base(&[0; 16], &[0; 16])]),
        &[san_dns("example.com")],
    ));
    refused(leaf_under(
        permitted(&[ip_base(&[0; 16], &[0; 16])]),
        &[san_ip(&[127, 0, 0, 1])],
    ));
    // BR §7.1.2.5.2: excluded 0.0.0.0/0.
    refused(leaf_under(
        excluded(&[ip_base(&[0; 4], &[0; 4])]),
        &[san_ip(&[127, 0, 0, 1])],
    ));
}

#[test]
fn noncontiguous_masks_refuse_the_path() {
    let bad = ip_base(&[10, 0, 10, 0], &[255, 0, 255, 0]);
    refused(run(&[], &[ca(&[], excluded(&[bad])), cert(&[])]));
    let good = ip_base(&[10, 0, 16, 0], &[255, 255, 240, 0]);
    accepted(run(&[], &[ca(&[], excluded(&[good])), cert(&[])]));
}

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------

#[test]
fn excluded_directory_name_refuses_the_path() {
    let base = dn_base(&cn_foo());
    refused(run(
        &[],
        &[
            ca(&[], excluded(std::slice::from_ref(&base))),
            cert(&[san_dns("example.com")]),
        ],
    ));
    refused(run(
        &[],
        &[
            ca(
                &[],
                nc(
                    Some(&[dns_base("example.com")]),
                    Some(std::slice::from_ref(&base)),
                ),
            ),
            cert(&[san_dns("example.com")]),
        ],
    ));
    // In permittedSubtrees it is applied, not refused.
    accepted(run(
        &[],
        &[
            ca(&[], permitted(std::slice::from_ref(&base))),
            cert_with_subject(cn_foo(), &[]),
        ],
    ));
    // The final certificate's own extension is never processed.
    accepted(run(
        &[],
        &[ca(
            &[san_dns("example.com")],
            excluded(std::slice::from_ref(&base)),
        )],
    ));
}

#[test]
fn permitted_subtrees_intersect_and_excluded_accumulate() {
    let foo = dns_base("foo.example.com");
    let bar = dns_base("bar.example.com");
    // Widening is refused.
    refused(run(
        &[],
        &[
            ca(&[], permitted(std::slice::from_ref(&bar))),
            ca(&[], permitted(&[foo.clone(), bar.clone()])),
            cert(&[san_dns("foo.example.com")]),
        ],
    ));
    // Narrowing is refused.
    refused(run(
        &[],
        &[
            ca(&[], permitted(&[foo.clone(), bar.clone()])),
            ca(&[], permitted(std::slice::from_ref(&bar))),
            cert(&[san_dns("foo.example.com")]),
        ],
    ));
    // The name both allow passes.
    accepted(run(
        &[],
        &[
            ca(&[], permitted(&[foo, bar.clone()])),
            ca(&[], permitted(std::slice::from_ref(&bar))),
            cert(&[san_dns("bar.example.com")]),
        ],
    ));
    // Excluded subtrees accumulate.
    refused(run(
        &[],
        &[
            ca(&[], excluded(&[dns_base("bad.example.com")])),
            ca(&[], excluded(&[dns_base("localhost")])),
            cert(&[san_dns("bad.example.com")]),
        ],
    ));
}

#[test]
fn intermediates_and_self_issued_certificates_are_checked() {
    // An intermediate's own SAN is checked against the earlier constraints.
    refused(run(
        &[],
        &[
            ca(
                &[san_dns("example.com")],
                nc(
                    Some(&[dns_base("foo.example.com")]),
                    Some(&[dns_base("bad.example.com")]),
                ),
            ),
            cert(&[san_dns("bad.example.com")]),
            cert(&[san_dns("foo.example.com")]),
        ],
    ));
    // permitted-self-issued, the listed divergence: a self-issued
    // intermediate outside the anchor's permitted subtree is checked.
    let anchor = permitted(&[dns_base("example.com")]);
    refused(run(
        std::slice::from_ref(&anchor),
        &[
            cert(&[san_dns("not-example.com")]),
            cert(&[san_dns("example.com")]),
        ],
    ));
    // excluded-self-issued-leaf: a self-issued final certificate is checked.
    refused(run(
        std::slice::from_ref(&anchor),
        &[cert(&[]), cert(&[san_dns("not-example.com")])],
    ));
    accepted(run(
        std::slice::from_ref(&anchor),
        &[
            cert(&[san_dns("example.com")]),
            cert(&[san_dns("www.example.com")]),
        ],
    ));
}

// ---------------------------------------------------------------------------
// directoryName
// ---------------------------------------------------------------------------

#[test]
fn directory_names() {
    let anchor = permitted(&[dn_base(&cn_foo())]);
    let one = std::slice::from_ref(&anchor);
    // permitted-dn-match: the subject and a directoryName entry.
    accepted(run(
        one,
        &[cert_with_subject(cn_foo(), &[san_dn(&cn_foo())])],
    ));
    // permitted-dn-mismatch, as a subject and as an entry.
    let not_foo = name(&[rdn_cn(b"not-foo", UTF8)]);
    refused(run(one, &[cert_with_subject(not_foo.clone(), &[])]));
    refused(run(
        one,
        &[cert_with_subject(cn_foo(), &[san_dn(&not_foo)])],
    ));
    // permitted-dn-match-subject-san-mismatch: the subject is checked even
    // with a SAN present.
    refused(run(
        one,
        &[cert_with_subject(not_foo, &[san_dn(&cn_foo())])],
    ));
    // An empty subject fails a non-empty permitted base.
    refused(run(
        one,
        &[cert_with_subject(name(&[]), &[san_dns("example.com")])],
    ));
    // The attribute type matters.
    refused(run(
        one,
        &[cert_with_subject(name(&[rdn_o(b"foo", UTF8)]), &[])],
    ));
    // No case normalization.
    refused(run(
        one,
        &[cert_with_subject(name(&[rdn_cn(b"Foo", UTF8)]), &[])],
    ));
}

#[test]
fn directory_prefix_and_tag_relaxation() {
    let example = rdn_o(b"Example", UTF8);
    let foo = rdn_cn(b"foo", UTF8);
    let org = permitted(&[dn_base(&name(std::slice::from_ref(&example)))]);
    let one = std::slice::from_ref(&org);
    accepted(run(
        one,
        &[cert_with_subject(
            name(&[example.clone(), foo.clone()]),
            &[],
        )],
    ));
    refused(run(
        one,
        &[cert_with_subject(name(&[foo.clone(), example]), &[])],
    ));
    // An empty base holds every name.
    accepted(run(
        &[permitted(&[dn_base(&name(&[]))])],
        &[cert_with_subject(name(std::slice::from_ref(&foo)), &[])],
    ));
    // UTF8String and PrintableString are interchangeable, both ways.
    let printable_foo = name(&[rdn_cn(b"foo", PRINTABLE)]);
    accepted(run(
        &[permitted(&[dn_base(&cn_foo())])],
        &[cert_with_subject(printable_foo.clone(), &[])],
    ));
    accepted(run(
        &[permitted(&[dn_base(&printable_foo)])],
        &[cert_with_subject(cn_foo(), &[])],
    ));
    // Values Chrome cannot normalize never match, even byte for byte.
    let bmp = name(&[rdn_cn(&[0, b'f'], BMP)]);
    refused(run(
        &[permitted(&[dn_base(&bmp)])],
        &[cert_with_subject(bmp.clone(), &[])],
    ));
    let star = name(&[rdn_cn(b"*", PRINTABLE)]);
    refused(run(
        &[permitted(&[dn_base(&star)])],
        &[cert_with_subject(star.clone(), &[])],
    ));
    // A malformed directoryName base refuses the path.
    refused(run(
        &[],
        &[
            ca(&[], permitted(&[dn_base(&[0x30, 0x02, 0x31, 0x00])])),
            cert(&[]),
        ],
    ));
}

// ---------------------------------------------------------------------------
// rfc822Name
// ---------------------------------------------------------------------------

#[test]
fn rfc822_functions() {
    // A mailbox base, a host base and a domain base.
    assert!(rfc822_within(b"foo", b"example.com", b"foo@example.com"));
    assert!(!rfc822_within(b"bar", b"example.com", b"foo@example.com"));
    assert!(rfc822_within(b"foo", b"EXAMPLE.com", b"foo@example.com"));
    assert!(rfc822_within(b"foo", b"example.com", b"example.com"));
    assert!(!rfc822_within(b"foo", b"sub.example.com", b"example.com"));
    assert!(rfc822_within(b"foo", b"sub.example.com", b".example.com"));
    assert!(!rfc822_within(b"foo", b"example.com", b".example.com"));
    // The local part: byte for byte when permitted, folded when excluded.
    assert!(!rfc822_within(b"foo", b"example.com", b"Foo@example.com"));
    assert!(rfc822_meets(b"foo", b"example.com", b"Foo@example.com"));
}

#[test]
fn rfc822_through_a_path() {
    // nc-permits-email-exact / -domain / -domain-rejects-subdomain.
    accepted(leaf_under(
        permitted(&[email_base("foo@example.com")]),
        &[san_email("foo@example.com")],
    ));
    accepted(leaf_under(
        permitted(&[email_base("example.com")]),
        &[san_email("foo@example.com")],
    ));
    refused(leaf_under(
        permitted(&[email_base("example.com")]),
        &[san_email("foo@sub.example.com")],
    ));
    // nc-permits-email-subdomains-rejects-apex.
    accepted(leaf_under(
        permitted(&[email_base(".example.com")]),
        &[san_email("foo@sub.example.com")],
    ));
    refused(leaf_under(
        permitted(&[email_base(".example.com")]),
        &[san_email("foo@example.com")],
    ));
    // nc-permits-email-literal-*: every character is literal.
    accepted(leaf_under(
        permitted(&[email_base("*@example.com")]),
        &[san_email("*@example.com")],
    ));
    refused(leaf_under(
        permitted(&[email_base("*@example.com")]),
        &[san_email("user@example.com")],
    ));
    refused(leaf_under(
        permitted(&[email_base("**@example.com")]),
        &[san_email("*@example.com")],
    ));
    // Local-part case: permitted is exact, excluded folds.
    refused(leaf_under(
        permitted(&[email_base("Foo@example.com")]),
        &[san_email("foo@example.com")],
    ));
    refused(leaf_under(
        excluded(&[email_base("Foo@example.com")]),
        &[san_email("foo@example.com")],
    ));
    accepted(leaf_under(
        permitted(&[email_base("foo@EXAMPLE.com")]),
        &[san_email("foo@example.com")],
    ));
}

#[test]
fn rfc822_malformed_names_and_bases() {
    // invalid-email-address: a base that is no mailbox refuses the path.
    refused(run(
        &[],
        &[
            ca(&[], permitted(&[email_base("i@i@example.com")])),
            cert(&[]),
        ],
    ));
    // nc-permits-invalid-email-san: a malformed entry beside good ones.
    refused(leaf_under(
        permitted(&[email_base("example.com")]),
        &[san_email("g@example.com"), san_email("i@a@example.com")],
    ));
    // A local part with a leading dot is no mailbox.
    refused(leaf_under(
        permitted(&[email_base("example.com")]),
        &[san_email(".foo@example.com")],
    ));
}

#[test]
fn subject_email_address_is_refused_under_an_rfc822_constraint() {
    let subject = name(&[rdn(EMAIL_OID, b"foo@example.com", 0x16)]);
    refused(run(
        &[permitted(&[email_base("example.com")])],
        &[cert_with_subject(
            subject.clone(),
            &[san_email("foo@example.com")],
        )],
    ));
    // With only dNSName constraints it is ignored.
    accepted(run(
        &[permitted(&[dns_base("example.com")])],
        &[cert_with_subject(subject, &[san_dns("example.com")])],
    ));
}

// ---------------------------------------------------------------------------
// The other forms
// ---------------------------------------------------------------------------

#[test]
fn other_forms() {
    let constraints = nc(Some(&[dns_base("example.com")]), Some(&[other_name_base()]));
    // nc-forbids-othername: refused with an otherName entry ...
    refused(leaf_under(
        constraints.clone(),
        &[san_dns("example.com"), san_other_name()],
    ));
    // ... nc-forbids-othername-noop: and unaffected without one.
    accepted(leaf_under(constraints, &[san_dns("example.com")]));
    // nc-permits-uri-*: a URI constraint fails every URI entry.
    refused(leaf_under(
        permitted(&[uri_base("example.com")]),
        &[san_dns("example.com"), san_uri("test.localhost")],
    ));
}

// ---------------------------------------------------------------------------
// The comparison bound (design §1.12)
// ---------------------------------------------------------------------------

/// `count` dNSName subtrees, the first of which is `b0.example`.
fn many_subtrees(count: usize) -> Vec<Vec<u8>> {
    (0..count)
        .map(|index| dns_base(&format!("b{index}.example")))
        .collect()
}

/// `count` dNSName entries all within `b0.example`.
fn many_entries(count: usize) -> Vec<Vec<u8>> {
    (0..count)
        .map(|index| san_dns(&format!("n{index}.b0.example")))
        .collect()
}

#[test]
fn comparison_bound() {
    // (63 entries + the subject) x 64 subtrees = 4096: at the bound, accepted.
    accepted(leaf_under(permitted(&many_subtrees(64)), &many_entries(63)));
    // (64 + 1) x 64 = 4160: beyond it, refused although every name is permitted.
    refused(leaf_under(permitted(&many_subtrees(64)), &many_entries(64)));
    // The same entries under fewer subtrees are fine.
    accepted(leaf_under(permitted(&many_subtrees(63)), &many_entries(64)));
}

#[test]
fn comparison_bound_accumulates_over_the_path() {
    // The first certificate costs (1 + 31) x 65 = 2,080 comparisons; a
    // second of the same size makes 4,160, beyond the bound, and one of 30
    // entries makes 2,080 + 2,015 = 4,095, within it.
    let state = permitted(&many_subtrees(65));
    refused(run(
        std::slice::from_ref(&state),
        &[cert(&many_entries(31)), cert(&many_entries(31))],
    ));
    accepted(run(
        std::slice::from_ref(&state),
        &[cert(&many_entries(31)), cert(&many_entries(30))],
    ));
}

#[test]
fn comparison_bound_counts_every_set_in_the_state() {
    // The subtrees of every set are counted, permitted and excluded alike.
    let sets = [
        permitted(&many_subtrees(40)),
        excluded(&[dns_base("x1.test"), dns_base("x2.test")]),
        nc(Some(&many_subtrees(20)), Some(&[dns_base("y.test")])),
    ];
    // 40 + 2 + 21 = 63 subtrees: (1 + 64) x 63 = 4,095 is within the bound,
    // (1 + 65) x 63 = 4,158 is beyond.
    accepted(run(&sets, &[cert(&many_entries(64))]));
    refused(run(&sets, &[cert(&many_entries(65))]));
}

#[test]
fn an_empty_state_costs_nothing() {
    // 5,000 names, more than the 4,096-comparison bound if names alone
    // counted. Miri takes 100, which no longer tests the bound: 5,000 took
    // over 300 s there, and Miri looks for undefined behaviour, which the
    // same code paths show at 100. The normal test job runs all 5,000.
    let count = if cfg!(miri) { 100 } else { 5000 };
    accepted(run(&[], &[cert(&many_entries(count))]));
}
