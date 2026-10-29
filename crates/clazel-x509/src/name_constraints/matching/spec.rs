//! RFC 5280 name-constraint matching: the meaning of a dNSName, iPAddress,
//! rfc822Name or directoryName subtree (§4.2.1.10), the permitted_subtrees and excluded_subtrees state
//! (§6.1.2 (b), (c)), the per-certificate checks (§6.1.3 (b), (c)) and the
//! state update (§6.1.4 (g)).
//!
//! Sources, pinned:
//! - RFC 5280, May 2008, <https://www.rfc-editor.org/rfc/rfc5280.txt>,
//!   SHA-256 `a2f2628c0a83b873fc4786abd921f9b2c02395954b655d190bf16b831633345d`
//!   (downloaded 2026-10-29). §4.2.1.10, §6.1.2 (b) and (c), §6.1.3 (b) and
//!   (c), §6.1.4 (g).
//! - RFC 9549, March 2024 (updates RFC 5280; replaces its §7.2),
//!   <https://www.rfc-editor.org/rfc/rfc9549.txt>, SHA-256
//!   `28c505895b36bda33264cb7d12ea81a2c9fc8821982ca329f6a8c51e3d4bc0f4`.
//!   §2.3: "When evaluating name constraints, conforming implementations MUST
//!   perform a case-insensitive exact match on a label-by-label basis."
//! - RFC 5280 errata, <https://www.rfc-editor.org/errata/rfc5280>, as listed
//!   on 2026-10-29. Two touch the dNSName rule: 5997 (Held for Document
//!   Update), "For DNS names, restrictions MUST use the dNSName syntax in
//!   Section 4.2.1.6", which rules out a leading period; and 3693 (Rejected),
//!   which asked that DNS constraints also apply to names taken from the
//!   subject DN.
//! - CA/Browser Forum Baseline Requirements v2.3.1, 4 October 2026,
//!   `cabforum/servercert` commit `3574ae809e5f909b58ee4c26b7bac4a3b9e78421`,
//!   `docs/BR.md`, SHA-256
//!   `ee4e4e95ba0f3fa1e11cb0dc01b2337aa26e88b8c7724c78f25e5743fc1e151e`.
//!   §7.1.2.5.2 (zero-length dNSName and 0.0.0.0/0 exclude a whole name
//!   type), §7.1.2.7.12 (a subscriber SAN holds only dNSName and iPAddress),
//!   §7.1.2.10.8.
//! - x509-limbo commit `1080e565f26e544bbe9cf99953be8a57c08e7e20`, vendored in
//!   `tests/data/x509-limbo/` (`limbo.json` SHA-256 `611e337b…acd4de`). Its
//!   9,491 `bettertls::nameconstraints::tcN` testcases are the BetterTLS
//!   suite; `rfc5280::nc::*`, `webpki::nc::*` and `cve::*` cover what
//!   BetterTLS does not. Each rule below cites the id that fixes its edge.
//! - The path-validation design (`.claude/plans/path-validation.md`, not in
//!   the repository): §1.9, §3.4 and question Q12 as revised on 2026-10-29.
//! - PKCS #9 (RFC 2985) §5.2.1, the emailAddress attribute
//!   `1.2.840.113549.1.9.1`; RFC 5322 §3.2.3 (atext, dot-atom-text); ITU-T
//!   X.680 (02/2021) §41.4, the PrintableString characters.
//!
//! - Browser behaviour, the profile this module follows (design Q12, revised
//!   2026-10-29: "do what Chrome and Firefox do"). Chrome: BoringSSL
//!   `pki/name_constraints.cc`, `pki/verify_name_match.cc` and
//!   `pki/verify_certificate_chain.cc`; Firefox: NSS `lib/mozpkix/lib/pkixnames.cpp`,
//!   both at their `main`/`master` heads read on 2026-10-29. A path is accepted
//!   only where both browsers accept it; where they differ this follows the
//!   stricter. Each remaining difference from either browser is a refusal,
//!   marked **(R)** and named with the browser it differs from. Nothing here
//!   accepts what either browser refuses.
//!
//! Modelling choices. Every place where this refuses more than RFC 5280
//! requires, or more than a browser does, is marked **(R)**.
//! - The forms matched are dNSName, iPAddress, rfc822Name and directoryName,
//!   the four Chrome supports (`kSupportedNameTypes`); Firefox matches them
//!   too. The state holds the decoded `NameConstraints` values of the path in
//!   order, and its denotation is the RFC's: a name is within
//!   permitted_subtrees iff, for every set whose permittedSubtrees has a base
//!   of the name's type, it is within one of those bases; it is within
//!   excluded_subtrees iff it meets any excluded base of its type. §6.1.4
//!   (g)(1) intersects one set at a time and leaves a type unchanged when the
//!   set has no base of it; (g)(2) unions. Keeping the sets instead of
//!   computing the intersection is the same set of names
//!   (`lemma_permitted_is_intersection`, `lemma_excluded_is_union`), and it
//!   never has to compute the intersection of two subtrees, which the RFC
//!   only illustrates. Both browsers check each extension's sets separately,
//!   which is the same denotation.
//! - **Within and meets.** A permitted subtree must hold the name (`within`);
//!   an excluded one need only meet it (`meets`). For every form, `within` is
//!   at most what both browsers call a match, and `meets` at least what either
//!   does, so a permitted check never passes a name a browser fails and an
//!   excluded check never misses a name a browser excludes.
//! - **The other forms** (otherName, x400Address, ediPartyName, URI,
//!   registeredID; the decoder's `Unsupported`). A constraint of such a form
//!   does not refuse the path by itself and has no subtree meaning. A
//!   subjectAltName entry of such a form fails §6.1.3 (b) and (c) iff some
//!   set in the state has a base of the same form, in either list. That is
//!   Firefox's rule. **(R) against Chrome:** Chrome counts such a form as
//!   constrained only when the extension is critical; this ignores
//!   criticality (`rfc5280::nc::nc-forbids-othername` fails,
//!   `rfc5280::nc::nc-forbids-othername-noop` passes,
//!   `rfc5280::nc::nc-permits-uri-host-rejects-subdomain` and
//!   `-uri-subdomains-rejects-apex` fail). RFC 5280 asks that such a
//!   constraint be processed or the certificate rejected when a name of that
//!   form appears; this rejects.
//! - **Entries of an unconstrained form are unconstrained** (§4.2.1.10
//!   "Restrictions apply only when the specified name form is present"; both
//!   browsers). **(R) malformed entries:** once at least one NameConstraints
//!   extension is in the state, a subjectAltName entry of a matched form that
//!   is malformed fails, whatever forms are constrained: a dNSName that is
//!   neither in preferred name syntax (`crate::spec::dns_name_shape`) nor
//!   `*.` followed by one, an iPAddress that is not 4 or 16 octets, an
//!   rfc822Name that is not a mailbox as defined below, and a directoryName
//!   that is not one Name. RFC 5280 leaves malformed names undefined, and the
//!   browsers check most of them only under a constraint of the same form;
//!   refusing them under any constraint is never more permissive. Fixed by
//!   `rfc5280::nc::nc-permits-invalid-dns-san` (a SAN `.example.com` under a
//!   permitted `example.com` must fail) and
//!   `rfc5280::nc::nc-permits-invalid-email-san`. With an empty state nothing
//!   is checked, as the RFC's initial state permits every name. BetterTLS's
//!   mixed-form SANs (`tc6`, `tc8755` to `tc8976`) expect FAILURE; every one
//!   of them fails on its hostname, not here.
//! - **(R) Malformed bases.** A dNSName base must be empty or in preferred
//!   name syntax, so a leading period (`rfc5280::nc::invalid-dnsname-leading-period`,
//!   erratum 5997), a wildcard (`rfc5280::nc::invalid-dnsname-wildcard`) or a
//!   trailing dot refuses the path. An iPAddress base must have a
//!   contiguous mask (leading ones, then zeros), as RFC 4632 CIDR, which
//!   §4.2.1.10 names, implies; a non-contiguous mask refuses the path. No
//!   limbo case has one. An rfc822Name base must be a mailbox, a host in
//!   preferred name syntax, or `.` followed by one
//!   (`rfc5280::nc::invalid-email-address`: `invalid@invalid@example.com`).
//!   Chrome treats a malformed rfc822Name base as matching nothing when
//!   permitted and everything when excluded; Firefox errors when it is
//!   compared. A directoryName base must be one Name that this crate's Name
//!   decoder accepts. A NameConstraints with both fields absent refuses the
//!   path: §4.2.1.10 "either the permittedSubtrees field or the
//!   excludedSubtrees MUST be present" (`webpki::nc::intermediate-permitted-excluded-subtrees-both-null`).
//!   The decoder already refuses empty `GeneralSubtrees` and an encoded
//!   minimum or maximum.
//! - An empty dNSName base (BR §7.1.2.5.2's "zero-length dNSName", accepted
//!   by both browsers and by the decoder) contains every DNS name, read as
//!   "adding zero or more labels" to the empty name (design §3.4).
//! - DNS labels compare by ASCII case folding (`crate::spec::ascii_fold`,
//!   A to Z only), per RFC 9549 §2.3. A-labels (`xn--`) are compared as
//!   ASCII and never converted. No limbo case varies case or uses A-labels.
//! - Wildcard SANs. RFC 5280 is silent; RFC 9525 §6.3 says `*.S` stands for
//!   every name of one label followed by S. Permitted asks that every name
//!   it stands for be within the base: S within the base. Excluded asks
//!   whether any name it stands for meets the base: S within the base, or
//!   the base is one label followed by S. Fixed by `cve::cve-2025-61727`,
//!   `cve::cve-2025-61727-nc-permits-variant` and
//!   `webpki::nc::nc-permits-dns-san-pattern`.
//! - iPAddress containment is "address AND mask equals base AND mask",
//!   octet by octet, with equal lengths (design §1.9). An IPv4 address is
//!   never within an IPv6 base or the reverse, and an IPv4-mapped IPv6
//!   address is not special. A base whose address has bits set outside its
//!   mask is not refused; the AND ignores them. IPv4 and IPv6 are one name
//!   type, iPAddress, so a set that permits only IPv4 ranges permits no
//!   IPv6 address.
//! - **rfc822Name** (§4.2.1.10: a constraint "MAY specify a particular
//!   mailbox, all addresses at a particular host, or all mailboxes in a
//!   domain"). A presented rfc822Name is a mailbox `local@host`: exactly one
//!   `@`, a local part that is RFC 5322 §3.2.3 dot-atom-text (atext, the
//!   characters Chrome's `IsAllowedRfc822LocalPart` lists, and single inner
//!   dots), and a host in preferred name syntax. Quoted local parts and
//!   address literals are malformed **(R)** (Chrome refuses them too;
//!   Firefox's `IsValidRFC822Name` admits no quoted string). A base with an
//!   `@` is a mailbox; a base starting with `.` is a domain, holding the
//!   mailboxes at any host with one or more labels added (not the host
//!   itself: `rfc5280::nc::nc-permits-email-subdomains-rejects-apex`); any
//!   other base is a host, holding the mailboxes at exactly that host
//!   (`nc-permits-email-domain`, `nc-permits-email-domain-rejects-subdomain`).
//!   Hosts compare by ASCII case folding in both browsers. Local parts:
//!   Chrome compares them case-sensitively in a permitted subtree, Firefox
//!   case-insensitively. `within` compares them byte for byte and `meets`
//!   with ASCII case folding, so a permitted mailbox `Foo@example.com` does
//!   not hold `foo@example.com` **(R) against Firefox**, and an excluded one
//!   catches it, as Firefox's does. Every character is literal, `*`
//!   included (`nc-permits-email-literal-*`, `nc-permits-email-exact`).
//! - **directoryName** (§4.2.1.10, §7.1). A presented directory name is
//!   matched within a permitted base when the base's RDNs are a prefix of the
//!   name's (Firefox: "the constraint RDNs just need to be a prefix of the
//!   presented RDNs"; Chrome: `VerifyNameInSubtree`), and each base RDN
//!   matches the name's RDN at the same index: the same number of attributes,
//!   and attribute k of one matching attribute k of the other. Two
//!   attributes match when their types are equal, their value contents are
//!   equal byte for byte, their value tags are equal or are UTF8String and
//!   PrintableString in either order (Firefox's relaxation, both
//!   directions), and each value is one Chrome can normalize: a
//!   PrintableString of X.680 §41.4 PrintableString characters (Chrome's
//!   `ENFORCE_PRINTABLE_STRING`), an IA5String of ASCII (`ENFORCE_ASCII`),
//!   and never a BMPString or UniversalString **(R)**. UTF8String values are
//!   compared as bytes, as both browsers do after Chrome's normalization,
//!   which a byte-equal pair always survives. Everything this accepts both
//!   browsers accept. **(R) against Chrome:** names equal only after Chrome's
//!   normalization (ASCII case folding, collapsed whitespace, BMPString or
//!   UniversalString values, the attributes of a multi-valued RDN in another
//!   order) do not match. An empty base holds every name
//!   (`rfc5280::nc::permitted-dn-match` passes,
//!   `rfc5280::nc::permitted-dn-mismatch` fails).
//! - **(R) Excluded directoryName.** Any directoryName base in
//!   excludedSubtrees refuses the path at §6.1.4 (g)
//!   (`rfc5280::nc::excluded-dn-match`, `excluded-dn-match-sub-mismatch`).
//!   Firefox errors on any non-empty excluded directoryName and, since it
//!   always checks the subject, refuses every such path; it lets an empty
//!   excluded base through for an empty name, and Chrome matches excluded
//!   names after normalization. This refuses all of them.
//! - **The subject field.** The subject DN of every checked certificate is a
//!   directory name, checked against directoryName constraints even when a
//!   subjectAltName is present and even when it is empty (Firefox; an empty
//!   subject fails a non-empty permitted base). **(R) against Chrome**, which
//!   skips an empty subject when a subjectAltName is present
//!   (`rfc5280::nc::permitted-dn-match-subject-san-mismatch` fails). Under
//!   any constraint, a subject the Name decoder refuses fails **(R)**.
//!   **(R) emailAddress:** when any set in the state has an rfc822Name base,
//!   in either list, a checked certificate whose subject has an emailAddress
//!   attribute (PKCS #9, `1.2.840.113549.1.9.1`) fails. Both browsers check
//!   emailAddress values against rfc822Name constraints only when there is
//!   no subjectAltName, and accept those that match; this refuses them all.
//! - **The subject CN is never a DNS name here.** The verifier never uses
//!   CN as an identity, and RFC 5280 does not constrain it (erratum 3693 was
//!   rejected). BetterTLS agrees: `tc1714` expects SUCCESS with CN
//!   `bad.example.com` under an excluded `bad.example.com`. Firefox checks
//!   an end-entity's CN (and emailAddress) against constraints when it has no
//!   subjectAltName; such a certificate has no identity for this verifier, so
//!   the hostname check refuses it before acceptance.
//! - **(R) Self-issued intermediates are checked.** RFC 5280 §6.1.3 (b) and
//!   (c) end "If certificate i is self-issued and it is not the final
//!   certificate in the path, skip this step for certificate i", and Chrome
//!   skips them (`verify_certificate_chain.cc`:
//!   `!IsSelfIssued(cert) || is_target_cert`). Firefox's
//!   `CheckNameConstraints` checks every certificate below the constrained
//!   one and skips none. This follows Firefox, the stricter: every
//!   certificate's names are checked, so a self-issued intermediate whose own
//!   names violate a constraint refuses the path. That makes
//!   `rfc5280::nc::permitted-self-issued` (SUCCESS in limbo) a listed
//!   divergence; `rfc5280::nc::excluded-self-issued-leaf` (FAILURE) still
//!   fails. Since nothing else here depends on it, whether a certificate is
//!   self-issued is not an input.
//! - Certificates are indexed from 0 here; the RFC numbers them 1 to n. The
//!   last element is the RFC's certificate n.
//!   The initial state is empty: §6.1.1 (h) and (i) with every name
//!   permitted and none excluded. A trust anchor's own constraints, if the
//!   path validator uses them, enter through `prepare_name_constraints`.
//! - Not here: refusing a NameConstraints extension in the final
//!   certificate (§4.2.1.10 "MUST be used only in a CA certificate",
//!   `rfc5280::nc::not-allowed-in-ee-critical`) and its criticality are the
//!   path specification's; this module never processes the final
//!   certificate's extension, as §6.1.4 does not. The bound on comparisons
//!   (design §1.12, `pathological::nc-dos-*`) belongs to the executable code.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Names this module matches
// ---------------------------------------------------------------------------

/// A subjectAltName entry of a form this module matches.
pub enum ConstrainedName {
    /// A dNSName in preferred name syntax.
    Dns(Seq<u8>),
    /// A wildcard dNSName `*.suffix`; the field is `suffix`.
    DnsWildcard(Seq<u8>),
    /// An iPAddress of 4 or 16 octets.
    Ip(Seq<u8>),
    /// An rfc822Name mailbox `local@host`.
    Rfc822 {
        /// The local part, before the `@`.
        local: Seq<u8>,
        /// The host, after the `@`, in preferred name syntax.
        host: Seq<u8>,
    },
    /// A directory name: a subject field or a directoryName entry, as the
    /// RDNs this crate's Name decoder produced.
    Directory(Seq<crate::name::spec::RelativeDistinguishedName>),
}

/// A presented `*.` followed by a name in preferred name syntax. Only the
/// whole left-most label may be `*` (RFC 9525 §6.3); `dns_name_shape` admits
/// no `*`, so there is no other one.
pub open spec fn is_wildcard_dns_name(name: Seq<u8>) -> bool {
    name.len() > 2 && name[0] == b'*' && name[1] == b'.'
        && crate::spec::dns_name_shape(name.subrange(2, name.len() as int))
}

/// The contents of a complete GeneralName TLV kept whole by the
/// subjectAltName decoder (`GeneralName::Other`).
pub open spec fn general_name_contents(der: Seq<u8>) -> Option<Seq<u8>> {
    match clazel_der::spec::read_tlv(der, 0, der.len()) {
        Some(tlv) if tlv.cend == der.len() => Some(der.subrange(tlv.cstart as int, tlv.cend as int)),
        _ => None,
    }
}

/// The matched form of a subjectAltName entry, or `None` for an entry of
/// another GeneralName form or a malformed one: a dNSName that is neither a
/// name nor a wildcard, an rfc822Name that is not a mailbox, a
/// directoryName that is not one Name.
pub open spec fn constrained_name(entry: crate::extensions::spec::GeneralName) -> Option<ConstrainedName> {
    match entry {
        crate::extensions::spec::GeneralName::DnsName(name) =>
            if crate::spec::dns_name_shape(name) {
                Some(ConstrainedName::Dns(name))
            } else if is_wildcard_dns_name(name) {
                Some(ConstrainedName::DnsWildcard(name.subrange(2, name.len() as int)))
            } else {
                None
            },
        crate::extensions::spec::GeneralName::IpAddress(address) =>
            if address.len() == 4 || address.len() == 16 {
                Some(ConstrainedName::Ip(address))
            } else {
                None
            },
        crate::extensions::spec::GeneralName::Other(tag, der) =>
            if tag == 1 {
                match general_name_contents(der) {
                    Some(mailbox) => if is_mailbox(mailbox) {
                        Some(ConstrainedName::Rfc822 { local: mailbox_local(mailbox), host: mailbox_host(mailbox) })
                    } else {
                        None
                    },
                    None => None,
                }
            } else if tag == 4 {
                // [4] EXPLICIT Name: the contents are one Name TLV.
                match general_name_contents(der) {
                    Some(name) => match crate::name::spec::parse_name(name) {
                        Some(parsed) => Some(ConstrainedName::Directory(parsed.rdns)),
                        None => None,
                    },
                    None => None,
                }
            } else {
                None
            },
    }
}

/// otherName [0], x400Address [3], ediPartyName [5],
/// uniformResourceIdentifier [6] and registeredID [8]: the GeneralName forms
/// this module gives no subtree meaning.
pub open spec fn is_uninterpreted_form(tag: u32) -> bool {
    tag == 0 || tag == 3 || tag == 5 || tag == 6 || tag == 8
}

/// A subjectAltName entry is well formed: of a matched form and well formed
/// for it, or of an uninterpreted form (which this module never parses).
pub open spec fn entry_well_formed(entry: crate::extensions::spec::GeneralName) -> bool {
    constrained_name(entry) is Some || match entry {
        crate::extensions::spec::GeneralName::Other(tag, _) => is_uninterpreted_form(tag),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// §4.2.1.10: the subtree a base stands for
// ---------------------------------------------------------------------------

/// §4.2.1.10: "DNS name restrictions are expressed as host.example.com. Any
/// DNS name that can be constructed by simply adding zero or more labels to
/// the left-hand side of the name satisfies the name constraint. For
/// example, www.host.example.com would satisfy the constraint but
/// host1.example.com would not." Labels compare case-insensitively (RFC 9549
/// §2.3). For a `name` in preferred name syntax, clause 3 is exactly "one or
/// more labels added" (`lemma_dns_within_adding_labels`).
pub open spec fn dns_within(name: Seq<u8>, base: Seq<u8>) -> bool {
    // 1. An empty base: adding labels to the empty name gives every name
    //    (BR §7.1.2.5.2's zero-length dNSName). Unreachable from DER today.
    if base.len() == 0 {
        true
    // 2. Zero labels added: the name is the base, ignoring ASCII case
    //    (`rfc5280::nc::permitted-dns-match`, BetterTLS `tc280`).
    } else if name.len() == base.len() {
        crate::spec::folded_equal_from(name, base, 0)
    // 3. One or more labels added: the name ends in "." and then the base.
    //    The dot keeps the label boundary: `not-example.com` is not within
    //    `example.com` (`rfc5280::nc::permitted-dns-mismatch`), and
    //    `test.localhost` is within `localhost` (BetterTLS `tc1`).
    } else if name.len() > base.len() {
        name[name.len() - base.len() - 1] == b'.'
            && crate::spec::folded_equal_from(name.subrange(name.len() - base.len(), name.len() as int), base, 0)
    // 4. A shorter name never results from adding labels.
    } else {
        false
    }
}

/// Every name `*.suffix` stands for is within `base`, which holds iff
/// `suffix` is (`lemma_wildcard_within_sound`). Permitted subtrees use this:
/// `*.example.com` is within `example.com`
/// (`webpki::nc::nc-permits-dns-san-pattern`) but not within
/// `foo.example.com` (`cve::cve-2025-61727-nc-permits-variant`).
pub open spec fn dns_wildcard_within(suffix: Seq<u8>, base: Seq<u8>) -> bool {
    dns_within(suffix, base)
}

/// Some name `*.suffix` stands for is within `base`: `suffix` is, or the
/// base is one label followed by `suffix` (`lemma_wildcard_meets_complete`).
/// Excluded subtrees use this: `*.example.com` meets an excluded
/// `bar.example.com` (`cve::cve-2025-61727`,
/// `rfc5280::nc::nc-forbids-dnsname-wildcard-san`).
pub open spec fn dns_wildcard_meets(suffix: Seq<u8>, base: Seq<u8>) -> bool {
    dns_within(suffix, base) || {
        let dot = crate::spec::first_dot(base, 0);
        dot < base.len() && crate::spec::folded_equal_from(base.subrange(dot + 1, base.len() as int), suffix, 0)
    }
}

/// `address[i] AND mask[i] == base[i] AND mask[i]` for every octet from `i`.
pub open spec fn ip_masked_equal_from(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>, i: int) -> bool
    recommends address.len() == base.len() && base.len() == mask.len() && 0 <= i
    decreases address.len() - i
{
    if i >= address.len() {
        true
    } else {
        address[i] & mask[i] == base[i] & mask[i] && ip_masked_equal_from(address, base, mask, i + 1)
    }
}

/// §4.2.1.10: an iPAddress base is an address and a mask "encoded in the
/// style of RFC 4632 (CIDR) to represent an address range". An address is
/// in the range iff it has the base's length and agrees with the base on
/// every bit the mask sets (design §1.9). `192.0.2.0/24` holds `192.0.2.1`
/// (`rfc5280::nc::permitted-ipv4-match`, BetterTLS `tc340`); `::1/128` holds
/// only `::1` (`rfc5280::nc::permitted-ipv6-match`).
pub open spec fn ip_within(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>) -> bool {
    address.len() == base.len() && base.len() == mask.len()
        && ip_masked_equal_from(address, base, mask, 0)
}

// ---------------------------------------------------------------------------
// §4.2.1.10: rfc822Name subtrees
// ---------------------------------------------------------------------------

/// RFC 5322 §3.2.3 atext: `ALPHA / DIGIT / "!" / "#" / "$" / "%" / "&" /
/// "'" / "*" / "+" / "-" / "/" / "=" / "?" / "^" / "_" / "`" / "{" / "|" /
/// "}" / "~"`. The same list as Chrome's `IsAllowedRfc822LocalPart`, less
/// its `.`.
pub open spec fn is_atext(b: u8) -> bool {
    b >= b'a' && b <= b'z' || b >= b'A' && b <= b'Z' || b >= b'0' && b <= b'9'
        || b == b'!' || b == b'#' || b == b'$' || b == b'%' || b == b'&' || b == b'\''
        || b == b'*' || b == b'+' || b == b'-' || b == b'/' || b == b'=' || b == b'?'
        || b == b'^' || b == b'_' || b == b'`' || b == b'{' || b == b'|' || b == b'}'
        || b == b'~'
}

/// RFC 5322 §3.2.3 `dot-atom-text = 1*atext *("." 1*atext)`, from byte `i`
/// on: no leading, trailing or doubled dot.
pub open spec fn dot_atom_text_from(local: Seq<u8>, i: int) -> bool
    recommends 0 <= i <= local.len()
    decreases local.len() - i
{
    if i >= local.len() {
        false
    } else if local[i] == b'.' {
        i > 0 && i + 1 < local.len() && local[i + 1] != b'.' && dot_atom_text_from(local, i + 1)
    } else {
        is_atext(local[i]) && (i + 1 == local.len() || dot_atom_text_from(local, i + 1))
    }
}

/// The first `@` at or after `i`, or `m.len()` if there is none.
pub open spec fn first_at(m: Seq<u8>, i: int) -> int
    recommends 0 <= i <= m.len()
    decreases m.len() - i
{
    if i >= m.len() { m.len() as int } else if m[i] == b'@' { i } else { first_at(m, i + 1) }
}

/// The local part of `local@host`: the bytes before the first `@`.
pub open spec fn mailbox_local(m: Seq<u8>) -> Seq<u8> {
    m.subrange(0, first_at(m, 0))
}

/// The host of `local@host`: the bytes after the first `@`.
pub open spec fn mailbox_host(m: Seq<u8>) -> Seq<u8> {
    m.subrange(first_at(m, 0) + 1, m.len() as int)
}

/// A mailbox `local@host`: an `@`, a dot-atom-text local part before it and
/// a host in preferred name syntax after it. Preferred name syntax has no
/// `@`, so there is exactly one.
pub open spec fn is_mailbox(m: Seq<u8>) -> bool {
    first_at(m, 0) < m.len()
        && dot_atom_text_from(mailbox_local(m), 0)
        && crate::spec::dns_name_shape(mailbox_host(m))
}

/// The three rfc822Name base shapes of §4.2.1.10: a mailbox (it has an
/// `@`), a domain (`.` and a host), or a host.
pub open spec fn rfc822_base_shape(base: Seq<u8>) -> bool {
    if first_at(base, 0) < base.len() {
        is_mailbox(base)
    } else if base.len() > 0 && base[0] == b'.' {
        crate::spec::dns_name_shape(base.subrange(1, base.len() as int))
    } else {
        crate::spec::dns_name_shape(base)
    }
}

/// The host part of §4.2.1.10's rfc822Name rule for a base without `@`:
/// "To indicate all Internet mail addresses on a particular host, specify
/// the host name"; "To specify any address within a domain, specify the
/// domain with a preceding period" (".example.com" covers the domain's
/// hosts "but not Internet mail addresses on the host 'example.com'").
/// Hosts compare by ASCII case folding (both browsers).
pub open spec fn rfc822_host_within(host: Seq<u8>, base: Seq<u8>) -> bool {
    // 2. A domain: one or more labels added, ending in ".domain".
    if base.len() > 0 && base[0] == b'.' {
        host.len() > base.len()
            && crate::spec::folded_equal_from(host.subrange(host.len() - base.len(), host.len() as int), base, 0)
    // 1. A host: exactly that host (`nc-permits-email-domain-rejects-subdomain`).
    } else {
        crate::spec::folded_equal_from(host, base, 0)
    }
}

/// §4.2.1.10: "a particular mailbox" when the base has an `@`; otherwise
/// the host rule. A permitted mailbox holds the same local part byte for
/// byte (Chrome's case-sensitive local part; stricter than Firefox).
pub open spec fn rfc822_within(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>) -> bool {
    if first_at(base, 0) < base.len() {
        local =~= mailbox_local(base)
            && crate::spec::folded_equal_from(host, mailbox_host(base), 0)
    } else {
        rfc822_host_within(host, base)
    }
}

/// As `rfc822_within`, but an excluded mailbox catches the local part
/// ignoring ASCII case (Firefox's comparison; wider than Chrome's).
pub open spec fn rfc822_meets(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>) -> bool {
    if first_at(base, 0) < base.len() {
        crate::spec::folded_equal_from(local, mailbox_local(base), 0)
            && crate::spec::folded_equal_from(host, mailbox_host(base), 0)
    } else {
        rfc822_host_within(host, base)
    }
}

// ---------------------------------------------------------------------------
// §4.2.1.10: directoryName subtrees
// ---------------------------------------------------------------------------

/// The universal, primitive tag `number` (UTF8String 12, PrintableString 19,
/// IA5String 22, UniversalString 28, BMPString 30).
pub open spec fn string_tag(number: u32) -> clazel_der::spec::Tag {
    clazel_der::spec::universal_primitive(number)
}

/// UTF8String or PrintableString.
pub open spec fn is_utf8_or_printable(tag: clazel_der::spec::Tag) -> bool {
    tag == string_tag(12) || tag == string_tag(19)
}

/// Firefox's tag rule for permitted directoryName attributes: equal tags, or
/// UTF8String and PrintableString in either order.
pub open spec fn value_tags_compatible(a: clazel_der::spec::Tag, b: clazel_der::spec::Tag) -> bool {
    a == b || (is_utf8_or_printable(a) && is_utf8_or_printable(b))
}

/// The contents of an attribute's value TLV.
pub open spec fn value_contents(value_der: Seq<u8>) -> Seq<u8> {
    match clazel_der::spec::read_tlv(value_der, 0, value_der.len()) {
        Some(tlv) => value_der.subrange(tlv.cstart as int, tlv.cend as int),
        None => value_der,
    }
}

/// X.680 §41.4 PrintableString characters: letters, digits, space and
/// `'()+,-./:=?`. Chrome's `ENFORCE_PRINTABLE_STRING` admits exactly these.
pub open spec fn is_printable_char(b: u8) -> bool {
    b >= b'a' && b <= b'z' || b >= b'A' && b <= b'Z' || b >= b'0' && b <= b'9'
        || b == b' ' || b == b'\'' || b == b'(' || b == b')' || b == b'+' || b == b','
        || b == b'-' || b == b'.' || b == b'/' || b == b':' || b == b'=' || b == b'?'
}

/// Every byte from `i` on is a PrintableString character.
pub open spec fn printable_from(s: Seq<u8>, i: int) -> bool
    recommends 0 <= i
    decreases s.len() - i
{
    i >= s.len() || (is_printable_char(s[i]) && printable_from(s, i + 1))
}

/// A value Chrome's `NormalizeValue` accepts, or one it compares as bytes:
/// a PrintableString of PrintableString characters, an IA5String of ASCII;
/// never a UniversalString or BMPString (R); any other value.
pub open spec fn value_comparable(attribute: crate::name::spec::AttributeTypeAndValue) -> bool {
    let contents = value_contents(attribute.value_der);
    if attribute.value_tag == string_tag(19) {
        printable_from(contents, 0)
    } else if attribute.value_tag == string_tag(22) {
        crate::extensions::spec::ia5_bytes(contents, 0)
    } else {
        attribute.value_tag != string_tag(28) && attribute.value_tag != string_tag(30)
    }
}

/// Two attributes match: equal types, equal value contents, compatible
/// tags, and values both browsers compare this way.
pub open spec fn attribute_match(
    base: crate::name::spec::AttributeTypeAndValue,
    name: crate::name::spec::AttributeTypeAndValue,
) -> bool {
    &&& base.oid =~= name.oid
    &&& value_tags_compatible(base.value_tag, name.value_tag)
    &&& value_contents(base.value_der) =~= value_contents(name.value_der)
    &&& value_comparable(base)
    &&& value_comparable(name)
}

/// Attribute k of `base` matches attribute k of `name`, for every k, and
/// there are as many of each (Firefox: "The AVAs have to be fully equal").
pub open spec fn attributes_match(
    base: Seq<crate::name::spec::AttributeTypeAndValue>,
    name: Seq<crate::name::spec::AttributeTypeAndValue>,
) -> bool
    decreases base.len()
{
    base.len() == name.len() && (base.len() == 0
        || (attribute_match(base.last(), name.last()) && attributes_match(base.drop_last(), name.drop_last())))
}

/// RDN k of `base` matches RDN k of `name`, for every k, and there are as
/// many of each.
pub open spec fn rdns_match(
    base: Seq<crate::name::spec::RelativeDistinguishedName>,
    name: Seq<crate::name::spec::RelativeDistinguishedName>,
) -> bool
    decreases base.len()
{
    base.len() == name.len() && (base.len() == 0
        || (attributes_match(base.last().attributes, name.last().attributes)
            && rdns_match(base.drop_last(), name.drop_last())))
}

/// A directory name is within a directoryName subtree when the subtree's
/// RDNs match the name's leading RDNs (§7.1 applied to a prefix; Firefox
/// "the constraint RDNs just need to be a prefix of the presented RDNs").
/// An empty base holds every name.
pub open spec fn directory_within(
    name: Seq<crate::name::spec::RelativeDistinguishedName>,
    base: Seq<crate::name::spec::RelativeDistinguishedName>,
) -> bool {
    base.len() <= name.len() && rdns_match(base, name.subrange(0, base.len() as int))
}

/// A directoryName base's RDNs, if it is one Name that the crate's Name
/// decoder accepts.
pub open spec fn directory_base(base: Seq<u8>) -> Option<Seq<crate::name::spec::RelativeDistinguishedName>> {
    match crate::name::spec::parse_name(base) {
        Some(parsed) => Some(parsed.rdns),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Every form
// ---------------------------------------------------------------------------

/// The name types of §6.1.4 (g): a dNSName base constrains DNS names and
/// wildcards, an iPAddress base constrains addresses (BetterTLS `tc259`:
/// an iPAddress-only permittedSubtrees leaves DNS names alone), an
/// rfc822Name base mailboxes and a directoryName base directory names.
pub open spec fn same_name_type(name: ConstrainedName, base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match (name, base) {
        (ConstrainedName::Dns(_), crate::name_constraints::spec::GeneralNameConstraint::DnsName(_)) => true,
        (ConstrainedName::DnsWildcard(_), crate::name_constraints::spec::GeneralNameConstraint::DnsName(_)) => true,
        (ConstrainedName::Ip(_), crate::name_constraints::spec::GeneralNameConstraint::IpAddress { .. }) => true,
        (ConstrainedName::Rfc822 { .. }, crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(_)) => true,
        (ConstrainedName::Directory(_), crate::name_constraints::spec::GeneralNameConstraint::DirectoryName(_)) => true,
        _ => false,
    }
}

/// The denotation of a subtree: `name` is within the subtree `base`. For a
/// wildcard, every name it stands for is. Never true across name types.
pub open spec fn within(name: ConstrainedName, base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match (name, base) {
        (ConstrainedName::Dns(n), crate::name_constraints::spec::GeneralNameConstraint::DnsName(b)) => dns_within(n, b),
        (ConstrainedName::DnsWildcard(s), crate::name_constraints::spec::GeneralNameConstraint::DnsName(b)) =>
            dns_wildcard_within(s, b),
        (ConstrainedName::Ip(a), crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask }) =>
            ip_within(a, address, mask),
        (ConstrainedName::Rfc822 { local, host }, crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(b)) =>
            rfc822_within(local, host, b),
        (ConstrainedName::Directory(rdns), crate::name_constraints::spec::GeneralNameConstraint::DirectoryName(b)) =>
            match directory_base(b) {
                Some(base_rdns) => directory_within(rdns, base_rdns),
                None => false,
            },
        _ => false,
    }
}

/// Some name that `name` stands for is within `base`, or, for a mailbox,
/// the base matches it ignoring the case of the local part. The same as
/// `within` except for a wildcard and a mailbox base.
pub open spec fn meets(name: ConstrainedName, base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match (name, base) {
        (ConstrainedName::DnsWildcard(s), crate::name_constraints::spec::GeneralNameConstraint::DnsName(b)) =>
            dns_wildcard_meets(s, b),
        (ConstrainedName::Rfc822 { local, host }, crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(b)) =>
            rfc822_meets(local, host, b),
        _ => within(name, base),
    }
}

// ---------------------------------------------------------------------------
// Malformed bases (Q12)
// ---------------------------------------------------------------------------

/// A mask byte of the form ones-then-zeros: 0x00, 0x80, 0xC0, ..., 0xFF.
pub open spec fn is_prefix_byte(b: u8) -> bool {
    b == 0x00 || b == 0x80 || b == 0xC0 || b == 0xE0 || b == 0xF0
        || b == 0xF8 || b == 0xFC || b == 0xFE || b == 0xFF
}

/// Every byte from `i` on is zero.
pub open spec fn all_zero_from(mask: Seq<u8>, i: int) -> bool
    recommends 0 <= i
    decreases mask.len() - i
{
    i >= mask.len() || (mask[i] == 0 && all_zero_from(mask, i + 1))
}

/// From `i` on, the mask is 0xFF bytes, at most one prefix byte, then zero
/// bytes: a CIDR prefix (RFC 4632 §3.1).
pub open spec fn mask_contiguous_from(mask: Seq<u8>, i: int) -> bool
    recommends 0 <= i
    decreases mask.len() - i
{
    if i >= mask.len() {
        true
    } else if mask[i] == 0xFF {
        mask_contiguous_from(mask, i + 1)
    } else {
        is_prefix_byte(mask[i]) && all_zero_from(mask, i + 1)
    }
}

/// A well-formed base ((R) malformed bases): a dNSName that is empty or in
/// preferred name syntax, an iPAddress with a contiguous mask, an rfc822Name
/// of one of the three shapes, a directoryName that is one Name. A base of
/// an uninterpreted form has no shape to check.
pub open spec fn base_supported(base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match base {
        crate::name_constraints::spec::GeneralNameConstraint::DnsName(b) => b.len() == 0 || crate::spec::dns_name_shape(b),
        crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask } =>
            (address.len() == 4 || address.len() == 16) && mask.len() == address.len()
                && mask_contiguous_from(mask, 0),
        crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(b) => rfc822_base_shape(b),
        crate::name_constraints::spec::GeneralNameConstraint::DirectoryName(b) => directory_base(b) is Some,
        crate::name_constraints::spec::GeneralNameConstraint::Unsupported { .. } => true,
    }
}

/// Every base in `items` is supported.
pub open spec fn subtrees_supported(items: Seq<crate::name_constraints::spec::GeneralSubtree>) -> bool
    decreases items.len()
{
    items.len() == 0 || (base_supported(items.last().base) && subtrees_supported(items.drop_last()))
}

/// A directoryName base.
pub open spec fn is_directory_name_base(base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    base is DirectoryName
}

/// Some base in `items` is a directoryName.
pub open spec fn has_directory_name_base(items: Seq<crate::name_constraints::spec::GeneralSubtree>) -> bool
    decreases items.len()
{
    items.len() > 0 && (is_directory_name_base(items.last().base) || has_directory_name_base(items.drop_last()))
}

/// A NameConstraints value this module can apply: at least one field present
/// (§4.2.1.10 "either the permittedSubtrees field or the excludedSubtrees
/// MUST be present"), every base well formed, and no directoryName in
/// excludedSubtrees (R, Excluded directoryName).
pub open spec fn constraints_supported(value: crate::name_constraints::spec::NameConstraints) -> bool {
    &&& (value.permitted_subtrees is Some || value.excluded_subtrees is Some)
    &&& match value.permitted_subtrees {
        Some(items) => subtrees_supported(items),
        None => true,
    }
    &&& match value.excluded_subtrees {
        Some(items) => subtrees_supported(items),
        None => true,
    }
    &&& match value.excluded_subtrees {
        Some(items) => !has_directory_name_base(items),
        None => true,
    }
}

// ---------------------------------------------------------------------------
// One NameConstraints value
// ---------------------------------------------------------------------------

/// Some base in `items` has `name`'s type.
pub open spec fn has_base_of_type(items: Seq<crate::name_constraints::spec::GeneralSubtree>, name: ConstrainedName) -> bool
    decreases items.len()
{
    items.len() > 0 && (same_name_type(name, items.last().base) || has_base_of_type(items.drop_last(), name))
}

/// `name` is within some base in `items`.
pub open spec fn within_some(items: Seq<crate::name_constraints::spec::GeneralSubtree>, name: ConstrainedName) -> bool
    decreases items.len()
{
    items.len() > 0 && (within(name, items.last().base) || within_some(items.drop_last(), name))
}

/// `name` meets some base in `items`.
pub open spec fn meets_some(items: Seq<crate::name_constraints::spec::GeneralSubtree>, name: ConstrainedName) -> bool
    decreases items.len()
{
    items.len() > 0 && (meets(name, items.last().base) || meets_some(items.drop_last(), name))
}

/// One set's contribution to permitted_subtrees, §6.1.4 (g)(1): with no
/// permittedSubtrees, or none of `name`'s type ("the permitted_subtrees state
/// variable is unchanged for that name type"), it permits `name`; otherwise
/// `name` must be within one of them (BetterTLS `tc304` fails, `tc1` passes).
pub open spec fn permitted_by(value: crate::name_constraints::spec::NameConstraints, name: ConstrainedName) -> bool {
    match value.permitted_subtrees {
        None => true,
        Some(items) => !has_base_of_type(items, name) || within_some(items, name),
    }
}

/// One set's contribution to excluded_subtrees, §6.1.4 (g)(2): `name` meets
/// one of its excludedSubtrees (BetterTLS `tc253`; `tc332` for iPAddress).
pub open spec fn excluded_by(value: crate::name_constraints::spec::NameConstraints, name: ConstrainedName) -> bool {
    match value.excluded_subtrees {
        None => false,
        Some(items) => meets_some(items, name),
    }
}

// ---------------------------------------------------------------------------
// §6.1.2 (b), (c): the state and its denotation
// ---------------------------------------------------------------------------

/// §6.1.2 (b), (c) and §6.1.1 (h), (i): the initial state permits every name
/// and excludes none.
pub open spec fn initial_state() -> Seq<crate::name_constraints::spec::NameConstraints> {
    seq![]
}

/// §6.1.2 (b) "permitted_subtrees": `name` is within the intersection of
/// every set's permitted subtrees of its type. Intersection across sets is
/// `rfc5280::nc::restrictive-permits-in-intermediates-narrows` and `-widens`.
pub open spec fn within_permitted_subtrees(state: Seq<crate::name_constraints::spec::NameConstraints>, name: ConstrainedName) -> bool
    decreases state.len()
{
    state.len() == 0
        || (permitted_by(state.last(), name) && within_permitted_subtrees(state.drop_last(), name))
}

/// §6.1.2 (c) "excluded_subtrees": `name` is within the union of every set's
/// excluded subtrees of its type.
pub open spec fn within_excluded_subtrees(state: Seq<crate::name_constraints::spec::NameConstraints>, name: ConstrainedName) -> bool
    decreases state.len()
{
    state.len() > 0
        && (excluded_by(state.last(), name) || within_excluded_subtrees(state.drop_last(), name))
}

/// A matched name satisfies the state: within permitted_subtrees and not
/// within excluded_subtrees. §4.2.1.10 "Any name matching a restriction in
/// the excludedSubtrees field is invalid regardless of information appearing
/// in the permittedSubtrees" (`rfc5280::nc::excluded-match-permitted-and-excluded`,
/// BetterTLS `tc280`).
pub open spec fn name_acceptable(state: Seq<crate::name_constraints::spec::NameConstraints>, name: ConstrainedName) -> bool {
    within_permitted_subtrees(state, name) && !within_excluded_subtrees(state, name)
}

// ---------------------------------------------------------------------------
// §6.1.3 (b), (c): one certificate's names
// ---------------------------------------------------------------------------

/// (R) malformed entries: every entry is well formed.
pub open spec fn names_well_formed(names: Seq<crate::extensions::spec::GeneralName>) -> bool
    decreases names.len()
{
    names.len() == 0 || (entry_well_formed(names.last()) && names_well_formed(names.drop_last()))
}

/// `base` is of the uninterpreted form `tag`.
pub open spec fn base_of_form(base: crate::name_constraints::spec::GeneralNameConstraint, tag: u32) -> bool {
    match base {
        crate::name_constraints::spec::GeneralNameConstraint::Unsupported { tag: t, .. } => t == tag,
        _ => false,
    }
}

/// Some base in `items` is of the uninterpreted form `tag`.
pub open spec fn has_base_of_form(items: Seq<crate::name_constraints::spec::GeneralSubtree>, tag: u32) -> bool
    decreases items.len()
{
    items.len() > 0 && (base_of_form(items.last().base, tag) || has_base_of_form(items.drop_last(), tag))
}

/// `value` has a base of the uninterpreted form `tag`, in either list.
pub open spec fn constrains_form(value: crate::name_constraints::spec::NameConstraints, tag: u32) -> bool {
    ||| match value.permitted_subtrees {
        Some(items) => has_base_of_form(items, tag),
        None => false,
    }
    ||| match value.excluded_subtrees {
        Some(items) => has_base_of_form(items, tag),
        None => false,
    }
}

/// Some set in the state constrains the uninterpreted form `tag`.
pub open spec fn form_constrained(state: Seq<crate::name_constraints::spec::NameConstraints>, tag: u32) -> bool
    decreases state.len()
{
    state.len() > 0 && (constrains_form(state.last(), tag) || form_constrained(state.drop_last(), tag))
}

/// The other forms: no entry is of an uninterpreted form that some set
/// constrains (Firefox's rule; R against Chrome, which also asks that the
/// extension be critical).
pub open spec fn names_of_unconstrained_forms(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
) -> bool
    decreases names.len()
{
    names.len() == 0 || ({
        let entry_ok = match names.last() {
            crate::extensions::spec::GeneralName::Other(tag, _) =>
                !is_uninterpreted_form(tag) || !form_constrained(state, tag),
            _ => true,
        };
        entry_ok && names_of_unconstrained_forms(state, names.drop_last())
    })
}

/// §6.1.3 (b): "verify that each of the alternative names in the
/// subjectAltName extension (critical or non-critical) is within one of the
/// permitted_subtrees for that name type." The subject-name half is
/// in `subject_acceptable`. Entries of other forms are left to
/// `names_of_unconstrained_forms`.
pub open spec fn names_within_permitted(state: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>) -> bool
    decreases names.len()
{
    names.len() == 0 || ({
        &&& match constrained_name(names.last()) {
            Some(name) => within_permitted_subtrees(state, name),
            None => true,
        }
        &&& names_within_permitted(state, names.drop_last())
    })
}

/// §6.1.3 (c): "verify that each of the alternative names in the
/// subjectAltName extension (critical or non-critical) is not within any of
/// the excluded_subtrees for that name type." Every entry is checked, not
/// only the first (`rfc5280::nc::excluded-dns-match-second`).
pub open spec fn names_not_excluded(state: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>) -> bool
    decreases names.len()
{
    names.len() == 0 || ({
        &&& match constrained_name(names.last()) {
            Some(name) => !within_excluded_subtrees(state, name),
            None => true,
        }
        &&& names_not_excluded(state, names.drop_last())
    })
}

/// §6.1.3 (b) and (c) for the subjectAltName entries `names` of a
/// certificate (empty when the extension is absent), under `state`.
pub open spec fn certificate_names_acceptable(state: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>) -> bool {
    // (R) malformed entries: under any constraint, refuse a malformed entry.
    &&& state.len() == 0 || names_well_formed(names)
    // (b)
    &&& names_within_permitted(state, names)
    // (c)
    &&& names_not_excluded(state, names)
    // The other forms: refuse an entry of a constrained uninterpreted form.
    &&& names_of_unconstrained_forms(state, names)
}

/// PKCS #9 emailAddress, `1.2.840.113549.1.9.1`.
pub open spec fn email_address_oid() -> Seq<nat> {
    seq![1nat, 2, 840, 113549, 1, 9, 1]
}

/// Some attribute in `attributes` is an emailAddress.
pub open spec fn attributes_have_email(attributes: Seq<crate::name::spec::AttributeTypeAndValue>) -> bool
    decreases attributes.len()
{
    attributes.len() > 0
        && (attributes.last().oid =~= email_address_oid() || attributes_have_email(attributes.drop_last()))
}

/// Some RDN in `rdns` has an emailAddress attribute.
pub open spec fn rdns_have_email(rdns: Seq<crate::name::spec::RelativeDistinguishedName>) -> bool
    decreases rdns.len()
{
    rdns.len() > 0 && (attributes_have_email(rdns.last().attributes) || rdns_have_email(rdns.drop_last()))
}

/// Some base in `items` is an rfc822Name.
pub open spec fn has_rfc822_base(items: Seq<crate::name_constraints::spec::GeneralSubtree>) -> bool
    decreases items.len()
{
    items.len() > 0 && (items.last().base is Rfc822Name || has_rfc822_base(items.drop_last()))
}

/// Some set in the state has an rfc822Name base, in either list.
pub open spec fn rfc822_in_force(state: Seq<crate::name_constraints::spec::NameConstraints>) -> bool
    decreases state.len()
{
    state.len() > 0 && ({
        ||| match state.last().permitted_subtrees {
            Some(items) => has_rfc822_base(items),
            None => false,
        }
        ||| match state.last().excluded_subtrees {
            Some(items) => has_rfc822_base(items),
            None => false,
        }
        ||| rfc822_in_force(state.drop_last())
    })
}

/// §6.1.3 (b) and (c) for the subject field: "verify that the subject name
/// is within one of the permitted_subtrees for X.500 distinguished names"
/// and "is not within any of the excluded_subtrees for X.500 distinguished
/// names". `subject` is the complete subject Name TLV. Under any
/// constraint, a subject the Name decoder refuses fails (R), and so does an
/// emailAddress attribute while an rfc822Name constraint is in force (R).
pub open spec fn subject_acceptable(state: Seq<crate::name_constraints::spec::NameConstraints>, subject: Seq<u8>) -> bool {
    state.len() == 0 || match crate::name::spec::parse_name(subject) {
        None => false,
        Some(parsed) => {
            &&& name_acceptable(state, ConstrainedName::Directory(parsed.rdns))
            &&& !(rfc822_in_force(state) && rdns_have_email(parsed.rdns))
        },
    }
}

// ---------------------------------------------------------------------------
// §6.1.4 (g) and the path
// ---------------------------------------------------------------------------

/// §6.1.4 (g): "If a name constraints extension is included in the
/// certificate, modify the permitted_subtrees and excluded_subtrees state
/// variables": (1) intersect and (2) union, both done by adding the set to
/// the state. `None` refuses the path (malformed bases, excluded
/// directoryName).
pub open spec fn prepare_name_constraints(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    extension: Option<crate::name_constraints::spec::NameConstraints>,
) -> Option<Seq<crate::name_constraints::spec::NameConstraints>> {
    match extension {
        None => Some(state),
        Some(value) => if constraints_supported(value) { Some(state.push(value)) } else { None },
    }
}

/// What §6.1.3 (b), (c) and §6.1.4 (g) read from one certificate.
pub struct NcCertificate {
    /// The complete subject Name TLV.
    pub subject: Seq<u8>,
    /// The subjectAltName entries, in order; empty when there is none.
    pub subject_alt_names: Seq<crate::extensions::spec::GeneralName>,
    /// The decoded NameConstraints extension, if present.
    pub name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
}

/// §6.1.3 (b) and (c) for one certificate: its subjectAltName entries and
/// its subject field.
pub open spec fn certificate_acceptable(state: Seq<crate::name_constraints::spec::NameConstraints>, certificate: NcCertificate) -> bool {
    certificate_names_acceptable(state, certificate.subject_alt_names)
        && subject_acceptable(state, certificate.subject)
}

/// The name-constraint steps of §6.1.3 and §6.1.4 for `path[i..]`, under
/// `state`. §6.1.3 (b), (c) are applied to every certificate, self-issued
/// ones included: the step's "If certificate i is self-issued and it is not
/// the final certificate in the path, skip this step for certificate i" is
/// not followed ((R) self-issued intermediates are checked; Firefox;
/// `rfc5280::nc::permitted-self-issued` is a listed divergence,
/// `rfc5280::nc::excluded-self-issued-leaf` fails). Intermediates' names are
/// checked (`rfc5280::nc::intermediate-with-san-rejected-by-intermediate-nc`).
/// §6.1.4 is "preparation for certificate i+1", so it is not applied to the
/// final certificate.
pub open spec fn names_constrained_from(path: Seq<NcCertificate>, i: int, state: Seq<crate::name_constraints::spec::NameConstraints>) -> bool
    recommends 0 <= i
    decreases path.len() - i
{
    if i < 0 || i >= path.len() {
        true
    } else {
        let certificate = path[i];
        let last = i == path.len() - 1;
        // §6.1.3 (b), (c), for every certificate ((R) no self-issued skip)
        &&& certificate_acceptable(state, certificate)
        // §6.1.4 (g), then certificate i + 1
        &&& last || match prepare_name_constraints(state, certificate.name_constraints) {
            Some(next) => names_constrained_from(path, i + 1, next),
            None => false,
        }
    }
}

/// The name-constraint part of §6.1 for a whole path, first certificate
/// first, starting from `initial` (normally `initial_state()`).
pub open spec fn names_constrained(path: Seq<NcCertificate>, initial: Seq<crate::name_constraints::spec::NameConstraints>) -> bool {
    names_constrained_from(path, 0, initial)
}

} // verus!
