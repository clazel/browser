//! RFC 5280 name-constraint matching: the meaning of a dNSName or iPAddress
//! subtree (§4.2.1.10), the permitted_subtrees and excluded_subtrees state
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
//!   the repository): §1.9, §3.4 and question Q12, accepted.
//!
//! Modelling choices. Every place where this refuses more than RFC 5280
//! requires is marked **(R)**.
//! - Only dNSName and iPAddress are matched (design §1.9). The state holds
//!   the decoded `NameConstraints` values of the path in order, and its
//!   denotation is the RFC's: a name is within permitted_subtrees iff, for
//!   every set whose permittedSubtrees has a base of the name's type, it is
//!   within one of those bases; it is within excluded_subtrees iff it meets
//!   any excluded base of its type. §6.1.4 (g)(1) intersects one set at a
//!   time and leaves a type unchanged when the set has no base of it; (g)(2)
//!   unions. Keeping the sets instead of computing the intersection is the
//!   same set of names (`lemma_permitted_is_intersection`,
//!   `lemma_excluded_is_union`), and it never has to compute the
//!   intersection of two subtrees, which the RFC only illustrates.
//! - **(R) Q12, constraints.** A NameConstraints extension with any base of
//!   another form (directoryName, rfc822Name, URI, otherName and the rest,
//!   the decoder's `Unsupported`), in either list, makes §6.1.4 (g) refuse
//!   the path when the certificate carrying it is processed, whether or not
//!   any later certificate has a name of that form. RFC 5280 asks only that
//!   such a constraint be processed or the certificate rejected when a name
//!   of that form appears; for rfc822Name and URI it would let the path
//!   through. This makes `rfc5280::nc::permitted-dn-match`,
//!   `rfc5280::nc::nc-forbids-othername-noop` and the `nc-permits-email-*`
//!   SUCCESS cases listed divergences. CA/B BR §7.1.2.5.2 requires a
//!   directoryName base in every technically constrained subordinate CA, so
//!   this refuses those paths too.
//! - **(R) Q12, names.** Once at least one NameConstraints extension is in
//!   the state, every subjectAltName entry of a checked certificate must be a
//!   dNSName in preferred name syntax (`crate::spec::dns_name_shape`), a
//!   wildcard `*.` followed by one, or a 4- or 16-octet iPAddress. Any other
//!   entry fails §6.1.3 (b) and (c). RFC 5280 §4.2.1.10 says "Restrictions
//!   apply only when the specified name form is present", so it would accept
//!   an rfc822Name or URI SAN under dNSName-only constraints, and leaves a
//!   malformed dNSName undefined. With an empty state nothing is checked, as
//!   the RFC's initial state permits every name. Fixed by
//!   `rfc5280::nc::nc-permits-invalid-dns-san` (a SAN `.example.com` under a
//!   permitted `example.com` must fail); BetterTLS's mixed-form SANs
//!   (`tc6`, `tc8755` to `tc8976`) all expect FAILURE.
//! - **(R) Malformed bases.** A dNSName base must be empty or in preferred
//!   name syntax, so a leading period (`rfc5280::nc::invalid-dnsname-leading-period`,
//!   erratum 5997), a wildcard (`rfc5280::nc::invalid-dnsname-wildcard`) or a
//!   trailing dot refuses the path. An iPAddress base must have a
//!   contiguous mask (leading ones, then zeros), as RFC 4632 CIDR, which
//!   §4.2.1.10 names, implies; a non-contiguous mask refuses the path. No
//!   limbo case has one. A NameConstraints with both fields absent refuses
//!   the path: §4.2.1.10 "either the permittedSubtrees field or the
//!   excludedSubtrees MUST be present" (`webpki::nc::intermediate-permitted-excluded-subtrees-both-null`).
//!   The decoder already refuses empty `GeneralSubtrees`, an encoded
//!   minimum or maximum, and an empty dNSName base.
//! - An empty dNSName base (BR §7.1.2.5.2's "zero-length dNSName") contains
//!   every DNS name, read as "adding zero or more labels" to the empty name
//!   (design §3.4). The decoder refuses it today, so this clause matters
//!   only once the decoder accepts it.
//! - **The subject field is never checked.** The subject DN is matched only
//!   against directoryName constraints, and emailAddress attributes only
//!   against rfc822Name constraints (§4.2.1.10); both forms are refused
//!   above, so the subject is always unconstrained. The subject CN is never
//!   a DNS name here: the verifier never uses CN as an identity, and RFC
//!   5280 does not constrain it (erratum 3693 was rejected). BetterTLS
//!   agrees: `tc1714` expects SUCCESS with CN `bad.example.com` under an
//!   excluded `bad.example.com`.
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
//! - Certificates are indexed from 0 here; the RFC numbers them 1 to n. The
//!   last element is the RFC's certificate n. Whether a certificate is
//!   self-issued is an input (the design compares names as bytes, §1.10).
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
}

/// A presented `*.` followed by a name in preferred name syntax. Only the
/// whole left-most label may be `*` (RFC 9525 §6.3); `dns_name_shape` admits
/// no `*`, so there is no other one.
pub open spec fn is_wildcard_dns_name(name: Seq<u8>) -> bool {
    name.len() > 2 && name[0] == b'*' && name[1] == b'.'
        && crate::spec::dns_name_shape(name.subrange(2, name.len() as int))
}

/// The matched form of a subjectAltName entry, or `None` for any entry that
/// this module does not match: another GeneralName form, or a dNSName that
/// is neither a name nor a wildcard (Q12, names).
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
        crate::extensions::spec::GeneralName::Other(_, _) => None,
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

/// The name types of §6.1.4 (g): a dNSName base constrains DNS names and
/// wildcards, an iPAddress base constrains addresses (BetterTLS `tc259`:
/// an iPAddress-only permittedSubtrees leaves DNS names alone).
pub open spec fn same_name_type(name: ConstrainedName, base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match (name, base) {
        (ConstrainedName::Dns(_), crate::name_constraints::spec::GeneralNameConstraint::DnsName(_)) => true,
        (ConstrainedName::DnsWildcard(_), crate::name_constraints::spec::GeneralNameConstraint::DnsName(_)) => true,
        (ConstrainedName::Ip(_), crate::name_constraints::spec::GeneralNameConstraint::IpAddress { .. }) => true,
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
        _ => false,
    }
}

/// Some name that `name` stands for is within `base`. The same as `within`
/// except for a wildcard.
pub open spec fn meets(name: ConstrainedName, base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match (name, base) {
        (ConstrainedName::DnsWildcard(s), crate::name_constraints::spec::GeneralNameConstraint::DnsName(b)) =>
            dns_wildcard_meets(s, b),
        _ => within(name, base),
    }
}

// ---------------------------------------------------------------------------
// Q12: which constraints are matched
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

/// A base this module matches (design §1.9, Q12): a dNSName that is empty
/// or in preferred name syntax, or an iPAddress with a contiguous mask.
pub open spec fn base_supported(base: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    match base {
        crate::name_constraints::spec::GeneralNameConstraint::DnsName(b) => b.len() == 0 || crate::spec::dns_name_shape(b),
        crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask } =>
            (address.len() == 4 || address.len() == 16) && mask.len() == address.len()
                && mask_contiguous_from(mask, 0),
        crate::name_constraints::spec::GeneralNameConstraint::Unsupported { .. } => false,
    }
}

/// Every base in `items` is supported.
pub open spec fn subtrees_supported(items: Seq<crate::name_constraints::spec::GeneralSubtree>) -> bool
    decreases items.len()
{
    items.len() == 0 || (base_supported(items.last().base) && subtrees_supported(items.drop_last()))
}

/// A NameConstraints value this module can apply: at least one field present
/// (§4.2.1.10 "either the permittedSubtrees field or the excludedSubtrees
/// MUST be present"), and every base supported.
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

/// Q12, names: every entry has a matched form.
pub open spec fn names_of_matched_forms(names: Seq<crate::extensions::spec::GeneralName>) -> bool
    decreases names.len()
{
    names.len() == 0 || (constrained_name(names.last()) is Some && names_of_matched_forms(names.drop_last()))
}

/// §6.1.3 (b): "verify that each of the alternative names in the
/// subjectAltName extension (critical or non-critical) is within one of the
/// permitted_subtrees for that name type." The subject-name half is
/// vacuous (modelling choices). Entries of unmatched forms are left to Q12.
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

/// §6.1.3 (b) and (c) for a certificate whose subjectAltName entries are
/// `names` (empty when the extension is absent), under `state`.
pub open spec fn certificate_names_acceptable(state: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>) -> bool {
    // Q12, names: under any constraint, refuse an entry of an unmatched form.
    &&& state.len() == 0 || names_of_matched_forms(names)
    // (b)
    &&& names_within_permitted(state, names)
    // (c)
    &&& names_not_excluded(state, names)
}

// ---------------------------------------------------------------------------
// §6.1.4 (g) and the path
// ---------------------------------------------------------------------------

/// §6.1.4 (g): "If a name constraints extension is included in the
/// certificate, modify the permitted_subtrees and excluded_subtrees state
/// variables": (1) intersect and (2) union, both done by adding the set to
/// the state. `None` refuses the path (Q12, constraints).
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
    /// The subjectAltName entries, in order; empty when there is none.
    pub subject_alt_names: Seq<crate::extensions::spec::GeneralName>,
    /// Whether the certificate is self-issued (§6.1, decided by the caller).
    pub self_issued: bool,
    /// The decoded NameConstraints extension, if present.
    pub name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
}

/// The name-constraint steps of §6.1.3 and §6.1.4 for `path[i..]`, under
/// `state`. §6.1.3 (b), (c): "If certificate i is self-issued and it is not
/// the final certificate in the path, skip this step for certificate i"
/// (`rfc5280::nc::permitted-self-issued` passes,
/// `rfc5280::nc::excluded-self-issued-leaf` fails). Intermediates' names are
/// checked too (`rfc5280::nc::intermediate-with-san-rejected-by-intermediate-nc`).
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
        // §6.1.3 (b), (c)
        &&& (certificate.self_issued && !last)
            || certificate_names_acceptable(state, certificate.subject_alt_names)
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
