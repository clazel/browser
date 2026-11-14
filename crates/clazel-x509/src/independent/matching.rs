//! Host name matching, transcribed for the independent decoder from RFC 6125
//! (March 2011), clauses 6.3 and 6.4 with 2.2 and 7.2 (text SHA-256
//! `ee1f413f420bfa6199302b1a85669243f27076c803a120d55c15198e300d7cf1`), used
//! here instead of RFC 9525 so that the second source has a different text.
//!
//! Not read while writing this file: see the list in `independent/mod.rs`.
//!
//! Modelling choices:
//! - The reference identifier is a DNS domain name in ASCII: U-labels are
//!   already A-labels, as 6.4.2 requires before checking. The conversion
//!   itself is outside this file.
//! - The presented identifiers come from a decoded certificate. A DNS-ID is a
//!   `dNSName` entry of `subjectAltName` (1.8). A URI-ID is a
//!   `uniformResourceIdentifier` entry, and an SRV-ID an `otherName` of form
//!   SRVName, `id-on-dnsSRV` 1.3.6.1.5.5.7.8.7 (RFC 4985). They matter only
//!   because they stop a CN-ID check (6.4.4); matching them against a
//!   reference needs an application service type (6.5), which is out of
//!   scope here. So 6.3's list of reference identifiers is one DNS-ID, with a
//!   CN-ID at the same name when [`MatchChoices::cn_id`] allows.
//! - A domain name is split at each `.` into labels; a name with an empty
//!   label is not a domain name ([DNS-CONCEPTS]) and matches nothing.
//! - The reference must not contain `*`: `*` is not an LDH character (2.2),
//!   so it never stands for itself in a reference.
//! - Label lengths and name lengths are not checked: 6.4 does not mention
//!   them.
//!
//! Every place 6.4 leaves open is a field of [`MatchChoices`], so that the
//! rules stay what the text says and the proof session can fix them to a
//! particular client's answers:
//! - 6.4.3 "MAY match ... '*'": `wildcards`.
//! - 6.4.3 rule 1 "SHOULD NOT": `wildcard_beyond_left_most`.
//! - 6.4.3 rule 2 "SHOULD NOT": `wildcard_spans_labels`.
//! - 6.4.3 rule 3 "MAY": `partial_label_wildcard`.
//! - 6.4.3 rule 3 "SHOULD NOT": `wildcard_in_a_label`.
//! - 6.4.4 "MAY as a last resort": `cn_id`.
//! - Not stated: whether `baz*` matches `baz`, `wildcard_may_be_empty`.
//! - Not stated: whether a reference with a trailing dot equals one without,
//!   `ignore_root_dot`.
//!
//! Other open points, settled here and listed in the pull request:
//! - More than one `*` in a label (7.2 lists `f*b*r.example.com` as an
//!   ambiguity) never matches: the rules speak of "the wildcard character".
//! - `*` in more than one label (`*.*.example.com`) is covered by rule 1,
//!   whichever way the choice falls: the left-most label is handled as a
//!   wildcard, and each other label's `*` is under
//!   `wildcard_beyond_left_most`.
//! - `*.com`, a wildcard over a public suffix (7.2 lists it as an ambiguity):
//!   6.4.3 sets no rule, so it matches. Any public-suffix rule belongs to the
//!   client, outside this text.
//! - With `wildcard_spans_labels` set, the wildcard stands for one or more
//!   whole left-most labels. This is the only reading of the behaviour that
//!   rule 2 advises against, but its details are not in the text.
//! - With `wildcard_beyond_left_most` set, a `*` in a non-left-most label
//!   follows the same rules as in the left-most one.
//! - Rule 3's "embedded within an A-label": a presented label that starts
//!   with `xn--` in any case. A wildcard filling the entire left-most label
//!   may match an A-label of the reference (7.2 allows `*.xn--...`, and rule
//!   3 is about the presented label).
//! - IP addresses are out of scope (1.7.2): nothing here matches one.
//! - Duplicates and order of the presented identifiers do not matter: 6.3
//!   succeeds "if any presented identifier matches".

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::extensions::*;

#[cfg(verus_only)]
use super::requirements::*;
#[cfg(verus_only)]
use super::structures::*;

verus! {

/// What RFC 6125 leaves to the client.
pub struct MatchChoices {
    /// 6.4.3 "MAY match" a presented `*`.
    pub wildcards: bool,
    /// 6.4.3 rule 1 "SHOULD NOT": a `*` outside the left-most label.
    pub wildcard_beyond_left_most: bool,
    /// 6.4.3 rule 2 "SHOULD NOT": a whole-label `*` taking several labels.
    pub wildcard_spans_labels: bool,
    /// 6.4.3 rule 3 "MAY": a `*` that is part of a label.
    pub partial_label_wildcard: bool,
    /// 6.4.3 rule 3 "SHOULD NOT": a `*` inside an A-label.
    pub wildcard_in_a_label: bool,
    /// 6.4.4 "MAY as a last resort": check the Common Name.
    pub cn_id: bool,
    /// Not stated: `baz*` matching `baz`.
    pub wildcard_may_be_empty: bool,
    /// Not stated: `example.com.` equal to `example.com`.
    pub ignore_root_dot: bool,
}

/// The answers that follow every SHOULD and SHOULD NOT and take no MAY except
/// the first, the plain `*.example.com`.
pub open spec fn cautious_choices() -> MatchChoices {
    MatchChoices {
        wildcards: true,
        wildcard_beyond_left_most: false,
        wildcard_spans_labels: false,
        partial_label_wildcard: false,
        wildcard_in_a_label: false,
        cn_id: false,
        wildcard_may_be_empty: false,
        ignore_root_dot: false,
    }
}

// ---------------------------------------------------------------------------
// Labels
// ---------------------------------------------------------------------------

/// The index of the first `.` of `s` from `i`, or `s.len()`.
pub open spec fn next_dot(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() {
        s.len()
    } else if s[i as int] == 0x2E {
        i
    } else {
        next_dot(s, i + 1)
    }
}

/// `s` from `i` as its labels, the separator being `.`.
pub open spec fn labels_from(s: Seq<u8>, i: nat) -> Seq<Seq<u8>>
    decreases s.len() - i + 1,
{
    if i > s.len() {
        Seq::<Seq<u8>>::empty()
    } else {
        let end = next_dot(s, i);
        if end < i || end >= s.len() {
            seq![s.subrange(i as int, s.len() as int)]
        } else {
            seq![s.subrange(i as int, end as int)] + labels_from(s, end + 1)
        }
    }
}

/// The labels of a domain name.
pub open spec fn labels(s: Seq<u8>) -> Seq<Seq<u8>> {
    labels_from(s, 0)
}

/// No label from `i` is empty.
pub open spec fn labels_non_empty(l: Seq<Seq<u8>>, i: nat) -> bool
    decreases l.len() - i,
{
    if i >= l.len() {
        true
    } else {
        l[i as int].len() > 0 && labels_non_empty(l, i + 1)
    }
}

/// `s` with one final `.` removed.
pub open spec fn without_root_dot(s: Seq<u8>) -> Seq<u8> {
    if s.len() > 0 && s[(s.len() - 1) as int] == 0x2E {
        s.subrange(0, s.len() - 1)
    } else {
        s
    }
}

/// How many `*` the octets of `s` from `i` hold.
pub open spec fn star_count(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() {
        0
    } else if s[i as int] == 0x2A {
        1 + star_count(s, i + 1)
    } else {
        star_count(s, i + 1)
    }
}

/// The position of the first `*` of `s` from `i`.
pub open spec fn star_position(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i >= s.len() {
        s.len()
    } else if s[i as int] == 0x2A {
        i
    } else {
        star_position(s, i + 1)
    }
}

/// [DNS-CASE] lower-casing: only ASCII letters change.
pub open spec fn ascii_lower(c: u8) -> int {
    if 0x41 <= c && c <= 0x5A {
        c + 0x20
    } else {
        c as int
    }
}

/// 6.4.1: "a case-insensitive ASCII comparison", of `count` octets of `a` from
/// `i` with `count` octets of `b` from `j`.
pub open spec fn same_octets(a: Seq<u8>, i: nat, b: Seq<u8>, j: nat, count: nat) -> bool
    decreases count,
{
    if count == 0 {
        true
    } else {
        i < a.len() && j < b.len() && ascii_lower(a[i as int]) == ascii_lower(b[j as int])
            && same_octets(a, i + 1, b, j + 1, (count - 1) as nat)
    }
}

/// 6.4.1, whole labels.
pub open spec fn same_label(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() == b.len() && same_octets(a, 0, b, 0, a.len())
}

/// 6.4.3 rule 3's "A-label": the prefix of IDNA-DEFS in any case.
pub open spec fn is_a_label(l: Seq<u8>) -> bool {
    l.len() >= 4 && ascii_lower(l[0]) == 0x78 && ascii_lower(l[1]) == 0x6E && l[2] == 0x2D && l[3]
        == 0x2D
}

/// 6.4.3 rule 3: `presented`, a label with one `*`, against a reference label.
/// The characters before and after the `*` must be those at the two ends of
/// `reference`.
pub open spec fn wildcard_label_matches(
    choices: MatchChoices,
    presented: Seq<u8>,
    reference: Seq<u8>,
) -> bool {
    let at = star_position(presented, 0);
    let after = (presented.len() - at - 1) as nat;
    let fixed = at + after;
    if presented.len() == 1 {
        // The wildcard is the only character of the label: it stands for a
        // whole, non-empty label.
        reference.len() > 0
    } else if !choices.partial_label_wildcard {
        // Rule 3 "MAY".
        false
    } else if is_a_label(presented) && !choices.wildcard_in_a_label {
        // Rule 3 "SHOULD NOT".
        false
    } else if reference.len() < fixed {
        false
    } else if reference.len() == fixed && !choices.wildcard_may_be_empty {
        false
    } else {
        same_octets(presented, 0, reference, 0, at) && same_octets(
            presented,
            at + 1,
            reference,
            (reference.len() - after) as nat,
            after,
        )
    }
}

/// One presented label against one reference label. `beyond_left_most` says it is
/// not the left-most.
pub open spec fn label_matches(
    choices: MatchChoices,
    presented: Seq<u8>,
    reference: Seq<u8>,
    beyond_left_most: bool,
) -> bool {
    let stars = star_count(presented, 0);
    if stars == 0 {
        // 6.4.1 "Each label MUST match".
        same_label(presented, reference)
    } else if !choices.wildcards {
        // 6.4.3 "MAY".
        false
    } else if stars > 1 {
        false
    } else if beyond_left_most && !choices.wildcard_beyond_left_most {
        // Rule 1 "SHOULD NOT".
        false
    } else {
        wildcard_label_matches(choices, presented, reference)
    }
}

/// Labels from `i` pairwise, the same number on each side, none left-most.
pub open spec fn remaining_labels_match(
    choices: MatchChoices,
    presented: Seq<Seq<u8>>,
    i: nat,
    reference: Seq<Seq<u8>>,
    j: nat,
) -> bool
    decreases presented.len() - i,
{
    if i >= presented.len() {
        j == reference.len()
    } else if j >= reference.len() {
        false
    } else {
        label_matches(choices, presented[i as int], reference[j as int], true)
            && remaining_labels_match(choices, presented, i + 1, reference, j + 1)
    }
}

/// The two label lists, as 6.4.1 and 6.4.3 compare them.
pub open spec fn label_lists_match(
    choices: MatchChoices,
    presented: Seq<Seq<u8>>,
    reference: Seq<Seq<u8>>,
) -> bool {
    if presented.len() == 0 || reference.len() == 0 {
        false
    } else if label_matches(choices, presented[0], reference[0], false) && remaining_labels_match(
        choices,
        presented,
        1,
        reference,
        1,
    ) {
        true
    } else {
        // Rule 2 "SHOULD NOT ... compare against anything but the left-most
        // label": the client that does lets a whole-label wildcard take more
        // reference labels than one.
        choices.wildcards && choices.wildcard_spans_labels && presented[0].len() == 1
            && presented[0][0] == 0x2A && reference.len() >= presented.len()
            && remaining_labels_match(
            choices,
            presented,
            1,
            reference,
            (reference.len() - presented.len() + 1) as nat,
        )
    }
}

/// `reference` is a name this file compares.
pub open spec fn reference_usable(reference: Seq<u8>) -> bool {
    star_count(reference, 0) == 0 && reference.len() > 0 && labels_non_empty(labels(reference), 0)
}

/// 6.4: one presented DNS domain name against the reference identifier.
pub open spec fn domain_name_matches(
    choices: MatchChoices,
    presented: Seq<u8>,
    reference: Seq<u8>,
) -> bool {
    let r = if choices.ignore_root_dot {
        without_root_dot(reference)
    } else {
        reference
    };
    let p = if choices.ignore_root_dot {
        without_root_dot(presented)
    } else {
        presented
    };
    reference_usable(r) && p.len() > 0 && labels_non_empty(labels(p), 0) && label_lists_match(
        choices,
        labels(p),
        labels(r),
    )
}

// ---------------------------------------------------------------------------
// 6.3, and 6.4.4
// ---------------------------------------------------------------------------

/// The certificate's `subjectAltName` entries.
pub open spec fn subject_alt_names(c: Certificate) -> Seq<GeneralName> {
    match find_extension(extensions_of(c), 0, id_ce_subject_alt_name()) {
        None => Seq::<GeneralName>::empty(),
        Some(x) => match x.value {
            ExtensionValue::SubjectAltName(names) => names,
            _ => Seq::<GeneralName>::empty(),
        },
    }
}

/// RFC 4985 `id-on-dnsSRV`.
pub open spec fn id_on_dns_srv() -> ObjectIdentifier {
    seq![1nat, 3nat, 6nat, 1nat, 5nat, 5nat, 7nat, 8nat, 7nat]
}

/// 6.4.4: an entry that is a DNS-ID, SRV-ID or URI-ID.
pub open spec fn blocks_cn_id(name: GeneralName) -> bool {
    match name {
        GeneralName::DNSName(_) => true,
        GeneralName::UniformResourceIdentifier(_) => true,
        GeneralName::OtherName { type_id, value: _ } => type_id == id_on_dns_srv(),
        _ => false,
    }
}

/// 6.4.4: "if and only if the presented identifiers do not include a DNS-ID,
/// SRV-ID, URI-ID", for the entries from `i`.
pub open spec fn no_blocking_identifier(names: Seq<GeneralName>, i: nat) -> bool
    decreases names.len() - i,
{
    if i >= names.len() {
        true
    } else {
        !blocks_cn_id(names[i as int]) && no_blocking_identifier(names, i + 1)
    }
}

/// 6.3: "if any presented identifier matches", over the DNS-IDs from `i`.
pub open spec fn some_dns_id_matches(
    choices: MatchChoices,
    names: Seq<GeneralName>,
    i: nat,
    reference: Seq<u8>,
) -> bool
    decreases names.len() - i,
{
    if i >= names.len() {
        false
    } else {
        (match names[i as int] {
            GeneralName::DNSName(presented) => domain_name_matches(choices, presented, reference),
            _ => false,
        }) || some_dns_id_matches(choices, names, i + 1, reference)
    }
}

/// X.520 `id-at-commonName`: `{id-at 3}`, with `id-at` `{ds 4}` (X.501 Annex
/// A).
pub open spec fn id_at_common_name() -> ObjectIdentifier {
    seq![2nat, 5nat, 4nat, 3nat]
}

/// 6.4.4 "a string whose form matches that of a fully qualified DNS domain
/// name": the value of `attribute` as a string, when it is a CN in one of the
/// ASCII-compatible forms. A BMPString or UniversalString is not read, and
/// so never matches (6.3: a CN-ID "always contains a string whose form
/// matches that of a DNS domain name").
pub open spec fn common_name_value(attribute: AttributeTypeAndValue) -> Option<Seq<u8>> {
    if attribute.attribute_type != id_at_common_name() {
        None
    } else {
        match decode_unbounded_directory_string(attribute.value) {
            Some(UnboundedDirectoryString::PrintableString(s)) => Some(s),
            Some(UnboundedDirectoryString::Utf8String(s)) => Some(s),
            _ => None,
        }
    }
}

/// Any CN of one RDN, from `i`.
pub open spec fn some_cn_in_rdn(
    choices: MatchChoices,
    rdn: RelativeDistinguishedName,
    i: nat,
    reference: Seq<u8>,
) -> bool
    decreases rdn.len() - i,
{
    if i >= rdn.len() {
        false
    } else {
        (match common_name_value(rdn[i as int]) {
            Some(s) => domain_name_matches(choices, s, reference),
            None => false,
        }) || some_cn_in_rdn(choices, rdn, i + 1, reference)
    }
}

/// Any CN of the subject, from RDN `i`. 6.4.4 says "a Common Name field" and
/// does not choose among several: any one that matches counts.
pub open spec fn some_cn_matches(
    choices: MatchChoices,
    rdns: Seq<RelativeDistinguishedName>,
    i: nat,
    reference: Seq<u8>,
) -> bool
    decreases rdns.len() - i,
{
    if i >= rdns.len() {
        false
    } else {
        some_cn_in_rdn(choices, rdns[i as int], 0, reference) || some_cn_matches(
            choices,
            rdns,
            i + 1,
            reference,
        )
    }
}

/// 6.3 and 6.4: does the certificate present an identifier that matches the
/// host name `reference`?
pub open spec fn certificate_matches_host(
    choices: MatchChoices,
    c: Certificate,
    reference: Seq<u8>,
) -> bool {
    let names = subject_alt_names(c);
    if some_dns_id_matches(choices, names, 0, reference) {
        true
    } else if choices.cn_id && no_blocking_identifier(names, 0) {
        // 6.4.4 "as a last resort".
        some_cn_matches(choices, c.to_be_signed.subject.rdn_sequence, 0, reference)
    } else {
        false
    }
}

} // verus!
