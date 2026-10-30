//! Executable RFC 5280 name-constraint matching, proven equal to
//! [`super::spec`] through [`super::contract`].
//!
//! Every function here is a direct reading of the spec function of the same
//! name. Byte scans are loops whose invariant is "the spec from position 0
//! equals the spec from the current position"; scans over lists keep a
//! prefix of the list in step with the spec's `drop_last` recursion. All
//! indexing is `get()` and all arithmetic is checked, so nothing here can
//! panic or overflow.

use super::spec as m;
use crate::extensions::exec as ext;
use crate::name::exec as nm;
use crate::name_constraints::exec as nc;
use clazel_der::decode as der;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Byte scans
// ---------------------------------------------------------------------------

/// ASCII case folding, as `crate::spec::ascii_fold`.
fn fold(b: u8) -> (r: u8)
    ensures r as nat == crate::spec::ascii_fold(b)
{
    match b {
        b'A'..=b'Z' => b | 0x20,
        _ => b,
    }
}

/// `crate::spec::folded_equal_from(a, b, 0)`.
fn folded_equal(a: &[u8], b: &[u8]) -> (result: bool)
    ensures result == crate::spec::folded_equal_from(a@, b@, 0)
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            crate::spec::folded_equal_from(a@, b@, 0) == crate::spec::folded_equal_from(a@, b@, i as int),
        decreases a.len() - i
    {
        let (Some(x), Some(y)) = (a.get(i), b.get(i)) else { return false; };
        if fold(*x) != fold(*y) { return false; }
        i = i.saturating_add(1);
    }
    true
}

/// `crate::spec::first_dot(name, 0)`.
fn first_dot(name: &[u8]) -> (result: usize)
    ensures result as int == crate::spec::first_dot(name@, 0)
{
    let mut i: usize = 0;
    while i < name.len()
        invariant
            i <= name.len(),
            crate::spec::first_dot(name@, 0) == crate::spec::first_dot(name@, i as int),
        decreases name.len() - i
    {
        let Some(byte) = name.get(i) else { return name.len(); };
        if *byte == b'.' { return i; }
        i = i.saturating_add(1);
    }
    name.len()
}

/// `crate::spec::dns_name_shape(name)`.
fn dns_shape(name: &[u8]) -> (result: bool)
    ensures result == crate::spec::dns_name_shape(name@)
{
    let mut i: usize = 0;
    while i < name.len()
        invariant
            i <= name.len(),
            crate::spec::valid_name_from(name@, 0) == crate::spec::valid_name_from(name@, i as int),
        decreases name.len() - i
    {
        let Some(byte) = name.get(i) else { return false; };
        let next = i.saturating_add(1);
        if *byte == b'.' {
            if i == 0 || next >= name.len() { return false; }
            if name.get(next) == Some(&b'.') { return false; }
        } else {
            let allowed = matches!(*byte, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'-');
            if !allowed { return false; }
            if next == name.len() { return true; }
        }
        i = next;
    }
    false
}

/// `m::ip_masked_equal_from(address, base, mask, 0)` for equal lengths.
fn ip_masked_equal(address: &[u8], base: &[u8], mask: &[u8]) -> (result: bool)
    requires address.len() == base.len(), base.len() == mask.len()
    ensures result == m::ip_masked_equal_from(address@, base@, mask@, 0)
{
    let mut i: usize = 0;
    while i < address.len()
        invariant
            i <= address.len(),
            address.len() == base.len(),
            base.len() == mask.len(),
            m::ip_masked_equal_from(address@, base@, mask@, 0)
                == m::ip_masked_equal_from(address@, base@, mask@, i as int),
        decreases address.len() - i
    {
        let (Some(a), Some(b), Some(k)) = (address.get(i), base.get(i), mask.get(i)) else { return false; };
        if *a & *k != *b & *k { return false; }
        i = i.saturating_add(1);
    }
    true
}

// ---------------------------------------------------------------------------
// dNSName and iPAddress subtrees
// ---------------------------------------------------------------------------

/// `m::dns_within`, §4.2.1.10.
pub fn dns_within(name: &[u8], base: &[u8]) -> (result: bool)
    ensures super::contract::dns_within_ensures(name@, base@, result)
{
    // 1. An empty base holds every name.
    if base.is_empty() { return true; }
    // 2. Zero labels added.
    if name.len() == base.len() { return folded_equal(name, base); }
    // 4. A shorter name never results from adding labels.
    if name.len() < base.len() { return false; }
    // 3. One or more labels added: "." and then the base.
    let Some(start) = name.len().checked_sub(base.len()) else { return false; };
    let Some(dot_at) = start.checked_sub(1) else { return false; };
    if name.get(dot_at) != Some(&b'.') { return false; }
    let Some(tail) = name.get(start..) else { return false; };
    folded_equal(tail, base)
}

/// `m::dns_wildcard_within`.
pub fn dns_wildcard_within(suffix: &[u8], base: &[u8]) -> (result: bool)
    ensures super::contract::dns_wildcard_within_ensures(suffix@, base@, result)
{
    dns_within(suffix, base)
}

/// `m::dns_wildcard_meets`.
pub fn dns_wildcard_meets(suffix: &[u8], base: &[u8]) -> (result: bool)
    ensures super::contract::dns_wildcard_meets_ensures(suffix@, base@, result)
{
    if dns_within(suffix, base) { return true; }
    let dot = first_dot(base);
    if dot >= base.len() { return false; }
    let Some(after) = dot.checked_add(1) else { return false; };
    let Some(rest) = base.get(after..) else { return false; };
    folded_equal(rest, suffix)
}

/// `m::ip_within`, §4.2.1.10.
pub fn ip_within(address: &[u8], base: &[u8], mask: &[u8]) -> (result: bool)
    ensures super::contract::ip_within_ensures(address@, base@, mask@, result)
{
    if address.len() != base.len() || base.len() != mask.len() { return false; }
    ip_masked_equal(address, base, mask)
}

// ---------------------------------------------------------------------------
// Byte equality and mailboxes
// ---------------------------------------------------------------------------

/// `a@ =~= b@`.
fn bytes_equal(a: &[u8], b: &[u8]) -> (result: bool)
    ensures result == (a@ =~= b@)
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        let (Some(x), Some(y)) = (a.get(i), b.get(i)) else { return false; };
        if *x != *y { return false; }
        i = i.saturating_add(1);
    }
    proof { assert(a@ =~= b@); }
    true
}

/// `m::is_atext`.
fn is_atext(b: u8) -> (result: bool)
    ensures result == m::is_atext(b)
{
    matches!(b, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'!' | b'#' | b'$' | b'%' | b'&' | b'\''
        | b'*' | b'+' | b'-' | b'/' | b'=' | b'?' | b'^' | b'_' | b'`' | b'{' | b'|' | b'}' | b'~')
}

/// `m::dot_atom_text_from(local, 0)`, RFC 5322 §3.2.3.
fn dot_atom_text(local: &[u8]) -> (result: bool)
    ensures result == m::dot_atom_text_from(local@, 0)
{
    let mut i: usize = 0;
    while i < local.len()
        invariant
            i <= local.len(),
            m::dot_atom_text_from(local@, 0) == m::dot_atom_text_from(local@, i as int),
        decreases local.len() - i
    {
        let Some(byte) = local.get(i) else { return false; };
        let next = i.saturating_add(1);
        if *byte == b'.' {
            if i == 0 || next >= local.len() { return false; }
            if local.get(next) == Some(&b'.') { return false; }
        } else {
            if !is_atext(*byte) { return false; }
            if next == local.len() { return true; }
        }
        i = next;
    }
    false
}

/// `m::first_at(mailbox, 0)`.
fn first_at(mailbox: &[u8]) -> (result: usize)
    ensures result as int == m::first_at(mailbox@, 0), result <= mailbox.len()
{
    let mut i: usize = 0;
    while i < mailbox.len()
        invariant
            i <= mailbox.len(),
            m::first_at(mailbox@, 0) == m::first_at(mailbox@, i as int),
        decreases mailbox.len() - i
    {
        let Some(byte) = mailbox.get(i) else { return mailbox.len(); };
        if *byte == b'@' { return i; }
        i = i.saturating_add(1);
    }
    mailbox.len()
}

/// The bytes before the first `@`, `m::mailbox_local`.
fn mailbox_local(mailbox: &[u8]) -> (result: &[u8])
    ensures result@ == m::mailbox_local(mailbox@)
{
    let at = first_at(mailbox);
    match mailbox.get(0..at) {
        Some(local) => local,
        None => mailbox,
    }
}

/// The bytes after the first `@`, `m::mailbox_host`; the mailbox has one.
fn mailbox_host(mailbox: &[u8]) -> (result: &[u8])
    requires m::first_at(mailbox@, 0) < mailbox@.len()
    ensures result@ == m::mailbox_host(mailbox@)
{
    let at = first_at(mailbox);
    let after = at.saturating_add(1);
    match mailbox.get(after..) {
        Some(host) => host,
        None => mailbox,
    }
}

/// `m::is_mailbox`.
fn is_mailbox(mailbox: &[u8]) -> (result: bool)
    ensures result == m::is_mailbox(mailbox@)
{
    let at = first_at(mailbox);
    if at >= mailbox.len() { return false; }
    let local = mailbox_local(mailbox);
    if !dot_atom_text(local) { return false; }
    dns_shape(mailbox_host(mailbox))
}

/// `m::rfc822_base_shape`.
fn rfc822_base_shape(base: &[u8]) -> (result: bool)
    ensures result == m::rfc822_base_shape(base@)
{
    let at = first_at(base);
    if at < base.len() { return is_mailbox(base); }
    if base.first() == Some(&b'.') {
        let Some(rest) = base.get(1..) else { return false; };
        return dns_shape(rest);
    }
    dns_shape(base)
}

/// `m::rfc822_host_within`.
fn rfc822_host_within(host: &[u8], base: &[u8]) -> (result: bool)
    ensures result == m::rfc822_host_within(host@, base@)
{
    if base.first() == Some(&b'.') {
        if host.len() <= base.len() { return false; }
        let Some(start) = host.len().checked_sub(base.len()) else { return false; };
        let Some(tail) = host.get(start..) else { return false; };
        folded_equal(tail, base)
    } else {
        folded_equal(host, base)
    }
}

/// `m::rfc822_within`, §4.2.1.10.
pub fn rfc822_within(local: &[u8], host: &[u8], base: &[u8]) -> (result: bool)
    ensures super::contract::rfc822_within_ensures(local@, host@, base@, result)
{
    let at = first_at(base);
    if at < base.len() {
        bytes_equal(local, mailbox_local(base)) && folded_equal(host, mailbox_host(base))
    } else {
        rfc822_host_within(host, base)
    }
}

/// `m::rfc822_meets`.
pub fn rfc822_meets(local: &[u8], host: &[u8], base: &[u8]) -> (result: bool)
    ensures super::contract::rfc822_meets_ensures(local@, host@, base@, result)
{
    let at = first_at(base);
    if at < base.len() {
        folded_equal(local, mailbox_local(base)) && folded_equal(host, mailbox_host(base))
    } else {
        rfc822_host_within(host, base)
    }
}

// ---------------------------------------------------------------------------
// directoryName subtrees
// ---------------------------------------------------------------------------

/// `tag == m::string_tag(number)`.
fn is_string_tag(tag: clazel_der::spec::Tag, number: u32) -> (result: bool)
    ensures result == (tag == m::string_tag(number))
{
    matches!(tag.class, clazel_der::spec::Class::Universal) && !tag.constructed && tag.number == number
}

/// `a == b` for tags.
fn tag_equal(a: clazel_der::spec::Tag, b: clazel_der::spec::Tag) -> (result: bool)
    ensures result == (a == b)
{
    use clazel_der::spec::Class;
    let same_class = matches!(
        (a.class, b.class),
        (Class::Universal, Class::Universal)
            | (Class::Application, Class::Application)
            | (Class::ContextSpecific, Class::ContextSpecific)
            | (Class::Private, Class::Private)
    );
    same_class && a.constructed == b.constructed && a.number == b.number
}

/// `m::value_tags_compatible`: equal tags, or UTF8String and PrintableString
/// in either order.
fn value_tags_compatible(a: clazel_der::spec::Tag, b: clazel_der::spec::Tag) -> (result: bool)
    ensures result == m::value_tags_compatible(a, b)
{
    let a_text = is_string_tag(a, 12) || is_string_tag(a, 19);
    let b_text = is_string_tag(b, 12) || is_string_tag(b, 19);
    if a_text && b_text { return true; }
    tag_equal(a, b)
}

/// `m::value_contents`: the contents of an attribute value's TLV.
fn value_contents(value_der: &[u8]) -> (result: &[u8])
    ensures result@ == m::value_contents(value_der@)
{
    match der::read_tlv(value_der, 0, value_der.len()) {
        Some(tlv) => match value_der.get(tlv.cstart..tlv.cend) {
            Some(contents) => contents,
            None => value_der,
        },
        None => value_der,
    }
}

/// `m::printable_from(s, 0)`.
fn printable(s: &[u8]) -> (result: bool)
    ensures result == m::printable_from(s@, 0)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            m::printable_from(s@, 0) == m::printable_from(s@, i as int),
        decreases s.len() - i
    {
        let Some(byte) = s.get(i) else { return false; };
        let ok = matches!(*byte, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b' ' | b'\'' | b'(' | b')'
            | b'+' | b',' | b'-' | b'.' | b'/' | b':' | b'=' | b'?');
        if !ok { return false; }
        i = i.saturating_add(1);
    }
    true
}

/// `crate::extensions::spec::ia5_bytes(s, 0)`.
fn ia5(s: &[u8]) -> (result: bool)
    ensures result == crate::extensions::spec::ia5_bytes(s@, 0)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            crate::extensions::spec::ia5_bytes(s@, 0) == crate::extensions::spec::ia5_bytes(s@, i as int),
        decreases s.len() - i
    {
        let Some(byte) = s.get(i) else { return false; };
        if *byte >= 128 { return false; }
        i = i.saturating_add(1);
    }
    true
}

/// `m::value_comparable`: a value both browsers compare byte for byte.
fn value_comparable(attribute: &nm::AttributeTypeAndValue<'_>) -> (result: bool)
    ensures result == m::value_comparable(nm::view_attribute(attribute))
{
    let contents = value_contents(attribute.value_der);
    if is_string_tag(attribute.value_tag, 19) {
        printable(contents)
    } else if is_string_tag(attribute.value_tag, 22) {
        ia5(contents)
    } else {
        !is_string_tag(attribute.value_tag, 28) && !is_string_tag(attribute.value_tag, 30)
    }
}

/// `der::nats(a@) =~= der::nats(b@)`: equal OBJECT IDENTIFIER arcs.
fn oid_equal(a: &[u64], b: &[u64]) -> (result: bool)
    ensures result == (der::nats(a@) =~= der::nats(b@))
{
    if a.len() != b.len() { return false; }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        let (Some(x), Some(y)) = (a.get(i), b.get(i)) else { return false; };
        if *x != *y {
            proof {
                if der::nats(a@) =~= der::nats(b@) {
                    assert(der::nats(a@)[i as int] == der::nats(b@)[i as int]);
                }
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    proof { assert(der::nats(a@) =~= der::nats(b@)); }
    true
}

/// The view of a list of attributes at an index is the view of the element.
proof fn lemma_view_attributes_index(items: Seq<nm::AttributeTypeAndValue<'_>>, k: int)
    requires 0 <= k < items.len(),
    ensures nm::view_attributes(items)[k] == nm::view_attribute(&items[k])
{
    reveal(nm::view_attributes);
}

/// The view of a list of RDNs at an index is the view of the element.
proof fn lemma_view_rdns_index(items: Seq<nm::RelativeDistinguishedName<'_>>, k: int)
    requires 0 <= k < items.len(),
    ensures nm::view_rdns(items)[k] == nm::view_rdn(&items[k])
{
    reveal(nm::view_rdns);
}

/// `m::attribute_match`.
fn attribute_match(base: &nm::AttributeTypeAndValue<'_>, name: &nm::AttributeTypeAndValue<'_>) -> (result: bool)
    ensures result == m::attribute_match(nm::view_attribute(base), nm::view_attribute(name))
{
    oid_equal(base.oid.as_slice(), name.oid.as_slice())
        && value_tags_compatible(base.value_tag, name.value_tag)
        && bytes_equal(value_contents(base.value_der), value_contents(name.value_der))
        && value_comparable(base)
        && value_comparable(name)
}

/// `m::attributes_match`: attribute k of one matches attribute k of the other.
fn attributes_match(base: &[nm::AttributeTypeAndValue<'_>], name: &[nm::AttributeTypeAndValue<'_>]) -> (result: bool)
    ensures result == m::attributes_match(nm::view_attributes(base@), nm::view_attributes(name@))
{
    proof {
        reveal(nm::view_attributes);
        assert(nm::view_attributes(base@).len() == base@.len());
        assert(nm::view_attributes(name@).len() == name@.len());
        super::lemmas::lemma_attributes_match_pointwise(nm::view_attributes(base@), nm::view_attributes(name@));
    }
    if base.len() != name.len() { return false; }
    let mut i: usize = 0;
    while i < base.len()
        invariant
            i <= base.len(),
            base.len() == name.len(),
            nm::view_attributes(base@).len() == base@.len(),
            nm::view_attributes(name@).len() == name@.len(),
            m::attributes_match(nm::view_attributes(base@), nm::view_attributes(name@))
                == (nm::view_attributes(base@).len() == nm::view_attributes(name@).len()
                && forall|k: int| 0 <= k < nm::view_attributes(base@).len() ==> #[trigger] m::attribute_match(
                    nm::view_attributes(base@)[k], nm::view_attributes(name@)[k])),
            forall|j: int| 0 <= j < i ==> #[trigger] m::attribute_match(
                nm::view_attribute(&base@[j]), nm::view_attribute(&name@[j])),
        decreases base.len() - i
    {
        let (Some(b), Some(n)) = (base.get(i), name.get(i)) else { return false; };
        if !attribute_match(b, n) {
            proof {
                lemma_view_attributes_index(base@, i as int);
                lemma_view_attributes_index(name@, i as int);
                assert(!m::attribute_match(nm::view_attributes(base@)[i as int], nm::view_attributes(name@)[i as int]));
                assert(!m::attributes_match(nm::view_attributes(base@), nm::view_attributes(name@)));
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    proof {
        assert forall|k: int| 0 <= k < nm::view_attributes(base@).len() implies
            #[trigger] m::attribute_match(nm::view_attributes(base@)[k], nm::view_attributes(name@)[k]) by {
            lemma_view_attributes_index(base@, k);
            lemma_view_attributes_index(name@, k);
        }
    }
    true
}

/// `m::directory_within`: the base's RDNs are a prefix of the name's, each
/// matching attribute by attribute.
pub fn directory_within(name: &[nm::RelativeDistinguishedName<'_>], base: &[nm::RelativeDistinguishedName<'_>])
    -> (result: bool)
    ensures super::contract::directory_within_ensures(nm::view_rdns(name@), nm::view_rdns(base@), result)
{
    if base.len() > name.len() { return false; }
    proof {
        reveal(nm::view_rdns);
        assert(nm::view_rdns(base@).len() == base@.len());
        assert(nm::view_rdns(name@).len() == name@.len());
        super::lemmas::lemma_rdns_match_pointwise(
            nm::view_rdns(base@), nm::view_rdns(name@).subrange(0, base.len() as int));
    }
    let mut i: usize = 0;
    while i < base.len()
        invariant
            i <= base.len(),
            base.len() <= name.len(),
            nm::view_rdns(base@).len() == base@.len(),
            nm::view_rdns(name@).len() == name@.len(),
            m::rdns_match(nm::view_rdns(base@), nm::view_rdns(name@).subrange(0, base.len() as int))
                == (nm::view_rdns(base@).len() == nm::view_rdns(name@).subrange(0, base.len() as int).len()
                && forall|k: int| 0 <= k < nm::view_rdns(base@).len() ==> #[trigger] m::attributes_match(
                    nm::view_rdns(base@)[k].attributes,
                    nm::view_rdns(name@).subrange(0, base.len() as int)[k].attributes)),
            forall|j: int| 0 <= j < i ==> #[trigger] m::attributes_match(
                nm::view_rdn(&base@[j]).attributes, nm::view_rdn(&name@[j]).attributes),
        decreases base.len() - i
    {
        let (Some(b), Some(n)) = (base.get(i), name.get(i)) else { return false; };
        if !attributes_match(b.attributes.as_slice(), n.attributes.as_slice()) {
            proof {
                lemma_view_rdns_index(base@, i as int);
                lemma_view_rdns_index(name@, i as int);
                assert(!m::attributes_match(nm::view_rdns(base@)[i as int].attributes,
                    nm::view_rdns(name@).subrange(0, base.len() as int)[i as int].attributes));
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    proof {
        assert forall|k: int| 0 <= k < nm::view_rdns(base@).len() implies
            #[trigger] m::attributes_match(nm::view_rdns(base@)[k].attributes,
                nm::view_rdns(name@).subrange(0, base.len() as int)[k].attributes) by {
            lemma_view_rdns_index(base@, k);
            lemma_view_rdns_index(name@, k);
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Names this module matches
// ---------------------------------------------------------------------------

/// A subjectAltName entry of a form this module matches, or a directory name.
pub enum ConstrainedName<'a> {
    /// A dNSName in preferred name syntax.
    Dns(&'a [u8]),
    /// A wildcard dNSName `*.suffix`; the field is `suffix`.
    DnsWildcard(&'a [u8]),
    /// An iPAddress of 4 or 16 octets.
    Ip(&'a [u8]),
    /// An rfc822Name mailbox `local@host`.
    Rfc822 {
        /// The local part, before the `@`.
        local: &'a [u8],
        /// The host, after the `@`.
        host: &'a [u8],
    },
    /// A directory name: the RDNs of a subject or directoryName entry.
    Directory(Vec<nm::RelativeDistinguishedName<'a>>),
}

/// The spec value of a matched name.
pub open spec fn view_constrained_name(name: &ConstrainedName<'_>) -> m::ConstrainedName {
    match name {
        ConstrainedName::Dns(n) => m::ConstrainedName::Dns(n@),
        ConstrainedName::DnsWildcard(s) => m::ConstrainedName::DnsWildcard(s@),
        ConstrainedName::Ip(a) => m::ConstrainedName::Ip(a@),
        ConstrainedName::Rfc822 { local, host } => m::ConstrainedName::Rfc822 { local: local@, host: host@ },
        ConstrainedName::Directory(rdns) => m::ConstrainedName::Directory(nm::view_rdns(rdns@)),
    }
}

impl View for ConstrainedName<'_> {
    type V = m::ConstrainedName;
    closed spec fn view(&self) -> Self::V { view_constrained_name(self) }
}

/// The spec value of an optional matched name.
pub open spec fn view_constrained_name_result(name: Option<ConstrainedName<'_>>) -> Option<m::ConstrainedName> {
    match name {
        Some(n) => Some(view_constrained_name(&n)),
        None => None,
    }
}

/// The contents of a complete GeneralName TLV, `m::general_name_contents`.
fn general_name_contents(der_bytes: &[u8]) -> (result: Option<&[u8]>)
    ensures nm::view_raw_option(result) == m::general_name_contents(der_bytes@)
{
    let tlv = der::read_tlv(der_bytes, 0, der_bytes.len())?;
    if tlv.cend != der_bytes.len() { return None; }
    der_bytes.get(tlv.cstart..tlv.cend)
}

/// `m::is_wildcard_dns_name`, with the suffix after `*.`.
fn wildcard_suffix(name: &[u8]) -> (result: Option<&[u8]>)
    ensures
        result is Some == m::is_wildcard_dns_name(name@),
        result is Some ==> result.unwrap()@ == name@.subrange(2, name@.len() as int),
{
    if name.len() <= 2 { return None; }
    if name.first() != Some(&b'*') || name.get(1) != Some(&b'.') { return None; }
    let rest = name.get(2..)?;
    if dns_shape(rest) { Some(rest) } else { None }
}

/// `m::constrained_name`: the matched form of a subjectAltName entry, or
/// `None` for another form or a malformed one.
pub fn constrained_name<'a>(entry: &ext::GeneralName<'a>) -> (result: Option<ConstrainedName<'a>>)
    ensures super::contract::constrained_name_ensures(ext::view_general_name(entry), view_constrained_name_result(result))
{
    match entry {
        ext::GeneralName::DnsName(name) => {
            if dns_shape(name) { return Some(ConstrainedName::Dns(name)); }
            let suffix = wildcard_suffix(name)?;
            Some(ConstrainedName::DnsWildcard(suffix))
        },
        ext::GeneralName::IpAddress(address) => {
            if address.len() == 4 || address.len() == 16 { Some(ConstrainedName::Ip(address)) } else { None }
        },
        ext::GeneralName::Other(tag, der_bytes) => {
            if *tag == 1 {
                let mailbox = general_name_contents(der_bytes)?;
                if !is_mailbox(mailbox) { return None; }
                Some(ConstrainedName::Rfc822 { local: mailbox_local(mailbox), host: mailbox_host(mailbox) })
            } else if *tag == 4 {
                let contents = general_name_contents(der_bytes)?;
                let parsed = nm::parse_name(contents)?;
                Some(ConstrainedName::Directory(parsed.rdns))
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Within and meets
// ---------------------------------------------------------------------------

/// `m::same_name_type`.
fn same_name_type(name: &ConstrainedName<'_>, base: &nc::GeneralNameConstraint<'_>) -> (result: bool)
    ensures result == m::same_name_type(view_constrained_name(name), nc::view_general_name_constraint(base))
{
    matches!(
        (name, base),
        (ConstrainedName::Dns(_), nc::GeneralNameConstraint::DnsName(_))
            | (ConstrainedName::DnsWildcard(_), nc::GeneralNameConstraint::DnsName(_))
            | (ConstrainedName::Ip(_), nc::GeneralNameConstraint::IpAddress { .. })
            | (ConstrainedName::Rfc822 { .. }, nc::GeneralNameConstraint::Rfc822Name(_))
            | (ConstrainedName::Directory(_), nc::GeneralNameConstraint::DirectoryName(_))
    )
}

/// `m::within`: the name is within the subtree `base`.
pub fn within(name: &ConstrainedName<'_>, base: &nc::GeneralNameConstraint<'_>) -> (result: bool)
    ensures super::contract::within_ensures(view_constrained_name(name), nc::view_general_name_constraint(base), result)
{
    match (name, base) {
        (ConstrainedName::Dns(n), nc::GeneralNameConstraint::DnsName(b)) => dns_within(n, b),
        (ConstrainedName::DnsWildcard(s), nc::GeneralNameConstraint::DnsName(b)) => dns_wildcard_within(s, b),
        (ConstrainedName::Ip(a), nc::GeneralNameConstraint::IpAddress { address, mask }) =>
            ip_within(a, address, mask),
        (ConstrainedName::Rfc822 { local, host }, nc::GeneralNameConstraint::Rfc822Name(b)) =>
            rfc822_within(local, host, b),
        (ConstrainedName::Directory(rdns), nc::GeneralNameConstraint::DirectoryName(b)) =>
            match nm::parse_name(b) {
                Some(parsed) => directory_within(rdns.as_slice(), parsed.rdns.as_slice()),
                None => false,
            },
        _ => false,
    }
}

/// `m::meets`: some name `name` stands for is within `base`.
pub fn meets(name: &ConstrainedName<'_>, base: &nc::GeneralNameConstraint<'_>) -> (result: bool)
    ensures super::contract::meets_ensures(view_constrained_name(name), nc::view_general_name_constraint(base), result)
{
    match (name, base) {
        (ConstrainedName::DnsWildcard(s), nc::GeneralNameConstraint::DnsName(b)) => dns_wildcard_meets(s, b),
        (ConstrainedName::Rfc822 { local, host }, nc::GeneralNameConstraint::Rfc822Name(b)) =>
            rfc822_meets(local, host, b),
        _ => within(name, base),
    }
}

// ---------------------------------------------------------------------------
// Malformed bases
// ---------------------------------------------------------------------------

/// `m::is_prefix_byte`.
fn is_prefix_byte(b: u8) -> (result: bool)
    ensures result == m::is_prefix_byte(b)
{
    b == 0x00 || b == 0x80 || b == 0xC0 || b == 0xE0 || b == 0xF0 || b == 0xF8 || b == 0xFC || b == 0xFE
        || b == 0xFF
}

/// `m::all_zero_from(mask, start)`.
fn all_zero_from(mask: &[u8], start: usize) -> (result: bool)
    requires start <= mask.len()
    ensures result == m::all_zero_from(mask@, start as int)
{
    let mut i: usize = start;
    while i < mask.len()
        invariant
            start <= i <= mask.len(),
            m::all_zero_from(mask@, start as int) == m::all_zero_from(mask@, i as int),
        decreases mask.len() - i
    {
        let Some(byte) = mask.get(i) else { return false; };
        if *byte != 0 { return false; }
        i = i.saturating_add(1);
    }
    true
}

/// `m::mask_contiguous_from(mask, 0)`.
fn mask_contiguous(mask: &[u8]) -> (result: bool)
    ensures result == m::mask_contiguous_from(mask@, 0)
{
    let mut i: usize = 0;
    while i < mask.len()
        invariant
            i <= mask.len(),
            m::mask_contiguous_from(mask@, 0) == m::mask_contiguous_from(mask@, i as int),
        decreases mask.len() - i
    {
        let Some(byte) = mask.get(i) else { return false; };
        let next = i.saturating_add(1);
        if *byte != 0xFF {
            return is_prefix_byte(*byte) && all_zero_from(mask, next);
        }
        i = next;
    }
    true
}

/// `m::base_supported`: the subtree base is well formed.
pub fn base_supported(base: &nc::GeneralNameConstraint<'_>) -> (result: bool)
    ensures super::contract::base_supported_ensures(nc::view_general_name_constraint(base), result)
{
    match base {
        nc::GeneralNameConstraint::DnsName(b) => b.is_empty() || dns_shape(b),
        nc::GeneralNameConstraint::IpAddress { address, mask } =>
            (address.len() == 4 || address.len() == 16) && mask.len() == address.len() && mask_contiguous(mask),
        nc::GeneralNameConstraint::Rfc822Name(b) => rfc822_base_shape(b),
        nc::GeneralNameConstraint::DirectoryName(b) => nm::parse_name(b).is_some(),
        nc::GeneralNameConstraint::Unsupported { .. } => true,
    }
}

// ---------------------------------------------------------------------------
// Lists: views and prefixes
// ---------------------------------------------------------------------------

/// The state as the spec sees it: the decoded NameConstraints of the path so
/// far, in order.
pub open spec fn view_state(items: Seq<&nc::NameConstraints<'_>>) -> Seq<crate::name_constraints::spec::NameConstraints> {
    items.map(|_i: int, item: &nc::NameConstraints<'_>| nc::view_name_constraints(item))
}

/// The last element of the first `j` is element `j - 1`, and dropping it
/// leaves the first `j - 1`.
proof fn lemma_take_last<T>(s: Seq<T>, j: int)
    requires 0 < j <= s.len(),
    ensures
        s.take(j).len() == j,
        s.take(j).last() == s[j - 1],
        s.take(j).drop_last() =~= s.take(j - 1),
{
}

proof fn lemma_take_all<T>(s: Seq<T>)
    ensures s.take(s.len() as int) == s
{
    assert(s.take(s.len() as int) =~= s);
}

proof fn lemma_subtrees_view(items: Seq<nc::GeneralSubtree<'_>>)
    ensures
        nc::view_subtrees(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] nc::view_subtrees(items)[k] == nc::view_general_subtree(&items[k]),
{
    reveal(nc::view_subtrees);
}

proof fn lemma_state_view(items: Seq<&nc::NameConstraints<'_>>)
    ensures
        view_state(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] view_state(items)[k] == nc::view_name_constraints(items[k]),
{
}

proof fn lemma_path_view(items: Seq<NcCertificate<'_>>)
    ensures
        view_path(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] view_path(items)[k] == view_nc_certificate(&items[k]),
{
}

proof fn lemma_names_view(items: Seq<ext::GeneralName<'_>>)
    ensures
        ext::view_general_names(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] ext::view_general_names(items)[k] == ext::view_general_name(&items[k]),
{
}

proof fn lemma_rdns_view(items: Seq<nm::RelativeDistinguishedName<'_>>)
    ensures
        nm::view_rdns(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] nm::view_rdns(items)[k] == nm::view_rdn(&items[k]),
{
    reveal(nm::view_rdns);
}

proof fn lemma_attributes_view(items: Seq<nm::AttributeTypeAndValue<'_>>)
    ensures
        nm::view_attributes(items).len() == items.len(),
        forall|k: int| 0 <= k < items.len() ==>
            #[trigger] nm::view_attributes(items)[k] == nm::view_attribute(&items[k]),
{
    reveal(nm::view_attributes);
}

// ---------------------------------------------------------------------------
// Lists of subtrees
// ---------------------------------------------------------------------------

/// `m::subtrees_supported`: every base is well formed.
fn subtrees_supported(items: &[nc::GeneralSubtree<'_>]) -> (result: bool)
    ensures result == m::subtrees_supported(nc::view_subtrees(items@))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::subtrees_supported(nc::view_subtrees(items@))
                == m::subtrees_supported(nc::view_subtrees(items@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if !base_supported(&item.base) { return false; }
        j = k;
    }
    true
}

/// `m::has_directory_name_base`.
fn has_directory_name_base(items: &[nc::GeneralSubtree<'_>]) -> (result: bool)
    ensures result == m::has_directory_name_base(nc::view_subtrees(items@))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::has_directory_name_base(nc::view_subtrees(items@))
                == m::has_directory_name_base(nc::view_subtrees(items@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if matches!(item.base, nc::GeneralNameConstraint::DirectoryName(_)) { return true; }
        j = k;
    }
    false
}

/// `m::has_base_of_type`: some base has the name's type.
fn has_base_of_type(items: &[nc::GeneralSubtree<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures result == m::has_base_of_type(nc::view_subtrees(items@), view_constrained_name(name))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::has_base_of_type(nc::view_subtrees(items@), view_constrained_name(name))
                == m::has_base_of_type(nc::view_subtrees(items@).take(j as int), view_constrained_name(name)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if same_name_type(name, &item.base) { return true; }
        j = k;
    }
    false
}

/// `m::within_some`: the name is within some base.
fn within_some(items: &[nc::GeneralSubtree<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures result == m::within_some(nc::view_subtrees(items@), view_constrained_name(name))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::within_some(nc::view_subtrees(items@), view_constrained_name(name))
                == m::within_some(nc::view_subtrees(items@).take(j as int), view_constrained_name(name)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if within(name, &item.base) { return true; }
        j = k;
    }
    false
}

/// `m::meets_some`: the name meets some base.
fn meets_some(items: &[nc::GeneralSubtree<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures result == m::meets_some(nc::view_subtrees(items@), view_constrained_name(name))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::meets_some(nc::view_subtrees(items@), view_constrained_name(name))
                == m::meets_some(nc::view_subtrees(items@).take(j as int), view_constrained_name(name)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if meets(name, &item.base) { return true; }
        j = k;
    }
    false
}

/// `m::has_base_of_form`: some base is of the uninterpreted form `tag`.
fn has_base_of_form(items: &[nc::GeneralSubtree<'_>], tag: u32) -> (result: bool)
    ensures result == m::has_base_of_form(nc::view_subtrees(items@), tag)
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::has_base_of_form(nc::view_subtrees(items@), tag)
                == m::has_base_of_form(nc::view_subtrees(items@).take(j as int), tag),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        match item.base {
            nc::GeneralNameConstraint::Unsupported { tag: t, .. } if t == tag => return true,
            _ => {},
        }
        j = k;
    }
    false
}

/// `m::has_rfc822_base`.
fn has_rfc822_base(items: &[nc::GeneralSubtree<'_>]) -> (result: bool)
    ensures result == m::has_rfc822_base(nc::view_subtrees(items@))
{
    proof { lemma_subtrees_view(items@); lemma_take_all(nc::view_subtrees(items@)); }
    let mut j: usize = items.len();
    while j > 0
        invariant
            j <= items.len(),
            nc::view_subtrees(items@).len() == items.len(),
            forall|k: int| 0 <= k < items.len() ==>
                #[trigger] nc::view_subtrees(items@)[k] == nc::view_general_subtree(&items@[k]),
            m::has_rfc822_base(nc::view_subtrees(items@))
                == m::has_rfc822_base(nc::view_subtrees(items@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(item) = items.get(k) else { return false; };
        proof { lemma_take_last(nc::view_subtrees(items@), j as int); }
        if matches!(item.base, nc::GeneralNameConstraint::Rfc822Name(_)) { return true; }
        j = k;
    }
    false
}

// ---------------------------------------------------------------------------
// One NameConstraints value, and the state
// ---------------------------------------------------------------------------

/// `m::constraints_supported`: a NameConstraints value this module can apply.
pub fn constraints_supported(value: &nc::NameConstraints<'_>) -> (result: bool)
    ensures super::contract::constraints_supported_ensures(nc::view_name_constraints(value), result)
{
    if value.permitted_subtrees.is_none() && value.excluded_subtrees.is_none() { return false; }
    let permitted_ok = match &value.permitted_subtrees {
        Some(items) => subtrees_supported(items.as_slice()),
        None => true,
    };
    let excluded_ok = match &value.excluded_subtrees {
        Some(items) => subtrees_supported(items.as_slice()) && !has_directory_name_base(items.as_slice()),
        None => true,
    };
    permitted_ok && excluded_ok
}

/// `m::permitted_by`.
fn permitted_by(value: &nc::NameConstraints<'_>, name: &ConstrainedName<'_>) -> (result: bool)
    ensures result == m::permitted_by(nc::view_name_constraints(value), view_constrained_name(name))
{
    match &value.permitted_subtrees {
        None => true,
        Some(items) => !has_base_of_type(items.as_slice(), name) || within_some(items.as_slice(), name),
    }
}

/// `m::excluded_by`.
fn excluded_by(value: &nc::NameConstraints<'_>, name: &ConstrainedName<'_>) -> (result: bool)
    ensures result == m::excluded_by(nc::view_name_constraints(value), view_constrained_name(name))
{
    match &value.excluded_subtrees {
        None => false,
        Some(items) => meets_some(items.as_slice(), name),
    }
}

/// `m::within_permitted_subtrees`, §6.1.2 (b): the name is within every
/// set's permitted subtrees of its type.
pub fn within_permitted_subtrees(state: &[&nc::NameConstraints<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures super::contract::within_permitted_subtrees_ensures(view_state(state@), view_constrained_name(name), result)
{
    proof { lemma_state_view(state@); lemma_take_all(view_state(state@)); }
    let mut j: usize = state.len();
    while j > 0
        invariant
            j <= state.len(),
            view_state(state@).len() == state.len(),
            forall|k: int| 0 <= k < state.len() ==>
                #[trigger] view_state(state@)[k] == nc::view_name_constraints(state@[k]),
            m::within_permitted_subtrees(view_state(state@), view_constrained_name(name))
                == m::within_permitted_subtrees(view_state(state@).take(j as int), view_constrained_name(name)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(set) = state.get(k) else { return false; };
        proof { lemma_take_last(view_state(state@), j as int); }
        if !permitted_by(set, name) { return false; }
        j = k;
    }
    true
}

/// `m::within_excluded_subtrees`, §6.1.2 (c): the name meets some set's
/// excluded subtrees.
pub fn within_excluded_subtrees(state: &[&nc::NameConstraints<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures super::contract::within_excluded_subtrees_ensures(view_state(state@), view_constrained_name(name), result)
{
    proof { lemma_state_view(state@); lemma_take_all(view_state(state@)); }
    let mut j: usize = state.len();
    while j > 0
        invariant
            j <= state.len(),
            view_state(state@).len() == state.len(),
            forall|k: int| 0 <= k < state.len() ==>
                #[trigger] view_state(state@)[k] == nc::view_name_constraints(state@[k]),
            m::within_excluded_subtrees(view_state(state@), view_constrained_name(name))
                == m::within_excluded_subtrees(view_state(state@).take(j as int), view_constrained_name(name)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(set) = state.get(k) else { return false; };
        proof { lemma_take_last(view_state(state@), j as int); }
        if excluded_by(set, name) { return true; }
        j = k;
    }
    false
}

/// `m::name_acceptable`: within permitted_subtrees and not within excluded_subtrees.
pub fn name_acceptable(state: &[&nc::NameConstraints<'_>], name: &ConstrainedName<'_>) -> (result: bool)
    ensures super::contract::name_acceptable_ensures(view_state(state@), view_constrained_name(name), result)
{
    within_permitted_subtrees(state, name) && !within_excluded_subtrees(state, name)
}

/// `m::form_constrained`: some set has a base of the uninterpreted form `tag`.
fn form_constrained(state: &[&nc::NameConstraints<'_>], tag: u32) -> (result: bool)
    ensures result == m::form_constrained(view_state(state@), tag)
{
    proof { lemma_state_view(state@); lemma_take_all(view_state(state@)); }
    let mut j: usize = state.len();
    while j > 0
        invariant
            j <= state.len(),
            view_state(state@).len() == state.len(),
            forall|k: int| 0 <= k < state.len() ==>
                #[trigger] view_state(state@)[k] == nc::view_name_constraints(state@[k]),
            m::form_constrained(view_state(state@), tag)
                == m::form_constrained(view_state(state@).take(j as int), tag),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(set) = state.get(k) else { return false; };
        proof { lemma_take_last(view_state(state@), j as int); }
        let in_permitted = match &set.permitted_subtrees {
            Some(items) => has_base_of_form(items.as_slice(), tag),
            None => false,
        };
        let in_excluded = match &set.excluded_subtrees {
            Some(items) => has_base_of_form(items.as_slice(), tag),
            None => false,
        };
        if in_permitted || in_excluded { return true; }
        j = k;
    }
    false
}

/// `m::rfc822_in_force`: some set has an rfc822Name base, in either list.
fn rfc822_in_force(state: &[&nc::NameConstraints<'_>]) -> (result: bool)
    ensures result == m::rfc822_in_force(view_state(state@))
{
    proof { lemma_state_view(state@); lemma_take_all(view_state(state@)); }
    let mut j: usize = state.len();
    while j > 0
        invariant
            j <= state.len(),
            view_state(state@).len() == state.len(),
            forall|k: int| 0 <= k < state.len() ==>
                #[trigger] view_state(state@)[k] == nc::view_name_constraints(state@[k]),
            m::rfc822_in_force(view_state(state@)) == m::rfc822_in_force(view_state(state@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(set) = state.get(k) else { return false; };
        proof { lemma_take_last(view_state(state@), j as int); }
        let in_permitted = match &set.permitted_subtrees {
            Some(items) => has_rfc822_base(items.as_slice()),
            None => false,
        };
        let in_excluded = match &set.excluded_subtrees {
            Some(items) => has_rfc822_base(items.as_slice()),
            None => false,
        };
        if in_permitted || in_excluded { return true; }
        j = k;
    }
    false
}

/// The spec value of an optional NameConstraints.
pub open spec fn view_extension(value: Option<&nc::NameConstraints<'_>>)
    -> Option<crate::name_constraints::spec::NameConstraints>
{
    match value {
        Some(v) => Some(nc::view_name_constraints(v)),
        None => None,
    }
}

/// `m::prepare_name_constraints`, §6.1.4 (g): add the certificate's set to
/// the state. When it is refused the state is left as it was.
pub fn prepare_name_constraints<'a>(
    state: &mut Vec<&'a nc::NameConstraints<'a>>,
    extension: Option<&'a nc::NameConstraints<'a>>,
) -> (accepted: bool)
    ensures
        super::contract::prepare_name_constraints_ensures(
            view_state(old(state)@), view_extension(extension), accepted, view_state(final(state)@)),
{
    match extension {
        None => true,
        Some(value) => {
            if constraints_supported(value) {
                state.push(value);
                proof {
                    assert(view_state(state@) =~= view_state(old(state)@).push(nc::view_name_constraints(value)));
                }
                true
            } else {
                false
            }
        },
    }
}

// ---------------------------------------------------------------------------
// One certificate
// ---------------------------------------------------------------------------

/// `m::is_uninterpreted_form`.
fn is_uninterpreted_form(tag: u32) -> (result: bool)
    ensures result == m::is_uninterpreted_form(tag)
{
    tag == 0 || tag == 3 || tag == 5 || tag == 6 || tag == 8
}

/// `m::entry_well_formed`.
fn entry_well_formed(entry: &ext::GeneralName<'_>) -> (result: bool)
    ensures result == m::entry_well_formed(ext::view_general_name(entry))
{
    if constrained_name(entry).is_some() { return true; }
    match entry {
        ext::GeneralName::Other(tag, _) => is_uninterpreted_form(*tag),
        _ => false,
    }
}

/// `m::names_well_formed`: every entry is well formed.
pub fn names_well_formed(names: &[ext::GeneralName<'_>]) -> (result: bool)
    ensures super::contract::names_well_formed_ensures(ext::view_general_names(names@), result)
{
    proof { lemma_names_view(names@); lemma_take_all(ext::view_general_names(names@)); }
    let mut j: usize = names.len();
    while j > 0
        invariant
            j <= names.len(),
            ext::view_general_names(names@).len() == names.len(),
            forall|k: int| 0 <= k < names.len() ==>
                #[trigger] ext::view_general_names(names@)[k] == ext::view_general_name(&names@[k]),
            m::names_well_formed(ext::view_general_names(names@))
                == m::names_well_formed(ext::view_general_names(names@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(entry) = names.get(k) else { return false; };
        proof { lemma_take_last(ext::view_general_names(names@), j as int); }
        if !entry_well_formed(entry) { return false; }
        j = k;
    }
    true
}

/// `m::names_of_unconstrained_forms`: no entry is of an uninterpreted form
/// that some set constrains.
pub fn names_of_unconstrained_forms(state: &[&nc::NameConstraints<'_>], names: &[ext::GeneralName<'_>])
    -> (result: bool)
    ensures super::contract::names_of_unconstrained_forms_ensures(
        view_state(state@), ext::view_general_names(names@), result)
{
    proof { lemma_names_view(names@); lemma_take_all(ext::view_general_names(names@)); }
    let mut j: usize = names.len();
    while j > 0
        invariant
            j <= names.len(),
            ext::view_general_names(names@).len() == names.len(),
            forall|k: int| 0 <= k < names.len() ==>
                #[trigger] ext::view_general_names(names@)[k] == ext::view_general_name(&names@[k]),
            m::names_of_unconstrained_forms(view_state(state@), ext::view_general_names(names@))
                == m::names_of_unconstrained_forms(view_state(state@),
                    ext::view_general_names(names@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(entry) = names.get(k) else { return false; };
        proof { lemma_take_last(ext::view_general_names(names@), j as int); }
        match entry {
            ext::GeneralName::Other(tag, _) if is_uninterpreted_form(*tag) && form_constrained(state, *tag) =>
                return false,
            _ => {},
        }
        j = k;
    }
    true
}

/// `m::names_within_permitted`, §6.1.3 (b).
pub fn names_within_permitted(state: &[&nc::NameConstraints<'_>], names: &[ext::GeneralName<'_>]) -> (result: bool)
    ensures super::contract::names_within_permitted_ensures(view_state(state@), ext::view_general_names(names@), result)
{
    proof { lemma_names_view(names@); lemma_take_all(ext::view_general_names(names@)); }
    let mut j: usize = names.len();
    while j > 0
        invariant
            j <= names.len(),
            ext::view_general_names(names@).len() == names.len(),
            forall|k: int| 0 <= k < names.len() ==>
                #[trigger] ext::view_general_names(names@)[k] == ext::view_general_name(&names@[k]),
            m::names_within_permitted(view_state(state@), ext::view_general_names(names@))
                == m::names_within_permitted(view_state(state@), ext::view_general_names(names@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(entry) = names.get(k) else { return false; };
        proof { lemma_take_last(ext::view_general_names(names@), j as int); }
        match constrained_name(entry) {
            Some(name) if !within_permitted_subtrees(state, &name) => return false,
            _ => {},
        }
        j = k;
    }
    true
}

/// `m::names_not_excluded`, §6.1.3 (c).
pub fn names_not_excluded(state: &[&nc::NameConstraints<'_>], names: &[ext::GeneralName<'_>]) -> (result: bool)
    ensures super::contract::names_not_excluded_ensures(view_state(state@), ext::view_general_names(names@), result)
{
    proof { lemma_names_view(names@); lemma_take_all(ext::view_general_names(names@)); }
    let mut j: usize = names.len();
    while j > 0
        invariant
            j <= names.len(),
            ext::view_general_names(names@).len() == names.len(),
            forall|k: int| 0 <= k < names.len() ==>
                #[trigger] ext::view_general_names(names@)[k] == ext::view_general_name(&names@[k]),
            m::names_not_excluded(view_state(state@), ext::view_general_names(names@))
                == m::names_not_excluded(view_state(state@), ext::view_general_names(names@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(entry) = names.get(k) else { return false; };
        proof { lemma_take_last(ext::view_general_names(names@), j as int); }
        match constrained_name(entry) {
            Some(name) if within_excluded_subtrees(state, &name) => return false,
            _ => {},
        }
        j = k;
    }
    true
}

/// `m::certificate_names_acceptable`: §6.1.3 (b) and (c) for the
/// subjectAltName entries.
pub fn certificate_names_acceptable(state: &[&nc::NameConstraints<'_>], names: &[ext::GeneralName<'_>])
    -> (result: bool)
    ensures super::contract::certificate_names_acceptable_ensures(
        view_state(state@), ext::view_general_names(names@), result)
{
    (state.is_empty() || names_well_formed(names))
        && names_within_permitted(state, names)
        && names_not_excluded(state, names)
        && names_of_unconstrained_forms(state, names)
}

/// PKCS #9 emailAddress, `1.2.840.113549.1.9.1`.
fn oid_is_email(oid: &[u64]) -> (result: bool)
    ensures result == (der::nats(oid@) =~= m::email_address_oid())
{
    let email: [u64; 7] = [1, 2, 840, 113549, 1, 9, 1];
    proof { assert(der::nats(email@) =~= m::email_address_oid()); }
    oid_equal(oid, email.as_slice())
}

/// `m::attributes_have_email`.
fn attributes_have_email(attributes: &[nm::AttributeTypeAndValue<'_>]) -> (result: bool)
    ensures result == m::attributes_have_email(nm::view_attributes(attributes@))
{
    proof { lemma_attributes_view(attributes@); lemma_take_all(nm::view_attributes(attributes@)); }
    let mut j: usize = attributes.len();
    while j > 0
        invariant
            j <= attributes.len(),
            nm::view_attributes(attributes@).len() == attributes.len(),
            forall|k: int| 0 <= k < attributes.len() ==>
                #[trigger] nm::view_attributes(attributes@)[k] == nm::view_attribute(&attributes@[k]),
            m::attributes_have_email(nm::view_attributes(attributes@))
                == m::attributes_have_email(nm::view_attributes(attributes@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(attribute) = attributes.get(k) else { return false; };
        proof { lemma_take_last(nm::view_attributes(attributes@), j as int); }
        if oid_is_email(attribute.oid.as_slice()) { return true; }
        j = k;
    }
    false
}

/// `m::rdns_have_email`.
fn rdns_have_email(rdns: &[nm::RelativeDistinguishedName<'_>]) -> (result: bool)
    ensures result == m::rdns_have_email(nm::view_rdns(rdns@))
{
    proof { lemma_rdns_view(rdns@); lemma_take_all(nm::view_rdns(rdns@)); }
    let mut j: usize = rdns.len();
    while j > 0
        invariant
            j <= rdns.len(),
            nm::view_rdns(rdns@).len() == rdns.len(),
            forall|k: int| 0 <= k < rdns.len() ==>
                #[trigger] nm::view_rdns(rdns@)[k] == nm::view_rdn(&rdns@[k]),
            m::rdns_have_email(nm::view_rdns(rdns@)) == m::rdns_have_email(nm::view_rdns(rdns@).take(j as int)),
        decreases j
    {
        let Some(k) = j.checked_sub(1) else { return false; };
        let Some(rdn) = rdns.get(k) else { return false; };
        proof { lemma_take_last(nm::view_rdns(rdns@), j as int); }
        if attributes_have_email(rdn.attributes.as_slice()) { return true; }
        j = k;
    }
    false
}

/// `m::subject_acceptable`: §6.1.3 (b) and (c) for the subject field, given
/// as the complete Name TLV.
pub fn subject_acceptable(state: &[&nc::NameConstraints<'_>], subject: &[u8]) -> (result: bool)
    ensures super::contract::subject_acceptable_ensures(view_state(state@), subject@, result)
{
    if state.is_empty() { return true; }
    let Some(parsed) = nm::parse_name(subject) else { return false; };
    let has_email = rdns_have_email(parsed.rdns.as_slice());
    let name = ConstrainedName::Directory(parsed.rdns);
    if !name_acceptable(state, &name) { return false; }
    !(rfc822_in_force(state) && has_email)
}

/// What §6.1.3 (b), (c) and §6.1.4 (g) read from one certificate.
pub struct NcCertificate<'a> {
    /// The complete subject Name TLV.
    pub subject: &'a [u8],
    /// The subjectAltName entries, in order; empty when there is none.
    pub subject_alt_names: &'a [ext::GeneralName<'a>],
    /// The decoded NameConstraints extension, if present.
    pub name_constraints: Option<&'a nc::NameConstraints<'a>>,
}

impl View for NcCertificate<'_> {
    type V = m::NcCertificate;
    closed spec fn view(&self) -> Self::V { view_nc_certificate(self) }
}

/// The spec value of a certificate.
pub open spec fn view_nc_certificate(certificate: &NcCertificate<'_>) -> m::NcCertificate {
    m::NcCertificate {
        subject: certificate.subject@,
        subject_alt_names: ext::view_general_names(certificate.subject_alt_names@),
        name_constraints: view_extension(certificate.name_constraints),
    }
}

/// The spec value of a path.
pub open spec fn view_path(items: Seq<NcCertificate<'_>>) -> Seq<m::NcCertificate> {
    items.map(|_i: int, item: NcCertificate<'_>| view_nc_certificate(&item))
}

/// `m::certificate_acceptable`: §6.1.3 (b) and (c) for one certificate.
pub fn certificate_acceptable(state: &[&nc::NameConstraints<'_>], certificate: &NcCertificate<'_>) -> (result: bool)
    ensures super::contract::certificate_acceptable_ensures(view_state(state@), view_nc_certificate(certificate), result)
{
    certificate_names_acceptable(state, certificate.subject_alt_names)
        && subject_acceptable(state, certificate.subject)
}

// ---------------------------------------------------------------------------
// The comparison bound (design §1.12) and the path
// ---------------------------------------------------------------------------

/// `acc` plus the subtrees of one set, or `None` if that exceeds `usize::MAX`.
fn add_subtrees(value: &nc::NameConstraints<'_>, acc: usize) -> (result: Option<usize>)
    ensures
        match result {
            Some(total) => total as nat == acc as nat + super::contract::subtrees_in(nc::view_name_constraints(value)),
            None => acc as nat + super::contract::subtrees_in(nc::view_name_constraints(value)) > usize::MAX,
        }
{
    let permitted = match &value.permitted_subtrees {
        Some(items) => items.len(),
        None => 0,
    };
    let excluded = match &value.excluded_subtrees {
        Some(items) => items.len(),
        None => 0,
    };
    let with_permitted = acc.checked_add(permitted)?;
    with_permitted.checked_add(excluded)
}

/// `super::contract::subtree_count(state)`, or `None` if it exceeds `usize::MAX`.
fn subtree_count(state: &[&nc::NameConstraints<'_>]) -> (result: Option<usize>)
    ensures
        match result {
            Some(total) => total as nat == super::contract::subtree_count(view_state(state@)),
            None => super::contract::subtree_count(view_state(state@)) > usize::MAX,
        }
{
    proof { lemma_state_view(state@); lemma_take_all(view_state(state@)); }
    let mut acc: usize = 0;
    let mut j: usize = state.len();
    while j > 0
        invariant
            j <= state.len(),
            view_state(state@).len() == state.len(),
            forall|k: int| 0 <= k < state.len() ==>
                #[trigger] view_state(state@)[k] == nc::view_name_constraints(state@[k]),
            acc as nat + super::contract::subtree_count(view_state(state@).take(j as int))
                == super::contract::subtree_count(view_state(state@)),
        decreases j
    {
        let k = j.checked_sub(1)?;
        let set = state.get(k)?;
        proof { lemma_take_last(view_state(state@), j as int); }
        acc = add_subtrees(set, acc)?;
        j = k;
    }
    Some(acc)
}

proof fn lemma_mul_at_least(a: nat, c: nat)
    requires a >= 1, c >= 1,
    ensures a * c >= a, a * c >= c,
{
    assert(a * c >= a * 1) by (nonlinear_arith) requires c >= 1;
    assert(a * c >= 1 * c) by (nonlinear_arith) requires a >= 1;
}

/// The comparisons spent after one more certificate, or `None` if that is
/// beyond the bound: `spent` plus `super::contract::comparisons(entries, subtrees)`.
fn charge(state: &[&nc::NameConstraints<'_>], entries: usize, spent: usize) -> (result: Option<usize>)
    requires super::contract::within_comparison_bound(spent as nat),
    ensures
        match result {
            Some(total) => total as nat == spent as nat
                    + super::contract::comparisons(entries as nat, super::contract::subtree_count(view_state(state@)))
                && super::contract::within_comparison_bound(total as nat),
            None => !super::contract::within_comparison_bound(spent as nat
                + super::contract::comparisons(entries as nat, super::contract::subtree_count(view_state(state@)))),
        }
{
    let Some(count) = subtree_count(state) else {
        proof {
            lemma_mul_at_least(entries as nat + 1, super::contract::subtree_count(view_state(state@)));
        }
        return None;
    };
    if count == 0 { return Some(spent); }
    // (entries + 1) * count: one subject and `entries` subjectAltName entries
    let Some(names) = entries.checked_add(1) else {
        proof { lemma_mul_at_least(entries as nat + 1, count as nat); }
        return None;
    };
    let cost = names.checked_mul(count)?;
    let total = spent.checked_add(cost)?;
    if total > 4096 { return None; }
    Some(total)
}

/// Moving from certificate `i` to `i + 1`: the check passed, and so did
/// §6.1.4 (g) unless `i` is the last certificate.
proof fn lemma_names_constrained_advance(
    steps: Seq<m::NcCertificate>,
    i: int,
    before: Seq<crate::name_constraints::spec::NameConstraints>,
    after: Seq<crate::name_constraints::spec::NameConstraints>,
)
    requires
        0 <= i < steps.len(),
        m::certificate_acceptable(before, steps[i]),
        i == steps.len() - 1 || m::prepare_name_constraints(before, steps[i].name_constraints) == Some(after),
    ensures
        m::names_constrained_from(steps, i, before) == m::names_constrained_from(steps, i + 1, after),
{
}

/// As [`lemma_names_constrained_advance`], for the comparison bound.
proof fn lemma_within_budget_advance(
    steps: Seq<m::NcCertificate>,
    i: int,
    before: Seq<crate::name_constraints::spec::NameConstraints>,
    after: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
    total: nat,
)
    requires
        0 <= i < steps.len(),
        total == spent + super::contract::certificate_comparisons(before, steps[i]),
        super::contract::within_comparison_bound(total),
        i == steps.len() - 1 || m::prepare_name_constraints(before, steps[i].name_constraints) == Some(after),
    ensures
        super::contract::within_budget_from(steps, i, before, spent) == super::contract::within_budget_from(steps, i + 1, after, total),
{
}

/// A certificate that fails the bound, the check or the preparation refuses
/// the path.
proof fn lemma_refusal(
    steps: Seq<m::NcCertificate>,
    i: int,
    before: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
)
    requires
        0 <= i < steps.len(),
        !({
            &&& super::contract::within_comparison_bound(spent + super::contract::certificate_comparisons(before, steps[i]))
            &&& m::certificate_acceptable(before, steps[i])
            &&& i == steps.len() - 1 || m::prepare_name_constraints(before, steps[i].name_constraints) is Some
        }),
    ensures
        !(m::names_constrained_from(steps, i, before) && super::contract::within_budget_from(steps, i, before, spent)),
{
}

/// The spec accepts the path, within the bound.
#[verifier::opaque]
spec fn path_accepted(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
) -> bool {
    m::names_constrained_from(steps, 0, start) && super::contract::within_budget_from(steps, 0, start, 0)
}

/// The loop's invariant: the spec's verdict on the whole path, and the
/// bound's, equal their verdicts on the certificates from `i` on, under the
/// state and the comparisons spent so far.
#[verifier::opaque]
spec fn progress(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
) -> bool {
    &&& m::names_constrained_from(steps, 0, start) == m::names_constrained_from(steps, i, state)
    &&& super::contract::within_budget_from(steps, 0, start, 0) == super::contract::within_budget_from(steps, i, state, spent)
}

proof fn lemma_progress_start(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
)
    ensures progress(steps, start, 0, start, 0),
{
    reveal(progress);
}

proof fn lemma_progress_advance(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
    before: Seq<crate::name_constraints::spec::NameConstraints>,
    after: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
    total: nat,
)
    requires
        progress(steps, start, i, before, spent),
        0 <= i < steps.len(),
        m::certificate_acceptable(before, steps[i]),
        total == spent + super::contract::certificate_comparisons(before, steps[i]),
        super::contract::within_comparison_bound(total),
        i == steps.len() - 1 || m::prepare_name_constraints(before, steps[i].name_constraints) == Some(after),
    ensures progress(steps, start, i + 1, after, total),
{
    reveal(progress);
    lemma_names_constrained_advance(steps, i, before, after);
    lemma_within_budget_advance(steps, i, before, after, spent, total);
}

proof fn lemma_progress_refusal(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
    before: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
)
    requires
        progress(steps, start, i, before, spent),
        0 <= i < steps.len(),
        !({
            &&& super::contract::within_comparison_bound(spent + super::contract::certificate_comparisons(before, steps[i]))
            &&& m::certificate_acceptable(before, steps[i])
            &&& i == steps.len() - 1 || m::prepare_name_constraints(before, steps[i].name_constraints) is Some
        }),
    ensures !path_accepted(steps, start),
{
    reveal(progress);
    reveal(path_accepted);
    lemma_refusal(steps, i, before, spent);
}

proof fn lemma_progress_done(
    steps: Seq<m::NcCertificate>,
    start: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
)
    requires progress(steps, start, i, state, spent), i >= steps.len(),
    ensures path_accepted(steps, start),
{
    reveal(progress);
    reveal(path_accepted);
}

/// One certificate of the path: charge its comparisons, check §6.1.3 (b) and
/// (c) and, unless it is the last, apply §6.1.4 (g). `Some(total)` is the
/// comparisons spent so far; `None` says the bound, the check or the
/// preparation refused.
fn check_certificate<'a>(
    state: &mut Vec<&'a nc::NameConstraints<'a>>,
    certificate: &NcCertificate<'a>,
    last: bool,
    spent: usize,
) -> (result: Option<usize>)
    requires super::contract::within_comparison_bound(spent as nat),
    ensures
        match result {
            Some(total) => {
                &&& total as nat == spent as nat
                    + super::contract::certificate_comparisons(view_state(old(state)@), view_nc_certificate(certificate))
                &&& super::contract::within_comparison_bound(total as nat)
                &&& m::certificate_acceptable(view_state(old(state)@), view_nc_certificate(certificate))
                &&& last || m::prepare_name_constraints(
                    view_state(old(state)@), view_extension(certificate.name_constraints))
                    == Some(view_state(final(state)@))
            },
            None => !({
                &&& super::contract::within_comparison_bound(spent as nat
                    + super::contract::certificate_comparisons(view_state(old(state)@), view_nc_certificate(certificate)))
                &&& m::certificate_acceptable(view_state(old(state)@), view_nc_certificate(certificate))
                &&& last || m::prepare_name_constraints(
                    view_state(old(state)@), view_extension(certificate.name_constraints)) is Some
            }),
        }
{
    proof { lemma_names_view(certificate.subject_alt_names@); }
    let total = charge(state.as_slice(), certificate.subject_alt_names.len(), spent)?;
    if !certificate_acceptable(state.as_slice(), certificate) { return None; }
    if !last && !prepare_name_constraints(state, certificate.name_constraints) { return None; }
    Some(total)
}

/// `m::names_constrained` for a whole path, first certificate first,
/// starting from the state `initial` (normally empty), refusing a path that
/// takes more than 4,096 comparisons (design §1.12): see
/// [`super::contract::names_constrained_ensures`].
pub fn names_constrained<'a>(path: &[NcCertificate<'a>], initial: Vec<&'a nc::NameConstraints<'a>>) -> (result: bool)
    ensures super::contract::names_constrained_ensures(view_path(path@), view_state(initial@), result)
{
    proof { lemma_path_view(path@); }
    let ghost start = view_state(initial@);
    let ghost steps = view_path(path@);
    proof { lemma_progress_start(steps, start); }
    let mut state: Vec<&'a nc::NameConstraints<'a>> = initial;
    let mut spent: usize = 0;
    let mut i: usize = 0;
    while i < path.len()
        invariant
            i <= path.len(),
            steps == view_path(path@),
            start == view_state(initial@),
            steps.len() == path.len(),
            super::contract::within_comparison_bound(spent as nat),
            progress(steps, start, i as int, view_state(state@), spent as nat),
        decreases path.len() - i
    {
        let Some(certificate) = path.get(i) else { return false; };
        let next = i.saturating_add(1);
        let ghost before = view_state(state@);
        proof {
            lemma_path_view(path@);
            assert(steps[i as int] == view_nc_certificate(certificate));
        }
        let Some(total) = check_certificate(&mut state, certificate, next >= path.len(), spent) else {
            proof {
                lemma_progress_refusal(steps, start, i as int, before, spent as nat);
                reveal(path_accepted);
            }
            return false;
        };
        proof {
            lemma_progress_advance(steps, start, i as int, before, view_state(state@), spent as nat, total as nat);
        }
        spent = total;
        i = next;
    }
    proof {
        lemma_progress_done(steps, start, i as int, view_state(state@), spent as nat);
        reveal(path_accepted);
    }
    true
}

} // verus!
