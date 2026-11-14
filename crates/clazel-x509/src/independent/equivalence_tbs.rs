//! `TBSCertificate` of `independent/structures.rs` against `tbs/spec.rs`, one
//! field at a time. `equivalence.rs` assembles them and states the domain.
//!
//! `tbs/spec.rs` walks a cursor over the fields and `structures.rs` indexes a
//! list of encodings. So each lemma here is about the list from one cursor
//! position on: `lemma_*_fwd` builds it up from the end, starting from what
//! `tbs/spec.rs` read, and `lemma_*_back` walks it down, starting from what
//! `structures.rs` decoded.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_extensions::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::name::spec as n;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// Skipping.
// ---------------------------------------------------------------------

/// Skipping twice.
pub proof fn lemma_skip_skip(l: Seq<i::Tlv>, a: int, b: int)
    requires
        0 <= a,
        0 <= b,
        a + b <= l.len(),
    ensures
        l.skip(a).skip(b) == l.skip(a + b),
{
    assert(l.skip(a).skip(b) =~= l.skip(a + b));
}

// ---------------------------------------------------------------------
// INTEGER at a position.
// ---------------------------------------------------------------------

/// `read_integer` and `decode_integer`.
pub proof fn lemma_read_integer(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_integer(b, pos, end) {
            Some((negative, start, finish, next)) => {
                let r = d::read_tlv(b, pos, end)->Some_0;
                let con = sl(b, r.cstart, r.cend);
                &&& d::read_tlv(b, pos, end) is Some
                &&& !tag_is_reserved(r.tag)
                &&& r.cend == next
                &&& finish == next
                &&& pos < next <= end
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& i::decode_integer(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(d::integer_value(con))
                &&& d::integer_contents_ok(con)
                &&& negative == (con[0] >= 128)
                &&& start == (if con.len() >= 2 && con[0] == 0 { r.cstart + 1 } else { r.cstart })
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => i::decode_integer(u) is None,
                None => true,
            },
        },
{
    lemma_tlv(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(r) = d::read_tlv(b, pos, end) {
        let con = sl(b, r.cstart, r.cend);
        lemma_integer_contents(con);
        if !tag_is_reserved(r.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, r, u, d::INTEGER, false);
        }
    } else {
        if let Some(u) = i::parse_tlv(sl(b, pos, end)) {
            assert(i::decode_integer(u) is Some ==> tag_fits(u));
        }
    }
}

/// `tbs/spec.rs`'s limit on a serial number, as a value: 20 octets hold the
/// non-negative values below 2^159 (RFC 5280 §4.1.2.2).
pub open spec fn serial_limit() -> int {
    (128 * d::pow256(19)) as int
}

/// A serial number from `tbs/spec.rs` to `structures.rs`.
pub proof fn lemma_serial_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_serial(b, pos, end) is Some,
    ensures
        ({
            let (der, next) = t::parse_serial(b, pos, end)->Some_0;
            &&& d::read_tlv(b, pos, end) is Some
            &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
            &&& d::read_tlv(b, pos, end)->Some_0.cend == next
            &&& pos < next <= end
            &&& i::parse_tlv(sl(b, pos, end)) is Some
            &&& i::decode_integer(i::parse_tlv(sl(b, pos, end))->Some_0) is Some
            &&& i::parse_single(der) == i::parse_tlv(sl(b, pos, end))
        }),
{
    lemma_read_integer(b, pos, end);
    lemma_tlv_alone(b, pos, end);
}

/// A serial number from `structures.rs` to `tbs/spec.rs`.
pub proof fn lemma_serial_back(b: Seq<u8>, pos: nat, end: nat, r: Seq<i::Tlv>, v: int)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(r),
        r.len() > 0,
        i::decode_integer(r[0]) == Some(v),
        0 <= v < serial_limit(),
    ensures
        t::parse_serial(b, pos, end) is Some,
        i::parse_single(t::parse_serial(b, pos, end)->Some_0.0) == Some(r[0]),
        pos < t::parse_serial(b, pos, end)->Some_0.1 <= end,
        i::parse_tlvs(sl(b, t::parse_serial(b, pos, end)->Some_0.1, end)) == Some(r.skip(1)),
{
    assert(tag_fits(r[0]));
    lemma_tlvs_head(b, pos, end, r);
    lemma_read_integer(b, pos, end);
    let u = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let con = sl(b, u.cstart, u.cend);
    assert(d::integer_value(con) == v);
    lemma_integer_size(con, 20);
    lemma_integer_sign(con);
    lemma_tlv_alone(b, pos, end);
}

// ---------------------------------------------------------------------
// version.
// ---------------------------------------------------------------------

/// The one INTEGER inside `[0]`, read both ways.
pub proof fn lemma_version_value_fwd(b: Seq<u8>, cs: nat, ce: nat)
    requires
        wf(b, cs, ce),
        ce - cs < two64(),
        d::read_integer(b, cs, ce) is Some,
        d::read_integer(b, cs, ce)->Some_0.3 == ce,
        !d::read_integer(b, cs, ce)->Some_0.0,
        d::read_integer(b, cs, ce)->Some_0.2 - d::read_integer(b, cs, ce)->Some_0.1 == 1,
        b[d::read_integer(b, cs, ce)->Some_0.1 as int] == 1 || b[d::read_integer(b, cs, ce)->Some_0.1 as int] == 2,
    ensures
        i::parse_single(sl(b, cs, ce)) is Some,
        i::decode_integer(i::parse_single(sl(b, cs, ce))->Some_0) == Some(
            b[d::read_integer(b, cs, ce)->Some_0.1 as int] as int,
        ),
{
    lemma_read_integer(b, cs, ce);
    let r = d::read_tlv(b, cs, ce)->Some_0;
    let con = sl(b, r.cstart, r.cend);
    let (negative, start, finish, next) = d::read_integer(b, cs, ce)->Some_0;
    assert(i::parse_tlv(sl(b, cs, ce))->Some_0.encoding.len() == ce - cs);
    if con.len() >= 2 && con[0] == 0 {
        // A pad is only before an octet of 128 or more.
        assert(con[1] == b[start as int]);
        assert(con.len() == 2);
        assert(false);
    }
    assert(con.len() == 1);
    assert(con[0] == b[start as int]);
    assert(con.drop_last() =~= Seq::<u8>::empty());
    assert(d::be_value(Seq::<u8>::empty()) == 0);
    assert(con.last() == con[0]);
    assert(d::be_value(con) == con[0] as nat);
}

/// `version` from `tbs/spec.rs`: a present one.
pub proof fn lemma_version_fwd(b: Seq<u8>, start: nat, end: nat)
    requires
        wf(b, start, end),
        end - start < two64(),
        t::parse_version(b, start, end) is Some,
        d::read_tlv(b, start, end) is Some,
        d::read_tlv(b, start, end)->Some_0.tag == d::context_specific(0, true),
    ensures
        ({
            let (version, next) = t::parse_version(b, start, end)->Some_0;
            &&& d::read_tlv(b, start, end)->Some_0.cend == next
            &&& start < next <= end
            &&& !tag_is_reserved(d::read_tlv(b, start, end)->Some_0.tag)
            &&& i::parse_tlv(sl(b, start, end)) is Some
            &&& s::decode_version(i::parse_tlv(sl(b, start, end))->Some_0) == Some(version as int)
            &&& i::parse_tlv(sl(b, start, end))->Some_0.class == 2
            &&& i::parse_tlv(sl(b, start, end))->Some_0.number == 0
        }),
{
    lemma_tlv(b, start, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    let r = d::read_tlv(b, start, end)->Some_0;
    lemma_version_value_fwd(b, r.cstart, r.cend);
    let (negative, vs, ve, next) = d::read_integer(b, r.cstart, r.cend)->Some_0;
    let inner = i::parse_single(sl(b, r.cstart, r.cend))->Some_0;
    let u = i::parse_tlv(sl(b, start, end))->Some_0;
    assert(u.contents == sl(b, r.cstart, r.cend));
}

/// `version` from `structures.rs`.
pub proof fn lemma_version_back(b: Seq<u8>, start: nat, end: nat, l: Seq<i::Tlv>, v: int)
    requires
        wf(b, start, end),
        end - start < two64(),
        i::parse_tlvs(sl(b, start, end)) == Some(l),
        l.len() > 0,
        tag_fits(l[0]),
        s::version_component(l) == Some(v),
        0 <= v <= 2,
    ensures
        t::parse_version(b, start, end) is Some,
        t::parse_version(b, start, end)->Some_0.0 == v as nat,
        start <= t::parse_version(b, start, end)->Some_0.1 <= end,
        i::parse_tlvs(sl(b, t::parse_version(b, start, end)->Some_0.1, end)) == Some(
            l.skip(s::after_version(l) as int),
        ),
{
    lemma_tlvs_head(b, start, end, l);
    let r = d::read_tlv(b, start, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, end);
    lemma_context_class(r.tag);
    if i::tag_at(l, 0, 2, 0) {
        let u = l[0];
        assert(u.constructed);
        let inner = i::parse_single(u.contents)->Some_0;
        assert(u.contents == sl(b, r.cstart, r.cend));
        assert(tag_fits(inner));
        lemma_single_back(b, r.cstart, r.cend, inner);
        lemma_read_integer(b, r.cstart, r.cend);
        let w = d::read_tlv(b, r.cstart, r.cend)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, r.cstart, r.cend);
        let con = sl(b, w.cstart, w.cend);
        assert(d::integer_value(con) == v);
        assert(d::pow256(0) == 1);
        lemma_integer_size(con, 1);
        lemma_integer_sign(con);
        assert(con.len() == 1);
        assert(con.drop_last() =~= Seq::<u8>::empty());
        assert(d::be_value(Seq::<u8>::empty()) == 0);
        assert(con.last() == con[0]);
        assert(d::be_value(con) == con[0] as nat);
        assert(b[w.cstart as int] == con[0]);
        assert(r.tag == d::context_specific(0, true));
        assert(t::parse_version(b, start, end) == Some((v as nat, r.cend)));
    } else {
        assert(l.skip(0) =~= l);
        assert(v == 0);
        assert(r.tag != d::context_specific(0, true));
        assert(l == l.skip(s::after_version(l) as int));
    }
}

// ---------------------------------------------------------------------
// The optional tail.
// ---------------------------------------------------------------------

/// What `structures.rs` reads after `subjectPublicKeyInfo`: the two unique
/// identifiers, the extensions, and how many encodings they took.
pub open spec fn tail_of(r: Seq<i::Tlv>) -> Option<
    (Option<i::BitString>, Option<i::BitString>, Option<Seq<e::Extension>>, nat),
> {
    match s::unique_identifier_component(r, 0, 1) {
        None => None,
        Some(issuer) => {
            let m = s::step(issuer);
            match s::unique_identifier_component(r, m, 2) {
                None => None,
                Some(subject) => {
                    let p = m + s::step(subject);
                    match s::extensions_component(r, p) {
                        None => None,
                        Some(extensions) => Some((issuer, subject, extensions, p + s::step(extensions))),
                    }
                },
            }
        },
    }
}

/// A unique identifier's encoding and its value agree.
pub open spec fn unique_agree(a: Option<Seq<u8>>, v: Option<i::BitString>) -> bool {
    match (a, v) {
        (None, None) => true,
        (Some(p), Some(q)) => {
            &&& i::parse_single(p) is Some
            &&& i::decode_tagged_bit_string(i::parse_single(p)->Some_0) == Some(q)
        },
        _ => false,
    }
}

/// The extensions of the two agree.
pub open spec fn optional_extensions_agree(a: Option<Seq<u8>>, v: Option<Seq<e::Extension>>) -> bool {
    match (a, v) {
        (None, None) => true,
        (Some(p), Some(q)) => {
            &&& x::parse_extensions(p) is Some
            &&& extensions_agree(x::parse_extensions(p)->Some_0, q)
            &&& forall|k: int| 0 <= k < q.len() ==> extension_in_domain(#[trigger] q[k])
        },
        _ => false,
    }
}

/// Every extension `tbs/spec.rs` keeps is one `extensions.rs` reads.
pub open spec fn extensions_decode(a: Option<Seq<u8>>) -> bool {
    match a {
        None => true,
        Some(p) => {
            &&& x::parse_extensions(p) is Some
            &&& forall|m: int|
                0 <= m < x::parse_extensions(p)->Some_0.len() ==> value_decodes(
                    #[trigger] x::parse_extensions(p)->Some_0[m],
                )
        },
    }
}

/// The two tests of a tagged bit string's contents.
pub proof fn lemma_implicit_bit_string(con: Seq<u8>)
    ensures
        t::valid_implicit_bit_string(con) == d::bit_string_contents_ok(con),
{
}

/// A tagged BIT STRING's contents, for `structures.rs`.
pub proof fn lemma_tagged_bit_string(u: i::Tlv)
    ensures
        !u.constructed ==> (i::decode_tagged_bit_string(u) is Some) == d::bit_string_contents_ok(u.contents),
        u.constructed ==> i::decode_tagged_bit_string(u) is None,
{
    lemma_bit_string_contents(u.contents);
}

/// `unique_identifier_component` at the head of the list.
pub proof fn lemma_unique_head(r: Seq<i::Tlv>, number: nat, o: Option<i::BitString>)
    requires
        s::unique_identifier_component(r, 0, number) == Some(o),
    ensures
        o is Some ==> r.len() > 0 && r[0].class == 2 && r[0].number == number,
        o is None ==> !i::tag_at(r, 0, 2, number),
{
}

/// A skip of the same list moves `unique_identifier_component`.
pub proof fn lemma_unique_skip(l: Seq<i::Tlv>, j: nat, m: nat, number: nat)
    requires
        j <= l.len(),
    ensures
        s::unique_identifier_component(l, j + m, number) == s::unique_identifier_component(
            l.skip(j as int),
            m,
            number,
        ),
{
    let r = l.skip(j as int);
    if j + m < l.len() {
        assert(r[m as int] == l[(j + m) as int]);
    }
}

/// The same for `extensions_component`.
pub proof fn lemma_extensions_skip(l: Seq<i::Tlv>, j: nat, m: nat)
    requires
        j <= l.len(),
    ensures
        s::extensions_component(l, j + m) == s::extensions_component(l.skip(j as int), m),
{
    let r = l.skip(j as int);
    if j + m < l.len() {
        assert(r[m as int] == l[(j + m) as int]);
    }
}

/// `[3]` from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_optional_extensions_fwd(b: Seq<u8>, pos: nat, end: nat, version: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::optional_extensions(b, pos, end, version) is Some,
        t::optional_extensions(b, pos, end, version)->Some_0.2 == end,
        extensions_decode(t::optional_extensions(b, pos, end, version)->Some_0.1),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let r = i::parse_tlvs(sl(b, pos, end))->Some_0;
            let (wrapper, sequence, after) = t::optional_extensions(b, pos, end, version)->Some_0;
            &&& r.len() == 0 || (r[0].class == 2 && r[0].number == 3)
            &&& s::extensions_component(r, 0) is Some
            &&& s::step(s::extensions_component(r, 0)->Some_0) == r.len()
            &&& optional_extensions_agree(sequence, s::extensions_component(r, 0)->Some_0)
            &&& (wrapper is Some) == (sequence is Some)
            &&& sequence is Some ==> version == 2
        }),
{
    hide(x::parse_extensions);
    hide(e::decode_extension_list);
    lemma_tlvs_empty(b, end);
    if pos < end {
        let (wrapper, sequence, after) = t::optional_extensions(b, pos, end, version)->Some_0;
        let w = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        assert(w.tag == d::context_specific(3, true));
        assert(w.cend == end);
        let v = sequence->Some_0;
        assert(v == sl(b, w.cstart, w.cend));
        assert(!tag_is_reserved(w.tag));
        lemma_tlv(b, pos, end);
        lemma_tlvs_cons(b, pos, end, Seq::<i::Tlv>::empty());
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = seq![u] + Seq::<i::Tlv>::empty();
        assert(r[0] == u);
        assert(r.len() == 1);
        assert(u.contents == v);
        theorem_extensions_fwd(v);
        lemma_context_class(w.tag);
    }
}

/// A unique identifier from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_unique_fwd(b: Seq<u8>, pos: nat, end: nat, number: u32, version: nat, r: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::optional_unique(b, pos, end, number, version) is Some,
        i::parse_tlvs(sl(b, t::optional_unique(b, pos, end, number, version)->Some_0.1, end)) == Some(r),
        r.len() == 0 || r[0].class != 2 || r[0].number != number,
    ensures
        ({
            let (o, next) = t::optional_unique(b, pos, end, number, version)->Some_0;
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& pos <= next <= end
            &&& {
                let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& s::unique_identifier_component(l, 0, number as nat) is Some
                &&& {
                    let v = s::unique_identifier_component(l, 0, number as nat)->Some_0;
                    &&& unique_agree(o, v)
                    &&& l.skip(s::step(v) as int) == r
                    &&& s::step(v) <= l.len()
                    &&& l.len() == 0 || (l[0].class == 2 && l[0].number >= number) || l == r
                    &&& o is Some ==> version != 0
                }
            }
        }),
{
    let (o, next) = t::optional_unique(b, pos, end, number, version)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if o is None {
        assert(next == pos);
        assert(r.skip(0) =~= r);
    } else {
        let w = d::read_tlv(b, pos, end)->Some_0;
        assert(w.tag == d::context_specific(number, false));
        assert(!tag_is_reserved(w.tag));
        lemma_tlvs_cons(b, pos, end, r);
        lemma_tlv(b, pos, end);
        lemma_tlv_alone(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let l = seq![u] + r;
        assert(l[0] == u);
        assert(l.skip(1) =~= r);
        lemma_context_class(w.tag);
        lemma_implicit_bit_string(u.contents);
        lemma_tagged_bit_string(u);
    }
}

/// The tail, from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_tail_fwd(b: Seq<u8>, pos: nat, end: nat, version: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_optional_tail(b, pos, end, version) is Some,
        extensions_decode(t::parse_optional_tail(b, pos, end, version)->Some_0.extensions_sequence_der),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
            let a = t::parse_optional_tail(b, pos, end, version)->Some_0;
            &&& tail_of(l) is Some
            &&& {
                let (issuer, subject, extensions, used) = tail_of(l)->Some_0;
                &&& used == l.len()
                &&& unique_agree(a.issuer_unique_id_der, issuer)
                &&& unique_agree(a.subject_unique_id_der, subject)
                &&& optional_extensions_agree(a.extensions_sequence_der, extensions)
                &&& (a.extensions_der is Some) == (a.extensions_sequence_der is Some)
                &&& a.extensions_sequence_der is Some ==> version == 2
                &&& a.issuer_unique_id_der is Some ==> version != 0
                &&& a.subject_unique_id_der is Some ==> version != 0
            }
        }),
{
    hide(t::optional_extensions);
    hide(t::optional_unique);
    let a = t::parse_optional_tail(b, pos, end, version)->Some_0;
    let (issuer, p1) = t::optional_unique(b, pos, end, 1, version)->Some_0;
    let (subject, p2) = t::optional_unique(b, p1, end, 2, version)->Some_0;
    assert(a.issuer_unique_id_der == issuer);
    assert(a.subject_unique_id_der == subject);
    lemma_unique_bounds(b, pos, end, 1, version);
    lemma_unique_bounds(b, p1, end, 2, version);
    lemma_optional_extensions_fwd(b, p2, end, version);
    let r3 = i::parse_tlvs(sl(b, p2, end))->Some_0;
    lemma_unique_fwd(b, p1, end, 2, version, r3);
    let r2 = i::parse_tlvs(sl(b, p1, end))->Some_0;
    lemma_unique_fwd(b, pos, end, 1, version, r2);
    let r1 = i::parse_tlvs(sl(b, pos, end))->Some_0;
    let v1 = s::unique_identifier_component(r1, 0, 1)->Some_0;
    let v2 = s::unique_identifier_component(r2, 0, 2)->Some_0;
    let m = s::step(v1);
    let p = m + s::step(v2);
    lemma_unique_skip(r1, m, 0, 2);
    lemma_skip_skip(r1, m as int, s::step(v2) as int);
    assert(r1.skip(p as int) == r3);
    lemma_extensions_skip(r1, p, 0);
}

/// `optional_unique` moves forward, inside the range.
pub proof fn lemma_unique_bounds(b: Seq<u8>, pos: nat, end: nat, number: u32, version: nat)
    requires
        pos <= end,
        t::optional_unique(b, pos, end, number, version) is Some,
    ensures
        pos <= t::optional_unique(b, pos, end, number, version)->Some_0.1 <= end,
{
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
}

/// A unique identifier from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_unique_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    number: u32,
    version: nat,
    l: Seq<i::Tlv>,
    v: Option<i::BitString>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        number == 1 || number == 2,
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        s::unique_identifier_component(l, 0, number as nat) == Some(v),
        l.len() > 0 ==> tag_fits(l[0]),
        v is Some ==> version != 0,
    ensures
        t::optional_unique(b, pos, end, number, version) is Some,
        unique_agree(t::optional_unique(b, pos, end, number, version)->Some_0.0, v),
        pos <= t::optional_unique(b, pos, end, number, version)->Some_0.1 <= end,
        i::parse_tlvs(sl(b, t::optional_unique(b, pos, end, number, version)->Some_0.1, end)) == Some(
            l.skip(s::step(v) as int),
        ),
{
    lemma_tlvs_none_left(b, pos, end, l);
    assert(l.skip(0) =~= l);
    if pos < end {
        lemma_tlvs_head(b, pos, end, l);
        let w = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        lemma_context_class(w.tag);
        let u = l[0];
        if v is Some {
            lemma_tagged_bit_string(u);
            lemma_implicit_bit_string(u.contents);
            assert(w.tag == d::context_specific(number, false));
            lemma_tlv_alone(b, pos, end);
        } else {
            assert(w.tag != d::context_specific(number, false));
        }
    }
}

/// `[3]` from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_optional_extensions_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    version: nat,
    l: Seq<i::Tlv>,
    v: Option<Seq<e::Extension>>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        s::extensions_component(l, 0) == Some(v),
        s::step(v) == l.len(),
        v is Some ==> version == 2 && extensions_in_domain(v->Some_0),
    ensures
        t::optional_extensions(b, pos, end, version) is Some,
        t::optional_extensions(b, pos, end, version)->Some_0.2 == end,
        optional_extensions_agree(t::optional_extensions(b, pos, end, version)->Some_0.1, v),
        (t::optional_extensions(b, pos, end, version)->Some_0.0 is Some) == (v is Some),
{
    hide(x::parse_extensions);
    hide(e::decode_extension_list);
    lemma_tlvs_none_left(b, pos, end, l);
    if pos < end {
        assert(l.len() == 1);
        let u = l[0];
        assert(i::tag_at(l, 0, 2, 3));
        assert(tag_fits(u));
        lemma_tlvs_head(b, pos, end, l);
        let w = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        lemma_context_class(w.tag);
        lemma_tlvs_none_left(b, w.cend, end, l.skip(1));
        assert(w.cend == end);
        assert(u.constructed);
        assert(w.tag == d::context_specific(3, true));
        let inner = i::parse_single(u.contents)->Some_0;
        let elements = s::sequence_elements(inner)->Some_0;
        assert(u.contents == sl(b, w.cstart, w.cend));
        assert(tag_fits(inner));
        lemma_single_back(b, w.cstart, w.cend, inner);
        lemma_tlv(b, w.cstart, w.cend);
        lemma_sequence_back(b, w.cstart, w.cend, inner, elements);
        theorem_extensions_back(u.contents, inner, elements, v->Some_0);
    }
}

/// The tail, from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_tail_back(b: Seq<u8>, pos: nat, end: nat, version: nat, l: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        tail_of(l) is Some,
        tail_of(l)->Some_0.3 == l.len(),
        tail_of(l)->Some_0.0 is Some ==> version != 0,
        tail_of(l)->Some_0.1 is Some ==> version != 0,
        tail_of(l)->Some_0.2 is Some ==> version == 2 && extensions_in_domain(tail_of(l)->Some_0.2->Some_0),
    ensures
        t::parse_optional_tail(b, pos, end, version) is Some,
        ({
            let a = t::parse_optional_tail(b, pos, end, version)->Some_0;
            let (issuer, subject, extensions, used) = tail_of(l)->Some_0;
            &&& unique_agree(a.issuer_unique_id_der, issuer)
            &&& unique_agree(a.subject_unique_id_der, subject)
            &&& optional_extensions_agree(a.extensions_sequence_der, extensions)
            &&& (a.extensions_der is Some) == (extensions is Some)
        }),
{
    hide(t::optional_extensions);
    hide(t::optional_unique);
    let (issuer, subject, extensions, used) = tail_of(l)->Some_0;
    let m = s::step(issuer);
    let m2 = s::step(subject);
    let p = m + m2;
    assert(p + s::step(extensions) == l.len());
    if l.len() > 0 {
        // Every encoding here is one of the three, so its tag is small.
        lemma_tail_first_tag(l);
    }
    lemma_unique_back(b, pos, end, 1, version, l, issuer);
    let (a1, p1) = t::optional_unique(b, pos, end, 1, version)->Some_0;
    let r2 = l.skip(m as int);
    lemma_unique_skip(l, m, 0, 2);
    if r2.len() > 0 {
        lemma_tail_second_tag(l);
    }
    lemma_unique_back(b, p1, end, 2, version, r2, subject);
    let (a2, p2) = t::optional_unique(b, p1, end, 2, version)->Some_0;
    let r3 = r2.skip(m2 as int);
    lemma_skip_skip(l, m as int, m2 as int);
    lemma_extensions_skip(l, p, 0);
    lemma_optional_extensions_back(b, p2, end, version, r3, extensions);
}

/// The first encoding of a whole tail has a small tag.
pub proof fn lemma_tail_first_tag(l: Seq<i::Tlv>)
    requires
        l.len() > 0,
        tail_of(l) is Some,
        tail_of(l)->Some_0.3 == l.len(),
    ensures
        tag_fits(l[0]),
{
    let (issuer, subject, extensions, used) = tail_of(l)->Some_0;
}

/// The encoding after the issuer's identifier has a small tag.
pub proof fn lemma_tail_second_tag(l: Seq<i::Tlv>)
    requires
        tail_of(l) is Some,
        tail_of(l)->Some_0.3 == l.len(),
        l.len() > s::step(tail_of(l)->Some_0.0),
    ensures
        tag_fits(l.skip(s::step(tail_of(l)->Some_0.0) as int)[0]),
{
    let (issuer, subject, extensions, used) = tail_of(l)->Some_0;
    let m = s::step(issuer);
    assert(l.skip(m as int)[0] == l[m as int]);
}

// ---------------------------------------------------------------------
// signature and issuer, subject and subjectPublicKeyInfo.
// ---------------------------------------------------------------------

/// `signature` and `issuer`, from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_signature_issuer_fwd(b: Seq<u8>, pos: nat, end: nat, rest: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_signature_issuer(b, pos, end) is Some,
        parameters_plain(t::parse_signature_issuer(b, pos, end)->Some_0.0),
        n::parse_name(t::parse_signature_issuer(b, pos, end)->Some_0.1) is Some,
        name_tags_plain(n::parse_name(t::parse_signature_issuer(b, pos, end)->Some_0.1)->Some_0),
        i::parse_tlvs(sl(b, t::parse_signature_issuer(b, pos, end)->Some_0.2, end)) == Some(rest),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let (algorithm, issuer, next) = t::parse_signature_issuer(b, pos, end)->Some_0;
            let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
            &&& pos < next <= end
            &&& l.len() == rest.len() + 2
            &&& l.skip(2) == rest
            &&& s::decode_algorithm_identifier(l[0]) is Some
            &&& algorithm_agree(algorithm, s::decode_algorithm_identifier(l[0])->Some_0)
            &&& s::decode_name(l[1]) is Some
            &&& name_agree(n::parse_name(issuer)->Some_0, s::decode_name(l[1])->Some_0)
        }),
{
    hide(n::parse_name);
    hide(s::decode_name);
    hide(s::decode_algorithm_identifier);
    let (algorithm, issuer, next) = t::parse_signature_issuer(b, pos, end)->Some_0;
    let (a, after) = c::parse_algorithm_identifier(b, pos, end)->Some_0;
    lemma_algorithm_fwd(b, pos, end);
    let w = d::read_tlv(b, after, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after, end);
    assert(!tag_is_reserved(w.tag));
    lemma_tlvs_cons(b, after, end, rest);
    lemma_tlv_alone(b, after, end);
    let nu = i::parse_tlv(sl(b, after, end))->Some_0;
    lemma_tlvs_cons(b, pos, end, seq![nu] + rest);
    let au = i::parse_tlv(sl(b, pos, end))->Some_0;
    let l = seq![au] + (seq![nu] + rest);
    assert(l[0] == au);
    assert(l[1] == nu);
    assert(l.skip(2) =~= rest);
    assert(issuer.len() < two64());
    theorem_name_fwd(issuer);
}

/// `signature` and `issuer`, from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_signature_issuer_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    l: Seq<i::Tlv>,
    algorithm: s::AlgorithmIdentifier,
    issuer: s::Name,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        l.len() >= 2,
        s::decode_algorithm_identifier(l[0]) == Some(algorithm),
        algorithm_in_domain(algorithm),
        s::decode_name(l[1]) == Some(issuer),
        issuer.rdn_sequence.len() > 0,
    ensures
        t::parse_signature_issuer(b, pos, end) is Some,
        ({
            let (a, der, next) = t::parse_signature_issuer(b, pos, end)->Some_0;
            &&& pos < next <= end
            &&& algorithm_agree(a, algorithm)
            &&& i::parse_single(der) == Some(l[1])
            &&& i::parse_tlvs(sl(b, next, end)) == Some(l.skip(2))
        }),
{
    assert(tag_fits(l[0]));
    assert(tag_fits(l[1]));
    lemma_tlvs_head(b, pos, end, l);
    lemma_algorithm_back(b, pos, end, l[0], algorithm);
    let (a, after) = c::parse_algorithm_identifier(b, pos, end)->Some_0;
    let w0 = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    assert(w0.cend == after);
    let r = l.skip(1);
    assert(r[0] == l[1]);
    lemma_tlvs_head(b, after, end, r);
    let w = d::read_tlv(b, after, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after, end);
    lemma_has_universal_tag(b, after, w, l[1], d::SEQUENCE, true);
    lemma_tlv_alone(b, after, end);
    let names = s::sequence_elements(l[1])->Some_0;
    assert(names.len() > 0);
    assert(i::parse_tlvs(l[1].contents) == Some(names));
    assert(l[1].contents.len() > 0);
    assert(w.cstart != w.cend);
    lemma_skip_skip(l, 1, 1);
}

/// `subject` and `subjectPublicKeyInfo`, from `tbs/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subject_spki_fwd(b: Seq<u8>, pos: nat, end: nat, rest: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        t::parse_subject_spki(b, pos, end) is Some,
        n::parse_name(t::parse_subject_spki(b, pos, end)->Some_0.0) is Some,
        name_tags_plain(n::parse_name(t::parse_subject_spki(b, pos, end)->Some_0.0)->Some_0),
        k::parse_subject_public_key_info(t::parse_subject_spki(b, pos, end)->Some_0.1) is Some,
        parameters_plain(
            k::parse_subject_public_key_info(t::parse_subject_spki(b, pos, end)->Some_0.1)->Some_0.algorithm,
        ),
        i::parse_tlvs(sl(b, t::parse_subject_spki(b, pos, end)->Some_0.2, end)) == Some(rest),
    ensures
        i::parse_tlvs(sl(b, pos, end)) is Some,
        ({
            let (subject, spki, next) = t::parse_subject_spki(b, pos, end)->Some_0;
            let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
            &&& pos < next <= end
            &&& l.len() == rest.len() + 2
            &&& l.skip(2) == rest
            &&& s::decode_name(l[0]) is Some
            &&& name_agree(n::parse_name(subject)->Some_0, s::decode_name(l[0])->Some_0)
            &&& s::decode_subject_public_key_info(l[1]) is Some
            &&& spki_agree(
                k::parse_subject_public_key_info(spki)->Some_0,
                s::decode_subject_public_key_info(l[1])->Some_0,
            )
        }),
{
    hide(n::parse_name);
    hide(s::decode_name);
    hide(k::parse_subject_public_key_info);
    hide(s::decode_subject_public_key_info);
    let (subject, spki, next) = t::parse_subject_spki(b, pos, end)->Some_0;
    let w = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let v = d::read_tlv(b, w.cend, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, w.cend, end);
    assert(!tag_is_reserved(w.tag));
    assert(!tag_is_reserved(v.tag));
    lemma_tlvs_cons(b, w.cend, end, rest);
    lemma_tlv_alone(b, w.cend, end);
    let ku = i::parse_tlv(sl(b, w.cend, end))->Some_0;
    lemma_tlvs_cons(b, pos, end, seq![ku] + rest);
    lemma_tlv_alone(b, pos, end);
    let nu = i::parse_tlv(sl(b, pos, end))->Some_0;
    let l = seq![nu] + (seq![ku] + rest);
    assert(l[0] == nu);
    assert(l[1] == ku);
    assert(l.skip(2) =~= rest);
    theorem_name_fwd(subject);
    theorem_spki_fwd(spki);
}

/// `subject` and `subjectPublicKeyInfo`, from `structures.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subject_spki_back(b: Seq<u8>, pos: nat, end: nat, l: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        l.len() >= 2,
        s::decode_name(l[0]) is Some,
        s::decode_subject_public_key_info(l[1]) is Some,
    ensures
        t::parse_subject_spki(b, pos, end) is Some,
        ({
            let (subject, spki, next) = t::parse_subject_spki(b, pos, end)->Some_0;
            &&& pos < next <= end
            &&& i::parse_single(subject) == Some(l[0])
            &&& i::parse_single(spki) == Some(l[1])
            &&& i::parse_tlvs(sl(b, next, end)) == Some(l.skip(2))
        }),
{
    assert(tag_fits(l[0]));
    assert(tag_fits(l[1]));
    lemma_tlvs_head(b, pos, end, l);
    let w = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_has_universal_tag(b, pos, w, l[0], d::SEQUENCE, true);
    lemma_tlv_alone(b, pos, end);
    let r = l.skip(1);
    assert(r[0] == l[1]);
    lemma_tlvs_head(b, w.cend, end, r);
    let v = d::read_tlv(b, w.cend, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, w.cend, end);
    lemma_has_universal_tag(b, w.cend, v, l[1], d::SEQUENCE, true);
    lemma_tlv_alone(b, w.cend, end);
    lemma_skip_skip(l, 1, 1);
}

} // verus!
