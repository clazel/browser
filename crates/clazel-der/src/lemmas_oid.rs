//! Facts proven about OBJECT IDENTIFIER contents in the spec
//! ([`super::spec`]): the subidentifiers' encoding is the fewest octets
//! (§8.19.2), reading inverts writing and writing inverts reading (so the
//! decoder accepts exactly the encodings the encoder writes), and the
//! decoder never produces more components than there are octets. Evidence
//! that the transcription is right, not part of what the implementation must
//! meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// One subidentifier.
// ---------------------------------------------------------------------------

/// Every octet of a subidentifier prefix has bit 8 set.
pub proof fn lemma_prefix_all_continue(w: nat)
    ensures
        forall|k: int| 0 <= k < subidentifier_prefix(w).len() ==> #[trigger] subidentifier_prefix(w)[k] >= 128,
    decreases w,
{
    if w > 0 {
        lemma_prefix_all_continue(w / 128);
        let p = subidentifier_prefix(w / 128);
        let s = p + seq![(128 + w % 128) as u8];
        assert(subidentifier_prefix(w) =~= s);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] >= 128 by {
            if k < p.len() {
                assert(s[k] == p[k]);
            }
        }
    }
}

/// The prefix of a positive number has a first octet above 128: its leading
/// digit is not zero (no `0x80` padding).
pub proof fn lemma_prefix_first(w: nat)
    requires
        w > 0,
    ensures
        subidentifier_prefix(w).len() >= 1,
        subidentifier_prefix(w)[0] > 128,
    decreases w,
{
    let p = subidentifier_prefix(w / 128);
    if w / 128 > 0 {
        lemma_prefix_first(w / 128);
        assert(subidentifier_prefix(w)[0] == p[0]);
    } else {
        assert(p =~= Seq::<u8>::empty());
        assert(w % 128 == w);
        assert(subidentifier_prefix(w) =~= seq![(128 + w % 128) as u8]);
    }
}

/// The prefix spells the number it was made from.
pub proof fn lemma_prefix_base128(w: nat)
    ensures
        base128(subidentifier_prefix(w)) == w,
    decreases w,
{
    if w > 0 {
        lemma_prefix_base128(w / 128);
        let p = subidentifier_prefix(w / 128);
        let x = (128 + w % 128) as u8;
        assert(subidentifier_prefix(w) =~= p.push(x));
        super::lemmas::lemma_base128_push(p, x);
        assert(x % 128 == w % 128);
    } else {
        assert(subidentifier_prefix(0) =~= Seq::<u8>::empty());
    }
}

/// A subidentifier's encoding: one or more octets, all but the last with
/// bit 8 set, the last with it clear, the first not `0x80` (§8.19.2: "the
/// leading octet of the subidentifier shall not have the value 80"), and it
/// spells the subidentifier.
pub proof fn lemma_encode_subidentifier_props(v: nat)
    ensures
        ({
            let e = encode_subidentifier(v);
            &&& e.len() >= 1
            &&& e.last() < 128
            &&& forall|k: int| 0 <= k < e.len() - 1 ==> #[trigger] e[k] >= 128
            &&& e[0] != 128
            &&& base128(e) == v
        }),
{
    let p = subidentifier_prefix(v / 128);
    let e = encode_subidentifier(v);
    lemma_prefix_all_continue(v / 128);
    lemma_prefix_base128(v / 128);
    assert(e =~= p.push((v % 128) as u8));
    super::lemmas::lemma_base128_push(p, (v % 128) as u8);
    assert(e.last() == (v % 128) as u8);
    assert forall|k: int| 0 <= k < e.len() - 1 implies #[trigger] e[k] >= 128 by {
        assert(e[k] == p[k]);
    }
    if v / 128 > 0 {
        lemma_prefix_first(v / 128);
        assert(e[0] == p[0]);
    } else {
        assert(p =~= Seq::<u8>::empty());
        assert(e[0] == (v % 128) as u8);
    }
}

/// A series that ends: every octet before the end has bit 8 set and the
/// end's is clear.
pub proof fn lemma_series_end_props(b: Seq<u8>, i: nat, end: nat)
    ensures
        match series_end(b, i, end) {
            Some(j) => {
                &&& i <= j < end
                &&& b[j as int] < 128
                &&& forall|k: int| i <= k < j ==> #[trigger] b[k] >= 128
            },
            None => true,
        },
    decreases end - i,
{
    if i < end && b[i as int] >= 128 {
        lemma_series_end_props(b, i + 1, end);
    }
}

/// A run of octets whose low seven bits do not all vanish in the first
/// spells a positive number.
pub proof fn lemma_base128_positive(r: Seq<u8>)
    requires
        r.len() >= 1,
        r[0] % 128 != 0,
    ensures
        base128(r) > 0,
    decreases r.len(),
{
    let d = r.drop_last();
    if r.len() == 1 {
        assert(d =~= Seq::<u8>::empty());
        assert(r.last() == r[0]);
    } else {
        assert(d[0] == r[0]);
        lemma_base128_positive(d);
    }
}

/// A prefix is rebuilt from the number its octets spell: the digits are the
/// only octets of the run (all with bit 8 set, no leading `0x80`).
pub proof fn lemma_prefix_canonical(r: Seq<u8>)
    requires
        forall|k: int| 0 <= k < r.len() ==> #[trigger] r[k] >= 128,
        r.len() >= 1 ==> r[0] != 128,
    ensures
        subidentifier_prefix(base128(r)) =~= r,
    decreases r.len(),
{
    if r.len() > 0 {
        let d = r.drop_last();
        let x = r.last();
        assert forall|k: int| 0 <= k < d.len() implies #[trigger] d[k] >= 128 by {
            assert(d[k] == r[k]);
        }
        if d.len() >= 1 {
            assert(d[0] == r[0]);
        }
        lemma_prefix_canonical(d);
        assert(r[0] % 128 != 0);
        lemma_base128_positive(r);
        let w = base128(r);
        assert(w == base128(d) * 128 + (x % 128) as nat);
        assert(w / 128 == base128(d)) by (nonlinear_arith)
            requires
                w == base128(d) * 128 + (x % 128) as nat,
                x % 128 < 128,
        ;
        assert(w % 128 == (x % 128) as nat) by (nonlinear_arith)
            requires
                w == base128(d) * 128 + (x % 128) as nat,
                x % 128 < 128,
        ;
        assert(x >= 128);
        assert((128 + w % 128) as u8 == x);
        assert(subidentifier_prefix(w) =~= subidentifier_prefix(w / 128) + seq![x]);
        assert(d + seq![x] =~= r);
    }
}

/// A series of octets (all but the last with bit 8 set, the last with it
/// clear, the first not `0x80`) is the encoding of the number it spells.
pub proof fn lemma_series_canonical(run: Seq<u8>)
    requires
        run.len() >= 1,
        run.last() < 128,
        forall|k: int| 0 <= k < run.len() - 1 ==> #[trigger] run[k] >= 128,
        run[0] != 128,
    ensures
        encode_subidentifier(base128(run)) =~= run,
{
    let d = run.drop_last();
    let last = run.last();
    assert forall|k: int| 0 <= k < d.len() implies #[trigger] d[k] >= 128 by {
        assert(d[k] == run[k]);
    }
    if d.len() >= 1 {
        assert(d[0] == run[0]);
    }
    lemma_prefix_canonical(d);
    let v = base128(run);
    assert(v == base128(d) * 128 + (last % 128) as nat);
    assert(last % 128 == last);
    assert(v / 128 == base128(d)) by (nonlinear_arith)
        requires
            v == base128(d) * 128 + (last % 128) as nat,
            last % 128 < 128,
    ;
    assert(v % 128 == (last % 128) as nat) by (nonlinear_arith)
        requires
            v == base128(d) * 128 + (last % 128) as nat,
            last % 128 < 128,
    ;
    assert(v % 128 == last as nat);
    assert(encode_subidentifier(v) =~= subidentifier_prefix(base128(d)) + seq![last]);
    assert(d + seq![last] =~= run);
}

// ---------------------------------------------------------------------------
// A list of subidentifiers.
// ---------------------------------------------------------------------------

/// The bytes of `subidentifiers` split into the first subidentifier and the
/// rest.
proof fn lemma_series_end_of_encoding(v: nat, rest: Seq<u8>)
    ensures
        ({
            let e = encode_subidentifier(v);
            let c = e + rest;
            series_end(c, 0, c.len()) == Some((e.len() - 1) as nat)
        }),
{
    lemma_encode_subidentifier_props(v);
    let e = encode_subidentifier(v);
    let c = e + rest;
    lemma_series_end_from(c, 0, e.len());
}

/// A series that has no end before octet `k - 1`, and ends there, ends
/// there in any longer sequence.
proof fn lemma_series_end_from(c: Seq<u8>, i: nat, k: nat)
    requires
        1 <= k <= c.len(),
        i <= k - 1,
        forall|m: int| i <= m < k - 1 ==> #[trigger] c[m] >= 128,
        c[k - 1] < 128,
    ensures
        series_end(c, i, c.len()) == Some((k - 1) as nat),
    decreases k - i,
{
    if i < k - 1 {
        lemma_series_end_from(c, i + 1, k);
    }
}

/// Reading what [`encode_subidentifiers`] wrote: every list of
/// subidentifiers below 2^64 survives.
pub proof fn lemma_subidentifiers_encode(s: Seq<nat>)
    requires
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < 0x1_0000_0000_0000_0000,
    ensures
        subidentifiers(encode_subidentifiers(s)) == Some(s),
    decreases s.len(),
{
    let c = encode_subidentifiers(s);
    if s.len() == 0 {
        assert(c =~= Seq::<u8>::empty());
    } else {
        let rest = s.drop_first();
        let v = s[0];
        let e = encode_subidentifier(v);
        let r = encode_subidentifiers(rest);
        assert(c == e + r);
        lemma_encode_subidentifier_props(v);
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i] < 0x1_0000_0000_0000_0000 by {
            assert(rest[i] == s[i + 1]);
        }
        lemma_subidentifiers_encode(rest);
        lemma_series_end_of_encoding(v, r);
        let j = (e.len() - 1) as nat;
        assert(c.len() > 0);
        assert(c.subrange(0, j as int + 1) =~= e);
        assert(c[0] == e[0]);
        assert(c.skip(j as int + 1) =~= r);
        assert(seq![v] + rest =~= s);
    }
}

/// Writing what [`subidentifiers`] read: the octets are the encoding of the
/// subidentifiers that were read, and each is below 2^64 (the decoder's
/// limit).
pub proof fn lemma_encode_subidentifiers_decode(c: Seq<u8>)
    ensures
        match subidentifiers(c) {
            Some(s) => {
                &&& encode_subidentifiers(s) =~= c
                &&& forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < 0x1_0000_0000_0000_0000
                &&& s.len() <= c.len()
            },
            None => true,
        },
    decreases c.len(),
{
    if c.len() > 0 {
        lemma_series_end_props(c, 0, c.len());
        if let Some(j) = series_end(c, 0, c.len()) {
            let run = c.subrange(0, j as int + 1);
            let v = base128(run);
            if c[0] != 128 && v < 0x1_0000_0000_0000_0000 {
                let rest_bytes = c.skip(j as int + 1);
                lemma_encode_subidentifiers_decode(rest_bytes);
                if let Some(rest) = subidentifiers(rest_bytes) {
                    assert(run.last() == c[j as int]);
                    assert forall|k: int| 0 <= k < run.len() - 1 implies #[trigger] run[k] >= 128 by {
                        assert(run[k] == c[k]);
                    }
                    assert(run[0] == c[0]);
                    lemma_series_canonical(run);
                    let s = seq![v] + rest;
                    assert(s.drop_first() =~= rest);
                    assert(s[0] == v);
                    assert(encode_subidentifiers(s) == encode_subidentifier(v) + encode_subidentifiers(rest));
                    assert(run + rest_bytes =~= c);
                    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] < 0x1_0000_0000_0000_0000 by {
                        if i > 0 {
                            assert(s[i] == rest[i - 1]);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Components.
// ---------------------------------------------------------------------------

/// The first two components survive being packed into the first
/// subidentifier and unpacked.
pub proof fn lemma_first_components(x: nat, y: nat)
    requires
        x <= 2,
        x < 2 ==> y < 40,
    ensures
        first_components(40 * x + y) == (x, y),
{
}

/// Reading what [`oid_contents`] wrote: every valid list of components
/// survives.
pub proof fn lemma_oid_components_oid_contents(arcs: Seq<nat>)
    requires
        oid_valid(arcs),
    ensures
        oid_components(oid_contents(arcs)) == Some(arcs),
{
    let subs = seq![40 * arcs[0] + arcs[1]] + arcs.skip(2);
    assert forall|i: int| 0 <= i < subs.len() implies #[trigger] subs[i] < 0x1_0000_0000_0000_0000 by {
        if i > 0 {
            assert(subs[i] == arcs[i + 1]);
        }
    }
    lemma_subidentifiers_encode(subs);
    lemma_first_components(arcs[0], arcs[1]);
    assert(subs[0] == 40 * arcs[0] + arcs[1]);
    assert(subs.skip(1) =~= arcs.skip(2));
    assert(seq![arcs[0], arcs[1]] + arcs.skip(2) =~= arcs);
}

/// Writing what [`oid_components`] read: the octets are the encoding of the
/// components that were read, which are valid, and there are no more of
/// them than the octets plus one (the first subidentifier gives two).
pub proof fn lemma_oid_contents_oid_components(c: Seq<u8>)
    ensures
        match oid_components(c) {
            Some(arcs) => oid_valid(arcs) && oid_contents(arcs) =~= c && arcs.len() <= c.len() + 1,
            None => true,
        },
{
    lemma_encode_subidentifiers_decode(c);
    if let Some(subs) = subidentifiers(c) {
        if subs.len() > 0 {
            let (x, y) = first_components(subs[0]);
            let arcs = seq![x, y] + subs.skip(1);
            assert(arcs[0] == x);
            assert(arcs[1] == y);
            assert(arcs.skip(2) =~= subs.skip(1));
            assert(40 * x + y == subs[0]);
            assert(subs[0] < 0x1_0000_0000_0000_0000);
            assert forall|i: int| 2 <= i < arcs.len() implies arcs[i] < 0x1_0000_0000_0000_0000 by {
                assert(arcs[i] == subs[i - 1]);
            }
            assert(seq![40 * x + y] + subs.skip(1) =~= subs);
        }
    }
}

/// The number of components decoded never exceeds the octets (plus one):
/// a vector built from them holds no more than there are octets to have
/// read, so a declared length of 2^64 reserves nothing.
pub proof fn lemma_oid_components_bound(c: Seq<u8>)
    ensures
        match oid_components(c) {
            Some(arcs) => arcs.len() <= c.len() + 1,
            None => true,
        },
{
    lemma_oid_contents_oid_components(c);
}

} // verus!
