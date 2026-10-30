//! Facts proven about the extension readers and writers of
//! [`super::spec`] (RFC 8446 §4.2): each extension a client writes is read
//! back, what is read is one encoding, and a block of extensions has no
//! more elements than quarters of its bytes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An extension that can be written: `extension_data<0..2^16-1>`.
pub open spec fn ext_ok(e: Ext) -> bool {
    e.data.len() <= 65535
}

/// An extension is at least four bytes (the type and the length field).
pub proof fn lemma_write_ext_len(e: Ext)
    requires
        ext_ok(e),
    ensures
        write_ext(e).len() == 4 + e.data.len(),
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_be_bytes_len(e.etype as nat, 2);
    super::lemmas_pl::lemma_be_bytes_len(e.data.len(), 2);
}

/// An extension is read back from what [`write_ext`] wrote, wherever it
/// sits and whatever follows it.
pub proof fn lemma_read_ext_write_ext(e: Ext, rest: Seq<u8>)
    requires
        ext_ok(e),
    ensures
        read_ext(write_ext(e) + rest) == Some((e, rest)),
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_len_width_holds(65535);
    let b = write_ext(e) + rest;
    assert(b =~= be_bytes(e.etype as nat, 2) + (write_vec(e.data, 65535) + rest));
    super::lemmas_pl::lemma_read_uint_write(e.etype as nat, 2, write_vec(e.data, 65535) + rest);
    super::lemmas_pl::lemma_read_vec_write_vec(e.data, 0, 65535, rest);
}

/// What [`read_ext`] accepts is what [`write_ext`] writes, and it
/// consumes at least four bytes.
pub proof fn lemma_read_ext_canonical(b: Seq<u8>)
    ensures
        match read_ext(b) {
            Some((e, rest)) => {
                &&& ext_ok(e)
                &&& write_ext(e) + rest =~= b
                &&& rest.len() + 4 <= b.len()
            },
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some((e, rest)) = read_ext(b) {
        super::lemmas_pl::lemma_read_uint_canonical(b, 2);
        if let Some((t, r)) = read_uint(b, 2) {
            super::lemmas_pl::lemma_read_vec_canonical(r, 0, 65535);
            assert(write_u16(e.etype) =~= be_bytes(t, 2));
            assert(b =~= write_u16(e.etype) + r);
            assert(r =~= write_vec(e.data, 65535) + rest);
            assert(b =~= write_ext(e) + rest);
        }
    }
}

/// No over-read: an extension's result does not depend on what follows.
pub proof fn lemma_read_ext_extend(b: Seq<u8>, extra: Seq<u8>)
    ensures
        match read_ext(b) {
            Some((e, rest)) => read_ext(b + extra) == Some((e, rest + extra)),
            None => true,
        },
{
    super::lemmas_pl::lemma_read_uint_extend(b, 2, extra);
    if let Some((t, r)) = read_uint(b, 2) {
        super::lemmas_pl::lemma_read_vec_extend(r, 0, 65535, extra);
        assert((b + extra).skip(2) =~= r + extra);
    }
}

/// The extensions of a block are read back from what [`write_exts`]
/// wrote, given that the block fits its declared bounds.
pub proof fn lemma_read_exts_write_exts(es: Seq<Ext>, floor: nat, ceil: nat, rest: Seq<u8>)
    requires
        ceil < 16777216,
        forall|i: int| 0 <= i < es.len() ==> ext_ok(#[trigger] es[i]),
        vec_in_bounds(write_list(es, |e: Ext| write_ext(e)), floor, ceil),
    ensures
        read_exts(write_exts(es, ceil) + rest, floor, ceil) == Some((es, rest)),
{
    let w = |e: Ext| write_ext(e);
    let f = |x: Seq<u8>| read_ext(x);
    let ok = |e: Ext| ext_ok(e);
    assert forall|e: Ext| #[trigger] ok(e) implies w(e).len() >= 1 by {
        lemma_write_ext_len(e);
    }
    assert forall|e: Ext, r: Seq<u8>| ok(e) implies #[trigger] f(w(e) + r) == Some((e, r)) by {
        lemma_read_ext_write_ext(e, r);
    }
    super::lemmas_pl::lemma_read_list_write_list(es, w, f, ok);
    super::lemmas_pl::lemma_read_vec_write_vec(write_list(es, w), floor, ceil, rest);
}

/// What [`read_exts`] accepts is what [`write_exts`] writes, the block is
/// within its bounds, and it has at most a quarter as many extensions as
/// it has bytes: a declared length cannot make a reader reserve memory
/// for extensions that are not there.
pub proof fn lemma_read_exts_canonical(b: Seq<u8>, floor: nat, ceil: nat)
    ensures
        match read_exts(b, floor, ceil) {
            Some((es, rest)) => {
                &&& forall|i: int| 0 <= i < es.len() ==> ext_ok(#[trigger] es[i])
                &&& vec_in_bounds(write_list(es, |e: Ext| write_ext(e)), floor, ceil)
                &&& b =~= write_exts(es, ceil) + rest
                &&& es.len() * 4 <= b.len()
            },
            None => true,
        },
{
    if let Some((es, rest)) = read_exts(b, floor, ceil) {
        super::lemmas_pl::lemma_read_vec_canonical(b, floor, ceil);
        let (c, r) = read_vec(b, floor, ceil).unwrap();
        let w = |e: Ext| write_ext(e);
        let f = |x: Seq<u8>| read_ext(x);
        assert forall|bb: Seq<u8>| #[trigger] f(bb) is Some implies w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb by {
            lemma_read_ext_canonical(bb);
        }
        super::lemmas_pl::lemma_write_list_read_list(c, w, f);
        lemma_read_exts_elements(c);
        assert(rest == r);
    }
}

/// Every extension [`read_list`] reads is [`ext_ok`], and there are at
/// most a quarter as many as bytes.
pub proof fn lemma_read_exts_elements(c: Seq<u8>)
    ensures
        match read_list(c, |x: Seq<u8>| read_ext(x)) {
            Some(es) => {
                &&& forall|i: int| 0 <= i < es.len() ==> ext_ok(#[trigger] es[i])
                &&& es.len() * 4 <= c.len()
            },
            None => true,
        },
    decreases c.len(),
{
    let f = |x: Seq<u8>| read_ext(x);
    if c.len() > 0 {
        lemma_read_ext_canonical(c);
        if let Some((e, rest)) = read_ext(c) {
            if rest.len() < c.len() {
                lemma_read_exts_elements(rest);
                if let Some(es) = read_list(rest, f) {
                    let all = seq![e] + es;
                    assert forall|i: int| 0 <= i < all.len() implies ext_ok(#[trigger] all[i]) by {
                        if i > 0 {
                            assert(all[i] == es[i - 1]);
                        }
                    }
                    assert(all.len() == es.len() + 1);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Key share entries and server names.
// ---------------------------------------------------------------------------

/// The one byte spelling zero.
proof fn lemma_be_bytes_zero_one()
    ensures
        be_bytes(0, 1) =~= seq![0u8],
{
    assert(be_bytes(0, 0) =~= Seq::<u8>::empty());
    assert(be_bytes(0nat, 1) =~= be_bytes(0nat / 256, 0).push((0nat % 256) as u8));
}

/// A key share entry that can be written.
pub open spec fn key_share_ok(k: KeyShare) -> bool {
    vec_in_bounds(k.key_exchange, 1, 65535)
}

/// A server name that can be written.
pub open spec fn server_name_ok(s: ServerName) -> bool {
    vec_in_bounds(s.host_name, 1, 65535)
}

/// A key share entry is read back from its encoding, and is at least four
/// bytes.
pub proof fn lemma_read_key_share_write(k: KeyShare, rest: Seq<u8>)
    requires
        key_share_ok(k),
    ensures
        read_key_share(write_key_share(k) + rest) == Some((k, rest)),
        write_key_share(k).len() >= 4,
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_len_width_holds(65535);
    super::lemmas_pl::lemma_be_bytes_len(k.group as nat, 2);
    super::lemmas_pl::lemma_be_bytes_len(k.key_exchange.len(), 2);
    let b = write_key_share(k) + rest;
    assert(b =~= be_bytes(k.group as nat, 2) + (write_vec(k.key_exchange, 65535) + rest));
    super::lemmas_pl::lemma_read_uint_write(k.group as nat, 2, write_vec(k.key_exchange, 65535) + rest);
    super::lemmas_pl::lemma_read_vec_write_vec(k.key_exchange, 1, 65535, rest);
}

/// What [`read_key_share`] accepts is one encoding.
pub proof fn lemma_read_key_share_canonical(b: Seq<u8>)
    ensures
        match read_key_share(b) {
            Some((k, rest)) => key_share_ok(k) && write_key_share(k) + rest =~= b && rest.len() < b.len(),
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some((k, rest)) = read_key_share(b) {
        super::lemmas_pl::lemma_read_uint_canonical(b, 2);
        if let Some((g, r)) = read_uint(b, 2) {
            super::lemmas_pl::lemma_read_vec_canonical(r, 1, 65535);
            assert(write_u16(k.group) =~= be_bytes(g, 2));
            assert(b =~= write_key_share(k) + rest);
        }
    }
}

/// A server name is read back from its encoding.
pub proof fn lemma_read_server_name_write(s: ServerName, rest: Seq<u8>)
    requires
        server_name_ok(s),
    ensures
        read_server_name(write_server_name(s) + rest) == Some((s, rest)),
        write_server_name(s).len() >= 1,
{
    super::lemmas_pl::lemma_pow256_widths();
    super::lemmas_pl::lemma_len_width_holds(65535);
    let b = write_server_name(s) + rest;
    assert(b =~= be_bytes(0, 1) + (write_vec(s.host_name, 65535) + rest)) by {
        lemma_be_bytes_zero_one();
    }
    super::lemmas_pl::lemma_read_uint_write(0, 1, write_vec(s.host_name, 65535) + rest);
    super::lemmas_pl::lemma_read_vec_write_vec(s.host_name, 1, 65535, rest);
}

/// What [`read_server_name`] accepts is one encoding.
pub proof fn lemma_read_server_name_canonical(b: Seq<u8>)
    ensures
        match read_server_name(b) {
            Some((s, rest)) => server_name_ok(s) && write_server_name(s) + rest =~= b && rest.len() < b.len(),
            None => true,
        },
{
    super::lemmas_pl::lemma_pow256_widths();
    if let Some((s, rest)) = read_server_name(b) {
        super::lemmas_pl::lemma_read_uint_canonical(b, 1);
        if let Some((nt, r)) = read_uint(b, 1) {
            super::lemmas_pl::lemma_read_vec_canonical(r, 1, 65535);
            lemma_be_bytes_zero_one();
            assert(b =~= write_server_name(s) + rest);
        }
    }
}

// ---------------------------------------------------------------------------
// The extension bodies a client writes.
// ---------------------------------------------------------------------------

/// `supported_versions` in a ClientHello is read back (1 to 127 versions).
pub proof fn lemma_supported_versions_ch_round_trip(vs: Seq<u16>)
    requires
        1 <= vs.len() <= 127,
    ensures
        read_supported_versions_ch(write_supported_versions_ch(vs)) == Some(vs),
{
    super::lemmas_pl::lemma_write_u16s_len(vs);
    super::lemmas_pl::lemma_read_u16s_write_u16s(vs);
    super::lemmas_pl::lemma_read_vec_write_vec(write_u16s(vs), 2, 254, seq![]);
    assert(write_supported_versions_ch(vs) + seq![] =~= write_supported_versions_ch(vs));
}

/// What [`read_supported_versions_ch`] accepts is one encoding.
pub proof fn lemma_supported_versions_ch_canonical(data: Seq<u8>)
    ensures
        match read_supported_versions_ch(data) {
            Some(vs) => write_supported_versions_ch(vs) =~= data && 1 <= vs.len() <= 127,
            None => true,
        },
{
    if let Some(vs) = read_supported_versions_ch(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 2, 254);
        let (c, rest) = read_vec(data, 2, 254).unwrap();
        super::lemmas_pl::lemma_write_u16s_read_u16s(c);
        assert(data =~= write_vec(c, 254) + rest);
        assert(rest.len() == 0);
    }
}

/// `supported_groups` is read back (1 to 32767 groups).
pub proof fn lemma_named_groups_round_trip(gs: Seq<u16>)
    requires
        1 <= gs.len() <= 32767,
    ensures
        read_named_groups(write_named_groups(gs)) == Some(gs),
{
    super::lemmas_pl::lemma_write_u16s_len(gs);
    super::lemmas_pl::lemma_read_u16s_write_u16s(gs);
    super::lemmas_pl::lemma_read_vec_write_vec(write_u16s(gs), 2, 65535, seq![]);
    assert(write_named_groups(gs) + seq![] =~= write_named_groups(gs));
}

/// What [`read_named_groups`] accepts is one encoding.
pub proof fn lemma_named_groups_canonical(data: Seq<u8>)
    ensures
        match read_named_groups(data) {
            Some(gs) => write_named_groups(gs) =~= data && 1 <= gs.len() <= 32767,
            None => true,
        },
{
    if let Some(gs) = read_named_groups(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 2, 65535);
        let (c, rest) = read_vec(data, 2, 65535).unwrap();
        super::lemmas_pl::lemma_write_u16s_read_u16s(c);
        assert(data =~= write_vec(c, 65535) + rest);
    }
}

/// `signature_algorithms` is read back (1 to 32767 schemes).
pub proof fn lemma_signature_schemes_round_trip(ss: Seq<u16>)
    requires
        1 <= ss.len() <= 32767,
    ensures
        read_signature_schemes(write_signature_schemes(ss)) == Some(ss),
{
    super::lemmas_pl::lemma_write_u16s_len(ss);
    super::lemmas_pl::lemma_read_u16s_write_u16s(ss);
    super::lemmas_pl::lemma_read_vec_write_vec(write_u16s(ss), 2, 65534, seq![]);
    assert(write_signature_schemes(ss) + seq![] =~= write_signature_schemes(ss));
}

/// What [`read_signature_schemes`] accepts is one encoding.
pub proof fn lemma_signature_schemes_canonical(data: Seq<u8>)
    ensures
        match read_signature_schemes(data) {
            Some(ss) => write_signature_schemes(ss) =~= data && 1 <= ss.len() <= 32767,
            None => true,
        },
{
    if let Some(ss) = read_signature_schemes(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 2, 65534);
        let (c, rest) = read_vec(data, 2, 65534).unwrap();
        super::lemmas_pl::lemma_write_u16s_read_u16s(c);
        assert(data =~= write_vec(c, 65534) + rest);
    }
}

/// `cookie` is read back (1 to 65535 bytes).
pub proof fn lemma_cookie_round_trip(c: Seq<u8>)
    requires
        1 <= c.len() <= 65535,
    ensures
        read_cookie(write_cookie(c)) == Some(c),
{
    super::lemmas_pl::lemma_read_vec_write_vec(c, 1, 65535, seq![]);
    assert(write_cookie(c) + seq![] =~= write_cookie(c));
}

/// What [`read_cookie`] accepts is one encoding.
pub proof fn lemma_cookie_canonical(data: Seq<u8>)
    ensures
        match read_cookie(data) {
            Some(c) => write_cookie(c) =~= data && 1 <= c.len() <= 65535,
            None => true,
        },
{
    if let Some(c) = read_cookie(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 1, 65535);
    }
}

/// `key_share` in a ClientHello is read back, for entries that can be
/// written and a list that fits.
pub proof fn lemma_key_share_ch_round_trip(shares: Seq<KeyShare>)
    requires
        forall|i: int| 0 <= i < shares.len() ==> key_share_ok(#[trigger] shares[i]),
        write_list(shares, |k: KeyShare| write_key_share(k)).len() <= 65535,
    ensures
        read_key_share_ch(write_key_share_ch(shares)) == Some(shares),
{
    let w = |k: KeyShare| write_key_share(k);
    let f = |x: Seq<u8>| read_key_share(x);
    let ok = |k: KeyShare| key_share_ok(k);
    assert forall|e: KeyShare| #[trigger] ok(e) implies w(e).len() >= 1 by {
        lemma_read_key_share_write(e, seq![]);
    }
    assert forall|e: KeyShare, r: Seq<u8>| ok(e) implies #[trigger] f(w(e) + r) == Some((e, r)) by {
        lemma_read_key_share_write(e, r);
    }
    super::lemmas_pl::lemma_read_list_write_list(shares, w, f, ok);
    super::lemmas_pl::lemma_read_vec_write_vec(write_list(shares, w), 0, 65535, seq![]);
    assert(write_key_share_ch(shares) + seq![] =~= write_key_share_ch(shares));
}

/// What [`read_key_share_ch`] accepts is one encoding.
pub proof fn lemma_key_share_ch_canonical(data: Seq<u8>)
    ensures
        match read_key_share_ch(data) {
            Some(shares) => write_key_share_ch(shares) =~= data,
            None => true,
        },
{
    if let Some(shares) = read_key_share_ch(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 0, 65535);
        let (c, rest) = read_vec(data, 0, 65535).unwrap();
        let w = |k: KeyShare| write_key_share(k);
        let f = |x: Seq<u8>| read_key_share(x);
        assert forall|bb: Seq<u8>| #[trigger] f(bb) is Some implies w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb by {
            lemma_read_key_share_canonical(bb);
        }
        super::lemmas_pl::lemma_write_list_read_list(c, w, f);
        assert(data =~= write_vec(c, 65535) + rest);
    }
}

/// `server_name` in a ClientHello is read back.
pub proof fn lemma_server_name_ch_round_trip(names: Seq<ServerName>)
    requires
        forall|i: int| 0 <= i < names.len() ==> server_name_ok(#[trigger] names[i]),
        1 <= write_list(names, |s: ServerName| write_server_name(s)).len() <= 65535,
    ensures
        read_server_name_ch(write_server_name_ch(names)) == Some(names),
{
    let w = |s: ServerName| write_server_name(s);
    let f = |x: Seq<u8>| read_server_name(x);
    let ok = |s: ServerName| server_name_ok(s);
    assert forall|e: ServerName| #[trigger] ok(e) implies w(e).len() >= 1 by {
        lemma_read_server_name_write(e, seq![]);
    }
    assert forall|e: ServerName, r: Seq<u8>| ok(e) implies #[trigger] f(w(e) + r) == Some((e, r)) by {
        lemma_read_server_name_write(e, r);
    }
    super::lemmas_pl::lemma_read_list_write_list(names, w, f, ok);
    super::lemmas_pl::lemma_read_vec_write_vec(write_list(names, w), 1, 65535, seq![]);
    assert(write_server_name_ch(names) + seq![] =~= write_server_name_ch(names));
}

/// What [`read_server_name_ch`] accepts is one encoding.
pub proof fn lemma_server_name_ch_canonical(data: Seq<u8>)
    ensures
        match read_server_name_ch(data) {
            Some(names) => write_server_name_ch(names) =~= data,
            None => true,
        },
{
    if let Some(names) = read_server_name_ch(data) {
        super::lemmas_pl::lemma_read_vec_canonical(data, 1, 65535);
        let (c, rest) = read_vec(data, 1, 65535).unwrap();
        let w = |s: ServerName| write_server_name(s);
        let f = |x: Seq<u8>| read_server_name(x);
        assert forall|bb: Seq<u8>| #[trigger] f(bb) is Some implies w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb by {
            lemma_read_server_name_canonical(bb);
        }
        super::lemmas_pl::lemma_write_list_read_list(c, w, f);
        assert(data =~= write_vec(c, 65535) + rest);
    }
}

// ---------------------------------------------------------------------------
// The recursive forms of the extension block checks.
// ---------------------------------------------------------------------------

/// [`has_ext`] is "some extension has type `t`".
pub proof fn lemma_has_ext_iff(es: Seq<Ext>, t: u16)
    ensures
        has_ext(es, t) <==> exists|i: int| 0 <= i < es.len() && es[i].etype == t,
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_has_ext_iff(es.skip(1), t);
        if has_ext(es, t) {
            if es[0].etype != t {
                let j = choose|j: int| 0 <= j < es.skip(1).len() && es.skip(1)[j].etype == t;
                assert(es[j + 1].etype == t);
            }
        }
        if exists|i: int| 0 <= i < es.len() && es[i].etype == t {
            let i = choose|i: int| 0 <= i < es.len() && es[i].etype == t;
            if i > 0 {
                assert(es.skip(1)[i - 1].etype == t);
            }
        }
    }
}

/// [`exts_unique`] is [`no_duplicates`]: the recursion and the quantified
/// rule of §4.2 say the same.
pub proof fn lemma_exts_unique_iff(es: Seq<Ext>)
    ensures
        exts_unique(es) <==> no_duplicates(es),
    decreases es.len(),
{
    if es.len() > 0 {
        let t = es.skip(1);
        lemma_exts_unique_iff(t);
        lemma_has_ext_iff(t, es[0].etype);
        if exts_unique(es) {
            assert forall|i: int, j: int| 0 <= i < j < es.len() implies (#[trigger] es[i]).etype != (#[trigger] es[j]).etype by {
                if i == 0 {
                    assert(t[j - 1].etype != es[0].etype);
                } else {
                    assert(t[i - 1].etype != t[j - 1].etype);
                }
            }
        }
        if no_duplicates(es) {
            assert forall|i: int, j: int| 0 <= i < j < t.len() implies (#[trigger] t[i]).etype != (#[trigger] t[j]).etype by {
                assert(es[i + 1].etype != es[j + 1].etype);
            }
            assert(no_duplicates(t));
            if has_ext(t, es[0].etype) {
                let j = choose|j: int| 0 <= j < t.len() && t[j].etype == es[0].etype;
                assert(es[0].etype != es[j + 1].etype);
            }
        }
    }
}

/// [`all_allowed`] is "every extension is allowed".
pub proof fn lemma_all_allowed_iff(es: Seq<Ext>, m: MsgKind)
    ensures
        all_allowed(es, m) <==> (forall|i: int| 0 <= i < es.len() ==> extension_allowed(#[trigger] es[i].etype, m)),
    decreases es.len(),
{
    if es.len() > 0 {
        let t = es.skip(1);
        lemma_all_allowed_iff(t, m);
        if all_allowed(es, m) {
            assert forall|i: int| 0 <= i < es.len() implies extension_allowed(#[trigger] es[i].etype, m) by {
                if i > 0 {
                    assert(t[i - 1].etype == es[i].etype);
                }
            }
        }
        if forall|i: int| 0 <= i < es.len() ==> extension_allowed(#[trigger] es[i].etype, m) {
            assert forall|i: int| 0 <= i < t.len() implies extension_allowed(#[trigger] t[i].etype, m) by {
                assert(es[i + 1].etype == t[i].etype);
            }
        }
    }
}

/// [`all_bodies_ok`] is "every extension's data is well formed".
pub proof fn lemma_all_bodies_ok_iff(es: Seq<Ext>, m: MsgKind)
    ensures
        all_bodies_ok(es, m) <==> (forall|i: int| 0 <= i < es.len() ==> ext_body_ok(#[trigger] es[i], m)),
    decreases es.len(),
{
    if es.len() > 0 {
        let t = es.skip(1);
        lemma_all_bodies_ok_iff(t, m);
        if all_bodies_ok(es, m) {
            assert forall|i: int| 0 <= i < es.len() implies ext_body_ok(#[trigger] es[i], m) by {
                if i > 0 {
                    assert(t[i - 1] == es[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < es.len() ==> ext_body_ok(#[trigger] es[i], m) {
            assert forall|i: int| 0 <= i < t.len() implies ext_body_ok(#[trigger] t[i], m) by {
                assert(es[i + 1] == t[i]);
            }
        }
    }
}

} // verus!
