//! The executable extensions (RFC 8446 §4.2), proven to meet
//! [`super::spec`]: reading an extension block, the §4.2 table of which
//! extension may appear in which message, the typed bodies of the
//! extensions this crate reads (`supported_versions`, `cookie`,
//! `signature_algorithms`, `supported_groups`, `key_share`,
//! `server_name`) and the checks of §4.2 on a block.

use super::reader::Cur;
use super::spec::{
    EXT_ALPN, EXT_CERTIFICATE_AUTHORITIES, EXT_CLIENT_CERTIFICATE_TYPE, EXT_COOKIE, EXT_EARLY_DATA,
    EXT_HEARTBEAT, EXT_KEY_SHARE, EXT_MAX_FRAGMENT_LENGTH, EXT_OID_FILTERS, EXT_PADDING,
    EXT_POST_HANDSHAKE_AUTH, EXT_PRE_SHARED_KEY, EXT_PSK_KEY_EXCHANGE_MODES, EXT_SCT,
    EXT_SERVER_CERTIFICATE_TYPE, EXT_SERVER_NAME, EXT_SIGNATURE_ALGORITHMS,
    EXT_SIGNATURE_ALGORITHMS_CERT, EXT_STATUS_REQUEST, EXT_SUPPORTED_GROUPS,
    EXT_SUPPORTED_VERSIONS, EXT_USE_SRTP, ErrKind, MsgKind,
};
use super::types::{Extension, KeyShare, ServerName};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Lists of uint16.
// ---------------------------------------------------------------------------

/// The spec view of an optional list of `uint16`.
pub open spec fn opt_u16s(r: Option<Vec<u16>>) -> Option<Seq<u16>> {
    match r {
        Some(v) => Some(v@),
        None => None,
    }
}

/// §3.4: read the rest of a vector's contents as `uint16` elements
/// ([`super::spec::read_u16s`]).
pub fn read_u16s(c: &mut Cur<'_>) -> (r: Option<Vec<u16>>)
    ensures
        opt_u16s(r) == super::spec::read_u16s(old(c)@),
        r is Some ==> r->Some_0@.len() <= old(c)@.len(),
{
    let mut acc: Vec<u16> = Vec::new();
    proof {
        super::lemmas_pl::lemma_read_list_len(old(c)@, |x: Seq<u8>| super::spec::read_u16(x));
    }
    while !c.is_empty()
        invariant
            super::lemmas_pl::list_after(acc@, c@, |x: Seq<u8>| super::spec::read_u16(x)) == super::spec::read_list(
                old(c)@,
                |x: Seq<u8>| super::spec::read_u16(x),
            ),
            acc@.len() + c@.len() <= old(c)@.len(),
        decreases c@.len(),
    {
        let ghost before = c@;
        proof {
            super::lemmas_pl::lemma_list_after_step(acc@, before, |x: Seq<u8>| super::spec::read_u16(x));
            super::lemmas_pl::lemma_read_uint_canonical(before, 2);
        }
        let v = c.uint(2)?;
        proof {
            super::lemmas_pl::lemma_read_uint_canonical(before, 2);
        }
        acc.push(v as u16);
    }
    proof {
        super::lemmas_pl::lemma_list_after_empty(acc@, |x: Seq<u8>| super::spec::read_u16(x));
        assert(c@ =~= Seq::<u8>::empty());
        super::lemmas_pl::lemma_read_list_len(old(c)@, |x: Seq<u8>| super::spec::read_u16(x));
    }
    Some(acc)
}

/// §4.2: whether the data is exactly one vector with these bounds, and
/// its contents ([`super::spec::read_vec`] with nothing left over).
pub open spec fn whole_vec(data: Seq<u8>, floor: nat, ceil: nat) -> Option<Seq<u8>> {
    match super::spec::read_vec(data, floor, ceil) {
        None => None,
        Some((c, rest)) => if rest.len() != 0 {
            None
        } else {
            Some(c)
        },
    }
}

/// The contents of `data` if it is exactly one vector ([`whole_vec`]).
pub fn vec_whole<'a>(data: &'a [u8], floor: usize, ceil: usize) -> (r: Option<Cur<'a>>)
    requires
        ceil < 16777216,
    ensures
        match r {
            Some(c) => whole_vec(data@, floor as nat, ceil as nat) == Some(c@),
            None => whole_vec(data@, floor as nat, ceil as nat) is None,
        },
{
    let mut c = Cur::new(data);
    let content = c.vec(floor, ceil)?;
    if !c.is_empty() {
        return None;
    }
    Some(content)
}

// ---------------------------------------------------------------------------
// §4.2: which extension may appear in which message.
// ---------------------------------------------------------------------------

/// §4.2, the table ([`super::spec::extension_allowed`]).
pub fn extension_allowed(t: u16, m: MsgKind) -> (b: bool)
    ensures
        b == super::spec::extension_allowed(t, m),
{
    let ch = matches!(m, MsgKind::Ch);
    let sh = matches!(m, MsgKind::Sh);
    let ee = matches!(m, MsgKind::Ee);
    let ct = matches!(m, MsgKind::Ct);
    let cr = matches!(m, MsgKind::Cr);
    let nst = matches!(m, MsgKind::Nst);
    let hrr = matches!(m, MsgKind::Hrr);
    if t == EXT_SERVER_NAME
        || t == EXT_MAX_FRAGMENT_LENGTH
        || t == EXT_SUPPORTED_GROUPS
        || t == EXT_USE_SRTP
        || t == EXT_HEARTBEAT
        || t == EXT_ALPN
        || t == EXT_CLIENT_CERTIFICATE_TYPE
        || t == EXT_SERVER_CERTIFICATE_TYPE
    {
        // CH, EE
        ch || ee
    } else if t == EXT_STATUS_REQUEST || t == EXT_SCT {
        // CH, CR, CT
        ch || cr || ct
    } else if t == EXT_SIGNATURE_ALGORITHMS || t == EXT_CERTIFICATE_AUTHORITIES || t == EXT_SIGNATURE_ALGORITHMS_CERT {
        // CH, CR
        ch || cr
    } else if t == EXT_PADDING || t == EXT_PSK_KEY_EXCHANGE_MODES || t == EXT_POST_HANDSHAKE_AUTH {
        // CH
        ch
    } else if t == EXT_KEY_SHARE || t == EXT_SUPPORTED_VERSIONS {
        // CH, SH, HRR
        ch || sh || hrr
    } else if t == EXT_PRE_SHARED_KEY {
        // CH, SH
        ch || sh
    } else if t == EXT_EARLY_DATA {
        // CH, EE, NST
        ch || ee || nst
    } else if t == EXT_COOKIE {
        // CH, HRR
        ch || hrr
    } else if t == EXT_OID_FILTERS {
        // CR
        cr
    } else {
        // Not a row of the table.
        true
    }
}

// ---------------------------------------------------------------------------
// §4.2: Extension and the extension block.
// ---------------------------------------------------------------------------

/// §4.2: read one `Extension` ([`super::spec::read_ext`]).
pub fn read_ext<'a>(c: &mut Cur<'a>) -> (r: Option<Extension<'a>>)
    ensures
        match r {
            Some(e) => super::spec::read_ext(old(c)@) == Some((e@, final(c)@)),
            None => super::spec::read_ext(old(c)@) is None,
        },
{
    let ghost before = c@;
    let t = c.uint(2)?;
    proof {
        super::lemmas_pl::lemma_read_uint_canonical(before, 2);
        super::lemmas_pl::lemma_pow256_widths();
    }
    let content = c.vec(0, 65535)?;
    Some(Extension { etype: t as u16, data: content.as_slice() })
}

/// The spec view of an optional list of extensions.
pub open spec fn opt_exts(r: Option<Vec<Extension<'_>>>) -> Option<Seq<super::spec::Ext>> {
    match r {
        Some(v) => Some(super::types::views(v@)),
        None => None,
    }
}

/// §4.2: read `Extension extensions<floor..ceil>`
/// ([`super::spec::read_exts`]). The list has at most a quarter as many
/// extensions as the input has bytes, whatever the lengths say.
pub fn read_exts<'a>(c: &mut Cur<'a>, floor: usize, ceil: usize) -> (r: Option<Vec<Extension<'a>>>)
    requires
        ceil < 16777216,
    ensures
        match r {
            Some(es) => {
                &&& super::spec::read_exts(old(c)@, floor as nat, ceil as nat) == Some((super::types::views(es@), final(c)@))
                &&& es@.len() * 4 <= old(c)@.len()
            },
            None => super::spec::read_exts(old(c)@, floor as nat, ceil as nat) is None,
        },
{
    let mut sub = c.vec(floor, ceil)?;
    let ghost content = sub@;
    let mut acc: Vec<Extension<'a>> = Vec::new();
    proof {
        assert(super::types::views(acc@) =~= Seq::<super::spec::Ext>::empty());
        super::lemmas_pl::lemma_read_vec_canonical(old(c)@, floor as nat, ceil as nat);
    }
    while !sub.is_empty()
        invariant
            super::spec::read_vec(old(c)@, floor as nat, ceil as nat) == Some((content, c@)),
            content.len() <= old(c)@.len(),
            super::lemmas_pl::list_after(super::types::views(acc@), sub@, |x: Seq<u8>| super::spec::read_ext(x))
                == super::spec::read_list(content, |x: Seq<u8>| super::spec::read_ext(x)),
            acc@.len() * 4 + sub@.len() <= content.len(),
        decreases sub@.len(),
    {
        let ghost before = sub@;
        proof {
            super::lemmas_pl::lemma_list_after_step(super::types::views(acc@), before, |x: Seq<u8>| super::spec::read_ext(x));
            super::lemmas_ext::lemma_read_ext_canonical(before);
        }
        let e = read_ext(&mut sub)?;
        proof {
            super::types::lemma_views_push(acc@, e);
        }
        acc.push(e);
    }
    proof {
        super::lemmas_pl::lemma_list_after_empty(super::types::views(acc@), |x: Seq<u8>| super::spec::read_ext(x));
        assert(sub@ =~= Seq::<u8>::empty());
    }
    Some(acc)
}

// ---------------------------------------------------------------------------
// The extensions that are read.
// ---------------------------------------------------------------------------

/// §4.2.8: read one `KeyShareEntry` ([`super::spec::read_key_share`]).
pub fn read_key_share<'a>(c: &mut Cur<'a>) -> (r: Option<KeyShare<'a>>)
    ensures
        match r {
            Some(k) => super::spec::read_key_share(old(c)@) == Some((k@, final(c)@)),
            None => super::spec::read_key_share(old(c)@) is None,
        },
{
    let ghost before = c@;
    let g = c.uint(2)?;
    proof {
        super::lemmas_pl::lemma_read_uint_canonical(before, 2);
        super::lemmas_pl::lemma_pow256_widths();
    }
    let kx = c.vec(1, 65535)?;
    Some(KeyShare { group: g as u16, key_exchange: kx.as_slice() })
}

/// RFC 6066 §3: read one `ServerName` ([`super::spec::read_server_name`]).
pub fn read_server_name<'a>(c: &mut Cur<'a>) -> (r: Option<ServerName<'a>>)
    ensures
        match r {
            Some(s) => super::spec::read_server_name(old(c)@) == Some((s@, final(c)@)),
            None => super::spec::read_server_name(old(c)@) is None,
        },
{
    let nt = c.uint(1)?;
    if nt != 0 {
        return None;
    }
    let h = c.vec(1, 65535)?;
    Some(ServerName { host_name: h.as_slice() })
}

/// §4.2.1: `supported_versions` in a ClientHello
/// ([`super::spec::read_supported_versions_ch`]).
pub fn supported_versions_ch(data: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        opt_u16s(r) == super::spec::read_supported_versions_ch(data@),
{
    let mut c = vec_whole(data, 2, 254)?;
    read_u16s(&mut c)
}

/// §4.2.1: `supported_versions` in a ServerHello or HelloRetryRequest
/// ([`super::spec::read_supported_versions_sh`]).
pub fn supported_versions_sh(data: &[u8]) -> (r: Option<u16>)
    ensures
        r == super::spec::read_supported_versions_sh(data@),
{
    let mut c = Cur::new(data);
    let v = c.uint(2)?;
    if !c.is_empty() {
        return None;
    }
    proof {
        super::lemmas_pl::lemma_read_uint_canonical(data@, 2);
        super::lemmas_pl::lemma_pow256_widths();
    }
    Some(v as u16)
}

/// §4.2.2: `cookie` ([`super::spec::read_cookie`]).
pub fn cookie(data: &[u8]) -> (r: Option<&[u8]>)
    ensures
        match r {
            Some(s) => super::spec::read_cookie(data@) == Some(s@),
            None => super::spec::read_cookie(data@) is None,
        },
{
    let c = vec_whole(data, 1, 65535)?;
    Some(c.as_slice())
}

/// §4.2.3: `signature_algorithms` and `signature_algorithms_cert`
/// ([`super::spec::read_signature_schemes`]).
pub fn signature_schemes(data: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        opt_u16s(r) == super::spec::read_signature_schemes(data@),
{
    let mut c = vec_whole(data, 2, 65534)?;
    read_u16s(&mut c)
}

/// §4.2.7: `supported_groups` ([`super::spec::read_named_groups`]).
pub fn named_groups(data: &[u8]) -> (r: Option<Vec<u16>>)
    ensures
        opt_u16s(r) == super::spec::read_named_groups(data@),
{
    let mut c = vec_whole(data, 2, 65535)?;
    read_u16s(&mut c)
}

/// §4.2.8: `key_share` in a ClientHello
/// ([`super::spec::read_key_share_ch`]).
pub fn key_share_ch<'a>(data: &'a [u8]) -> (r: Option<Vec<KeyShare<'a>>>)
    ensures
        match r {
            Some(v) => super::spec::read_key_share_ch(data@) == Some(super::types::views(v@)),
            None => super::spec::read_key_share_ch(data@) is None,
        },
{
    let mut sub = vec_whole(data, 0, 65535)?;
    let ghost content = sub@;
    let mut acc: Vec<KeyShare<'a>> = Vec::new();
    proof {
        assert(super::types::views(acc@) =~= Seq::<super::spec::KeyShare>::empty());
    }
    while !sub.is_empty()
        invariant
            whole_vec(data@, 0, 65535) == Some(content),
            super::lemmas_pl::list_after(super::types::views(acc@), sub@, |x: Seq<u8>| super::spec::read_key_share(x))
                == super::spec::read_list(content, |x: Seq<u8>| super::spec::read_key_share(x)),
        decreases sub@.len(),
    {
        let ghost before = sub@;
        proof {
            super::lemmas_pl::lemma_list_after_step(super::types::views(acc@), before, |x: Seq<u8>| super::spec::read_key_share(x));
            super::lemmas_ext::lemma_read_key_share_canonical(before);
        }
        let k = read_key_share(&mut sub)?;
        proof {
            super::types::lemma_views_push(acc@, k);
        }
        acc.push(k);
    }
    proof {
        super::lemmas_pl::lemma_list_after_empty(super::types::views(acc@), |x: Seq<u8>| super::spec::read_key_share(x));
        assert(sub@ =~= Seq::<u8>::empty());
    }
    Some(acc)
}

/// §4.2.8: `key_share` in a HelloRetryRequest
/// ([`super::spec::read_key_share_hrr`]).
pub fn key_share_hrr(data: &[u8]) -> (r: Option<u16>)
    ensures
        r == super::spec::read_key_share_hrr(data@),
{
    supported_versions_sh(data)
}

/// §4.2.8: `key_share` in a ServerHello
/// ([`super::spec::read_key_share_sh`]).
pub fn key_share_sh<'a>(data: &'a [u8]) -> (r: Option<KeyShare<'a>>)
    ensures
        match r {
            Some(k) => super::spec::read_key_share_sh(data@) == Some(k@),
            None => super::spec::read_key_share_sh(data@) is None,
        },
{
    let mut c = Cur::new(data);
    let k = read_key_share(&mut c)?;
    if !c.is_empty() {
        return None;
    }
    Some(k)
}

/// RFC 6066 §3: `server_name` in a ClientHello
/// ([`super::spec::read_server_name_ch`]).
pub fn server_name_ch<'a>(data: &'a [u8]) -> (r: Option<Vec<ServerName<'a>>>)
    ensures
        match r {
            Some(v) => super::spec::read_server_name_ch(data@) == Some(super::types::views(v@)),
            None => super::spec::read_server_name_ch(data@) is None,
        },
{
    let mut sub = vec_whole(data, 1, 65535)?;
    let ghost content = sub@;
    let mut acc: Vec<ServerName<'a>> = Vec::new();
    proof {
        assert(super::types::views(acc@) =~= Seq::<super::spec::ServerName>::empty());
    }
    while !sub.is_empty()
        invariant
            whole_vec(data@, 1, 65535) == Some(content),
            super::lemmas_pl::list_after(super::types::views(acc@), sub@, |x: Seq<u8>| super::spec::read_server_name(x))
                == super::spec::read_list(content, |x: Seq<u8>| super::spec::read_server_name(x)),
        decreases sub@.len(),
    {
        let ghost before = sub@;
        proof {
            super::lemmas_pl::lemma_list_after_step(super::types::views(acc@), before, |x: Seq<u8>| super::spec::read_server_name(x));
            super::lemmas_ext::lemma_read_server_name_canonical(before);
        }
        let s = read_server_name(&mut sub)?;
        proof {
            super::types::lemma_views_push(acc@, s);
        }
        acc.push(s);
    }
    proof {
        super::lemmas_pl::lemma_list_after_empty(super::types::views(acc@), |x: Seq<u8>| super::spec::read_server_name(x));
        assert(sub@ =~= Seq::<u8>::empty());
    }
    Some(acc)
}

/// RFC 6066 §3: `server_name` in EncryptedExtensions
/// ([`super::spec::server_name_ee_ok`]).
pub fn server_name_ee_ok(data: &[u8]) -> (b: bool)
    ensures
        b == super::spec::server_name_ee_ok(data@),
{
    data.is_empty()
}

/// Whether the `extension_data` of `e`, in a message of kind `m`, has the
/// structure of the extensions this crate reads
/// ([`super::spec::ext_body_ok`]).
pub fn ext_body_ok(e: &Extension<'_>, m: MsgKind) -> (b: bool)
    ensures
        b == super::spec::ext_body_ok(e@, m),
{
    if e.etype == EXT_SUPPORTED_VERSIONS {
        if matches!(m, MsgKind::Ch) {
            supported_versions_ch(e.data).is_some()
        } else {
            supported_versions_sh(e.data).is_some()
        }
    } else if e.etype == EXT_COOKIE {
        cookie(e.data).is_some()
    } else if e.etype == EXT_SIGNATURE_ALGORITHMS || e.etype == EXT_SIGNATURE_ALGORITHMS_CERT {
        signature_schemes(e.data).is_some()
    } else if e.etype == EXT_SUPPORTED_GROUPS {
        named_groups(e.data).is_some()
    } else if e.etype == EXT_KEY_SHARE {
        if matches!(m, MsgKind::Ch) {
            key_share_ch(e.data).is_some()
        } else if matches!(m, MsgKind::Hrr) {
            key_share_hrr(e.data).is_some()
        } else {
            key_share_sh(e.data).is_some()
        }
    } else if e.etype == EXT_SERVER_NAME {
        if matches!(m, MsgKind::Ch) {
            server_name_ch(e.data).is_some()
        } else {
            server_name_ee_ok(e.data)
        }
    } else {
        true
    }
}

// ---------------------------------------------------------------------------
// The checks of §4.2 on an extension block.
// ---------------------------------------------------------------------------

/// §4.2: "There MUST NOT be more than one extension of the same type in a
/// given extension block" ([`super::spec::no_duplicates`]).
pub fn no_duplicates(es: &[Extension<'_>]) -> (b: bool)
    ensures
        b == super::spec::no_duplicates(super::types::views(es@)),
{
    let n = es.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == es@.len(),
            i <= n,
            forall|a: int, b: int| 0 <= a < b < n && a < i ==> (#[trigger] es@[a]).etype != (#[trigger] es@[b]).etype,
        decreases n - i,
    {
        let ti = match es.get(i) {
            Some(e) => e.etype,
            None => 0,
        };
        // i < n, so this does not saturate.
        let mut j: usize = i.saturating_add(1);
        while j < n
            invariant
                n == es@.len(),
                i < n,
                i < j <= n || j == i.saturating_add(1),
                ti == es@[i as int].etype,
                forall|a: int, b: int| 0 <= a < b < n && a < i ==> (#[trigger] es@[a]).etype != (#[trigger] es@[b]).etype,
                forall|b: int| i < b < j ==> (#[trigger] es@[b]).etype != ti,
            decreases n - j,
        {
            let tj = match es.get(j) {
                Some(e) => e.etype,
                None => 0,
            };
            if tj == ti {
                proof {
                    assert(!super::spec::no_duplicates(super::types::views(es@))) by {
                        assert(super::types::views(es@)[i as int].etype == es@[i as int].etype);
                        assert(super::types::views(es@)[j as int].etype == es@[j as int].etype);
                    }
                }
                return false;
            }
            // j < n, so this does not saturate.
            j = j.saturating_add(1);
        }
        // i < n, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert forall|a: int, b: int| 0 <= a < b < super::types::views(es@).len() implies (#[trigger] super::types::views(es@)[a]).etype != (
        #[trigger] super::types::views(es@)[b]).etype by {
            assert(super::types::views(es@)[a].etype == es@[a].etype);
            assert(super::types::views(es@)[b].etype == es@[b].etype);
        }
    }
    true
}

/// Whether an extension of type `t` is in the block
/// ([`super::spec::has_ext`]).
pub fn has_ext(es: &[Extension<'_>], t: u16) -> (b: bool)
    ensures
        b == super::spec::has_ext(super::types::views(es@), t),
{
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] es@[k]).etype != t,
        decreases es@.len() - i,
    {
        let ti = match es.get(i) {
            Some(e) => e.etype,
            None => 0,
        };
        if ti == t {
            proof {
                assert(super::types::views(es@)[i as int].etype == t);
                super::lemmas_ext::lemma_has_ext_iff(super::types::views(es@), t);
            }
            return true;
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas_ext::lemma_has_ext_iff(super::types::views(es@), t);
        assert forall|k: int| 0 <= k < super::types::views(es@).len() implies (#[trigger] super::types::views(es@)[k]).etype
            != t by {
            assert(super::types::views(es@)[k].etype == es@[k].etype);
        }
    }
    false
}

/// Whether every extension of the block is allowed in a message of kind
/// `m` ([`super::spec::extension_allowed`]).
fn all_allowed(es: &[Extension<'_>], m: MsgKind) -> (b: bool)
    ensures
        b == (forall|i: int| 0 <= i < es@.len() ==> super::spec::extension_allowed(#[trigger] es@[i].etype, m)),
{
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            forall|k: int| 0 <= k < i ==> super::spec::extension_allowed(#[trigger] es@[k].etype, m),
        decreases es@.len() - i,
    {
        let ok = match es.get(i) {
            Some(e) => extension_allowed(e.etype, m),
            None => true,
        };
        if !ok {
            return false;
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    true
}

/// Whether every extension of the block has the structure its type calls
/// for ([`super::spec::ext_body_ok`]).
fn all_bodies_ok(es: &[Extension<'_>], m: MsgKind) -> (b: bool)
    ensures
        b == (forall|i: int| 0 <= i < es@.len() ==> super::spec::ext_body_ok((#[trigger] es@[i])@, m)),
{
    let mut i: usize = 0;
    while i < es.len()
        invariant
            i <= es@.len(),
            forall|k: int| 0 <= k < i ==> super::spec::ext_body_ok((#[trigger] es@[k])@, m),
        decreases es@.len() - i,
    {
        let ok = match es.get(i) {
            Some(e) => ext_body_ok(e, m),
            None => true,
        };
        if !ok {
            return false;
        }
        // i < len, so this does not saturate.
        i = i.saturating_add(1);
    }
    true
}

/// §4.2: the checks on an extension block, in order
/// ([`super::spec::check_extensions`]).
pub fn check_extensions(es: &[Extension<'_>], m: MsgKind) -> (r: Option<ErrKind>)
    ensures
        super::contract::check_extensions_ensures(super::types::views(es@), m, r),
{
    proof {
        super::lemmas_ext::lemma_exts_unique_iff(super::types::views(es@));
        super::lemmas_ext::lemma_all_allowed_iff(super::types::views(es@), m);
        super::lemmas_ext::lemma_all_bodies_ok_iff(super::types::views(es@), m);
    }
    if !no_duplicates(es) {
        return Some(ErrKind::DuplicateExtension);
    }
    if !all_allowed(es, m) {
        proof {
            assert(!(forall|i: int| 0 <= i < super::types::views(es@).len() ==> super::spec::extension_allowed(
                #[trigger] super::types::views(es@)[i].etype,
                m,
            ))) by {
                let i = choose|i: int| 0 <= i < es@.len() && !super::spec::extension_allowed(es@[i].etype, m);
                assert(super::types::views(es@)[i].etype == es@[i].etype);
            }
        }
        return Some(ErrKind::ExtensionNotAllowed);
    }
    if !all_bodies_ok(es, m) {
        proof {
            assert(!(forall|i: int| 0 <= i < super::types::views(es@).len() ==> super::spec::ext_body_ok(#[trigger] super::types::views(es@)[i], m))) by {
                let i = choose|i: int| 0 <= i < es@.len() && !super::spec::ext_body_ok(es@[i]@, m);
                assert(super::types::views(es@)[i] == es@[i]@);
            }
        }
        return Some(ErrKind::Decode);
    }
    proof {
        assert(forall|i: int| 0 <= i < super::types::views(es@).len() ==> super::spec::extension_allowed(
            #[trigger] super::types::views(es@)[i].etype,
            m,
        )) by {
            assert forall|i: int| 0 <= i < super::types::views(es@).len() implies super::spec::extension_allowed(
                #[trigger] super::types::views(es@)[i].etype,
                m,
            ) by {
                assert(super::types::views(es@)[i].etype == es@[i].etype);
            }
        }
        assert(forall|i: int| 0 <= i < super::types::views(es@).len() ==> super::spec::ext_body_ok(#[trigger] super::types::views(es@)[i], m)) by {
            assert forall|i: int| 0 <= i < super::types::views(es@).len() implies super::spec::ext_body_ok(#[trigger] super::types::views(es@)[i], m) by {
                assert(super::types::views(es@)[i] == es@[i]@);
            }
        }
    }
    None
}

} // verus!
