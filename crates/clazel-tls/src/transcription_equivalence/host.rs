//! RFC 6066 §3: the crate's typed host (`host/spec.rs`, `sni_host_name`) and
//! the server_name of its ClientHello (`hello::client_spec::extensions`)
//! against the clean-room `transcription::server_name` (#140):
//! [`theorem_host_equivalence`].
//!
//! The two sides model the host differently. The crate's is typed, a `Dns`
//! name (no trailing dot) or an `Ip` address in octets; the transcription's is
//! the client's text, from which it decides whether it is a DNS hostname. A
//! crate host is compared with every text that names it ([`names_host`]): a
//! `Dns` name with or without one trailing dot, and an `Ip` address with any
//! textual IP literal, one with a `:` (IPv6, RFC 4291 §2.2) or one ending in a
//! dot and a non-empty run of digits (IPv4 dotted decimal, RFC 1123 §2.1).
//!
//! No domain. Since #139 both sides read RFC 6066 §3 with RFC 2181 §11: a
//! DNS hostname is labels of 1 to 63 ASCII octets, at most 253 octets, with
//! no `:` and a last label not all digits (no IP literal). The crate checks
//! this octet by octet (`host::spec::dns_labels_ok`), the transcription label
//! by label ([`lemma_dns_labels`]). (The transcription first used LDH
//! labels, and the crate sent any name of 1 to 253 octets; see
//! docs/ERRATA.md, "RFC 6066 §3: no rule for a host that is not a DNS
//! hostname".)
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A textual IP literal: one with a `:`, or one ending in a dot and a
/// non-empty run of digits.
pub open spec fn ip_literal(t: Seq<u8>) -> bool {
    (exists|i: int| 0 <= i < t.len() && t[i] == 0x3Au8)
    || (exists|k: int| 0 <= k && k + 1 < t.len() && t[k] == 0x2Eu8
        && #[trigger] crate::transcription::server_name::all_digits(t.subrange(k + 1, t.len() as int)))
}

/// The text `t` names the crate's host.
pub open spec fn names_host(host: crate::host::spec::Host, t: Seq<u8>) -> bool {
    match host {
        crate::host::spec::Host::Dns(name) => t == name || t == name.push(0x2Eu8),
        crate::host::spec::Host::Ip(address) => ip_literal(t),
    }
}

/// The crate's one-name ServerNameList is the transcription's.
pub proof fn lemma_server_name_bytes(name: Seq<u8>)
    ensures
        crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: name }])
            == crate::transcription::server_name::write_server_name_list(name),
{
    let s = crate::spec::ServerName { host_name: name };
    let w = |x: crate::spec::ServerName| crate::spec::write_server_name(x);
    assert(seq![s].skip(1) =~= Seq::<crate::spec::ServerName>::empty());
    assert(crate::spec::write_list(Seq::<crate::spec::ServerName>::empty(), w) == Seq::<u8>::empty());
    assert(crate::spec::write_list(seq![s], w) == w(seq![s][0]) + crate::spec::write_list(seq![s].skip(1), w));
    assert(crate::spec::write_list(seq![s], w) =~= crate::spec::write_server_name(s));
    super::schedule::lemma_write_vec(name, 65535);
    assert(crate::transcription::presentation::encode_uint(0, 0) =~= Seq::<u8>::empty());
    assert(crate::transcription::presentation::encode_uint(0, 1) =~= seq![0u8]);
    super::schedule::lemma_write_vec(crate::spec::write_server_name(s), 65535);
}

/// A byte string of HostName octets with one more byte is one with those
/// bytes and that one.
pub proof fn lemma_octets_push(s: Seq<u8>, x: u8)
    ensures
        crate::transcription::server_name::all_host_name_octets(s.push(x))
            == (crate::transcription::server_name::all_host_name_octets(s) && crate::transcription::server_name::is_host_name_octet(x)),
    decreases s.len(),
{
    let p = s.push(x);
    if s.len() > 0 {
        assert(p[0] == s[0]);
        assert(p.subrange(1, p.len() as int) =~= s.subrange(1, s.len() as int).push(x));
        lemma_octets_push(s.subrange(1, s.len() as int), x);
    } else {
        assert(p[0] == x);
        assert(p.subrange(1, p.len() as int) =~= Seq::<u8>::empty());
        assert(crate::transcription::server_name::all_host_name_octets(Seq::<u8>::empty()));
    }
}

/// The same for digits.
pub proof fn lemma_digits_push(s: Seq<u8>, x: u8)
    ensures
        crate::transcription::server_name::all_digits(s.push(x))
            == (crate::transcription::server_name::all_digits(s) && crate::transcription::server_name::is_digit(x)),
    decreases s.len(),
{
    let p = s.push(x);
    if s.len() > 0 {
        assert(p[0] == s[0]);
        assert(p.subrange(1, p.len() as int) =~= s.subrange(1, s.len() as int).push(x));
        lemma_digits_push(s.subrange(1, s.len() as int), x);
    } else {
        assert(p[0] == x);
        assert(p.subrange(1, p.len() as int) =~= Seq::<u8>::empty());
        assert(crate::transcription::server_name::all_digits(Seq::<u8>::empty()));
    }
}

/// Every octet of a string of HostName octets is one.
pub proof fn lemma_octets_index(l: Seq<u8>, i: int)
    requires
        crate::transcription::server_name::all_host_name_octets(l),
        0 <= i < l.len(),
    ensures crate::transcription::server_name::is_host_name_octet(l[i]),
    decreases l.len(),
{
    if i > 0 {
        let r = l.subrange(1, l.len() as int);
        lemma_octets_index(r, i - 1);
        assert(r[i - 1] == l[i]);
    }
}

/// The first label of `split_labels(rest, c)` starts with `c`.
pub proof fn lemma_split_prefix(rest: Seq<u8>, c: Seq<u8>)
    ensures ({
        let l = crate::transcription::server_name::split_labels(rest, c);
        l.len() >= 1 && l[0].len() >= c.len() && l[0].subrange(0, c.len() as int) == c
    }),
    decreases rest.len(),
{
    let l = crate::transcription::server_name::split_labels(rest, c);
    if rest.len() == 0 {
        assert(l[0] == c);
        assert(c.subrange(0, c.len() as int) =~= c);
    } else if rest[0] == 0x2E {
        assert(l[0] == c);
        assert(c.subrange(0, c.len() as int) =~= c);
    } else {
        let cx = c.push(rest[0]);
        lemma_split_prefix(rest.subrange(1, rest.len() as int), cx);
        assert(l[0].subrange(0, c.len() as int) =~= l[0].subrange(0, cx.len() as int).subrange(0, c.len() as int));
        assert(cx.subrange(0, c.len() as int) =~= c);
    }
}

/// The crate's octet-by-octet reading of a name (`host::spec::dns_labels_ok`)
/// is the transcription's label rule (`is_dns_host_name` without its length),
/// from any point inside a label `cur`.
pub proof fn lemma_dns_labels(rest: Seq<u8>, cur: Seq<u8>)
    requires
        cur.len() <= 63,
        crate::transcription::server_name::all_host_name_octets(cur),
    ensures ({
        let l = crate::transcription::server_name::split_labels(rest, cur);
        crate::host::spec::dns_labels_ok(rest, cur.len(), crate::transcription::server_name::all_digits(cur))
            == (crate::transcription::server_name::all_dns_labels(l) && !crate::transcription::server_name::all_digits(l.last()))
    }),
    decreases rest.len(),
{
    let l = crate::transcription::server_name::split_labels(rest, cur);
    let empty = Seq::<Seq<u8>>::empty();
    if rest.len() == 0 {
        assert(l == seq![cur]);
        assert(l.subrange(1, l.len() as int) =~= empty);
        assert(crate::transcription::server_name::all_dns_labels(empty));
    } else if rest[0] == 0x2E {
        let r = rest.subrange(1, rest.len() as int);
        let t = crate::transcription::server_name::split_labels(r, seq![]);
        assert(l == seq![cur] + t);
        assert(crate::transcription::server_name::all_host_name_octets(Seq::<u8>::empty()));
        assert(crate::transcription::server_name::all_digits(Seq::<u8>::empty()));
        lemma_dns_labels(r, seq![]);
        lemma_split_prefix(r, seq![]);
        assert(l[0] == cur);
        assert(l.subrange(1, l.len() as int) =~= t);
        assert(l.last() == t.last());
    } else {
        let x = rest[0];
        let r = rest.subrange(1, rest.len() as int);
        let cx = cur.push(x);
        assert(l == crate::transcription::server_name::split_labels(r, cx));
        lemma_octets_push(cur, x);
        lemma_digits_push(cur, x);
        if crate::transcription::server_name::is_host_name_octet(x) && cur.len() < 63 {
            lemma_dns_labels(r, cx);
        } else {
            lemma_split_prefix(r, cx);
            if crate::transcription::server_name::all_dns_labels(l) {
                assert(crate::transcription::server_name::is_dns_label(l[0]));
                assert(l[0][cur.len() as int] == l[0].subrange(0, cx.len() as int)[cur.len() as int]);
                lemma_octets_index(l[0], cur.len() as int);
            }
        }
    }
}

/// A name the crate's reading accepts does not end in a dot.
pub proof fn lemma_no_trailing_dot(rest: Seq<u8>, run: nat, digits: bool)
    requires crate::host::spec::dns_labels_ok(rest, run, digits), rest.len() > 0,
    ensures rest.last() != 0x2Eu8,
    decreases rest.len(),
{
    let r = rest.subrange(1, rest.len() as int);
    if rest.len() > 1 {
        let (run2, digits2) = if rest[0] == 0x2E { (0nat, true) } else { (run + 1, digits && 0x30u8 <= rest[0] && rest[0] <= 0x39u8) };
        lemma_no_trailing_dot(r, run2, digits2);
        assert(r.last() == rest.last());
    } else {
        assert(r.len() == 0);
        assert(rest.last() == rest[0]);
        assert(!crate::host::spec::dns_labels_ok(r, 0, true));
    }
}

/// A `Dns` host is accepted by the crate exactly when its name is a DNS
/// hostname by the transcription's rule (RFC 6066 §3, RFC 2181 §11).
pub proof fn lemma_host_ok_is_hostname(name: Seq<u8>)
    ensures
        crate::host::spec::host_ok(crate::host::spec::Host::Dns(name))
            == crate::transcription::server_name::is_dns_host_name(name),
        crate::host::spec::host_ok(crate::host::spec::Host::Dns(name)) ==> name.len() > 0 && name.last() != 0x2Eu8,
{
    if crate::host::spec::host_ok(crate::host::spec::Host::Dns(name)) {
        lemma_no_trailing_dot(name, 0, true);
    }
    assert(crate::transcription::server_name::all_host_name_octets(Seq::<u8>::empty()));
    assert(crate::transcription::server_name::all_digits(Seq::<u8>::empty()));
    lemma_dns_labels(name, seq![]);
    if name.len() == 0 {
        let l = crate::transcription::server_name::split_labels(name, seq![]);
        assert(l == seq![Seq::<u8>::empty()]);
        assert(!crate::transcription::server_name::is_dns_label(l[0]));
    }
}

/// If every label is a DNS label, every byte of the name is a dot or a
/// HostName octet.
pub proof fn lemma_labels_bytes(name: Seq<u8>, current: Seq<u8>)
    requires
        crate::transcription::server_name::all_dns_labels(crate::transcription::server_name::split_labels(name, current)),
    ensures
        crate::transcription::server_name::all_host_name_octets(current),
        forall|i: int| 0 <= i < name.len() ==> name[i] == 0x2Eu8 || crate::transcription::server_name::is_host_name_octet(#[trigger] name[i]),
    decreases name.len(),
{
    let rest = name.subrange(1, name.len() as int);
    if name.len() == 0 {
        let l = crate::transcription::server_name::split_labels(name, current);
        assert(l[0] == current);
    } else if name[0] == 0x2E {
        let tail = crate::transcription::server_name::split_labels(rest, seq![]);
        let l = seq![current] + tail;
        assert(l.subrange(1, l.len() as int) =~= tail);
        lemma_labels_bytes(rest, seq![]);
        assert forall|i: int| 0 <= i < name.len() implies name[i] == 0x2Eu8
            || crate::transcription::server_name::is_host_name_octet(#[trigger] name[i]) by {
            if i > 0 { assert(name[i] == rest[i - 1]); }
        }
    } else {
        lemma_labels_bytes(rest, current.push(name[0]));
        lemma_octets_push(current, name[0]);
        assert forall|i: int| 0 <= i < name.len() implies name[i] == 0x2Eu8
            || crate::transcription::server_name::is_host_name_octet(#[trigger] name[i]) by {
            if i > 0 { assert(name[i] == rest[i - 1]); }
        }
    }
}
/// A name without dots is one label.
pub proof fn lemma_one_label(d: Seq<u8>, current: Seq<u8>)
    requires forall|i: int| 0 <= i < d.len() ==> #[trigger] d[i] != 0x2Eu8,
    ensures crate::transcription::server_name::split_labels(d, current) == seq![current + d],
    decreases d.len(),
{
    if d.len() > 0 {
        let rest = d.subrange(1, d.len() as int);
        lemma_one_label(rest, current.push(d[0]));
        assert(current.push(d[0]) + rest =~= current + d);
    } else {
        assert(current + d =~= current);
    }
}

/// The last label of `x . d`, `d` without dots, is `d`.
pub proof fn lemma_last_label(x: Seq<u8>, d: Seq<u8>, current: Seq<u8>)
    requires forall|i: int| 0 <= i < d.len() ==> #[trigger] d[i] != 0x2Eu8,
    ensures ({
        let l = crate::transcription::server_name::split_labels(x + seq![0x2Eu8] + d, current);
        l.len() > 0 && l.last() == d
    }),
    decreases x.len(),
{
    let name = x + seq![0x2Eu8] + d;
    let rest = name.subrange(1, name.len() as int);
    if x.len() == 0 {
        assert(rest =~= d);
        lemma_one_label(d, seq![]);
        assert(Seq::<u8>::empty() + d =~= d);
    } else {
        let xr = x.subrange(1, x.len() as int);
        assert(rest =~= xr + seq![0x2Eu8] + d);
        if x[0] == 0x2E {
            lemma_last_label(xr, d, seq![]);
        } else {
            lemma_last_label(xr, d, current.push(x[0]));
        }
    }
}

/// Digits are not dots.
pub proof fn lemma_digits_no_dot(d: Seq<u8>)
    requires crate::transcription::server_name::all_digits(d),
    ensures forall|i: int| 0 <= i < d.len() ==> #[trigger] d[i] != 0x2Eu8,
    decreases d.len(),
{
    if d.len() > 0 {
        let rest = d.subrange(1, d.len() as int);
        lemma_digits_no_dot(rest);
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] != 0x2Eu8 by {
            if i > 0 { assert(d[i] == rest[i - 1]); }
        }
    }
}

/// A textual IP literal is never a DNS hostname, so the transcription sends
/// no server_name for one.
pub proof fn lemma_ip_literal(t: Seq<u8>)
    requires ip_literal(t),
    ensures crate::transcription::server_name::host_name_for(t) is None,
{
    let name = if t.len() > 0 && t.last() == 0x2E { t.drop_last() } else { t };
    if exists|i: int| 0 <= i < t.len() && t[i] == 0x3Au8 {
        let i = choose|i: int| 0 <= i < t.len() && t[i] == 0x3Au8;
        if crate::transcription::server_name::all_dns_labels(crate::transcription::server_name::split_labels(name, seq![])) {
            lemma_labels_bytes(name, seq![]);
            if i < name.len() {
                assert(name[i] == t[i]);
            }
        }
        assert(i < name.len());
    } else {
        let k = choose|k: int| 0 <= k && k + 1 < t.len() && t[k] == 0x2Eu8
            && #[trigger] crate::transcription::server_name::all_digits(t.subrange(k + 1, t.len() as int));
        let x = t.subrange(0, k);
        let d = t.subrange(k + 1, t.len() as int);
        assert(t =~= x + seq![0x2Eu8] + d);
        lemma_digits_no_dot(d);
        assert(t.last() == d.last());
        assert(name == t);
        lemma_last_label(x, d, seq![]);
    }
}

/// A DNS hostname by the grammar, with or without one trailing dot, is sent
/// as itself.
pub proof fn lemma_dns_name(name: Seq<u8>)
    requires
        crate::transcription::server_name::is_dns_host_name(name),
        name.len() > 0 && name.last() != 0x2Eu8,
    ensures
        crate::transcription::server_name::host_name_for(name) == Some(name),
        crate::transcription::server_name::host_name_for(name.push(0x2Eu8)) == Some(name),
{
    assert(name.push(0x2Eu8).drop_last() =~= name);
}

/// The server_name of the crate's ClientHello: the extension the
/// transcription would send for every text that names the host.
pub proof fn lemma_client_hello_server_name(c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>)
    requires
        crate::host::spec::host_ok(c.host),
        names_host(c.host, t),
    ensures
        crate::transcription::extensions::find_extension(
            super::messages::exts_view(crate::hello::client_spec::extensions(c, cookie)), 0)
            == match crate::transcription::server_name::host_name_for(t) {
                Some(host_name) => Some(crate::transcription::server_name::write_server_name_list(host_name)),
                None => None,
            },
{
    let es = crate::hello::client_spec::extensions(c, cookie);
    super::auth_flight::lemma_find(es, 0);
    match c.host {
        crate::host::spec::Host::Dns(name) => {
            lemma_host_ok_is_hostname(name);
            lemma_dns_name(name);
            lemma_server_name_bytes(name);
            assert(es[0].etype == 0);
        },
        crate::host::spec::Host::Ip(address) => {
            lemma_ip_literal(t);
            assert forall|i: int| 0 <= i < es.len() implies #[trigger] es[i].etype != 0 by {}
            lemma_no_type(es, 0);
        },
    }
}

/// A block with no extension of type `t` has none.
pub proof fn lemma_no_type(es: Seq<crate::spec::Ext>, t: u16)
    requires forall|i: int| 0 <= i < es.len() ==> #[trigger] es[i].etype != t,
    ensures !crate::spec::has_ext(es, t),
    decreases es.len(),
{
    if es.len() > 0 {
        let rest = es.skip(1);
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i].etype != t by {
            assert(rest[i] == es[i + 1]);
        }
        lemma_no_type(rest, t);
        assert(es[0].etype != t);
    }
}

/// RFC 6066 §3, for every host the crate accepts and every text that names
/// it: the crate's server_name host name is the transcription's, and its
/// ClientHello carries exactly the server_name extension the
/// transcription's would (`client_hello_names_host`'s condition). And the
/// crate accepts a `Dns` name exactly when the transcription calls it a DNS
/// hostname, so the names it refuses as the caller's error are exactly the
/// ones the transcription would send no server_name for.
pub proof fn theorem_host_equivalence()
    ensures
        forall|name: Seq<u8>|
            #[trigger] crate::host::spec::host_ok(crate::host::spec::Host::Dns(name))
                == crate::transcription::server_name::is_dns_host_name(name),
        forall|host: crate::host::spec::Host, t: Seq<u8>|
            crate::host::spec::host_ok(host) && #[trigger] names_host(host, t)
                ==> crate::host::spec::sni_host_name(host) == crate::transcription::server_name::host_name_for(t),
        forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>|
            crate::host::spec::host_ok(c.host) && #[trigger] names_host(c.host, t)
                ==> crate::transcription::extensions::find_extension(
                    super::messages::exts_view(#[trigger] crate::hello::client_spec::extensions(c, cookie)), 0)
                    == match crate::transcription::server_name::host_name_for(t) {
                        Some(host_name) => Some(crate::transcription::server_name::write_server_name_list(host_name)),
                        None => None,
                    },
{
    assert forall|name: Seq<u8>|
        #[trigger] crate::host::spec::host_ok(crate::host::spec::Host::Dns(name))
            == crate::transcription::server_name::is_dns_host_name(name) by {
        lemma_host_ok_is_hostname(name);
    }
    assert forall|host: crate::host::spec::Host, t: Seq<u8>|
        crate::host::spec::host_ok(host) && #[trigger] names_host(host, t)
        implies crate::host::spec::sni_host_name(host) == crate::transcription::server_name::host_name_for(t) by {
        match host {
            crate::host::spec::Host::Dns(name) => { lemma_host_ok_is_hostname(name); lemma_dns_name(name); },
            crate::host::spec::Host::Ip(address) => { lemma_ip_literal(t); },
        }
    }
    assert forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>|
        crate::host::spec::host_ok(c.host) && #[trigger] names_host(c.host, t)
        implies crate::transcription::extensions::find_extension(
            super::messages::exts_view(#[trigger] crate::hello::client_spec::extensions(c, cookie)), 0)
            == match crate::transcription::server_name::host_name_for(t) {
                Some(host_name) => Some(crate::transcription::server_name::write_server_name_list(host_name)),
                None => None,
            } by {
        lemma_client_hello_server_name(c, cookie, t);
    }
}

} // verus!
