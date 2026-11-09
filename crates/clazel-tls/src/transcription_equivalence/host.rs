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
//! Domain, and why: **a `Dns` name is a DNS hostname by the transcription's
//! grammar** (LDH labels of at most 63 octets, a last label not all digits).
//! The crate sends server_name for every `Dns` name it accepts (1 to 253
//! octets, no trailing dot) and the transcription only for such hostnames.
//! On the others the two disagree, and [`lemma_names_outside_the_grammar`]
//! proves that they do; which reading to keep is open (docs/ERRATA.md,
//! "RFC 6066 §3: no rule for a host that is not a DNS hostname").

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

/// A byte string of letters, digits and hyphens with one more byte is one
/// with those bytes and that one.
pub proof fn lemma_ldh_push(s: Seq<u8>, x: u8)
    ensures
        crate::transcription::server_name::all_let_dig_hyp(s.push(x))
            == (crate::transcription::server_name::all_let_dig_hyp(s) && crate::transcription::server_name::is_let_dig_hyp(x)),
    decreases s.len(),
{
    let p = s.push(x);
    if s.len() > 0 {
        assert(p[0] == s[0]);
        assert(p.subrange(1, p.len() as int) =~= s.subrange(1, s.len() as int).push(x));
        lemma_ldh_push(s.subrange(1, s.len() as int), x);
    } else {
        assert(p[0] == x);
        assert(p.subrange(1, p.len() as int) =~= Seq::<u8>::empty());
        assert(crate::transcription::server_name::all_let_dig_hyp(Seq::<u8>::empty()));
    }
}

/// If every label is LDH, every byte of the name is a dot or LDH.
pub proof fn lemma_labels_ldh_bytes(name: Seq<u8>, current: Seq<u8>)
    requires
        crate::transcription::server_name::all_ldh_labels(crate::transcription::server_name::split_labels(name, current)),
    ensures
        crate::transcription::server_name::all_let_dig_hyp(current),
        forall|i: int| 0 <= i < name.len() ==> name[i] == 0x2Eu8 || crate::transcription::server_name::is_let_dig_hyp(#[trigger] name[i]),
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
        lemma_labels_ldh_bytes(rest, seq![]);
        assert forall|i: int| 0 <= i < name.len() implies name[i] == 0x2Eu8
            || crate::transcription::server_name::is_let_dig_hyp(#[trigger] name[i]) by {
            if i > 0 { assert(name[i] == rest[i - 1]); }
        }
    } else {
        lemma_labels_ldh_bytes(rest, current.push(name[0]));
        lemma_ldh_push(current, name[0]);
        assert forall|i: int| 0 <= i < name.len() implies name[i] == 0x2Eu8
            || crate::transcription::server_name::is_let_dig_hyp(#[trigger] name[i]) by {
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
        if crate::transcription::server_name::all_ldh_labels(crate::transcription::server_name::split_labels(name, seq![])) {
            lemma_labels_ldh_bytes(name, seq![]);
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

/// A `Dns` name outside the grammar: the crate sends it, the transcription
/// sends no server_name. This is the disagreement the domain excludes.
pub proof fn lemma_names_outside_the_grammar(name: Seq<u8>)
    requires
        crate::host::spec::host_ok(crate::host::spec::Host::Dns(name)),
        !crate::transcription::server_name::is_dns_host_name(name),
    ensures
        crate::host::spec::sni_host_name(crate::host::spec::Host::Dns(name)) == Some(name),
        crate::transcription::server_name::host_name_for(name) is None,
{
}

/// The server_name of the crate's ClientHello: the extension the
/// transcription would send for every text that names the host.
pub proof fn lemma_client_hello_server_name(c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>)
    requires
        crate::host::spec::host_ok(c.host),
        names_host(c.host, t),
        c.host matches crate::host::spec::Host::Dns(name) ==> crate::transcription::server_name::is_dns_host_name(name),
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
/// it, under the domain above: the crate's server_name host name is the
/// transcription's, and its ClientHello carries exactly the server_name
/// extension the transcription's would (`client_hello_names_host`'s
/// condition). Without the domain, the two differ exactly on `Dns` names
/// outside the grammar ([`lemma_names_outside_the_grammar`]).
pub proof fn theorem_host_equivalence()
    ensures
        forall|host: crate::host::spec::Host, t: Seq<u8>|
            crate::host::spec::host_ok(host) && #[trigger] names_host(host, t)
                && (host matches crate::host::spec::Host::Dns(name) ==> crate::transcription::server_name::is_dns_host_name(name))
                ==> crate::host::spec::sni_host_name(host) == crate::transcription::server_name::host_name_for(t),
        forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>|
            crate::host::spec::host_ok(c.host) && #[trigger] names_host(c.host, t)
                && (c.host matches crate::host::spec::Host::Dns(name) ==> crate::transcription::server_name::is_dns_host_name(name))
                ==> crate::transcription::extensions::find_extension(
                    super::messages::exts_view(#[trigger] crate::hello::client_spec::extensions(c, cookie)), 0)
                    == match crate::transcription::server_name::host_name_for(t) {
                        Some(host_name) => Some(crate::transcription::server_name::write_server_name_list(host_name)),
                        None => None,
                    },
{
    assert forall|host: crate::host::spec::Host, t: Seq<u8>|
        crate::host::spec::host_ok(host) && #[trigger] names_host(host, t)
            && (host matches crate::host::spec::Host::Dns(name) ==> crate::transcription::server_name::is_dns_host_name(name))
        implies crate::host::spec::sni_host_name(host) == crate::transcription::server_name::host_name_for(t) by {
        match host {
            crate::host::spec::Host::Dns(name) => { lemma_dns_name(name); },
            crate::host::spec::Host::Ip(address) => { lemma_ip_literal(t); },
        }
    }
    assert forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>, t: Seq<u8>|
        crate::host::spec::host_ok(c.host) && #[trigger] names_host(c.host, t)
            && (c.host matches crate::host::spec::Host::Dns(name) ==> crate::transcription::server_name::is_dns_host_name(name))
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
