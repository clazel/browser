//! The executable request builder, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::field::string::copy;
use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::serialize::serialize_request;
use clazel_http::message::types::RequestBuf;
use clazel_url::host::record::append;
use clazel_url::host::serialize::push_decimal;
use clazel_url::url::record::ParsedUrl;
use clazel_url::url::serialize::url_path_serializer;

verus! {

/// `ascii_octets`: `s` as octets, or `None` if a code point is not ASCII.
fn ascii_octets_exec(s: &[u32]) -> (out: Option<Vec<u8>>)
    ensures
        match out {
            Some(v) => ascii_octets(s@) == Some(v@),
            None => ascii_octets(s@) is None,
        },
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(s@.skip(0) =~= s@);
    while i < s.len()
        invariant
            i <= s.len(),
            all_ascii(s@) == (all_ascii(s@.take(i as int)) && all_ascii(s@.skip(i as int))),
            all_ascii(s@.take(i as int)),
            out@ =~= s@.take(i as int).map_values(|c: u32| c as u8),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            assert(s@.skip(i as int)[0] == *c);
            assert(s@.skip(i as int).drop_first() =~= s@.skip(i + 1));
            if *c >= 0x80 {
                return None;
            }
            proof {
                lemma_all_ascii_push(s@.take(i as int), *c);
                assert(s@.take(i as int).push(*c) =~= s@.take(i + 1));
            }
            out.push(*c as u8);
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(s.len() as int) =~= s@);
    Some(out)
}

/// Appending an ASCII code point keeps a string ASCII, and `all_ascii`
/// of a concatenation is the conjunction.
proof fn lemma_all_ascii_push(s: Seq<u32>, c: u32)
    ensures
        all_ascii(s.push(c)) == (all_ascii(s) && c < 0x80),
    decreases s.len()
{
    assert(s.push(c)[0] == if s.len() > 0 { s[0] } else { c });
    if s.len() > 0 {
        assert(s.push(c).drop_first() =~= s.drop_first().push(c));
        lemma_all_ascii_push(s.drop_first(), c);
    } else {
        assert(s.push(c).drop_first() =~= Seq::<u32>::empty());
        assert(all_ascii(Seq::<u32>::empty()));
    }
}

/// `origin_form` (RFC 9112 §3.2.1).
fn origin_form_exec(url: &ParsedUrl) -> (out: Vec<u32>)
    ensures
        out@ == origin_form(url@),
{
    let mut out = url_path_serializer(&url.path);
    if out.is_empty() {
        out.push(0x2F);
        assert(out@ =~= seq![0x2Fu32]);
    }
    if let Some(q) = &url.query {
        let ghost before = out@;
        out.push(0x3F);
        append(&mut out, q.as_slice());
        assert(out@ =~= before + seq![0x3Fu32] + q@);
    }
    out
}

/// `host_value` (RFC 9110 §7.2).
fn host_value_exec(url: &ParsedUrl) -> (out: Option<Vec<u32>>)
    ensures
        match out {
            Some(v) => host_value(url@) == Some(v@),
            None => host_value(url@) is None,
        },
{
    match &url.host {
        Some(host) => {
            let mut out = host.serialize();
            if let Some(port) = url.port {
                let ghost before = out@;
                out.push(0x3A);
                push_decimal(port as u32, &mut out);
                assert(out@ =~= before + seq![0x3Au32] + clazel_url::host::spec::serialize_integer(port as nat));
            }
            Some(out)
        },
        None => None,
    }
}

/// Are two code point strings equal?
fn eq32(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a.get(i) != b.get(i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// A field line from two literals.
fn line(name: &[u8], value: &[u8]) -> (out: FieldLineBuf)
    ensures
        out.name@ == name@,
        out.value@ == value@,
{
    FieldLineBuf { name: copy(name), value: copy(value) }
}

/// `request_bytes`: the bytes to send for `url`, or `None` if this client
/// does not fetch it.
pub fn request_bytes(url: &ParsedUrl) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::request_bytes_ensures(url@, match out {
            Some(v) => Some(v@),
            None => None,
        }),
{
    if !eq32(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70]) || !url.username.is_empty() || !url.password.is_empty() {
        return None;
    }
    let target = ascii_octets_exec(origin_form_exec(url).as_slice())?;
    let host = ascii_octets_exec(host_value_exec(url)?.as_slice())?;
    let fields = vec![
        FieldLineBuf { name: copy(&[0x48, 0x6F, 0x73, 0x74]), value: host },
        line(&[0x43, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E], &[0x63, 0x6C, 0x6F, 0x73, 0x65]),
        line(&[0x41, 0x63, 0x63, 0x65, 0x70, 0x74], &[0x2A, 0x2F, 0x2A]),
        line(&[0x55, 0x73, 0x65, 0x72, 0x2D, 0x41, 0x67, 0x65, 0x6E, 0x74], &[0x63, 0x6C, 0x61, 0x7A, 0x65, 0x6C]),
    ];
    let req = RequestBuf { method: copy(&[0x47, 0x45, 0x54]), target, fields };
    assert(req@ == request_for(url@)->Some_0) by {
        assert(clazel_http::field::types::lines_view(req.fields@) =~= request_for(url@)->Some_0.fields);
    }
    serialize_request(&req)
}

/// `request_bytes_cookie`: the bytes to send for `url` carrying the
/// cookie-string `cookie` (Fetch §3.1.1 steps 6 to 8: a `Cookie` field,
/// last, unless it is empty), or `None` if this client does not fetch it.
pub fn request_bytes_cookie(url: &ParsedUrl, cookie: &[u8]) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::request_bytes_cookie_ensures(url@, cookie@, match out {
            Some(v) => Some(v@),
            None => None,
        }),
{
    if !eq32(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70]) || !url.username.is_empty() || !url.password.is_empty() {
        return None;
    }
    let target = ascii_octets_exec(origin_form_exec(url).as_slice())?;
    let host = ascii_octets_exec(host_value_exec(url)?.as_slice())?;
    let mut fields = vec![
        FieldLineBuf { name: copy(&[0x48, 0x6F, 0x73, 0x74]), value: host },
        line(&[0x43, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E], &[0x63, 0x6C, 0x6F, 0x73, 0x65]),
        line(&[0x41, 0x63, 0x63, 0x65, 0x70, 0x74], &[0x2A, 0x2F, 0x2A]),
        line(&[0x55, 0x73, 0x65, 0x72, 0x2D, 0x41, 0x67, 0x65, 0x6E, 0x74], &[0x63, 0x6C, 0x61, 0x7A, 0x65, 0x6C]),
    ];
    let ghost base = clazel_http::field::types::lines_view(fields@);
    if !cookie.is_empty() {
        fields.push(line(&[0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65], cookie));
    }
    let req = RequestBuf { method: copy(&[0x47, 0x45, 0x54]), target, fields };
    assert(req@ == request_for_cookie(url@, cookie@)->Some_0) by {
        assert(base =~= request_for(url@)->Some_0.fields);
        assert(clazel_http::field::types::lines_view(req.fields@) =~= request_for_cookie(url@, cookie@)->Some_0.fields);
    }
    serialize_request(&req)
}

/// `connect_to`: the host for the resolver and the port.
pub fn connect_to(url: &ParsedUrl) -> (out: Option<(Vec<u8>, u16)>)
    ensures
        super::contract::connect_to_ensures(url@, match out {
            Some((h, p)) => Some((h@, p as nat)),
            None => None,
        }),
{
    let host = url.host.as_ref()?;
    let h = ascii_octets_exec(host.serialize().as_slice())?;
    Some((h, url.port.unwrap_or(80)))
}

/// `is_interim` (RFC 9110 §15.2).
pub fn is_interim(status: u16) -> (r: bool)
    ensures
        super::contract::is_interim_ensures(status as nat, r),
{
    (100..=199).contains(&status) && status != 101
}

} // verus!
