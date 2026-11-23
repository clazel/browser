//! The executable request builder, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::field::string::copy;
use clazel_http::field::types::FieldLineBuf;
use clazel_http::message::serialize::serialize_request;
use clazel_http::message::types::RequestBuf;
use clazel_origin::exec::ParsedOrigin;
use clazel_url::host::record::append;
use clazel_url::host::serialize::push_decimal;
use clazel_url::url::record::{ParsedUrl, clone_host, clone_opt_host};
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

/// `is_fetched_scheme`: `http` or `https`.
fn is_fetched_scheme_exec(scheme: &[u32]) -> (r: bool)
    ensures
        r == is_fetched_scheme(scheme@),
{
    proof {
        assert(clazel_url::url::spec::http_str() =~= seq![0x68u32, 0x74, 0x74, 0x70]);
        assert(clazel_url::url::spec::https_str() =~= seq![0x68u32, 0x74, 0x74, 0x70, 0x73]);
    }
    eq32(scheme, &[0x68, 0x74, 0x74, 0x70]) || eq32(scheme, &[0x68, 0x74, 0x74, 0x70, 0x73])
}

/// `uses_tls` (RFC 9110 §4.2.2): whether the connection for `url` speaks
/// TLS, which is when its scheme is `https`.
pub fn uses_tls(url: &ParsedUrl) -> (r: bool)
    ensures
        super::contract::uses_tls_ensures(url@, r),
{
    proof {
        assert(clazel_url::url::spec::https_str() =~= seq![0x68u32, 0x74, 0x74, 0x70, 0x73]);
    }
    eq32(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73])
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
    if !is_fetched_scheme_exec(url.scheme.as_slice()) || !url.username.is_empty() || !url.password.is_empty() {
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
    if !is_fetched_scheme_exec(url.scheme.as_slice()) || !url.username.is_empty() || !url.password.is_empty() {
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

/// `connect_to`: the host for the resolver and the port, the URL's or the
/// scheme's default (443 for `https`, 80 otherwise).
pub fn connect_to(url: &ParsedUrl) -> (out: Option<(Vec<u8>, u16)>)
    ensures
        super::contract::connect_to_ensures(url@, match out {
            Some((h, p)) => Some((h@, p as nat)),
            None => None,
        }),
{
    let host = url.host.as_ref()?;
    let h = ascii_octets_exec(host.serialize().as_slice())?;
    let port = match url.port {
        Some(p) => p,
        None => if uses_tls(url) {
            443
        } else {
            80
        },
    };
    Some((h, port))
}

/// `is_interim` (RFC 9110 §15.2).
pub fn is_interim(status: u16) -> (r: bool)
    ensures
        super::contract::is_interim_ensures(status as nat, r),
{
    (100..=199).contains(&status) && status != 101
}


// ===========================================================================
// Item 6.16: a request with a method and a body.
// ===========================================================================

/// [`Payload`], executable.
pub struct PayloadBuf {
    /// the `Content-Type` field value
    pub content_type: Vec<u8>,
    /// the octets
    pub bytes: Vec<u8>,
}

impl View for PayloadBuf {
    type V = Payload;

    open spec fn view(&self) -> Payload {
        Payload { content_type: self.content_type@, bytes: self.bytes@ }
    }
}

/// [`Req`], executable.
pub struct ReqBuf {
    /// the method
    pub method: Vec<u8>,
    /// the body, or null
    pub body: Option<PayloadBuf>,
    /// the origin of the document that made the request, or none
    pub initiator: Option<ParsedOrigin>,
    /// the redirect-taint is not "same-origin"
    pub origin_tainted: bool,
    /// the author's header lines (item 7.16)
    pub headers: Vec<FieldLineBuf>,
    /// mode "cors" (item 7.16)
    pub cors: bool,
}

impl View for ReqBuf {
    type V = Req;

    open spec fn view(&self) -> Req {
        Req {
            method: self.method@,
            body: match self.body {
                Some(p) => Some(p@),
                None => None,
            },
            initiator: match self.initiator {
                Some(o) => Some(o@),
                None => None,
            },
            origin_tainted: self.origin_tainted,
            headers: clazel_http::field::types::lines_view(self.headers@),
            cors: self.cors,
        }
    }
}

/// [`get_req`], executable: `GET`, no body, no client.
pub fn get_req_buf() -> (out: ReqBuf)
    ensures
        out@ == get_req(),
{
    let out = ReqBuf { method: vec![0x47, 0x45, 0x54], body: None, initiator: None, origin_tainted: false, headers: Vec::new(), cors: false };
    assert(out@.method =~= lit_get());
    assert(out@.headers =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
    out
}

/// A copy of an origin.
pub fn clone_origin(o: &ParsedOrigin) -> (out: ParsedOrigin)
    ensures
        out@ == o@,
{
    match o {
        ParsedOrigin::Opaque(id) => ParsedOrigin::Opaque(*id),
        ParsedOrigin::Tuple { scheme, host, port, domain } => {
            let d = clone_opt_host(domain);
            let out = ParsedOrigin::Tuple {
                scheme: clazel_url::host::record::copy(scheme.as_slice()),
                host: clone_host(host),
                port: *port,
                domain: d,
            };
            assert(clazel_origin::exec::opt_host_view(out->Tuple_domain) == clazel_origin::exec::opt_host_view(*domain)) by {
                assert(clazel_url::host::record::option_view(out->Tuple_domain) == clazel_url::host::record::option_view(*domain));
            }
            assert(out@ == o@);
            out
        },
    }
}

/// A copy of an optional origin.
pub fn clone_opt_origin(o: &Option<ParsedOrigin>) -> (out: Option<ParsedOrigin>)
    ensures
        match (out, *o) {
            (Some(a), Some(b)) => a@ == b@,
            (None, None) => true,
            _ => false,
        },
{
    let Some(o) = o else {
        return None;
    };
    Some(clone_origin(o))
}

/// Are two octet strings equal?
fn eq8(a: &[u8], b: &[u8]) -> (r: bool)
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

/// `m` is "GET".
pub fn is_get(m: &[u8]) -> (r: bool)
    ensures
        r == (m@ == lit_get()),
{
    proof {
        assert(lit_get() =~= seq![0x47u8, 0x45, 0x54]);
    }
    eq8(m, &[0x47, 0x45, 0x54])
}

/// `m` is "POST".
pub fn is_post(m: &[u8]) -> (r: bool)
    ensures
        r == (m@ == lit_post()),
{
    proof {
        assert(lit_post() =~= seq![0x50u8, 0x4F, 0x53, 0x54]);
    }
    eq8(m, &[0x50, 0x4F, 0x53, 0x54])
}

/// `m` is "HEAD".
fn is_head(m: &[u8]) -> (r: bool)
    ensures
        r == (m@ == lit_head()),
{
    proof {
        assert(lit_head() =~= seq![0x48u8, 0x45, 0x41, 0x44]);
    }
    eq8(m, &[0x48, 0x45, 0x41, 0x44])
}

/// [`is_safe_method`] (RFC 9110 §9.2.1).
fn is_safe_method_exec(m: &[u8]) -> (r: bool)
    ensures
        r == is_safe_method(m@),
{
    proof {
        assert(lit_options() =~= seq![0x4Fu8, 0x50, 0x54, 0x49, 0x4F, 0x4E, 0x53]);
        assert(lit_trace() =~= seq![0x54u8, 0x52, 0x41, 0x43, 0x45]);
    }
    is_get(m) || is_head(m) || eq8(m, &[0x4F, 0x50, 0x54, 0x49, 0x4F, 0x4E, 0x53]) || eq8(m, &[0x54, 0x52, 0x41, 0x43, 0x45])
}

/// [`method_is_safe`].
pub fn method_is_safe(req: &ReqBuf) -> (r: bool)
    ensures
        super::contract::method_is_safe_ensures(req@, r),
{
    is_safe_method_exec(req.method.as_slice())
}

/// [`req_ok`].
pub fn req_ok_exec(req: &ReqBuf) -> (r: bool)
    ensures
        r == req_ok(req@),
{
    let g = is_get(req.method.as_slice());
    let p = is_post(req.method.as_slice());
    if !(g || p) {
        return false;
    }
    match &req.body {
        Some(b) => {
            if g {
                return false;
            }
            if b.bytes.len() > 0x100_0000 {
                return false;
            }
        },
        None => {},
    }
    author_headers_ok_exec(req.headers.as_slice())
}

/// `s` as octets, narrowing each code point.
fn narrow_exec(s: &[u32]) -> (out: Vec<u8>)
    ensures
        out@ == s@.map_values(|c: u32| c as u8),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ =~= s@.take(i as int).map_values(|c: u32| c as u8),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c as u8);
            assert(s@.take(i as int + 1) =~= s@.take(i as int).push(*c));
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(s.len() as int) =~= s@);
    out
}

/// [`decimal_octets`].
fn decimal_exec(n: u32) -> (out: Vec<u8>)
    ensures
        out@ == decimal_octets(n as nat),
{
    let mut d: Vec<u32> = Vec::new();
    push_decimal(n, &mut d);
    assert(d@ =~= clazel_url::host::spec::serialize_integer(n as nat));
    narrow_exec(d.as_slice())
}

/// "null".
fn null_value() -> (v: Vec<u8>)
    ensures
        v@ == lit_null(),
{
    let v = vec![0x6Eu8, 0x75, 0x6C, 0x6C];
    assert(v@ =~= lit_null());
    v
}

/// [`origin_value`].
fn origin_value_exec(url: &ParsedUrl, req: &ReqBuf) -> (out: Option<Vec<u8>>)
    ensures
        match out {
            Some(v) => origin_value(url@, req@) == Some(v@),
            None => origin_value(url@, req@) is None,
        },
{
    match &req.initiator {
        None => Some(null_value()),
        Some(o) => {
            if req.origin_tainted {
                return Some(null_value());
            }
            match o {
                ParsedOrigin::Tuple { scheme, .. } => {
                    proof {
                        assert(clazel_url::url::spec::https_str() =~= seq![0x68u32, 0x74, 0x74, 0x70, 0x73]);
                    }
                    if !req.cors && eq32(scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73]) && !eq32(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73]) {
                        Some(null_value())
                    } else {
                        ascii_octets_exec(clazel_origin::exec::serialization_of_origin_exec(o).as_slice())
                    }
                },
                ParsedOrigin::Opaque(_) => Some(null_value()),
            }
        },
    }
}

/// `request_bytes_req_cookie`: the bytes to send for `url` as `req`, carrying
/// the cookie-string `cookie`: the head (RFC 9112 §3, §5; the fields of
/// [`request_for_req_cookie`]) then the body's octets (§6.2); `None` if this
/// client does not build it.
pub fn request_bytes_req_cookie(url: &ParsedUrl, req: &ReqBuf, cookie: &[u8]) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::request_bytes_req_cookie_ensures(url@, req@, cookie@, match out {
            Some(v) => Some(v@),
            None => None,
        }),
{
    if !req_ok_exec(req) {
        return None;
    }
    if !is_fetched_scheme_exec(url.scheme.as_slice()) || !url.username.is_empty() || !url.password.is_empty() {
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
    proof {
        assert(base =~= request_for(url@)->Some_0.fields);
        assert(lit_content_type() =~= seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65]);
        assert(lit_content_length() =~= seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68]);
        assert(lit_origin() =~= seq![0x4Fu8, 0x72, 0x69, 0x67, 0x69, 0x6E]);
    }
    // Content-Type and Content-Length (Fetch §4.6 steps 6 to 9).
    match &req.body {
        Some(p) => {
            fields.push(line(&[0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65], p.content_type.as_slice()));
            // Never truncates: `req_ok` bounds the length by 16 MiB.
            let n = p.bytes.len() as u32;
            fields.push(FieldLineBuf {
                name: copy(&[0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68]),
                value: decimal_exec(n),
            });
        },
        None => {
            if is_post(req.method.as_slice()) {
                fields.push(FieldLineBuf {
                    name: copy(&[0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68]),
                    value: decimal_exec(0),
                });
            }
        },
    }
    let ghost with_body = clazel_http::field::types::lines_view(fields@);
    assert(with_body =~= base + body_field_lines(req@));
    // The author's headers (item 7.16).
    let mut k: usize = 0;
    while k < req.headers.len()
        invariant
            k <= req.headers.len(),
            clazel_http::field::types::lines_view(fields@) =~= with_body + clazel_http::field::types::lines_view(req.headers@).take(k as int),
        decreases req.headers.len() - k,
    {
        if let Some(h) = req.headers.get(k) {
            let ghost before = fields@;
            fields.push(FieldLineBuf { name: copy(h.name.as_slice()), value: copy(h.value.as_slice()) });
            proof {
                assert(clazel_http::field::types::lines_view(req.headers@).take(k as int + 1) =~= clazel_http::field::types::lines_view(req.headers@).take(
                    k as int,
                ).push(h@));
                assert(clazel_http::field::types::lines_view(fields@) =~= clazel_http::field::types::lines_view(before).push(h@));
            }
        }
        // Never saturates: k < req.headers.len().
        k = k.saturating_add(1);
    }
    assert(clazel_http::field::types::lines_view(req.headers@).take(req.headers.len() as int) =~= req@.headers);
    let ghost with_headers = clazel_http::field::types::lines_view(fields@);
    // Origin (Fetch §4.6 step 13; item 7.16: every request in mode "cors").
    if req.cors || !(is_get(req.method.as_slice()) || is_head(req.method.as_slice())) {
        let v = origin_value_exec(url, req)?;
        fields.push(FieldLineBuf { name: copy(&[0x4F, 0x72, 0x69, 0x67, 0x69, 0x6E]), value: v });
    }
    let ghost with_origin = clazel_http::field::types::lines_view(fields@);
    assert(with_origin =~= with_headers + origin_field_lines(url@, req@)->Some_0);
    // Cookie (step 22.1).
    if !cookie.is_empty() {
        fields.push(line(&[0x43, 0x6F, 0x6F, 0x6B, 0x69, 0x65], cookie));
    }
    let head = RequestBuf { method: copy(req.method.as_slice()), target, fields };
    assert(head@ == request_for_req_cookie(url@, req@, cookie@)->Some_0) by {
        assert(clazel_http::field::types::lines_view(head.fields@) =~= request_for_req_cookie(url@, req@, cookie@)->Some_0.fields);
    }
    let mut bytes = serialize_request(&head)?;
    if let Some(p) = &req.body {
        clazel_http::field::string::append(&mut bytes, p.bytes.as_slice());
    }
    assert(bytes@ =~= clazel_http::message::spec::serialize_request(head@) + body_bytes(req@));
    Some(bytes)
}

/// `request_bytes_req`: [`request_bytes_req_cookie`] with no cookies.
pub fn request_bytes_req(url: &ParsedUrl, req: &ReqBuf) -> (out: Option<Vec<u8>>)
    ensures
        match out {
            Some(v) => super::spec::request_bytes_req(url@, req@) == Some(v@),
            None => super::spec::request_bytes_req(url@, req@) is None,
        },
{
    let empty: &[u8] = &[];
    let r = request_bytes_req_cookie(url, req, empty);
    assert(empty@ =~= Seq::<u8>::empty());
    r
}

/// `rewrite_for_redirect` (Fetch HTTP-redirect fetch step 12).
pub fn rewrite_for_redirect(status: u16, req: ReqBuf) -> (out: ReqBuf)
    ensures
        super::contract::rewrite_for_redirect_ensures(status as nat, req@, out@),
{
    let post = is_post(req.method.as_slice());
    let get = is_get(req.method.as_slice());
    let head = is_head(req.method.as_slice());
    if ((status == 301 || status == 302) && post) || (status == 303 && !get && !head) {
        let out = ReqBuf {
            method: vec![0x47, 0x45, 0x54],
            body: None,
            initiator: req.initiator,
            origin_tainted: req.origin_tainted,
            headers: req.headers,
            cors: req.cors,
        };
        assert(out@.method =~= lit_get());
        assert(out@ == super::spec::rewrite_for_redirect(status as nat, req@));
        out
    } else {
        req
    }
}


// ---------------------------------------------------------------------------
// Item 7.16: author headers.
// ---------------------------------------------------------------------------

/// The view of a list of names.
pub open spec fn names_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|x: Vec<u8>| x@)
}

/// [`byte_lowercase`].
pub fn byte_lowercase_exec(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == byte_lowercase(s@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ =~= byte_lowercase(s@.take(i as int)),
        decreases s.len() - i,
    {
        if let Some(b) = s.get(i) {
            let c = if 0x41 <= *b && *b <= 0x5A { *b + 0x20 } else { *b };
            let ghost before = out@;
            out.push(c);
            proof {
                assert(s@.take(i as int + 1) =~= s@.take(i as int).push(*b));
                assert(byte_lowercase(s@.take(i as int + 1)) =~= byte_lowercase(s@.take(i as int)).push(c));
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(s.len() as int) =~= s@);
    out
}

/// [`starts_with`].
pub fn starts_with_exec(s: &[u8], p: &[u8]) -> (r: bool)
    ensures
        r == starts_with(s@, p@),
{
    if p.len() > s.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < p.len()
        invariant
            i <= p.len(),
            p.len() <= s.len(),
            forall|k: int| 0 <= k < i ==> s@[k] == p@[k],
        decreases p.len() - i,
    {
        if s.get(i) != p.get(i) {
            assert(s@.take(p.len() as int)[i as int] != p@[i as int]);
            return false;
        }
        // Never saturates: i < p.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(p.len() as int) =~= p@);
    true
}

/// [`in_names`] is `contains`.
proof fn lemma_in_names(ns: Seq<Seq<u8>>, x: Seq<u8>)
    ensures
        in_names(ns, x) == ns.contains(x),
    decreases ns.len(),
{
    if ns.len() > 0 {
        lemma_in_names(ns.drop_first(), x);
        if ns.drop_first().contains(x) {
            let j = choose|j: int| 0 <= j < ns.drop_first().len() && ns.drop_first()[j] == x;
            assert(ns[j + 1] == x);
        }
        if ns.contains(x) && ns[0] != x {
            let j = choose|j: int| 0 <= j < ns.len() && ns[j] == x;
            assert(ns.drop_first()[j - 1] == x);
        }
    }
}

/// `names` holds `l`.
fn contains_name(names: &Vec<Vec<u8>>, l: &[u8]) -> (r: bool)
    ensures
        r == in_names(names_view(names@), l@),
{
    proof {
        lemma_in_names(names_view(names@), l@);
    }
    let mut k: usize = 0;
    while k < names.len()
        invariant
            k <= names.len(),
            forall|j: int| 0 <= j < k ==> names@[j]@ != l@,
            in_names(names_view(names@), l@) == names_view(names@).contains(l@),
        decreases names.len() - k,
    {
        if let Some(n) = names.get(k) {
            if eq8(n.as_slice(), l) {
                proof {
                    assert(names_view(names@)[k as int] == l@);
                    assert(names_view(names@).contains(l@));
                }
                return true;
            }
        }
        // Never saturates: k < names.len().
        k = k.saturating_add(1);
    }
    proof {
        if names_view(names@).contains(l@) {
            let j = choose|j: int| 0 <= j < names_view(names@).len() && names_view(names@)[j] == l@;
            assert(names@[j]@ == l@);
        }
    }
    false
}

/// [`forbidden_names`].
fn forbidden_names_exec() -> (out: Vec<Vec<u8>>)
    ensures
        names_view(out@) == forbidden_names(),
{
    let out = vec![
        vec![0x61u8, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2D, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74],
        vec![0x61u8, 0x63, 0x63, 0x65, 0x70, 0x74, 0x2D, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67],
        vec![0x61u8, 0x63, 0x63, 0x65, 0x73, 0x73, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x72, 0x6F, 0x6C, 0x2D, 0x72, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x2D, 0x68, 0x65, 0x61, 0x64, 0x65, 0x72, 0x73],
        vec![0x61u8, 0x63, 0x63, 0x65, 0x73, 0x73, 0x2D, 0x63, 0x6F, 0x6E, 0x74, 0x72, 0x6F, 0x6C, 0x2D, 0x72, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x2D, 0x6D, 0x65, 0x74, 0x68, 0x6F, 0x64],
        vec![0x63u8, 0x6F, 0x6E, 0x6E, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E],
        vec![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68],
        vec![0x63u8, 0x6F, 0x6F, 0x6B, 0x69, 0x65],
        vec![0x63u8, 0x6F, 0x6F, 0x6B, 0x69, 0x65, 0x32],
        vec![0x64u8, 0x61, 0x74, 0x65],
        vec![0x64u8, 0x6E, 0x74],
        vec![0x65u8, 0x78, 0x70, 0x65, 0x63, 0x74],
        vec![0x68u8, 0x6F, 0x73, 0x74],
        vec![0x6Bu8, 0x65, 0x65, 0x70, 0x2D, 0x61, 0x6C, 0x69, 0x76, 0x65],
        vec![0x6Fu8, 0x72, 0x69, 0x67, 0x69, 0x6E],
        vec![0x72u8, 0x65, 0x66, 0x65, 0x72, 0x65, 0x72],
        vec![0x73u8, 0x65, 0x74, 0x2D, 0x63, 0x6F, 0x6F, 0x6B, 0x69, 0x65],
        vec![0x74u8, 0x65],
        vec![0x74u8, 0x72, 0x61, 0x69, 0x6C, 0x65, 0x72],
        vec![0x74u8, 0x72, 0x61, 0x6E, 0x73, 0x66, 0x65, 0x72, 0x2D, 0x65, 0x6E, 0x63, 0x6F, 0x64, 0x69, 0x6E, 0x67],
        vec![0x75u8, 0x70, 0x67, 0x72, 0x61, 0x64, 0x65],
        vec![0x76u8, 0x69, 0x61],
    ];
    assert(names_view(out@) =~~= forbidden_names());
    out
}

/// [`method_override_names`].
fn method_override_names_exec() -> (out: Vec<Vec<u8>>)
    ensures
        names_view(out@) == method_override_names(),
{
    let out = vec![
        vec![0x78u8, 0x2D, 0x68, 0x74, 0x74, 0x70, 0x2D, 0x6D, 0x65, 0x74, 0x68, 0x6F, 0x64],
        vec![0x78u8, 0x2D, 0x68, 0x74, 0x74, 0x70, 0x2D, 0x6D, 0x65, 0x74, 0x68, 0x6F, 0x64, 0x2D, 0x6F, 0x76, 0x65, 0x72, 0x72, 0x69, 0x64, 0x65],
        vec![0x78u8, 0x2D, 0x6D, 0x65, 0x74, 0x68, 0x6F, 0x64, 0x2D, 0x6F, 0x76, 0x65, 0x72, 0x72, 0x69, 0x64, 0x65],
    ];
    assert(names_view(out@) =~~= method_override_names());
    out
}

/// [`managed_names`].
fn managed_names_exec() -> (out: Vec<Vec<u8>>)
    ensures
        names_view(out@) == managed_names(),
{
    let out = vec![
        vec![0x61u8, 0x63, 0x63, 0x65, 0x70, 0x74],
        vec![0x75u8, 0x73, 0x65, 0x72, 0x2D, 0x61, 0x67, 0x65, 0x6E, 0x74],
        vec![0x63u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65],
    ];
    assert(names_view(out@) =~~= managed_names());
    out
}

/// [`author_header_dropped`].
pub fn author_header_dropped_exec(name: &[u8]) -> (r: bool)
    ensures
        r == author_header_dropped(name@),
{
    let l = byte_lowercase_exec(name);
    proof {
        assert(lit_proxy_prefix() =~= seq![0x70u8, 0x72, 0x6F, 0x78, 0x79, 0x2D]);
        assert(lit_sec_prefix() =~= seq![0x73u8, 0x65, 0x63, 0x2D]);
    }
    contains_name(&forbidden_names_exec(), l.as_slice()) || starts_with_exec(l.as_slice(), &[0x70, 0x72, 0x6F, 0x78, 0x79, 0x2D]) || starts_with_exec(
        l.as_slice(),
        &[0x73, 0x65, 0x63, 0x2D],
    ) || contains_name(&method_override_names_exec(), l.as_slice()) || contains_name(&managed_names_exec(), l.as_slice())
}

/// [`author_headers_ok`].
pub fn author_headers_ok_exec(headers: &[FieldLineBuf]) -> (r: bool)
    ensures
        r == author_headers_ok(clazel_http::field::types::lines_view(headers@)),
{
    let ghost hv = clazel_http::field::types::lines_view(headers@);
    let mut k: usize = 0;
    proof {
        assert(hv.skip(0) =~= hv);
    }
    while k < headers.len()
        invariant
            k <= headers.len(),
            hv == clazel_http::field::types::lines_view(headers@),
            author_headers_ok(hv) == author_headers_ok(hv.skip(k as int)),
        decreases headers.len() - k,
    {
        if let Some(h) = headers.get(k) {
            proof {
                assert(hv[k as int] == h@);
                assert(hv.skip(k as int)[0] == h@);
                assert(hv.skip(k as int).drop_first() =~= hv.skip(k as int + 1));
            }
            if author_header_dropped_exec(h.name.as_slice()) {
                return false;
            }
        }
        // Never saturates: k < headers.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(hv.skip(headers.len() as int) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
    }
    true
}

} // verus!
