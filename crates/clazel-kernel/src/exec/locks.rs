//! Locks, cookie-averse documents and the cookie request of a renderer, as
//! exec functions proven equal to their spec functions in [`crate::spec`].

use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use super::urls::*;
use clazel_cookie::matching::exec::{CanonicalHostName, canonicalize_a_host_name};
use clazel_cookie::storage::exec::{
    DocumentCallRecord, RequestContextRecord, RequestUrlRecord, is_public_suffix_string_exec,
    narrow_exec,
};
use clazel_origin::exec::{ParsedOrigin, host_equals};
use clazel_url::host::record::{ParsedHost, copy};
use clazel_url::url::record::clone_host;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether two strings of code points are equal.
pub fn u32s_eq(a: &[u32], b: &[u32]) -> (r: bool)
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
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => {
                if *x != *y {
                    return false;
                }
            },
            _ => {
                return false;
            },
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// A copy of an optional host.
fn clone_opt_host(h: &Option<ParsedHost>) -> (out: Option<ParsedHost>)
    ensures
        clazel_origin::exec::opt_host_view(out) == clazel_origin::exec::opt_host_view(*h),
{
    let h = h.as_ref()?;
    Some(clone_host(h))
}

/// A copy of an origin.
pub fn clone_origin(o: &ParsedOrigin) -> (out: ParsedOrigin)
    ensures
        out@ == o@,
{
    match o {
        ParsedOrigin::Opaque(id) => ParsedOrigin::Opaque(*id),
        ParsedOrigin::Tuple { scheme, host, port, domain } => ParsedOrigin::Tuple {
            scheme: copy(scheme.as_slice()),
            host: clone_host(host),
            port: *port,
            domain: clone_opt_host(domain),
        },
    }
}

/// Whether two optional hosts are equal.
fn opt_hosts_eq(a: &Option<ParsedHost>, b: &Option<ParsedHost>) -> (r: bool)
    ensures
        r == (clazel_origin::exec::opt_host_view(*a) == clazel_origin::exec::opt_host_view(*b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => host_equals(x, y),
        _ => false,
    }
}

/// Structural equality of origins: the same variant and the same fields
/// (the domain included), as `==` on the spec's [`clazel_origin::spec::Origin`].
pub fn origin_eq_exec(a: &ParsedOrigin, b: &ParsedOrigin) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (ParsedOrigin::Opaque(x), ParsedOrigin::Opaque(y)) => *x == *y,
        (
            ParsedOrigin::Tuple { scheme: sa, host: ha, port: pa, domain: da },
            ParsedOrigin::Tuple { scheme: sb, host: hb, port: pb, domain: db },
        ) => {
            let r = u32s_eq(sa.as_slice(), sb.as_slice()) && *pa == *pb && host_equals(ha, hb) && opt_hosts_eq(da, db);
            proof {
                assert(clazel_url::url::record::port_view(*pa) == clazel_url::url::record::port_view(*pb) <==> *pa == *pb);
            }
            r
        },
        _ => false,
    }
}

/// [`lock_host`]: the canonicalized host of a tuple lock; `None` for an
/// opaque one.
pub fn lock_host_exec(lock: &ParsedOrigin) -> (r: Option<CanonicalHostName>)
    ensures
        clazel_cookie::matching::exec::option_view(r) == lock_host(lock@),
{
    match lock {
        ParsedOrigin::Tuple { host, .. } => canonicalize_a_host_name(&Some(clone_host(host))),
        ParsedOrigin::Opaque(_) => None,
    }
}

/// [`crate::domain::domain_of_lock`], over the generated Public Suffix List:
/// the partition key of a navigation started by a renderer locked to `lock`.
pub fn domain_of_lock_exec(lock: &ParsedOrigin) -> (r: DomainRecord)
    ensures
        r@ == crate::domain::domain_of_lock(clazel_psl::table::psl_rules(), lock@),
{
    match lock {
        ParsedOrigin::Opaque(id) => DomainRecord::Opaque(*id),
        ParsedOrigin::Tuple { .. } => match lock_host_exec(lock) {
            Some(h) => DomainRecord::Root(clazel_cookie::storage::exec::cookie_root_exec(&h)),
            None => DomainRecord::Root(CanonicalHostName { name: Vec::new(), is_ip_address: false }),
        },
    }
}

/// [`valid_tuple_origin`].
pub fn valid_tuple_origin_exec(o: &ParsedOrigin) -> (r: bool)
    ensures
        r == valid_tuple_origin(o@),
{
    match o {
        ParsedOrigin::Opaque(_) => false,
        ParsedOrigin::Tuple { host, domain, .. } => {
            if domain.is_some() {
                return false;
            }
            match canonicalize_a_host_name(&Some(clone_host(host))) {
                Some(h) => !h.name.is_empty(),
                None => false,
            }
        },
    }
}

/// [`lock_of_origin`].
pub fn lock_of_origin_exec(o: ParsedOrigin, id: u64) -> (r: Option<ParsedOrigin>)
    ensures
        origin_opt_view(r) == lock_of_origin(o@, id as nat),
{
    match o {
        ParsedOrigin::Opaque(_) => Some(ParsedOrigin::Opaque(id)),
        ParsedOrigin::Tuple { .. } => {
            if valid_tuple_origin_exec(&o) { Some(o) } else { None }
        },
    }
}

/// [`lock_of_url`].
pub fn lock_of_url_exec<U: UrlFnsExec>(urls: &U, url: &[u32], id: u64) -> (r: Option<ParsedOrigin>)
    ensures
        origin_opt_view(r) == lock_of_url(urls.urls(), url@, id as nat),
{
    match urls.origin_of(url) {
        Some(o) => lock_of_origin_exec(o, id),
        None => None,
    }
}

/// The scheme of a tuple lock ([`lock_scheme`]), copied.
pub fn lock_scheme_exec(lock: &ParsedOrigin) -> (r: Vec<u32>)
    ensures
        r@ == lock_scheme(lock@),
{
    match lock {
        ParsedOrigin::Tuple { scheme, .. } => copy(scheme.as_slice()),
        ParsedOrigin::Opaque(_) => Vec::new(),
    }
}

/// Whether the code points are `http`.
fn is_http(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == clazel_url::url::spec::http_str()),
{
    let http = vec![0x68u32, 0x74, 0x74, 0x70];
    assert(http@ =~= clazel_url::url::spec::http_str());
    u32s_eq(s, http.as_slice())
}

/// Whether the code points are `https`.
fn is_https(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == clazel_url::url::spec::https_str()),
{
    let https = vec![0x68u32, 0x74, 0x74, 0x70, 0x73];
    assert(https@ =~= clazel_url::url::spec::https_str());
    u32s_eq(s, https.as_slice())
}

/// [`lock_on_public_suffix`], over the generated Public Suffix List.
pub fn lock_on_public_suffix_exec(lock: &ParsedOrigin) -> (r: bool)
    ensures
        r == lock_on_public_suffix(clazel_psl::table::psl_rules(), lock@),
{
    match lock_host_exec(lock) {
        Some(h) => !h.is_ip_address && is_public_suffix_string_exec(h.name.as_slice()),
        None => false,
    }
}

/// [`cookie_averse`], over the generated Public Suffix List.
pub fn cookie_averse_exec(lock: &ParsedOrigin) -> (r: bool)
    ensures
        r == cookie_averse(clazel_psl::table::psl_rules(), lock@),
{
    match lock {
        ParsedOrigin::Opaque(_) => true,
        ParsedOrigin::Tuple { scheme, .. } => {
            if !(is_http(scheme.as_slice()) || is_https(scheme.as_slice())) {
                return true;
            }
            lock_on_public_suffix_exec(lock)
        },
    }
}

/// [`request_url_of`] for a renderer.
pub fn request_url_exec<U: UrlFnsExec>(urls: &U, r: &RendererRecord) -> (out: RequestUrlRecord)
    ensures
        out@ == request_url_of(urls.urls(), r@),
{
    let scheme = lock_scheme_exec(&r.lock);
    RequestUrlRecord { scheme: narrow_exec(scheme.as_slice()), host: lock_host_exec(&r.lock), path: urls.path_of(r.url.as_slice()) }
}

/// [`document_context`].
pub fn document_context_exec(lock: &ParsedOrigin) -> (out: RequestContextRecord)
    ensures
        out@ == document_context(lock@),
{
    RequestContextRecord::NonHttp(DocumentCallRecord { site_for_cookies: clone_origin(lock), top_level_origin: clone_origin(lock) })
}

} // verus!
