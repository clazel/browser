//! Contracts the executable request functions must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `request_bytes(&ParsedUrl) -> Option<Vec<u8>>`.
pub open spec fn request_bytes_ensures(url: clazel_url::url::spec::Url, output: Option<Seq<u8>>) -> bool {
    output == request_bytes(url)
}

/// Contract for `request_bytes_cookie(&ParsedUrl, &[u8]) -> Option<Vec<u8>>`.
pub open spec fn request_bytes_cookie_ensures(url: clazel_url::url::spec::Url, cookie: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == request_bytes_cookie(url, cookie)
}

/// Contract for `connect_to(&ParsedUrl) -> Option<(Vec<u8>, u16)>`.
pub open spec fn connect_to_ensures(url: clazel_url::url::spec::Url, output: Option<(Seq<u8>, nat)>) -> bool {
    output == connect_to(url)
}

/// Contract for `uses_tls(&ParsedUrl) -> bool`.
pub open spec fn uses_tls_ensures(url: clazel_url::url::spec::Url, output: bool) -> bool {
    output == uses_tls(url)
}

/// Contract for `is_interim(u16) -> bool`.
pub open spec fn is_interim_ensures(status: nat, output: bool) -> bool {
    output == is_interim(status)
}

/// Contract for `request_bytes_req_cookie(&ParsedUrl, &ReqBuf, &[u8]) ->
/// Option<Vec<u8>>` (item 6.16): the head, then the body.
pub open spec fn request_bytes_req_cookie_ensures(url: clazel_url::url::spec::Url, req: Req, cookie: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == request_bytes_req_cookie(url, req, cookie)
}

/// Contract for `rewrite_for_redirect(u16, ReqBuf) -> ReqBuf` (HTTP-redirect
/// fetch step 12).
pub open spec fn rewrite_for_redirect_ensures(status: nat, req: Req, output: Req) -> bool {
    output == rewrite_for_redirect(status, req)
}

/// Contract for `method_is_safe(&ReqBuf) -> bool`.
pub open spec fn method_is_safe_ensures(req: Req, output: bool) -> bool {
    output == method_is_safe(req)
}

/// **`theorem_redirect_method`'s statement at the level of one redirect**
/// (HTTP-redirect fetch step 12; RFC 9110 §15.4): for a request that is
/// valid ([`req_ok`]), the request after a redirect with `status` is
/// - on 301 and 302: a `GET` without a body if it was a `POST`, else
///   unchanged;
/// - on 303: a `GET` without a body, unless it was a `GET` or `HEAD` already;
/// - on 307 and 308: unchanged, method and body;
/// - on any other status: unchanged;
/// and in every case the result is again valid, its body is the same body
/// or none (never another one), and its initiator is unchanged.
pub open spec fn redirect_method_rule(status: nat, req: Req) -> bool {
    let out = rewrite_for_redirect(status, req);
    &&& (status == 307 || status == 308) ==> out == req
    &&& (status == 301 || status == 302) ==> (if req.method == lit_post() {
        out.method == lit_get() && out.body is None
    } else {
        out == req
    })
    &&& status == 303 ==> (if req.method == lit_get() || req.method == lit_head() {
        out == req
    } else {
        out.method == lit_get() && out.body is None
    })
    &&& !is_redirect_status_n(status) ==> out == req
    &&& req_ok(req) ==> req_ok(out)
    &&& out.body is None || out.body == req.body
    &&& out.initiator == req.initiator
    &&& out.origin_tainted == req.origin_tainted
}

/// Fetch §2.2.3: 301, 302, 303, 307, 308 (as the transducer's spec).
pub open spec fn is_redirect_status_n(status: nat) -> bool {
    status == 301 || status == 302 || status == 303 || status == 307 || status == 308
}

/// **`theorem_post_cookies`'s request-level fact**: the "safe method" bit
/// the cookie functions see is false for `POST`, so a cross-site request
/// with a body is never given `SameSite=Lax` cookies by RFC 6265bis §5.8.3.
pub open spec fn post_is_unsafe(req: Req) -> bool {
    req.method == lit_post() ==> !method_is_safe(req)
}

} // verus!
