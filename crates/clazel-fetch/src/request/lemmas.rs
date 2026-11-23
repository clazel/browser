//! Lemmas about the request spec (item 6.16).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A request in the class before 6.16 ([`is_plain_get`]) has the bytes it
/// always had: [`request_bytes_req_cookie`] of it is
/// [`request_bytes_cookie`], and with no cookies [`request_bytes`].
pub proof fn lemma_plain_get_bytes(url: clazel_url::url::spec::Url, req: Req, cookie: Seq<u8>)
    requires
        is_plain_get(req),
    ensures
        request_bytes_req_cookie(url, req, cookie) == request_bytes_cookie(url, cookie),
        request_bytes_req(url, req) == request_bytes(url),
{
    assert(body_field_lines(req) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
    assert(body_bytes(req) =~= Seq::<u8>::empty());
    assert(origin_field_lines(url, req) == Some(Seq::<clazel_http::field::spec::FieldLine>::empty()));
    assert(cookie_field_lines(Seq::<u8>::empty()) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
    if let Some(r) = request_for(url) {
        assert(r.fields + body_field_lines(req) + Seq::<clazel_http::field::spec::FieldLine>::empty() =~= r.fields);
        assert(r.fields + cookie_field_lines(Seq::<u8>::empty()) =~= r.fields);
        assert(clazel_http::message::spec::serialize_request(r) + body_bytes(req) =~= clazel_http::message::spec::serialize_request(r));
        assert(request_for_req(url, req) == Some(r));
    }
}


/// [`super::contract::redirect_method_rule`] holds for every request and
/// status: HTTP-redirect fetch step 12 and RFC 9110 §15.4.
pub proof fn lemma_redirect_method_rule(status: nat, req: Req)
    ensures
        super::contract::redirect_method_rule(status, req),
{
    let out = rewrite_for_redirect(status, req);
    assert(lit_get() != lit_post()) by {
        assert(lit_get()[0] != lit_post()[0]);
    }
    assert(lit_head() != lit_get()) by {
        assert(lit_head()[0] != lit_get()[0]);
    }
    assert(lit_head() != lit_post()) by {
        assert(lit_head()[1] != lit_post()[1]);
    }
}

/// `POST` is not a safe method (RFC 9110 §9.2.1).
pub proof fn lemma_post_is_unsafe(req: Req)
    ensures
        super::contract::post_is_unsafe(req),
{
    assert(lit_post() != lit_get()) by {
        assert(lit_post()[0] != lit_get()[0]);
    }
    assert(lit_post() != lit_head()) by {
        assert(lit_post()[0] != lit_head()[0]);
    }
    assert(lit_post() != lit_options()) by {
        assert(lit_post()[1] != lit_options()[1]);
    }
    assert(lit_post() != lit_trace()) by {
        assert(lit_post()[0] != lit_trace()[0]);
    }
}


/// A request in the class before 6.16 is not changed by a redirect's
/// rewriting (a `GET` stays a `GET`, whatever the status).
pub proof fn lemma_rewrite_plain_get(status: nat, req: Req)
    requires
        is_plain_get(req),
    ensures
        rewrite_for_redirect(status, req) == req,
{
    assert(lit_get() != lit_post()) by {
        assert(lit_get()[0] != lit_post()[0]);
    }
}

} // verus!
