//! Concrete requests with the page's headers and mode "cors", evaluated on
//! the spec (item 7.16) by Verus (`by (compute_only)`); nothing here is
//! trusted. One lemma per row. In their own module: a mutation certificate
//! is checked with its module's other evaluations.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `http://example.com/p`.
pub open spec fn ex_url() -> clazel_url::url::spec::Url {
    clazel_url::url::spec::Url {
        scheme: seq![0x68u32, 0x74, 0x74, 0x70],
        username: Seq::<u32>::empty(),
        password: Seq::<u32>::empty(),
        host: Some(clazel_url::host::spec::Host::Domain(seq![0x65u32, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F, 0x6D])),
        port: None,
        path: clazel_url::url::spec::UrlPath::List(seq![seq![0x70u32]]),
        query: None,
        fragment: None,
    }
}

/// A `GET` with no body and no client, with these page headers and mode.
pub open spec fn ex_get_with(headers: Seq<clazel_http::field::spec::FieldLine>, cors: bool) -> Req {
    Req { method: lit_get(), body: None, initiator: None, origin_tainted: false, headers, cors }
}

/// The header line `name: 1`.
pub open spec fn ex_line(name: Seq<u8>) -> clazel_http::field::spec::FieldLine {
    clazel_http::field::spec::FieldLine { name, value: seq![0x31u8] }
}

/// A page header Fetch allows (`X-A: 1`) is sent after the client's four
/// fields, as it was given.
pub proof fn lemma_headers_00()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false)) is Some,
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false))->Some_0.fields.len() == 5,
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false))->Some_0.fields[4] == ex_line(seq![0x58u8, 0x2D, 0x41]),
{
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false)) is Some) by (compute_only);
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false))->Some_0.fields.len() == 5) by (compute_only);
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x58u8, 0x2D, 0x41])], false))->Some_0.fields[4] == ex_line(seq![0x58u8, 0x2D, 0x41]))
        by (compute_only);
}

/// A page's `Cookie` (in any case: `cOOKie`) is forbidden (Fetch §2.2.2
/// step 1): the request is not built.
pub proof fn lemma_headers_01()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x63u8, 0x4F, 0x4F, 0x4B, 0x69, 0x65])], false)) is None,
{
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x63u8, 0x4F, 0x4F, 0x4B, 0x69, 0x65])], false)) is None) by (compute_only);
}

/// In mode "cors" a `GET` carries `Origin` (`null`: no client), the last
/// field ("append a request `Origin` header" step 3).
pub proof fn lemma_headers_02()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![], true)) is Some,
        request_for_req(ex_url(), ex_get_with(seq![], true))->Some_0.fields.len() == 5,
        request_for_req(ex_url(), ex_get_with(seq![], true))->Some_0.fields[4] == (clazel_http::field::spec::FieldLine { name: lit_origin(), value: lit_null() }),
{
    assert(request_for_req(ex_url(), ex_get_with(seq![], true)) is Some) by (compute_only);
    assert(request_for_req(ex_url(), ex_get_with(seq![], true))->Some_0.fields.len() == 5) by (compute_only);
    assert(request_for_req(ex_url(), ex_get_with(seq![], true))->Some_0.fields[4] == (clazel_http::field::spec::FieldLine { name: lit_origin(), value: lit_null() }))
        by (compute_only);
}

/// A page header starting with `Sec-` is forbidden (§2.2.2 step 2).
pub proof fn lemma_headers_03()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x53u8, 0x65, 0x63, 0x2D, 0x58])], false)) is None,
{
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x53u8, 0x65, 0x63, 0x2D, 0x58])], false)) is None) by (compute_only);
}

/// A page's `Accept` is the client's own field: the request is not built.
pub proof fn lemma_headers_04()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x41u8, 0x63, 0x63, 0x65, 0x70, 0x74])], false)) is None,
{
    assert(request_for_req(ex_url(), ex_get_with(seq![ex_line(seq![0x41u8, 0x63, 0x63, 0x65, 0x70, 0x74])], false)) is None) by (compute_only);
}

/// Without mode "cors", a `GET` carries no `Origin` (step 4): four fields.
pub proof fn lemma_headers_05()
    ensures
        request_for_req(ex_url(), ex_get_with(seq![], false)) is Some,
        request_for_req(ex_url(), ex_get_with(seq![], false))->Some_0.fields.len() == 4,
{
    assert(request_for_req(ex_url(), ex_get_with(seq![], false)) is Some) by (compute_only);
    assert(request_for_req(ex_url(), ex_get_with(seq![], false))->Some_0.fields.len() == 4) by (compute_only);
}

} // verus!
