//! Concrete evaluations that mutation certificates name. Kept apart from
//! `mutation_lemmas` so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there (as `clazel-ipc`'s
//! `examples.rs`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `Content-Type` a commit carries is the response's (evaluated on a
/// response with one `Content-Type` line, its name in another case).
pub proof fn ml_response_content_type()
    ensures
        response_document(
            clazel_http::message::spec::Response {
                fields: seq![clazel_http::field::spec::FieldLine { name: seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65], value: seq![0x74u8, 0x2F, 0x68] }],
                ..crate::mutation_lemmas::ml_response(Seq::<u8>::empty())
            },
        ).content_type == seq![0x74u8, 0x2F, 0x68],
{
    assert(response_document(
        clazel_http::message::spec::Response {
            fields: seq![clazel_http::field::spec::FieldLine { name: seq![0x43u8, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65], value: seq![0x74u8, 0x2F, 0x68] }],
            ..crate::mutation_lemmas::ml_response(Seq::<u8>::empty())
        },
    ).content_type == seq![0x74u8, 0x2F, 0x68]) by (compute_only);
}

} // verus!
