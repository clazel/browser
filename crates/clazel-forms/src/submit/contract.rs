//! Contracts the executable submission functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these predicates
//! (and its `requires`, where it has one), so reviewing these and
//! [`super::spec`] is enough to know what the implementation guarantees.
//!
//! The functions that read the DOM take a `clazel_dom` arena that is
//! well-formed ([`clazel_dom::spec::wf`]) and element arguments that are
//! elements (an attribute is read from an element). Strings are code points
//! as `u32`, byte strings `u8`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[cfg(verus_only)]
use clazel_encoding::labels::spec::Encoding;
#[cfg(verus_only)]
use clazel_encoding::utf8::spec::all_scalar_values;
#[cfg(verus_only)]
use clazel_percent::spec::PercentEncodeSet;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every name and value of `es` is a scalar value string (the serializer's
/// step 3.1 assertion, which [`scalar_entries`] discharges).
pub open spec fn entries_scalar(es: Seq<Entry>) -> bool {
    forall|k: int| 0 <= k < es.len() ==> all_scalar_values(#[trigger] es[k].name) && all_scalar_values(es[k].value)
}

/// Contract for `to_scalar_exec(&[u32])`.
pub open spec fn to_scalar_ensures(s: Seq<u32>, out: Seq<u32>) -> bool {
    out == to_scalar(s)
}

/// Contract for `scalar_entries_exec(&[ExecEntry])`.
pub open spec fn scalar_entries_ensures(es: Seq<Entry>, out: Seq<Entry>) -> bool {
    out == scalar_entries(es)
}

/// Contract for `crlf_newlines_exec(&[u32])`.
pub open spec fn crlf_newlines_ensures(s: Seq<u32>, out: Seq<u32>) -> bool {
    out == crlf_newlines(s)
}

/// Contract for `split_ws_exec(&[u32])`: the tokens.
pub open spec fn split_ws_ensures(s: Seq<u32>, out: Seq<Seq<u32>>) -> bool {
    out == split_ws(s)
}

/// Contract for `pick_encoding_exec(Encoding, Option<&[u32]>)`.
pub open spec fn pick_encoding_ensures(document_encoding: Encoding, accept_charset: Option<Seq<u32>>, out: Encoding) -> bool {
    out == pick_encoding(document_encoding, accept_charset)
}

/// Precondition of `percent_encode_after_encoding_exec`: an encoder exists
/// and the input is a scalar value string.
pub open spec fn percent_encode_after_encoding_requires(e: Encoding, input: Seq<u32>) -> bool {
    encodable(e) && all_scalar_values(input)
}

/// Contract for `percent_encode_after_encoding_exec(Encoding, &[u32],
/// PercentEncodeSet)`.
pub open spec fn percent_encode_after_encoding_ensures(
    e: Encoding,
    input: Seq<u32>,
    set: PercentEncodeSet,
    out: Seq<u32>,
) -> bool {
    out == percent_encode_after_encoding(e, input, set)
}

/// Precondition of `urlencoded_serialize_exec(&[ExecEntry], Encoding)`: an
/// encoder exists for the output encoding, and the tuples are scalar value
/// strings.
pub open spec fn urlencoded_serialize_requires(tuples: Seq<Entry>, encoding: Encoding) -> bool {
    encodable(output_encoding(encoding)) && entries_scalar(tuples)
}

/// Contract for `urlencoded_serialize_exec(&[ExecEntry], Encoding)`.
pub open spec fn urlencoded_serialize_ensures(tuples: Seq<Entry>, encoding: Encoding, out: Seq<u32>) -> bool {
    out == urlencoded_serialize(tuples, encoding)
}

/// Contract for `convert_to_pairs_exec(&[ExecEntry])`.
pub open spec fn convert_to_pairs_ensures(entry_list: Seq<Entry>, out: Seq<Entry>) -> bool {
    out == convert_to_pairs(entry_list)
}

/// Contract for `text_plain_encode_exec(&[ExecEntry])`.
pub open spec fn text_plain_encode_ensures(pairs: Seq<Entry>, out: Seq<u32>) -> bool {
    out == text_plain_encode(pairs)
}

/// Precondition of `encode_with_exec(Encoding, &[u32])`.
pub open spec fn encode_with_requires(e: Encoding, s: Seq<u32>) -> bool {
    encodable(e) && all_scalar_values(s)
}

/// Contract for `encode_with_exec(Encoding, &[u32])`.
pub open spec fn encode_with_ensures(e: Encoding, s: Seq<u32>, out: Seq<u8>) -> bool {
    out == encode_with(e, s)
}

/// Contract for `escape_name_exec(&[u8])`.
pub open spec fn escape_name_ensures(b: Seq<u8>, out: Seq<u8>) -> bool {
    out == escape_name(b)
}

/// Contract for `wf_boundary_exec(&[u8])`.
pub open spec fn wf_boundary_ensures(b: Seq<u8>, out: bool) -> bool {
    out == wf_boundary(b)
}

/// Precondition of `multipart_encode_exec(&[ExecEntry], Encoding, &[u8])`.
pub open spec fn multipart_encode_requires(entries: Seq<Entry>, encoding: Encoding) -> bool {
    encodable(encoding) && entries_scalar(entries)
}

/// Contract for `multipart_encode_exec(&[ExecEntry], Encoding, &[u8])`.
pub open spec fn multipart_encode_ensures(entries: Seq<Entry>, encoding: Encoding, boundary: Seq<u8>, out: Seq<u8>) -> bool {
    out == multipart_encode(entries, encoding, boundary)
}

/// Contract for `method_of_value_exec(&[u32])`.
pub open spec fn method_of_value_ensures(v: Seq<u32>, out: MethodState) -> bool {
    out == method_of_value(v)
}

/// Contract for `enctype_of_value_exec(&[u32])`.
pub open spec fn enctype_of_value_ensures(v: Seq<u32>, out: EnctypeState) -> bool {
    out == enctype_of_value(v)
}

/// Precondition of the functions that read a form's and a submitter's
/// attributes: a well-formed arena with `form` and `submitter` elements.
pub open spec fn attrs_requires(doc: Document, form: NodeId, submitter: NodeId) -> bool {
    &&& dom::wf(doc)
    &&& is_element(doc, form)
    &&& is_element(doc, submitter)
}

/// Contract for `is_submit_button_exec(&Arena, usize)`.
pub open spec fn is_submit_button_ensures(doc: Document, n: NodeId, out: bool) -> bool {
    out == is_submit_button(doc, n)
}

/// Contract for `submitter_action_exec(&Arena, usize, usize)`.
pub open spec fn submitter_action_ensures(doc: Document, form: NodeId, submitter: NodeId, out: Seq<u32>) -> bool {
    out == submitter_action(doc, form, submitter)
}

/// Contract for `submitter_method_exec(&Arena, usize, usize)`.
pub open spec fn submitter_method_ensures(doc: Document, form: NodeId, submitter: NodeId, out: MethodState) -> bool {
    out == submitter_method(doc, form, submitter)
}

/// Contract for `submitter_enctype_exec(&Arena, usize, usize)`.
pub open spec fn submitter_enctype_ensures(doc: Document, form: NodeId, submitter: NodeId, out: EnctypeState) -> bool {
    out == submitter_enctype(doc, form, submitter)
}

/// Precondition of `first_base_target_exec(&Arena, &[usize])`: a
/// well-formed arena whose listed nodes are nodes of it.
pub open spec fn first_base_target_requires(doc: Document, order: Seq<NodeId>) -> bool {
    dom::wf(doc) && forall|k: int| 0 <= k < order.len() ==> dom::valid(doc, #[trigger] order[k])
}

/// Contract for `first_base_target_exec(&Arena, &[usize])`.
pub open spec fn first_base_target_ensures(doc: Document, order: Seq<NodeId>, out: Option<Seq<u32>>) -> bool {
    out == first_base_target(doc, order)
}

/// Contract for `get_an_elements_target_exec(...)`.
pub open spec fn get_an_elements_target_ensures(
    doc: Document,
    form: NodeId,
    target: Option<Seq<u32>>,
    base_target: Option<Seq<u32>>,
    out: Option<Seq<u32>>,
) -> bool {
    out == get_an_elements_target(doc, form, target, base_target)
}

/// Contract for `choose_navigable_exec(Option<&[u32]>)`.
pub open spec fn choose_navigable_ensures(target: Option<Seq<u32>>, out: Target) -> bool {
    out == choose_navigable(target)
}

/// Precondition of `submit_exec(...)`: a well-formed arena, a `form` and
/// a `submitter` that are elements, and the control state table.
pub open spec fn submit_requires(doc: Document, form: NodeId, submitter: NodeId) -> bool {
    &&& dom::wf(doc)
    &&& is_element(doc, form)
    &&& is_element(doc, submitter)
}

/// Contract for `submit_exec(...)`: the form submission algorithm.
pub open spec fn submit_ensures(
    doc: Document,
    st: FormState,
    form: NodeId,
    submitter: NodeId,
    document_encoding: Encoding,
    document_url: Seq<u32>,
    base_url: Url,
    boundary: Seq<u8>,
    out: Outcome,
) -> bool {
    out == submit(doc, st, form, submitter, document_encoding, document_url, base_url, boundary)
}

} // verus!
