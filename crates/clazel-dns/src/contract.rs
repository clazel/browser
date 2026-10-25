//! Contracts the executable functions must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates (and its
//! `requires`, where it has one), so reviewing these and [`super::spec`] is
//! enough to know what the implementation guarantees.
//!
//! The decoded message of the executable decoder is `types::Msg`; its view
//! is the spec's [`Message`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode_message(&[u8]) -> Option<Msg>`: `None` exactly when
/// the bytes are not one message, and the decoded message otherwise.
pub open spec fn decode_message_ensures(input: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_message(input)
}

/// Contract for `decode_udp(&[u8]) -> Option<Msg>`: as above, for a
/// datagram.
pub open spec fn decode_udp_ensures(input: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_udp(input)
}

/// Contract on what `decode_message` allocates: the decoded sections never
/// hold more records in all than the input has octets, so a header that
/// declares 65535 records of each kind cannot make the decoder reserve
/// memory for records that are not there (it pushes only records it has
/// read: `lemmas::lemma_decode_alloc_bound`).
pub open spec fn decode_alloc_ensures(input_len: nat, output_count: Option<nat>) -> bool {
    match output_count {
        Some(n) => n <= input_len,
        None => true,
    }
}

/// Contract for `dotted_to_wire(&[u8]) -> Option<Vec<u8>>`.
pub open spec fn dotted_to_wire_ensures(name: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == dotted_to_wire(name)
}

/// Contract for `wire_to_dotted(&[u8]) -> Option<Vec<u8>>`: the dotted
/// spelling of an uncompressed wire name, or `None` if it has none.
pub open spec fn wire_to_dotted_ensures(name: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == wire_to_dotted(name)
}

/// Contract for `encode_query(u16, &[u8], u16) -> Option<Vec<u8>>`: the
/// standard query for `qtype` at the dotted name, or `None` if the name is
/// not valid.
pub open spec fn encode_query_ensures(id: u16, name: Seq<u8>, qtype: u16, output: Option<Seq<u8>>) -> bool {
    output == encode_query(Query { id, name, qtype })
}

/// Contract for `answer_addresses(u16, &[u8], u16, &Msg) -> Option<Resolved>`.
pub open spec fn answer_addresses_ensures(id: u16, name: Seq<u8>, qtype: u16, msg: Message, output: Option<Resolution>) -> bool {
    output == answer_addresses(Query { id, name, qtype }, msg)
}

/// Contract for `tcp_frame(&[u8]) -> Option<Vec<u8>>`.
pub open spec fn tcp_frame_ensures(msg: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == tcp_frame(msg)
}

/// Contract for `tcp_message_len(&[u8]) -> Option<usize>`.
pub open spec fn tcp_message_len_ensures(input: Seq<u8>, output: Option<nat>) -> bool {
    output == tcp_message_len(input)
}

} // verus!
