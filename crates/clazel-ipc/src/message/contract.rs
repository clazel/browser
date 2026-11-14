//! Contracts the executable message codec must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode_message(&[u8]) -> Option<Message>`.
pub open spec fn decode_message_ensures(input: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_message(input)
}

/// Contract for `decode_renderer_message(&[u8]) -> Option<Message>`: what
/// the kernel runs on the bytes of a frame from a renderer.
pub open spec fn decode_renderer_message_ensures(input: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_renderer_message(input)
}

/// Contract for `decode_gpu_message(&[u8]) -> Option<Message>`: what the
/// kernel runs on the bytes of a frame from a GPU process (item 5.18).
pub open spec fn decode_gpu_message_ensures(input: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_gpu_message(input)
}

/// Precondition of `encode_message(&Message) -> Vec<u8>`.
pub open spec fn encode_message_requires(m: Message) -> bool {
    message_ok(m)
}

/// Contract for `encode_message(&Message) -> Vec<u8>`.
pub open spec fn encode_message_ensures(m: Message, output: Seq<u8>) -> bool {
    output == encode_message(m)
}

/// Contract for `decode_framed(&[u8]) -> Option<Message>`: a whole frame
/// from the transport to a message.
pub open spec fn decode_framed_ensures(frame: Seq<u8>, output: Option<Message>) -> bool {
    output == decode_framed(frame)
}

/// Contract for `encode_framed(&Msg) -> Option<Vec<u8>>`: the message's
/// frame, or `None` if its bytes are over `MAX_FRAME`.
pub open spec fn encode_framed_ensures(m: Message, output: Option<Seq<u8>>) -> bool {
    output == if crate::frame::spec::payload_ok(encode_message(m)) {
        Some(crate::frame::spec::encode_frame(encode_message(m)))
    } else {
        None
    }
}

} // verus!
