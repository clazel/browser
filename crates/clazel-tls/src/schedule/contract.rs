//! Contracts for the TLS key-schedule execution, RFC 8446 §7.1–§7.3.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// §7.1 HkdfLabel vector bounds (the six-byte prefix counts).
pub open spec fn label_requires(label: Seq<u8>, context: Seq<u8>) -> bool {
    1 <= label.len() <= 249 && context.len() <= 255
}

/// §7.1 HkdfLabel serialization, including the output length.
pub open spec fn label_ensures(label: Seq<u8>, context: Seq<u8>, length: u16,
    out: Seq<u8>) -> bool
{
    out == super::spec::hkdf_label(label, context, length)
}

/// §7.1 HKDF-Expand's SHA-256 bound (RFC 5869 §2.3).
pub open spec fn expand_requires(secret: Seq<u8>, context: Seq<u8>, length: u16) -> bool {
    secret.len() == super::spec::HASH_LEN && context.len() <= 255 && length <= 8160
}
} // verus!
