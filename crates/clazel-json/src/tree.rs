//! The executable value tree the parser returns, and its meaning as a
//! [`JsonValue`](super::spec::JsonValue). The parser's contract is stated
//! on this meaning (`view`), so this file is part of what a reader checks:
//! each variant must mean what its counterpart in `spec.rs` means.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A JSON value, the executable counterpart of
/// [`JsonValue`](super::spec::JsonValue).
pub enum Json {
    /// `null`.
    Null,
    /// `true` or `false`.
    Bool(bool),
    /// A number's source text, ASCII code points.
    Number(Vec<u32>),
    /// A string's UTF-16 code units.
    String(Vec<u16>),
    /// An array's elements.
    Array(Vec<Json>),
    /// An object's members in source order, duplicate keys kept.
    Object(Vec<Member>),
}

/// The executable counterpart of [`JsonMember`](super::spec::JsonMember).
pub struct Member {
    /// The member's name.
    pub key: Vec<u16>,
    /// The member's value.
    pub value: Json,
}

impl View for Json {
    type V = JsonValue;

    open spec fn view(&self) -> JsonValue
        decreases self,
    {
        match self {
            Json::Null => JsonValue::Null,
            Json::Bool(b) => JsonValue::Bool(*b),
            Json::Number(t) => JsonValue::Number(t@),
            Json::String(u) => JsonValue::String(u@),
            Json::Array(items) => JsonValue::Array(
                Seq::new(items@.len(), |i: int| if 0 <= i < items@.len() { items@[i].view() } else { JsonValue::Null }),
            ),
            Json::Object(members) => JsonValue::Object(
                Seq::new(
                    members@.len(),
                    |i: int|
                        if 0 <= i < members@.len() {
                            JsonMember { key: members@[i].key@, value: members@[i].value.view() }
                        } else {
                            JsonMember { key: Seq::empty(), value: JsonValue::Null }
                        },
                ),
            ),
        }
    }
}

} // verus!
