//! The executable request serializer (RFC 9112 §3, §5), proven to meet
//! [`super::contract::serialize_request_ensures`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::types::RequestBuf;
use crate::field::string::{append, is_field_name, is_field_value, is_token};
use crate::field::types::FieldLineBuf;

verus! {

/// `all_vchar`.
fn all_vchar_exec(s: &[u8]) -> (r: bool)
    ensures
        r == all_vchar(s@),
{
    let mut i: usize = 0;
    assert(s@.skip(0) =~= s@);
    while i < s.len()
        invariant
            i <= s.len(),
            all_vchar(s@) == all_vchar(s@.skip(i as int)),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => return false,
        };
        assert(s@.skip(i as int)[0] == c);
        assert(s@.skip(i as int).drop_first() =~= s@.skip(i + 1));
        if !(0x21..=0x7E).contains(&c) {
            return false;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    true
}

/// `all_valid_fields`.
fn all_valid_fields_exec(fields: &[FieldLineBuf]) -> (r: bool)
    ensures
        r == all_valid_fields(crate::field::types::lines_view(fields@)),
{
    let ghost lines = crate::field::types::lines_view(fields@);
    let mut i: usize = 0;
    assert(lines.skip(0) =~= lines);
    while i < fields.len()
        invariant
            i <= fields.len(),
            lines == crate::field::types::lines_view(fields@),
            all_valid_fields(lines) == all_valid_fields(lines.skip(i as int)),
        decreases fields.len() - i,
    {
        let f = match fields.get(i) {
            Some(f) => f,
            None => return false,
        };
        assert(lines.skip(i as int)[0] == f@);
        assert(lines.skip(i as int).drop_first() =~= lines.skip(i + 1));
        if !(is_field_name(f.name.as_slice()) && is_field_value(f.value.as_slice())) {
            return false;
        }
        // Never saturates: i < fields.len().
        i = i.saturating_add(1);
    }
    true
}

/// `serialize_request` (§2.1, §3, §5): the bytes of `r`, or `None` if it
/// is not a valid request.
pub fn serialize_request(r: &RequestBuf) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::serialize_request_ensures(r@, match out {
            Some(v) => Some(v@),
            None => None,
        }),
{
    let valid = is_token(r.method.as_slice()) && !r.target.is_empty() && all_vchar_exec(r.target.as_slice())
        && all_valid_fields_exec(r.fields.as_slice());
    if !valid {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    append(&mut out, r.method.as_slice());
    out.push(0x20);
    append(&mut out, r.target.as_slice());
    out.push(0x20);
    append(&mut out, &[0x48, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x0D, 0x0A]);
    let ghost line = out@;
    assert(line =~= r.method@ + seq![0x20u8] + r.target@ + seq![0x20u8] + lit_http_1_1() + lit_crlf());
    let ghost lines = crate::field::types::lines_view(r.fields@);
    assert(lines.skip(0) =~= lines);
    let mut i: usize = 0;
    while i < r.fields.len()
        invariant
            i <= r.fields.len(),
            lines == crate::field::types::lines_view(r.fields@),
            line + serialize_fields(lines) == out@ + serialize_fields(lines.skip(i as int)),
        decreases r.fields.len() - i,
    {
        if let Some(f) = r.fields.get(i) {
            assert(lines.skip(i as int)[0] == f@);
            assert(lines.skip(i as int).drop_first() =~= lines.skip(i + 1));
            let ghost before = out@;
            append(&mut out, f.name.as_slice());
            out.push(0x3A);
            out.push(0x20);
            append(&mut out, f.value.as_slice());
            out.push(0x0D);
            out.push(0x0A);
            assert(out@ =~= before + (f.name@ + seq![0x3Au8, 0x20u8] + f.value@ + lit_crlf()));
            assert(before + serialize_fields(lines.skip(i as int))
                =~= out@ + serialize_fields(lines.skip(i + 1)));
        }
        // Never saturates: i < r.fields.len().
        i = i.saturating_add(1);
    }
    assert(lines.skip(r.fields.len() as int) =~= Seq::<crate::field::spec::FieldLine>::empty());
    let ghost before = out@;
    out.push(0x0D);
    out.push(0x0A);
    assert(out@ =~= before + lit_crlf());
    assert(out@ =~= super::spec::serialize_request(r@));
    Some(out)
}

} // verus!
