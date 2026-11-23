//! The executable encodings: URL's `application/x-www-form-urlencoded`
//! serializer, the conversion to name-value pairs, `text/plain` and
//! `multipart/form-data`. Each function is proven equal to the spec
//! function it names (see [`crate::submit::contract`]).

use super::strings::*;
use crate::exec::entry::{ExecEntry, append};
#[cfg(verus_only)]
use crate::exec::entry::{entries_view, lemma_entries_push};
use crate::exec::strings::decimal_into;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::submit::contract::*;
#[cfg(verus_only)]
use crate::submit::lemmas::*;
#[cfg(verus_only)]
use crate::submit::spec::*;
use clazel_encoding::labels::spec::Encoding;
use clazel_encoding::single_byte::spec::EncoderResult;
#[cfg(verus_only)]
use clazel_encoding::utf8::spec::all_scalar_values;
use clazel_percent::spec::PercentEncodeSet;
#[cfg(verus_only)]
use clazel_percent::spec::encode_output_byte;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`output_encoding`]: Encoding "get an output encoding".
pub fn output_encoding_exec(e: Encoding) -> (r: Encoding)
    ensures
        r == output_encoding(e),
{
    match e {
        Encoding::Replacement | Encoding::Utf16Be | Encoding::Utf16Le => Encoding::Utf8,
        _ => e,
    }
}

/// [`encode_output_byte`]: percent-encode after encoding, step 7.3's body
/// for one byte.
pub fn encode_output_byte_exec(set: PercentEncodeSet, space_as_plus: bool, byte: u8) -> (r: Vec<u32>)
    ensures
        r@ == encode_output_byte(set, space_as_plus, byte),
{
    let mut out: Vec<u32> = Vec::new();
    if space_as_plus && byte == 0x20 {
        out.push(0x2B);
        proof {
            assert(out@ =~= seq![0x2Bu32]);
        }
    } else {
        let isomorph = byte as u32;
        if !set.contains(isomorph) {
            out.push(isomorph);
            proof {
                assert(out@ =~= seq![isomorph]);
            }
        } else {
            return clazel_percent::encode::percent_encode(byte);
        }
    }
    out
}

/// [`percent_encode_after_encoding_sb`]: the single-byte branch of "percent-encode
/// after encoding".
pub fn percent_encode_after_encoding_sb_exec(e: Encoding, input: &[u32], set: PercentEncodeSet) -> (r: Vec<u32>)
    ensures
        r@ == percent_encode_after_encoding_sb(e, input@, set),
{
    let space_as_plus = matches!(set, PercentEncodeSet::ApplicationXWwwFormUrlencoded);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.skip(0) =~= input@);
    }
    while i < input.len()
        invariant
            i <= input.len(),
            space_as_plus == (set == PercentEncodeSet::ApplicationXWwwFormUrlencoded),
            out@ + percent_encode_after_encoding_sb(e, input@.skip(i as int), set) == percent_encode_after_encoding_sb(
                e,
                input@,
                set,
            ),
        decreases input.len() - i,
    {
        let ghost before = out@;
        if let Some(c) = input.get(i) {
            let c = *c;
            proof {
                assert(input@.skip(i as int).drop_first() =~= input@.skip(i as int + 1));
                assert(input@.skip(i as int)[0] == input@[i as int]);
            }
            match clazel_encoding::single_byte::encode::run_encoder_handler(e, c) {
                EncoderResult::Byte(b) => {
                    let piece = encode_output_byte_exec(set, space_as_plus, b);
                    append(&mut out, piece.as_slice());
                },
                EncoderResult::Error(code) => {
                    out.push(0x25);
                    out.push(0x32);
                    out.push(0x36);
                    out.push(0x25);
                    out.push(0x32);
                    out.push(0x33);
                    decimal_into(code, &mut out);
                    out.push(0x25);
                    out.push(0x33);
                    out.push(0x42);
                    proof {
                        assert(out@ =~= before + (seq![0x25u32, 0x32, 0x36, 0x25, 0x32, 0x33] + decimal(code as nat)
                            + seq![0x25u32, 0x33, 0x42]));
                    }
                },
                EncoderResult::Finished => {},
            }
        }
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(input@.skip(input.len() as int) =~= Seq::<u32>::empty());
    }
    out
}

/// [`percent_encode_after_encoding`]: URL §1.3, with UTF-8 or a single-byte
/// encoding.
pub fn percent_encode_after_encoding_exec(e: Encoding, input: &[u32], set: PercentEncodeSet) -> (r: Vec<u32>)
    requires
        percent_encode_after_encoding_requires(e, input@),
    ensures
        percent_encode_after_encoding_ensures(e, input@, set, r@),
{
    match e {
        Encoding::Utf8 => clazel_percent::encode::utf8_percent_encode(input, set),
        _ => percent_encode_after_encoding_sb_exec(e, input, set),
    }
}

/// [`urlencoded_serialize`]: URL §5.2.
pub fn urlencoded_serialize_exec(tuples: &[ExecEntry], encoding: Encoding) -> (r: Vec<u32>)
    requires
        urlencoded_serialize_requires(entries_view(tuples@), encoding),
    ensures
        urlencoded_serialize_ensures(entries_view(tuples@), encoding, r@),
{
    // 1. "Set encoding to the result of getting an output encoding from
    // encoding."
    let enc = output_encoding_exec(encoding);
    let ghost all = entries_view(tuples@);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(all.skip(0) =~= all);
    }
    while i < tuples.len()
        invariant
            i <= tuples.len(),
            all == entries_view(tuples@),
            encodable(enc),
            entries_scalar(all),
            serialize_loop(all, enc, Seq::empty()) == serialize_loop(all.skip(i as int), enc, out@),
        decreases tuples.len() - i,
    {
        if let Some(t) = tuples.get(i) {
            proof {
                assert(all.skip(i as int).drop_first() =~= all.skip(i as int + 1));
                assert(all.skip(i as int)[0] == all[i as int]);
                assert(all[i as int] == tuples@[i as int]@);
            }
            // 3.2, 3.3
            let name = percent_encode_after_encoding_exec(
                enc,
                t.name.as_slice(),
                PercentEncodeSet::ApplicationXWwwFormUrlencoded,
            );
            let value = percent_encode_after_encoding_exec(
                enc,
                t.value.as_slice(),
                PercentEncodeSet::ApplicationXWwwFormUrlencoded,
            );
            // 3.4 "If output is not the empty string, then append U+0026 (&)."
            let ghost before = out@;
            if !out.is_empty() {
                out.push(0x26);
            }
            // 3.5 "Append name, followed by U+003D (=), followed by value."
            append(&mut out, name.as_slice());
            out.push(0x3D);
            append(&mut out, value.as_slice());
            proof {
                let o2 = if before.len() != 0 {
                    before.push(0x26u32)
                } else {
                    before
                };
                assert(out@ =~= o2 + name@ + seq![0x3Du32] + value@);
            }
        }
        // Never saturates: i < tuples.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(all.skip(tuples.len() as int) =~= Seq::<Entry>::empty());
    }
    out
}

/// [`convert_to_pairs`]: HTML "convert to a list of name-value pairs".
pub fn convert_to_pairs_exec(entry_list: &[ExecEntry]) -> (r: Vec<ExecEntry>)
    ensures
        convert_to_pairs_ensures(entries_view(entry_list@), entries_view(r@)),
{
    let mut out: Vec<ExecEntry> = Vec::new();
    let mut i: usize = 0;
    let ghost all = entries_view(entry_list@);
    proof {
        assert(all.skip(0) =~= all);
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
    }
    while i < entry_list.len()
        invariant
            i <= entry_list.len(),
            all == entries_view(entry_list@),
            entries_view(out@) + convert_to_pairs(all.skip(i as int)) == convert_to_pairs(all),
        decreases entry_list.len() - i,
    {
        if let Some(e) = entry_list.get(i) {
            let ghost before = out@;
            let name = crlf_newlines_exec(e.name.as_slice());
            let value = crlf_newlines_exec(e.value.as_slice());
            proof {
                assert(all.skip(i as int).drop_first() =~= all.skip(i as int + 1));
                assert(all.skip(i as int)[0] == all[i as int]);
                assert(all[i as int] == entry_list@[i as int]@);
            }
            out.push(ExecEntry { name, value });
            proof {
                lemma_entries_push(before, out@[before.len() as int]);
                assert(out@ =~= before.push(out@[before.len() as int]));
                assert(entries_view(before).push(Entry {
                    name: crlf_newlines(entry_list@[i as int].name@),
                    value: crlf_newlines(entry_list@[i as int].value@),
                }) + convert_to_pairs(all.skip(i as int + 1)) =~= entries_view(before) + convert_to_pairs(
                    all.skip(i as int),
                ));
            }
        }
        // Never saturates: i < entry_list.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(all.skip(entry_list.len() as int) =~= Seq::<Entry>::empty());
    }
    out
}

/// [`text_plain_encode`]: HTML "text/plain encoding algorithm".
pub fn text_plain_encode_exec(pairs: &[ExecEntry]) -> (r: Vec<u32>)
    ensures
        text_plain_encode_ensures(entries_view(pairs@), r@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let ghost all = entries_view(pairs@);
    proof {
        assert(all.skip(0) =~= all);
    }
    while i < pairs.len()
        invariant
            i <= pairs.len(),
            all == entries_view(pairs@),
            text_plain_loop(all, Seq::empty()) == text_plain_loop(all.skip(i as int), out@),
        decreases pairs.len() - i,
    {
        if let Some(p) = pairs.get(i) {
            let ghost before = out@;
            proof {
                assert(all.skip(i as int).drop_first() =~= all.skip(i as int + 1));
                assert(all.skip(i as int)[0] == all[i as int]);
                assert(all[i as int] == pairs@[i as int]@);
            }
            append(&mut out, p.name.as_slice());
            out.push(0x3D);
            append(&mut out, p.value.as_slice());
            out.push(0x0D);
            out.push(0x0A);
            proof {
                assert(out@ =~= before + pairs@[i as int].name@ + seq![0x3Du32] + pairs@[i as int].value@ + seq![
                    0x0Du32,
                    0x0Au32,
                ]);
            }
        }
        // Never saturates: i < pairs.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(all.skip(pairs.len() as int) =~= Seq::<Entry>::empty());
    }
    out
}

/// [`encode_with`]: Encoding "encode" with UTF-8 or a single-byte encoding.
pub fn encode_with_exec(e: Encoding, s: &[u32]) -> (r: Vec<u8>)
    requires
        encode_with_requires(e, s@),
    ensures
        encode_with_ensures(e, s@, r@),
{
    match e {
        Encoding::Utf8 => clazel_encoding::utf8::encode::encode(s),
        _ => clazel_encoding::single_byte::encode::encode(e, s),
    }
}

/// One part of the `multipart/form-data` resource, appended to `out`
/// ([`multipart_part`]).
pub fn push_part(out: &mut Vec<u8>, entry: &ExecEntry, encoding: Encoding, boundary: &[u8])
    requires
        encodable(encoding),
        all_scalar_values(entry.name@),
        all_scalar_values(entry.value@),
    ensures
        final(out)@ == old(out)@ + multipart_part(entry@, encoding, boundary@),
{
    let ghost start = out@;
    let name = crlf_newlines_exec(entry.name.as_slice());
    let value = crlf_newlines_exec(entry.value.as_slice());
    proof {
        lemma_crlf_scalar(entry.name@);
        lemma_crlf_scalar(entry.value@);
    }
    let name_bytes = encode_with_exec(encoding, name.as_slice());
    let value_bytes = encode_with_exec(encoding, value.as_slice());
    let escaped = escape_name_exec(name_bytes.as_slice());
    append8(out, b"--");
    append8(out, boundary);
    append8(out, b"\r\nContent-Disposition: form-data; name=\"");
    append8(out, escaped.as_slice());
    append8(out, b"\"\r\n\r\n");
    append8(out, value_bytes.as_slice());
    append8(out, b"\r\n");
    proof {
        assert(out@ =~= start + multipart_part(entry@, encoding, boundary@));
    }
}

/// [`multipart_encode`]: HTML "multipart/form-data encoding algorithm".
pub fn multipart_encode_exec(entries: &[ExecEntry], encoding: Encoding, boundary: &[u8]) -> (r: Vec<u8>)
    requires
        multipart_encode_requires(entries_view(entries@), encoding),
    ensures
        multipart_encode_ensures(entries_view(entries@), encoding, boundary@, r@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost all = entries_view(entries@);
    proof {
        assert(all.skip(0) =~= all);
    }
    while i < entries.len()
        invariant
            i <= entries.len(),
            all == entries_view(entries@),
            encodable(encoding),
            entries_scalar(all),
            out@ + multipart_parts(all.skip(i as int), encoding, boundary@) == multipart_parts(
                all,
                encoding,
                boundary@,
            ),
        decreases entries.len() - i,
    {
        if let Some(e) = entries.get(i) {
            let ghost before = out@;
            proof {
                assert(all.skip(i as int).drop_first() =~= all.skip(i as int + 1));
                assert(all.skip(i as int)[0] == all[i as int]);
                assert(all[i as int] == entries@[i as int]@);
            }
            push_part(&mut out, e, encoding, boundary);
        }
        // Never saturates: i < entries.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(all.skip(entries.len() as int) =~= Seq::<Entry>::empty());
    }
    append8(&mut out, b"--");
    append8(&mut out, boundary);
    append8(&mut out, b"--\r\n");
    proof {
        assert(out@ =~= multipart_encode(all, encoding, boundary@));
    }
    out
}

} // verus!
