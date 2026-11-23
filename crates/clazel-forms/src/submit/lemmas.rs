//! Facts proven about [`super::spec`]. They are evidence that the
//! transcription is right and the bridge the implementation uses (the
//! serializer's output is ASCII, so it is a scalar value string that UTF-8
//! encoding leaves unchanged; scalar value strings stay so through the
//! newline replacement), not part of what the implementation must meet.

#[cfg(verus_only)]
use super::contract::entries_scalar;
#[cfg(verus_only)]
use super::spec::*;
#[cfg(verus_only)]
use crate::spec::{ascii, decimal, is_ascii_whitespace};
#[cfg(verus_only)]
use clazel_encoding::single_byte::spec::EncoderResult;
#[cfg(verus_only)]
use clazel_encoding::utf8::spec::{all_scalar_values, is_scalar_value};
#[cfg(verus_only)]
use clazel_percent::lemmas::{all_ascii, lemma_sets_include_non_ascii};
#[cfg(verus_only)]
use clazel_percent::spec::{
    PercentEncodeSet, ascii_upper_hex_digit, contains, encode_output_bytes, is_code_point,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A scalar value followed by a scalar value string is one.
pub proof fn lemma_scalar_cons1(a: u32, rest: Seq<u32>)
    requires
        is_scalar_value(a),
        all_scalar_values(rest),
    ensures
        all_scalar_values(seq![a] + rest),
{
    let c = seq![a] + rest;
    assert forall|k: int| 0 <= k < c.len() implies is_scalar_value(#[trigger] c[k]) by {
        if k > 0 {
            assert(c[k] == rest[k - 1]);
        }
    }
}

/// Two scalar values followed by a scalar value string.
pub proof fn lemma_scalar_cons2(a: u32, b: u32, rest: Seq<u32>)
    requires
        is_scalar_value(a),
        is_scalar_value(b),
        all_scalar_values(rest),
    ensures
        all_scalar_values(seq![a, b] + rest),
{
    let c = seq![a, b] + rest;
    assert forall|k: int| 0 <= k < c.len() implies is_scalar_value(#[trigger] c[k]) by {
        if k > 1 {
            assert(c[k] == rest[k - 2]);
        }
    }
}

/// Scalar value strings stay scalar value strings through
/// [`crlf_newlines`].
pub proof fn lemma_crlf_scalar(s: Seq<u32>)
    requires
        all_scalar_values(s),
    ensures
        all_scalar_values(crlf_newlines(s)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else if s[0] == 0x0D && s.len() > 1 && s[1] == 0x0A {
        assert forall|k: int| 0 <= k < s.skip(2).len() implies is_scalar_value(#[trigger] s.skip(2)[k]) by {
            assert(s.skip(2)[k] == s[k + 2]);
        }
        lemma_crlf_scalar(s.skip(2));
        lemma_scalar_cons2(0x0D, 0x0A, crlf_newlines(s.skip(2)));
    } else {
        assert forall|k: int| 0 <= k < s.drop_first().len() implies is_scalar_value(#[trigger] s.drop_first()[k]) by {
            assert(s.drop_first()[k] == s[k + 1]);
        }
        lemma_crlf_scalar(s.drop_first());
        if s[0] == 0x0D || s[0] == 0x0A {
            lemma_scalar_cons2(0x0D, 0x0A, crlf_newlines(s.drop_first()));
        } else {
            assert(is_scalar_value(s[0]));
            lemma_scalar_cons1(s[0], crlf_newlines(s.drop_first()));
        }
    }
}

/// [`to_scalar`] gives a scalar value string.
pub proof fn lemma_to_scalar_scalar(s: Seq<u32>)
    ensures
        all_scalar_values(to_scalar(s)),
{
    assert forall|k: int| 0 <= k < to_scalar(s).len() implies is_scalar_value(#[trigger] to_scalar(s)[k]) by {
        assert(to_scalar(s)[k] == (if is_scalar_value(s[k]) {
            s[k]
        } else {
            0xFFFDu32
        }));
    }
}

/// [`scalar_entries`] gives entries that are scalar value strings.
pub proof fn lemma_scalar_entries_scalar(es: Seq<Entry>)
    ensures
        entries_scalar(scalar_entries(es)),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_scalar_entries_scalar(es.drop_first());
        lemma_to_scalar_scalar(es[0].name);
        lemma_to_scalar_scalar(es[0].value);
        let rest = scalar_entries(es.drop_first());
        let all = scalar_entries(es);
        assert(all =~= seq![Entry { name: to_scalar(es[0].name), value: to_scalar(es[0].value) }] + rest);
        assert forall|k: int| 0 <= k < all.len() implies all_scalar_values(#[trigger] all[k].name) && all_scalar_values(
            all[k].value,
        ) by {
            if k > 0 {
                assert(all[k] == rest[k - 1]);
            }
        }
    }
}

/// [`convert_to_pairs`] keeps entries that are scalar value strings so.
pub proof fn lemma_convert_scalar(es: Seq<Entry>)
    requires
        entries_scalar(es),
    ensures
        entries_scalar(convert_to_pairs(es)),
    decreases es.len(),
{
    if es.len() > 0 {
        assert forall|k: int| 0 <= k < es.drop_first().len() implies all_scalar_values(
            #[trigger] es.drop_first()[k].name,
        ) && all_scalar_values(es.drop_first()[k].value) by {
            assert(es.drop_first()[k] == es[k + 1]);
        }
        lemma_convert_scalar(es.drop_first());
        lemma_crlf_scalar(es[0].name);
        lemma_crlf_scalar(es[0].value);
        let rest = convert_to_pairs(es.drop_first());
        let all = convert_to_pairs(es);
        assert(all =~= seq![Entry { name: crlf_newlines(es[0].name), value: crlf_newlines(es[0].value) }] + rest);
        assert forall|k: int| 0 <= k < all.len() implies all_scalar_values(#[trigger] all[k].name) && all_scalar_values(
            all[k].value,
        ) by {
            if k > 0 {
                assert(all[k] == rest[k - 1]);
            }
        }
    }
}

/// Concatenating scalar value strings gives a scalar value string.
pub proof fn lemma_scalar_concat(a: Seq<u32>, b: Seq<u32>)
    requires
        all_scalar_values(a),
        all_scalar_values(b),
    ensures
        all_scalar_values(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies is_scalar_value(#[trigger] (a + b)[k]) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// The `text/plain` encoding's loop keeps a scalar value string scalar.
pub proof fn lemma_text_plain_loop_scalar(pairs: Seq<Entry>, result: Seq<u32>)
    requires
        entries_scalar(pairs),
        all_scalar_values(result),
    ensures
        all_scalar_values(text_plain_loop(pairs, result)),
    decreases pairs.len(),
{
    if pairs.len() > 0 {
        assert forall|k: int| 0 <= k < pairs.drop_first().len() implies all_scalar_values(
            #[trigger] pairs.drop_first()[k].name,
        ) && all_scalar_values(pairs.drop_first()[k].value) by {
            assert(pairs.drop_first()[k] == pairs[k + 1]);
        }
        assert(all_scalar_values(pairs[0].name) && all_scalar_values(pairs[0].value));
        let eq = seq![0x3Du32];
        let crlf = seq![0x0Du32, 0x0Au32];
        assert(all_scalar_values(eq)) by {
            assert(is_scalar_value(0x3Du32));
        }
        assert(all_scalar_values(crlf)) by {
            assert(is_scalar_value(0x0Du32));
            assert(is_scalar_value(0x0Au32));
        }
        lemma_scalar_concat(result, pairs[0].name);
        lemma_scalar_concat(result + pairs[0].name, eq);
        lemma_scalar_concat(result + pairs[0].name + eq, pairs[0].value);
        lemma_scalar_concat(result + pairs[0].name + eq + pairs[0].value, crlf);
        lemma_text_plain_loop_scalar(
            pairs.drop_first(),
            result + pairs[0].name + eq + pairs[0].value + crlf,
        );
    }
}

/// The `text/plain` encoding of scalar value strings is a scalar value
/// string.
pub proof fn lemma_text_plain_scalar(pairs: Seq<Entry>)
    requires
        entries_scalar(pairs),
    ensures
        all_scalar_values(text_plain_encode(pairs)),
{
    lemma_text_plain_loop_scalar(pairs, Seq::empty());
}

/// One step of [`split_ws_acc`].
pub proof fn lemma_split_step(s: Seq<u32>, cur: Seq<u32>)
    requires
        s.len() > 0,
    ensures
        split_ws_acc(s, cur) == (if is_ascii_whitespace(s[0]) {
            (if cur.len() > 0 {
                seq![cur]
            } else {
                Seq::empty()
            }) + split_ws_acc(s.drop_first(), Seq::empty())
        } else {
            split_ws_acc(s.drop_first(), cur.push(s[0]))
        }),
{
}

/// The first candidate encoding of a list of labels whose first label
/// gives an encoding.
pub proof fn lemma_candidates_first(labels: Seq<Seq<u32>>, e: clazel_encoding::labels::spec::Encoding)
    requires
        labels.len() > 0,
        clazel_encoding::labels::spec::get_an_encoding(labels[0]) == Some(e),
    ensures
        candidate_encodings(labels).len() > 0,
        candidate_encodings(labels)[0] == e,
{
    assert(candidate_encodings(labels) == seq![e] + candidate_encodings(labels.drop_first()));
}

/// Appending an ASCII code point to an ASCII string.
pub proof fn lemma_ascii_push(s: Seq<u32>, c: u32)
    requires
        all_ascii(s),
        c <= 0x7F,
    ensures
        all_ascii(s.push(c)),
{
    assert forall|k: int| 0 <= k < s.push(c).len() implies #[trigger] s.push(c)[k] <= 0x7F by {
        if k < s.len() {
            assert(s.push(c)[k] == s[k]);
        }
    }
}

/// The literals the serializer appends for an unencodable code point
/// ("%26%23" and "%3B") are ASCII.
pub proof fn lemma_ascii_literals()
    ensures
        all_ascii(seq![0x25u32, 0x32, 0x36, 0x25, 0x32, 0x33]),
        all_ascii(seq![0x25u32, 0x33, 0x42]),
{
    let e = Seq::<u32>::empty();
    assert(all_ascii(e));
    lemma_ascii_push(e, 0x25);
    lemma_ascii_push(e.push(0x25), 0x32);
    lemma_ascii_push(e.push(0x25).push(0x32), 0x36);
    lemma_ascii_push(e.push(0x25).push(0x32).push(0x36), 0x25);
    lemma_ascii_push(e.push(0x25).push(0x32).push(0x36).push(0x25), 0x32);
    lemma_ascii_push(e.push(0x25).push(0x32).push(0x36).push(0x25).push(0x32), 0x33);
    assert(seq![0x25u32, 0x32, 0x36, 0x25, 0x32, 0x33] =~= e.push(0x25).push(0x32).push(0x36).push(0x25).push(
        0x32,
    ).push(0x33));
    lemma_ascii_push(e.push(0x25), 0x33);
    lemma_ascii_push(e.push(0x25).push(0x33), 0x42);
    assert(seq![0x25u32, 0x33, 0x42] =~= e.push(0x25).push(0x33).push(0x42));
}

/// Concatenating ASCII strings gives an ASCII string.
pub proof fn lemma_ascii_concat(a: Seq<u32>, b: Seq<u32>)
    requires
        all_ascii(a),
        all_ascii(b),
    ensures
        all_ascii(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies #[trigger] (a + b)[k] <= 0x7F by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// [`decimal`] is a string of ASCII digits.
pub proof fn lemma_decimal_ascii(n: nat)
    ensures
        all_ascii(decimal(n)),
    decreases n,
{
    if n < 10 {
        assert(decimal(n) =~= seq![(0x30 + n) as u32]);
    } else {
        lemma_decimal_ascii(n / 10);
        let d = seq![(0x30 + n % 10) as u32];
        assert(all_ascii(d));
        lemma_ascii_concat(decimal(n / 10), d);
    }
}

/// Percent-encode after encoding, step 7.3's body is ASCII: a non-ASCII
/// byte is in every set (step 7.3.3's assertion) so it is percent-encoded
/// into `%` and two upper hex digits.
pub proof fn lemma_encode_output_byte_ascii(set: PercentEncodeSet, space_as_plus: bool, byte: u8)
    ensures
        all_ascii(clazel_percent::spec::encode_output_byte(set, space_as_plus, byte)),
{
    if space_as_plus && byte == 0x20 {
    } else if !contains(set, byte as u32) {
        if byte > 0x7F {
            lemma_sets_include_non_ascii(set, byte as u32);
        }
    } else {
        let hi = byte / 16;
        let lo = byte % 16;
        assert(ascii_upper_hex_digit(hi) <= 0x7F);
        assert(ascii_upper_hex_digit(lo) <= 0x7F);
    }
}

/// The bytes' contribution from position `i` is ASCII.
pub proof fn lemma_encode_output_bytes_ascii(set: PercentEncodeSet, space_as_plus: bool, bytes: Seq<u8>, i: nat)
    requires
        i <= bytes.len(),
    ensures
        all_ascii(encode_output_bytes(set, space_as_plus, bytes, i)),
    decreases bytes.len() - i,
{
    if i < bytes.len() {
        lemma_encode_output_byte_ascii(set, space_as_plus, bytes[i as int]);
        lemma_encode_output_bytes_ascii(set, space_as_plus, bytes, i + 1);
        lemma_ascii_concat(
            clazel_percent::spec::encode_output_byte(set, space_as_plus, bytes[i as int]),
            encode_output_bytes(set, space_as_plus, bytes, i + 1),
        );
    }
}

/// The single-byte branch of percent-encode after encoding is ASCII.
pub proof fn lemma_pea_sb_ascii(e: clazel_encoding::labels::spec::Encoding, input: Seq<u32>, set: PercentEncodeSet)
    ensures
        all_ascii(percent_encode_after_encoding_sb(e, input, set)),
    decreases input.len(),
{
    if input.len() > 0 {
        lemma_pea_sb_ascii(e, input.drop_first(), set);
        let space_as_plus = set == PercentEncodeSet::ApplicationXWwwFormUrlencoded;
        match clazel_encoding::single_byte::spec::encoder_handler(e, ScalarItem::ScalarValue(input[0])) {
            EncoderResult::Byte(b) => {
                lemma_encode_output_byte_ascii(set, space_as_plus, b);
                lemma_ascii_concat(
                    clazel_percent::spec::encode_output_byte(set, space_as_plus, b),
                    percent_encode_after_encoding_sb(e, input.drop_first(), set),
                );
            },
            EncoderResult::Error(c) => {
                lemma_decimal_ascii(c as nat);
                let pre = seq![0x25u32, 0x32, 0x36, 0x25, 0x32, 0x33];
                let post = seq![0x25u32, 0x33, 0x42];
                lemma_ascii_literals();
                assert(all_ascii(pre));
                assert(all_ascii(post));
                lemma_ascii_concat(pre, decimal(c as nat));
                lemma_ascii_concat(pre + decimal(c as nat), post);
                lemma_ascii_concat(
                    pre + decimal(c as nat) + post,
                    percent_encode_after_encoding_sb(e, input.drop_first(), set),
                );
            },
            EncoderResult::Finished => {},
        }
    }
}

/// "Percent-encode after encoding" outputs an ASCII string, for UTF-8 and
/// for a single-byte encoding.
pub proof fn lemma_pea_ascii(e: clazel_encoding::labels::spec::Encoding, input: Seq<u32>, set: PercentEncodeSet)
    ensures
        all_ascii(percent_encode_after_encoding(e, input, set)),
{
    if e is Utf8 {
        let space_as_plus = set == PercentEncodeSet::ApplicationXWwwFormUrlencoded;
        lemma_encode_output_bytes_ascii(
            set,
            space_as_plus,
            clazel_encoding::utf8::spec::utf8_encode(input),
            0,
        );
    } else {
        lemma_pea_sb_ascii(e, input, set);
    }
}

/// The serializer's loop keeps its output ASCII.
pub proof fn lemma_serialize_loop_ascii(tuples: Seq<Entry>, encoding: clazel_encoding::labels::spec::Encoding, output: Seq<u32>)
    requires
        all_ascii(output),
    ensures
        all_ascii(serialize_loop(tuples, encoding, output)),
    decreases tuples.len(),
{
    if tuples.len() > 0 {
        let name = percent_encode_after_encoding(
            encoding,
            tuples[0].name,
            PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        );
        let value = percent_encode_after_encoding(
            encoding,
            tuples[0].value,
            PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        );
        lemma_pea_ascii(encoding, tuples[0].name, PercentEncodeSet::ApplicationXWwwFormUrlencoded);
        lemma_pea_ascii(encoding, tuples[0].value, PercentEncodeSet::ApplicationXWwwFormUrlencoded);
        let o1 = if output.len() != 0 {
            output.push(0x26u32)
        } else {
            output
        };
        assert(all_ascii(o1)) by {
            if output.len() != 0 {
                assert forall|k: int| 0 <= k < o1.len() implies #[trigger] o1[k] <= 0x7F by {
                    if k < output.len() {
                        assert(o1[k] == output[k]);
                    }
                }
            }
        }
        lemma_ascii_concat(o1, name);
        assert(all_ascii(seq![0x3Du32]));
        lemma_ascii_concat(o1 + name, seq![0x3Du32]);
        lemma_ascii_concat(o1 + name + seq![0x3Du32], value);
        lemma_serialize_loop_ascii(tuples.drop_first(), encoding, o1 + name + seq![0x3Du32] + value);
    }
}

/// The serializer's output is an ASCII string ("They return an ASCII
/// string"), so a scalar value string.
pub proof fn lemma_urlencoded_serialize_ascii(tuples: Seq<Entry>, encoding: clazel_encoding::labels::spec::Encoding)
    ensures
        all_ascii(urlencoded_serialize(tuples, encoding)),
        all_scalar_values(urlencoded_serialize(tuples, encoding)),
{
    lemma_serialize_loop_ascii(tuples, output_encoding(encoding), Seq::empty());
    let s = urlencoded_serialize(tuples, encoding);
    assert forall|k: int| 0 <= k < s.len() implies is_scalar_value(#[trigger] s[k]) by {
        assert(s[k] <= 0x7F);
    }
}

} // verus!
