//! Theorems about the input byte stream's spec. They are evidence that the transcription
//! is right, not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A label the protocol gives that names an encoding decides, whatever else there is.
pub proof fn theorem_protocol_first(
    stylesheet: Seq<u8>,
    label: Seq<u32>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
)
    requires
        clazel_encoding::labels::spec::get_an_encoding(label) is Some,
    ensures
        determine_the_fallback_encoding(stylesheet, Some(label), environment_encoding) == {
            clazel_encoding::labels::spec::get_an_encoding(label)->0
        },
{
}

/// Only the first 1024 bytes are read, so a sheet can be sniffed before all of it arrives.
pub proof fn theorem_reads_first_1024_bytes(
    a: Seq<u8>,
    b: Seq<u8>,
    protocol_label: Option<Seq<u32>>,
    environment_encoding: Option<clazel_encoding::labels::spec::Encoding>,
)
    requires
        first_1024_bytes(a) == first_1024_bytes(b),
    ensures
        determine_the_fallback_encoding(a, protocol_label, environment_encoding)
            == determine_the_fallback_encoding(b, protocol_label, environment_encoding),
{
}

/// With neither protocol nor document to say otherwise, the fallback is never UTF-16: a
/// sheet's own bytes cannot claim that.
pub proof fn theorem_bytes_never_give_utf16(stylesheet: Seq<u8>)
    ensures
        determine_the_fallback_encoding(stylesheet, None, None)
            != clazel_encoding::labels::spec::Encoding::Utf16Be,
        determine_the_fallback_encoding(stylesheet, None, None)
            != clazel_encoding::labels::spec::Encoding::Utf16Le,
{
}

/// A byte order mark decides, so nothing around the sheet changes what it decodes to
/// (the note under "decode").
pub proof fn theorem_bom_wins(
    stylesheet: Seq<u8>,
    label_a: Option<Seq<u32>>,
    environment_a: Option<clazel_encoding::labels::spec::Encoding>,
    label_b: Option<Seq<u32>>,
    environment_b: Option<clazel_encoding::labels::spec::Encoding>,
)
    requires
        clazel_encoding::hooks::spec::bom_sniff(stylesheet) is Some,
    ensures
        decode_bytes(stylesheet, label_a, environment_a) == decode_bytes(
            stylesheet,
            label_b,
            environment_b,
        ),
{
}

} // verus!
