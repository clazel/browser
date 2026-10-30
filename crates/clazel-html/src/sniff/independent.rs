//! A second text for the sniffing algorithm's first steps, proven to agree.
//!
//! The Encoding Standard's "decode" hook (§6) is a second body's text for
//! steps 1 to 4: it, too, lets a byte order mark override the encoding it
//! is given. HTML's note on step 1 says its BOM step exists so that the
//! document's encoding and confidence are right, "although the decode
//! algorithm will itself change the encoding to use based on the presence
//! of a byte order mark". [`lemma_decode_agrees`] proves exactly that:
//! decoding with the sniffed encoding is decoding with the encoding steps 4
//! to 9 pick, and the confidence is certain exactly when the Encoding
//! Standard's own (second, independent) reading of the byte order mark
//! finds one (`clazel_encoding::hooks::independent::byte_order_mark`) or
//! the transport layer named an encoding.
//!
//! For the prescan the only text is HTML's; its evidence is the
//! html5lib-tests suite and the `encoding_rs` differential
//! (`tests/conformance_sniff.rs`), the examples (`examples.rs`) and the
//! lemmas (`lemmas.rs`). A same-text second transcription of the prescan is
//! not written yet (listed in the pull request).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Steps 4 to 9: the encoding the algorithm picks when there is no byte
/// order mark.
pub open spec fn without_bom(bytes: Seq<u8>, transport: Option<clazel_encoding::labels::spec::Encoding>) -> clazel_encoding::labels::spec::Encoding {
    match transport {
        Some(e) => e,
        None => match prescan(prescan_input(bytes)) {
            Some(e) => e,
            None => clazel_encoding::labels::spec::Encoding::Windows1252,
        },
    }
}

/// Decoding with the sniffed encoding is decoding with the encoding steps
/// 4 to 9 pick: the BOM step only repeats what "decode" does. The
/// confidence is certain exactly when a byte order mark or the transport
/// layer decided.
pub proof fn lemma_decode_agrees(bytes: Seq<u8>, transport: Option<clazel_encoding::labels::spec::Encoding>)
    ensures
        clazel_encoding::hooks::spec::decode(bytes, sniff(bytes, transport).0)
            == clazel_encoding::hooks::spec::decode(bytes, without_bom(bytes, transport)),
        (sniff(bytes, transport).1 == Confidence::Certain) == (
        clazel_encoding::hooks::independent::byte_order_mark(bytes) is Some || transport is Some),
        clazel_encoding::hooks::independent::byte_order_mark(bytes) is None ==> sniff(bytes, transport).0
            == without_bom(bytes, transport),
{
    clazel_encoding::hooks::independent::lemma_equals_bom_sniff(bytes);
}

} // verus!
