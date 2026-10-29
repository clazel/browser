//! Two more examples, kept apart from [`super::examples`] so that the
//! mutations they kill (`attribute-single-quote` and
//! `attribute-unquoted-end` in `mutations.json`) are verified against this
//! module alone. Each of those mutants makes some example in
//! `super::examples` look up a label that matches no row (`'866'`, or a
//! value that runs on past a space), and the evaluator times out scanning
//! all 228 rows, which Verus reports as an error that stops the build
//! rather than as a failed proof. Here neither mutant reaches a lookup that
//! fails: each example's mutant result is the windows-1252 default.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A `>` inside a quoted value does not end the tag.
pub proof fn lemma_example_quoted_gt()
    ensures
        sniff(seq![0x3Cu8, 0x6Du8, 0x65u8, 0x74u8, 0x61u8, 0x20u8, 0x78u8, 0x3Du8, 0x27u8, 0x3Eu8, 0x27u8, 0x20u8, 0x63u8, 0x68u8, 0x61u8, 0x72u8, 0x73u8, 0x65u8, 0x74u8, 0x3Du8, 0x38u8, 0x36u8, 0x36u8, 0x3Eu8], None) == (clazel_encoding::labels::spec::Encoding::Ibm866, Confidence::Tentative),
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(sniff(seq![0x3Cu8, 0x6Du8, 0x65u8, 0x74u8, 0x61u8, 0x20u8, 0x78u8, 0x3Du8, 0x27u8, 0x3Eu8, 0x27u8, 0x20u8, 0x63u8, 0x68u8, 0x61u8, 0x72u8, 0x73u8, 0x65u8, 0x74u8, 0x3Du8, 0x38u8, 0x36u8, 0x36u8, 0x3Eu8], None) == (clazel_encoding::labels::spec::Encoding::Ibm866, Confidence::Tentative)) by (compute_only);
}

/// An unquoted value ends at a space; the next attribute follows.
pub proof fn lemma_example_unquoted_value_end()
    ensures
        sniff(seq![0x3Cu8, 0x6Du8, 0x65u8, 0x74u8, 0x61u8, 0x20u8, 0x78u8, 0x3Du8, 0x61u8, 0x20u8, 0x63u8, 0x68u8, 0x61u8, 0x72u8, 0x73u8, 0x65u8, 0x74u8, 0x3Du8, 0x38u8, 0x36u8, 0x36u8, 0x3Eu8], None) == (clazel_encoding::labels::spec::Encoding::Ibm866, Confidence::Tentative),
{
    reveal(clazel_encoding::labels::data::LABEL_START_0);
    reveal(clazel_encoding::labels::data::LABEL_LEN_0);
    reveal(clazel_encoding::labels::data::LABEL_ENCODING_0);
    reveal(clazel_encoding::labels::data::LABEL_CHARS_0);
    assert(sniff(seq![0x3Cu8, 0x6Du8, 0x65u8, 0x74u8, 0x61u8, 0x20u8, 0x78u8, 0x3Du8, 0x61u8, 0x20u8, 0x63u8, 0x68u8, 0x61u8, 0x72u8, 0x73u8, 0x65u8, 0x74u8, 0x3Du8, 0x38u8, 0x36u8, 0x36u8, 0x3Eu8], None) == (clazel_encoding::labels::spec::Encoding::Ibm866, Confidence::Tentative)) by (compute_only);
}

} // verus!
