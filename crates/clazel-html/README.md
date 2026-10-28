# clazel-html

The HTML tokenizer and character references, formally verified with Verus.
Part of [Clazel](../../README.md), a web browser built from the bottom up by
AI using formal verification instead of trust.

## What it is

An implementation of the tokenization stage of the WHATWG HTML Standard
(Living Standard, whatwg/html commit `939677714d`, 26 October 2026):
preprocessing of the input stream (section 13.2.3.5), the tokenizer's state
(13.2.4) and all 84 states of section 13.2.5, with the named character
references of section 13.5 and the numeric character reference rules. The
standard at that commit has 84 states, not the 80 of earlier editions: the
decimal character reference start state is gone and five processing
instruction states are new, with a processing instruction token. Strings are
Unicode code points as `u32`, as elsewhere in Clazel.

Two faces, proven equal: `tokenize(input, start_state, last_start_tag)`
over the whole input, and `ExecTokenizer::next_token`, one token at a time,
which the tree builder drives (it switches the tokenizer's state between
tokens and sets `in_foreign_content` for the CDATA rule). Neither recurses
on the input's length, so the stack is bounded whatever the page.

Not included: the encoding sniffing algorithm (section 13.2.3.2, Phase 4
item 4.2, a later change to this crate), parse errors (not modelled: the
standard proceeds the same way with or without them), the insertion point
and `document.write`, and the parser pause flag (never set without
scripting).

## Verification

Tier 0 today, target tier 2. The crate's `tier` is raised only after CI's
full verification is green on a run with everything below. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- Every exec state function is proven equal to its spec function, a
  case-by-case transcription of the standard (`src/tokenizer/spec.rs`),
  and `next_token` and `tokenize` to the spec's two faces. Verus also
  proves that nothing panics, overflows or indexes out of bounds.
- The spec is total: every step consumes input, emits the end-of-file
  token, or hands the current character to a state of lower rank
  (`src/tokenizer/termination.rs`, one lemma per state).
- `theorem_tokenizer_total`: every run ends with exactly one end-of-file
  token, its last. `theorem_step_equals_whole`: the whole-input face is
  the fold of the one-token face. `theorem_output_bounded`: the character
  tokens are no more than the input's code points.
- The named character reference table is generated from the standard's
  `entities.json` (`cargo xtask tables`); Verus proves facts about it by
  evaluating it in pieces (every name non-empty and in bounds, the
  first-character index the matcher uses), and a match consumes at least
  two code points and emits at most two.
- 69 inputs and the standard's character reference examples are evaluated
  by Verus on the spec (`src/tokenizer/examples.rs`,
  `src/charref/examples.rs`); they are what the certified mutation kills
  contradict (`mutations.json`: all 118 mutations killed with
  certificates).
- An independent transcription from W3C HTML 5.2 §8.2.4 (`independent.rs`,
  79 states), written without reading `spec.rs`. **Not yet proven:** that
  it agrees with the spec on every input where the texts agree. Verus
  compares the two on 68 inputs (`agreement.rs`): 57 agree, and the 11
  that differ do so for listed differences of the texts (processing
  instructions; W3C's decimal character references, see
  [docs/ERRATA.md](../../docs/ERRATA.md)). This is what keeps the crate
  below tier 2.
- Conformance: every html5lib-tests `tokenizer/*.test` case, once per
  initial state, through the proven implementation (7,050 of 7,053 pass;
  3 expected failures, `xmlViolation.test`, which expects infoset
  coercion); and a differential test against `html5gum` on every html5lib
  input, each one mutated, and 20,000 random inputs (33,792 agree, none
  differ; 86 inputs with `<?` or lone surrogates are expected
  differences).

Current proof, mutation and conformance counts are in the
[status table](../../README.md#verification-status).

## Trust

The proofs assume the Rust compiler, Verus, and that the spec matches the
standard, which the conformance tests, the differential test and the
independent transcription support but cannot prove. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).

## Usage

Not yet published to crates.io (the workspace sets `publish = false`, and
the version is `0.0.0`). Use it as a path dependency:

```toml
[dependencies]
clazel-html = { path = "crates/clazel-html" }
```

```rust
use clazel_html::tokenizer::buffer::ExecToken;
use clazel_html::tokenizer::machine::{preprocess_exec, tokenize};
use clazel_html::tokenizer::spec::State;

fn main() {
    let input: Vec<u32> = "<p class=x>a&amp;b".chars().map(u32::from).collect();
    let tokens = tokenize(&preprocess_exec(&input), State::Data, None);
    assert!(matches!(tokens.first(), Some(ExecToken::StartTag { .. })));
    assert!(matches!(tokens.last(), Some(ExecToken::EndOfFile)));
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
