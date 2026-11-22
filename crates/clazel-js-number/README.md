# clazel-js-number

Part of [Clazel](../../README.md). ECMAScript's Number conversions
([phase-7.md](../../docs/phases/phase-7.md) item 7.11): no dependencies, no
`unsafe`.

| Function | What it is |
| --- | --- |
| `string_to_number(&str) -> f64` | StringToNumber (§7.1.4.1.1†): white space, decimal, `Infinity`, `0x`/`0o`/`0b`. Correctly rounded: Clinger's exact path, Eisel–Lemire, and an exact big-integer fallback. |
| `number_to_string(f64) -> String` | Number::toString, radix 10 (§6.1.6.1.20†): the shortest digits that round-trip, by Ryū. |
| `to_fixed`, `to_exponential`, `to_precision` | The three `Number.prototype` formatters (§21.1.3†), exact, by big integers. |
| `string_to_bigint(&str) -> Option<BigInt>` | StringToBigInt (§7.1.14†): white space, sign, decimal, `0x`/`0o`/`0b`, empty string is `0n`; `None` is the spec's `undefined`. |
| `bigint_literal_value(&str) -> Option<BigInt>` | The value of a lexer BigInt literal (`n` suffix, `_` separators, §12.9.3†). |
| `BigInt::to_string_radix(u32)` | BigInt::toString (§6.1.6.2.23†), radix 2 to 36, lowercase; `RangeError` outside that. |

`BigInt` is a sign and a `Big` magnitude (zero is never negative), so the limb
arithmetic exists once. Conversion takes a word-sized chunk of digits at a
time (quadratic), with a bit-extraction path for radix 2, 4, 8, 16 and 32.

† The section numbers are from `phase-7.md`; the spec text is not vendored, so
they are unchecked against the pinned commit (`clazel-js-lexer/SPEC-PIN.md`).

## Status: tier 0, target tier 1

Nothing is claimed as verified. What exists:

- **Differential tests** (`tests/differential.rs`) against Rust's correctly
  rounded `f64` parsing and shortest `Display`/`LowerExp`: every `f32` widened
  (a stride in a debug `cargo test`, every pattern with
  `CLAZEL_F32_STRIDE=1` in a release build, a far larger stride under Miri),
  300,000 random doubles and 400,000 random decimal strings from a fixed-seed
  generator, exact halfway cases between neighbouring doubles, and
  `toFixed`/`toExponential`/`toPrecision` against `{:.*}` and `{:.*e}`.
- **Kani harnesses** (`src/proofs.rs`): freedom from panics and overflow on
  bounded inputs (the list is in the file's header), including the BigInt
  digit functions and single-limb steps.
- **BigInt tests** (`tests/bigint.rs`) against an independent `Vec<u32>`
  schoolbook reference (parse by multiply-add, print by repeated division by
  the radix): random values in every radix 2 to 36, all radix pairs, every
  limb boundary up to 2^300, and the syntax edges of StringToBigInt and
  literals.

Raising the tier to 1 waits for CI's full verification on the pull request.

## Not here yet

- Heap storage for BigInts (item 7.5): this crate parses and prints them.
- Number::toString for a radix other than 10.
- The powers-of-five tables are computed on first use from `Big`, not stored.
  A later change can emit them as a checked-in constant, as `cargo xtask
  tables` does for IDNA.

## A difference from Rust's `Display`

Where the exact value of a double is halfway between two equally short
decimals, ECMA-262 picks the one with the even last digit; Rust's formatter
rounds the tie up (for example `-181082718617782.625`: JavaScript prints
`...62`, Rust prints `...63`). The tests assert that every disagreement with
Rust is such a tie, with the even digit on our side.
