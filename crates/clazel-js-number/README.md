# clazel-js-number

Part of [Clazel](../../README.md). ECMAScript's Number conversions
([phase-7.md](../../docs/phases/phase-7.md) item 7.11): no dependencies, no
`unsafe`.

| Function | What it is |
| --- | --- |
| `string_to_number(&str) -> f64` | StringToNumber (§7.1.4.1.1†): white space, decimal, `Infinity`, `0x`/`0o`/`0b`. Correctly rounded: Clinger's exact path, Eisel–Lemire, and an exact big-integer fallback. |
| `number_to_string(f64) -> String` | Number::toString, radix 10 (§6.1.6.1.20†): the shortest digits that round-trip, by Ryū. |
| `to_fixed`, `to_exponential`, `to_precision` | The three `Number.prototype` formatters (§21.1.3†), exact, by big integers. |

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
  bounded inputs (the list is in the file's header).

Raising the tier to 1 waits for CI's full verification on the pull request.

## Not here yet

- **BigInt parsing and printing** (StringToBigInt, BigInt::toString), which
  item 7.11 also lists. A later change adds them.
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
