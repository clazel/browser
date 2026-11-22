# clazel-js-regexp

Part of [Clazel](../../README.md). The ECMAScript pattern parser, the matcher
and the Unicode tables behind `\p{..}` and case folding
([phase-7.md](../../docs/phases/phase-7.md) item 7.10).

**Written: the pattern parser and its early errors. Not written: the matcher,
the case-folding tables and the property tables.** Tier 0 (target tier 1).

The Unicode 18.0.0 files the tables will be generated from are vendored in
`tests/data/ucd-regexp/` (see `SOURCE.md` there).

## The parser

`parse(pattern: &[u16], flags: Flags) -> Result<Pattern, Error>` reads a
pattern as UTF-16 code units (code points with `u` or `v`) into the tree of
`ast`, or says why not. `Flags::parse` reads the flag string.

Spec: ECMA-262, 2026 edition (pin in `clazel-js-lexer/SPEC-PIN.md`). The
specification's text is not vendored, so every section number is marked †
(from memory, not checked against the pinned commit): §22.2.1† (the
grammar), §22.2.1.1† (early errors), Annex B §B.1.2† (without `u` or `v`),
§13.2.7.1† and §22.2.3.4† (flags). `src/parser.rs` lists the modelling
choices at its top.

**Covered**

- The grammar of §22.2.1†, with Annex B's web-compatibility grammar when
  neither `u` nor `v` is set: braces and `]` as characters, legacy octal
  escapes, `\8` and `\9`, backreferences that become octal escapes when there
  are too few groups, `\c` quirks (also in classes), `[\d-x]`, quantifiable
  lookaheads, `InvalidBracedQuantifier`, `\k` as an identity escape when the
  pattern has no group names.
- The `u` flag: code points, `\u{..}` and surrogate-pair escapes, strict
  identity escapes, `\p{..}` and `\P{..}`.
- The `v` flag: class set expressions (union, `&&`, `--`, nested classes,
  `\q{..}`, ranges), the reserved double punctuators, `MayContainStrings` and
  the errors on negated classes, properties of strings.
- Named groups (`(?<name>..)`, `\k<name>`, escapes in names, ID_Start and
  ID_Continue from `clazel-js-lexer`'s Unicode 18 tables), and duplicate names
  in different alternatives.
- Regular expression modifiers (`(?i-ms:..)`).
- The early errors: out-of-order quantifier bounds (compared exactly, however
  large), out-of-order class ranges, class escapes as range ends with `u`/`v`,
  undeclared `\k<name>`, duplicate group names that can both take part,
  `\N` beyond the group count with `u`/`v`, invalid modifiers, invalid
  property names, negated classes that match strings, invalid flags.
- **A depth bound:** groups, lookarounds and classes nest at most
  `MAX_DEPTH` (128) deep; a deeper pattern is `ErrorKind::TooDeep`. The
  standard has no limit, so this is a deviation. The parser is recursive; the
  bound is what keeps its stack use small.

**Not done**

- `\p{Script=..}` and `\p{Script_Extensions=..}` values are accepted by
  syntax. A script table plugs in through `props::Names` (`parse_with`); the
  generated tables of item 7.10's second half are where it comes from.
  `General_Category` values, the binary properties and the properties of
  strings are checked, against lists in `src/props.rs` that
  `tests/conformance_names.rs` compares with the vendored UCD.
- The section numbers are not checked against the specification's text (†).
- There is no `spec.rs`: the parser is the transcription, with the grammar's
  production names at each step. No Verus.
- The matcher; `lastIndex`; `RegExp`'s object half (7.10's other items).
- Test262's `built-ins/RegExp` is not vendored (7.1 vendored `test/language/`
  only), so `new RegExp(..)` strings and the generated property-escape tests
  are not run.

## Evidence

- `tests/parser.rs`: about 240 hand-written accept and reject cases by mode
  (with the error each gives), tree shapes, the depth bound, large patterns,
  and every pattern of up to three code units over 33 grammar-significant
  units in all three modes (a stride under Miri).
- `tests/conformance_test262.rs`: every regular expression literal of the
  vendored Test262 (`language/literals/regexp/` and every other positive test
  with a literal), and the `eval` string arguments of those tests. The
  167 negative tests that `clazel-js-syntax` cannot reject (its README says
  so) are all rejected here. What is not judged is listed in the test, by name
  and reason (lexical errors, which are `clazel-js-lexer`'s; patterns built by
  computing a string; two tests whose error is in the JavaScript parser).
- `tests/conformance_names.rs`: the property names against the vendored UCD.
- `src/proofs.rs`: the Kani harnesses, below.

## Kani harnesses (compiled only under `cargo kani`)

`src/parser/proofs.rs`. Each runs one step of the parser on every input up to
a bound (a symbolic array of code units, a symbolic length, a symbolic start
position), and checks that no panic, overflow or out-of-bounds read is
reachable, with unwinding assertions that every loop finishes within the stated
bound. Each also asserts what the step's callers rely on: the position stays in
the pattern, a step that succeeds consumed something, an error's position is in
the pattern.

| Harness | Step | Bound |
|---------|------|-------|
| `cursor_any_4` | reading a code point, advancing | 4 units, each mode |
| `braces_any_6` | digit runs, `{n,m}` scanning, exact comparison of two bounds | 6 units |
| `quantifier_any_6` | a quantifier | 6 units |
| `character_escape_any_4` | `\n \cX \0 \x \u` and identity escapes | 4 units, each mode |
| `unicode_escape_any_8` | `\u{..}`, surrogate pairs | 8 units, both forms |
| `legacy_octal_any_4` | Annex B octal escapes | 4 units |
| `decimal_escape_any_3` | backreferences, Annex B's "only if" | 3 units, without `u` |
| `modifiers_any_6` | `(?ims-ims:` | 6 units |
| `property_escape_any_4` | `\p{x}` | 4 units (one-character names), `u` and `v` |
| `group_name_any_4` | `<name>` | 4 units below U+0080, each mode |
| `flags_any_9` | the flag string | 9 units |

**Not done.** The whole parse, and the steps that build a vector of tree nodes
in a loop (`class_ranges`, `class_set_expr`, `alternative`, `term`, `group`),
did not finish under CBMC: `class_ranges` ran 5 to 14 CPU-minutes at one, two
and three units, and the whole parse over 5 minutes at one unit and over 8 at
two. A `Vec`'s growth and the recursive drop glue of the tree are what cost.
So no harness covers the steps' composition: that each loop consumes a code
unit or fails, and that recursion is bounded by `MAX_DEPTH`. Those are tested
(every pattern of up to three units over 33 grammar-significant units in all
three modes, deep and wide patterns, 200 000-deep nesting), not proven. The
duplicate-name check (`names_in_disjunction`) is in no harness either. Group
names are checked only below U+0080: the lexer's `ID_Start` table lookup, which
Verus proves total there, is a bisection that costs CBMC minutes.

**The tier stays 0** until CI's full verification of the harnesses has passed
on a pull request (CLAUDE.md rule 7), and the whole-parse gap above is closed.
