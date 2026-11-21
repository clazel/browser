# clazel-js-regexp

Part of [Clazel](../../README.md). The ECMAScript pattern parser, the matcher
and the Unicode tables behind `\p{..}` and case folding
([phase-7.md](../../docs/phases/phase-7.md) item 7.10).

**Written: the pattern parser and its early errors; the backtracking matcher
with a bounded stack, a step budget and an interrupt hook; the case-folding
tables, and the General_Category, binary-property, Script, Script_Extensions
and properties-of-strings tables.**
Tier 0 (target tier 1): see "What is proven".

The Unicode 18.0.0 files the tables are generated from are vendored in
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

- `General_Category` values, the binary properties and the properties of
  strings are checked, against lists in `src/props.rs` that
  `tests/conformance_names.rs` compares with the vendored UCD. `Script` and
  `Script_Extensions` values are checked by `parse` against the generated
  `tables::SCRIPTS` (`props::UcdScripts`); `parse_with` takes any other
  `props::Names`.
- The section numbers are not checked against the specification's text (†).
- There is no `spec.rs`: the parser is the transcription, with the grammar's
  production names at each step. No Verus.
- The matcher; `lastIndex`; `RegExp`'s object half (7.10's other items).
- Test262's `built-ins/RegExp` is not vendored (7.1 vendored `test/language/`
  only), so `new RegExp(..)` strings and the generated property-escape tests
  are not run.

## The matcher

```rust
let pattern = parse(&pattern_units, flags)?;       // §22.2.1†
let program = compile(&pattern, flags)?;           // §22.2.2† as instructions
let m = program.exec(&input, start, sticky, &Limits::default(), None)?;
```

`Program::exec` matches UTF-16 input (`&[u16]`) from a code unit index
`start`: only there with `sticky` (`y`), else scanning forward. `lastIndex`,
`g` and what to do with the result are the caller's. A `Match` holds the
captures as code unit index pairs (index 0 the whole match; `None` for a group
that did not take part); `Program::named_capture` finds the group of a name,
duplicate names included.

Spec: §22.2.2† (Pattern Semantics), section numbers marked † as everywhere.
`src/compile.rs` and `src/vm.rs` list the modelling choices at their tops.

**Covered**

- Alternation, groups (capturing, named, duplicate names, non-capturing),
  greedy and lazy quantifiers with RepeatMatcher's empty check and the reset of
  captures on each iteration, counted quantifiers (`{n,m}` is a counter, not a
  copy), backreferences (numbered, named, backward ones in lookbehind),
  `^ $ \b \B` with `m`, `.` with and without `s`, classes and the escapes
  `\d \D \s \S \w \W`.
- Lookahead and lookbehind, positive and negative. A lookbehind matches
  backwards (terms right to left, characters read before the position, groups
  capture end first); bodies are atomic.
- `i`: `Canonicalize` without `u`/`v` is `toUppercase` of the code unit (never
  into or out of ASCII, never to more than one unit), with `u`/`v` simple case
  folding; `\w`/`\b` get U+017F and U+212A with `u`/`v` and `i`. Classes ask,
  as the standard does, whether some member has the character's canonical form
  (so `/\P{Lu}/iu` matches `A`, and `v` mode does not).
- `u` and `v` (code points): `.` and classes match a pair as one character,
  a lone surrogate is itself, and a search steps by code point.
- Modifiers `(?ims-ims:..)`, as compile-time flag scopes.
- `v` class sets: union, `&&`, `--`, nested and negated classes, ranges, and
  `\q{..}` with strings (matched longest first, then single characters, then
  the empty string).
- `\p{..}` and `\P{..}` for `General_Category` (every value and alias) and
  the binary properties of ECMA-262's table (`Any`, `ASCII`, `Assigned` and
  the others from tables generated from the UCD).
- `\p{Script=..}`, `\p{sc=..}`, `\p{Script_Extensions=..}`, `\p{scx=..}` and
  their `\P` forms, for every value of `PropertyValueAliases.txt` by long
  name, short name or further alias (`Qaai` for `Inherited`), including
  `Unknown` (`Zzzz`: every code point `Scripts.txt` does not list) and
  `Katakana_Or_Hiragana` (`Hrkt`: no code points). Under `i` they follow the
  same per-leaf rule as the other properties (`/\P{sc=Greek}/iu` matches
  `\u03b9`, `v` mode does not).
- Properties of strings with `v`: `Basic_Emoji`, `Emoji_Keycap_Sequence`,
  `RGI_Emoji_Modifier_Sequence`, `RGI_Emoji_Flag_Sequence`,
  `RGI_Emoji_Tag_Sequence`, `RGI_Emoji_ZWJ_Sequence` and `RGI_Emoji` (their
  union, UTS #51 ED-27), as an atom or in a class set, with `&&` and `--`: the
  strings of two or more code points longest first, then the one-character
  members (only `Basic_Emoji` has any), as for `\q{..}`.
- **An explicit backtrack stack, no recursion over the pattern or the input.**
  Choice points and register changes are entries of a `Vec` capped at
  `Limits::max_stack` entries (default a million, 16 to 24 bytes each). A
  match that needs more is `MatchError::StackOverflow`, which the engine turns
  into a `RangeError`: a listed deviation (the standard has no limit). A
  greedy loop over one character is one entry for the whole run.
- **A step budget and an interrupt hook** for 7.0(g): `Limits::max_steps`
  (`MatchError::StepLimit`), and a closure asked every 4096 steps
  (`MatchError::Interrupted`). A catastrophic pattern such as `(a*)*b` runs
  until one of these; the empty check and the one-entry runs keep its stack
  shallow, so it is the step budget that ends it, while `(?:a|aa)*b` on a long
  run of `a` fills the stack first and ends in `StackOverflow`
  (`tests/limits.rs`).
- Compilation recurses over the pattern, bounded by the parser's `MAX_DEPTH`
  (a deeper hand-built tree is `CompileError::TooDeep`); matching does not.

**Not done**

- A string property is matched as a flat list of alternatives, one
  instruction run per string (about 2 800 strings for `RGI_Emoji`), not a
  trie: correct, but a search for `\p{RGI_Emoji}` tries every string at each
  start. `CompileError::UnsupportedProperty` is now only for a tree built by
  hand with a name the tables do not hold.
- The `RegExp` object: `lastIndex`, `exec`'s result object, `d` indices,
  `Symbol.replace` and the rest (7.10's other items).
- Test262's `built-ins/RegExp` is not vendored, and the
  `language/literals/regexp` tests that run a match need a JavaScript engine
  (they assert on the result of `.exec`), so no Test262 match test is run
  here. The conformance tests are the standard's own worked examples
  (`tests/matching.rs`).
- Two choices, listed in `src/vm.rs`: a match that starts inside a surrogate
  pair with `u` starts at the pair, and the stack bound's allocation can be up
  to twice `max_stack` entries (the `Vec` doubles).
- The section numbers are not checked against the specification's text (†).
- No Verus. No `spec.rs`: the compiler and the matcher are the transcription.

## The tables

`src/tables.rs` is generated by `tests/tables.rs` from `tests/data/ucd-regexp/`
(there is no `cargo xtask tables` step: the generator is a test, so no other
crate's check is affected). The test `tables_are_current` fails if the
committed file differs from what the generator writes; to rewrite it run
`CLAZEL_WRITE_TABLES=1 cargo test -p clazel-js-regexp --test tables` and
`cargo fmt`. Contents: Simple Case Folding (`CaseFolding.txt`, `C` and `S`),
`toUppercase` of the BMP (`SpecialCasing.txt` and `UnicodeData.txt`),
`General_Category` (`DerivedGeneralCategory.txt`), and the binary properties
(`PropList.txt`, `DerivedCoreProperties.txt`, `DerivedNormalizationProps.txt`,
`DerivedBinaryProperties.txt`, `emoji-data.txt`), `Script` and
`Script_Extensions` per script (`Scripts.txt`, `ScriptExtensions.txt`, names
from `PropertyValueAliases.txt`), and the six emoji sequence types
(`emoji-sequences.txt`, `emoji-zwj-sequences.txt`; `RGI_Emoji` is their
union). About 29 500 lines.
Independent checks in the same file: the categories against `UnicodeData.txt`
for every code point, the equivalence classes (`unicode::equivalents`) against
`canonicalize` for every code point, folding idempotent, the word-character
extras exactly U+017F and U+212A, every property name resolving, every script
name resolving, `Script` and `Script_Extensions` against `Scripts.txt` and
`ScriptExtensions.txt` for every code point (read again, not through the
generator), and the string properties against the emoji files.

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
- `tests/matching.rs`: 234 hand-written matches by feature, with the
  result the standard's algorithm gives (several are the standard's own
  worked examples: `(z)((a+)?(b+)?(c))*`, `(?=(a+))a*b\1`,
  `(.*?)a(?!(a+)b\2c)\2(.*)`, `(?<=(\d+)(\d+))$`), start indexes and `y`,
  long inputs (100 000 characters, counts of 100 000 and 4 000 000 000).
- `tests/limits.rs`: catastrophic patterns end in `StepLimit` or
  `StackOverflow`; the stack bound is exact; the hook is asked and stops.
- `tests/differential.rs`: a reference matcher (a recursive, exponential,
  spec-literal transcription of §22.2.2† over characters, with closures for
  continuations, sharing only the parser, the case-folding function and the
  tables) against the matcher, over random patterns and inputs: 12 000
  patterns, about 87 000 comparisons (about 52 000 with a match), each at
  every start with and without `y`, in all of `i m s u v`. The test is not
  vacuous: injecting a bug into the empty check, the backward group capture,
  `\b`, the word-character extras, lookahead negation, or subtraction
  operand order each made it fail. A reduced count under Miri. A second test
  runs 33 patterns for `Script`, `Script_Extensions` and strings (order of
  the alternatives, `\P` under `iu` and `iv`, set operations, lookbehind) on
  every input of up to two tokens and a sample of three, about 19 000
  comparisons; making the strings shortest-first made it fail. The reference
  reads the same tables, so the tables are checked by `tests/tables.rs`.
- `tests/tables.rs`: the generated tables against the UCD, above.
- `src/proofs.rs`: the Kani harnesses, below.

## Kani harnesses (compiled only under `cargo kani`)

**The matcher's** (`src/proofs.rs`):

| Harness | Checks |
|---------|--------|
| `canonicalize_unit_any` | for every code unit, `Canonicalize` without `u` is a code unit and a non-ASCII unit never becomes ASCII |
| `simple_fold_any` | simple case folding of every code point is a code point |
| `stack_push_respects_the_bound` | any bound up to 4, six pushes: the length never exceeds the bound, a push is refused exactly when full |
| `stack_pop_returns_the_last_push` | a pop returns the last push, an empty stack nothing |
| `stack_commit_look_keeps_only_the_undos` | a positive lookaround's commit drops the mark and the choices above it, keeps the undo entries in order, returns the mark's position |
| `read_any_3` | reading a character at any position of any 3-unit input, either direction, either mode: the new position is inside and one or two units away, the character valid |

Not here: the matcher loop and the compiler (they build `Vec`s in loops, which
CBMC does not finish on, as for the parser below), and that the inverse case
table agrees with the forward one (a bisection twice over a table, with a
growing `Vec`: over ten CPU-minutes). Those are tested: the differential, and
`tests/tables.rs` for every code point.

**The parser's** (`src/parser/proofs.rs`). Each runs one step of the parser on every input up to
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

## What is proven

Nothing beyond the harnesses above, and none of them has had CI's full
verification on a pull request. **The tier stays 0** until it has (CLAUDE.md
rule 7), and the whole-parse gap and the matcher gap above are closed. The
matcher is tested, not proven: that it implements §22.2.2† rests on the
differential against a reference written from the same reading of the
standard, and on the hand-written cases.
