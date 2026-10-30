# Phase 4: HTML and DOM, detailed plan

**Goal:** the renderer turns the bytes the kernel fetched into a document
and shows it. Every byte of a page is parsed inside the sandbox by proven
code: the encoding is sniffed and decoded (HTML §13.2.3, Encoding Standard),
the stream is tokenized (HTML §13.2.5), the tokens build a DOM tree (HTML
§13.2.6, DOM Standard §4), and a text layout turns the tree into lines. The
tokenizer is proven total and panic-free, as the roadmap promises; the tree
builder and the DOM are proven functionally correct (tier 2, decided in
item 4.0). The kernel
gains two things and two theorems: a committed document is the fetched
body, carried whole to the right renderer, and what the user sees is
labelled by the kernel (the tab and its committed URL), never by the
renderer that drew it.

*Exit:* a text-mode browser in the style of Lynx: `cargo run -p clazel --
browse URL` fetches the page through the kernel, parses it in the sandboxed
renderer, prints the title, the text and numbered links, and follows the
link whose number the user types, with every parser on that path at its
target tier.

Nothing in this phase styles, scripts or draws. CSS is Phase 5 (the text
layout here is ours, replaced then); images and forms are Phase 6 (an image
is its `alt` text, a form is its text); JavaScript is Phase 7 (`<script>`
contents are tokenized as the standard requires and never run; the parser's
scripting flag is false, so `<noscript>` content is shown).

## Exit criteria

Phase 4 is done when all of these hold on macOS arm64 and Linux x86-64:

1. `clazel-html` (tokenizer, character references, encoding sniffing) and
   `clazel-dom` are at **tier 2**, accepted by `cargo xtask check` (every
   mutation a certified `killed`, conformance tests, an independent
   transcription each), and so is `clazel-treebuilder` (4.0 decided tier
   2); `clazel-encoding` is at tier 2 with every decoder it ships (a decoder
   lands with its proof, or not at all); `clazel-ipc` and `clazel-kernel`
   are at tier 2 with the schema and theorems of 4.12.
2. The html5lib-tests and WPT tree-construction suites pass through the
   proven implementation, vendored at pinned upstream commits: every
   `tokenizer/*.test` file
   (`initialStates`, `lastStartTag` and `doubleEscaped` cases included),
   every `tree-construction/*.dat` file except `scripted/` (which needs
   JavaScript), `#document-fragment` cases through the fragment parsing
   algorithm, `#script-on` and `#script-off` cases with the flag they name,
   and every `encoding/*.dat` file through the encoding sniffer. Any
   expected failure is listed by name with its reason, and counted in the
   README table.
3. `cargo run -p clazel -- browse http://example.com/` prints the page's
   title, text and links, typing a link's number navigates the tab through
   the kernel, and the address line the host prints is the kernel's
   committed URL for that tab. The same works for `https://` URLs once
   Phase 3's TLS (3.5) lands; until then the demo runs on `http://` sites
   and the in-process server of 4.16.
4. `clazel-kernel` proves `theorem_show_only_own_tab` and
   `theorem_address_bar_integrity` (4.12): what a renderer displays is shown
   for the tab of the socket it arrived on, labelled with the URL the kernel
   committed there, whatever the message says; and
   `theorem_body_is_the_response`: the body a committed renderer receives is
   the fetched response's body, whole and in order. The Phase 2 and 3
   theorems still hold with the new messages.
5. The hostile pages of 4.16 never panic a renderer, never exceed the stated
   memory bound, and never change the address line; the Phase 2 demo and
   the WPT `cookies/` run through real processes still pass.
6. `scripts/verify.sh` exits 0, with the README table showing the new rows,
   and VERIFICATION.md's required-tier list matches the decision in 4.0.

## What is proven, and what is assumed

1. **Proven (Verus):** "get an encoding" and the encoding sniffing
   algorithm with its prescan; every decoder `clazel-encoding` ships; the
   tokenizer, as a total function from a sequence of code points to a
   sequence of tokens, and as a one-token step the tree builder drives; the
   named and numeric character references; the DOM tree operations and that
   they keep the tree well formed; the tree builder; and in the kernel, the new commit protocol and display
   attribution theorems.
2. **Small and unproven (Tier 0, listed in the TCB):** the text layout
   (`clazel-text`, replaced by Phase 5's layout), the renderer's pipeline
   glue (read the frames, call the proven functions in order, send the
   result), and the host's command loop. The text layout runs inside the
   sandbox on an already-parsed tree; VERIFICATION.md puts layout at Tier 0,
   and its evidence is the hostile-page tests of 4.16.
3. **Assumed (TCB):** as before (the compiler, the tools, the OS, libcrux,
   `clazel-sys`), plus the html5lib-tests and WPT suites and the
   independent engines the differential tests use, as evidence that the
   specs match the standards.

What a parser bug can and cannot do, stated once: the renderer parses
untrusted bytes, but it does so inside the sandbox, and the kernel's
theorems (Phase 2 and 3, restated in 4.12) do not depend on anything the
renderer does. A bug in the tokenizer, the tree builder or the layout can
therefore mis-render or kill one tab; it cannot read another origin's
cookies, change the address line, or send anything the kernel's theorems
forbid. The proofs in this phase are about correctness and totality, which
is what makes the renderer *useful*; the sandbox and the kernel are what
make it *safe*.

Not covered by any theorem, and said so: timing and resource exhaustion
beyond the stated bounds (the tree builder is not linear in the worst case,
see 4.10 and 4.16); parse errors (never modelled, since the standard says a
user agent proceeds the same way with or without them); speculative and
incremental parsing (HTML §13.2.8, and `document.write`, which needs
JavaScript); everything outside the phase: CSS, scripting, images, forms,
`<meta http-equiv=refresh>`, session history in the kernel (the host keeps
a list of visited URLs for `b`ack), East Asian width and bidirectional text
in the text layout, and legacy multi-byte encodings until 4.4 lands. Nested
browsing contexts (`<iframe>`) are a kernel design question, since an
iframe of another origin is another renderer under the one-renderer,
one-origin rule; that design belongs to the Phase 5 plan, and here an
`<iframe>` is a link to its `src`.

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-encoding` | 2 (exists) | Encoding §4.2, §6, §9, §14; 4.4: §10 to §13 | "get an encoding" (labels), BOM sniff, the single-byte decoders, UTF-16, replacement, x-user-defined; later the multi-byte decoders |
| `clazel-html` | 2 | HTML §13.2.3 to §13.2.5, §13.5 | the encoding sniffing algorithm and prescan, input preprocessing, the tokenizer, character references, the entity table |
| `clazel-dom` | 2 | DOM §4.2, §4.4 to §4.14 (the parts the parser uses); Infra §8 | the node tree as an arena, the mutation algorithms, well-formedness |
| `clazel-treebuilder` | 2 | HTML §13.2.4, §13.2.6, §13.2.7, §13.4 | parse state, the insertion modes, foreign content, the fragment algorithm, the whole parser from code points to a `Document` |
| `clazel-text` | 0 | HTML §15.3 (which elements are blocks, hidden, or preformatted); the rest is ours | the text layout: a `Document` to lines and a link list |
| `clazel-ipc` | 2 (exists) | RFC 8949 §3; ours | byte strings in the profile; `Commit`, `Body`, `BodyEnd`, `Display` |
| `clazel-kernel` | 2 (exists) | ours | the commit protocol, `Show`, the display theorems |
| `clazel-renderer` | 0 (exists) | — | the document pipeline, run inside the sandbox |
| `clazel` | 0 (exists) | — | `browse`: the command loop; the host shell stays under 300 lines |

Section numbers are from the documents at the time of writing; each spec
header pins the exact commit it transcribes (SPEC-STYLE.md).

Each new Tier 2 crate starts as `tier = 0, target-tier = 2`. The tokenizer
and the tree builder are separate crates because a tier is a property of a
crate: the tokenizer's tier 2 must not wait for the tree builder's proof,
which is the largest in the phase.

## Dependencies on Phase 3

Phase 3's kernel join (3.7) is what makes this phase possible: a navigation
is a fetch the kernel steps itself, and `commit_navigation` already hands
the tab's renderer the response's body. Phase 4 changes what that commit
carries (4.12) and what the renderer does with it (4.13). Used:
`clazel-fetch`'s `Done { url, response }` (the body and the fields, for
`Content-Type`), `clazel-http`'s combined field value (RFC 9110 §5.2, to
read `Content-Type` out of the response), `clazel-mime` (parse the type,
sniff an unknown one), `clazel-url` (the document base URL and resolving
every `href`), `clazel-encoding` (UTF-8, extended here), `clazel-ipc` and
`clazel-kernel` (extended here), and the host and network shells (3.8).

TLS (3.5) is not a dependency: the text-mode browser runs on `http://`
until it lands, then speaks `https://` with no change here. 4.12 edits
`clazel-kernel`, `clazel-ipc` and `clazel`, which 3.7 and 3.8 also edit, so
it starts after the kernel-join branch is merged; everything else in this
phase is new crates and can start at once.

As in Phases 2 and 3, each crate is written against parameters first and
joined last: the tree builder takes the DOM operations and the tokenizer
step as parameters, so its proofs do not wait on theirs, and the whole
parser is their composition, stated once.

## Looking ahead: what Phases 5 to 7 will do with this

The DOM and the parser are the first structures every later phase reads,
and a proven crate is expensive to reshape, so this plan fixes now the few
shapes that later phases need, and names what it leaves to them.

- **The parser is a transducer.** The tree builder's step returns actions
  as item 3.6's fetch transducer does: `ChangeEncoding(enc)` (§13.2.3.4),
  `ScriptReady(node)` (where §13.2.6 says "prepare the script element", at a
  `</script>` in the "text" mode and at "the end"), `StopParsing` (§13.2.7
  and the node limit). Phase 4's pipeline acts on the first and the last and
  ignores `ScriptReady`, because the scripting flag is false; Phase 7 acts
  on it, pauses the parser, runs the script and resumes, and `document.write`
  becomes an edit of the input sequence at the insertion point. The spec is
  not restructured then: a driver is.
- **The tokenizer and tree builder are one-token steps** with explicit
  state (4.6, 4.9), so incremental parsing is a different driver over the
  same proven functions; the whole-input functions are their folds.
- **Node ids are handles.** An id is never reused within a document, as
  renderer ids are not; `remove` detaches a node and keeps its record, so a
  JavaScript reference to a removed node (Phase 7) stays valid; freeing is
  the job of Phase 7's collector, which marks nodes from the tree and from
  wrappers. Every node has an optional **wrapper slot** (a Phase 7 object
  id, always none here) and every element a **form owner** (set by the
  parser at creation, §13.2.6.1, read by Phase 6's form submission), so
  neither phase re-proves the parser to add a field. `wf` therefore allows
  detached subtrees, which the adoption agency and foster parenting create
  anyway.
- **A document is one arena.** The "node document" is implicit, and moving
  a node between documents (`adoptNode`, iframes) is not an operation here;
  Phase 7 adds it with its own proof.
- **What CSS needs is there.** Phase 5's selector matching reads parent,
  children, siblings, namespace, local name and attributes; computed style
  and the layout tree are side tables keyed by node id, not fields of the
  DOM. `<style>` contents and `style` attributes are kept like any text and
  attribute.
- **The display channel is Phase 4's.** `Display` carries text and links
  (4.12); Phase 5 replaces it with a drawn surface, and keeps the two
  theorems' shape: a renderer's output is shown for its own tab, labelled by
  the kernel. User actions take both paths already: the host's
  `navigate_tab` (a typed URL or link number) and the renderer's `Navigate`
  (a click, in Phase 5).
- **Left to later plans, by name:** nested browsing contexts and
  out-of-process iframes (Phase 5's kernel item), fetches started by a page
  (images in Phase 6, `fetch()` in Phase 7: new IPC messages, with the
  kernel's partition key choosing connections), the event loop and tasks,
  mutation observers and live collections (DOM's "insertion steps" and
  "removing steps" hooks, which the 4.8 operations are the one place to
  add), shadow trees and custom elements.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or
more. Each item follows CLAUDE.md rule 3: spec and contracts in one commit,
then the implementation and proof. The decisions of 4.0 are recorded, so
nothing waits on them.

### 4.0 The tree builder's tier, and two scope decisions (S) — decided

Three choices the maintainer makes before the items that depend on them.

**(a) The tree builder's tier.** VERIFICATION.md requires tier 2 for "the
HTML tokenizer state machine" and says nothing about the tree builder, so
as written the tree builder falls under "every other parser of untrusted
bytes: Tier 1 minimum". The tree builder is the largest parser in the
browser: HTML §13.2.6 is 23 insertion modes, foreign content, the adoption
agency algorithm, foster parenting and the list of active formatting
elements, several times the size of the URL parser (`clazel-url`: 5,725
spec lines, 565 verified functions).

- **Option A: target tier 2.** The tree builder is a pure step function
  over a DOM arena, proven equal to its spec mode by mode, as the URL
  parser was proven state by state; the DOM operations are proven to keep
  the tree well formed; html5lib-tests and a differential against Servo's
  `html5ever` are the conformance evidence; the independent transcription
  is W3C HTML 5.2 §8.2.5 (below). Cost: 4.9 to 4.11 are each L and the
  phase is not done until they are; the Phase 5 claim "every parser of
  untrusted input carries machine-checked proofs" is then true at tier 2
  for the whole HTML path.
- **Option B: target tier 1.** Kani harnesses prove the exec tree builder
  never panics on inputs up to a bound; html5lib-tests and the differential
  are the only evidence that it is correct. Cost: a wrong tree is not a
  proof failure, and the Phase 5 claim is true only in the weaker sense
  (Tier 1 is also what CSS and images will have).
- **Option C: tier 2 for a stated part.** The tree builder is split so
  that the modes a text-mode browser exercises most (initial, before html,
  before head, in head, after head, in body, text, after body) are proven
  at tier 2 in this phase and the rest (tables, select, template, frameset,
  foreign content) are tier 1 until Phase 8. Cost: a tier is a property of
  a crate, so this needs two crates with the second calling the first, and
  "in body" alone is most of the work anyway.

**Recommendation: A**, with the exit demo not waiting on the proof: 4.11's
conformance tests gate the demo (4.16), and the crate stays at tier 0 until
the proof is done. The grounds are those of 3.0: the claim must be true
when it is announced, and the DOM is the first structure every later phase
(CSS selectors, JavaScript bindings) reads, so a proven-well-formed tree
pays for itself. If A is taken, VERIFICATION.md's "Tier 2 required" list
gains "the HTML tree builder and the DOM operations it uses", and the
checker is unchanged (it reads `target-tier` from `Cargo.toml`).

**(b) Legacy encodings.** Phase 1 left every encoding but UTF-8 to this
phase, and VERIFICATION.md requires tier 2 for "encodings". The Encoding
Standard has 40 encodings: UTF-8; 28 single-byte ones (§9: one decoder
and one encoder algorithm each, over an index of 128 code points); UTF-16BE
and UTF-16LE, replacement and x-user-defined (§14); and seven multi-byte
ones (gb18030 and GBK §10, Big5 §11, ISO-2022-JP, Shift_JIS and EUC-JP
§12, EUC-KR §13), each a state machine over indexes of thousands of
entries. Recommendation: 4.3 (single-byte, UTF-16, replacement,
x-user-defined; M) is in this phase, and 4.4 (multi-byte; L) is in the
plan but may slip to Phase 8 without blocking the exit. Until 4.4 lands, a
document whose sniffed encoding has no decoder is **not rendered**: the
renderer shows the notice "encoding `<name>` is not supported" and the
page's links are not extracted. That is fail-closed and listed in the
README; decoding such a page as windows-1252 would show wrong text as if
it were right.

**(c) Where the body is parsed, and how it gets there.** In the renderer,
inside the sandbox (Quark's design and this plan's first paragraph). The
body reaches it through the kernel's commit, which today is `Commit { url,
script }` with the body as the `script` text string: a body that is not
valid UTF-8 cannot be framed (`frame_of` gives none), and `MAX_FRAME` is
1 MiB while `clazel-http` accepts bodies up to 64 MiB. 4.12 fixes both by
giving the CBOR profile byte strings and chunking the body into `Body`
frames after the `Commit`. The alternative, a larger frame limit for the
kernel-to-renderer direction only, is smaller to build but leaves the
profile with one limit that means two things and gives Phase 7 nothing to
stream into; chunking is recommended.

**Decision (2026-10-28), by the maintainer: the recommendations, all
three.** (a) Option A: `clazel-treebuilder` and `clazel-dom` have
`target-tier = 2`, and VERIFICATION.md's "Tier 2 required" list gains "the
HTML tree builder and the DOM operations it uses" (4.17). The cost accepted
is that the phase is not done until the tree builder's proof, independent
transcription and certified mutations are complete, while the text-mode
browser demo runs on 4.11's conformance tests alone. (b) 4.3 is in the
phase and 4.4 may slip to Phase 8; a page in an encoding with no decoder is
not rendered and says so. (c) Byte strings join the CBOR profile and the
body travels as `Body` frames after the `Commit`, re-proving `clazel-ipc`'s
codec. Taken with the forward-design additions of "Looking ahead" below,
which were part of the same decision.

### 4.1 Test data and tables (M)

Vendoring and conversion, in the pattern of items 1.0 and 3.3:

- **html5lib-tests** (MIT), pinned to one commit, under
  `crates/clazel-html/tests/data/html5lib-tokenizer/` (`tokenizer/*.test`,
  JSON: `input`, `output` as `["Character", …]`, `["StartTag", name,
  attributes, self-closing]`, `["EndTag", name]`, `["Comment", data]`,
  `["DOCTYPE", name, public, system, correctness]`, plus `initialStates`,
  `lastStartTag`, `doubleEscaped` and `errors`),
  and `crates/clazel-html/tests/data/html5lib-encoding/`
  (`encoding/*.dat`: `#data`, `#encoding`). html5lib-tests no longer
  carries the tree-construction suite; it lives in WPT, so
  `html/syntax/parsing/resources/*.dat` from the WPT commit the repository
  already pins (item 3.3) is vendored under
  `crates/clazel-treebuilder/tests/data/wpt-tree-construction/`
  (`#data`, `#errors`, `#new-errors`, `#document-fragment`, `#script-on`,
  `#script-off`, `#document` with the `| ` indented tree).
  `cargo xtask testdata` gains a
  converter for each shape (`xtask/src/testdata/html5lib_*.rs`), reading
  the fixed format and failing if it changes; `errors` and `#errors` are
  read and ignored, because parse errors are not modelled (stated in the
  generated file). `scripted/` is vendored for completeness and converted
  to a count of cases not run, never to passes.
- **WHATWG `entities.json`** (the named character references, HTML §13.5;
  2,231 entries) and the **Encoding Standard's `indexes.json`** (§5, the
  indexes every legacy decoder reads), each vendored byte for byte with a
  `SOURCE.md` (URL, commit, SHA-256, license), under `data/` of the crate
  that reads them, and turned into Rust tables by `cargo xtask tables`
  (`xtask/src/entities.rs`, `xtask/src/encoding_indexes.rs`), as `psl.rs`,
  `unicode.rs` and `roots.rs` do; `check` and `verify` fail if a table
  differs from what the vendored data gives. The entity table carries, for
  each name, its code points and whether it may match without a semicolon
  (the names listed in the standard's table without one).
- **WPT `encoding/`** legacy cases for 4.3 and 4.4: `textdecoder-labels.any.js`
  (every label to its encoding), `single-byte-decoder.window.js` and the
  `legacy-mb-*` directories, vendored at the pinned WPT commit already
  used, with a converter for each shape.

Dev-dependencies for the differential tests of 4.7, 4.11 and 4.3 get `test`
rows in DEPENDENCIES.md with their exact versions and the reason; the
candidates and what to measure are named in those items.

### 4.2 Encoding labels and the encoding sniffing algorithm (M)

In `clazel-encoding`: Encoding §4.2 "get an encoding" (the labels table:
ASCII case-insensitive, with leading and trailing ASCII whitespace
stripped), and §6 "BOM sniff". Lemmas: every label maps to exactly one
encoding; "get an encoding" of an encoding's own name is itself. The crate
stays at tier 2: the table and the two functions land proven, with their
mutations and the WPT labels suite.

In `clazel-html`, module `sniff/`: HTML §13.2.3.2 "determining the
character encoding" as the pure function `sniff(bytes, transport) ->
(Encoding, Confidence)` over the whole body (the standard's "wait for 1024
bytes or 500 ms" becomes "the first 1024 bytes of a body we hold whole", a
listed modelling choice): step 1 the BOM, step 2 no user override, step 3
the transport layer encoding (the `charset` parameter of the parsed
`Content-Type`, through `clazel-mime`, then "get an encoding"), step 4 the
prescan ("prescan a byte stream to determine its encoding": the comment,
`<meta>` with "get an attribute" and "extracting a character encoding from
a meta element", and the "a tag" and "punctuation" steps, over at most
1024 bytes), the steps that pass with no parent browsing context and no
history, and the final default, which the standard makes locale-dependent
and this plan fixes as windows-1252 (listed). §13.2.3.4 "changing the
encoding while parsing" is modelled as a restart: because the body is
whole, the tree builder's "change the encoding" (a `<meta charset>` found
after the prescan missed it) returns the new encoding to the pipeline,
which decodes and parses again from the start with confidence *certain*,
so a second change cannot happen (the standard's own rule). The pipeline
(4.13) therefore runs the parser at most twice.

Independent: the Encoding Standard §6 "decode" hook (BOM handling, "get an
encoding" for the fallback) is a second text for the first three steps,
proven equal where it covers them; for the prescan, the only text is
HTML's, so the second transcription is same-text, as `clazel-ipc` did for
CBOR, and the evidence is html5lib-tests' `encoding/*.dat` through
`sniff`, plus a differential against `encoding_rs`'s label resolution
(`Encoding::for_label`, Firefox's) on every label and random strings.
Mutations for each step and for each `<meta>` shape in the prescan.

### 4.3 Legacy single-byte encodings, UTF-16, replacement, x-user-defined (M)

`clazel-encoding`: Encoding §9 (one decoder and one encoder for the 28
single-byte encodings, each reading its index: a byte below 0x80 is itself,
otherwise "index code point" in the encoding's index, with null giving an
error), §14.1 replacement (one error, then end-of-queue), §14.2 and §14.3
UTF-16BE and UTF-16LE (the shared UTF-16 decoder with its lead-surrogate
state, unpaired surrogates to U+FFFD), §14.4 x-user-defined (bytes above
0x7F to U+F780 to U+F7FF). Decoders take the whole input, as the UTF-8
decoder does (no streaming; listed). Only the decoders are needed to show a
page; the single-byte encoder is small and is included for symmetry with
UTF-8 (forms, Phase 6, need it).

The indexes come from 4.1's generated tables. Lemmas: a single-byte
decoder never emits a surrogate; decoding is injective on bytes the index
defines; the UTF-16 decoder emits only scalar values.

Independent: the decoder algorithms are tiny; their second transcription
is same-text. The table *data* is checked against a second body's files
where one exists: the Unicode Consortium's `MAPPINGS/VENDORS/MICSFT/`
tables for the windows-125x and ISO-8859 encodings, vendored with their
terms, with the differences listed (the Encoding Standard maps 0x81, 0x8D,
0x8F, 0x90 and 0x9D of windows-1252 to C1 controls where Microsoft leaves
them undefined, and ISO-8859-8-I is a label). Conformance: the WPT labels
and single-byte suites of 4.1, and a differential against `encoding_rs`
(already a `test` row) on random bytes for every encoding. `encoding_rs`'s
tables are generated from the same `indexes.json`, so that differential
checks the algorithms, not the data; the Unicode files check the data.
Mutations per decoder step and per table (a swapped or missing entry is a
mutation of the generated table's checker, not of the spec).

### 4.4 Legacy multi-byte encodings (L; may slip to Phase 8, per 4.0)

`clazel-encoding`: Encoding §10 gb18030 (the four-byte ranges through
"index gb18030 ranges code point", GBK as a label of gb18030 with the
encoder difference), §11 Big5 (the "index Big5 pointer" lead and trail
rules, the four code points that decode to two), §12 ISO-2022-JP (the
escape-sequence state machine and its "output flag"), Shift_JIS (the
Shift_JIS lead rules, 0xA1 to 0xDF to half-width katakana, pointer
arithmetic with the 0x40 to 0x7E and 0x80 to 0xFC trail ranges), EUC-JP
(JIS X 0208 and 0212 through 0x8E and 0x8F), §13 EUC-KR; each with its
decoder only (encoders in Phase 6 if forms need them). The indexes
(`index-jis0208`, `index-jis0212`, `index-euc-kr`, `index-big5`,
`index-gb18030`, `index-gb18030-ranges`) are 4.1's tables.

Independent and conformance as 4.3: same-text transcriptions of the
algorithms, table data against the Unicode mapping files where they exist
(`JIS0208.TXT`, `JIS0212.TXT`, `BIG5.TXT`, `KSC5601.TXT`, obsolete but a
different body's; the Encoding Standard's vendor extensions listed as
differences), WPT `legacy-mb-*` suites, and `encoding_rs` on random bytes
(its gb18030 and Big5 are the right oracle for the algorithms, since its
data is the same). Until this item lands, 4.0(b)'s fail-closed notice
applies.

### 4.5 Character references and the entity table (S)

`clazel-html`, module `charref/`: HTML §13.5 named character references as
the generated table of 4.1 with the matching rule the tokenizer's "named
character reference state" needs (the longest name that is a prefix of the
input, with and without a terminating semicolon as the table allows, and
the "historical reasons" rule: in an attribute value, a match without a
semicolon followed by `=` or an ASCII alphanumeric is not a reference), and
the numeric character reference rules of §13.2.5's "numeric character
reference end state" (the C1 remap table: the 27 code points of 0x80
to 0x9F that are remapped, null to U+FFFD,
surrogates and values above U+10FFFF to U+FFFD, noncharacters and controls
emitted as parse errors only). Lemmas: a match consumes at least two code
points and emits at most two, so the tokenizer's output never exceeds its
input in code points; the table is prefix-free in the sense the matching
rule needs. Conformance: html5lib-tests' `namedEntities.test` covers every
entry, through 4.7. Mutations: a dropped entry, a semicolon rule reversed,
the attribute rule dropped, each C1 remap row.

**As built (4.1, tokenizer part, and 4.5):** html5lib-tests `tokenizer/`
is vendored at `c777c408` (2026-10-01; 6,827 cases) under
`crates/clazel-html/tests/data/html5lib-tokenizer/` with its converter
(`xtask/src/testdata/html5lib_tokenizer.rs`). html5lib-tests no longer
carries `tree-construction/` (its README says those tests now live in WPT
`html/syntax/parsing`); the tree builder's session vendors them from WPT.
`entities.json` is vendored from whatwg/html-build `283a3531` under
`crates/clazel-html/data/entities-283a3531/`, and `xtask/src/entities.rs`
generates `src/charref/data.rs`: the standard's 2,231 rows (names as the
table lists them, so the 106 names without a semicolon are their own rows)
and a first-character index, which `charref/index.rs` proves against the
rows. `charref/` has the spec (longest match, the attribute rule, the
numeric end state with the C1 table), contracts, the exec matcher proven
equal to the spec, and lemmas: every name non-empty and in bounds (Verus
evaluates the table in pieces), a match consumes at least two code points
and emits at most two, the match is the longest prefix, the end state
emits a scalar value other than U+0000. The standard's examples (`&notit;`,
`&notin;`, names with and without semicolons, two-code-point names) and
every C1 row are evaluated by Verus (`charref/examples.rs`); the 2,231-row
scan is beyond Verus's evaluator, so a divide-and-conquer form of the rule
is proven equal to it and evaluated by blocks. The encoding sniffer (4.2)
and `encoding/*.dat` are not part of this work.

### 4.6 The tokenizer: spec and contracts (L)

`clazel-html`, module `tokenizer/`: HTML §13.2.3.5 "preprocessing the input
stream" (CR LF and lone CR to LF; the character classes that are parse
errors and change nothing), §13.2.4 the tokenizer's state (the state, the
return state, the temporary buffer, the character reference code, the
current token, the "appropriate end tag token" rule from the last start
tag emitted), and §13.2.5: all 84 states, from the data state to the
numeric character reference end state (the standard added five
processing-instruction states and a processing instruction token in
2026, and dropped the decimal character reference start state; the
count is the standard's, not this plan's), as one spec function per state,
each step numbered against the standard's "Consume the next input
character" cases; the tokens (`DOCTYPE` with name, public and system
identifiers and the force-quirks flag; start and end tags with name,
attributes and self-closing flag; comment; character; end-of-file); the
attribute rules ("if there is already an attribute on the token with the
exact same name" drops the new one); and the `<!--`, `<![CDATA[` and
`</script>` escapes of the script data states.

Form, listed as modelling choices in the spec header:

- the input is `Seq<u32>` of code points after preprocessing, with the
  read position and "reconsume" modelled as the UTF-8 decoder modelled
  "restore" (not advancing);
- the tokenizer has two faces, proven equal: `tokenize(input, start_state,
  last_start_tag) -> Seq<Token>` over the whole input, which the
  html5lib tokenizer tests call (their `initialStates` and `lastStartTag`
  are these parameters, as the URL parser's state override was a
  parameter), and `next_token(state) -> (state, Seq<Token>)`, one token at
  a time, which the tree builder drives because it switches the tokenizer's
  state after `<title>`, `<textarea>`, `<style>`, `<script>`, `<xmp>`,
  `<iframe>`, `<noembed>`, `<noframes>`, `<plaintext>` and, with scripting,
  `<noscript>` (§13.2.6.2 and the "in head" rules);
- the "adjusted current node is not an element in the HTML namespace" test
  of the CDATA section state is a flag the tree builder sets on the
  tokenizer state (`in_foreign_content`), since the tokenizer never sees
  the tree;
- parse errors are not modelled (above); the `errors` arrays of the tests
  are ignored and the generated file says so;
- the tokenizer does not insert the "insertion point" or handle
  `document.write`.

Proven about the spec, and seeded as mutations: `theorem_tokenizer_total`,
that `tokenize` is defined for every input (every state either consumes a
code point or reconsumes into a state of lower rank, so the pair (remaining
input, rank) decreases; the rank is a table over the 84 states, and a cycle
in the reconsume graph would fail this proof, which is exactly what should
happen); `theorem_output_bounded`, that the character data emitted is no
longer than the input in code points (from 4.5's lemma); and that the two
faces agree, `theorem_step_equals_whole`. Contracts (`contract.rs`): the
exec tokenizer's `next_token` equals the spec's, its `wf` invariant, and
that `tokenize` is the fold of `next_token`.

**As built (4.6):** the standard at the pinned commit (whatwg/html
`939677714d`, 26 October 2026) has **84 tokenizer states, not 80**: the
decimal character reference start state is gone, and five processing
instruction states (§13.2.5.72 to §13.2.5.76, reached from the tag open
state on `?`) are new, with a processing instruction token (target and
data). `tokenizer/spec.rs` transcribes all 84, one spec function per state
(states the standard words identically call one shared function with
their states as parameters, listed in the header), with the modelling
choices of this item plus: the return state is an enum of the five states
it is ever set to, and the current attribute is kept apart from the tag's
list with whether it was removed as a duplicate. Proven: the spec is total
(`termination.rs`: a rank over the state and the next character that
every hand-off lowers, one lemma per state; a cycle would fail it),
`theorem_tokenizer_total` (every run ends with exactly one end-of-file
token, its last), `theorem_step_equals_whole` (`tokenize` is the fold of
`next_token`), and `theorem_output_bounded` (`output.rs`: the character
tokens are no more than the input's code points, from every start state
the tests and the tree builder use). The contracts relate the exec
tokenizer to the spec with the character reference code capped at
0x110000, which loses nothing (`charref::lemmas::lemma_end_code_cap`).

### 4.7 The tokenizer: implementation, independent transcription, conformance (L)

The exec tokenizer over `Vec<u32>` and `&[u32]`, one function per state as
in `clazel-url`, with the token under construction in a buffer type whose
view is the spec's token; every function proven equal to its spec function;
the whole-input face proven to be the fold. No recursion on input length in
exec code (the spec is recursive, the implementation iterates), so the
stack is bounded by a constant: Verus proves the absence of panics, not of
stack overflow, and a page is as long as a server likes.

Independent: W3C HTML 5.2 (Recommendation, 14 December 2017) §8.2.4
"Tokenization", a different body's publication of the algorithm, from a
text that has since diverged (states have been added and renamed; the
character reference states were restructured in 2017), transcribed without
reading `tokenizer/spec.rs` and proven equal on the inputs where the two
texts decide the same, with every difference listed in the lemma, as
`clazel-http` listed RFC 7230 against RFC 9112. Where the W3C text and the
living standard differ on an input, the living standard wins and the
difference is in the header, not hidden.

Conformance (`tests/conformance_tokenizer.rs`): every html5lib
`tokenizer/*.test` case through the exec tokenizer, with `initialStates`
run one state at a time, `doubleEscaped` cases unescaped by the converter,
character tokens coalesced as the suite expects, and `errors` ignored; and a
differential against an independent engine on random and mutated inputs
and on the suite's inputs. Candidates: `html5gum` (a spec-following
tokenizer with few dependencies) for the tokenizer alone; the agent
measures its dependency count and the `test` row says why. Expected
failures, if any, listed by name with the reason. Mutations: one or more
per state (a dropped case, a wrong target state, a flag not set), and for
each rule of 4.5.

After 4.5 to 4.7: **raise `clazel-html` to tier 2** (4.2's sniffer is
proven with it).

**As built (4.7):** every exec state function (`states_text.rs`,
`states_markup.rs`, `states_ref.rs`, with the shared actions in
`actions.rs`) is proven equal to its spec function, and `next_token` and
`tokenize` (`machine.rs`, loops only) meet the contracts; Verus verifies
the crate with 0 errors. Conformance (`tests/conformance_tokenizer.rs`):
html5lib-tests, every case once per initial state, 7,050 of 7,053 runs
pass and 3 are expected failures (`xmlViolation.test`, which expects the
infoset coercion step that follows tokenization); a differential against
`html5gum` 0.8.4 (no default features, no dependencies) on every html5lib
input, each mutated, and 20,000 random inputs: 33,792 agree, 0 differ, 86
expected differences (inputs with `<?`, which html5gum predates, or lone
surrogates). 69 inputs are evaluated by Verus on the spec
(`examples.rs`), visiting every state. `mutations.json` has 118 mutations:
one or more per state and per character reference rule, all 118
`killed` with certificates: a tokenizer mutant's tokens differ from an
evaluated example, or (for the attribute tests of the named character
reference and ambiguous ampersand states, which no whole-input example
Verus can evaluate reaches) contradict a state-level example
(`state_examples.rs`; the named one proven from the evaluated match and
its table row evaluated alone). The independent transcription
(`independent.rs`) is W3C HTML 5.2 §8.2.4, written by a separate agent
without reading `spec.rs`: 79 states (W3C 5.2 has 79), its own termination
proof. `theorem_w3c_equivalent` (`equivalence.rs`) proves the two equal on
every input with no `&`, no `<?` and no `[CDATA[`, from the html5lib start
states, state by state (a relation between the two tokenizers, one lemma
per shared state, and the cases where one text takes two steps for the
other's one: W3C "switches" to the bogus DOCTYPE state where the living
standard reconsumes there, and W3C has no `>` case in the before attribute
value state and no EOF case in the tag open state). The excluded inputs
are where the texts differ: character references (restructured since W3C
5.2; W3C §8.2.4.77 multiplies decimal digits by 16, ERRATA.md), processing
instructions (new), and `[CDATA[` in HTML content (same tokens, different
steps). Verus also evaluates both on 68 inputs, character references
included (`agreement.rs`): 57 agree, 11 differ for those differences. The
crate stays `tier = 0` until CI's full verification is green.

### 4.8 The DOM: node tree as an arena (M)

`crates/clazel-dom`. The tree the parser builds and everything later
phases read. A `Document` is an arena `Seq<Node>` indexed by node id (so
the whole DOM is safe Rust with no reference cycles, as the roadmap plans
for Phase 7's heap), where a `Node` is a `Document` (with its mode:
no-quirks, quirks or limited-quirks; its URL; and its base URL), a
`DocumentType` (name, public id, system id), an `Element` (namespace,
prefix, local name, attributes as an ordered list of namespace, prefix,
local name and value; and, for `<template>`, its contents as a
`DocumentFragment` child that is not in `children`), a `Text`, a `Comment`
or a `DocumentFragment`; each with `parent: Option<nat>`, `children:
Seq<nat>` and a wrapper slot `wrapper: Option<nat>` (always `None` in this
phase; Phase 7's object id, see "Looking ahead"); an `Element` also has
`form_owner: Option<nat>` (set by the parser, §13.2.6.1 "create an element
for a token"; read in Phase 6). Namespaces are Infra §8's six.

The operations, each cited to DOM §4.2.3 and proven against its steps on
the class of calls the parser makes: `append(parent, node)`, `insert_before
(parent, node, child)` ("insert" with a `child` reference, the "appropriate
place for inserting a node" needs it), `remove(node)`, `reparent_children
(from, to)` (the adoption agency's "move all children"), and the readers
§13.2.6 needs: parent, previous sibling, "has a child", "is a descendant".
DOM's mutation observers, slots, shadow trees, live ranges and the
"ensure pre-insertion validity" checks are out: the parser never violates
them, and that is a lemma (`lemma_parser_calls_are_valid`) proven in 4.10,
not a check at run time.

Proven: `wf(doc)`, that every child's parent is the node it is a child of
and conversely, that `children` lists are duplicate-free, that every
connected node has a depth with a child's one more than its parent's (so
the tree is acyclic), that the document node has no parent and is the root
of the connected part, that a template's contents fragment has the template
as its host and no parent, and that a detached node (no parent, not the
document) heads a well-formed subtree of its own: `remove` detaches and
never deletes a record, and ids are never reused (`theorem_remove_keeps_record`, `theorem_ids_stable`), so later phases can hold a node across its
removal; and that every operation keeps `wf` and does what its DOM steps
say (`theorem_append_wf`, …). A node limit is a spec parameter (`max_nodes`,
listed with its number, 4 million): `append` and `insert_before` refuse
beyond it, and the tree builder (4.9) treats a refusal as "stop parsing"
with the document shown truncated and a notice (4.13); this is the one
deliberate deviation from a standard that has no limits, in the pattern of
`clazel-http`'s `max_body`.

Independent: DOM §4.2.3's "insert" and "remove" have no second body's
text, so the second transcription is same-text, and the evidence is 4.11's
tree-construction suite, which checks the trees these operations build.
Mutations: a parent pointer not updated, a child inserted at the wrong
index, `remove` leaving the parent's list, `reparent_children` losing order,
the limit off by one.

**As built:** `crates/clazel-dom` on branch
`claude/phase4-dom-treebuilder-279901`. The arena, `wf` (with each node's
chain of inclusive ancestors as the acyclicity witness, so a node's depth
is one more than its parent's) and the operations as planned, plus a
`ProcessingInstruction` leaf (the pinned HTML standard inserts processing
instructions). The node limit is checked on node creation, where the arena
grows, rather than in `append` and `insert_before`. All thirteen theorems
are proven, the executable arena (`Vec<Node>`, ids `usize`, children edited
in place, no recursion) is proven equal to the spec, and the five planned
mutations are killed with certificates. `independent.rs` is a same-text
transcription of insert and remove (DOM §4.2.3 has no second body's text),
proven equal on the parser's calls. The crate stays at tier 0 until CI's
full verification is green; its conformance evidence is 4.11's suite.

### 4.9 The tree builder: spec and contracts (L)

`crates/clazel-treebuilder`, module `spec.rs` split by section, as
`clazel-url` was split by state: HTML §13.2.4.1 the insertion mode and
"reset the insertion mode appropriately"; §13.2.4.2 the stack of open
elements, the lists of *special* and *formatting* elements, "has an element
in scope" with the five scope definitions (scope, list item, button, table,
select), the *current node* and *adjusted current node*; §13.2.4.3 the
list of active formatting elements with markers, "push onto" with the
Noah's Ark clause, "reconstruct" and "clear up to the last marker";
§13.2.4.4 the head and form element pointers; §13.2.4.5 the scripting,
frameset-ok and foster-parenting flags, the stack of template insertion
modes and the "parser pause" flag (always false); §13.2.6.1 "appropriate
place for inserting a node" (foster parenting), "create an element for a
token" (the "is" attribute and custom element definitions are always null
without scripting, listed), "insert a foreign element", "insert a
character" (merging into an adjacent `Text`), "insert a comment";
§13.2.6.2 "generic raw text element parsing" and "generic RCDATA element
parsing" (which switch the tokenizer's state, 4.6); §13.2.6.3 "generate
implied end tags" and "generate all implied end tags thoroughly";
§13.2.6.4 all 23 insertion modes, each one spec function with its cases
numbered, including the "initial" mode's quirks determination (the public
identifier prefix tables), the "in body" rules in full with the adoption
agency algorithm (the outer loop of 8 and inner loop of 3, which give the
`decreases`), the table modes with foster parenting, "in select", "in
template" with the template modes stack, "in frameset" and the "after
after" modes; §13.2.6.5 foreign content with the MathML and HTML
integration points, the three adjustment tables (SVG attributes, MathML
attributes, foreign attributes) and the SVG tag name table; §13.2.7 "the
end" (stop parsing, with no scripts to run); and §13.4 the fragment parsing
algorithm (the context element, the tokenizer state it sets, the fake
`<html>` root, "reset the insertion mode" with the context, the form
element pointer), which the tests and Phase 7's `innerHTML` need.

Form, listed in the header:

- the state is `Parser { doc: clazel_dom::Document, tokenizer:
  clazel_html::State, mode, original_mode, open: Seq<nat>, formatting:
  Seq<Entry>, head, form, template_modes, frameset_ok, foster, scripting,
  pending_table_text, ignore_next_lf, … }`; the DOM operations and the
  tokenizer step are parameters (`DomFns`, `TokFns`), joined in the last
  commit as the kernel joined `UrlFns`;
- one spec function per insertion mode, `mode_X(parser, token) ->
  Parser`, and `dispatch(parser, token)` (the "tree construction
  dispatcher" of §13.2.6, which chooses HTML or foreign content rules);
- "reprocess the token" is a call of `dispatch` with the new mode. Its
  termination is a theorem (`theorem_dispatch_total`): a ranking over
  (mode, length of the stack of open elements, the template modes stack)
  that every reprocessing edge in §13.2.6.4 decreases. If some edge does
  not, that is either an erratum (ERRATA.md, with the loop as the witness)
  or a fuel bound stated as a modelling choice with its number, never a
  silent one;
- the step is a transducer, `dispatch(parser, token) -> (Parser,
  Seq<Action>)`, with `Action::ChangeEncoding(enc)` where §13.2.3.4 says
  "change the encoding" (`<meta charset>` in "in head"),
  `Action::ScriptReady(node)` where §13.2.6 says "prepare the script
  element" (the `</script>` case of the "text" mode, and "the end"), and
  `Action::StopParsing` for §13.2.7 and the `max_nodes` refusal (4.8); the
  parser takes no step for any of them, the driver does (4.13 now, Phase 7
  later, see "Looking ahead");
- the scripting flag is a parameter (false in the browser; the tests set
  it), the parser pause flag never set, `<script>` elements inserted and
  never executed, "prepare the script element" skipped (listed; Phase 7).

Proven about the spec: `theorem_dispatch_total`; `theorem_doc_wf`, that
every step keeps `clazel_dom::wf` (so the parser's calls are valid, 4.8's
lemma); `theorem_open_elements_in_doc`, that every id on the stack of open
elements and in the formatting list is a node of the document (an element,
with the document's `<html>` at the bottom); `theorem_nodes_per_token`,
that one token creates at most 1 + the length of the formatting list new
nodes (so growth is bounded by the input's formatting start tags, not
linear, see 4.16). Contracts: `step_requires` (`wf`, the tokenizer's `wf`),
`step_ensures` (equality with `dispatch` for any `DomFns` and `TokFns`),
and `parse_requires`/`parse_ensures` for the whole parser `parse(code
points, scripting) -> (Document, Seq<Action>)` and `parse_fragment(context,
code points, scripting) -> Seq<nat>`; `theorem_actions_ordered`, that
`StopParsing` is the last action and `ChangeEncoding` occurs at most once,
is what lets the pipeline run the parser at most twice.

**As built:** the pinned standard (HTML `939677714d`, 26 October 2026)
has 21 insertion modes, not 23 ("in select" and "in select in table" are
gone; `select` content is parsed by "in body"), a processing instruction
token, a sanitizer configuration, an insertion target redirection map and
template content patching; the spec follows the standard and lists the
last three, declarative shadow roots, custom elements, scripting and the
`selectedcontent` update of HTML §4.10.10 as stated restrictions
(`src/spec/mod.rs`). The DOM is called directly (`clazel-dom`'s spec), not
through a `DomFns` parameter, because both crates were built together; the
tokenizer is the `TokFns` parameter. `theorem_dispatch_total` is proven
with a lexicographic ranking (image token, template modes, a growth budget
for the implicit `html`, `head`, `body`, `colgroup`, `tbody` and `tr`
elements, stack length, an order of the rules); finding it took two
changes to the spec (popping an empty stack changes nothing; the fuel
bound is 372 (T + 1)(L + F·P + 5T + 11)) and an invariant on the modes,
`modes_ok`, which the theorem assumes. `theorem_actions_ordered` is proven
with no hypotheses (its proof found a spec bug, fixed: the bound's
exhaustion repeated the last step's actions). `theorem_reachable`: every
parser reachable from `new_parser` or `fragment_parser` by `dispatch` steps
satisfies `reachable_inv` (each mode's stack shape, `modes_ok`, the cells
of "in cell"), with no hypotheses, so `theorem_dispatch_total` holds for
every reachable parser. `theorem_doc_wf` and `theorem_open_elements_in_doc`
(a step keeps `clazel_dom::spec::wf` and every id of the parse state in the
document) and `theorem_nodes_per_token` are proven for a step from a
parser with `parser_wf`, a valid head pointer and `dispatch_needs` (which
`reachable_inv` gives); the last also assumes no element has two
formatting entries. `theorem_reachable_wf` discharges these hypotheses:
every reachable parser, stopped or not, has `parser_wf` (a well-formed
document, every id of its parse state in it, `modes_ok`: a stopped one has
an empty stack, `theorem_reachable_stopped`) and no element with two
formatting entries, and, until it stops, a valid head pointer; so the
three hold for a step from every reachable parser, with no hypotheses
(`theorem_reachable_doc_wf`, `theorem_reachable_open_elements_in_doc`,
`theorem_reachable_nodes_per_token`). `theorem_open_distinct`: a step keeps
the stack's elements distinct, so every reachable parser has distinct
elements on its stack (part of `theorem_reachable_wf`, with the
list of active formatting elements holding HTML elements and the
redirection map being the fragment case's); `theorem_reachable_w3c_facts`
proves the state preconditions of the W3C equivalence lemmas that are
facts of reachable states (`document_rooted`, `no_document_redirect`,
`aa_wf`, `tags_wf`, distinct stack, `place_stable`, `html_only_at_root`,
and in "in cell" a cell in table scope, from `reachable_inv`'s `html_once`
and `cell_scoped`), `theorem_reachable_foreign_content` states the foreign
content equivalence on every reachable parser without its stack
hypothesis, `theorem_reachable_frameset_cell` the "in frameset" and
"in cell" equivalences on every reachable parser with no hypothesis, and
`theorem_reachable_in_body_table` the "in body", "in table" and "in
table text" equivalences on every reachable parser after "before html"
with only the text-difference hypotheses (their precondition
`element_plain` of `html` and `body` follows from `reachable_inv`'s
`html_plain`: every HTML element but the context element has plain
attributes).
`theorem_reachable_parser_inv`: every reachable parser satisfies
`parser_inv` until it stops, `templates_wf` included (the reachable-state
invariant carries the document facts: every `template` record on the
stack has template contents, and no `template` element without them has
a child, since every insertion's parent comes from the stack's records,
tagged by their names). Not proven at the spec level: whether reachable parsers need the
6T term of the node bound (it pays for "in template"'s end of file
resetting the mode once per template). The true node bound is 44 +
6T + 2F + P(F + 1) per token (T template modes, F formatting entries, P
pending table characters), not the plan's 1 + F: the adoption agency alone may
clone 32 nodes, and a `nobr` start tag reconstructs twice.

### 4.10 The tree builder: implementation and proof (L)

The exec parser: `step(&mut ParserBuf, Token)` proven equal to `dispatch`
mode by mode, over `clazel-dom`'s exec arena (`Vec<Node>`, ids as `usize`
with the `nat` view) and `clazel-html`'s exec tokenizer, generic over
`DomFnsExec` and `TokFnsExec`, joined to the real ones in `real.rs` with
`parse_real` and `parse_fragment_real`. Nothing in exec recurses on the
tree's depth or the input's length (the adoption agency walks the stack by
index; "reset the insertion mode" and "has an element in scope" are loops),
so a page of a million nested `<div>`s is a million nodes, not a stack
overflow.

If one mode's proof is too slow for Verus, split its cases into functions
(the "in body" start-tag cases by tag group), which is how `clazel-url`'s
larger states were handled. Mutations: one or more per insertion mode and
per case that decides the tree (a dropped case, a wrong mode after
reprocessing, an element popped too early or not at all, the Noah's Ark
count off by one, foster parenting disabled, an adjustment table row
dropped, a scope definition widened), with certificates by example;
`theorem_dispatch_total` and `theorem_doc_wf` kill the structural ones.

**As built:** every insertion mode, foreign content, the adoption agency
and every shared helper has an executable function proven equal to its
spec function and to keep the parse state invariant; `exec::step::step`
(the reprocessing loop, iterative with a counter) is proven equal to
`dispatch` for every state with `parser_inv` and `reachable_inv`, and keeps
both, so it is equal on every reachable state. One resource limit is
raised (`chars_at_exec`, 300, with the reason at the attribute); the
others were removed by splitting proofs. Mutations: 48, all certified
kills (through the termination ranking, the order of actions and the W3C
equivalences of 4.11, foreign content and its tables included). The two
checks written as `exists`, which `compute_only` cannot evaluate, are
certified with the quantifier-free part of the check as the witness and
Z3 finding the contradiction.

### 4.11 The tree builder: independent transcription and conformance (L)

Independent (`independent.rs`): W3C HTML 5.2 §8.2.5 "Tree construction",
transcribed without reading `spec.rs`, proven equal to `dispatch` mode by
mode on the inputs where the texts agree, with the differences listed in
the lemma (the W3C text has `<menuitem>` and `<keygen>` rules, lacks later
changes to `<template>`, foreign content and the adoption agency's
details). This is the item most likely to run past the phase; if it does,
the crate stays at its real tier and the status table says so.

Conformance (`tests/conformance_tree_construction.rs`): every html5lib
`tree-construction/*.dat` case through `parse_real` or
`parse_fragment_real` with the scripting flag the case names, the built
tree printed in the suite's own `| ` format by a dumper in the test
(indentation by depth, attributes sorted by name as the suite does,
namespace prefixes `svg ` and `math `, `content` for template contents,
the `<!DOCTYPE …>` line) and compared byte for byte; the `scripted/` cases
counted and not run; expected failures listed by name with the reason. The
sniffing suite (`encoding/*.dat`) runs in `clazel-html` (4.2). A
differential against `html5ever` (Servo's parser, with `markup5ever_rcdom`
for its tree) on random, mutated and generated inputs: the agent measures
the dependency count (`markup5ever`, `string_cache`, `tendril`, `phf` and
their chains) and the `test` rows say why; if the count is unreasonable,
the differential runs against `html5ever` through a pinned binary built
outside the workspace, as a test fixture, and the row count stays small.
Where html5lib-tests and `html5ever` disagree, the suite wins and the case
is listed.

**As built:** html5lib-tests no longer carries the tree-construction
suite; it is vendored from WPT (`tests/data/wpt-tree-construction/`, 1,967
cases plus 6 scripted ones counted and not run).
`tests/conformance_tree_construction.rs` runs every case through
`clazel-html`'s proven tokenizer and the proven step, joined by
`clazel-treebuilder`'s `exec::driver` (`parse_real`,
`parse_fragment_real`; not test-only, the pipeline of 4.13 will call it):
it preprocesses the input, feeds each token the tokenizer emits to `step`
and applies the step's tokenizer switches and the foreign-content flag
before the next token. Verus proves each call meets its precondition, the
loop ends (the tokenizer's measure goes down on every call, a switch only
sets a text state, of the lowest rank, and after the tokenizer stops the
end-of-file token stops the parser, `theorem_eof_stops`), and the driver
equals the spec's `parse` and `parse_fragment` with `TokFns` instantiated
by the tokenizer (`spec::base::join::join_fns`: the tokens of one
tokenizer step are queued and handed out one at a time), for every bound
on the tokens from some bound on (`contract::parse_real_ensures`,
`contract::parse_fragment_real_ensures`); so the conformance results are
results of the spec. 1,963 cases pass and 4 are the `selectedcontent` restriction
(`webkit02.dat` 44 to 47), listed by name; no case found a bug in the tree
builder, the tokenizer or the driver. The test-only stand-in tokenizer is
removed. The W3C HTML 5.2
§8.2.5 transcription (`src/independent/`, from the dated REC URL; the
undated one now redirects to the WHATWG standard) covers 21 of its 23
modes, "in body" with the adoption agency among them, each proven equal to
the spec with the texts' differences stated; the W3C's two "in select"
modes have no counterpart. Its §8.2.5.5 foreign content rules, with the
three attribute adjustments and the SVG tag name table (transcribed from
the W3C text without reading the spec's tables), are proven equal too: the
tables on every name (same rows), the rules on every token the dispatcher
sends there, except the living standard's `menu` breakout start tag, its
`br` and `p` breakout end tags and the W3C's fragment case of the breakout
entries, and assuming distinct elements on the stack. The `html5ever`
differential (22 packages with `markup5ever_rcdom`) is not done.

After 4.9 to 4.11: **raise `clazel-treebuilder` to tier 2.**

### 4.12 The IPC schema and the kernel: commits, bodies and display (M)

`clazel-ipc`: the CBOR profile gains byte strings (RFC 8949 §3.1 major
type 2, definite length, as the profile already takes text strings), with
the codec's spec, contracts, lemmas, independent transcription, RFC 8949
vectors and `minicbor` differential extended; the message schema's field
types gain byte strings and one nested array of text strings. The schema
changes:

| Tag | Direction | Message | Fields |
|-----|-----------|---------|--------|
| 101 | kernel to renderer | `Commit` | url (text), content type (bytes, the combined `Content-Type` field value or empty), kind (unsigned: 0 a document, 1 a user script) |
| 106 | kernel to renderer | `Body` | bytes (at most `MAX_FRAME` minus the header and tag) |
| 107 | kernel to renderer | `BodyEnd` | |
| 10 | renderer to kernel | `Display` | title (text), text (text), links (array of text: absolute URLs) |

A committed document is `Commit`, zero or more `Body` frames, `BodyEnd`;
the body's bytes are the concatenation in order. `Display` is this phase's
channel to the user; Phase 5 replaces it with a drawn surface and keeps the
theorems below in shape. `kind` 1 is the Phase 2
script path (`OpenTab` with a script, the demo and the WPT `cookies/` run
through processes), which stays until Phase 7 replaces scripts with
JavaScript; a `Commit` of a fetched page always has kind 0. The two schema
rules of item 2.3 still hold and their lemma is restated: no message
carries a claimed identity (`Display` names no tab, origin or URL of its
own), and renderer ids never reach a renderer.

`clazel-kernel`: `commit_navigation` emits the sequence above with the
response's combined `Content-Type` value (RFC 9110 §5.2, through
`clazel-http`'s field functions; the kernel does not parse the type, the
renderer does) and the body; `open_tab(url, None)` starts a fetch
(`begin_navigation`) instead of committing an empty script, and
`open_tab(url, Some(script))` commits kind 1; a renderer's `Display` becomes
the output `Show { tab, url, title, text, links }`, where `tab` is the
sender's tab and `url` is the sender's committed URL, both from kernel
state. Theorems, each with certified mutations: `theorem_body_is_the_response` (the `Body` frames between a tab's `Commit` and `BodyEnd`
concatenate to the fetched response's body, for every fetch);
`theorem_show_only_own_tab` (a `Display` from renderer *r* produces at most
one `Show`, for *r*'s tab, and no other output); `theorem_address_bar_integrity` (`Show.url` is the committed URL of the renderer the frame came
from, for every message content, so no renderer can change the address
line); `theorem_reply_only_to_sender` and `theorem_cookie_noninterference`
restated with `Show` in the observation of a domain (the `Show`s of a
domain's tabs agree between two runs that agree on the domain's events,
and nothing else about them is claimed); the Phase 3 `Net` theorems
unchanged. A `Display` over `MAX_FRAME`, or from a renderer that is not
committed, is handled as any malformed or disallowed frame is (item 2.10's
rules).

`clazel`: the host shell carries out `Show` by printing (4.15) and stays
under 300 lines; `clazel-renderer` reads the new sequence (4.13). The
process tests of 2.16 and the `clazel` conformance rows run unchanged in
meaning (their scripts arrive as kind 1).

### 4.13 The renderer's document pipeline (M)

`clazel-renderer`: on `Commit` of kind 0, collect the `Body` frames to
`BodyEnd` (refusing more than `clazel-http`'s 64 MiB body limit, which the
kernel never exceeds; a listed check), then, in order and each by a proven
function: parse the content type (`clazel-mime`); if it is absent or
unknown, sniff it with the supplied type as the MIME Sniffing Standard says
(`clazel-mime`'s `sniff`, Phase 1); if the computed type is an HTML MIME
type, sniff the encoding (4.2), decode (4.3, 4.4), parse (4.10), and act on
the actions: on `ChangeEncoding` decode and parse again once, on
`StopParsing` keep the document built so far, and ignore `ScriptReady`
(Phase 7); if it is
`text/plain`, decode with the same sniff and show the text as one
preformatted block; otherwise show the notice "`<type>` is not shown" with
the URL. The document's URL is the committed URL; its base URL is the first
`<base href>` resolved against it (HTML "document base URL", through
`clazel-url`), and every `<a href>` and `<iframe src>` is resolved against
that for the link list (a `href` that does not parse is not a link). Then
the text layout (4.14) and one `Display`. On kind 1, the Phase 2 script
runner, unchanged.

The renderer stays single-threaded (the seccomp allowlist has no `clone`)
and allocates in proportion to the body: at most the body's bytes as code
points (`u32`, four times), the token buffer (bounded by 4.6's theorem),
the arena (`max_nodes` nodes, 4.8) and the text (4.14's bound); the sum is
stated in the crate's README with its numbers and measured in 4.16. Memory
beyond it is a bug, not a limit to raise.

### 4.14 The text layout (M)

`crates/clazel-text`, Tier 0 (the policy's tier for layout; Phase 5
replaces it). A pure function `layout(doc, width) -> Page { title, lines,
links }`, with these rules, each cited where a standard has one and marked
ours where it does not:

- hidden: `head`, `script`, `style`, `template` contents, `noscript` only
  when scripting is enabled (it is not), elements with the `hidden`
  attribute (HTML §15.3.1), and `title` (shown once as the page title);
- blocks: the elements HTML §15.3.3, §15.3.6, §15.3.7, §15.3.8 and
  §15.3.11 render as blocks (`p`, `div`, `h1` to `h6`, `ul`, `ol`, `li`,
  `blockquote`, `pre`, `hr`, `table`, `tr`, `address`, `section`, …), each
  starting a new line, with one empty line between paragraphs and headings
  (ours); everything else is inline;
- text: runs of ASCII whitespace collapse to one space and are trimmed at
  line edges (the effect of `white-space: normal`; ours, since CSS is
  Phase 5), except inside `pre`, `textarea` and `listing`, which keep their
  text (HTML §15.3.3's `white-space: pre`); `br` breaks the line;
- lists: `li` gets `* ` or its 1-based number in an `ol` (ours); `hr` is a
  line of hyphens (ours); a table's cells are separated by two spaces and
  its rows are lines (ours, as Lynx does);
- links: each `a` with an `href` that resolved (4.13) and each `iframe` with
  a `src` is followed by `[n]`, its 1-based index in `links` (ours, as
  Lynx does); `img` is `[alt]` or `[image]` (ours; Phase 6);
- wrapping at `width` columns on spaces, with a word longer than the width
  broken at the width; every scalar value is one column (a listed
  simplification: East Asian width, combining marks and bidi are Phase 5).

Bound: the text is at most the document's text plus a constant per
element. Evidence: unit tests per rule, a golden test of the html5lib
tree-construction inputs (the output committed and reviewed as fixtures),
and 4.16's hostile pages (no panic, the bound holds). A Kani harness over
bounded documents is welcome and not required.

### 4.15 The host: `clazel browse URL` (M)

`crates/clazel/cli/browse.rs`, outside the counted shell: open a tab at
the URL (a fetch, 4.12), then loop: on `Show`, print a rule, the address
line `URL: <the kernel's url>` (never anything from the message), the
title, the text, and `Links:` with each number and URL; then read a line
from standard input: a number follows that link (`navigate_tab(tab,
links[n])`, the user's own action, which is why the host and not the
renderer sends it), `g URL` navigates, `b` goes back along the host's list
of committed URLs, `r` reloads, `q` quits. A fetch failure (`Error` to the
renderer, item 3.7) is printed as such with the URL. Width from `COLUMNS`
or 80. No terminal library (rule 8): plain lines.

The host shell (`crates/clazel/src`) gains only the routing of `Show` and
the `Body` sequence and stays under 300 lines; `cargo xtask report` still
fails over it.

### 4.16 Exit demo, hostile pages, process tests (M)

- **Demo:** `cargo run -p clazel -- browse http://example.com/` and two or
  three `http://` sites that still serve plain HTML; the pages read, a link
  followed. Run locally (no Internet in CI), as the Phase 2 and 3 demos
  are; with 3.5 merged, the same for `https://` sites.
- **Through real processes:** an in-process server (`clazel-net`'s test
  server of 3.8) serves html5lib tree-construction inputs and a page with
  links, and a test drives `browse`'s loop against it: the `Show`
  outputs, the address line and the link numbers are checked, cross-origin
  links spawn a new renderer, and a `Set-Cookie` on the page reaches the
  jar (the WPT `cookies/` rows Phase 3 left for the kernel's `Set-Cookie`
  path run here too).
- **Hostile pages**, each through a real sandboxed renderer and all with
  the bound of 4.13 checked: a million nested `<div>`s; `<b>`, `<i>` and
  `<u>` repeated so the formatting list grows, then text that reconstructs
  it (the quadratic case, timed and its node count compared with 4.9's
  theorem); a body of 64 MiB of `&amp;`; `&` references without
  semicolons; a `<meta charset>` at byte 1025 (the restart); a page whose
  `Content-Type` lies; bytes that are not valid in any encoding; a page
  that is one `<plaintext>`; a `<title>` and a `<base href>` that look like
  the address bar (the address line is unchanged); a page over
  `max_nodes` (truncated with a notice); a hostile renderer that sends
  `Display` with another tab's URL as its title (shown under its own tab).
- **Phase 2 kept:** the demo, the escape attempts and the WPT `cookies/`
  run through processes pass with the new schema.

### 4.17 Status and README (S)

`cargo xtask report --write` for the local preview, the Phase 4 note in
README.md (what `browse` does, the encodings supported and the notice for
the others, the bound of 4.13), this file's Status table, ROADMAP.md, and
VERIFICATION.md's required-tier list per 4.0.

## Order of work

```
4.0 decisions (a) (b) (c)
4.1 test data + tables ─┬─> 4.2 labels + sniffing ──────────────────────────┐
                        ├─> 4.3 single-byte, UTF-16 ───> 4.4 multi-byte (may slip) │
                        └─> 4.5 charrefs ─> 4.6 tokenizer spec ─> 4.7 tokenizer ─┤
4.8 DOM ──────────────────> 4.9 tree builder spec ─> 4.10 exec ─> 4.11 evidence ─┼─> 4.13 pipeline ─> 4.16 demo ─> 4.17
4.12 IPC + kernel (after the kernel-join branch merges) ───────────────────────┤
4.14 text layout ──────────────────────────────────────────────────────────────┤
4.15 host browse ──────────────────────────────────────────────────────────────┘
```

4.1, 4.8, 4.9 (against abstract `DomFns` and `TokFns`), 4.14 and 4.15
start at once; 4.6 can start as soon as 4.5's table type exists; 4.12
starts when the kernel join is merged. The demo (4.16) needs 4.7, 4.11's conformance tests
and 4.12 to 4.15, not the tree builder's proof or tier.

## Status

| Item | State |
|------|-------|
| 4.0 Decisions | done (2026-10-28): A, tier 2 for the tree builder and DOM; 4.3 in phase and 4.4 may slip; byte strings and `Body` frames; the forward-design additions folded in. Decided (2026-10-30), by the maintainer: `html5ever` with `markup5ever_rcdom` is the tree builder's second engine (4.11's differential), as test-only dependencies (`[dev-dependencies]` of `clazel-treebuilder`, 22 `test` rows in DEPENDENCIES.md), not a pinned binary outside the workspace |
| 4.1 Test data and tables | tokenizer suite and entity table done (`clazel-html`); WPT tree-construction suite vendored with its converter (`clazel-treebuilder`); encoding data done: `encodings.json` and `indexes.json` vendored and generated (`cargo xtask tables`), the single-byte indexes checked against the Unicode mapping files (Apple's not vendored: no redistribution grant), WPT `encoding/` labels, single-byte, fatal single-byte and UTF-16 cases, html5lib-tests `encoding/`; `legacy-mb-*` with 4.4 |
| 4.2 Encoding labels and sniffing | done locally: get an encoding, BOM sniff and decode proven (`clazel-encoding`, tier 2) with both lemmas; the sniffing algorithm, prescan and change the encoding proven (`clazel-html` `sniff/`), Encoding's decode proven to agree with its first steps; WPT labels, html5lib-tests `encoding/` (75 pass, 7 expected failures needing the parser's restart, 1 scripted not run) and `encoding_rs` differentials; mutations certified; a same-text second transcription of the prescan proven equal on every input; waiting for CI's full run |
| 4.3 Single-byte, UTF-16, replacement, x-user-defined | done locally: every decoder and the single-byte encoder proven, with the three lemmas and same-text independent transcriptions; WPT and `encoding_rs` conformance; tables checked against the Unicode mapping files; mutations per step and per table certified; waiting for CI's full run |
| 4.4 Multi-byte encodings | not started |
| 4.5 Character references | done: spec, contracts, proof, examples, mutations |
| 4.6 Tokenizer spec and contracts | done: 84 states (the standard now has 84, not 80); total, output bounded, two faces equal |
| 4.7 Tokenizer implementation and evidence | done locally: proof, conformance, differential, 118 certified mutations, W3C transcription proven equivalent on its stated domain; `tier = 2` raised in PR `phase4/tier2-html-dom-treebuilder`, awaiting CI's full verification (real only once it is green) |
| 4.8 DOM | proofs, mutations and independent transcription done (merged); stays tier 0: `cargo xtask check` requires a `tests/conformance*.rs` in the crate itself for tier 2, and its conformance evidence is 4.11's suite in `clazel-treebuilder`, so the tier is not raised in PR `phase4/tier2-html-dom-treebuilder` |
| 4.9 Tree builder spec and contracts | spec done (21 modes); all five planned theorems proven, plus `theorem_reachable` and `theorem_reachable_wf`, which removes the hypotheses of the three document theorems for reachable parsers (`parser_wf` of every reachable parser, stopped or not: `theorem_reachable_stopped`), `theorem_reachable_parser_inv` (`parser_inv` of every reachable parser until it stops), `theorem_open_distinct` (distinct elements on the stack of every reachable parser), and `theorem_reachable_w3c_facts`, `theorem_reachable_foreign_content`, `theorem_reachable_frameset_cell` and `theorem_reachable_in_body_table`, which discharge the W3C equivalences' state preconditions that are facts of reachable states (`element_plain` of `html` and `body` included); `clazel-treebuilder` raised to `tier = 2` in PR `phase4/tier2-html-dom-treebuilder` (with 4.9 to 4.11), awaiting CI's full verification (real only once it is green) |
| 4.10 Tree builder implementation | every mode proven equal to the spec; `step` equal to `dispatch` for every reachable state; 48 mutations, all 48 certified; `clazel-treebuilder` raised to `tier = 2` in PR `phase4/tier2-html-dom-treebuilder` (with 4.9 to 4.11), awaiting CI's full verification (real only once it is green) |
| 4.11 Tree builder evidence | conformance through `clazel-html`'s tokenizer (`exec::driver`, proven equal to the spec's `parse` and `parse_fragment` with that tokenizer): 1,963 of 1,967 pass, the 4 `selectedcontent` cases listed; W3C transcription proven equal for 21 of 23 modes (the other two, "in select", are not in the living standard); differential against `html5ever` 0.39.0 (`markup5ever_rcdom`, `tests/conformance_html5ever.rs`): on the suite's inputs (3,898 parses, a case naming no scripting flag run with both), 3,699 trees agree and 199 differ in five listed classes, in each of which ours is the suite's tree and html5ever is behind our pinned standard or departs from it (processing instructions 175, `search` special 10, frameset-ok after head 6, "parsing template contents" for `form` 6, `input` in a `select` fragment 2); on 10,000 random tag-soup inputs, 9,991 agree and 9 differ by the same rules (`search` 3, `select` fragment 5, and html5ever's "in table body" scope test lacking `thead` 1, seen only there); no failure, no bug found in ours; `clazel-treebuilder` raised to `tier = 2` in PR `phase4/tier2-html-dom-treebuilder` (with 4.9 to 4.11), awaiting CI's full verification (real only once it is green) |
| 4.12 IPC schema and kernel | done locally: schema (Commit, Body, BodyEnd, Display), kernel commit protocol and Show, `theorem_show_only_own_tab`, `theorem_address_bar_integrity`, `theorem_body_is_the_response` proven, `theorem_committed_only_after_commit` proven, Phase 2 and 3 theorems restated; both crates stay at tier 2; waiting for CI's full run |
| 4.13 Renderer pipeline | done locally on branch `phase4/renderer-pipeline`, CI not yet run: `clazel-renderer` (tier 0) runs content type, MIME sniffing, encoding sniffing, decode, parse, one restart on "change the encoding", document base URL, link resolution and the text layout, and sends one `Display` cut to fit a frame; unit tests per rule; html5lib-tests `encoding/` through the pipeline 82 of 82 (the 7 restart cases included); `clazel browse` shows a parsed page and follows its link through the sandboxed renderer; the memory bound is stated in the crate README and not yet measured (4.16) |
| 4.14 Text layout | done locally on branch `claude/phase4-text-layout`, CI not yet run: `clazel-text` (tier 0), every rule unit-tested; golden test of the 1,761 html5lib document cases at width 80; the bound (`T + A + 80·N` characters, `T + A + 82·N` lines) checked on them and on generated documents |
| 4.15 `clazel browse` | done locally: the loop, tested against an in-process server through real renderers; with 4.13 it prints parsed pages (title, text, numbered links) and follows their links; the host passes its width to the renderers |
| 4.16 Demo and hostile pages | not started |
| 4.17 Status and README | not started |

## Risks

- **The tree builder dominates.** §13.2.6 is the largest algorithm the
  project has transcribed, and its proof (4.10) and second transcription
  (4.11) are each at least the size of the URL parser's. Mitigation: the
  demo does not wait on them; the spec is split by mode and the exec by
  case group; the tier stays honest until the proof is complete.
- **Termination of reprocessing.** The standard's "reprocess the token"
  edges are not stated as terminating; the proof needs a ranking. If a
  genuine cycle exists for some token and state, that is a finding
  (ERRATA.md), and a fuel bound is a stated choice, never silent.
- **The parser is not linear.** Reconstructing the active formatting
  elements can create as many nodes as the list holds, per token; a page
  can make that quadratic. The bound is stated (4.9's theorem, `max_nodes`)
  and measured (4.16); a renderer that hits it shows a truncated page,
  which is what browsers do when they give up too, only visibly.
- **Stack depth.** Verus proves no panics, not no stack overflow. Every
  exec loop over the tree or the input is iterative (4.7, 4.10, 4.14), and
  the million-nested-`<div>` page checks it.
- **Verus on a tree.** The arena with `wf` as an invariant is new; the
  kernel's `Seq`-of-records state with `kernel_wf` is the precedent. If
  depth-based acyclicity is too slow, state acyclicity as "parent index is
  smaller than the child's" (the parser only ever appends, except in the
  adoption agency and foster parenting, which move subtrees and would break
  that order) and prove the general form only where those run.
- **Independence.** The W3C HTML 5.2 text is a fork of the same text, not
  a second body's own algorithm; the lemmas list its differences, and the
  weight is on html5lib-tests and the `html5ever` differential, which come
  from outside the project (VERIFICATION.md, "Trust without reviewers").
- **A dependency-heavy oracle.** `html5ever`'s dependency chain may be
  long for a `test` row list; 4.11 names the fallback (a pinned binary as a
  fixture).
- **Encodings are wide, not deep.** Thirty-nine legacy encodings are
  mostly tables; the risk is the generated tables, which `cargo xtask
  tables` checks against the vendored `indexes.json`, and the Unicode
  mapping files check from a second body.
- **The schema change touches three tier-2 crates at once.** 4.12 lands as
  one pull request with `clazel-ipc`'s and `clazel-kernel`'s proofs,
  mutations and conformance all green; the 2.16 process tests are its
  regression suite.
- **No Internet in CI, and no TLS yet.** Every test runs against in-process
  servers; the demo on real sites is local and `http://` until 3.5 lands.
- **The text layout is throwaway.** It is Tier 0 and replaced by Phase 5;
  keep it small enough that its hostile-page tests are credible evidence,
  and do not grow it toward CSS.
