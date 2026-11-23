# clazel-forms

HTML's form owner and "constructing the entry list" (the form data set), over
a `clazel-dom` arena, with Verus proofs. Part of
[Clazel](../../README.md), a web browser built from the bottom up by AI using
formal verification instead of trust. Phase 6 items 6.13 (the form data set) and
6.14 (the encodings and the submission algorithm, `src/submit/`); item 6.15 will
add the editing module (a separate tier 0 module, decision 6.0(b)).

## What it is

`construct_entry_list_exec(arena, rows, form, submitter, encoding,
constructing)` returns the list of (name, value) entries HTML §4.10.22.4
builds for `form`: the submittable elements whose form owner is `form`, in
tree order, each run through step 5 (skipped when under a `datalist`,
disabled, a button that is not the submitter, an unchecked checkbox or radio;
an image button's `name.x` and `name.y` from the click; no entry without a
name; a `select`'s selected enabled options; a checkbox or radio's value or
"on"; a hidden `_charset_`'s encoding name; the value of every other
control; a `dirname` entry, always `ltr` until bidi). Control state (value,
checkedness, selectedness, the dirty flags, the click's coordinates) is the
side table `rows`, one row per node id.

Form owner: the owner the tree builder set (it sets the parser inserted
flag), or HTML's "reset the form owner" on the final tree (nearest ancestor
`form`, or the first element with the `form` attribute's ID, if it is a
`form` and the control is connected).

## Encodings and submission (item 6.14, `src/submit/`)

`submit_exec(arena, rows, (form, submitter), document_encoding,
document_url, base_url, boundary)` runs HTML's form submission algorithm
(§4.10.22.3, from step 9: the caller has run validation and events) and
returns a plain value, `ExecOutcome`: `Ignored` (the standard returns),
`Refused(reason)`, or `Navigate` with the URL (a `clazel-url` record), GET or
POST, the body and its content type (POST), this tab or a new one, and
whether the referrer policy is `no-referrer`. The pieces:

- URL §5.2's `application/x-www-form-urlencoded` serializer, on
  `clazel-percent`'s set, with `clazel-encoding`'s UTF-8 and single-byte
  encoders (an unencodable code point becomes `%26%23N%3B`);
- HTML's "convert to a list of name-value pairs", the `text/plain` and
  `multipart/form-data` encoding algorithms (RFC 7578 parts; the boundary is a
  parameter, 1 to 70 `bchars`), "pick an encoding for the form"
  (`accept-charset`);
- the attributes `action`, `method`, `enctype`, `target`, `rel` of the form and
  `formaction`, `formmethod`, `formenctype`, `formtarget` of a submit button; the
  scheme table (`http`, `https`: mutate action URL for GET, entity body for POST;
  `data`, `ftp`: get action URL).

**Refused, listed** (`Refusal`): `method=dialog`; `mailto:` and `javascript:`
actions; any scheme not in the standard's table; an encoding with no encoder
here (the multi-byte legacy encodings, until Phase 8, and x-user-defined); a
multipart boundary that is not well formed. **Not run** (the caller's): the
sandbox flag, the `submit` and `formdata` events, interactive validation
(6.15), history handling (6.16). **Targets**: `_self`, `_parent`, `_top`, none
and empty mean this tab; `_blank` and every name mean a new tab (no other
tabs to find; the maintainer may reverse this). The action URL's own query
is parsed in UTF-8 (`clazel-url`), so for a POST in a single-byte document
encoding it differs from "encoding-parsing a URL". The boundary's absence from
the body is not checked.

## Verification

Target tier 2; `tier = 0` until CI's full verification is green on the pull
request (CLAUDE.md rule 7). Evidence so far, all run in WSL with Verus
`0.0.0-2026-10-04-0306` (see the pull request for the commands):

- `src/spec.rs` is a step-by-step transcription (HTML Standard commit
  `0793d3d8544eee95a862e6637130a8106c3d11ca`, section and step numbers in the
  comments; the modelling choices are listed at the top). `src/contract.rs`
  states what each executable function is proven to satisfy. Both were
  committed before any executable code.
- Every public function of `src/exec/` is proven **equal to its spec
  function**, for every well-formed arena (the Phase 4 theorem says the tree
  builder's output is one): `construct_entry_list_exec`, `field_entries_exec`,
  `controls_exec` (the form owner, resolved by one tree-order walk of the
  form's tree), `tree_order_exec` and `list_of_options_exec` (explicit-stack
  walks, so a deep tree cannot overflow the call stack), the ancestor walks,
  the value of each kind of control, `normalize_newlines`, `strip_newlines`,
  the whitespace strip, the textarea wrapping, `cols`' parse, decimal. Verus
  also proves no panic and no overflow. Lemmas (`src/lemmas.rs`) prove that
  every node of a tree order has the form's root as its root and so is
  connected exactly when that root is the document, and that **every entry of
  every entry list has a non-empty name**.
- `src/examples.rs`: the string algorithms on small inputs, evaluated by
  Verus. `mutations.json`: ten mutations of those algorithms, each
  certified killed by a lemma that is false for the mutant, and ten of the
  entry list's steps, recorded `killed-incidentally`.
- `tests/entry_list.rs`: 20 hand-made cases through the tree builder.
  `tests/conformance_forms.rs`: 19 checks from three pages of WPT
  `form-submission-0/` (all 32 of its pages need script, so the test reads
  the markup and data tables from the vendored files and runs the
  script-free part; see the file's header).

### Item 6.14's evidence

`src/submit/spec.rs` (HTML at the same commit as 6.13, URL at `clazel-url`'s
commit, modelling choices at the top) and `contract.rs` were committed first.
Every public function of `src/submit/exec/` is proven equal to its spec
function: the serializer (UTF-8 and single-byte), the pairs, `text/plain`,
multipart, the encoding pick, the attribute states, the target, and
`submit_exec` itself (for every well-formed arena). Lemmas
(`src/submit/lemmas.rs`): the serializer's output is ASCII (so UTF-8
encoding it is the identity), scalar value strings stay so through the newline
replacement and conversion. `src/submit/examples.rs`: worked examples
evaluated by Verus. `mutations.json`: mutations of the new spec, the string
and serializer ones certified, the document-dependent ones recorded
`killed-incidentally`. Tests: `tests/submit.rs` (hand-made cases through the
tree builder), `tests/conformance_encodings.rs` (WPT `urlencoded-parser` as
serialize-then-parse round trips, WPT `form-submission-0` `urlencoded2`,
`text-plain` and `multipart-formdata` without the `File` calls, and a
differential test of the serializer against `form_urlencoded` on 5000 random
inputs). The WPT files are copied under `tests/data/wpt-form-encodings/` and
converted by `xtask/src/testdata/wpt_form_encodings.rs`; the older
`conformance_forms.rs` still reads three pages from
`crates/clazel/tests/wpt-phase6/` with `include_str!`, so `verify --changed`
does not recheck this crate if those files change (docs/VERIFICATION.md).

## What is not done

- **The independent transcription** (`independent.rs`, proven equal to the
  spec) is not written for either item (6.14's would be RFC 7578 and RFC 3986
  for the encodings), and no mutation of a document-dependent step has a
  certificate (they need a concrete `Document` for Verus to evaluate). Both
  are required for tier 2.
- **Modelling choices that are gaps** (each in `src/spec.rs`'s header): an
  `option`'s value without a `value` attribute is the table's, the "get
  HTML-aware text content" algorithm is not transcribed; the selectedness
  setting algorithm and the radio button group's exclusion are the caller's
  (an option's selectedness is read from the table alone); file inputs
  contribute no entry; `email` is read as one address; input types other than
  the listed ones are read as text; `dirname` is always `ltr`; the textarea's
  hard wrapping is a fixed implementation-defined algorithm (a break after
  every `cols` characters).
- **Cost on hostile input.** The tree walks are linear. The per-control
  checks (nearest `form` ancestor, `datalist` ancestor, disabled `fieldset`
  and its first `legend`) walk up the ancestors, so a document with very many
  controls at the bottom of a very deep tree costs controls × depth; a version
  that carries the answers down the walk, and its proof, is item 6.20's if
  its measurement needs it.
- `select`'s `selectedcontent` and the form-associated custom elements are out
  (no script). No Kani harnesses, no Miri run of this crate's tests yet.

## Trust

The proofs assume the Rust compiler, Verus, `clazel-dom`'s well-formedness
(a Phase 4 theorem for the tree builder's output), and that the spec matches
the standard, which the examples, the tests and the WPT checks support but
cannot prove. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).
