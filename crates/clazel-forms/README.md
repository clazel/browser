# clazel-forms

HTML's form owner and "constructing the entry list" (the form data set), over
a `clazel-dom` arena, with Verus proofs. Part of
[Clazel](../../README.md), a web browser built from the bottom up by AI using
formal verification instead of trust. Phase 6 item 6.13; item 6.14 will add
the encodings (`application/x-www-form-urlencoded`, `multipart/form-data`,
`text/plain`) and the submission algorithm to this crate, and item 6.15 the
editing module (a separate tier 0 module, decision 6.0(b)).

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

## What is not done

- **The independent transcription** (`independent.rs`, proven equal to the
  spec) is not written, and no mutation of a document-dependent step has a
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
