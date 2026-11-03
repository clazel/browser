# Spec reviews

**Optional.** Reviews gate nothing. Whether a spec matches its standard is
established by machine-checked evidence instead: conformance tests,
independent transcriptions and certified mutation kills (see
[VERIFICATION.md](VERIFICATION.md#trust-without-reviewers)). A reviewer can be
socially engineered, so no reviewer is required. A human review is still a
useful extra signal, and this file records the ones that happen.

**Only humans add rows.** AI agents may edit spec files but must never add or
change a row here (CLAUDE.md), so that a row always means a person read the
file. The checker cannot tell who wrote a row; git history can.

## What needs review

Every file in a crate named:

- `spec.rs`: transcriptions of standards;
- `contract.rs`: what the implementation is proven to satisfy;
- `axioms.rs`: anything assumed rather than proven;
- `mutations.json`: the judgment, for each mutation, of whether a proven
  theorem is false for it (`killed`) or only the proof script breaks
  (`killed-incidentally`).

## How to review

1. Read the file against the standard it cites, at the commit it cites.
2. Run `cargo xtask check`. Under "spec reviews" it lists every file that
   is unreviewed or stale, with its current SHA-256.
3. Add (or update) one row per file: path, that SHA-256, your name, the
   date, and what you reviewed it against.

A row is **current** while the file's SHA-256 matches. Any edit to the file
makes the review **stale**. Review status is listed on every run and shown in
the status table (docs/STATUS.md). It never blocks anything.

<!-- BEGIN REVIEWS: checked by `cargo xtask check` -->
| File | SHA-256 | Reviewer | Date | Reviewed against |
|------|---------|----------|------|------------------|
<!-- END REVIEWS -->
