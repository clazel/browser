# Rules for AI contributors

This codebase is written by AI agents. These rules exist so that nobody has
to trust the agents. Read `docs/VERIFICATION.md` and `docs/ROADMAP.md` first.

## Hard rules
1. **`unsafe` lives in one crate, `clazel-sys`.** `unsafe_code` is forbidden
   workspace-wide except in `crates/clazel-sys`, the crate that enters the OS
   sandbox. No other crate may override that lint, and `clazel-sys` overrides
   only that lint, in its `Cargo.toml` (never an inline `#[allow]`). Its only
   dependency is `libc`. Inside it, every `unsafe` is one block holding one
   call to a foreign function from the fixed list in `xtask/src/sys.rs`, with
   a `// SAFETY:` comment directly above it citing the man page and the
   `libc` declaration; there is no raw pointer arithmetic and every `pub fn`
   is safe. It makes no policy decisions: it takes data that safe, verified
   code built and hands it to the OS. `cargo xtask check` enforces all of
   this, and the README states the measured `unsafe` count.
   **Every change to `clazel-sys` is audited** by a different LLM session
   from the one that wrote it. The audit is a new row in
   `docs/SYS-AUDITS.md` carrying the SHA-256 of the crate's source
   (`cargo xtask check` prints it); `check` fails while the latest row's hash
   differs from the source. **Whoever writes or edits any file of
   `clazel-sys` never writes its audit row, in the same session or a
   continuation of it.** This is a rule, not a machine check: the checker
   cannot tell who wrote a row. After changing `clazel-sys`, leave the audit
   step failing and say so in the PR. An auditor follows the instructions in
   `docs/SYS-AUDITS.md`.
2. **Never weaken workspace lints** in a crate or with inline `#[allow]`
   (rule 1's `unsafe_code` in `clazel-sys` is the one exception).
   If a lint fires, restructure the code (use `get()`, checked arithmetic,
   explicit error types).
3. **Contracts before code.** In a Tier 2 crate, write the `spec fn` and the
   `requires`/`ensures` first and commit them separately, *then* the
   implementation and proof. The spec is the part humans review.
4. **No proof escape hatches.** `assume`, `admit`, `assume_specification`,
   and the `#[verifier::...]` attributes `external_body`, `external`,
   `external_fn_specification` and `exec_allows_no_decreases_clause` are
   banned. A genuinely needed axiom goes in the crate's `axioms.rs`, with a
   `// AXIOM:` justification within the three lines above it. The checker
   rejects every other use and counts the axioms in the README table.
5. **Cite the spec, and follow `docs/SPEC-STYLE.md`.** Every function
   implementing a standard links to the exact algorithm and quotes the step
   numbers it covers, e.g. `// URL §4.4 basic URL parser, step 3.2`. Spec
   files keep the standard's structure, names and step numbers, and list
   every modelling choice at the top.
6. **Never write spec reviews.** Do not add, edit or delete rows in
   `docs/SPEC-REVIEWS.md`, and do not "refresh" a stale review's hash, so that
   a row always means a person read the file. Reviews are optional and gate
   nothing; never present a review as evidence a spec is right. The evidence
   is in rule 7.
7. **Never mark something verified that isn't.** If a proof doesn't go through,
   say so in the PR and leave the crate at its real tier. Raising `tier` in a
   crate's `Cargo.toml` requires all of the following, and `cargo xtask check`
   rejects the claim otherwise:
   - every proof and harness passing in a full `cargo xtask verify`, which
     for a tier change means CI's green run on the pull request (a local
     `--changed` run does not count);
   - Tier 1: Kani harnesses;
   - Tier 2: Verus enabled; every mutation in `mutations.json` a `killed` with
     a certificate that Verus checks; conformance tests
     (`tests/conformance*.rs`) against official suites and independent
     engines; and an independent transcription (`independent.rs`) proven
     equivalent to the spec.

   No tier requires, or may cite, a human review. Never relabel a mutation's
   `expect` to get past this: a `killed` needs a certificate that verifies in
   the mutant and fails on the real spec, so a false one fails the run.
8. **Write our own parsers.** Any code that parses untrusted bytes is ours.
   Shipped dependencies are allowed only for crypto (verified libraries), OS and
   windowing bindings, and GPU access. Proof libraries (`vstd`) and build
   tooling that never ships (`xtask`) may use others. Every resolved package,
   transitive ones included, needs a row in the allowlist table in
   `docs/DEPENDENCIES.md`, with its exact version and class. `cargo xtask check`
   enforces this.
9. **Never report upstream.** When a standard, read literally, is wrong,
   specify its evident intent, comment why at that spot, and add an entry to
   `docs/ERRATA.md`. Filing an issue with a standards body is public: leave
   "Reported upstream: not yet" for a human to act on.

## Workflow
- Before handing work over, run `cargo xtask verify --changed` and report its
  output honestly. It runs every check, but repeats proofs, harnesses,
  mutations, conformance and tests only for the crates that differ from
  `origin/main` (the commit CI last verified) and the crates that depend on
  them; a change to anything shared (`Cargo.lock`, the workspace manifest,
  toolchain pins, `scripts/`, `xtask/`) makes it check every crate. It ends
  in `CHANGED CRATES PASSED`, which is not `ALL CHECKS PASSED` and must not
  be reported as such. Work is **done** only when CI's full verification
  (every job of `.github/workflows/ci.yml`, ending in `Full verification`)
  is green on its pull request; say so if it has not run yet. To repeat CI's run locally, use `scripts/verify.sh` or the
  Docker command in README.md. `cargo xtask check` runs only the fast static
  checks (unsafe, the `clazel-sys` audit, lint overrides, escape hatches,
  tier declarations, pins); use it while iterating, never as the final
  check.
- The only accepted lint overrides are `#[allow(unused_imports)]` directly on
  `use vstd::prelude::*;` or `use super::spec::*;` (ghost imports look unused
  to normal builds), and `unsafe_code = "allow"` in `clazel-sys`'s manifest.
  The checker rejects everything else.
- Never edit README.md's status table by hand, and do not commit a
  regenerated one with a change. CI keeps it up to date: after every push to
  `main` whose full verification passes, its `table` job writes the table
  from that run's measurements and commits it as github-actions[bot].
  `cargo xtask report --changed` still shows locally what the table would
  say; a table that differs from what a run measured is reported, not a
  failure.
- Keep changes small: one spec section or one proof per commit where practical.
- Test against official suites (WPT, html5lib-tests), vendored under `tests/`.
