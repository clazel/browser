# Verification policy

This browser is written by AI. We do not ask anyone to trust that code.
Instead, every component carries a machine-checked guarantee, and the strength
of that guarantee is stated, not implied.

Machines check the implementations, and also the evidence that each spec
matches its standard. **No step depends on a human approving something.** A
reviewer can be socially engineered; a proof checker, an official test suite
and several unrelated browser engines are much harder to fool all at once.
See "Trust without reviewers" below.

## Tiers

| Tier | Guarantee | How it is checked |
|------|-----------|-------------------|
| 0 | Memory safe, no undefined behaviour | Safe Rust (`unsafe_code = "forbid"`, except in `clazel-sys`, below), Miri on tests, workspace clippy deny-lints |
| 1 | Never panics, overflows or indexes out of bounds, on **any** input | Kani bounded model checking harnesses over all inputs up to a stated bound |
| 2 | Functionally correct: the implementation refines an executable spec | Verus proofs (SMT-backed, unbounded) |

Each tier includes the ones below it, so a higher number is always a stronger
guarantee. **Testing is not a tier.** Web Platform Tests, fuzzing, and
differential testing against other engines apply at every tier. They catch
mistakes in specs, which proofs cannot, and they are the only evidence for
Tier 0 code.

Every crate declares its tier in `Cargo.toml`:

```toml
[package.metadata.clazel]
tier = 0          # what is proven about the shipped code today
target-tier = 2   # what this policy requires for the crate
```

`tier` is never raised for proofs about a spec alone; it describes the code
that runs. `cargo xtask verify` checks that every crate declares both, that the
declared tier is backed by tooling (Tier 2: Verus enabled for the crate,
since Verus also proves the absence of panics; Tier 1: the crate has Kani
harnesses), and it reports every crate whose `tier` is below its
`target-tier`.

## What must be at which tier

- **Tier 2 required:** the browser kernel (origin isolation, cookie and storage
  policy, permission checks), the IPC message codec, and the parsers for URL,
  HTTP/1.1 framing, encodings, percent-encoding, base64, MIME sniffing, and the HTML
  tokenizer state machine.
- **Tier 1 minimum:** every other parser of untrusted bytes: CSS, image
  decoders, font tables, JS lexer and parser.
- **Tier 0 minimum:** everything else (layout, paint, JS interpreter, UI).

## Tools

- **Verus**: functional-correctness proofs written in Rust syntax inside
  `verus! { ... }`. Chosen over Lean/F*/Coq extraction because the proof and the
  shipped code are the same artifact, so no extraction step can go wrong.
- **Kani**: bit-precise bounded model checking of ordinary Rust. Used for
  panic-freedom and for cross-checking Verus specs on small inputs.
- **Miri**: `cargo xtask verify` runs every test under Miri, which reports
  undefined behaviour. Our code has no `unsafe` outside `clazel-sys`, so it
  checks the dependency code our tests execute and `clazel-sys`'s safe
  parts. Miri cannot run foreign calls, so `clazel-sys`'s tests skip them
  under Miri (`cfg_attr(miri, ignore)`) and its evidence for them is the
  audit and the sandbox integration tests (Phase 2, items 2.15 and 2.16). Miri sees only code paths the tests run, so it is evidence, not
  proof. (Smoke test: an out-of-bounds read and a use-after-free that plain
  `cargo test` passes are both reported.)

Pinned versions (proofs must be reproducible). The source of truth is
`scripts/toolchains.env`; `verify.sh` fails if installed tools differ.

| Tool | Version |
|------|---------|
| Rust | `1.98.1` (stable; the toolchain Verus is built with) |
| Verus | `0.2026.10.04.426d8b0` |
| Kani | `0.68.0` (CBMC 6.11.0) |
| Miri | on `nightly-2026-08-21` (the nightly Kani uses) |

`scripts/setup.sh` installs all of them on macOS (arm64, x86-64) and Linux
(x86-64). It checks every download against `scripts/checksums.txt` and
installs nothing if a checksum differs.

## Local and CI runs

The full `cargo xtask verify` takes hours, so it runs where it is the gate:
in CI (`.github/workflows/ci.yml`), on Linux x86-64 with the pinned
toolchain, on every push to `main`, every manual run (Actions, "Run
workflow") and every pull request. Nothing is done, and no tier is raised,
until that run is green.

On a pull request the proofs (the `crate` parts below) wait for a person:
they need CI's `approval` job, which uses the `full-verification`
environment, and a reviewer set in that environment's settings approves it
("Review deployments" on the run). Until then only the cheap jobs run and
`Full verification` stays pending, so opening pull requests, however many,
never starts hours of proof jobs. Every push to a pull request starts a new
run, which needs a new approval.

CI splits the run into parts, one job each, so no job comes near GitHub's
six-hour limit (`xtask/src/parts.rs`):

- `verify --part base`: static checks, rustfmt, clippy and tests over the
  whole workspace.
- `verify --part miri`: static checks, then the workspace's tests under
  Miri. On macOS it runs in the same job as `base`, after it.
- `verify --part crate <names> --metrics <dir>`, where `<names>` is one
  crate or several separated by commas: static checks, then Kani, Verus,
  line counts, mutations and conformance for those crates. CI runs one job
  per crate with proof work (Verus, Kani harnesses or mutations) and one
  job for all the others together; the groups come from `cargo xtask
  crates`. Mutants run several at a time, each in its own sandbox
  (`CLAZEL_MUTANT_JOBS`, default one per core up to 4). On success it
  writes what it measured to `<dir>/<name>.json` for each crate, tagged
  with the commit (with `+dirty` if tracked files have uncommitted
  changes).
- `verify --part assemble --metrics <dir>`, the `Full verification` job,
  which fails unless every other job passed (a skipped job included, but
  `approval`, which runs on pull requests only): static checks, then it
  requires a file for every
  workspace crate from this commit, and reports whether README.md's table
  matches them.
- On pushes to `main` only, the `table` job runs the same part with
  `--write` after `assemble` passed, and commits README.md's regenerated
  table to `main` as github-actions[bot] if it changed. So the committed
  table always comes from CI's own measurements of a fully verified commit,
  and no change has to carry it.

The parts together run exactly the checks of one `cargo xtask verify`, which
`scripts/verify.sh` and the Docker command in README.md still run on one
machine. "CI is green" means every job passed on the same commit, the
`Full verification` (assemble) job included.

Locally, `cargo xtask verify --changed [base]` runs the same checks over
less. `base` defaults to `origin/main`, the last commit CI verified, and
the run compares the working tree (committed, staged, unstaged and
untracked files) with HEAD's merge base with it (`xtask/src/changed.rs`):

- The static checks, rustfmt and clippy cover the whole workspace, as in a
  full run.
- Tests, Miri, Kani, Verus, mutations and conformance run only for the
  crates with a changed file and every crate that depends on one of them,
  directly or not, dev-dependencies included.
- A change anywhere else, except `docs/`, `.github/`, `.claude/`, README.md,
  CLAUDE.md, LICENSE and `.gitignore`, checks every crate. That covers
  `Cargo.lock`, the workspace `Cargo.toml`, `rust-toolchain.toml`,
  `scripts/` and `xtask/`, which decides what passing means.
- The run ends in `RESULT: CHANGED CRATES PASSED (n of m crates …)`, never
  `ALL CHECKS PASSED`.

`cargo xtask report --write --changed` updates README.md's table the same
way. Rows of crates it checked are measured afresh. Rows of the others
keep their Verus, Kani, line, mutation and conformance cells from the
committed table, since nothing they depend on changed, and the remaining
cells (tier, axioms, `unsafe`, reviews) come from the static checks, which
always cover every crate. If the committed table has another column layout,
or lacks a row to keep, it refuses and asks for a full run. Its table is a
preview: the committed one is written by CI on `main`, which re-measures
every row, so a kept cell that is wrong never reaches it.

What this relies on: that a crate's proofs and tests depend only on its own
files, the workspace crates it depends on, and the shared files listed
above. Verus, Kani and the tests read nothing else, but a crate that read a
file outside its directory (say, another crate's vendored data through
`include_str!`) would not be re-checked when that file changed. CI's full
run catches it; the local run may not.

## Trusted computing base (what we do *not* prove)

We list this openly. Proofs are only as good as their assumptions.

- The Rust compiler, LLVM, and the Verus and Kani tools themselves
- The OS kernel and its sandboxing primitives (macOS Seatbelt, Linux seccomp,
  Landlock and namespaces)
- `clazel-sys`, the one crate with `unsafe` (see "The `unsafe` exception"
  below): a handful of foreign calls that enter the OS sandbox, and `libc`,
  its only shipped dependency, for struct layouts and constants
- Cryptography, which comes from formally verified libraries (libcrux / HACL\*), not our own code
- That each spec matches the standard it transcribes. No proof can check
  this, because the standard is English. It is backed by machine-checked
  evidence instead of a reviewer (next section), and that evidence is only as
  good as the test suites and the independence of the transcriptions.

## The `unsafe` exception

`unsafe_code` is forbidden workspace-wide (Tier 0) except in
`crates/clazel-sys`, because entering an OS sandbox needs calls that Rust's
standard library does not have: `sandbox_init` on macOS, and `prctl`,
`seccomp`, the `landlock_*` system calls and `unshare` on Linux. The choice,
and the options rejected, are in
[phases/phase-2.md](phases/phase-2.md#20-the-sandbox-and-unsafe-decision-s).
That crate is trusted, not proven, so what we claim for it is stated
precisely. "Audited" means two things, neither of them a human approval:

1. **Machine checks** (`cargo xtask check`):
   - `unsafe_code` is overridden in `clazel-sys` and nowhere else, and only
     that lint;
   - its only dependency is `libc`, pinned exactly;
   - only foreign functions from a fixed list in `xtask/src/sys.rs` may be
     declared or called (`sandbox_init`, `sandbox_free_error`, `prctl`,
     `unshare`, and `syscall` with only the numbers of `seccomp` and the three
     `landlock_*` calls);
   - every `unsafe` is a block or an `unsafe extern` block, with exactly one
     foreign call per block, and a `// SAFETY:` comment directly above it that
     cites a man page;
   - no raw pointer arithmetic and no dereference inside a block, and every
     `pub fn` is safe;
   - the README states the measured number of `unsafe` blocks and lines, and
     the generated status table lists them per crate.
2. **An LLM audit** of every change, by a session other than the one that
   wrote it, recorded in [SYS-AUDITS.md](SYS-AUDITS.md) with the SHA-256 of the
   crate's source. `check` fails if the latest audit's hash differs from the
   source. The auditor checks each `unsafe` block against the man page and
   the `libc` declaration it uses. That the author never audits its own
   change is a rule in `CLAUDE.md`, not a machine check, because the checker
   cannot tell which session wrote a row. It is therefore weaker than the
   machine checks: an audit is a second opinion from a model, not a proof.

`clazel-sys` makes no policy decisions. What a sandbox allows is data built
by safe, verified `clazel-sandbox`; `clazel-sys` hands it to the OS. The
crate stays at Tier 0, and renderers fail closed if any layer cannot be
applied.

## Trust without reviewers

A proof only shows that code matches its spec. What connects the spec to the
English standard is evidence, and Tier 2 requires all of it. Each piece is
checked by `cargo xtask`:

1. **Conformance tests through the proven implementation.** The
   implementation is proven equal to the spec, and is tested against the
   official suites (Web Platform Tests) and diffed against independent
   engines (for UTF-8: Rust's `String::from_utf8_lossy` and `encoding_rs`,
   used by Firefox). Proof plus tests means the *spec* behaves like the
   standard on every tested input. Subverting this needs WPT and several
   unrelated engines to agree on the same mistake.
   *Required for Tier 2: `tests/conformance*.rs`.*
2. **Independent transcriptions, proven equivalent.** A second transcription
   of the same standard (`independent.rs`), written without seeing the
   first, must be proven equal to it. A misreading shows up as a failed
   equivalence at the exact step. Where another standard defines the same
   thing (UTF-8 in the Unicode Standard, Table 3-7), that is the better
   second source, because a different body wrote it.
   *Required for Tier 2: `independent.rs`.*
3. **Certified mutation kills.** Every mutation must be a `killed` with a
   certificate that Verus checks: a concrete input on which the mutated spec
   violates a proven theorem, and the real spec does not.
   *Required for Tier 2: every mutation certified.*

Limits, stated plainly:
- For (1) and (2), `cargo xtask check` only checks that the files exist.
  That they pass is checked by `cargo test` and Verus, as usual. That they
  are *good* (thorough suites, truly separate transcriptions) is not
  machine-checked.
- Two AI transcriptions are not truly independent: they may share a
  misreading. That is why (1), which draws on sources outside the project,
  carries the most weight.
- Tests cover only what they test. Each crate's README row says which
  suites it runs and how many of their cases pass (below).

Human reviews ([SPEC-REVIEWS.md](SPEC-REVIEWS.md)) are still welcome and still
shown, but they gate nothing.

## Proof mutation testing

A proof can pass for the wrong reason, for example because its spec is too weak
to rule anything out. `cargo xtask mutate` (also run by `verify`) applies small,
deliberate bugs to each spec, listed in the crate's `mutations.json`, and checks
the proofs react as recorded: **killed** (a proven theorem is false for the
mutant), **killed incidentally** (only the proof script breaks, so this is not
coverage), or **survives** (a known gap, with what will close it). The report
counts these three separately.

Every `killed` carries a **certificate** that Verus checks: it evaluates the
spec on a concrete input and proves that the result contradicts a named
lemma. The certificate must verify with the mutation and fail without it. So
the only label that claims coverage cannot be wrong without the run failing.
The format is in `xtask/src/mutate.rs`.

## Honesty metrics

The README's status table is generated, never typed. For each crate it shows
the tier and target tier, the Verus result, Kani harness results, the number of
documented axioms (every other escape hatch is rejected outright), spec / proof /
exec line counts, the three-way mutation result, and conformance pass rates.
CI writes the committed table on `main` from the measurements of a commit
whose every verification part passed (the `table` job). `cargo xtask verify`
reports a committed table that differs from what it measured, and
`cargo xtask report --write` and `verify --part assemble --write` refuse to
write one while any check is failing.

The **Conformance** column lists every vendored suite a crate's
`tests/conformance*.rs` runs (WPT `encoding/`, `url/` percent-encoding,
`fetch/data-urls` base64, `mimesniff/mime-types`, …) as passing / total.
Expected failures, each listed in the test with its reason, are shown
separately and never counted as passes. The numbers are not typed: each
conformance test prints one `clazel-conformance:` summary line per suite,
and `verify` and `report` run every conformance test target and read those
lines from its output. A target that prints no summary, a malformed line, a
suite whose counts do not add up to its total, or an unexpected failure
fails the run. The line format is defined in one place, the module comment
of `xtask/src/conformance.rs`; a new conformance test must print it. The
count is only as good as the test's own bookkeeping: `total` is meant to be
the size of the generated table, counted independently of the pass count,
but that it is honest is not machine-checked.
