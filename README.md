# Clazel

A web browser built from the bottom up by AI, using formal verification
instead of trust.

- **Memory safe:** 100% safe Rust except `clazel-sys`: 43 `unsafe` blocks (151 lines) that enter the OS sandbox, machine-checked and audited. Shipped dependencies are `libc` and libcrux.
- **Verified where it matters:** the kernel's security policy and every parser
  of untrusted input carry machine-checked proofs (Verus, Kani).
- **Honest about it:** each crate declares its verification tier, and the
  trusted computing base is listed in [docs/VERIFICATION.md](docs/VERIFICATION.md).

Status: Phases 0 (foundations) and 1 (verified primitives) are complete:
UTF-8 (`clazel-encoding`), percent-encoding (`clazel-percent`), forgiving
base64 (`clazel-base64`), MIME types and sniffing (`clazel-mime`), IDNA
(`clazel-idna`) and URLs (`clazel-url`) are at Tier 2, on macOS and on
Linux CI. Phase 2 (kernel and IPC) is complete; see
[docs/STATUS.md](docs/STATUS.md) and
[docs/phases/phase-2.md](docs/phases/phase-2.md). Phase 3 (networking) is
in progress. HTTP/1.1 field syntax, response framing and request
serialization (`clazel-http`), DNS (`clazel-dns`), the fetch client with
redirects and cookies (`clazel-fetch`), DER (`clazel-der`) and RSA PKCS#1
v1.5 verification (`clazel-pkcs1`) are at Tier 2. The kernel
(`clazel-kernel`, still Tier 2) runs the fetch client itself: connections are
kernel state, every request, redirect and cookie is its decision, and its
Phase 2 theorems still hold with network events. The network shell
(`clazel-net`) only carries bytes. TLS is not done yet: X.509, the TLS 1.3
handshake and the libcrux join are partly built at Tier 0; `clazel fetch`
uses them for `https://`, but certificate chains with a P-384 issuer key
are refused for now, so most sites fail, and they are not yet joined to the
kernel, so `clazel browse` speaks only `http://`. What
remains is listed in [docs/phases/phase-3.md](docs/phases/phase-3.md#status).

Phase 4 (HTML and DOM) is built but not yet complete: every CI job but
Miri passed at `e29265d`, and `clazel-dom` is not at Tier 2 yet. `cargo run -p clazel -- browse URL`
is a text-mode browser in the style of Lynx: the kernel fetches the page,
a sandboxed renderer parses it and prints the title, the text and numbered
links, and typing a link's number navigates the tab through the kernel,
under an address line that is always the kernel's committed URL. Every
parser on the page's path is proven: the encoding sniffing algorithm
(`clazel-html`) and the decoders (`clazel-encoding`), the tokenizer, proven
total and panic-free, with its character references (`clazel-html`), and
the tree builder (`clazel-treebuilder`), all at Tier 2. The DOM operations
(`clazel-dom`) are proven too, but the crate stays at Tier 0 until it has a
conformance test of its own. The kernel proves that what a renderer
displays is shown for its own tab, labelled with the URL the kernel
committed there (`theorem_show_only_own_tab`,
`theorem_address_bar_integrity`), and that a renderer receives the fetched
body whole (`theorem_body_is_the_response`). The text layout (`clazel-text`)
and the renderer's glue are Tier 0. Pages in the seven legacy multi-byte
encodings (Shift_JIS, GBK, Big5 and others) are not rendered yet: the page
says "encoding `<name>` is not supported" (moved to Phase 8). See
[docs/phases/phase-4.md](docs/phases/phase-4.md#status).

Recheck every proof yourself, on Linux x86-64, with:

```sh
docker build --platform linux/amd64 -t clazel-verify .
docker run --rm --platform linux/amd64 clazel-verify
```

See [docs/ROADMAP.md](docs/ROADMAP.md).

## Verification status

[![Verification status: crates proven correct, proof obligations, mutants caught, conformance cases, unsafe blocks and axioms, and each component's crates by tier](docs/status.svg)](docs/STATUS.md)

Every crate, where it runs and the full table, with every conformance suite:
[docs/STATUS.md](docs/STATUS.md). CI redraws both after every push to
`main` whose full verification passes, so they can lag behind `main`.


**Phase 2 process tests: where they have run.** The demo (`cargo run -p clazel
-- demo`), the sandbox escape attempts, the hostile-renderer test and the WPT
`cookies/` run through real processes (item 2.16) run in CI on Linux x86-64
(`ubuntu-24.04`) and on macOS arm64. On Ubuntu the renderer needs an AppArmor
profile that allows unprivileged user namespaces, or it fails closed; CI loads
it, and so does the release tarball's `install.sh` (see item 2.16 in
[docs/phases/phase-2.md](docs/phases/phase-2.md)). The escape attempts include
`fork` and `ptrace` of a sibling. Where Yama restricts `ptrace` on Linux, the
`ptrace` result shows less than it does on macOS.

**Phase 4 process tests: where they have run.** `crates/clazel/tests/pages.rs`
(the 1,761 html5lib document cases and a page with links, visited through
real renderers, and the WPT `cookies/` rows through the kernel's
`Set-Cookie` path) and `crates/clazel/tests/hostile_pages.rs` (12 hostile
pages, each through a real sandboxed renderer, checked for panics, the
memory bound and the address line) run in CI's base jobs on Linux x86-64
(`ubuntu-24.04`) and macOS arm64, as do the Phase 2 tests, and passed there
at `e29265d`; they are Unix only, so not on Windows. Two hostile pages are ignored for time, not for
failure: a million nested `<div>`s and 64 MiB of `&amp;` (see item 4.16 in
[docs/phases/phase-4.md](docs/phases/phase-4.md)). The `browse` demo on
real sites runs locally only, since CI has no Internet.

Formalizing the standards has already found one spec bug: see
[docs/ERRATA.md](docs/ERRATA.md).

## Building

```sh
scripts/setup.sh         # install the pinned, checksummed toolchain (needs rustup)
scripts/verify.sh        # every check, fresh proof runs (same as `cargo xtask verify`; CI runs this)
cargo xtask verify --changed   # every check, but proofs and tests only for crates changed since origin/main
cargo xtask check        # fast static checks only
```

The command-line browser, `clazel`, and the sandboxed renderer it starts for
each tab:

```sh
cargo build --release --bin clazel --bin clazel-renderer   # both land in target/release/
target/release/clazel fetch http://example.com/           # GET, redirects followed, response printed
```

`fetch` resolves the host with our own DNS client and drives the proven fetch
client: it builds each request, frames each response with the proven HTTP/1.1
parser, follows redirects and keeps the cookies they set for the rest of the
run. It needs the Internet. An `https://` URL goes over our TLS 1.3 client
with Mozilla's roots as the trust store; until P-384 issuer keys are
supported, a chain that has one (most sites today) fails with `unknown_ca`.

```sh
target/release/clazel browse http://info.cern.ch/         # text-mode browser: title, text, numbered links
```

`browse` shows a page as text, with its links numbered: type a number to
follow a link, `g URL` to go elsewhere, `b` to go back, `q` to quit. The
kernel fetches every page and the page is parsed in a sandboxed renderer,
one per origin; the address line is the kernel's, whatever the page says.
It speaks only `http://` until TLS is joined to the kernel.

Each GitHub release has a Linux x86-64 tarball with both binaries and an
installer: unpack it and run `sudo ./install.sh` (or `PREFIX=... ./install.sh`).
On Ubuntu 23.10 and later, which restrict unprivileged user namespaces, the
installer also adds an AppArmor profile that lets `clazel-renderer` create the
one its sandbox needs, and nothing else; without it the renderer refuses to
start, by design. Built from source, run the same script once:

```sh
sudo packaging/apparmor/allow-userns.sh clazel-renderer "$PWD/target/release/clazel-renderer"
```

## How to get involved

The code is written by AI agents under rules ([CLAUDE.md](CLAUDE.md)) designed
so that nobody has to trust them. That leaves a lot of useful work for people,
and much of it is work only a person can do.

- **Check our work.** Rerun every proof on your own machine with the Docker
  command above, or `scripts/verify.sh`. If anything does not match the
  [verification status](#verification-status) table, open an issue: a claim
  nobody can reproduce is a bug.
- **Review a spec against its standard.** Each `spec.rs` transcribes a
  standard step by step, with its modelling choices listed at the top
  ([docs/SPEC-STYLE.md](docs/SPEC-STYLE.md)). Reviews gate nothing, and only
  people may record one, so a reviewed file means a person read it. See
  [docs/SPEC-REVIEWS.md](docs/SPEC-REVIEWS.md) for how. `contract.rs` files are
  the shortest route to what each crate actually promises.
- **Take errata upstream.** Formalising the standards has found places where
  they are wrong as written. Agents never file issues with standards bodies;
  the entries marked "Reported upstream: not yet" in
  [docs/ERRATA.md](docs/ERRATA.md) are waiting for a person to check them and
  report them.
- **Try to break it.** Feed the parsers hostile input, look for a spec bug the
  proofs would not catch (each crate's `mutations.json` lists the known gaps,
  marked `survives`), or close one of those gaps with a lemma or a Kani
  harness.
- **Add test suites.** Every Tier 2 crate is tested against official suites
  and independent engines (`tests/conformance*.rs`). Point us at suites we have
  not vendored, or at engines worth differential testing against.
- **Run it where we have not.** The Phase 2 and 4 process tests (the sandbox,
  the hostile renderer, the hostile pages) run in CI on `ubuntu-24.04` and
  macOS arm64 only. Other Linux distributions and kernels are untested.
- **Read `clazel-sys`.** It is the only crate with `unsafe`: 43 blocks that
  enter the OS sandbox, read the OS random source or list the DNS servers
  (Windows). Every change is audited
  by a second model ([docs/SYS-AUDITS.md](docs/SYS-AUDITS.md)); a person
  reading it too is welcome.
- **Build the next phases.** The plan is in [docs/ROADMAP.md](docs/ROADMAP.md)
  and the detailed plans in [docs/phases/](docs/phases/). TLS is partly
  built and not yet joined to the kernel. Contributions go through the same
  machine checks as everything else, whoever (or whatever) wrote them: read
  [CLAUDE.md](CLAUDE.md) first, and expect `cargo xtask verify --changed` and
  CI's full verification to be the bar.

## License

MIT. See [LICENSE](LICENSE).
