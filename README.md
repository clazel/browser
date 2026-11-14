# Clazel

A web browser built from the bottom up by AI, using formal verification
instead of trust.

- **Memory safe:** 100% safe Rust except `clazel-sys`: 138 `unsafe` blocks (338 lines) that enter the OS sandbox, machine-checked and audited. Of those, 21 are `"C-unwind"` casts of `objc_msgSend` to a typed function pointer, one per Objective-C message signature that Metal drawing uses. Shipped dependencies are `libc` and libcrux.
- **Verified where it matters:** the kernel's security policy and every parser
  of untrusted input carry machine-checked proofs (Verus, Kani).
- **Honest about it:** each crate declares its verification tier, and the
  trusted computing base is listed in [docs/VERIFICATION.md](docs/VERIFICATION.md).


Recheck every proof yourself, on Linux x86-64, with:

```sh
docker build --platform linux/amd64 -t clazel-verify .
docker run --rm --platform linux/amd64 clazel-verify
```

## Verification status

[![Verification status: crates proven correct, proof obligations, mutants caught, conformance cases, unsafe blocks and axioms, and each component's crates by tier](docs/status.svg)](docs/STATUS.md)

Every crate, where it runs and the full table, with every conformance suite:
[docs/STATUS.md](docs/STATUS.md). CI redraws both after every push to
`main` whose full verification passes, so they can lag behind `main`.

## What it does today

- **Fetches.** `clazel fetch URL` is a `curl` clone over `http:` and
  `https:`, on our own DNS client, HTTP/1.1 parser and TLS 1.3 client, with
  redirects and cookies.
- **Browses, as text.** `clazel browse URL` shows a page in the style of
  Lynx: the title, the text and numbered links. Pages in the seven legacy
  multi-byte encodings (Shift_JIS, GBK, Big5 and others) are not rendered
  yet: the page says "encoding `<name>` is not supported".
- **Not yet:** pages drawn in a window, images, forms and JavaScript. The
  crates for CSS, layout, fonts, GPU drawing and the window are on `main`,
  but `browse` does not use them yet.

What comes next, and in what order, is in [docs/ROADMAP.md](docs/ROADMAP.md).

## How it is put together

Clazel runs as several processes, and the one that makes the security
decisions is the one that is proven.

- **The kernel** (`clazel-kernel`) is a proven state machine. Tabs, origins,
  connections, cookies and storage are its state, and every navigation,
  request, redirect and cookie is its decision. Its theorems say, among other
  things, that what a renderer displays is shown for its own tab, under the
  URL the kernel committed there (`theorem_show_only_own_tab`,
  `theorem_address_bar_integrity`), and that a renderer receives the fetched
  body whole (`theorem_body_is_the_response`).
- **Renderers** (`clazel-renderer`) parse and lay out pages, one process per
  origin, inside the OS sandbox: namespaces, seccomp and Landlock on Linux,
  Seatbelt on macOS, an AppContainer on Windows. A renderer talks only to the
  kernel, over a proven message codec (`clazel-ipc`).
- **Parsers of untrusted bytes are ours**, and each is proven against a
  transcription of its standard: URLs, encodings, HTTP, DNS, cookies, HTML
  tokenizing and tree building, certificates and more.
- **Shells carry bytes.** The host (`clazel`), the network shell
  (`clazel-net`) and the store's shell (`clazel-store-shell`) do the I/O and
  make no protocol decisions: those belong to the proven crates they call.
- **`clazel-sys`** holds every `unsafe` block: single calls into the OS,
  with no policy of their own.

## How it is verified

Each crate declares a tier in its `Cargo.toml`, and
`cargo xtask verify` rejects a claim that is not backed:

| Tier | Guarantee | Checked by |
|------|-----------|------------|
| 0 | Memory safe | Safe Rust, Miri, deny-lints |
| 1 | Never panics on any input | Kani harnesses |
| 2 | Functionally correct against an executable spec | Verus proofs |

A proof only shows that code matches its spec. That the spec matches the
standard is shown by evidence that machines check too: official test suites
(Web Platform Tests, html5lib-tests and others) run through the proven code,
differential tests against independent engines, deliberately broken specs
that a theorem must reject, and a second, independent transcription proven
equivalent to the first. No step depends on a person approving something.
The policy, the tools and the trusted computing base are in
[docs/VERIFICATION.md](docs/VERIFICATION.md).

Formalising the standards has found places where they are wrong as written:
see [docs/ERRATA.md](docs/ERRATA.md).

**Where it has run.** CI builds and tests on Linux x86-64 (`ubuntu-24.04`),
macOS arm64 and Windows, and runs the proofs on Linux. The tests that start
real sandboxed processes (the sandbox escape attempts, hostile renderers and
hostile pages) run on Linux and macOS; they are Unix only. On Ubuntu the
renderer needs an AppArmor profile that allows unprivileged user namespaces,
or it fails closed (see [Building](#building)). Where Yama restricts `ptrace`
on Linux, the `ptrace` escape attempt shows less than it does on macOS. The
`browse` demo on real sites runs locally only, since CI has no Internet.

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
with Mozilla's roots as the trust store.

```sh
target/release/clazel browse http://info.cern.ch/         # text-mode browser: title, text, numbered links
```

`browse` shows a page as text, with its links numbered: type a number to
follow a link, `g URL` to go elsewhere, `b` to go back, `q` to quit. The
kernel fetches every page and the page is parsed in a sandboxed renderer,
one per origin; the address line is the kernel's, whatever the page says.

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
- **Take errata upstream.** Agents never file issues with standards bodies;
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
- **Run it where we have not.** The tests that start real sandboxed
  processes run in CI on `ubuntu-24.04` and macOS arm64 only. Other Linux
  distributions and kernels are untested.
- **Read `clazel-sys`.** It is the only crate with `unsafe`. Every change is
  audited by a second model ([docs/SYS-AUDITS.md](docs/SYS-AUDITS.md)); a
  person reading it too is welcome.
- **Build what is missing.** The plan is in [docs/ROADMAP.md](docs/ROADMAP.md),
  and crates below their target tier are listed in
  [docs/STATUS.md](docs/STATUS.md). Contributions go through the same machine
  checks as everything else, whoever (or whatever) wrote them: read
  [CLAUDE.md](CLAUDE.md) first, and expect `cargo xtask verify --changed` and
  CI's full verification to be the bar.

## License

MIT. See [LICENSE](LICENSE).
