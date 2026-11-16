# Phase 7: JavaScript, detailed plan

**Status: proposed (2026-11-16). Nothing is built. The decisions in item 7.0
are open.** The JIT half of this phase is planned in [jit.md](jit.md), whose
decisions (J.0) were taken on 2026-11-16. This file plans the rest and fixes
the shapes jit.md's item J.1 asks of it.

**Goal:** pages run their scripts. A `<script>` the tree builder reaches is
fetched through the kernel, parsed, compiled to bytecode and run:
- in the interpreter loop while it is cold, and as machine code from the
  baseline JIT once it is warm;
- against a DOM, events, timers and the network APIs that common sites use.

The heap is an index-based arena, so every JS object, string and DOM
wrapper lives in safe Rust; the only memory a script's machine code can
reach is the regions jit.md's validator proves it stays inside. The kernel
learns the new things a script can ask for: fetching scripts, `fetch()` and
`XMLHttpRequest`, changing its own URL with `history.pushState`, and opening
a window. Each gets a theorem, so a script can do no more through the kernel
than the page could already do.

*Exit:* on Windows x86-64, Linux x86-64 and macOS arm64, `cargo run -p
clazel -- browse URL` runs the scripts of 7.20's fixture sites, with every
parser on the path at its target tier:
- **Hacker News** with `hn.js`: comments collapse and expand;
- **TodoMVC**, in its vanilla, React and Vue versions: add, complete,
  filter and delete items;
- **a Wikipedia article.**

Test262 and the listed WPT directories give the results 7.1 records, with
every failure listed by name and reason, and give the same results with the
JIT off, on and forced on.

**Not in this phase:**
- Web Workers, `SharedArrayBuffer` and `Atomics` (the renderer is
  single-threaded, 7.0(e)).
- `Intl` beyond the fallback 7.0(b) lists.
- Temporal.
- Cross-site iframes and `postMessage` between sites (7.0(d)).
- Service workers, IndexedDB, WebSockets, WebRTC, the Cache API.
- Canvas, which needs Phase 8's drawing breadth.

Forms are Phase 6. Their script-visible parts (`HTMLFormElement`,
`HTMLInputElement.value`, the `submit` event) join 7.13 when Phase 6 has
built forms; until then those interfaces are listed as absent.

A convention for this file, as in phase-5.md: a section number marked † was
written from memory, not read at a pinned commit. It must be checked against
the commit a spec header pins before that header cites it. Every ECMA-262
number here carries the mark, because the edition is pinned only in 7.1.

## Exit criteria

Phase 7 is done when all of these hold on Windows x86-64, Linux x86-64 and
macOS arm64. Verus, Kani and Miri run on Linux, as CI does.

1. **Tiers**, as 7.0(a) decides them and `cargo xtask check` accepts.
   - Recommended:
     - `clazel-js-lexer` and `clazel-json` at **tier 2**;
     - `clazel-js-syntax`, `clazel-js-regexp` and `clazel-js-number` at
       **tier 1**;
     - `clazel-js-vm`'s bytecode semantics as a Verus spec, with the
       crate at tier 0 and that spec in place for jit.md;
     - `clazel-js-heap` at **tier 1**;
     - `clazel-dom` still at **tier 2**, with every operation 7.13 adds;
     - `clazel-ipc` and `clazel-kernel` at **tier 2**, with 7.16's schema
       and theorems.
   - jit.md's exit criteria hold for its crates.
2. **Suites**, vendored at pinned commits and run through the shipped code,
   each printing its `clazel-conformance:` line with every expected failure
   listed by name and reason:
   - **Test262** for the language and built-ins in 7.0(b)'s scope;
   - **WPT testharness.js tests**, run by our engine:
     - `dom/nodes/`, `dom/events/`, `dom/collections/`;
     - `html/webappapis/timers/`, `html/webappapis/microtask-queuing/`,
       `html/semantics/scripting-1/` (a listed subset);
     - `fetch/api/basic/`, `fetch/api/cors/`, `xhr/` (listed subsets);
     - `url/` through the `URL` API (`clazel-url`'s setters, waiting since
       Phase 1);
     - `cookies/` and `webstorage/` as real scripts, replacing the Phase 2
       line format (7.17);
   - **html5lib tree-construction** with the scripting flag on (the
     `#script-on` cases).

   The JIT runs are part of this criterion (jit.md, exit criterion 4).
3. **Demo.** 7.20's fixtures behave as the exit paragraph says, run from an
   in-process server in CI and locally against the live sites, whose
   results are reported, not asserted.
4. **Kernel theorems** (7.16):
   - `theorem_script_fetch_shape` (5.19's sub-fetch rule, for scripts);
   - `theorem_cors_read` (a renderer receives the body of a cross-origin
     response only if the CORS check passed, or the request was no-cors and
     opaque-response blocking let it through);
   - `theorem_forbidden_headers` (no header a renderer supplied that Fetch
     forbids, `Cookie`, `Origin` and `Host` among them, ever leaves the
     kernel);
   - `theorem_url_update_same_origin` (`pushState` and `replaceState`
     change a tab's committed URL only to a URL with the same origin, so
     the address bar still names the document's origin);
   - `theorem_popup_needs_input` (a renderer opens a new tab only within a
     stated window after the kernel delivered it a user input);
   - the Phase 2 to 5 theorems, restated over the new messages and outputs.
5. **Hostile pages** (7.19) never panic a renderer, exceed its memory bound,
   or change what the host draws outside the content area. They include
   endless loops, deep recursion, catastrophic regular expressions, a
   gigabyte string, deeply nested source and JSON, and a flood of timers
   and fetches. A renderer that stops responding is ended by the host, as
   7.0(g) decides.
6. **Miri:** every new `tests/conformance*.rs` runs a stated stride under
   Miri, sized to about a minute. No test takes 300 s of Miri's time or
   more.
7. `scripts/verify.sh` exits 0 and CI's full verification is green on the
   pull request that completes the phase.
   - VERIFICATION.md's "Tier 1 minimum" names the JS lexer, parser, RegExp
     and number parsers.
   - Its TCB gains what jit.md lists.
   - Every `clazel-sys` change has an audit row by another session.

## What is proven, and what is assumed

1. **Proven (Verus, tier 2):**
   - the JS lexer, as a total function over source text, against the
     lexical grammar (§12†), with the goal symbols (`InputElementDiv`,
     `InputElementRegExp` and the others) a parameter the parser supplies;
   - `JSON.parse`'s grammar and value construction (ECMA-404; ECMA-262
     §25.5.1†);
   - the new DOM operations (7.13), against DOM §4.2.3† and the rest of
     DOM §4.2†;
   - the kernel's new theorems (7.16);
   - jit.md's validators, IR and, where finished, its back ends and front
     end, all against the bytecode semantics (7.4).
2. **Proven free of panics and overflow (Kani, tier 1):**
   - the parser, early errors included;
   - the RegExp pattern parser and matcher;
   - StringToNumber, `Number.prototype.toString`, `toFixed`,
     `toPrecision` and `toExponential`;
   - the heap and collector (`clazel-js-heap`).

   Each harness covers every input up to a bound written in the harness
   and the crate's README. Correctness evidence for these is Test262 and
   the differentials.
3. **Specified but not proven:** the bytecode semantics (`clazel-js-vm`'s
   `spec fn step`) is a definition, not a theorem. It is the reference that
   jit.md's proofs refine. Whether bytecode compiled from a program means
   what ECMA-262 says the program means is evidence from Test262, not a
   proof. The README states that gap.
4. **Small and tested (Tier 0):**
   - the bytecode compiler;
   - the op handlers and the interpreter loop;
   - the built-ins;
   - the WebIDL bindings;
   - the event loop.

   It is all safe Rust, and Miri checks the dependency code its tests run.
   A bug here gives a page wrong answers or ends its renderer. It cannot
   reach another site's data, because the kernel decides everything that
   crosses a process boundary, and it cannot leave the arena regions.
5. **Not covered, and said so:**
   - **Spectre-style side channels** inside a renderer. The defence is one
     site per renderer, `SharedArrayBuffer` absent, and `performance.now()`
     coarsened to 100 µs.
   - **That sites work.** The fixtures and the WPT subsets are the
     evidence.
   - **Performance.**

## Crates

| Crate | Place | Target tier | What it holds |
|---|---|---|---|
| `clazel-js-lexer` | Renderer | 2 | Source text to tokens (§12†), goal symbol as input |
| `clazel-js-syntax` | Renderer | 1 | Parser to AST, early errors, Annex B syntax |
| `clazel-json` | Primitive | 2 | JSON text to values, and serialization's string quoting |
| `clazel-js-number` | Renderer | 1 | String ↔ Number and BigInt conversions |
| `clazel-js-regexp` | Renderer | 1 | Pattern parser, matcher, Unicode tables |
| `clazel-js-heap` | Renderer | 1 | Values (NaN-boxed), arena, shapes, strings, the collector |
| `clazel-js-vm` | Renderer | 0 (spec at 2) | Bytecode, `spec fn step`, compiler, op handlers, interpreter loop |
| `clazel-js-builtins` | Renderer | 0 | The global object's built-ins (§19† to §28†) |
| `clazel-webidl` | Renderer | 0 | Generated bindings, WebIDL conversions, `DOMException` |
| `clazel-web` | Renderer | 0 | Window, Document and Node APIs, events, timers, event loop, fetch and XHR APIs, storage, history |
| `clazel-dom` | Renderer | 2 | (existing) gains 7.13's operations |
| `clazel-kernel`, `clazel-ipc` | Kernel, Primitive | 2 | (existing) gain 7.16's messages and theorems |
| jit.md's crates | | | see jit.md |

`clazel-json` is a Primitive because the kernel and tools may parse JSON
too (import maps, later manifests). Each new crate joins `PLACES` in
`xtask/src/status.rs`.

## Dependencies on other phases

- **Phase 4** (built): the tree builder's `ScriptReady` action, the wrapper
  slot on every node, and node ids that stay valid after `remove`. This
  plan uses all three as Phase 4 designed them, so the tree builder's proof
  is not redone.
- **Phase 5** (planned, not started):
  - the window, `Input` (5.18) and the frame pipeline, for events and
    `requestAnimationFrame`;
  - `clazel-style`'s side table, for `getComputedStyle`;
  - `clazel-selectors`, for `querySelector`;
  - 5.19's sub-fetch request shape and its credentials rule (5.0(h) F1),
    for scripts.
- **Phase 6** (not planned): forms and images. Their script interfaces wait
  for it.
- **Phase 3:** TLS in the kernel, for the live-site runs.

7.2 to 7.12 and jit.md's J.2 to J.6 depend on none of Phases 5 and 6, so
the engine is built while those phases are. 7.13 to 7.17 and 7.20 need
Phase 5's window and input.

## Shapes fixed here for the JIT (jit.md J.1)

- **The bytecode semantics is a `spec fn step`** (7.4), written and committed
  before the handlers (rule 3).
- **Register-based bytecode.** Each frame is a window of `u64` slots in one
  value-stack region: header slots (callee, `this`, the argument count,
  the return address), then arguments, then registers. The interpreter and
  the JIT read and write the same slots.
- **Values are NaN-boxed `u64`s.**
  - A double is itself, with NaN canonicalized.
  - Other values (undefined, null, booleans, int32, heap references) are
    in the NaN space, with a tag.
  - A heap reference is a `u32` arena index plus a `u16` generation (7.6),
    so a stale reference is caught as a defined error, never a silent
    alias.
- **Inline caches are data:** a (shape id, slot index) table per site, in a
  region the code reads.
- **Every op that can allocate, call out, or throw is distinguished**, and is
  an exit in the JIT and a handler call in the interpreter. Handlers are
  plain Rust functions over the frame region and the heap, shared by both.
- **JS-to-JS calls push frames in the region.** The native stack depth of
  the engine is bounded by the number of nested native calls (a built-in
  calling back into JS, such as `Array.prototype.map`), which is counted
  and limited (7.19).

## Work items

Ordered by dependency. Sizes as in earlier plans: S under a day, M a few
days, L a week or more.

### 7.0 Decisions for the maintainer (S): open

**(a) Tiers.** VERIFICATION.md requires at least tier 1 for "JS lexer and
parser", and tier 0 for the interpreter.
- **A: tier 2 for the lexer, parser, RegExp and JSON.**
  - Every parser so far went to tier 2.
  - **Cost:** the JS grammar has parameterized productions (`[Yield, Await,
    In, Return]`), cover grammars, automatic semicolon insertion and
    several hundred early errors. RegExp has its own grammar and
    Annex B's. Each needs a spec, a proof, a second transcription and
    certified mutations: several L items more than any parser so far.
- **B: tier 1 for all four**, the policy's minimum.
- **C: tier 2 for the lexer and JSON, tier 1 for the parser, RegExp and
  numbers.**
  - The lexer is a state machine with a goal symbol, the shape tier 2 has
    handled before; JSON is a small grammar.
  - The parser's attack surface is panics and resource use, which Kani's
    tier 1 covers. Its correctness evidence is Test262's roughly 20,000
    syntax tests, many of them negative, plus differentials.

**Recommendation: C**, with the parser's `target-tier` left at 1 and tier 2
for it a Phase 8 decision. VERIFICATION.md's "Tier 2 required" gains "the JS
lexer and JSON" if C or A is taken.

**(b) Language scope.** The ECMA-262 edition pinned in 7.1, with Annex B
(sites depend on it), modules, generators, async functions, classes with
private fields, Proxy and Reflect, typed arrays, BigInt, `WeakRef` and
`FinalizationRegistry`.
- **Left out, and listed:**
  - `SharedArrayBuffer` and `Atomics`: no threads, and no cross-origin
    isolation;
  - Temporal;
  - ECMA-402 (`Intl`).
- **Fallbacks:**
  - `toLocaleString` and friends give the `en-US` form.
  - `Date` uses the time zone offset the host passes at spawn, a fixed
    offset for the renderer's life with no daylight-saving rules. A date
    on the other side of a daylight-saving change from now is off by an
    hour, and that is listed.

**Recommendation:** this scope. `Intl` and real time zones are Phase 8: they
need CLDR and tzdb data, read by our own parsers.

**(c) The kernel's rule for script-initiated fetches.**
- **S1: 5.0(h)'s F1 for every sub-fetch**, scripts and `fetch()` and XHR
  alike:
  - same-origin requests carry cookies;
  - cross-origin requests carry none;
  - CORS is checked in the kernel, preflights included;
  - no-cors responses pass opaque-response blocking (ORB) before a renderer
    sees them.

  This matches Fetch's defaults (`credentials: "same-origin"`, and
  `withCredentials` false). A cross-origin `credentials: "include"` request
  is sent without cookies, a listed deviation that keeps
  `theorem_cookie_noninterference` as stated.
- **S2: S1 plus credentialed CORS.** Here another site's cookies may
  produce a response a renderer reads, when that site answers with
  `Access-Control-Allow-Credentials: true`. The noninterference theorem
  then needs a declassification: a site's data reaches another site's
  renderer only with that site's consent, stated per response.

**Recommendation: S1.** S2 is a theorem change of its own, and fits Phase
8's third-party cookie work.

**(d) Frames.** 5.24 designed out-of-process iframes and left building them
to this phase.
- **O1: build 5.24 here**, and add `postMessage` relayed by the kernel,
  which stamps the sender's origin, plus same-origin frames scripted
  in-process.
- **O2: no frames in this phase.** An `iframe` is an empty box of its
  attribute size, `contentWindow` is `null`, and `postMessage` to another
  window does nothing.

Embeds and ads then show blank, and the fixture sites do not need frames.
**Recommendation: O2,** with 5.24 and `postMessage` the first item of Phase
8. O1 is as large as 5.18 again, and the exit does not need it.

**(e) Workers.**
- **W1: none.** `Worker` is not defined, which sites feature-detect.
- **W2: a dedicated worker as another sandboxed renderer process**, talking
  through the kernel.

**Recommendation: W1** in this phase. W2 is the design for Phase 8: it
keeps the renderer single-threaded and the seccomp list without `clone`.

**(f) The collector.**
- **G1: stop-the-world mark and sweep**, non-moving.
  - Free slots are reused, and every arena slot has a generation that is
    bumped on reuse, so a stale index is a caught error.
  - Roots are:
    - the value-stack region;
    - the handles the bindings and built-ins hold (a scoped handle stack,
      checked on scope exit);
    - every DOM node in a document's tree, whose wrapper is marked
      (Phase 4's wrapper slot);
    - the job and task queues.

  A removed DOM node is freed when nothing marks it, as Phase 4 planned.
- **G2: generational or incremental.** It has shorter pauses, but write
  barriers in every store, including the JIT's templates, and a larger
  proof.

**Recommendation: G1**, at tier 1. The pause is measured on the fixtures,
and G2 is a Phase 8 decision if the pause matters.

**(g) A script that never yields.**
- **Recommendation:** if a renderer has not returned to its event loop for
  10 seconds while it has a visible tab, the host offers to end it, and
  ends it on the user's word. The tab shows the kernel's "this page stopped
  responding" notice.
- The renderer needs no interrupt check, because the host's kill is
  enough.
- The alternative, an interrupt counter checked at loop back-edges in the
  interpreter and in JIT code, lets a page be stopped without losing the
  tab. It is a later addition that the shared frame layout permits.

### 7.1 Inventory and test data (M)

Pin and vendor, each with its `SOURCE.md` and checksum, through `cargo xtask
testdata`:
- **The language spec:** `tc39/ecma262` at the commit of the newest edition
  published by then.
- **Test262** at a commit matching that edition. The runner reads each
  test's frontmatter (`flags`, `features`, `negative`, `includes`), and
  every `features` tag outside 7.0(b)'s scope is an expected failure with
  that reason.
- **WPT** at a pinned commit, for the directories in exit criterion 2.
- **The WebIDL files:** from the WHATWG DOM, HTML, Fetch, XHR, URL and
  Storage standards, and the W3C UI Events and CSSOM specs, at pinned
  commits.
- **The Unicode Character Database files** RegExp needs, at the version
  `clazel-idna` already uses.
- **TodoMVC's vanilla, React and Vue implementations** (MIT), and a
  Wikipedia article's HTML, CSS and scripts with their licence (CC BY-SA
  for the text). Whether the Wikipedia fixture belongs in the repository is
  the maintainer's call; the alternative is a fixture written for this
  repository that uses the same APIs.
- **Independent engines for differentials** (test dependencies only):
  - Boa (Rust, crate) for the parser and built-ins;
  - QuickJS's or engine262's output, recorded as data files where a crate
    is not available.

Record the baseline 7.20 asserts: which Test262 and WPT tests pass, named.

### 7.2 Lexer: spec and contracts, then implementation (M, then M)

`clazel-js-lexer`.
- **Input:** source text as code points (§11.1†); the renderer decodes
  bytes to code points with the encodings Phase 4 built.
- **Output:** tokens with spans: identifiers with escapes resolved,
  reserved words, punctuators, numeric literals (with separators, BigInt
  suffix and legacy octal under Annex B), string literals (as UTF-16 code
  units, lone surrogates allowed), template parts, regular expression
  literals (body and flags, unparsed), comments, and the line-terminator
  flag ASI needs.
- **Goal symbol:** a parameter of each step, as the tree builder's mode is.
- **Proven:**
  - totality;
  - span coverage (the tokens and the skipped trivia are the input,
    concatenated);
  - agreement with the grammar transcribed in `spec.rs`;
  - an independent transcription, written from the grammar summary in
    Annex A†, proven equal.
- **Conformance:** Test262's lexical tests, through the parser.

### 7.3 Parser and early errors (L)

`clazel-js-syntax`.
- **Approach:** recursive descent over the lexer, with:
  - the parameterized productions as flags;
  - cover grammars, reparsed as the spec says (§13.2.5.1† and friends);
  - ASI (§12.10†);
  - early errors (every "It is a Syntax Error if" rule, each cited);
  - Annex B's syntax (HTML-like comments, legacy octal, labelled function
    declarations).
- **Recursion:** depth is bounded by an explicit limit; deeper nesting is a
  `SyntaxError`, a listed deviation with its number.
- **Output:** an arena AST with spans.
- **Tier 1:** harnesses over every token sequence up to the stated length.
- **Conformance:** Test262's syntax tests, the negative ones included.
- **Differential:** Boa's parser, comparing accept/reject and the AST
  shape.

### 7.4 Bytecode and its semantics: spec first (M)

`clazel-js-vm`.
- **The instruction set:** moves between registers, constants, int32 and
  double arithmetic, comparisons, branches, property get and set (with an
  inline-cache index), element get and set, calls and returns, closures,
  environment access, iteration, generator suspend and resume, and throw.
- **`spec fn step(state, op) -> state`** over an abstract machine:
  - the frame region, the program counter and the heap as an abstract map;
  - the core ops given in full;
  - each op that calls a handler specified as calling an uninterpreted
    `handler_k`, whose behaviour Test262 is evidence for.

  This is what jit.md's front-end proofs refine.
- **Commit:** the spec and the op list together, before any handler or
  compiler code (rule 3).

### 7.5 Values, strings, shapes (L)

`clazel-js-heap`.
- **Values:** the NaN-boxing of "Shapes fixed here".
- **Strings:** UTF-16 code unit sequences, stored as Latin-1 when every
  unit is under 256. Interned property keys. Ropes are a later
  optimization, measured first.
- **Shapes:** hidden classes with transitions, so inline caches have a key;
  dictionary mode past a stated property count.
- **Elements:** dense `u64` arrays, falling back to sparse.
- **The rest:** symbols, and BigInt as our own arbitrary-precision
  integers.
- **Tier 1:** harnesses for the arena's invariants (no slot is both free
  and live, and generations only grow) over all heaps up to a bound.

### 7.6 The collector (M)

As 7.0(f) decides.
- **What it handles:** ephemerons for `WeakMap` and `WeakSet`, `WeakRef`,
  and `FinalizationRegistry` callbacks queued as tasks.
- **When it runs:** only between ops, which with exit-based JIT code means
  only in Rust, at a known point (jit.md's exits).
- **Proven (tier 1):** a slot reachable from the roots is never freed, for
  every heap up to the bound. The same property is a property test over
  random heaps of any size.
- **Measured:** pause times on the fixtures.

### 7.7 Compiler: AST to bytecode (L)

- **Scope analysis.** Variables that are never captured live in registers;
  captured ones live in environment objects.
- **Language features compiled:**
  - TDZ checks, destructuring, spread, classes, private names,
    `super`, optional chaining, templates and tagged templates;
  - generators and async functions, whose frames are copied to a heap
    object on suspend and back on resume;
  - `with` and sloppy direct `eval` under Annex B, which force
    environment objects.
- **Each op is emitted with a source span,** for stack traces and errors.
- **Tier 0.** The evidence is Test262, plus a differential against Boa on
  generated programs.

### 7.8 Op handlers and the interpreter loop (M)

- **Handlers:** one per handler op, as plain functions over the frame
  region and the heap, shared with jit.md's exits.
- **The interpreter loop:** fetches, decodes and runs ops; counts function
  entries and loop back-edges for jit.md's tiering; and runs the JIT-off
  mode.
- **Exceptions:** unwinding through frame headers, in the region.

### 7.9 Built-ins (L, several)

`clazel-js-builtins`, in pull requests by group:
- `Object`, `Function`, `Error`s, `Symbol`, `Boolean`, iteration;
- `Array` and its iterators;
- `String` (with `normalize` reusing `clazel-idna`'s NFC and adding NFD and
  the K forms from the same data);
- `Number`, `Math`, `BigInt`;
- `JSON` (7.11);
- `Map`, `Set`, `WeakMap`, `WeakSet`, `WeakRef`, `FinalizationRegistry`;
- `Promise` and the job queue;
- `Proxy`, `Reflect`;
- `ArrayBuffer`, typed arrays, `DataView`;
- `Date` (7.0(b));
- `RegExp`'s object half (7.10);
- `globalThis`;
- the Annex B built-ins.

Each group lands with its Test262 directory's results recorded.

### 7.10 RegExp (L)

`clazel-js-regexp`.
- **The pattern parser:** §22.2.1†, with Annex B §B.1.2† and the `u` and
  `v` flags.
- **The matcher:** a backtracking implementation of §22.2.2†'s matcher
  semantics, with:
  - an explicit backtrack stack in the heap, not recursion;
  - case folding and property tables generated from the UCD by `cargo
    xtask tables`, as IDNA's are.
- **Tier 1** for both.
- **Catastrophic patterns** run until 7.0(g)'s host limit, as other engines
  do, but the backtrack stack's memory is bounded. Exceeding it throws a
  `RangeError`, a listed deviation.

### 7.11 Numbers and JSON (M)

- **`clazel-js-number`** (tier 1):
  - StringToNumber (§7.1.4.1.1†), correctly rounded, with an
    Eisel–Lemire fast path and a big-integer fallback;
  - Number::toString's shortest round-trip digits (§6.1.6.1.20†), with a
    Ryū-style algorithm;
  - `toFixed`, `toPrecision`, `toExponential`;
  - BigInt parsing and printing.
  - **Differentials:** Rust's `f64` parsing and `Display` (both correctly
    rounded and shortest), exhaustively over every `f32` widened, and over
    random doubles.
- **`clazel-json`** (tier 2):
  - the grammar and value construction, proven against ECMA-404 and
    §25.5.1†;
  - an independent transcription from RFC 8259, proven equal;
  - `JSON.stringify`'s string quoting (§25.5.2.3† QuoteJSONString), proven;
  - the nesting depth bounded, with the excess a `SyntaxError` (listed).

### 7.12 WebIDL bindings (L)

- **The generator** is `cargo xtask bindings`. It reads 7.1's vendored IDL
  with our own IDL parser (tooling, so other crates are allowed, but ours
  is small) and writes Rust into `clazel-webidl`, checked in, with a
  staleness check as the generated tables have.
- **Conversions:** WebIDL §3.2† for every type the IDL uses.
- **Covered:** overload resolution, `[LegacyUnforgeable]`, `[Replaceable]`,
  `[SameObject]`, `[PutForwards]`, `[LegacyUnenumerableNamedProperties]`,
  and `DOMException`.
- **Wrappers:** one per platform object, created on first access and stored
  in Phase 4's wrapper slot for nodes, and in a side table for the others.

### 7.13 The DOM API (L)

`clazel-web`'s `Node`, `Element`, `Document`, `Text`, `Comment`,
`DocumentFragment`, `Attr`, `NodeList`, `HTMLCollection`, `DOMTokenList`,
`DOMStringMap`, `MutationObserver`, `Range` (a subset) and the HTML element
interfaces the fixtures use.
- **New `clazel-dom` operations, proven at tier 2** before the bindings use
  them: pre-insertion validity, `insert` with arbitrary arguments,
  `replace`, `replace_all`, `clone` (deep and shallow), `adopt`, and
  attribute changes.
  - Each is cited to DOM §4.2.3† and §4.9†, and proven to keep
    `clazel_dom::wf`.
  - The "insertion steps" and "removing steps" hooks Phase 4 named are
    added here, once, for mutation observers and live collections.
- **`innerHTML` and `outerHTML`:** the HTML fragment parsing algorithm
  (HTML §13.4†) through the tree builder Phase 4 built, and the HTML
  serialization algorithm (§13.3†).
- **`querySelector` and `matches`:** through `clazel-selectors` (Phase 5).
- **`getComputedStyle`:** reads `clazel-style`'s side table, and restyle
  and relayout follow mutations, the whole document at once as Phase 5
  does.

### 7.14 Events and input (M)

- **Dispatch:** DOM §2.9†, with the event path, capture, target and bubble
  phases, `stopPropagation`, `preventDefault` and passive listeners.
- **UI events:** from Phase 5's `Input`: mouse, keyboard, `input`, focus,
  `wheel` and `scroll`.
- **Default actions** run when the event was not cancelled: following a
  link (the existing `Navigate`) and, after Phase 6, submitting a form.
- **User activation** (HTML §6.4†) is tracked in the renderer for the APIs
  that read it. The kernel keeps its own record for 7.16's popup rule.

### 7.15 HTML integration (L)

- **The scripting flag is true** in the tree builder's driver, and the
  html5lib `#script-on` cases run.
- **"Prepare the script element"** (HTML §4.12.1.1†) acts on Phase 4's
  `ScriptReady`:
  - classic and module scripts;
  - inline and external scripts;
  - `async` and `defer`;
  - parser-blocking scripts, which pause the parser's driver;
  - `nomodule`;
  - `document.currentScript`.
- **`document.write` and `document.writeln`:** an edit of the input at the
  insertion point, as Phase 4's design says. `document.open` and
  `document.close` for the cases the WPT subset covers.
- **The event loop** (HTML §8.1.7†): task queues, the microtask checkpoint,
  timers (§8.6†, with clamping and nesting levels), `queueMicrotask`, and
  `requestAnimationFrame` in the rendering update.
- **`Window`, `Location`, `History` and `Navigator`** (a fixed, honest
  user-agent string).
  - `location.href = …` sends `Navigate`.
  - `pushState` and `replaceState` send 7.16's `UpdateUrl`.
- **`console`** writes to the host's log, never to the page.
- **`javascript:` URLs:**
  - from a link the page drew, the renderer runs them itself;
  - typed by the user, the kernel refuses them, as other browsers strip
    them from pasted text.
- **Module scripts:** fetch, link and evaluate (§16.2†), dynamic `import()`
  and top-level `await`. Import maps go to Phase 8.
- **`performance.now()`:** coarsened to 100 µs.

### 7.16 The kernel: scripts, `fetch()`, XHR, URL updates, popups (L)

New messages in `clazel-ipc`, each with its schema row:
- `FetchScript`, with 5.19's request shape, and its responses chunked like
  `Style*`;
- `Fetch` (method, URL, headers, body, mode, credentials, redirect mode),
  with responses chunked the same way, used by both `fetch()` and XHR;
- `UpdateUrl` (`pushState` and `replaceState`);
- `OpenTab`, for `window.open` and `target=_blank`.

In `clazel-kernel`:
- **Fetch §4.1† main fetch** for script-initiated requests, under 7.0(c)'s
  rule:
  - forbidden request headers (§2.2.2†) removed;
  - `Origin` and `Referer` set by the kernel from the tab's committed URL;
  - the CORS preflight (§4.8†) and CORS check (§4.9†);
  - redirects re-checked at every hop;
  - ORB on no-cors responses.

**Theorems, each with certified mutations:**
- `theorem_script_fetch_shape`;
- `theorem_cors_read`;
- `theorem_forbidden_headers`;
- `theorem_url_update_same_origin`;
- `theorem_popup_needs_input`, whose window is stated as a number of
  kernel steps after an `Input`, not wall time, so it is a property of the
  kernel's state;
- `theorem_cookie_noninterference` and `theorem_address_bar_integrity`,
  restated over the new messages.

The `document.cookie` and `localStorage` messages are Phase 2's, unchanged,
now sent by script.

### 7.17 The renderer pipeline, and retiring the line scripts (M)

`clazel-renderer` runs a document's scripts through 7.15, and the event loop
replaces the one-shot pipeline. Phase 2's kind 1 line format (`cookie-get`,
`storage-set`, and the rest) is deleted, with its parser, in the same pull
request that runs WPT's `cookies/` and `webstorage/` tests as real
testharness.js pages through the kernel. The kernel theorems about cookies
and storage do not change: their messages are the same.

### 7.18 The JIT

jit.md's items J.2 to J.12, scheduled as its "Order of work" says:
- J.3 to J.6 alongside 7.2 to 7.6;
- J.9 and J.10 after 7.4 and 7.8.

### 7.19 Limits and hostile pages (M)

- **Stated limits, each with its error:**
  - heap size per renderer (a `RangeError` on allocation past it, after a
    full collection);
  - value-stack region size (a `RangeError` for too much recursion);
  - nested native calls;
  - parser and JSON nesting depth;
  - the RegExp backtrack stack;
  - pending timers;
  - in-flight fetches per renderer, which the kernel also bounds.
- **Hostile pages:**
  - `while(true){}`;
  - unbounded recursion;
  - `(a+)+b` on a long input;
  - a 1 GiB string build;
  - 10⁶ nested arrays in source and in JSON;
  - 10⁶ timers;
  - 10⁴ concurrent fetches;
  - a `MutationObserver` that mutates in its callback;
  - a finalizer that resurrects.

  None may panic, cross a limit without its error, or affect another tab.

### 7.20 Exit demo and fixture sites (M)

The fixtures run in CI from an in-process server, on all three platforms:
- **HN and `hn.js`:** collapsing a comment hides its subtree, and the count
  label updates.
- **TodoMVC** in three frameworks: add three items, complete one, filter
  "Active", delete one. The DOM is checked after each step.
- **The Wikipedia article:** its scripts run without uncaught exceptions,
  and the table of contents collapses.

Each step is checked by the DOM and by 5.25's screenshot comparison. Live
runs against the real sites are local only, and reported.

### 7.21 Status and README (S)

- The README states:
  - what runs: the language scope and the APIs;
  - what is proven (the lexer, JSON, the DOM operations, the kernel
    theorems, the validators);
  - what is evidence only (the compiler, handlers, built-ins and
    bindings).
- VERIFICATION.md is updated as exit criterion 7 says.

## Order of work

7.0 → 7.1 → 7.2 → 7.3, with 7.4 (spec) in parallel → 7.5 → 7.6 → 7.7 →
7.8 → 7.9, 7.10 and 7.11 in parallel → 7.12 → 7.13 to 7.16 (after Phase 5's
window and input) → 7.17 → 7.19 → 7.20 → 7.21.

The JIT (7.18) follows jit.md:
- its instruction-set and validator items start with 7.2;
- its front end follows 7.4 and 7.8.

Nothing in 7.13 onwards waits on the JIT: the interpreter loop runs the
fixtures first.

## Risks

- **Size.** ECMA-262's built-ins and the web APIs are the largest body of
  code in the browser, and most of it is tier 0 with Test262 and WPT as the
  only evidence. The scope is bounded by 7.0(b) and by what the fixtures
  use, and every API outside that is listed as absent rather than
  half-built.
- **Speed of safe Rust.** The interpreter loop pays for bounds checks and
  has no computed goto. This is why the JIT is the main path, and why the
  loop is measured in 7.8 before tuning.
- **The collector's pauses** with a non-moving, stop-the-world design (G1).
  They are measured on the fixtures; G2 is the fallback, at a stated cost
  to the JIT's templates.
- **`step` drifting from the handlers.** The spec is a definition, so
  nothing stops a handler from disagreeing with it except tests: each core
  op's handler is checked against `step` on random states, as a
  differential, in 7.8.
- **Phase 5's slip delays the exit**, not the engine: 7.2 to 7.12 and the
  JIT need nothing from it.
- **Sites need what is left out:** frames, workers, `Intl`. The fixtures
  were chosen to need none of them; the live runs report what breaks, and
  Phase 8 takes them in that order.

## Looking ahead: Phase 8

- **Cross-site iframes and `postMessage`** (5.24's design).
- **Workers as processes** (7.0(e) W2).
- **`Intl` and time zones,** from our own CLDR and tzdb readers.
- **Credentialed CORS** with its declassification theorem (7.0(c) S2).
- **Import maps; IndexedDB and the Cache API** on 3.10's store.
- **An interrupt check** for stopping a script without ending the renderer.
- **The parser at tier 2,** if 7.0(a) left it at 1.
- **WebAssembly** on jit.md's back ends.
