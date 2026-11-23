# Phase 6: Images and forms, detailed plan

**Goal:** the renderer draws the images a page names and submits the forms
a user fills in. Image bytes are fetched by the kernel as sub-resources,
sniffed (MIME Sniffing §6.1, already proven in `clazel-mime`), and decoded
inside the renderer's sandbox by decoders of our own, written in the style of
WUFFS (resumable state machines over caller-owned buffers, no allocation
while decoding, every arithmetic step checked) and proven never to panic,
overflow or index out of bounds (tier 1). The decoded pixels reach the GPU
process through new display list items that `clazel-displaylist`'s proven
validator checks like every other item. Forms gain their controls (text
fields, checkboxes, radio buttons, selects, buttons, `textarea`), focus and
text editing, and HTML's form submission algorithm, which turns a form into a
`GET` or a `POST` navigation. The kernel learns to send a request with a
body, and proves that the body it sends is the one the renderer gave, sent
once, to the URL the renderer named, with cookies the method allows.

*Exit (6.0(g)):* `clazel https://news.ycombinator.com/` shows the front page **with its images**, and
the user can **log in, vote and post a comment** through HN's own forms,
with every decoder on that path at its target tier. In CI the same flow runs
against 6.20's fixture server, and every image format is checked against
reference decoders on the vendored suites.

Nothing in this phase runs a script, so a form whose submission needs
JavaScript (HN's search, which goes to a JavaScript site; any `onsubmit`)
does not work, and the README says so. Not in this phase: SVG images (unless
6.0(c) takes S2), AVIF, HEIC, JPEG XL, JPEG 2000, ICC colour management,
`<input type=file>`, `<dialog>`, form validation UI beyond refusing to
submit, autofill and password saving, `<canvas>`, video and audio.

A convention for this file, as in phase-5.md: a section number marked † was
written from the documents as remembered, not read at a pinned commit, and
must be checked against the commit a spec header pins before it is cited
there (SPEC-STYLE.md, "Pin the source"). RFC numbers and their section
numbers are fixed and unmarked; they too are checked before a spec header
cites them.

## Where Phase 5 left things

Phase 5 is built and on `main` (CI's full verification green at `72e11de`,
2026-11-15), with its tier raises still to come (ROADMAP.md). What this
phase builds on, as it is on `main`:

- **The window and the pipeline** (5.18 to 5.23): `clazel URL` opens a
  window, the renderer lays out and paints, the GPU process draws, and the
  kernel decides what is shown. `--headless OUT URL` writes a PNG, which is
  what CI's pixel checks read.
- **Replaced boxes** (5.13, `crates/clazel-layout/src/boxes/replaced.rs`):
  `img` sized from its attributes and drawn empty; `input` and `textarea`
  as empty bordered boxes of HTML's suggested size.
- **The display list** (5.17a, `crates/clazel-displaylist/src/spec.rs`):
  tags 1 to 6 (fills, clips, masks), with "Phase 6's image item is not
  here. It gets the next tag", so 6.10 takes tag 7 onward. The crate is at
  tier 0, target 2; 6.10's items join its spec before or after its tier
  raise, and either way its tier-2 evidence (independent transcription,
  certified mutations) must cover them.
- **Sub-resource fetches** (5.19): shipped as `FetchStyle` (tag 14) and
  `StyleResponse`, `StyleBody`, `StyleEnd`, `StyleFailed`, style sheets
  only (`crates/clazel-ipc/src/message/spec.rs`). 6.0(e) decides how images
  join.
- **Input** (5.18): `Input { kind, x, y, negative, delta, key }`, kind 0 a
  click, 1 a scroll, 2 a key code; the renderer does nothing with keys yet
  (`crates/clazel-renderer/src/lib.rs`, "A key: nothing in this phase").
  6.0(f) decides how typed text arrives.
- **`Display` (tag 10) and `clazel-text`** are still there, as `--text`,
  until Phase 5 deletes them (5.0(g)); this phase draws nothing through
  them.

So every item here can start now. Phase 5's open tier raises do not block
any of them: they need its crates' interfaces, not their tiers.

## Exit criteria

Phase 6 is done when all of these hold on macOS arm64, Linux x86-64 and
Windows x86-64 (Verus, Kani and Miri run on Linux, as CI does):

1. **Tiers**, as 6.0 decides them and `cargo xtask check` accepts:
   `clazel-deflate` at **tier 2** (6.0(a)); `clazel-png`, `clazel-jpeg`,
   `clazel-gif` and `clazel-webp` at **tier 1** (Kani harnesses over every
   state and input chunk up to the bounds their READMEs state);
   `clazel-displaylist` still at tier 2 with the image items;
   `clazel-forms` at tier 2 for the form data set and its encodings, its
   editing module at tier 0 (6.0(b)); `clazel-fetch`, `clazel-ipc` and
   `clazel-kernel` still at tier 2 with 6.16's and 6.17's theorems.
2. **Suites**, vendored at pinned commits, through the shipped code, each
   printing its `clazel-conformance:` line with every expected failure listed
   by name and reason: DEFLATE, zlib's and Wuffs' test streams plus a
   differential against `miniz_oxide`; PNG, PngSuite plus a differential
   against the `png` crate, exact; JPEG, the libjpeg-turbo test images and
   ITU-T T.83's† conformance streams against libjpeg-turbo's output within a
   stated per-sample tolerance (JPEG's IDCT is not exact, 6.5); GIF, Wuffs'
   GIF test data against the `gif` crate, exact; WebP, the libwebp test
   vectors against libwebp's output, exact for lossless and lossy (VP8 decoding
   is bit-exact by RFC 6386); WPT `html/semantics/forms/form-submission-0/`,
   `url/urlencoded-parser` and the `FormData`-free cases of
   `html/semantics/forms/` through 6.13 and 6.14; and WPT
   `html/semantics/embedded-content/the-img-element/` reftests that need no
   script, through 5.25's harness.
3. **Demo.** On `https://news.ycombinator.com/`, run locally: the logo and
   spacer images draw; logging in with a test account sets the session
   cookie; a vote link and a comment form work; the comment appears on the
   reloaded page. In CI, 6.20's fixture server does the same with a stored
   screenshot compared exactly. Posting on the real site is the maintainer's
   act, done by hand; no test posts there.
4. **Kernel theorems** (6.16, 6.17): `theorem_body_from_requester`,
   `theorem_body_sent_once`, `theorem_post_cookies` (3.6's
   `theorem_wire_cookies` over methods with a body),
   `theorem_redirect_method` (RFC 9110 §15.4's method and body rewriting),
   `theorem_orb` (a cross-origin `no-cors` response reaches a renderer only
   if Opaque Response Blocking allows it), and the Phase 2 to 5 theorems
   restated.
5. **Hostile inputs** (6.20): decompression bombs, malformed and truncated
   files of every format, images whose header claims 2^31 × 2^31 pixels, a
   million `img` elements naming one URL and a thousand naming different
   ones, a form with a million fields or a 1 GiB `textarea`, a form posting
   to another site, a redirect loop on `POST`: none panics a renderer,
   exceeds its memory bound or stated time, or sends a body the user did not
   submit.
6. **Miri:** every new suite runs a stated stride under Miri, about a minute
   each, nothing over 300 s.
7. `scripts/verify.sh` exits 0 and CI's full verification is green on the
   pull request that completes the phase.

## What is proven, and what is assumed

1. **Proven (Verus, tier 2):** DEFLATE and zlib decoding against RFC 1951
   and RFC 1950 transcribed (6.0(a)); the form data set, the
   `application/x-www-form-urlencoded` serializer and `multipart/form-data`
   encoding against HTML and URL (6.13, 6.14); the display list's image
   items (6.10); the request body path, the method rewriting on redirect,
   ORB and the sub-resource rules in the fetch transducer and the kernel
   (6.16, 6.17); the codec over the new messages.
2. **Proven free of panics and overflow (Kani, tier 1):** the PNG, JPEG, GIF
   and WebP decoders. Each decoder is a step function over an explicit
   state, and each harness takes **any** state satisfying the decoder's
   stated invariant and **any** input chunk up to a stated length, and
   proves that one step never panics, never overflows, never indexes out of
   bounds, writes only inside the caller's buffers and keeps the invariant.
   By induction over steps (argued in each README, not machine-checked),
   that covers every input of every length. Correctness evidence is the
   suites and differentials.
3. **Small and tested (tier 0):** layout's use of natural sizes, the GPU
   process's image drawing, the controls' painting and text editing, and the
   renderer's pipeline glue. All run in sandboxes.
4. **Assumed (TCB), new:** nothing new beyond Phase 5's. No image is decoded
   outside the renderer, and no image library ships (rule 8).

What a bug can and cannot do: decoders run in the renderer, on bytes any
server chose. A bug there mis-draws or kills one tab. Decoded pixels reach
the GPU process only as a validated upload with stated bounds, so a decoder
bug cannot widen the GPU process's attack surface beyond Phase 5's. A
compromised renderer can submit any form it likes to any URL, which is what
the web already lets any script do; what it cannot do is make the kernel
send a body it did not hand over, send it twice, attach cookies the method
and site forbid, or read a cross-origin response ORB blocks.

Not covered by any theorem, and said so: that the pixels are right (the
suites are the evidence); colour accuracy (sRGB assumed, ICC and PNG
`gAMA`/`cHRM` ignored, listed); that what the user typed is what the
renderer submits (the renderer holds the text; a compromised renderer can
change it, as script can); CSRF, which is the web's model and which
SameSite cookies, proven in 3.6, limit.

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-deflate` | 0 (2, per 6.0(a)) | RFC 1951; RFC 1950; RFC 1952 for gzip (6.0(h)) | Huffman tables, the inflate state machine, the zlib and gzip wrappers, Adler-32 and CRC-32 |
| `clazel-png` | 0 (1) | PNG Specification, Third Edition (W3C)† | chunks, CRC, IHDR to IEND, filters, Adam7, palettes and `tRNS`, bit depths 1 to 16, APNG's `acTL`/`fcTL`/`fdAT` per 6.0(d) |
| `clazel-jpeg` | 0 (1) | ITU-T T.81 (baseline and progressive Huffman, Annexes F and G); JFIF 1.02; EXIF orientation tag only | markers, Huffman decoding, dequantization, IDCT, upsampling, YCbCr and Adobe CMYK/YCCK to RGB |
| `clazel-gif` | 0 (1) | GIF89a Specification (CompuServe, 1990) | blocks, LZW, interlacing, the Graphic Control Extension, frames and disposal per 6.0(d) |
| `clazel-webp` | 0 (1) | RFC 9649 (WebP container and lossless); RFC 6386 (VP8) | RIFF container, VP8L lossless, VP8 key frames, `ALPH`, `ANIM`/`ANMF` per 6.0(d) |
| `clazel-image-shape` | 0 (1) | ours (WUFFS-style interface; 6.0(j) limits) | the `Decoder` trait, RGBA8 buffers, the size limits, premultiplication, the Kani step-harness template (6.3) |
| `clazel-image` | 0 (0) | HTML §4.8.4† (img), §4.8.4.3† (srcset), MIME Sniffing §6.1 | format dispatch from the sniffed type, the per-document image list, the decoded pixel budget, frame timing |
| `clazel-forms` | 0 (2 for `data/`, 0 for `edit/`; 6.0(b)) | HTML §4.10.22 (form submission), §4.10.18.3 (form owner), §4.10.5† (input types in scope); URL §5 (urlencoded) | form owner and the form data set, the three encodings, text field editing state |
| `clazel-displaylist` | 2 (exists) | ours | the image items (6.10) |
| `clazel-gpu` | 0 (exists) | as Phase 5 | image textures and the sampled quad pipeline (6.12) |
| `clazel-layout` | 0 (exists) | CSS 2.1 §10.3.2†, §10.6.2† (replaced sizing); CSS Images 3† (`object-fit` out); CSS Backgrounds 3† per 6.0(c) | natural sizes, relayout when they arrive, control boxes, background images if taken |
| `clazel-fetch` | 2 (exists) | Fetch §4.4† (HTTP-redirect fetch, method rewriting), §3.x† (ORB, as its own spec) | requests with a body, method rewriting, ORB |
| `clazel-ipc` | 2 (exists) | ours | 6.16's and 6.17's messages |
| `clazel-kernel` | 2 (exists) | ours; Fetch | navigations with a body, image sub-fetches, the theorems |
| `clazel-renderer` | 0 (exists) | — | the pipeline of 6.18 |

Decoders are one crate per format because a tier is a property of a crate:
WebP's VP8 is far larger than GIF and must not hold GIF's tier back.
`clazel-image` is the tier 0 glue so the decoders stay free of policy (which
format, how much memory, which frame to show).

## Dependencies on Phases 3 to 5

- **Phase 3:** the fetch transducer (3.6) is GET-only with no body
  (`crates/clazel-fetch/src/request/spec.rs`, `transducer/real.rs`), sends no
  `Accept-Encoding` (so servers answer with identity content), and already
  models SameSite with an unsafe method in its cookie retrieval (phase-3.md,
  3.6, the "unsafe method" mutation). 6.16 adds the body. `https:` works through the kernel
  (phase-3.md, 3.7 and 3.8), so the demo needs nothing more from Phase 3;
  until 3.10b, the HN session cookie does not outlive a run, so the demo
  logs in each time.
- **Phase 4:** every element has a form owner set by the parser
  (phase-4.md, 4.8, `form_owner`); `clazel-encoding`'s single-byte encoders
  exist for this phase's use (`crates/clazel-encoding/src/single_byte/spec.rs`
  says so); `clazel-percent` has the urlencoded percent-encode set.
- **Phase 5:** replaced boxes sized by attributes (5.13), paint (5.16), the
  display list and its validator (5.17a), the GPU process (5.17b), input
  (5.18), sub-resource fetches (5.19), the pipeline (5.20), the reftest
  harness (5.25), all on `main` ("Where Phase 5 left things", above).
  Phase 5's "Looking ahead" names each of these as Phase 6's entry points.

## What the exit page needs

Measured on 2026-11-16 by 6.1's `scripts/phase6-inventory.mjs` (5.1's script
was never written: `scripts/` holds none, so 6.1 wrote this one), plain `GET`s
with no login, counts only. Nothing of the pages is stored (their copyright is
Y Combinator's and its users'; Wikipedia's text and images are theirs).

**Hacker News.** The numbers are for the day; the shapes are what matters.

- **Front page** (34,013 bytes): two `img`: `s.gif` (`width="0" height="10"`,
  sniffed GIF) and the logo `y18.svg` (`18` by `18`, sniffed **SVG**). One
  style sheet, `news.css` (7,456 bytes), with two `url()` uses, both
  `triangle.svg`, one in `background`, one in `background-image` (the vote
  arrows; there is no `img` for them). The sheet has two `-gradient(` uses (a
  `linear-gradient(transparent, transparent)` layered with the arrow) and two
  `background-size`, no `background-repeat` or `background-position`. No
  `srcset`, `picture`, inline `<svg>`, `object`, `embed`, `canvas`, `video` or
  `audio`, no `style` attribute holding `url(`.
- **One item page** (106,286 bytes, 76 `img`: 75 `s.gif` spacers and the
  logo): spacer sizes `40x1` (31), `80x1` (20), `0x1` (16), `120x1` (7); the
  same single sheet and the same two `url()` uses. Images by sniffed
  signature over every distinct URL on both pages: **GIF 1 (`s.gif`), SVG 2
  (`y18.svg`, `triangle.svg`), PNG 0, JPEG 0, WebP 0.** URL extensions and
  signatures agree.
- **SVG files** (the exit's only vector images): `y18.svg`, 315 bytes: elements
  `svg`, `path` (2); attributes `xmlns`, `width`, `height`, `viewBox`, `d`,
  `fill`. `triangle.svg`, 131 bytes: the same elements and attributes (one
  `path`). The `d` data uses only `m`, `h`, `v`, `z` and implicit `lineto`
  after `m`, all relative, with decimal numbers; `fill` is `#rgb` or `#rrggbb`.
  `triangle.svg`'s path reaches outside its `viewBox` (to be clipped), and it
  is drawn as a CSS background scaled by `background-size`.
- **Forms.** Front page: one, the search box, `method="get"`
  `action="//hn.algolia.com/"` (a JavaScript site, so it does not work, as
  the goal says), one `input type=text`. Item page: that one and `comment`:
  `method="post"` `action="comment"`, no `enctype` (so
  `application/x-www-form-urlencoded`), controls `input[hidden]` x3,
  `textarea` x1, `input[submit]` x1. Login page (1,125 bytes, no sheet, no
  image): two forms, both `method="post"` with **no `action`** (the form's own
  URL), the first `input[text]`, `input[password]`, `input[submit]`, the
  second (create account) `input[hidden]`, `input[text]`, `input[password]`,
  `input[submit]`. The reply page, fetched logged out, is the login page again
  (1,168 bytes, the same two forms): the reply form itself is the item page's
  `comment` form, which a logged-in session sees, and is not reachable
  without logging in. Control types in all: `hidden`, `text`, `password`,
  `submit`, `textarea`; none of `checkbox`, `radio`, `select`, `button`,
  `file` or `image` (attributes beyond the types were not counted). Voting is
  a link (`vote?id=...&how=up&auth=...`), a plain `GET` Phase 5 already
  follows.

**Settled: HN's logo and vote arrows are SVG** (`y18.svg`, `triangle.svg`,
the latter as a CSS background). 6.0(c)'s rule therefore applies: **S2 for
exactly the elements and attributes those two files use becomes a new item,
6.11a**, and `s.gif` (GIF, with 6.7) is the only raster image the exit page
loads. Without 6.11a the exit page would show no logo and no vote arrows.

**One Wikipedia article** (Hacker News, 144,605 bytes), the second shape the
decoders meet: 9 `img` (5 URL-extension `svg`, 3 `png`, 1 without extension,
a tracking beacon whose sniffed signature is none of ours); sniffed over the
13 distinct URLs (`img` and CSS): **SVG 9, PNG 3, other 1**; the PNGs are
server-rendered rasters of SVG sources. Attributes on `img`: `width` and
`height` on 8, `alt` on 8, `loading="lazy"` on 5, `decoding="async"` on 3,
`srcset` (density `2x`) on 2, inside 2 `picture`s with 2 `source`. Four CSS
`background` uses of SVG. Its SVG files use far more than HN's:
`linearGradient`, `radialGradient`, `stop`, `defs`, `g`, `clipPath`, `circle`,
`style` attributes, `transform`, editor metadata (`sodipodi:*`, `inkscape:*`,
`rdf:*`) and 155 `stop`s in the largest. That is what 6.0(c)'s S2 deliberately
does not cover: those SVGs show as broken images (their `alt`), and the README
says so. Forms: two search forms, `method` absent (so `GET`), `input[search]`,
`input[hidden]`, `button`.

**What this means for the plan.** No JPEG, WebP or PNG appears on HN's pages.
The decoders are built for the four formats the roadmap names and for the
web beyond HN (Wikipedia shows PNG and `srcset` densities), and their
evidence is the vendored suites. 6.6 (progressive JPEG) and 6.9 (VP8), the
two largest items, do not gate the exit: **they may be cut or deferred
without losing it**, and the order of work says so.

## Looking ahead: what Phases 7 and 8 do with this

- **JavaScript (Phase 7):** `HTMLImageElement.decode()`, `naturalWidth`,
  `FormData`, `form.submit()`, `requestSubmit()`, input events and
  constraint validation read the state this phase keeps per node id.
  `<canvas>` reuses the image upload item.
- **Phase 8:** SVG in full, AVIF, ICC colour, `<input type=file>` (a host
  file picker; the kernel hands the renderer one file the user chose),
  `<picture>` media conditions beyond width and density, IME composition,
  the HTTP cache (decoded images keyed by URL), and the legacy multi-byte
  encoders forms need for pages in those encodings.

## Work items

Ordered by dependency. Size: S under a day, M a few days, L a week or more.
Tier 2 items follow CLAUDE.md rule 3 (spec and contracts committed first);
tier 1 items commit their harness statements and the invariant first.

### 6.0 Decisions for the maintainer (S) — decided

**Decided (2026-11-16) by a Claude session, on the maintainer's delegation
("for the decisions I think you can choose, take into account the project
goals"): every recommendation below is taken.** That is: (a) **B**,
`clazel-deflate` at tier 2; (b) **B**, the form data set and its encodings
at tier 2, editing at tier 0; (c) **F1, U2**, and **S1** unless 6.1's
inventory shows the exit page's images are SVG, in which case 6.1 records
it and S2 for exactly the elements HN's files use becomes a new item
(**6.1 found them SVG: see 6.11a**);
(d) **A**, first frame only for the exit, with 6.19 (animation) last;
(e) **B**, one `FetchSub` family with a destination, retiring `FetchStyle`
and the `Style*` replies; (f) **B**, a new `TextInput` message; (g) **A**,
HN with images, login, vote and comment, the real site by the maintainer's
hand only, the fixture in CI; (h) **A**, no `Accept-Encoding` this phase;
(i) **B**, ORB in the kernel, proven; (j) the numbers as proposed,
provisional until 6.20 measures them. The grounds are the project's: every
byte a page chose passes first through proven code where the shape allows
it (a, b, i), messages are general before they multiply (e), and the exit
is one real site whose evidence in CI is our own fixture (g). A maintainer
may reverse any of these; items built on a reversed choice say what is out
of date.

**Decided (2026-11-16), by the maintainer: the image decoders stay at tier 1**
for this phase, as VERIFICATION.md's minimum and the roadmap say. Tier 2 was
weighed: PNG, GIF, WebP lossless and VP8 are defined bit-exactly, so each
could be transcribed and proven; JPEG could too, with one integer IDCT
pinned as a listed modelling choice, since T.81 allows any IDCT within an
accuracy bound. That roughly doubles the decoder work, and safe Rust
already rules out memory corruption, so tier 2's gain here is correct pixels,
not isolation. Raising a decoder to tier 2 later is open, one crate at a
time; the WUFFS-style step functions of 6.3 are the shape such a proof would
start from.

**(a) DEFLATE's tier.** PNG's image data is zlib (RFC 1950) over DEFLATE
(RFC 1951), so every PNG byte passes through inflate. **A:** tier 1 inside
`clazel-png`, as the roadmap says for decoders. **B:** its own crate at
tier 2: RFC 1951 is a short, exact state machine (block header, stored,
fixed and dynamic Huffman, length and distance), the shape tier 2 has
handled six times, and an exact spec gives a correctness proof, not only
panic-freedom; the same crate later decodes HTTP `Content-Encoding: gzip`
(6.0(h)). Cost: one L item more than A, mostly the canonical Huffman
construction's proof. **Recommendation: B.**

**(b) Forms' tier.** VERIFICATION.md requires tier 0 for UI; the form data
set and its encodings are not parsers of untrusted bytes but they decide
what is sent. **A:** all tier 0. **B:** the form data set construction and
the three encodings at tier 2 (they are short numbered algorithms over the
DOM arena, which is already proven well formed), text editing at tier 0.
**Recommendation: B**, with `clazel-forms` split into `data/` (Verus) and
`edit/` (tier 0) as two crates if a crate-wide tier forces it (`clazel-forms`
and `clazel-forms-edit`).

**(c) Scope of image formats and uses.** *Formats:* **F1:** PNG, JPEG
(baseline and progressive; arithmetic coding, 12-bit and lossless JPEG out),
GIF, WebP (lossless and lossy) — the roadmap's four. **F2:** F1 plus BMP and
ICO (small; favicons). *SVG:* **S1:** none; an SVG image is a broken image
showing its `alt`. **S2:** a static subset (`svg`, `path`, `rect`,
`circle`, `polygon`, `g`, fills and strokes in solid colours, `viewBox`), a
parser of our own on Phase 4's XML-free tokenizer is not enough, so S2 needs
an XML parser too: an L item at least. *Uses:* **U1:** `img` only. **U2:**
`img` plus CSS `background-image: url()` with `background-repeat`,
`background-position` and `background-size` (CSS Backgrounds 3†), which many
sites rely on. **Recommendation: F1, S1 unless 6.1 shows the exit needs SVG
(then S2 for exactly what HN's files use, listed), U2.** `srcset` with
density descriptors and `sizes` (HTML §4.8.4.3†) is in either way: it is
small, and the right density matters at scale 2.

**(d) Animation.** **A:** first frame only, for GIF, APNG and animated WebP.
**B:** animate, driven by the kernel's `Tick` (each frame a new list
uploading a new image id or reusing a frame cache), with a per-document cap
on decoded frames. **Recommendation: A in this phase's exit, B as the last
item (6.19) if time allows**: the decoders decode every frame from the start
so B adds no decoder work, only timing and memory policy.

**(e) The sub-resource fetch message.** 5.19 shipped `FetchStyle` (tag 14)
and four `Style*` replies (tags 110 to 113), for style sheets only. **A:** a
parallel family for images (`FetchImage` and `Image*`, five new tags), with
5.19's theorems copied and restated for it. **B:** one general family,
`FetchSub { request, destination, url }` with `destination` one of `style`
and `image` (Phase 7 adds `script` and `empty`), and `Sub*` replies, under
new tags; `FetchStyle` and the `Style*` replies are retired (their tags
stay unused, as tag 10's will) once the renderer sends `FetchSub` for
sheets; 5.19's theorems are restated once over destinations. **C:** keep
`FetchStyle` and add a destination field to it, which changes a shipped
message's fields, against the codec's rule that a tag's meaning never
changes. **Recommendation: B.** It costs one restatement of 5.19's theorems
now instead of a copy per destination in this phase and the next.

**(f) Text input.** 5.18's `Input` carries a key code. Typing into a field
needs the characters the OS's keyboard layout produced, which a key code
does not give (dead keys, AltGr, other layouts). **A:** the renderer maps
key codes to characters with a fixed US layout (wrong for most of the
world). **B:** a new message, `TextInput { text }` (kernel to renderer,
under a new tag), carrying the string the host read from the OS's text
event (`NSEvent characters` on macOS, the keymap through our own X11 client
on Linux, `WM_CHAR` on Windows); `Input`'s key kind stays for editing keys
(arrows, Backspace, Tab, Enter). The kernel routes it as it routes `Input`,
and `theorem_input_only_to_own_tab` is restated over both. IME composition
stays out (Phase 8), listed. **Recommendation: B.**

**(g) The exit.** **A:** HN with images, login, vote and comment
(as above), run by hand on the real site, and the full flow on the fixture
in CI. **B:** A plus a second real site whose images are the point (a
Wikipedia article), which needs floats (Phase 8's CSS breadth) to look
right. **Recommendation: A**; Wikipedia's images are in 6.20's local
checks, with its layout gap stated.

**(h) Content-Encoding.** With 6.0(a)'s B, `gzip` and `deflate` response
bodies are cheap to support. Where: decoding in the kernel puts a
decompressor on unsandboxed bytes; decoding in the renderer keeps it in the
sandbox but the kernel's `theorem_body_is_the_response` then speaks of
encoded bytes. **A:** keep sending no `Accept-Encoding` (today's behaviour,
servers send identity). **B:** send `Accept-Encoding: gzip`, carry encoded
bodies to the renderer with the coding named, decode there with
`clazel-deflate`. **Recommendation: A in this phase** (nothing on the exit
needs it and it changes a Phase 4 theorem's statement), B as a Phase 8
performance item.

**(i) ORB.** Cross-origin image (and, by 5.19, style) responses are
`no-cors` and reach the renderer. Under 5.0(h)'s F1 they carry no
credentials, which limits what a compromised renderer can read to what an
anonymous client on the user's network could read (intranet hosts are the
case that matters). **A:** no blocking, listed. **B:** Fetch's Opaque
Response Blocking† in the kernel, proven (`theorem_orb`), so a cross-origin
`no-cors` response reaches a renderer only if its type or sniffed bytes are
an image, a style sheet (for `style`), or allowed media; everything else
becomes an empty response. **Recommendation: B**: it is a small spec, it
closes the intranet case, and it is what any later move to Fetch's
credentials (5.0(h)'s F2) needs first.

**(j) Memory and decoding policy.** Proposed numbers, each stated in
`clazel-image`'s README and measured by 6.20: a decoded image at most 2^14
pixels on a side and 2^26 pixels in all; decoded pixels per document at most
512 MiB, with images outside the viewport by more than one viewport height
dropped and decoded again on scroll; an image's encoded bytes at most the
body limit of 4.13. An image over a limit is a broken image. One fetch and
one decode per URL per document (HTML's "list of available images"†), which
HN's 115 identical spacers need. `loading=lazy` is honoured with the same
one-viewport margin. **Recommendation: these numbers.**

### 6.1 Inventory and test data (M) — built (2026-11-16)

**Inventory: done.** `scripts/phase6-inventory.mjs` (Node, run locally,
never in CI; stores nothing) measured HN's front page, an item page, the login
page and the reply page (which, logged out, is the login page), and one
Wikipedia article. The result is in "What the exit page needs" above. It
settled 6.0(c): **HN's images are SVG, so 6.11a exists.** A news site beyond
HN was not measured (this run named HN and Wikipedia only); the script takes
URLs as arguments if a later item wants more shapes.

**Vendored now**, shared by 6.13, 6.14, 6.10 and 6.11, at WPT commit
`4ad507b28db0a636f528def9161d109fe11b93a3` (the commit `clazel-css` and
`clazel-encoding` already use), in `crates/clazel/tests/wpt-phase6/`
(no crate of this phase exists yet to hold it; the item that converts it may
move it) with `LICENSE.md` (BSD-3-Clause), `SOURCE.md` and `MANIFEST.sha256`:
`html/semantics/forms/` (`form-submission-0`, `the-form-element`,
`the-input-element`, `the-button-element`, `the-select-element`,
`the-textarea-element`, `the-option-element`, `the-optgroup-element`,
`resetting-a-form`, `attributes-common-to-form-controls`,
`form-control-infrastructure`; `form-submission-target`, `constraints`,
`textfieldselection`, `the-label-element` and the rest are left out as
needing nested browsing contexts, validation UI or script),
`html/semantics/embedded-content/the-img-element/` and
`url/urlencoded-parser.any.js`. These are browser tests and most pages need
script, so no table is generated yet and nothing reads them; the item that
uses them writes the converter in `xtask/src/testdata/` and picks the
script-free cases. Four upstream files holding CR or CRLF (`multiline-placeholder-cr.html` and `-crlf.html` in `the-input-element` and `the-textarea-element`) are left out so the
repository's `eol=lf` rule cannot change them. Resources the pages name from
outside these directories (`/common/`, `/images/`, `/resources/`) are not
vendored; an item that needs one adds it with its commit recorded.

**Not vendored now; each is vendored by the item that uses it, at a pinned
commit, with its licence file beside it.** Licences checked on 2026-11-16
against the upstreams:

| Data | Upstream | Licence | Item |
|------|----------|---------|------|
| PngSuite | http://www.schaik.com/pngsuite/ (the 2011 archive; pin its SHA-256) | its own permissive notice: "Permission to use, copy, modify and distribute these images for any purpose and without fee is hereby granted" (Willem van Schaik); keep the notice beside it | 6.4 |
| libjpeg-turbo `testimages/` | github.com/libjpeg-turbo/libjpeg-turbo, tag `3.2.1` or later | mixed, stated in `testimages/LICENSE.txt`: `testorig*` and `testimg*` under the IJG licence, the rest Modified BSD, two ICC profiles MIT (Little CMS), one ICC profile with free use if unaltered; all redistributable, each file's licence recorded | 6.5, 6.6 |
| ITU-T T.83 conformance streams | ITU-T | **a gap**: not read at source, and the terms of the recommendation's attached streams do not clearly allow redistribution; 6.5 states the gap unless it finds a redistributable copy. libjpeg-turbo's and Wuffs' files stand in | 6.5, 6.6 |
| Wuffs `test/data` (PNG, GIF, JPEG, WebP, DEFLATE, zlib, gzip, `artificial-*` corner cases) | github.com/google/wuffs, `test/data/`, pin a commit (`main` was `b36a81d3352604fee1fee3661f39909706b1b966` on 2026-11-16) | MIT or Apache-2.0, our choice (`LICENSE-MIT`, `LICENSE-APACHE`); its README says some files derive from third-party images, so each directory used is read for notices | 6.2, 6.4, 6.5, 6.7, 6.8 |
| libwebp test vectors | chromium.googlesource.com/webm/libwebp-test-data | **licence not stated**: the repository has no `LICENSE` or `README` (155 entries, all data), so it cannot be vendored as it stands; Wuffs' `*.lossless.webp` and `*.lossy.webp` stand in, and the maintainer may ask the owners for a licence | 6.8, 6.9 |
| DEFLATE and zlib streams | Wuffs' `test/data` and its `artificial-deflate`; zlib (github.com/madler/zlib, zlib licence) only where a file is data, not code | MIT/Apache-2.0; zlib licence | 6.2 |

Dev-dependencies (`miniz_oxide`, `png`, `gif`, `image-webp`, `zune-jpeg`)
were **not** added here: this item adds no crate and no `test` rows to
`docs/DEPENDENCIES.md`. Each is added by the item that runs that reference
decoder, with its transitive rows. Reference outputs from libjpeg-turbo and
libwebp, generated by a script under `scripts/` at pinned versions and
committed so CI runs no C, are made by 6.5 and 6.9, not here.

### 6.2 DEFLATE and zlib (L)

`clazel-deflate`, target tier 2 (6.0(a)). Spec and contracts first:
RFC 1951 §3.2.3 (block format), §3.2.4 (stored), §3.2.5 (lengths and
distances), §3.2.6 (fixed codes), §3.2.7 (dynamic codes), §3.2.2 (canonical
Huffman construction, as "the algorithm"); RFC 1950 §2.2 (header, FCHECK,
FDICT refused, Adler-32 trailer); RFC 1952 §2.3 (gzip, for 6.0(h) later).
Modelling choices at the top: a decoder is a function of the whole input
and of input split into any chunks, proven equal (as Phase 4's tokenizer);
the output limit is a parameter, and exceeding it is a stated error, not a
spec deviation. Exec: resumable, one bounded step at a time, a 32 KiB window
inside a caller buffer, table-driven Huffman decoding with a proof that the
fast table equals the canonical code. Theorems: `theorem_inflate_total`,
`theorem_chunking_irrelevant`, `theorem_output_bounded` (output never
exceeds the limit, so a bomb stops), `theorem_huffman_table` (the fast table
decodes exactly the canonical code). Independent transcription from
RFC 1951's prose without reading `spec.rs`, proven equal; certified
mutations per rule (each length base, each extra-bits count, the
incomplete-code rule, the distance-too-far rule). Conformance: the vendored
streams and a differential against `miniz_oxide` on them and on mutated
streams.

### 6.3 Image buffers and the decoder shape (S)

`clazel-image-shape` (a crate of its own, target tier 1; the plan first put
it as module `shape` of `clazel-image`, see "Where it lives" below). One
interface every decoder implements, in
WUFFS style: `decode_config` (format, width, height, frame count if known)
from the first bytes; `decode_frame` into a caller-owned RGBA8 buffer the
caller sized from the config, with a caller-owned work buffer whose size the
decoder states as a function of the config; each call takes a chunk and
returns `NeedMore`, `FrameDone` or an error. No decoder allocates after its
config is read. Every decoder exposes `step(state, chunk, buffers)` and the
invariant `inv(state, buffers)` its Kani harness uses. The harness template
(`decoder_step_harness!`) lives here and each decoder instantiates it. The
crate also holds the 6.0(j) limits (`MAX_SIDE` 2^14, `MAX_PIXELS` 2^26) with
a checked size function and straight-to-premultiplied RGBA8, each with Kani
harnesses.

**Where it lives.** A `shape` module inside `clazel-image` (tier 0) would
make a cycle (`clazel-image` dispatches to the decoders, which implement the
shape) and would put tier 0 code under tier 1 decoders, whose claim covers
the workspace crates they depend on. So the shape is its own crate with no
dependencies; `clazel-image` stays the policy glue and depends on it and on
the decoders. Premultiplication moved here from `clazel-image`'s contents for
the same reason (the renderer and the decoders both need it, and it is
arithmetic on page-controlled bytes).

### 6.4 PNG (L)

`clazel-png`, target tier 1. Chunk layout and CRC-32; IHDR (every allowed
colour type and bit depth combination, others refused), PLTE, `tRNS`, IDAT
across any number of chunks through `clazel-deflate`, IEND; the five
filters with their exact arithmetic; Adam7; expansion of 1, 2 and 4-bit
samples and 16-bit reduction to 8 (a listed choice: truncation or rounding,
matching the `png` crate's choice so the differential is exact); `acTL`,
`fcTL`, `fdAT` parsed and frames decoded (6.0(d)); `gAMA`, `cHRM`, `iCCP`,
`sRGB`, `cICP` read and ignored, listed. Kani: the step function over any
state with the invariant and any chunk up to a stated length; the filter
functions over any row up to a stated width; the Adam7 pass geometry over
every width and height up to 2^14. Tests: PngSuite's every file (its `x*`
files must be refused), exact against `png`; mutated PngSuite files never
panic.

### 6.5 JPEG: baseline (L) — built (2026-11-17)

`clazel-jpeg`, target tier 1. ITU-T T.81 Annex B (markers: SOI, SOF0, SOF1,
DHT, DQT, DRI, SOS, RSTn, APPn, COM, EOI), Annex C (Huffman tables),
Annex F (baseline sequential decoding: DC prediction, AC run-length,
restart intervals, `0xFF00` stuffing), Annex A's IDCT (a listed choice: the
integer IDCT libjpeg-turbo's `jidctint` uses, so the differential can be
near-exact), chroma upsampling (listed: the "fancy" triangular upsampling
libjpeg-turbo defaults to), JFIF's YCbCr to RGB (JFIF 1.02 §7), Adobe's
APP14 transform flag for CMYK and YCCK (inverted CMYK as Adobe writes it,
listed), and EXIF's Orientation tag (CSS Images 3's `image-orientation:
from-image`† default) and nothing else of EXIF. Kani: the step function, the
bit reader, Huffman decoding over any table that passed construction, the
IDCT over every coefficient block with coefficients in the range
dequantization can produce (`i16` times quantizer, checked), upsampling over
every geometry. Tests: libjpeg-turbo's images against its own output, every
sample within a stated tolerance (expected: zero for the integer IDCT; any
nonzero difference is reported per file), with the histogram printed.

### 6.6 JPEG: progressive (M) — built (2026-11-21)

`clazel-jpeg`. Annex G: SOF2, spectral selection and successive
approximation, DC and AC first and refinement scans, EOB runs; the whole
coefficient plane kept (its size from the config, inside 6.0(j)'s budget).
Kani as 6.5 for the new scan decoders. Tests: libjpeg-turbo's progressive
images and `jpegtran`-converted copies of every baseline test image.

### 6.7 GIF (M)

`clazel-gif`, target tier 1. GIF89a: header, logical screen descriptor,
global and local colour tables, image descriptor, interlacing, the variable
code-size LZW with clear and end codes and the full-table behaviour (deferred
clear, as browsers do: a listed choice with the GIF89a text quoted), the
Graphic Control Extension (transparency index, disposal, delay), and every
other extension skipped by its block sizes. Frames are composited onto the
canvas with each disposal method, so 6.0(d)'s A shows the first composited
frame and B needs nothing more from the decoder. Kani: the step function and
LZW over any table state. Tests: Wuffs' GIF data exact against `gif`; the
animated files' every frame.

### 6.8 WebP: container and lossless (L)

`clazel-webp`, target tier 1. RFC 9649: RIFF, `VP8 `, `VP8L`, `VP8X` with
`ALPH`, `ANIM` and `ANMF`; VP8L: the transforms (predictor with its fourteen
modes, colour, subtract-green, colour indexing with pixel bundling), the
colour cache, the meta prefix codes, LZ77 backward references with the
distance map. Kani: the step function, prefix code construction over any
code lengths, each transform over any row up to a stated width. Tests:
libwebp's lossless vectors, exact.

### 6.9 WebP: lossy (VP8) (L)

`clazel-webp`. RFC 6386, key frames only (WebP has no inter frames): the
boolean entropy decoder (§7), frame header (§9), the mode and coefficient
token trees and probabilities (§11 to §13), dequantization (§14), the
inverse WHT and DCT (§14.3, §14.4, exactly as the RFC's reference code),
intra prediction for every mode (§12), the loop filter, simple and normal
(§15), and YUV 4:2:0 to RGB (listed: the conversion libwebp uses, with its
fixed-point constants). With `ALPH` the alpha plane (filtered, possibly
VP8L-compressed). Kani: the boolean decoder, each prediction mode at block
edges, the loop filter over any pixel values, the transforms over any
coefficients in range. Tests: libwebp's lossy vectors against `dwebp`'s
output, exact (VP8 decoding is defined bit-exactly; the RGB conversion is
pinned to libwebp's).

### 6.10 The display list: image items (M)

`clazel-displaylist`, tier 2, spec and contracts first, in the format 5.17a
designed, taking the next tags after the last 5.17a uses: **upload image**
(id, width, height, then width × height × 4 bytes of premultiplied RGBA8),
**draw image** (id, destination x, y, width, height, as tag 1; source
rectangle in the image's pixels; a filter flag, nearest or linear), **free
image** (id). Validation rules added: image ids are a separate space below
2^16; an upload's id is not live and its sides are 1 to 2^14; live image
bytes stay at most a stated bound (proposed 2^28, inside 6.0(j)'s budget,
the GPU process's limit, not the renderer's); a draw names a live image and
a source rectangle inside it; the whole list's byte limit grows by a stated
amount for uploads, or uploads move to a second channel if 6.12's prototype
shows copying through the socket is too slow (decided there, with numbers).
Theorems extended (`theorem_validated_bounds` covers image bytes and source
rectangles); certified mutations per rule; independent transcription
extended.

### 6.11 Layout: natural sizes and background images (M)

`clazel-layout`. Replaced elements take their natural size from the image's
config once known (CSS 2.1 §10.3.2†, §10.6.2†: width and height from
attributes, the natural size, or the natural ratio), so an `img` without
attributes lays out at 0×0 until its config arrives and then the document
lays out again (the renderer batches relayouts per `Tick`). A broken image
shows its `alt` text inside an inline box, as HTML §15.4.2† suggests. With
6.0(c)'s U2: `background-image: url()` resolved against the sheet's URL,
`background-repeat`, `background-position` and `background-size` painted as
tiled image draws clipped to the background painting area. Paint emits 6.10's
draw items. Tests: WPT `css/CSS2/` replaced-element reftests and
`css/css-backgrounds/` reftests for the subset, through 5.25.

### 6.11a Static SVG images: exactly what HN's files use (S to M)

Added by 6.1's inventory (6.0(c): S2 for exactly the elements HN's files
use). `clazel-svg`, a new crate, target tier 1, `tier = 0` to start. SVG 2
(W3C) is the standard for the pieces it covers, section numbers† pinned when
the spec is written; the path grammar is SVG 2 §9.3†.
**Scope is exactly the two files measured (`y18.svg`, `triangle.svg`) and no
more:** elements `svg` and `path`; attributes `xmlns`, `width`, `height`,
`viewBox`, `d` and `fill`; path commands `M`/`m`, `L`/`l`, `H`/`h`, `V`/`v`,
`Z`/`z` (including the implicit `lineto` after `moveto`), numbers as decimal
fractions; `fill` as `#rgb` or `#rrggbb`; the default non-zero fill rule; the
default `preserveAspectRatio` (`xMidYMid meet`), clipped to the viewBox. A
tiny XML tokenizer of our own for just these (start tags, attributes with
quoted values, the XML declaration and comments skipped). Anything else (any
other element, attribute, command or colour syntax, `style`, entities,
`DOCTYPE`, namespace prefixes) makes the image a broken image showing its
`alt` (6.0(c) S1's behaviour), never a partial draw. **Out, and Wikipedia's
SVGs need them:** gradients, `g`, `circle`, `rect`, `clipPath`, `defs`,
`transform`, `style`, strokes, curves, metadata. Phase 8 does SVG in full.

It rasterises to an RGBA8 buffer at the requested size (anti-aliased scanline
coverage, integer arithmetic) behind 6.3's `shape` interface, so 6.10's image
items and 6.12's upload carry it unchanged. MIME Sniffing has no SVG
signature, so the declared type (`image/svg+xml`, which 6.17's ORB must
allow) selects this decoder: `clazel-image` dispatches on the declared type
for SVG only, a listed departure from "dispatch on the sniffed type".
Tier 1 proves no panic, no overflow and no out-of-bounds in the tokenizer,
path parser and rasteriser. Tests: both files rasterised and compared with a
reference renderer's output at the sizes HN uses (18x18; 32x16 as a
`background-size`-scaled background), tolerance stated in the harness; a
corpus of malformed XML and path data. Depends on 6.3; needed by 6.18 and the
exit.

### 6.12 The GPU process: images (M)

`clazel-gpu`. A textured-quad pipeline sampling an RGBA8 texture, nearest or
linear, premultiplied source-over (the same blending as 5.17b), shaders fixed
at build time as 5.17b's. Uploads go to per-image textures (or an atlas for
small ones, a listed choice measured on HN's spacers). Prototype first:
measure an upload of a 4096 × 4096 image through 5.18's list socket on each
OS; if it takes more than a frame, 6.10's second channel (a shared memory
region the renderer writes and the GPU process maps read-only, through
`clazel-sys`) is built here, with its calls audited. Tests: every new item on
lavapipe against stored pixels.

### 6.13 Forms: the form data set and form owner (L)

`clazel-forms`, `data/`, target tier 2 (6.0(b)). HTML §4.10.18.3 (form
owner, read from the DOM's `form_owner` and the `form` attribute; checked
against the text at HTML commit `0793d3d8`, 2026-11-16),
§4.10.22.4 "constructing the entry list" for the controls in scope:
`input` of types `text`, `search`, `email`, `url`, `tel`, `password`,
`hidden`, `checkbox`, `radio`, `submit`, `image` (the click coordinates),
`number` (as text), and `button`, `select` (single and `multiple`),
`textarea` (with "the textarea wrapping transformation"†); disabled
controls, `datalist` ancestors, the submitter, `name` absent or empty,
`dirname` (direction always `ltr` until bidi, listed). Control state (value,
checkedness, selectedness, dirty flags) is a side table keyed by node id, as
Phase 5's computed style. Proven: the entry list equals the spec's for every
DOM the tree builder can produce; independent transcription; mutations per
step. Tests: WPT `form-submission-0/` cases that need no script, run by
building DOMs with the tree builder and comparing entry lists.

### 6.14 Forms: encodings and the submission algorithm (M)

`clazel-forms`, `data/`, tier 2. URL §5.2 the
`application/x-www-form-urlencoded` serializer (on `clazel-percent`'s set,
with the encoding's encoder from `clazel-encoding`; a page in a multi-byte
legacy encoding cannot submit until Phase 8, listed); HTML §4.10.22.8
`multipart/form-data` (boundary from the kernel's randomness, passed in;
file entries cannot exist since `type=file` is out) and §4.10.22.9
`text/plain`; HTML §4.10.22.3 "form submission algorithm" steps from the
form's action, method (`get`, `post`; `dialog` out), enctype, target
(`_self`, `_parent`, `_top` all mean this tab until nested browsing contexts;
`_blank` and named targets open a new tab through the kernel's existing
`OpenTab`, a listed choice the maintainer may reverse) and `novalidate`; the
"mutate action URL" and "submit as entity body" branches; `mailto:` and
`javascript:` actions refused, listed. Output: a navigation request, URL,
method and optional body with its content type. Proven against the spec;
independent transcription; conformance: WPT `url/urlencoded-parser` (as
round trips), the `form-submission-0` method and enctype cases.

### 6.15 Controls: painting, focus and editing (L)

`clazel-forms-edit` (or `clazel-forms`' `edit/`), tier 0, and
`clazel-layout`. Controls drawn as the host platform's plain look would be
too large a surface; a single fixed look (bordered boxes, a check mark, a
filled circle, a button with a gradient-free fill) is drawn from boxes and
glyphs, listed. Focus (click, Tab and Shift-Tab in tree order with
`tabindex`† as numbers, focus ring), text field editing (insert from 6.0(f)'s
text input, caret, Backspace, Delete, arrows, Home, End, selection by Shift
and mouse drag, no clipboard until the host offers one, listed), `password`
fields drawn as bullets, `textarea` with lines, `select` as a list drawn in
the content area (a native popup would be outside the tab's surface), Enter
in a text field submitting its form's default button (HTML §4.10.22.2
"implicit submission"), checkboxes and radio groups toggling, `maxlength`,
`readonly`, `disabled`, `placeholder`. Constraint validation: `required`,
`pattern` waits for a regular expression engine (Phase 7) and is ignored,
listed; a form with an empty required field refuses to submit and focuses
it. Tests: per control, driven by synthetic `Input` messages, against stored
box tree dumps and pixels.

### 6.16 The fetch transducer and kernel: navigations with a body (L)

`clazel-fetch`, `clazel-ipc` and `clazel-kernel`, tier 2, spec and contracts
first. `clazel-ipc`: the renderer's `Navigate` gains a method and an
optional body with its content type, as a new tag (tag 9 stays as the
`GET`-only form; the new one is `Submit { url, method, content_type, body
}`, with a body at most a stated size, proposed 16 MiB). `clazel-fetch`:
requests carry a method and body; `Content-Length` and the body are written
by `clazel-http`'s request serializer (built in 3.2 for `GET`, extended);
Fetch's HTTP-redirect fetch step 12† and RFC 9110 §15.4: on 301 and 302 a
`POST` becomes a `GET` without a body, on 303 every method but `HEAD`
becomes a `GET`, on 307 and 308 method and body are kept (and the body is
sent again, which is the one resend the standard allows); `Origin` is sent
on a `POST` (Fetch's "append a request `Origin` header"†); the cookie
retrieval already takes the method (3.6) and now receives it. Kernel: a
`Submit` from a committed renderer starts a navigation in its tab only;
history entries made by a `POST` are not resubmitted on back or reload
(the page is fetched again with `GET`, or shows a notice: a listed choice,
recommended the notice).

Theorems, with certified mutations: `theorem_body_from_requester` (every
body octet the kernel sends on a connection is from the `Submit` that
started that navigation, of the tab whose renderer sent it);
`theorem_body_sent_once` (a body is sent at most once, plus once per
307/308 hop, and never after the navigation is replaced, cancelled or the
renderer is gone); `theorem_redirect_method`; `theorem_post_cookies`
(`theorem_wire_cookies` restated: SameSite `Lax` and `Strict` cookies are
not sent on a cross-site `POST`); `theorem_address_bar_integrity` and the
Phase 2 to 5 theorems restated with `Submit`. The independent transcription
of 3.6 is widened to methods with a body. Tests: the transducer's rows;
`tests/fetch.rs` against an in-process server that echoes requests.

### 6.17 The kernel: image sub-fetches and ORB (M)

`clazel-fetch`, `clazel-ipc`, `clazel-kernel`, tier 2. With 6.0(e)'s B, image
requests are 5.19's sub-resource fetch with destination `image`, `no-cors`,
credentials per 5.0(h)'s F1, `Accept` as Fetch sets it for images†, and a
per-document limit on images in flight and in all (proposed 16 and 4,096).
With 6.0(i)'s B: ORB† as its own spec in `clazel-fetch`, on the response
headers and the first 1,024 bytes through `clazel-mime`'s sniffer, deciding
before any body octet is forwarded. Theorems: `theorem_orb`;
`theorem_subfetch_only_to_requester` and `theorem_subfetch_credentials`
over the new destination. Tests: ORB's WPT cases (`fetch/orb/`†) that need
no script, as transducer rows; through processes in 6.20.

### 6.18 The renderer pipeline (M)

`clazel-renderer`, tier 0. After 5.20's style step: collect `img` elements
(and, with U2, background images from computed style), choose a candidate
from `srcset`/`sizes` by the viewport's scale, deduplicate by URL, request
those within 6.0(j)'s margin of the viewport, sniff each response with
`clazel-mime`'s image rules, decode in chunks as bytes arrive (so the config
arrives early and layout can proceed), premultiply, upload, and redraw.
Relayouts are batched to one per `Tick`. Inputs go to 6.15's focus and
editing; a submit runs 6.14 and sends `Submit`. The memory bound of 5.20
grows by 6.0(j)'s numbers and the decoders' work buffers; stated in the
README and measured by 6.20.

### 6.19 Animation (M, if 6.0(d) takes B)

`clazel-image`. Frame timing on `Tick` (GIF's delay with browsers' minimum
of 2 centiseconds treated as 10†, a listed choice; APNG's and WebP's
delays), one decoded frame kept per image plus the canvas, frames uploaded
under fresh ids and freed, animation paused while the image is outside the
viewport. Tests: frame sequences against the decoders' composited output.

### 6.20 Exit demo, hostile inputs, process tests (M)

- **Demo:** on each OS, HN's front page with images, login, a vote, a
  comment, by hand on the real site with a test account; the result recorded
  in the Status table.
- **The fixture server:** in-process, implementing an HN-shaped login (a
  `POST` setting a session cookie with `SameSite=Lax`), a vote link, and a
  comment form whose `POST` 302-redirects to the page that now shows the
  comment; images of each format; a cross-origin image host. A test drives
  `clazel --headless` and the kernel through the whole flow and compares the final buffer to
  a stored screenshot, exactly.
- **Hostile inputs**, through a real sandboxed renderer with the memory
  bound and a time limit: a DEFLATE stream that expands 1,000× and one that
  expands without limit; PNGs whose IHDR claims 2^31 × 2^31, whose IDAT is
  truncated, whose palette is shorter than its indices; JPEGs with
  65,535 × 65,535 SOF, a million restart markers, a progressive scan
  sequence that never ends, Huffman tables that are over-subscribed; GIFs
  with LZW codes past the table, a million frames; WebPs with a VP8 partition
  pointing past the end, VP8L code lengths that build no code, an `ANIM`
  with a million frames; every vendored image mutated a thousand ways; a
  million `img` with one URL; a thousand with different ones; a form with a
  million fields; a 1 GiB `textarea`; a `POST` redirect loop; a 307 chain
  that would resend the body twenty times (stopped at Fetch's limit of 20);
  a cross-site form `POST` (no `Lax` cookie sent, checked on the wire); a
  cross-origin `img` pointing at an intranet HTML page (ORB empties it).
- **Phases 2 to 5 kept**, with the new schema.

### 6.21 Status and README (S)

`cargo xtask report --write` locally; README's Phase 6 note (formats,
what is not decoded, forms in scope, the memory numbers, the `unsafe` count
if 6.12 added calls); this file's Status table and exit criteria one by one;
ROADMAP.md; VERIFICATION.md's tier lists (DEFLATE and forms' data at tier 2
if 6.0 takes them).

## Order of work

```
6.0 decisions (a) to (j)
6.1 data ─┬─> 6.2 deflate ─> 6.4 PNG ─────────────────────────────┐
          ├─> 6.3 shape ─┬─> 6.5 JPEG baseline ─> 6.6 progressive ─┤
          │              ├─> 6.7 GIF ──────────────────────────────┤
          │              └─> 6.8 WebP lossless ─> 6.9 WebP lossy ──┤
          └─> 6.13 form data ─> 6.14 encodings, submission ────────┤
6.10 image items ─> 6.12 GPU images ───────────────────────────────┤
6.11 layout: natural sizes, backgrounds ────────────────────────────┤
6.3 shape ─> 6.11a static SVG (HN's logo and arrows) ───────────────┤
6.15 controls (after 6.0(f)'s message) ─────────────────────────────┤
6.16 bodies in fetch + kernel ──────────────────────────────────────┤
6.17 image fetches, ORB (after 6.0(e)'s message) ───────────────────┴─> 6.18 pipeline ─> 6.19 animation ─> 6.20 demo ─> 6.21
```

6.11a, needed by the exit because HN's logo and vote arrows are SVG (6.1),
starts once 6.3 fixes the shape. 6.6 (progressive JPEG) and 6.9 (VP8) are not
on HN's pages (6.1), so they may be cut or deferred without losing the exit.

Every item can start once 6.0 is decided: Phase 5's pipeline, window and
kernel are on `main`. The decoders start once 6.3 fixes the shape (PNG also
needs 6.2's exec, not its proof). 6.10, 6.15, 6.16 and 6.17 each change a
tier 2 crate (`clazel-displaylist`, `clazel-ipc`, `clazel-fetch`,
`clazel-kernel`) and land as one pull request each with proofs, mutations
and process tests green, as Phase 5's 5.18 and 5.19 did. Nothing here needs
another item's proof or tier to proceed, only its interface.

## Status

| Item | State |
|------|-------|
| 6.0 Decisions | taken (2026-11-16): decoders at tier 1 by the maintainer; (a) to (j) as recommended, by a Claude session on the maintainer's delegation |
| 6.1 Inventory and test data | built (2026-11-16); docs and data, no crate, nothing proven. `scripts/phase6-inventory.mjs` ran (not in CI) over HN front, item, login and reply pages and one Wikipedia article: HN's logo and vote arrows are SVG, so 6.11a was added; the only raster is `s.gif`. WPT forms, img element and `urlencoded-parser` vendored at `4ad507b2`; no table is generated yet and nothing reads them. Not done: no news site other than HN measured; format suites (PngSuite, libjpeg-turbo, Wuffs, DEFLATE) left to their items, licences recorded in 6.1; libwebp-test-data has no licence and the ITU-T T.83 streams are a gap; no dev-dependencies added |
| 6.2 DEFLATE and zlib | built (2026-11-16) as the new crate `clazel-deflate` (tier 0, target 2; shipped dependency `vstd` only; `miniz_oxide` 0.9.1 and its `adler2` are dev-dependencies, class `test`). Spec and contracts committed first (rule 3): RFC 1951 §3.2.2 to §3.2.7 and RFC 1950 §2.2 and §2.3 as Verus spec functions of the whole input, ten modelling choices listed at the top of `spec.rs` (the output limit as a stated error, incomplete codes refused as zlib refuses them, HLIT, FDICT refused, fuel for termination, the order of errors); `docs/ERRATA.md` has one entry (§3.2.5's "most-significant bit first" for the extra bits contradicts §3.1.1). The decoder is `Inflater::step(src, dst, window)`: resumable, a 32 KiB window the caller provides, every element read whole or not at all, a 15-bit lookup table per code, the output limit checked before anything is written; it allocates only its three tables, in `new()`. Proven (Verus 0.2026.10.04, WSL, **37 verified, 0 errors**, the whole crate): every spec function terminates; `adler::update` and `adler::adler32` equal the spec's Adler-32 for every input (no overflow); `theorem_output_bounded` (about the spec: a successful decode never exceeds the limit); the length and distance tables are chains of consecutive ranges ending at 258 and 32,768; the RFC's worked code examples evaluate to the codes it lists; `code_usable` and the zlib header checks evaluate as they should. Mutations: 88 of the spec, all 88 killed with certificates Verus checks (every length and distance base, every extra-bit count, the `code_usable` rules, the zlib header checks). Tested (`tests/conformance_deflate.rs`, 13 tests, all pass): Wuffs' streams and its six artificial corner cases (commit `b36a81d`); a differential against `miniz_oxide` over 33,979 streams (mutated, truncated, hand-made error streams): no difference; the decoder equal to a naive Rust transcription of the spec (`tests/model`) on 12,119 streams with every error kind; every chunk and output-room size equal to the whole-input decode; the limit exact and a 64 MiB stream of zeros stopped at 1 MiB; hand-made streams for every length and distance code, stored, dynamic and each `Error`. Not done: **`Inflater::step`, `Table::build` and `Table::lookup` are not proven**, so `theorem_chunking_irrelevant`, `theorem_inflate_total` and `theorem_huffman_table` are statements in `contract.rs` (`chunked_ensures`, `build_table_ensures`), not theorems; no independent transcription (`independent.rs`); no mutation of the block loop, the dynamic header or the Huffman steps (the compute engine's recursion limit stops a certificate that evaluates a stream through the fixed code); no gzip (6.0(h), later); no Kani; Miri was started and stopped (the bomb test alone took 208 s of the 300 s allowed), so its strides are not measured; `cargo xtask verify --part crate clazel-deflate` in WSL passed every step (Verus 37 verified, 88 mutations killed, conformance) except writing its metrics file (git cannot read this Windows-linked worktree from WSL); full `verify --changed` (every crate, since `xtask/` changed) and CI not run, so the tier stays 0 |
| 6.3 Image buffers and the decoder shape | built (2026-11-16) as the new crate `clazel-image-shape` (tier 0, target 1; no dependencies; separate from `clazel-image` to avoid a cycle and tier 0 code under tier 1 decoders). The `Decoder` trait (`decode_config`, `work_len`, `start`, `step`, `inv`), `Buffers`, `Config`, the 6.0(j) limits with a checked `rgba_len`, `premultiply`, the `decoder_step_harness!` Kani template and a toy raw-format decoder instantiating it. Proven: 6 Kani harnesses run in WSL, 6 pass (size function over every `u32` pair; premultiplication over every channel and alpha, in place over 3 pixels and a partial one; the template on the toy at images up to 2 by 2 and chunks up to 8 bytes; a mutated toy step fails it). Tested: 14 unit tests (toy at every chunk size, limits, exact rounding). Not done: no real decoder yet; `FrameDone` carries no frame timing (GIF, APNG and WebP add it per 6.0(d)); the template is untried from another crate (6.7 ran it: it works, see 6.7); full `cargo xtask verify` and CI not run, so the tier stays 0 |
| 6.4 PNG | built (2026-11-17) as the new crate `clazel-png` (tier 0, target 1; shipped dependencies `clazel-image-shape` and `clazel-deflate` only; the `png` crate 0.18.1 and its dependencies are `test` rows). Chunks and CRC-32, IHDR with every Table 11.1 colour type and depth (others refused), PLTE, `tRNS`, IDAT across any number of chunks through `clazel-deflate`'s streaming zlib (behind an `Engine` trait so the proofs can stand in for it), the five filters, Adam7, 1/2/4-bit expansion and 16-bit truncation as `png` does, `gAMA`/`cHRM`/`iCCP`/`sRGB`/`cICP` read and ignored, and APNG `acTL`/`fcTL`/`fdAT` with every frame composited by dispose and blend; every choice the standard leaves open is listed in `lib.rs` (the work buffer holds a canvas copy, so a still PNG costs twice its pixels; every chunk's CRC is checked). PngSuite (2017-07-19 archive, 176 files, vendored with an xtask converter) differential against `png`: 176 of 176 (14 `x*` files refused by both, 162 exact RGBA8); chunking 176 of 176; 9,720 mutants no panic, none accepted by ours and refused by `png`; 1,080 generated images, 60 `png`-encoder streams and 600 random APNGs exact; 180 + 25 hand-made stream cases. A `png` 0.18.1 fault found and worked round in the test (interlaced APNG frames narrower than the canvas are written with the canvas's stride; not reported upstream). **Proven (Kani 0.68.0, `cargo kani -p clazel-png`: 39 successfully verified harnesses, 0 failures; each run alone in at most 380 s and 3.4 GB on a loaded Mac, 42 minutes one after another; the README has the table with bounds, times and memory):** `paeth_is_the_spec`; `unfilter_any` (every filter over rows up to 16 bytes, `bpp` 1 to 8, as `filter_bpp()` is `.max(1)`); Adam7 for every width and height to 2^14 as three harnesses (every pixel in exactly one pass at the position the pass gives back, every pass pixel in the image, a non-interlaced image is one pass) and `adam7_axis_split` (the counts along one axis split as the passes split the pixels, every length to 2^31); `sample_and_rgba_any`; `crc_update_any`; and **the step function in parts**, over any state with the invariant on a 2 by 2 canvas, any buffers and an input up to 2 bytes, with an engine that does anything its contract allows: `advance` in each phase and each kind of chunk (16 harnesses), `begin_frame_any`, and the zlib loop of the image data as `engine_round_any`, `unfilter_row_any`, ten `place_row_*` (one per colour type and blend operation), `next_row_any` and `round_end_any` (`feed` is a loop of `feed_once`, which is the engine's call, `finish_row` when the scanline is full, and `round_end`; only `next_row` of `finish_row`'s three parts changes the state). The split replaces the four written harnesses that gave no verdict or failed (`control_any`, `data_any`, `feed_any`, `finish_row_any`) and comes with building each state with the phase a constant (a symbolic phase kept every phase's code in the formula: 10 GB without a verdict became 0.4 GB and 11 seconds). Kani found `state_inv` too weak in the gather phase (a chunk with more data than gathered, IHDR in a frame in progress); strengthened, tests unchanged. Written but **not harnesses** (comment blocks in `proofs.rs`): `adam7_sizes_add_up` (no verdict in 25 minutes with three solvers, nor split by residues in 10; the axis counting is proven, the sum is algebra, argued) and the template on the whole step. **Not one harness:** `advance` in the image-data phase with a frame idle or active, because `feed`'s loop cannot be unrolled; it is covered by `advance_data_finished` (`advance`'s own lines of that arm) and the parts above, composed by the structure of the code (argued). So every Tier 1 statement the plan names now has passing harnesses, with those two arguments; CI's full run has not happened, so the tier stays 0. Miri: a first full run passed all 26 tests but five exceeded 300 s (850 s at most; Miri was about 25,000 times slower than native, not 1,600), so the strides were cut and **not re-measured**. Not done: Tier 1 claim, `cargo xtask verify` (full) and CI, the `verify --changed` result is in the PR; no colour management; looping and frame timing policy are 6.19's; `clazel-deflate`'s step is not proven, so the PNG proofs are relative to the `Engine` contract; the tier stays 0 |
| 6.5 JPEG: baseline | built (2026-11-17) as the new crate `clazel-jpeg` (tier 0, target 1; only dependency `clazel-image-shape`; no new dependency rows). T.81 sequential Huffman decoding (SOF0 and SOF1 at 8 bits; DHT, DQT 8 and 16-bit, DRI and restart markers, interleaved and one-scan-per-component, 1, 3 or 4 components at sampling factors 1 to 4), libjpeg-turbo's `jidctint` IDCT and "fancy" upsampling (h2v1, h2v2, h1v2; replication otherwise), JFIF YCbCr, Adobe APP14 (RGB, inverted CMYK, YCCK), EXIF Orientation only; progressive (SOF2), arithmetic, lossless, 12-bit and 2-component files are refused with `Unsupported`. Nine listed choices in `lib.rs`. Resumable one byte at a time; the work buffer is the worst case for the config (four padded planes), a listed choice. Tested: libjpeg-turbo `testorig.jpg` and `testimgint.jpg` plus a 132-file corpus made by `scripts/jpeg-reference.py` (every sampling ratio, restart intervals, non-interleaved scans, gray, YCbCr, RGB, CMYK, YCCK, SOF1, 16-bit tables, sizes 1 by 1 to 227 by 149, EXIF orientations 1 to 8) against libjpeg-turbo's output: **134 files, 2,065,288 samples, every one exact (tolerance 0)**, difference histogram printed; changing an IDCT or upsampling constant by one fails it; arithmetic and 12-bit files refused; every file at chunk sizes 1 to 4096 equal; 2,680 byte mutants never panic; 15 hand-made and 24 unit tests. **The reference is libjpeg-turbo 2.1.5 (Ubuntu's, through ctypes), not the pinned 3.2.1**: building 3.2.1 was refused by the session's permission system. Proven: 12 Kani harnesses run in WSL (Kani 0.68.0), 12 pass: bit reader, Huffman decoding over **any** table with the invariant, one bit of a block over any state and tables, the two IDCT passes (composed: `idct` never overflows for every `i16` block and `u16` quantizer), the range limit over every `i64`, upsampling over every geometry up to 16 by 16, orientation over every size to 2^14, YCbCr over all 2^24 inputs, CMYK over all 2^32. **Not proven**: `Table::build` (the model checker's memory grew without bound), the marker state machine, the entropy pipeline and `step` (harnesses over the whole state did not finish and were removed), so `Jpeg::state_inv` being kept is argued, not checked. Miri: the 24 unit tests ran under Miri (none over 5 s); the conformance suite has stated strides (`MIRI_*` in the test, sized by native timing with the Miri branch forced: 0.02 s, 0.03 s, 0.01 s) but **was not completed under Miri**: the shared WSL machine kept dying. ITU-T T.83 streams not used (the gap 6.1 recorded); `zune-jpeg` not added. Not done: `cargo xtask verify --changed` (fails from WSL in a worktree), CI, so the tier stays 0; not benchmarked or optimised (entropy decoding is one bit per call); a stream without EOI never completes |
| 6.6 JPEG: progressive | built (2026-11-21) in `clazel-jpeg` (tier 0, target 1, unchanged; no new dependency rows). T.81 Annex G: SOF2, DC and AC first scans, DC and AC refinement, spectral selection, successive approximation, EOB runs, restart intervals, interleaved DC scans; one bit per call in `src/progressive.rs`, resumable at any byte. The whole coefficient plane is kept as `i16` in the work buffer and the inverse DCT runs in place at EOI (2 bytes per padded sample plus one block row, not 3); **`work_len` is `6 * (w + 31) * (h + 35)` for a progressive JPEG** (about 387 MiB at 2^13 by 2^13) and stays four planes of `(w + 31) * (h + 31)` for a sequential one: the config now carries a `Coding` (`clazel-image-shape`), set by `decode_config` from the frame marker, and a frame whose marker differs from it is refused; a 4-component frame at full resolution does not fit and is refused (`Unsupported`). Hostile input: more than 100 scans, a frame over 2^26 pixels, and coefficients over the buffer are errors, not work. Tested: **654 progressive files, 650 exactly equal to libjpeg-turbo (9,358,872 samples, difference 0), 4 refused as above**: `jpegtran -progressive` (libjpeg-turbo 2.1.5, via `scripts/jpeg-progressive.py`) copies of every one of 134 baseline files in five scan scripts (libjpeg default, with restarts, libjpeg-turbo's own `test.scan`, spectral selection only, successive approximation of DC and AC), each checked by the script to decode in libjpeg-turbo as the baseline original; chunk sizes 1, 5, 4096; 1,968 byte mutants never panic; hand-made streams for DC and AC refinement, EOB runs, header errors, 5,000 scans, huge sizes. Written, **not run: 5 Kani harnesses** (one per scan kind: `prog_dc_first_bits`, `prog_dc_refine_bit`, `prog_ac_first_code`, `prog_ac_refine_code`, `prog_ac_refine_correction`; each in one concrete stage with the rest symbolic; not run because the machine is memory-constrained, so unchecked even for compilation under `cfg(kani)`) and `cargo xtask verify`; CI's proof jobs need `full-verification` approval, so the tier stays 0. The Kani-verified claims of 6.5 do not cover this code. Reference is libjpeg-turbo 2.1.5 (as 6.5), not 3.2.1; no new dev-dependency. Not done: progressive CMYK at full resolution, block smoothing of incomplete images, progressive display of partial scans, the T.83 streams |
| 6.7 GIF | built (2026-11-16) as the new crate `clazel-gif` (tier 0, target 1; only dependency `clazel-image-shape`; `gif` 0.14.2 and its `weezl` are dev-dependencies, class `test`). GIF89a (GIF87a too, pinned: W3C copy, SHA-256 in `lib.rs`): header, screen, global and local colour tables, image descriptors, interlacing, variable-code-size LZW (clear, end, full table keeps decoding: the "deferred clear", with the Appendix F text quoted where it is silent), the Graphic Control Extension, every other extension skipped by sub-block sizes, the trailer; **every frame composited** with the previous frame's disposal (none, keep, background to transparent, previous from a saved canvas), `Gif::frame()` with delay, disposal and rectangle (on the decoder, the shared `Decoder` trait is unchanged); ten listed choices in `lib.rs`. The work buffer is 17,920 bytes plus a copy of the canvas. Proven: 7 Kani harnesses run in WSL (Kani 0.68.0), 7 pass: `control_byte_any` and `data_byte_any` (one byte in every phase of the state machine, for any state with the invariant and any buffer contents, canvas 2 by 2, LZW at 3 bits), `lzw_any` and `lzw_code_any` (LZW over **any contents** of its three arrays, 3 and 4 bits; `lzw_code_any` found a real mistake in my first statement of the invariant), `sink_put_any`, `interlace_row_any` (every `u16` height) and `interlace_covers_frame` (every size up to 4 by 4); a mutated `Lzw::add` fails `lzw_code_any`. Statements were committed first (with stubs), then changed once: the template `decoder_step_harness!` **works from another crate** but on the whole `step` CBMC passed 6 GB after 5.5 minutes on an 8 GB machine, so that harness is not in the crate and `step`'s own statement (keeps `inv` over several bytes, `consumed`) is argued from the two byte harnesses in the README, not proven; LZW is proven at 3 and 4 bits, not 12 (the code is generic over the size). Tested: 31 Wuffs GIF files (`tests/data/wuffs-gif*`, commit `b36a81d`, through a new converter in `xtask/src/testdata/wuffs_gif.rs`) against `gif` 0.14.2, **every frame's composited RGBA exact on 25, 6 differ in listed choices** (empty palette, no frames, no or too little pixel data, a zero-width frame, garbage LZW after the last pixel), each named with its reason; every file at chunk sizes 1 to 4096 equal; 9,653 byte mutants never panic; 62 hand-made GIFs (disposal 1 to 3, transparency, interlacing at every height 1 to 40, a real LZW encoder with and without a clear at a full table); `s.gif`. Miri: 8 tests in 291 s, none over 90 s (stride in the test header). Not done: full `cargo xtask verify` and CI not run, so the tier stays 0; the NETSCAPE2.0 loop count is not read (6.19); animation policy is `clazel-image`'s |
| 6.8 WebP: container and lossless | built (2026-11-19) as the new crate `clazel-webp` (tier 0, target 1; only dependency `clazel-image-shape`; `image-webp` 0.2.4 with `byteorder-lite` and `quick-error` are dev-dependencies, class `test`). RFC 9649 (pinned, SHA-256 in `lib.rs`): RIFF, `VP8X`, `ANIM` and `ANMF` with **every frame composited** (disposal, blending; `Webp::frame()`), `ICCP`/`ALPH`/`EXIF`/`XMP `/unknown chunks skipped, `VP8 ` recognised (its size read by `decode_config`) and refused with `Error::Unsupported` (item 6.9); VP8L: the four transforms (predictor with its fourteen modes, colour, subtract green, colour indexing with pixel bundling), colour cache, meta prefix codes, simple and normal code length codes, LZ77 backward references with the distance map; twelve listed choices in `lib.rs`. The lossless decoder is a byte-at-a-time machine of atomic actions over caller-owned buffers; prefix codes are decoded without tables; the work buffer is about 11.6 kB plus 12 bytes per 4 by 4 block, 6.4 kB per prefix code group held (at most 1,024) and, for an animation, the canvas again. Kani: **69 harnesses**, not yet green on CI (prefix code construction over any code lengths, decoding, the distance map, every predictor mode, each inverse transform over any row of 3 pixels, colour indexing at every bundling width in place, blending, and the step function in parts: one atomic action of the lossless decoder per phase, finishing an image of each role and transform kind, one container byte per phase; the whole `step` is not attempted, as for GIF). The first CI run lost its runner after two hours on the original 16, whose step harnesses had a symbolic phase; split, and each run on its own locally under Kani 0.68.0 with a 4 GB cap, they found gaps the invariants and the decoder now close (see the commits). Tested: 22 unit tests; Wuffs' WebP files (`tests/data/wuffs-webp`, commit `b36a81d`, through a new converter in `xtask/src/testdata/wuffs_webp.rs`; libwebp's own vectors have no licence, so they stand in) against `image-webp`: **all 11 lossless files exact** (up to 1,165 by 859), the animation exact on its first frame and within 1 per channel on blended ones (listed: `image-webp` rounds blending more precisely than libwebp's formula), 2 lossy files refused; every file at chunk sizes 1 to 4096 equal; 1,440 byte mutants never panic; a VP8L encoder written for the tests makes 531 images (ten orders of transforms, every predictor mode, bundling at every palette size, caches of 0 to 11 bits, meta prefix codes, references of every distance code) that decode to exactly the source and agree with `image-webp`; an animation of five frames against a compositor written in the test; twelve malformed inputs. Miri: every suite runs a stride sized to about 0.002 s native (stated in the test headers); not run here. Not done: lossy VP8 and `ALPH` (6.9); the loop count and frame timing (6.19); more than 1,024 prefix code groups; CI's Kani run and full verification not green yet (CI's Miri job for the crate passed), so the tier stays 0 |
| 6.9 WebP: lossy (VP8) | built (2026-11-21), in `clazel-webp` (tier stays 0, target 1; no new dependency). RFC 6386 (pinned with its SHA-256 in `src/vp8/mod.rs`), key frames: boolean decoder (§7), frame header (§9), mode and token trees (§11, §13), dequantization (§14.1), inverse WHT and DCT as the RFC's code (§14.3, §14.4, 16-bit storage), intra prediction of every mode (§12), loop filter simple and normal (§15), whole-frame reconstruction then filtering; YUV to RGB is libwebp's fixed-point conversion with fancy upsampling (listed choice, constants cited); `ALPH` decoded (every filter, raw and lossless-compressed, reusing the crate's VP8L through a headerless start). The `VP8 ` chunk is gathered whole (in the frame's RGBA buffer, or 1 kB of work space if small; over 4 bytes to the pixel is `Unsupported`) and decoded in the call that gives its last byte; the work buffer grows by about 2.6 bytes per pixel for a file whose config says `Coding::Lossy` (a simple `VP8 ` file or any `VP8X` file; a simple `VP8L` file is `Coding::Base` and keeps the 6.8 size, and a `VP8 ` chunk under it is refused). Tables extracted from the RFC's text by script. Four RFC errata in `docs/ERRATA.md` (not reported upstream). Tested: all 14 of Wuffs' lossy files (`tests/data/wuffs-webp`, 12 added) **exactly equal to `image-webp` 0.2.4**, including the one with an `ALPH` (gradient filter, lossless-compressed); 399 of 400 frames written by a VP8 writer made for the tests (every mode, segments in both modes, both filters, 1 to 8 partitions, skips, probability updates, sizes off 16) exactly equal, the 400th refused as over 4 bytes to the pixel; 48 alpha files (4 filters, raw and compressed, 6 sizes) equal; `ALPH` edge cases; mutants never panic. libwebp's own vectors have no licence and no `dwebp` output is stored, so the reference is `image-webp`, not libwebp. Kani: 6 new harnesses (boolean decoder, every subblock mode, whole-block modes at the edges, the three loop filters, both transforms, YUV to RGB) and 2 container harnesses, **written but not run** (CI's proof jobs need `full-verification` approval); the whole-frame decode is not harnessed. Not done: Miri not run here; `image-webp` differs from the RFC on 16-bit overflow (avoided in the writer); tier stays 0 |
| 6.10 Display list: image items | built and proven locally, not on `main`. `clazel-displaylist` is at tier 2 on `main` (raised there before this item); its tier 2 claim covers these items only once CI's full run on this pull request is green. Tags 7 to 9 (upload, draw, free image) in the spec, with contracts committed before the code; the encoder, decoder and validator proven (Verus: 131 verified, 0 errors); `theorem_validated_bounds` extended to image bytes and to every image draw's source inside its image; 130 of 130 mutations killed by a theorem with certificates (51 new); `independent.rs` extended and proven equal, but written by the same session as the spec, not blind; conformance tests extended (second decoder and validator, 110 hand-built cases, random and hostile bytes). `clazel-gpu` refuses image items until 6.12. Not done: CI's full verification; the 2^28 image budget and the 2^27 + 2^28 list limit are unmeasured; `clazel-gpu`'s `LIST_MAX` (256 MiB) is below the new list limit (384 MiB) and is for 6.12 to settle with the second-channel decision |
| 6.11 Layout: natural sizes and background images | built, tier 0 (unchanged), not on `main`, CI not yet run. `clazel-layout`: an `images::Images` map (the interface 6.18 fills: an `img` by node id, a background by absolute URL; states pending, sized, ready with a display list image id, broken); `img` natural size and ratio (CSS 2.1 §10.3.2, §10.6.2 with ratio); a broken `img` with `alt` an inline box of the text (HTML §15.4.2); `Item::Image` from paint for an `img` and for tiled `background-image` layers (`repeat`, `space`, `round`, `no-repeat`, position, size, origin, clip, layers, the canvas). `clazel-style`: the `background-*` longhands computed, `url()` made absolute against its sheet. Tests: 10 layout image tests, 7 tiling tests, 4 style tests, native; no Kani, Verus or Miri run locally (CI). Not done: WPT reftests (they need decoders and `browse --headless`; the classifier now counts background position, size, repeat, origin and clip as in the subset); `srcset` densities, 6.18's; images on inline boxes and table tracks; three- and four-value `background-position`; `background-attachment: fixed`; gradients; the alt text's icon; the renderer does not draw `Item::Image` yet (6.18) |
| 6.11a Static SVG for HN's files | built (2026-11-16) as the new crate `clazel-svg` (tier 0, target 1; only dependency `clazel-image-shape`; `tiny-skia` 0.12.0 and 3 small crates are dev-dependencies, class `test`). Our own XML tokenizer, the path grammar (`M L H V Z`, implicit `lineto`), SVG 2 9.3, 8.2, 13.4 section numbers pinned to the 06 October 2026 CR snapshot, hex `fill`, non-zero fill, `xMidYMid meet`, an integer rasterizer (16 sub-scanlines, exact horizontal coverage), the `Decoder` implementation drawing at the `Config`'s size; everything else refused, and the document read twice so nothing is drawn in part; eleven listed choices in `lib.rs`. **Two findings against the plan's text:** `triangle.svg` is `width="32" height="32"` with `viewBox="0 0 32 16"` (intrinsic 32 by 32, drawn 10 by 10 at HN's `background-size: 10px`, not 32 by 16), and clipping is to the image, not the `viewBox` (clipped to the `viewBox` the arrow would be a 5 px strip; choice 5). Proven: 10 Kani harnesses run in WSL (Kani 0.68.0), 10 pass (number reader, attribute readers, rasterizer pieces over edges of any `i32` coordinates and any buffers; a span adds exactly its overlap), at small bounds listed in the README. Tested: 22 unit tests and 18 conformance tests: HN's two files (vendored with provenance) at 17 sizes against tiny-skia (solid pixels exact, anti-aliased within 43 of 255, ours within 6 of a 16x-averaged truth), every chunk size equal, a refusal corpus with the buffer untouched on error, 25,422 byte mutants; Miri: 40 tests pass in 540 s (`verify --part miri clazel-svg`), the tiny-skia comparison skipped under Miri. **Not done: Kani harnesses for the tokenizer, the path reader, the viewport transform, `crossing` and the whole `step` (written, did not finish: unwinding and memory limits, 64-bit solver time), so tier 1 is not claimed and the tier stays 0**; the reference is tiny-skia, not resvg, so the tokenizer has no independent comparison; no browser comparison; `clazel-image` dispatch not built; full `cargo xtask verify` and CI not run (`verify --part crate clazel-svg` passes its static checks, Kani and conformance, and then fails to write its measurements because the worktree's git pointer is a Windows path that WSL cannot read) |
| 6.12 GPU process: images | built, **not run on Metal, nor on a real GPU, nor in the sandbox; not on `main`**; `clazel-gpu` stays at tier 0 (target 0), no tier raised. Image upload, draw and free (tags 7 to 9) in the batching, the fake backend, the software reference, the Vulkan backend and the Metal backend; the fragment shader filters (nearest or bilinear, clamped to the source rectangle) in 32-bit arithmetic over an image store held as a storage buffer, in the **same one pipeline** (made at start, so a warm-up frame already compiled it): **a listed choice that departs from the plan's wording**, which says a textured-quad pipeline sampling an RGBA8 texture: no texture, sampler or descriptor type was added, so no `clazel-sys` call, no audit and no `unsafe` (`clazel-sys` is untouched), at the cost of doing a texture unit's work in the shader and of one buffer holding every live image (up to 512 MiB; a driver may refuse a buffer that large, and nothing here measured a store above 64 MiB). The image store is the glyph atlas's design (`src/images.rs`: bump allocator, compaction, CPU copy kept for it). `LIST_MAX` is now `clazel_displaylist::spec::MAX_LIST_BYTES` (384 MiB), a test pins it, and `hostile_graphics.rs`'s `GPU_LIMIT` comment states that images are outside its 1 GiB and that a worst-case image list is about 1.4 GiB, unmeasured. Tests: hand-worked pixels through the fake backend, the new scenes (`images`, `image-frames`, `image-store`) against the exact software reference on every backend (GPUs within one level), the reference's pixels stored in `tests/pixels-reference/`; **no pixels stored for lavapipe or Metal** (none could be drawn here), so those two comparisons skip for the image scenes until someone blesses them. Measured: `tests/upload_measure.rs` prints the cost of a 4096 × 4096 upload through the list socket on each OS (read CI's log; a Windows optimised build measured about 23 to 29 ms over loopback TCP, more than a 16.7 ms frame). **The second channel is not built; deciding it is the maintainer's.** **Direct3D 12 does not take images** (its backend refuses them: the HLSL and its DXBC, which only `vkd3d-compiler` makes, are unchanged). Not done: CI's run of any of this; the Linux sandbox with an image store |
| 6.13 Forms: the form data set and form owner | built in part (2026-11-16) as the new crate `clazel-forms` (tier 0, target 2; dependencies `vstd` and `clazel-dom`; `clazel-treebuilder` a dev-dependency). **Spec** (`src/spec.rs`, HTML at commit `0793d3d8`, 2026-11-14; the item's † numbers were §4.10.17.3 and §4.10.21.4, the real ones are §4.10.18.3 and §4.10.22.4) and **contracts** committed first, then the code: "form owner" and "reset the form owner" (the parser's association, else the nearest ancestor `form` or the `form` attribute's ID), "constructing the entry list" steps 1 to 5.11 for `input` of every state, `button`, `select` (single and multiple, the "list of options", option disabled), `textarea` (newline normalization, hard wrapping), disabled (with the `fieldset` and `legend` rule), `datalist` ancestors, the submitter, image coordinates, `_charset_`, `dirname` (ltr), value sanitization; control state is a side table keyed by node id. **Proven** (Verus, run in WSL): every public function of `src/exec/` equals its spec function for every well-formed arena, 162 verified, 0 errors; the tree order and `list_of_options` are explicit-stack walks; lemmas that every node of a tree order has the form's root as root, and that every entry has a non-empty name. **Mutations:** 20, 10 killed with certificates (the string algorithms) and 10 killed incidentally (the entry list's steps; they need a concrete `Document` for a certificate). **Tested:** 20 hand-made cases through the tree builder; WPT `form-submission-0`: all 32 pages need script, so the markup and tables of three pages are read from the vendored files and run, 19 of 19 checks pass (`clazel-conformance:` line). Not done: `independent.rs` covers only the string algorithms (`src/independent.rs`, 27 verified, 0 errors: ASCII lowercase, strip newlines, strip whitespace, normalize newlines, non-negative integer parsing, the base-ten string; written beside `spec.rs`, so independent in formulation, not in author), not the form owner, `disabled` or the entry list; the 10 document-dependent mutations have no certificates, because `compute_only` panics on the byte-string literals (`b"input"@`) those steps read and Verus cannot prove `b"input"@` equals a `seq!` (the spec would need sequence literals and the executable code arrays of known contents); `option` text without a `value` attribute is the table's (HTML-aware text content not transcribed); the selectedness setting algorithm and radio groups are the caller's; no `File` entries; per-control ancestor walks cost controls times depth on a very deep tree (README); Miri on this crate's tests (cargo +nightly-2026-08-21 miri test -p clazel-forms, 2026-11-23): 42 tests pass, the slowest 84 s; full `cargo xtask verify` and CI not run, so the tier stays 0. 6.14 and 6.15 add to this crate |
| 6.14 Forms: encodings and the submission algorithm | built in part (2026-11-16) in `clazel-forms` (tier stays 0, target 2; new dependencies `clazel-encoding`, `clazel-percent`, `clazel-url`; `form_urlencoded` a dev-dependency, already in `docs/DEPENDENCIES.md`). **Spec** (`src/submit/spec.rs`: HTML at commit `0793d3d8`, URL and Encoding at the commits `clazel-url` and `clazel-encoding` pin; the item's † numbers were §4.10.21.3, .6 and .8, the real ones are §4.10.22.3, .9 and .8, URL §5.2) and **contracts** committed first: URL's `application/x-www-form-urlencoded` serializer (UTF-8, and the single-byte encoders with `%26%23N%3B` for an unencodable code point), "convert to a list of name-value pairs", `text/plain`, `multipart/form-data` (RFC 7578 parts, boundary a parameter), "picking an encoding for the form", and the submission algorithm's steps to a navigation request: method, enctype, action (empty means the document URL, resolved against the base URL by `clazel-url`), the scheme table, "mutate action URL", "submit as entity body", submit button `formaction`/`formmethod`/`formenctype`/`formtarget`, target (this tab or a new one), `rel=noreferrer`. Output: a plain value (`ExecOutcome`: URL record, GET or POST, body and content type, tab, no-referrer). **Refused, listed:** `dialog`, `mailto:`, `javascript:`, schemes outside the table, encodings with no encoder (multi-byte legacy until Phase 8, x-user-defined), a bad boundary. **Proven** (Verus, WSL): every public function of `src/submit/exec/` equals its spec function (`submit_exec` for every well-formed arena), 256 verified, 0 errors in this crate; lemmas that the serializer's output is ASCII and that scalar value strings stay so. `clazel-encoding`'s `run_encoder_handler` was made `pub` (no proof change; its 365 proofs re-run, 0 errors). **Mutations:** 21 new (41 in all): 7 killed with certificates, 14 killed incidentally (single-byte table, label table, byte-string literals and the document-dependent steps need what `compute_only` cannot evaluate); 0 survived (`cargo xtask mutate clazel-forms`). **Tested:** 15 hand-made submission cases; WPT `urlencoded-parser` as serialize-then-parse round trips, 35 of 35; `urlencoded2`, `text-plain`, `multipart-formdata` without the `File` calls, 20 of 20 each (11 `File` calls each skipped); a differential test of the serializer against `form_urlencoded` on 5000 random inputs, 0 differences (`clazel-conformance:` lines). The WPT files are copied under `tests/data/wpt-form-encodings/` and converted by `xtask/src/testdata/wpt_form_encodings.rs`. Not done: `independent.rs` covers only the CR LF replacement and the split on ASCII whitespace (`src/submit/independent.rs`, 11 verified, 0 errors; independent in formulation, not in author), not the serializers, the encoding pick or the submission algorithm; the 14 incidental mutations still have no certificates (byte-string literals, as in 6.13, and tables `compute_only` cannot evaluate); validation, events, `dialog` and history handling (6.15, 6.16); the action URL's own query is parsed in UTF-8 whatever the document encoding; the boundary's absence from the body is not checked; Miri passes (see 6.13: 42 tests in the crate); full `cargo xtask verify --changed` and CI not run, so the tier stays 0 |
| 6.15 Controls: painting, focus and editing | built (2026-11-21), **tier 0**, CI not yet run. New crate `clazel-forms-edit` (plain Rust, no spec or proof: 6.0(b) puts editing at tier 0; dependencies `clazel-dom`, `clazel-forms`, `clazel-layout`, `clazel-style`, all ours) and, in `clazel-layout`, `controls.rs` plus `paint_with_controls` (`paint` is unchanged) and `select` as a replaced list. **Built:** the fixed look from rectangles and glyph runs (text field, `textarea`, checkbox with a check mark of squares, radio disc of one rectangle per row, push buttons, `button` chrome, `select` as an in-content list, greyed disabled, 2px focus ring); focus by click and Tab or Shift-Tab in tree order with numeric `tabindex` (positive first, 0 and none in tree order, negative by click only, radio group one stop, wraps); text editing (typed text, caret, Backspace, Delete, arrows, Home, End, selection by Shift and by mouse drag, `maxlength` in UTF-16 units, `readonly`, `disabled`, `placeholder`, `password` as bullets, one-line scroll); `textarea` with soft-wrapped lines and Enter; checkbox and radio-group toggling; `select` click and keys; implicit submission (HTML §4.10.22.2: the default button, the disabled default button, the one-field rule); `required` (§4.10.22.3 steps 5 and 6: the first missing control gets the focus and the form is not submitted; `novalidate`, `formnovalidate`, `readonly`, `disabled` and `datalist` barred); reset buttons; state is `clazel-forms`' control state table, so submission sends what was typed. **Listed choices** (in each module's header): `pattern` and every constraint but `required` ignored; no clipboard, IME, word or line selection, select-all, keyboard movement between radio buttons or type-ahead in a `select`; Up and Down in a `textarea` move by logical line; a `select` is a list of its option count rows (at most 8) or `size` or 4, `optgroup` labels not drawn; a control reset has no event; key codes are the DOM's `keyCode` numbers with Shift as bit 16 of `Input`'s key field, and press, drag and release are **proposed `Input` kinds 3, 4 and 5 that `clazel-ipc`'s schema does not have** (kind 0 is a press and a release), and `TextInput` (6.0(f)) is not in the schema or routed by the kernel either, so the crate takes `Event::Text`; the user agent sheet gives text controls no border or padding, so a one-line field is one line high and its text is drawn under the 1px border. **Tested:** 6 unit tests of the editing state and 32 tests per control through the tree builder, the cascade, layout (`IdFont`, 10px) and `paint_with_controls`, driven by synthetic events and `Input` fields, against 27 stored files in `crates/clazel-forms-edit/tests/golden/` (box tree dumps, one display list, character-grid pixels); `clazel-layout`'s box, flow and paint goldens of the 15 html5lib cases that hold a `select` were regenerated (a select's subtree is now one replaced box). **Not done:** the renderer does not call any of it yet (no `Input` routing, no relayout on edits: 6.16 to 6.20); no spec file, `independent.rs`, mutations or Kani harnesses; no Miri run; no fonts other than the test font were tried for the bullet; `cargo xtask verify` and CI not run, so the tier stays 0 |
| 6.16 The fetch transducer and kernel: navigations with a body | built in part (2026-11-16, kernel part written 2026-11-19, NOT yet verified: awaiting CI proof jobs): `clazel-fetch` and `clazel-ipc` (tiers stay 2, declared before; nothing raised); `clazel-kernel` written but not proven (see the last paragraph of this row). **Spec** (`src/request/spec.rs`, `contract.rs`) and **contracts** committed first (`df3f5afe`); this item's implementation commits change that spec in one place only, adding `body_len_ok(n)` (the size bound as a named predicate, meaning unchanged). `Req` (method, body with content type, initiator, origin redirect-taint); Content-Type and Content-Length (Fetch §4.6 steps 6 to 9, `POST` without a body sends `Content-Length: 0`); `Origin` on a method other than `GET` and `HEAD` ("append a request Origin header", null for no initiator, an opaque one, an https initiator on a non-https URL, or after a redirect that left the origin); the body after the head; HTTP-redirect fetch step 12 (301, 302: `POST` to `GET` without a body; 303: every method but `GET` and `HEAD`; 307, 308 keep both and the body is sent again); the cookie context takes the method's safety and the initiator as the site for cookies. Only `GET` and `POST` are built, a body is at most 16 MiB. The transducer's state holds the `Req`; `start_req` starts any request, `start` is the old `GET`. **Proven** (Verus, WSL, `cargo verus verify` in the crate): the exec request and transducer functions equal their spec functions, 255 verified, 0 errors (dependencies: 2060, 407, 365, 54, 375 verified, 0 errors); `theorem_redirect_method`, `theorem_post_cookies`, `theorem_sends_have_valid_req`, and the earlier theorems (21 connections, wire cookies, jar frame, TLS) re-proven over the new state. **Mutations:** 12 new in `mutations.json`, 5 old ones repaired to the new spec (their `find` text had changed); `cargo xtask mutate clazel-fetch` (run with 85 including four more): 81 killed with certificates, 0 survived; the four others (request context and the redirect step of the transducer) were killed by the example proofs but their certificates time out at 600 s, and tier 2 forbids uncertified mutations, so they are dropped, not counted **Tested:** 27 request and 19 transducer rows evaluated by Verus (`examples_body.rs`); `tests/conformance_post.rs`: 1378 random `GET`/`POST` chains through all redirect statuses against a model of step 12 with rust-url, 1378 of 1378 agree (the model is our reading of the standards, listed); `PUT` and `GET` with a body are refused. **`clazel-ipc`'s `Submit`** (tag 12, renderer to kernel: url, method, content type, body; tag 9 `Navigate` stays the `GET`-only form): spec committed first (`53f80793`), then the codec; Verus 221 verified, 0 errors; example lemma, round-trip tests of three messages and of the largest body that fits, 4 new mutations and 2 old ones repaired (their `find` text had changed): `cargo xtask mutate clazel-ipc`, 102 mutations, 102 killed with certificates, 0 survived. **The body bound is the frame's, not the proposed 16 MiB:** one `Submit` is one frame (1 MiB), so with a URL, method and content type of at most 8192 octets a body of at most 1,040,320 octets fits (`lemma_submit_fits_frame`); larger needs chunking or a larger `MAX_FRAME`, not done. `clazel-kernel` was brought back to compiling and proving against the earlier fetch changes (they had broken it; 866 verified, 0 errors; `lemma_d_kill` needed a spinoff prover and rlimit 60) and covers `Submit` in frame well-formedness; it does **not** handle `Submit`: a renderer's `Submit` decodes and is ignored. An attempt (the request threaded through `begin_navigation`, `submit_request`/`submit` in the spec, Submit branches beside Navigate's in about 25 lemmas) is on the local branch `wip/6.16-kernel-submit` (unpushed, not verified); WSL's service became unreachable whenever the kernel's full proof run was under load, so it was not completed. The kernel has no history or reload, so there is no POST entry to resubmit (the listed choice is moot until it has). **Not done:** the kernel's handling of `Submit`, `theorem_body_from_requester`, `theorem_body_sent_once`, `theorem_address_bar_integrity` and the Phase 2 to 5 theorems restated with `Submit`, `tests/fetch.rs` with a `Submit`, `independent.rs` widened to methods with a body (its correspondence still requires a plain `GET`), Kani/Miri, `HEAD`/`PUT` and other methods; the four mutations dropped for time-outs; full `cargo xtask verify` and CI not run, so no tier changes. 6.16 stays open until the `clazel-kernel` part lands. **Kernel part, written, unverified (2026-11-19):** contracts committed first (`5fa21a9a`: `Event::SubmitTab`, the declassified part of another domain's `Submit`, never produced by the host; `declassified` for `Submit`; statements `body_from_requester_statement`, `body_sent_once_statement`, `redirect_method_statement`, `post_cookies_statement`); then the executable `Submit` (`submit_request_exec`, `begin_navigation_exec` takes the request; the exec frame gate now kills a `Submit` from an uncommitted renderer, as the spec does: found by a native test), `SubmitTab` arms and `lemma_d_submit` through the noninterference lemmas, and `src/body_theorems.rs` with the proofs of the four theorems (`theorem_body_from_requester` over traces with no `SubmitTab`, by the invariant `bodies_step`; `theorem_body_sent_once` as one-step facts: no `Send` when a navigation starts, one `Send` only on `Connected` of a connecting fetch; `theorem_address_bar_integrity` is the existing theorem, whose `Submit` arms are in the WIP lemmas). **None of these has run through Verus**: the proofs were written without it and are sent to CI; expect errors. Native: `tests/fetch.rs` has 10 new tests of `Submit` (34 pass), clippy and `cargo xtask check` clean. **Not done:** the independent transcription widened to bodies; the four dropped mutations; kernel mutations for `Submit`; Kani/Miri runs; the clause that a replaced navigation's connections are gone is left to `theorem_connection_ownership` and `conns_wf`. **CI state (2026-11-21):** the first CI run's only failure was `rustfmt` (`body_theorems.rs`, `tests/fetch.rs`), fixed by formatting; static checks, clippy, tests and Miri for fetch, ipc and kernel passed; the proof jobs (Verus, mutations, Kani) had not run (waiting for the `full-verification` approval), so there is still no Verus output for the kernel part: the kernel proofs, `body_theorems.rs` and the kernel mutations remain unverified. |
| 6.17 The kernel: image sub-fetches and ORB | written (2026-11-21), Verus NOT yet run, tier unchanged (`clazel-fetch`, `clazel-ipc`, `clazel-kernel` stay at 2, nothing raised). Spec and contracts committed first in each crate. `clazel-fetch`: `src/orb/` (Fetch PR 1755 section 2.11, steps 1 to 15 and the MIME type sets; kernel model refuses where the standard needs a JS parser; 8096 octets sniffed, not the plan's 1,024; every 206 refused), exec `safelist_check_exec`, `theorem_orb`, 6 mutations, `tests/conformance_orb.rs` over vendored WPT `fetch/orb` pages that need no script (4 rows of the coverage page follow an older draft, listed). `clazel-ipc`: `FetchSub` (13) and `SubResponse`, `SubBody`, `SubEnd`, `SubFailed` (115 to 118), codec, lemma, 5 mutations. `clazel-kernel`: `SubFetch.sub`, `fetch_start` generalising `fetch_style`, image limits 16 and 4,096, ORB on every sub-fetch end (a refused response is a failure frame), `theorem_orb`, `theorem_subfetch_limits` restated, about twenty lemmas generalised. Native: ipc, fetch ORB and kernel tests pass, clippy and `cargo xtask check` clean. **Not done:** no Verus, Kani or Miri run (proofs, certificates, `compute_only` examples all unchecked: expect errors); `Accept` for images; kernel mutations; `independent.rs`; CORP; ORB at sub-fetch start. Waits for CI `full-verification` approval |
| 6.18 to 6.21 | not started |

**Phase 6: planned (2026-11-16); decisions in 6.0 taken the same day.
Phase 5, which it builds on, is on `main`.**

## Risks

- **Kani's reach on decoders.** Bounded model checking of a whole decoder
  over all inputs does not scale; the plan proves one step over any state
  satisfying an invariant, so the risk moves to the invariant: too weak and
  the harness fails, too strong and it is false of reachable states (which a
  Kani `assert(inv)` after each step in the tests' traces would catch).
  Mitigation: WUFFS' design, which was built for exactly this kind of
  per-step bounds reasoning; small steps; the invariant checked on every
  suite file's trace in tests.
- **VP8 and progressive JPEG are large.** Each is an L item with many
  modes; a slip here delays the exit only if HN serves those formats, which
  6.1 measured: HN serves GIF and SVG only (see "What the exit page needs").
- **Four tier 2 crates change** (`clazel-displaylist`, `clazel-ipc`,
  `clazel-fetch`, `clazel-kernel`), two of them twice (6.0(e) and (f) retire
  and add messages). Phase 5's open tier raises touch some of the same
  crates' evidence, so the order of those pull requests matters; each lands
  alone, green.
- **Upload bandwidth.** Decoded images are large; copying them through the
  list socket may be too slow, and the second channel adds audited `unsafe`
  (6.12 measures first).
- **Text input across three OSes.** Characters from the OS's text events
  are platform-specific in each window backend; IME is out, so CJK input does
  not work, listed.
- **The exit is a real site's logged-in flow.** HN can change its forms at
  any time; the fixture is the CI evidence, and the real run is a recorded
  manual check, never automated against the site.
- **Section numbers.** Most HTML and Fetch section numbers here are marked †;
  ORB is a section of Fetch now† and must be pinned.
