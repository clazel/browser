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
| `clazel-image` | 0 (0) | HTML §4.8.4† (img), §4.8.4.3† (srcset), MIME Sniffing §6.1 | format dispatch from the sniffed type, the per-document image list, the decoded pixel budget, premultiplication, frame timing |
| `clazel-forms` | 0 (2 for `data/`, 0 for `edit/`; 6.0(b)) | HTML §4.10.21† (form submission), §4.10.17.3† (form owner), §4.10.5† (input types in scope); URL §5† (urlencoded) | form owner and the form data set, the three encodings, text field editing state |
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

Not yet measured; 6.1 measures it with 5.1's script. From memory†, to be
confirmed: HN's images are `s.gif` (the spacers, a 1×1 GIF, repeated 115
times on an item page), the logo (`y18.svg`† or `y18.gif`†) and the vote
arrows (`triangle.svg`†, possibly as a CSS background). If the logo and
arrows are SVG, the exit needs either 6.0(c)'s S2 or a stated gap; 6.1
settles this before 6.0(c) is decided. HN's forms are `login` and
`comment` (`method="post"`, `application/x-www-form-urlencoded`,
`input type="text"`, `password`, `hidden`, `submit`, and a `textarea`), and
voting is a plain link (`vote?id=…&how=up&auth=…`), which is a `GET`
navigation Phase 5 already follows.

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
it and S2 for exactly the elements HN's files use becomes a new item;
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

### 6.1 Inventory and test data (M)

Run 5.1's script over HN's front page, an item page, the login page and a
reply page, plus a Wikipedia article and a news site, counting image
formats (by sniffed type), sizes, `srcset` use, background images, SVG use,
form methods, enctypes and control types. The answer settles 6.0(c)'s SVG
question. Vendor at pinned commits, with licences: PngSuite; libjpeg-turbo's
`testimages`; ITU-T T.83's† conformance streams if their licence allows,
else a stated gap; Wuffs' `test/data`; libwebp's test vectors
(`libwebp-test-data`†); zlib's and Wuffs' DEFLATE streams; WPT
`html/semantics/forms/`, `html/semantics/embedded-content/the-img-element/`
and `url/urlencoded-parser`. Dev-dependencies as `test` rows in
DEPENDENCIES.md: `miniz_oxide`, `png`, `gif`, `image-webp`, `zune-jpeg`; and
reference outputs from libjpeg-turbo and libwebp generated by a script under
`scripts/` at pinned versions and committed, so CI runs no C.

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

`clazel-image`, module `shape`. One interface every decoder implements, in
WUFFS style: `decode_config` (format, width, height, frame count if known)
from the first bytes; `decode_frame` into a caller-owned RGBA8 buffer the
caller sized from the config, with a caller-owned work buffer whose size the
decoder states as a function of the config; each call takes a chunk and
returns `NeedMore`, `FrameDone` or an error. No decoder allocates after its
config is read. Every decoder exposes `step(state, chunk, buffers)` and the
invariant `inv(state, buffers)` its Kani harness uses. The harness template
lives here and each decoder instantiates it.

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

### 6.5 JPEG: baseline (L)

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

### 6.6 JPEG: progressive (M)

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

`clazel-forms`, `data/`, target tier 2 (6.0(b)). HTML §4.10.17.3† (form
owner, read from the DOM's `form_owner` and the `form` attribute),
§4.10.21.4† "constructing the entry list" for the controls in scope:
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

`clazel-forms`, `data/`, tier 2. URL §5.2† the
`application/x-www-form-urlencoded` serializer (on `clazel-percent`'s set,
with the encoding's encoder from `clazel-encoding`; a page in a multi-byte
legacy encoding cannot submit until Phase 8, listed); HTML §4.10.21.8†
`multipart/form-data` (boundary from the kernel's randomness, passed in;
file entries cannot exist since `type=file` is out) and §4.10.21.6†
`text/plain`; HTML §4.10.21.3† "form submission algorithm" steps from the
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
in a text field submitting its form's default button (HTML §4.10.21.2†
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
6.15 controls (after 6.0(f)'s message) ─────────────────────────────┤
6.16 bodies in fetch + kernel ──────────────────────────────────────┤
6.17 image fetches, ORB (after 6.0(e)'s message) ───────────────────┴─> 6.18 pipeline ─> 6.19 animation ─> 6.20 demo ─> 6.21
```

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
| 6.10 Display list: image items | built and proven locally, not on `main`. `clazel-displaylist` is at tier 2 on `main` (raised there before this item); its tier 2 claim covers these items only once CI's full run on this pull request is green. Tags 7 to 9 (upload, draw, free image) in the spec, with contracts committed before the code; the encoder, decoder and validator proven (Verus: 131 verified, 0 errors); `theorem_validated_bounds` extended to image bytes and to every image draw's source inside its image; 130 of 130 mutations killed by a theorem with certificates (51 new); `independent.rs` extended and proven equal, but written by the same session as the spec, not blind; conformance tests extended (second decoder and validator, 110 hand-built cases, random and hostile bytes). `clazel-gpu` refuses image items until 6.12. Not done: CI's full verification; the 2^28 image budget and the 2^27 + 2^28 list limit are unmeasured; `clazel-gpu`'s `LIST_MAX` (256 MiB) is below the new list limit (384 MiB) and is for 6.12 to settle with the second-channel decision |
| 6.12 GPU process: images | built, **not run on Metal, nor on a real GPU, nor in the sandbox; not on `main`**; `clazel-gpu` stays at tier 0 (target 0), no tier raised. Image upload, draw and free (tags 7 to 9) in the batching, the fake backend, the software reference, the Vulkan backend and the Metal backend; the fragment shader filters (nearest or bilinear, clamped to the source rectangle) in 32-bit arithmetic over an image store held as a storage buffer, in the **same one pipeline** (made at start, so a warm-up frame already compiled it): **a listed choice that departs from the plan's wording**, which says a textured-quad pipeline sampling an RGBA8 texture: no texture, sampler or descriptor type was added, so no `clazel-sys` call, no audit and no `unsafe` (`clazel-sys` is untouched), at the cost of doing a texture unit's work in the shader and of one buffer holding every live image (up to 512 MiB; a driver may refuse a buffer that large, and nothing here measured a store above 64 MiB). The image store is the glyph atlas's design (`src/images.rs`: bump allocator, compaction, CPU copy kept for it). `LIST_MAX` is now `clazel_displaylist::spec::MAX_LIST_BYTES` (384 MiB), a test pins it, and `hostile_graphics.rs`'s `GPU_LIMIT` comment states that images are outside its 1 GiB and that a worst-case image list is about 1.4 GiB, unmeasured. Tests: hand-worked pixels through the fake backend, the new scenes (`images`, `image-frames`, `image-store`) against the exact software reference on every backend (GPUs within one level), the reference's pixels stored in `tests/pixels-reference/`; **no pixels stored for lavapipe or Metal** (none could be drawn here), so those two comparisons skip for the image scenes until someone blesses them. Measured: `tests/upload_measure.rs` prints the cost of a 4096 × 4096 upload through the list socket on each OS (read CI's log; a Windows optimised build measured about 23 to 29 ms over loopback TCP, more than a 16.7 ms frame). **The second channel is not built; deciding it is the maintainer's.** **Direct3D 12 does not take images** (its backend refuses them: the HLSL and its DXBC, which only `vkd3d-compiler` makes, are unchanged). Not done: CI's run of any of this; the Linux sandbox with an image store |
| 6.1 to 6.9, 6.11, 6.13 to 6.21 | not started |

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
  6.1 measures.
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
