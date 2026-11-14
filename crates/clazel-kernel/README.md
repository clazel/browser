# clazel-kernel

The browser kernel of [Clazel](../../README.md): a pure step function
`step(State, Event) -> (State, Seq<Output>)` over renderers, their GPU
processes, the cookie jar, Web Storage and the connections of the
navigations in flight, with the isolation theorems proven about it in Verus.
The host shell (`crates/clazel`) reads frames from sockets, attaches the id
of the process whose socket it was, calls `step` and carries out the
outputs. The kernel has no clock and does no I/O.

The specification is `src/spec.rs` (its header lists every modelling
choice); the theorems' statements are `src/statements.rs` and
`src/noninterference.rs`; the executable kernel is `src/exec/`, proven to
equal the spec (`src/contract.rs`). `Cargo.toml` lists every theorem, and
`cargo xtask check` fails if one is not defined.

## Surfaces, viewports and input (phase-5.md item 5.18)

As decided under 5.0 on 2026-11-09, the GPU path is added **beside**
`Display` and `Show`, which are unchanged (with their theorems) until item
5.26 deletes them. The kernel decides who may draw, for which tab and under
which URL; it carries no pixels and no display lists.

- **Events** `FromGpu { id, bytes }` (a frame from the GPU process paired
  with renderer `id`), `Resize { tab, width, height, scale }` (the host's) and
  `Input { tab, input }` (the user's). **Outputs** `ToGpu { id, bytes }` and
  `Paint { tab, url, title, buffer, width, height }`; `Policy::Gpu` for
  `Spawn`.
- **Messages** (`clazel-ipc`): `Title` (11), `FrameReady` (15), `GpuReady`
  (18), `GpuRefused` (19), `Viewport` (108), `Input` (109), `GpuViewport`
  (114). No tag is reused; `Display` keeps tag 10.

### Decisions (taken here, from the plan's goals; each is also in `src/spec.rs`)

1. **A GPU process is named by its renderer's id.** Every renderer spawn is
   `Spawn { id, Gpu }` then `Spawn { id, Renderer }` in the same step, and
   `Kill { id }` ends both. The host makes the list socket pair at the GPU
   spawn and hands the renderer its end at the renderer spawn, since the
   renderer cannot receive a descriptor later (no `recvmsg` in its sandbox).
   So the GPU process starts with the tab's first renderer, before that
   renderer's first commit: the item says "with the tab's first committed
   renderer", which cannot be met with an inherited channel. A frame from a
   replaced GPU process names no live renderer (ids are never reused) and is
   dropped.
2. **The kernel always pairs; the host's mode starts the process.** Until
   the window exists (5.20 to 5.23) the host runs in text mode, starts no GPU
   process and passes no list socket, and the renderer sends `Display` as
   today. No theorem assumes a GPU process exists or behaves.
3. **A frame larger than the viewport is dropped, not a kill.** The item
   says anything but an allowed `FrameReady` is a disallowed frame (kill).
   A `Resize` that shrinks the viewport races frames drawn at the old size,
   and a resize must not close tabs; so an oversized frame changes nothing
   and gives nothing. A frame before the renderer's first commit, a buffer
   outside the ring, a frame that does not decode, or a message a GPU
   process may not send still kills the pair. `GpuReady` and `GpuRefused`
   change nothing until 5.17c.
4. **The ring has 3 buffers** (ids 0 to 2: shown, drawing, spare). The
   kernel checks only the id.
5. **Viewports are per tab and kept across navigations**; a tab the host
   never sized has a 0 by 0 viewport. A renderer that replaces another on a
   cross-origin navigation gets `Viewport`, and its GPU process
   `GpuViewport`, before its `Commit`. The kernel trusts the host's `scale`.
6. **Titles are per renderer, tagged with its lock.** `Title` (only from a
   committed renderer, as `Display`) replaces the renderer's entry; the
   entry is forgotten when the renderer is killed, exits or is replaced, so
   the table holds at most one entry per live renderer. An entry is read
   only by the renderer with its id and its lock, which lets the
   noninterference proof compare only the observer's titles without a new
   invariant. A same-origin navigation keeps the renderer and its title
   until the new document's `Title`.
7. **`Input` carries every field in every kind** (a click's delta and key
   are zero, and so on), and the scroll delta is a sign and a magnitude; the
   kernel forwards it to the tab's renderer and reads nothing of it.
8. **`theorem_channel_only_own_tab` is stated over ids** (a GPU process is
   started only with the renderer of its id, in the step that spawns both
   with the fresh id; a `ToGpu` goes only to that pair or, on `Resize`, to
   the tab's renderer's GPU process). The first statement also claimed the
   pair's renderer is its tab's current renderer after the step; that
   follows from the fresh id and `renderers_wf`, but needs a frame lemma
   through every navigation path, and was dropped from the statement before
   its proof.
9. **The noninterference theorem** keeps its form and hypotheses: a
   `FromGpu` belongs to its renderer's domain and has no declassified part;
   `Resize` and `Input` are the user's and kept by every purge (with no new
   hypothesis on the trace: a `Resize` or `Input` of a tab that is closed in
   one run and open in the other sends nothing to the observer in either);
   `Paint` is addressed by its tab, `ToGpu` by its renderer id. The relation
   between the runs gains equal viewports and equal titles under the
   observer's locks.

What the kernel cannot prove, because it never sees the bytes: that a
buffer's size matches its `FrameReady`, and that its pixels are those the
renderer's list asked for. The compositor and the child window bound the
first (5.21 to 5.23); the second only concerns one tab's own drawing. Within
one site, a compromised GPU process could show a stale frame under a newer
same-origin URL (listed in the item).

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE).
