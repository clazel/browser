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

## Style sheet fetches (phase-5.md item 5.19)

A committed renderer asks for a style sheet with `FetchStyle { request, url }`;
the kernel fetches it with item 3.6's transducer, the one navigations use,
and answers `StyleResponse`, `StyleBody` frames and `StyleEnd` in one write,
or `StyleFailed`, under the renderer's own `request` id. The renderer
sends `FetchStyle` for each linked sheet (item 5.20, `clazel-renderer`'s
`page/sheets.rs`). The host carries out the `Sub*` outputs on its network
driver, as it does a navigation's, and feeds back `SubNet`
(`clazel_net::SubConns` keeps the names). It steps a `Tick` when idle, so
decision 6's timeout fires on a page that is waiting for a sheet and nothing
else.

- **Event** `SubNet { renderer, serial, hop, input }` (the network shell's
  report on a sub-fetch connection). **Outputs** `SubConnect`, `SubSend` and
  `SubClose`, each naming `(renderer, serial, hop)`.
- **Messages** (`clazel-ipc`): `FetchStyle` (14), `StyleResponse` (110),
  `StyleBody` (111), `StyleEnd` (112), `StyleFailed` (113). None collides
  with 5.18's.

### Decisions (taken here, from the plan's goals; each is also in `src/spec.rs`)

1. **The table is the state's, not the renderer's.** The item names
   `Renderer::subfetches`; the state instead has `subfetches` and
   `subcounts`, each entry tagged with its renderer's id and lock, as 5.18's
   titles are. They are read and changed only by key `(renderer, lock,
   serial)`, so where another domain's entries sit never decides what
   happens to the observer's, and noninterference compares only the
   observer's entries.
2. **Sub-fetch connections have their own names**, `(renderer, serial,
   hop)`, not `next_conn`: the serial is the renderer's own count and the
   hop counts its `Connect`s, so no counter is shared between domains (a
   shared one would be a channel the noninterference theorem forbids). Every
   connection is new (`Connection: close`), of the renderer's tab, with the
   renderer's domain as its partition key. A report on anything but the
   current connection of a live sub-fetch is ignored in full.
3. **Credentials per 5.0(h), decided per hop** (`credentialed`): a request
   whose URL's origin is the renderer's lock, and whose cookie host is the
   lock's host, is given the kernel's jar, and its jar operations are
   applied; any other request is given an empty jar, so it carries no
   `Cookie` field, and its operations are dropped. An opaque-origin document
   has no host, so its requests carry none. Fetch's "no-cors" with
   credentials "include" would send cookies cross-origin; 5.0(h) chose not
   to.
4. **Limits, stated once** (`src/spec.rs`): at most 8 sub-fetches in flight
   per renderer, 64 started per document (a commit starts a new count), and
   2^64 − 1 serial numbers. A `FetchStyle` past a limit, or whose URL does not
   decode, resolve or parse, gets `StyleFailed` and starts nothing. A
   `FetchStyle` before the renderer's first commit is a disallowed frame
   (killed), as `Display` and `Title` are.
5. **A navigation ends the old document's sub-fetches.** A same-origin
   commit marks the renderer's sub-fetches ended; a replaced, killed or
   exited renderer is not live. An ended or dead sub-fetch changes nothing
   and sends nothing; the next `Tick` closes its connection and drops it.
6. **A `Tick` fails a sub-fetch** that started 60 seconds ago or more:
   `SubClose`, then `StyleFailed` to its renderer.
7. **Noninterference keeps its form and hypotheses.** `SubNet` belongs to
   its renderer's domain and has no declassified part; the `Sub*` outputs
   are addressed to no renderer (they go to the network shell); the relation
   between the runs gains equal sub-fetch tables and counts under the
   observer's locks. `quark_cookie_integrity` gains a disjunct for cookies a
   credentialed sub-fetch stores, which are under the lock's own cookie
   root.

### Theorems

`theorem_subfetch_only_to_requester` (a sub-fetch's frames go only to the
renderer that asked, while its document is live), `theorem_subfetch_credentials`
(every octet on a sub-fetch connection is 3.6's `theorem_wire_cookies`
request for the current URL, with the kernel's jar only when the hop is
credentialed), `theorem_subfetch_ownership` (the second half of
`theorem_connection_ownership`, which now ensures both: sub-fetch outputs
name the event's renderer, and every entry keeps the tab and partition it
started with), `theorem_subfetch_limits` and
`theorem_commit_ends_subfetches`. Every earlier theorem is re-proven over
the new event, outputs and message. The ownership and limits proofs rest on
an invariant of reachable states (`subfetch_tables_wf`: each key once, each
serial below its renderer's counter).

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE).
