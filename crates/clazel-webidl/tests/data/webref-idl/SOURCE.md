# WebIDL of the DOM, HTML, Fetch, XHR, URL, Storage, UI Events and CSSOM standards

Upstream: https://github.com/w3c/webref/tree/1c0592d0155506fd72fea259330981d9c208d9be/ed/idl
Commit: 1c0592d0155506fd72fea259330981d9c208d9be
License: MIT for webref itself (`LICENSE.md`, copied from the root of w3c/webref). The IDL in each file is extracted, unchanged, from its standard (the WHATWG standards license code portions under BSD-3-Clause; the W3C's UI Events and CSSOM fall under the W3C Software and Document License); the header of each file names its standard.

The commit is w3c/webref's "Update of ed report from new reffy run" of
2026-11-16 (07:00 UTC). `ed/idl/` holds the IDL that Reffy extracted from each
specification's editor's draft that day. Copied byte for byte, the nine files
of `ed/idl/` named for the standards (and one more, `pointerevents.idl`,
below):

- `dom.idl`: DOM Standard (https://dom.spec.whatwg.org/)
- `html.idl`: HTML Standard (https://html.spec.whatwg.org/multipage/)
- `fetch.idl`: Fetch Standard (https://fetch.spec.whatwg.org/)
- `xhr.idl`: XMLHttpRequest Standard (https://xhr.spec.whatwg.org/)
- `url.idl`: URL Standard (https://url.spec.whatwg.org/)
- `storage.idl`: Storage Standard (https://storage.spec.whatwg.org/)
- `uievents.idl`: UI Events (https://w3c.github.io/uievents/)
- `cssom.idl`: CSS Object Model (https://drafts.csswg.org/cssom-1/)
- `pointerevents.idl`: Pointer Events (https://w3c.github.io/pointerevents/).
  Added for item 7.14: at this commit webref extracts the IDL of
  `MouseEvent`, `MouseEventInit`, `WheelEvent` and `WheelEventInit` into this
  file and into no other (UI Events' own `uievents.idl` has none of them), and
  `html.idl`'s `DragEvent` inherits `MouseEvent`. It also holds
  `PointerEvent`, the `onpointer*` handlers and `Element`'s pointer capture
  methods, which the bindings do not expose.

Why webref and not each specification's repository: the WHATWG standards
keep their IDL inside the source of the document (Bikeshed or Wattsi
markup), not as a file; extracting it is Reffy's job, done the same way for
every standard, and webref publishes the result at a commit, which pins every
file at once. The standards' own repositories would be eight pins and an
extractor of our own.

Not vendored, though these files refer to their types (item 7.12's generator
must supply them or reject the references): `webidl.idl` (`DOMException`,
`QuotaExceededError`), `hr-time.idl` (`DOMHighResTimeStamp`), `streams.idl`
(`ReadableStream`), `FileAPI.idl` (`Blob`, `File`), `cssom-view.idl`,
`DOM-Style.idl` and the other files of `ed/idl/`. To update, copy the files
from a newer webref commit, change the commit above, and run
`cargo xtask testdata`.

`xtask/src/testdata/inventory.rs` writes `tests/generated/webref_idl.rs`, the
inventory of paths, sizes and hashes. Nothing parses the IDL yet.
