# clazel-web

Part of [Clazel](../../README.md). The script-facing web platform: `Window`,
`Document` and `Node` APIs, events, timers, the event loop, `fetch()` and
`XMLHttpRequest`, storage and history
([phase-7.md](../../docs/phases/phase-7.md) items 7.13 to 7.17).

Tier 0, target tier 0: safe Rust, tested, nothing proven. So far:

- **`serialize`**: the HTML fragment serialization algorithm (HTML §13.3†)
  over a `clazel-dom` arena: `serialize_fragment` is the `innerHTML` getter's
  string and `serialize_outer` the `outerHTML` getter's. It is here, and not
  in `clazel-treebuilder` or `clazel-dom` (tier 2), so that no tier 2 crate
  holds code that is only tested. The module's header lists its modelling
  choices and the two points the pinned standard text must settle (`<` and
  `>` escaped in attributes; the line feed after `pre`, `textarea` and
  `listing`), because the text of §13.3 is not vendored.
  `tests/serialize.rs` covers each step on hand-built trees.
  `tests/conformance_round_trip.rs` serializes the children of every element of every
  tree the html5lib tree-construction suite builds and fragment-parses the
  result with that element as the context, through
  `clazel-treebuilder`'s `parse_fragment_real`: 9,360 contexts, 9,213 give
  the same tree and 147 fall in the six listed classes (a tree no markup
  produces: carriage returns, processing instructions, `plaintext`, script
  data double escapes, directly nested `a`/`nobr`/`p`/`form`, a `form` under
  a form context); a difference in no class fails the test. The fragment
  parsing half of `innerHTML` is the treebuilder's. Binding it to the DOM
  (adopting the fragment's nodes into the target document) waits for item
  7.13's `clazel-dom` operations and for 7.8 and 7.12.

- **`event_loop`**: the engine-independent HTML event loop (HTML §8.1.7†
  and §8.6†): task sources and queues (round-robin between sources, FIFO
  within), "queue a task", the processing model's run-one-task-then-microtask
  -checkpoint, the microtask checkpoint with its re-entrancy flag, a
  rendering-opportunity stand-in, and the timers (`setTimeout`,
  `setInterval`, `clearTimeout`, `clearInterval`: id allocation, the nesting
  level 4 ms clamp, ordering by due time then start, interval rescheduling).
  Callbacks are host-supplied ids; time is the caller's. `Limits` caps
  active timers, queued tasks and queued microtasks (7.19): the call that
  would pass a cap fails and changes nothing. `tests/event_loop.rs` has the
  unit tests and hand transcriptions of WPT `timers/` and `microtask-queuing/`
  orderings (which need a JS engine to run).

- **`page`**: the platform objects of a page exposed to script through
  `clazel-webidl`'s generated bindings (item 7.12). `Page` is the
  `clazel-js` host and the bindings' platform: it owns the document (a
  `clazel-dom` arena), the listeners, the other platform objects and the
  wrappers (a node's in `clazel-dom`'s wrapper slot, the others in a side
  table). It implements `EventTarget`, `Event`, `CustomEvent`,
  `AbortController`, `AbortSignal`, `Node`, `Document`, `DocumentType`,
  `DocumentFragment`, `CharacterData`, `Text`, `Comment`, `Element`, the
  HTML element interfaces the bindings expose (their `[Reflect]` attributes
  and `HTMLTitleElement.text`), `NodeList`, `HTMLCollection`,
  `DOMTokenList`, `Window`, `Location`, `History`, `Navigator` (a fixed,
  honest user-agent string) and `console`, which writes to the host's log.
  `location.href = …` and the other navigations call `PageHooks::navigate`;
  `pushState` and `replaceState` call `PageHooks::update_url` (no renderer
  runs `clazel-web` yet, item 7.17, and 7.16's `UpdateUrl` message is not
  built, so these are the hooks the renderer will implement). Each module's
  header lists what is not implemented; those members throw a
  `NotSupportedError` naming themselves. `tests/bindings.rs` runs script
  against parsed documents, with checks transcribed from WPT's `dom/` and
  `html/` tests (testharness.js needs more of the engine than it has).

- **The DOM API (item 7.13)**, in `page/` on top of `clazel-dom`'s proven
  operations (which already hold pre-insertion validity, `insert`, `replace`,
  `replace all`, deep and shallow `clone`, `adopt` and the attribute
  changes, each proven to keep `wf`: the theorems are in
  `clazel-dom/Cargo.toml`; this item adds no operation to that crate):
  - `mutation.rs`: the one place the arena changes. Each operation runs
    `clazel-dom`'s and also queues the mutation records (DOM §4.3†), adds the
    transient registered observers and moves the live ranges' boundary points
    (DOM §4.2.3† "insert" and "remove", §4.10† "replace data"): the insertion
    and removing steps hooks, written once. `MutationObserver` and
    `MutationRecord` are here; the host calls
    `mutation::notify_mutation_observers` at its microtask checkpoint (no
    microtask is queued by the page: the event loop is not joined to the
    engine yet, item 7.15).
  - `fragment.rs`: HTML §13.4† fragment parsing through
    `clazel-treebuilder`'s `parse_fragment_real`, copied into the page's
    arena. `innerHTML` and `outerHTML` (getters over `serialize.rs`, setters
    over this), `insertAdjacentHTML`, `Range.createContextualFragment`.
  - `attr.rs`: `Attr`, `NamedNodeMap`, the attribute-node and `*NS` methods,
    `createAttribute(NS)`, and `dataset` (`DOMStringMap`).
  - `range.rs`: `Range` (not `StaticRange`): boundary points and their
    setters, `compareBoundaryPoints`, `comparePoint`, `isPointInRange`,
    `intersectsNode`, `cloneRange`, `toString`, `deleteContents`,
    `extractContents`, `cloneContents`, `insertNode`, `surroundContents`.
  - `node.rs` also gained `normalize`, `isEqualNode`,
    `compareDocumentPosition`, the namespace lookups, `baseURI`,
    `splitText`, `wholeText`, `importNode`, `adoptNode`,
    `getElementsByTagNameNS`, `insertAdjacent*` and `ProcessingInstruction`.
  - Not done: `getComputedStyle` (the bindings expose no
    `CSSStyleDeclaration`), a second document (`document.implementation`,
    `new Document()`, `createHTMLDocument`: the arena is one document, which
    is most of what the WPT `dom/nodes` tests that fail need), `createElementNS`
    and `setAttributeNS` outside Infra §8's six namespaces,
    `dataset.name`, `list[0]` and `map.name` (named and indexed properties
    need the engine's exotic dispatch, which the VM does not call yet), the
    HTML element interfaces beyond the eight the bindings expose,
    `TreeWalker`/`NodeIterator`, `Selection`, shadow trees and custom
    elements.
  - `tests/dom_api.rs` tests each of these through script. `tests/wpt_dom.rs`
    runs the vendored WPT `dom/nodes` and `dom/collections` tests with a
    stand-in for `testharness.js` (`tests/support/standin-dom-harness.js`;
    the real file does not load in the engine yet) and compares the result
    per file with `tests/wpt_dom_expected.txt`; a subtest is a pass only
    if it ran and held, async and promise tests are counted as skipped, and
    a test that needs a WPT helper that is not vendored is listed as
    blocked.

Item 7.1 vendored the test
data later items run: the WPT `testharness.js` tests (`tests/data/wpt-web/`) and
the TodoMVC vanilla, React and Vue implementations (`tests/data/todomvc/`).
