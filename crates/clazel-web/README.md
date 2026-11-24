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
- **`scripting`** (item 7.15, the script half): a document parsed with the
  scripting flag on by `clazel-treebuilder`'s incremental driver, and its
  scripts run through `clazel-js`'s embedding API. `scripting::Page` is one
  document and one `Runtime`, whose `Host` holds the page's state. Each
  module cites the algorithms and steps it transcribes and lists its
  modelling choices:
  - `element`: "prepare the script element" (HTML §4.12.1.1†) acting on
    the parser's `ScriptReady`: the type string, classic and module
    scripts, inline and external ones (fetched through the embedder:
    `Page::take_requests` and `Page::fetched`), `async`, `defer`, the
    pending parsing-blocking script, `nomodule`, `event`/`for`; "mark as
    ready", "execute the script element" with `document.currentScript`;
    "create a classic script" and "run a classic script", with exceptions
    reported and a microtask checkpoint when the last script returns.
  - `parser`: the "text" insertion mode's end tag "script" steps around
    preparation (script nesting level, parser pause flag, the insertion
    point), the tokenizer blocked on a parsing-blocking script, "abort a
    parser" and "the end" (deferred scripts, `DOMContentLoaded`, the load
    event's wait for async scripts).
  - `write`: `document.write`, `writeln`, `open` and `close`: writes are
    inserted at the insertion point and parsed before the rest; `open`
    after the load starts a script-created parser on an empty document.
  - `module`: module scripts' HTML half (the module map, "fetch a single
    module script" with its MIME type check, HostLoadImportedModule,
    "fetch the descendants of and link", "run a module script"). The engine
    half (`parse_module`, linking, evaluation, promises) is
    `NotImplemented` in `clazel-js` today, so a module script ends in an
    engine report and an `error` event; dynamic `import()` and top-level
    `await` wait on the same engine pieces.
  - `javascript_url`: "evaluate a javascript: URL" in the page.
  - `time`: `performance.now()`, coarsened to 100 µs.
  - `globals`: the minimum the scripts need before item 7.12's bindings,
    through the embedding API: `document` (`write`, `writeln`, `open`,
    `close`, `currentScript`), `performance.now`, and one wrapper object
    per node. Item 7.12 replaces it.

  The events the page fires (`load`, `DOMContentLoaded`, `readystatechange`,
  `error`) are dispatched to the listeners and `on*` handlers of the page's
  bindings, in order, after the step that fired them (the "recorded, not
  dispatched" deviation of item 7.15's first pull request is gone).
  `tests/scripting.rs`: unit tests by algorithm step; the six html5lib
  `scripted_*.dat` tree-construction cases (2 pass, 4 listed: they need
  item 7.12's DOM methods); and 21 vendored WPT `execution-timing/` pages
  run with a stand-in for `testharness.js` and `testlib.js` (the engine
  cannot run `testharness.js` yet): 17 pass, 4 listed.

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

- **Events and input** (item 7.14), in `events`, `activation`,
  `user_activation`, `page::{event, ui_events, handlers, forms, input}` and
  `scripting::input`:
  - *Dispatch* (`events`): DOM §2.9† with the event path, the capture, target
    and bubble phases, `stopPropagation`, `stopImmediatePropagation`,
    `preventDefault`, passive listeners and `once`/`signal`, and now the
    activation target: for a `MouseEvent` named `click`, the target (or, if
    the click bubbles, the nearest ancestor) with activation behavior runs
    its legacy-pre-activation behavior before the listeners and its
    activation behavior after them, or its legacy-canceled-activation
    behavior if the event was canceled. `tests/activation.rs` (7 tests, the
    standard's steps) and `tests/events.rs`.
  - *UI events* (`page::ui_events`): `UIEvent`, `MouseEvent`, `WheelEvent`,
    `KeyboardEvent`, `FocusEvent` and `InputEvent` with their constructors,
    dictionaries and `init*` methods. Not implemented: `PointerEvent`,
    `CompositionEvent`, `TextEvent`, `layerX` and `layerY` (they are the
    client position), `getModifierState` for keys other than Control, Shift,
    Alt and Meta.
  - *Input* (`scripting::Page::{click, key, wheel, scrolled, set_focus}`,
    `page::input`): the renderer passes the node it hit-tested. A click is
    `mousemove`, `mousedown`, focus change, `mouseup`, `click`; a key is
    `keydown`, `keypress`, `beforeinput`, the change, `input`, `keyup` with
    the default actions of Tab (sequential focus navigation), Enter (follow a
    link, click a button or checkbox, implicit submission, a line break in a
    `textarea`), Space (click on `keyup`) and Backspace; a wheel turn is a
    cancelable `wheel` event (its default action, scrolling, is the
    renderer's); the page's scroll is a `scroll` event at the document;
    focus is `blur`, `focusout`, `focus`, `focusin` in that order and
    `document.activeElement`, `focus()`, `blur()`, `tabIndex`; a text control
    that changed since it got focus fires `change` when it loses it.
  - *Default actions* (`page::forms`, `activation`): following a link
    (`PageHooks::navigate`: the renderer sends `Navigate`, or runs a
    `javascript:` URL in the page), submitting a form (the submission
    algorithm from its step 9 and the entry list are `clazel-forms`' proven
    `submit_exec`; a `GET` is `navigate`, a `POST` is `PageHooks::submit`,
    the kernel's `Submit`), resetting a form, toggling a checkbox, checking a
    radio button (with the group), clicking a `label`'s control. A disabled
    form control gets no mouse events.
  - *Event handlers* (`page::handlers`, HTML §8.1.8†): the `on*` IDL
    attributes of `Window`, `Document`, the elements and `AbortSignal` (the
    generated bindings call `Platform::event_handler_get` and
    `event_handler_set`), and the content attributes, compiled when first
    read or called; the handler's place among the listeners is where it was
    first set; `return false` cancels; a `body`'s Window-reflecting handlers
    are the Window's.
  - *User activation* (`user_activation`, HTML §6.4†): the window's
    transient (5 s), sticky and history-action activation, notified by
    `mousedown` and by `keydown` (except Escape) before they are
    dispatched, `navigator.userActivation`, `consume_user_activation`.
    The renderer-side `window.open` and `target=_blank` of item 7.16 ask it
    before sending `OpenTab`; the kernel's own record, for
    `theorem_popup_needs_input`, is the kernel's (it sees every `Input` it
    forwards): that is the hook, and nothing here reads the kernel.
  - *What is not done, and the deviations*: the handler content attribute's
    function has the global scope only (no element, form and document scope
    chain: the engine has no `with` and no `Function()`); `onerror` gets
    only the event (there is no `ErrorEvent`); a `submit` event is a plain
    `Event` (no `SubmitEvent.submitter`) and constraint validation is not
    run; a link's `target` is ignored (this tab; item 7.16's `OpenTab`);
    text editing has no caret or selection (typing appends, Backspace
    deletes the last character); `HTMLInputElement`, `HTMLFormElement` and
    the other control interfaces are not exposed (item 7.13), so script
    reads a control's value through the page (`Page::control_value`);
    `mouseover`, `mouseout`, `mouseenter`, `mouseleave`, `dblclick`,
    `contextmenu`, `auxclick` and the pointer events are not fired; only the
    main button; hit testing ignores `z-index`, clipping and `pointer-events`.
  - `window.event` (the legacy current event, set around each listener) and
    `document.createEvent` (DOM §4.5†'s table, for the interfaces the
    bindings expose), and `Event.timeStamp` from the page's clock.
  - `tests/ui_events.rs`: 48 tests of the above through a parsed document
    and the input API. `tests/wpt_events.rs` runs 64 vendored WPT
    `dom/events/` pages (the `.html` ones, and the `.any.js` and
    `.window.js` ones inside a page) with a stand-in for `testharness.js`
    (`tests/support/standin-events.js`: the engine cannot run the real one
    yet): 40 pages pass (226 subtests), 24 are listed with the reason each
    (`for...of`, `class extends`, `Promise` and `Object.getOwnPropertyDescriptor`
    in the engine; `HTMLInputElement` and the other element interfaces, other
    documents and shadow DOM in item 7.13; `ErrorEvent`; WPT's `/dom/constants.js`,
    which is not vendored). `CLAZEL_WPT_ONLY=text` runs the pages whose name
    has the text. WPT's `uievents/` is not vendored, so none of it runs; the
    `dom/events/scrolling/` and `non-cancelable-when-passive/` pages need a
    window with layout and are not run.

  The caps and their defaults (`Limits::default()`): 65,536 active timers
  (`LimitError::TooManyTimers`), 65,536 queued tasks (`TooManyTasks`) and
  1,048,576 queued microtasks (`TooManyMicrotasks`). The host turns a refusal
  into the script's error; HTML's is a `QuotaExceededError`, which waits for
  `clazel-webidl`'s `DOMException`. `tests/hostile.rs` runs 7.19's flood of
  10^6 timers from script, through `clazel-js`'s public API with a test
  `setTimeout` over this loop that throws a `RangeError`
  for now, and a page whose timers multiply for ever.

Item 7.1 vendored the test
data later items run: the WPT `testharness.js` tests (`tests/data/wpt-web/`) and
the TodoMVC vanilla, React and Vue implementations (`tests/data/todomvc/`).
