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

  Events are recorded, not dispatched (no listeners exist before 7.12).
  `tests/scripting.rs`: unit tests by algorithm step; the six html5lib
  `scripted_*.dat` tree-construction cases (2 pass, 4 listed: they need
  item 7.12's DOM methods); and 21 vendored WPT `execution-timing/` pages
  run with a stand-in for `testharness.js` and `testlib.js` (the engine
  cannot run `testharness.js` yet): 17 pass, 4 listed.

Item 7.1 vendored the test
data later items run: the WPT `testharness.js` tests (`tests/data/wpt-web/`) and
the TodoMVC vanilla, React and Vue implementations (`tests/data/todomvc/`).
