# clazel-js: the engine's embedding API

`clazel-js` is the one crate a program names to embed Clazel's JavaScript
engine. The browser embeds it, and so can a command-line runtime, a
Node-style server, or another Rust program. This is phase-7.md item 7.8, and
"The engine as a library" in that file is the plan this README works out.

**Status: the contract, and its first implementation.** The types and
signatures here are the proposal. The contract was written first, as the plan
says, so that people can review it before `clazel-webidl` and `clazel-web`
build on it; the first part of the implementation is on top of it without
changing a signature, over the interpreter (`clazel-js-vm`) and the built-ins
(`clazel-js-builtins`). What the VM does not have yet still returns
`Error::NotImplemented`; "What is implemented" below lists each item and why.
Tier 0, no proofs. What to review is in "Open questions".

Read the API in `src/`, one file per topic: `runtime.rs` (Runtime, limits,
Terminator), `value.rs` (the four ways to hold a value), `scope.rs` (all the
operations), `code.rs` (realms, source, scripts, modules), `native.rs`
(native functions, host objects), `host.rs` (the `Host` trait), `error.rs`.
`cargo doc -p clazel-js --no-deps --open` shows the same with the examples.

## What is implemented

Works now, with tests that use the public API only (`tests/api.rs`, and
the doctests): `Runtime::new` (VM, built-ins, host), `scope`, `run_jobs`,
`terminator` (the interpreter's own flag), `limits`, `heap_used` (an estimate);
primitives and strings (UTF-16 exact), `kind` and the `as_*`, `to_*` and `is_*`
conversions, `strict_equals`, `same_value`, `instance_of`; `new_object`, `get`,
`set`, `has_property`, `define_property` (data properties),
`get_prototype_of`, `set_prototype_of`, `get_method`, `call`, `construct`;
accessor properties (`define_property` with `get`/`set`, `get_own_property`;
`define_accessor` from native closures, whose two function objects are made
when something first needs them, which script cannot observe: the method's
documentation says why, and `tests/lazy_accessors.rs` runs each first use on
a lazy and an eager object and compares),
`delete_property`, `new_array`, `new_array_from` and `is_array` (item 7.12
needed them: WebIDL attributes are accessors);
`function`, `shared_function` (re-entrant), `define_method`, `Args`,
`new_host_object` with `host_data`,
`get_prototype_from_constructor`, `host_mut`, `check_terminated`; errors,
`new_exception`, `throw_error`, `throw`, `report`, `Error::Thrown`;
`create_realm` (once), `global`, realm and script host data; `Scope::run_jobs`
(a microtask checkpoint from inside a scope, item 7.15); `compile_script`,
`run_script`, `eval_script`; `Handle`, `Weak`, `Member`; `gc` and
`clear_kept_objects` as no-ops.

Still `NotImplemented`, each because the VM lacks the feature: promises
(`new_promise` and the rest), `iterate` and symbols (`new_symbol`,
`well_known_symbol`), BigInt, ArrayBuffer, modules and synthetic modules (the compiler's module goal and the runtime's
module records), a second realm and `RealmOptions::global`, `construct` with a
`new_target` other than the constructor, `instance_of` of a bound function,
`ErrorKind::EvalError` and `UriError`. The infallible constructors for the
missing values (`new_symbol`, `well_known_symbol`, `bigint_from_*`) cannot
return an error, so they record it and the next fallible call returns it.

**Where it deviates, so reviewers see it:**

- **No completion value.** `run_script` and `eval_script` return `undefined`
  because the compiler's script has no completion value. Results go out
  through globals or native functions.
- **Re-entrance** works: a native closure that JavaScript re-enters while
  it runs runs again, nested. That needed `Sync` on the closures (open
  question 14, answered as its proposal said).
- **Rooting.** There is no collector in this tree (open pull requests), so
  nothing is ever freed: `Local`, `Handle`, `Weak` and `Member` are checked
  (the runtime they belong to, the arena's generation) but root nothing;
  `Weak::upgrade` is always `Some`, `HostObject::trace` and `Host::trace_roots`
  are never called, `Scope::nested` releases nothing, and a `Handle` drop does
  nothing. The API is written so that a collector can start rooting without a
  signature change: every value passes through `Scope`, `Handle` is the only
  long-lived root, and `Member` is reported by its owner.
- **The `Host` hooks.** None is called: they are what promises, modules,
  `Date`, `eval` of strings and `FinalizationRegistry` call, and the VM has
  none of them. The engine's job queue works (`Scope::enqueue_job_internal`,
  `run_job`, `run_jobs`) but nothing makes a job yet, so `run_jobs` returns 0.
- **Exotic hooks of `HostObject`** are not called: a host object is an
  ordinary object with its data beside it.
- **Limits.** All but `code_bytes` (no JIT) and `regexp_backtrack_entries`
  (no RegExp built-in; the VM stores it for one) are applied; see "Limits
  and the `Terminator`". The heap limit's `RangeError` comes without a
  collection first, because the VM does not use the collector yet and never
  frees anything.
- **Stack traces.** `ErrorReport::stack` is empty and `Source::start_line` is
  not used: the VM keeps no source positions.

## The boundary

- Engine crates depend on no browser crate. `cargo xtask check` enforces it
  with the `ENGINE` list in `xtask/src/status.rs`, which holds this crate.
- `clazel-js` depends on the engine's `clazel-js-vm`, `clazel-js-builtins`,
  `clazel-js-syntax` and `clazel-js-heap` and no other crate. No type of
  theirs is in its public API: a `Local` is private data over the heap's value.
- The browser uses only this public API. A binding that needs something the API
  lacks gets it added here, not a private path.
- The Test262 runner (`clazel-js-shell`, a later item) is a second embedder and
  builds `$262` from public calls alone.

## A `Runtime`

A `Runtime` is one ECMAScript agent: a heap, a job queue, limits and a `Host`.

- **No global state.** No `static`, no thread-local. A process can hold many
  runtimes.
- **`Send`, not `Sync`.** A runtime can move to another thread between calls, and
  only one thread uses it at a time. Compile-checked by doctests. For this to
  hold the `Host` is `Send` too. The browser runs one runtime per renderer, on
  one thread (7.0(e)).
- **Everything goes through a scope.** `Runtime::scope(|scope| ...)` is the only
  way in. Inside native functions and `Host` hooks the engine hands over a
  `Scope` for that call.
- **Dropping a runtime** frees the heap and drops native closures and host
  object data. It runs no JavaScript.

Configuration is a `Config` of `Limits` and a `JitMode` (only `Off` until jit.md's
crate exists), and a `Host`:

```rust
use clazel_js::{Config, DefaultHost, Key, Limits, RealmOptions, Runtime, Source};

fn main() -> Result<(), clazel_js::Error> {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    let sum = rt.scope(|scope| {
        // The script's completion value is not produced yet (see "What is
        // implemented"), so the result goes out through a global.
        scope.eval_script(&realm, Source::new("sum.js", "var sum = 1 + 2;"))?;
        let global = scope.global(&realm)?;
        let value = scope.get(global, Key::from("sum"))?;
        Ok(scope.as_number(value))
    })?;
    assert_eq!(sum, Some(3.0));
    rt.run_jobs()?;
    Ok(())
}
```

## Realms

`Scope::create_realm` makes a realm: a global object and its own built-ins.
`$262.createRealm()` is exactly this, and frames would be later. A `Realm` is a
root (cloneable, `Send`, `Sync`) and every call that runs code names its realm.
`Scope::global` reaches the global object, and installing `console` or `window`
is ordinary property definition on it. `RealmOptions::global` lets the
global object be a host object, which the browser's `Window` needs.
`Scope::set_realm_host_defined` attaches the embedder's data to a realm (HTML's
environment settings object).

## Scripts and modules

- **Source** is `Source { name, text, start_line, host_defined }`. The text is a
  `&str`, a sequence of code points, as ECMA-262 defines source text. The name
  is for stack traces and reports, and `host_defined` is the embedder's data
  (base URL, fetch options), kept with the compiled code.
- **Scripts.** `eval_script` does `compile_script` then `run_script`, which are
  separate so a host can follow HTML's "prepare the script element". A syntax
  error is a thrown `SyntaxError`.
- **Modules** follow ECMA-262's phases, one method each: `parse_module`,
  `load_requested_modules`, `link`, `evaluate_module`, plus `module_namespace` and
  `module_status`. Loading is asynchronous and the host's: the engine calls
  `Host::load_imported_module(referrer, request, payload)`, and the host
  answers with `Scope::finish_loading_imported_module(payload, result)`, now or
  on a later event-loop turn. Dynamic `import()` uses the same hook. The
  `Referrer` carries the importing code's `host_defined` data, so the host knows
  what to resolve against. `import.meta` goes through two more hooks. A host
  can add its own resolver, or CommonJS (through synthetic modules), without
  engine changes.
- **Jobs.** The engine queues jobs and runs them only when asked:
  `Runtime::run_jobs` is a microtask checkpoint. The event loop is the host's.
  HTML's lives in `clazel-web`, and a Node-style runtime would drive the same
  calls from its own.

## Values, and holding them

Values live in the collector's heap, which does not move them (7.0(f)). Four
types hold a value, from cheapest to most durable:

| Type | Roots the value? | Lives | Use |
|---|---|---|---|
| `Local<'s>` | yes, until its scope ends | one `Scope` | everything inside a call. `Copy`; cannot escape the closure (compile-checked) |
| `Handle` | yes, until dropped | any time, any thread | what outlives a call: a callback to run later, a promise's resolvers. `Clone`, `Send`, `Sync`; dropping needs no runtime |
| `Weak` | no | any time | side tables from platform objects to wrappers; `upgrade` gives `None` after collection |
| `Member` | only if its owner reports it | owner's choice | JS values inside a host object's data or the host, reported from `trace` so there is no uncollectable cycle |

- **Stale is an error, never an alias.** Every reference carries the arena's
  generation (7.5, 7.6). Using one that no longer names its object gives
  `Error::StaleHandle`. A handle from another runtime gives `Error::WrongRuntime`.
- **When the collector runs:** inside an operation that allocates, or on
  `Scope::gc()` (`$262.gc()`), at points the engine chooses. Never between two
  of the embedder's own Rust statements, and never while tracing, which is given
  no `Scope`.
- **Roots** are the value stack, every live `Local`, every `Handle`, the job
  queue, and what the host reports from `Host::trace_roots` (for the browser:
  the wrapper of every node in a tree) and each host object's `trace`.
- **Strings** are UTF-16 code unit sequences, as in the language.
  `Scope::string` takes Rust text; `string_utf16` takes units, including lone
  surrogates, which WebIDL's conversions need. `string_to_utf16` reads exactly,
  and `string_to_string_lossy` replaces lone surrogates.

## Native functions and host objects

- **`Scope::function(name, length, Callable, f)`** makes a JavaScript function
  from a Rust closure `Fn(&mut Scope, &Args) -> Result<Local>`. It is `Fn`, not
  `FnMut`, because a native function can be re-entered through JavaScript it
  calls. State it needs lives in a host object, in the `Host`, or behind a lock.
  `Callable::Constructor` makes it usable with `new`, with `Args::new_target`
  set, and `get_prototype_from_constructor` gives subclasses their prototype.
- **`HostObject`** is a trait for the Rust data of a JavaScript object. It is
  typed (`host_data::<T>` checks, `Error::WrongType` otherwise), is dropped when
  the collector frees the object, reports the values it refers to from `trace`,
  and may have four exotic hooks (`get_own_property`, `define_own_property`,
  `delete_property`, `own_property_keys`) for WebIDL's legacy platform objects.
  This is how `clazel-webidl` builds DOM wrappers.

## `Host`

One trait for everything ECMA-262 leaves to the host, each with a stated
default, so `DefaultHost` works for a program that needs none. Hooks get
`&mut self` and a `Scope`, may re-enter the engine, and may fail with an
`Error`, which the calling operation passes on.

| Group | Methods (ECMA-262 name) | Default |
|---|---|---|
| Jobs | `enqueue_promise_job`, `enqueue_generic_job`, `enqueue_timeout_job`, `enqueue_finalization_registry_cleanup_job` | the engine's own queue |
| Job callbacks | `make_job_callback`, `call_job_callback` | a plain callback; call it |
| Modules | `load_imported_module`, `supported_import_attributes`, `get_import_meta_properties`, `finalize_import_meta` | refuse with a `TypeError`; none; none; nothing |
| Promises | `promise_rejection_tracker` | nothing |
| Code from strings | `ensure_can_compile_strings`, `has_source_text_available` | allow; yes |
| Objects | `ensure_can_add_private_element`, `resize_array_buffer` | allow; `Unhandled` |
| The world | `now_ms`, `local_tza`, `random_u64`, `default_locale` | system clock; UTC; (required); `en-US` |
| The collector | `trace_roots` | nothing |

The browser's answers for the world are its own: 7.0(b)'s fixed offset and
`en-US`, in `clazel-web`. The engine fixes none of them. `random_u64` has no
default because the engine has no entropy source and rule 8 forbids adding a
dependency for one. `DefaultHost` implements it from the standard library.

**`$262`, built from public calls.** The shell's hooks need nothing private:

| `$262` | Public call |
|---|---|
| `createRealm()` | `Scope::create_realm`, then `global` |
| `evalScript(src)` | `Scope::eval_script` in the realm |
| `gc()` | `Scope::gc` |
| `detachArrayBuffer(buf)` | `Scope::detach_array_buffer` |
| `agent` | none; see the open questions |

## Errors and exceptions

`Result<T, Error>` throughout. One variant is a JavaScript value; the rest are the
engine's and cannot be caught by JavaScript:

- `Thrown(Exception)`: JavaScript threw. An `Exception` holds the value in a
  `Handle`, so it can be reported after the call returned. This includes the
  `SyntaxError` for bad source and the `RangeError`s the limits raise.
  `Scope::report` turns it into an `ErrorReport` (name, message, stack) without
  running user code.
- `Terminated`: a `Terminator` ended the evaluation.
- `OutOfMemory`: the heap limit was hit and not even the `RangeError` could be
  allocated. Rare.
- `StaleHandle`, `WrongRuntime`, `WrongType`, `Busy`: misuse of the API,
  caught and reported, never undefined behaviour.
- `NotImplemented`: something the VM does not have yet; see "What is
  implemented".

A native function returns errors of either kind with `?`. To throw:
`return Err(scope.throw_error(ErrorKind::TypeError, "..."))`, or
`scope.throw(value)` for a value the embedder made (a `DOMException`).

## Limits and the `Terminator`

**Limits are the embedder's.** `Limits` has no `Default`, and a struct literal must
name every field, so nothing is fixed in the engine and adding a limit makes
each embedder choose. `Limits::unlimited()` is a named choice for tests, and
`Limits::recommended()` one for untrusted pages on a 2 MiB thread stack
(phase-7.md 7.19). Neither is a default: nothing in the engine calls them.

| Limit | `recommended()` | When passed |
|---|---|---|
| `heap_bytes` | 512 MiB | `RangeError` ("Out of memory: the heap limit was reached"), catchable; `OutOfMemory` once the 64 KiB reserve the error comes from is spent too |
| `value_stack_bytes` | 4 MiB | `RangeError` ("Maximum call stack size exceeded") |
| `native_depth` | 32 | `RangeError` ("Maximum call stack size exceeded", or "too many nested native calls" for the embedder's closures) |
| `code_bytes` | 64 MiB | the JIT stops compiling; not an error (no JIT yet) |
| `regexp_backtrack_entries` | 1 Mi entries | `RangeError` from the match (no RegExp built-in yet) |
| `nesting_depth` | 512 | `SyntaxError` (source, `JSON.parse`), `RangeError` (`JSON.stringify`) |

What each counts:

- **`heap_bytes`** is the VM heap's own byte count, an estimate: 64 bytes a
  cell, a string's code units at one byte (Latin-1) or two, 8 bytes a slot an
  object is made with, and 32 bytes each property added later.
  `Runtime::heap_used` reads it. The built-ins count too (about 23 KB), so a
  limit below them makes `Runtime::new` fail with `OutOfMemory`. Nothing is
  freed yet, so a page that filled the heap leaves it full: compiling another
  script in the same runtime is then `OutOfMemory`.
- **`value_stack_bytes`** is the frame region, at 8 bytes a slot. JavaScript
  calling JavaScript uses it and not the host stack, so plain recursion is
  bounded by it alone.
- **`native_depth`** bounds natives running one inside another (built-ins
  that call back, such as `forEach`, and the embedder's own), and one more
  than it bounds runs of the interpreter loop nested inside an operation
  (the `toString` that `'' + o` calls). Both use the host stack: about 40 KB
  a level unoptimised and 1.5 KB optimised (measured on aarch64 macOS), so
  32 fits a 2 MiB thread in either build. The thread must hold the limit the
  embedder chooses, or a page can overflow the host stack and abort the
  process; `unlimited()` does not bound it.
- **`nesting_depth`** is the height of the parse tree for source, and levels
  of arrays and objects for JSON. Each also has a fixed bound that keeps its
  own recursion on the host stack, and the smaller applies: 1024 (source),
  512 (`JSON.parse`), 128 (`JSON.stringify`). JSON past it is a
  `SyntaxError`, as phase-7.md 7.11 lists.

Pending timers are the event loop's to bound (`clazel-web`'s
`event_loop::Limits`), and fetches in flight the kernel's; neither is the
engine's. `tests/hostile.rs` runs the hostile pages of 7.19 through this API.

**`Terminator`** (`Runtime::terminator()`; `Clone`, `Send`, `Sync`) stops a runtime
from another thread. It sets a flag; the interpreter checks it at loop back-edges
and calls, JIT code at the same points, built-ins in their long loops, and native
functions via `Scope::check_terminated`. The evaluation ends with
`Error::Terminated`. JavaScript cannot catch it, and no `finally` runs. The flag
stays set until `Terminator::clear`. The `Terminator` itself is implemented
and tested here, because it is only an atomic flag. The browser keeps 7.0(g)'s
policy (it ends a stuck renderer, on the user's word) and may use this later to
keep the tab. jit.md adds no interaction beyond "JIT code checks the same flag at
the same points".

**Executable memory** is the embedder's choice (jit.md J.0(b)). `JitMode` gains a
variant that carries a `CodeMapper` when `clazel-jit` exists. Until then it is
interpreter only, which is complete.

## What the browser's bindings will use

| Browser need | API |
|---|---|
| Install `window`, `document`, `console` | `create_realm` with a host-object global; `global`; `define_property`, `define_method` |
| Interface objects and prototypes (7.12) | `function` with `Callable::Constructor`; `get_prototype_from_constructor`; `define_property`; `define_accessor` (attributes); `set_prototype_of` |
| Wrappers, one per platform object (7.12, 7.13) | `new_host_object` with typed data; `Weak` for the side table; `Host::trace_roots` for nodes in a tree |
| `NodeList[0]`, `HTMLCollection.name` | `HostObject`'s exotic hooks |
| WebIDL conversions (3.2) | `to_number`, `to_string`, `to_boolean`, `to_object`, `is_callable`, `get_method`, `iterate`, `string_utf16`, `bigint_from_*` |
| `DOMException`, TypeErrors | `throw_error`, `throw` |
| Event listeners calling JS (7.14) | `Handle` or `Member` to the callback; `call`; `report` for uncaught exceptions |
| Promises from `fetch()`, `import()` (7.15, 7.16) | `new_promise`, `resolve_promise`, `reject_promise`, `promise_then`, `promise_state` |
| Script elements (7.15) | `compile_script`, `run_script`, `parse_module`, `load_requested_modules`, `link`, `evaluate_module`, `Host::load_imported_module` |
| Event loop, microtasks, `queueMicrotask` (7.15) | `Runtime::run_jobs`; `Host::enqueue_promise_job`, `make_job_callback`, `call_job_callback`; `clear_kept_objects` after a checkpoint |
| Unhandled rejections | `Host::promise_rejection_tracker` |
| `Date`, `Math.random`, locale | `Host::now_ms`, `local_tza`, `random_u64`, `default_locale` |
| A stuck page (7.0(g)) | `Terminator` |

## What is deliberately not in the API

- **A C API** (`clazel-js-capi`): Phase 8, and needs its own decision under rule 1.
- **Stability.** Rust only, unstable, no semver promise until Phase 8 has a second
  real user.
- **Node as a drop-in.** A Node-compatible runtime on `clazel-js` is the
  realistic path, not V8 API emulation.
- **Threads and shared memory**: `SharedArrayBuffer`, `Atomics`, and so
  `$262.agent`; one runtime per thread only (7.0(b), 7.0(e)).
- **`Intl`, Temporal, WebAssembly, a debugger protocol, heap snapshots.**
- **Event loops, timers, `console`, `fetch`, a DOM.** The embedder's. The engine
  has none and calls the `Host` instead.
- **Catching panics from native functions.** The lints forbid them here, and an
  embedder's panic is its own.
- **Safety against a hostile embedder is not a goal; safety against hostile
  JavaScript is.** An embedder that runs untrusted code without the browser's
  sandbox relies on the engine's own guarantees: no `unsafe` outside
  `clazel-sys`, the arena's generation checks, the validator's theorem for JIT
  code, and the limits.

## Open questions

Nothing here is a decision the plan marks as the maintainer's. These are what the
plan leaves open and this contract had to settle, or leaves unsettled, so please
look at each.

1. **After `Terminated`, is the runtime usable?** The proposal: the flag is
   sticky, so every call ends `Terminated` until the embedder calls
   `Terminator::clear`; after that the heap is consistent and the runtime
   usable. It rests on `finally` blocks not running. It makes termination safe
   for a runtime that is then dropped, and for the browser, but "usable after"
   is a promise to implement and test.
2. **Handle model.** `Local<'s>` scoped to a closure, plus `Handle` (reference
   counted, dropped without the runtime) and `Member` (reported from `trace`).
   Plan 7.0(f) says "a scoped handle stack, checked on scope exit". The scope
   here is a closure with a lifetime the compiler enforces, which is checked
   earlier than at exit. The cost is that a value cannot be returned from a
   nested scope except as a `Handle`; an `escape` call is possible if that bites.
3. **`Host: Send`.** It keeps `Runtime: Send`. It means the browser's host cannot
   hold `Rc`s of DOM state: nodes are arena ids (Phase 4), which should work,
   but it is the contract's strictest demand on `clazel-web`.
4. **Exotic hooks.** Four are given; WebIDL §3.9 and §3.10 (legacy platform
   objects, named properties) may need `set`/`get` receivers or more. The
   set is to be fixed against 7.12's generator, and may grow.
5. **The global's `this` value** (HTML's `WindowProxy`) is not in `RealmOptions`.
   ECMA-262 lets a host set it separately from the global object. Needed by
   7.15, and the contract does not yet say how.
6. **Synthetic modules** (`new_synthetic_module`, `set_synthetic_export`) are
   reserved in the contract, since "a host can add CommonJS" needs them and
   JSON modules do. The plan does not list them as a Phase 7 deliverable.
7. **`$262.agent`.** The plan lists `agent` among the host hooks, and 7.0(b)
   leaves out `SharedArrayBuffer` and `Atomics`, which `agent` exists to test.
   This API has no agent hook, and the shell skips those tests. If another
   host wants agents in Phase 8, a `Runtime` per thread plus shared memory
   needs its own design.
8. **Hooks the plan's list lacks.** `HostEnqueueFinalizationRegistryCleanupJob`
   (7.6 needs it) and `HostGetSupportedImportAttributes` are in the trait;
   the plan's list does not name them. 7.4's check against the pinned edition
   decides which stay.
9. **ECMA-262 section numbers** are not cited on the hooks, because 7.1 has not
   pinned an edition. They are named by abstract operation instead, which does
   not change between editions. Rule 5 asks for sections, so they are added when
   7.1 pins one. Until then the citations are incomplete.
10. **`run_jobs` and a throwing job.** A job that throws stops the run and
    returns the exception; later jobs stay queued. A host that wants
    "report and continue" overrides the queue hooks and runs jobs itself.
    The alternative is one more hook. The plan names none.
11. **`Source` text as `&str`.** Source with a lone surrogate cannot be written. ECMA-262
    source text is code points, and the browser decodes with `clazel-encoding`,
    which gives scalar values only, so nothing is lost in practice. Say so if
    UTF-16 source is wanted.
12. **Where `CodeMapper` lives.** jit.md names it; this crate cannot depend on a
    crate that does not exist. Likely `clazel-jit` defines it and `clazel-js`
    re-exports it.
13. **`OutOfMemory` versus `RangeError`.** 7.19 says the heap limit gives a
    `RangeError`. This contract keeps `OutOfMemory` for when even that cannot
    be allocated. The heap now keeps a 64 KiB reserve for the error, so the
    variant remains only for a page that catches the error and allocates
    again until the reserve is spent too, and for a limit too small for the
    built-ins or for compiling a script.
14. **Native closures and re-entrance.** Answered: `Scope::function` takes
    `Fn + Send + Sync`, and the table holds each closure in an `Arc` that a
    call clones, so a re-entrant call runs (HTML's `document.write`, item
    7.15, needs it). The browser's closures hold ids, not `Rc`s, as open
    question 3 already asks of the host.
15. **Infallible constructors that cannot work yet.** `bigint_from_*`,
    `new_symbol` and `well_known_symbol` return a `Local`, not a `Result`, so
    when the VM lacks the type the error is held for the next fallible call.
    Proposal: make them return `Result` (they allocate, so `string` and
    `string_utf16` could fail the same way, with `OutOfMemory`, which is also
    held today).
16. **Script completion value.** `run_script` documents the value of the last
    expression statement; the compiler does not produce it yet. No signature
    change, but embedders should not rely on it until the compiler does.
