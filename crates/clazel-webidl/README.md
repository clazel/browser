# clazel-webidl

Part of [Clazel](../../README.md). The generated WebIDL bindings, the WebIDL
type conversions, overload resolution, wrappers and `DOMException` for the
JavaScript engine ([phase-7.md](../../docs/phases/phase-7.md) item 7.12).

Tier 0, target tier 0. It reaches the engine only through `clazel-js`'s public
embedding API ("The engine as a library").

## What is here

- **The generator.** `cargo xtask bindings` parses the vendored IDL
  (`tests/data/webref-idl/`, item 7.1; `SOURCE.md` names the commit) with our
  own parser (`xtask/src/bindings/`, WebIDL §2's grammar), merges partial
  interfaces, mixins and `includes`, and writes `src/generated/`: the
  resolved model as plain data (`src/model.rs`'s types), and
  `src/generated/bindings.rs`, the binding glue for the interfaces the
  browser exposes (`EXPOSED` in `xtask/src/bindings/glue.rs`). `cargo xtask
  check` fails if any generated file is stale.
- **The glue**, per exposed interface: a trait (`<Interface>Impl`) the
  platform implements, with IDL values as Rust types; a native function per
  member that checks `this`, the argument count, converts the arguments,
  resolves overloads, calls the trait and converts the result; and the code
  that installs the interface object, the interface prototype object, the
  constants, attributes and operations (WebIDL §3.7†). Every trait method
  has a default that throws a `NotSupportedError` naming the member.
- **Conversions** (`src/convert.rs`): WebIDL §3.2† for every type the
  exposed IDL uses: `any`, `undefined`, `boolean`, the integer types with
  `[EnforceRange]` and `[Clamp]` (ConvertToInt), `float`, `double` and their
  unrestricted forms, `DOMString` with `[LegacyNullToEmptyString]`,
  `ByteString`, `USVString`, `object`, interface types, callback interfaces,
  callback functions, nullable types, sequences, dictionaries, enumerations
  and unions (the last three generated).
- **Overload resolution** (`src/overload.rs`): the effective overload set and
  the overload resolution algorithm (§2.5.8†, §3.6†).
- **Wrappers** (`src/platform.rs`): one per platform object, made on first
  access with the prototype of its most derived interface and its
  `[LegacyUnforgeable]` members. The platform keeps them: `clazel-web` puts a
  node's in `clazel-dom`'s wrapper slot, the others in a side table.
- **Extended attributes:** `[LegacyUnforgeable]`, `[Replaceable]`,
  `[SameObject]`, `[PutForwards]`, `[LegacyLenientSetter]`, `[Reflect]` (for
  `DOMString` and `boolean`), `[Global]` (Window's members on the global
  object), `[HTMLConstructor]` (always "Illegal constructor": there are no
  custom elements).
- **`DOMException`** (`src/exception.rs`), written by hand because
  `webidl.idl` is not vendored: the constructor, `name`, `message`, `code`,
  the legacy code constants, and `DOMException.prototype`'s prototype
  `Error.prototype`.

## Deviations and what is not done

- **The global object is an ordinary object** standing for the `Window`:
  `clazel-js` cannot yet make a realm whose global is a host object. Its
  prototype is `Window.prototype`, and the bindings treat it as the Window
  platform object.
- **No `[[Prototype]]` named properties object** for `Window`
  (`WindowProperties`), no `@@toStringTag`, no `@@iterator` and no
  `iterable`, `maplike` or `setlike` declarations: the engine has no Symbols.
- **`sequence<T>` is read from an Array only**, by index, not with the
  iterator protocol (no Symbols).
- **Indexed and named properties** (legacy platform objects, so
  `[LegacyUnenumerableNamedProperties]` too) are not exposed: `clazel-js`
  does not call `HostObject`'s exotic hooks yet. `NodeList.item()` and
  `HTMLCollection.item()`/`namedItem()` work; `list[0]` does not.
- **Members left out**, with the reason for each, are listed in the header
  of `src/generated/bindings.rs`: types the bindings cannot convert
  (`Promise`, `record`, buffer types, `bigint`, interfaces not exposed),
  `[SecureContext]` members, and special operations without a name.
- **Event handler IDL attributes** (`onclick` and the rest, of type
  `EventHandler`, `OnErrorEventHandler` or `OnBeforeUnloadEventHandler`: HTML
  §8.1.8.1†) have no trait method: the glue converts the value
  (`convert::event_handler`: a non-object is null, an object is the callback,
  callable or not) and calls the platform's `Platform::event_handler_get` and
  `event_handler_set` with the event type's name. What a handler is, and when
  its content attribute is compiled, is the platform's (`clazel-web`'s
  `page::handlers`).
- **An operation of more than 7 parameters** (`initMouseEvent`,
  `initKeyboardEvent`) takes its arguments as one struct
  (`MouseEventInitMouseEventArgs`), so that the trait method does not pass
  clippy's `too_many_arguments`, which the workspace keeps. Dictionary members whose types cannot
  be converted are not read; the header lists them.
- **Overload resolution converts after choosing**: the arguments before the
  distinguishing index are converted once the overload is chosen; the
  values are the same, only the order of a conversion's exception against
  "no overload matches" differs.
- **Wrappers are kept by strong handles**; `clazel-js` has no collector yet.
- **`[PutForwards]` assigns with a throwing `Set`** (strict), where WebIDL
  says `Set(Q, forwardId, V, false)`.
