# clazel-webidl

Part of [Clazel](../../README.md). The generated WebIDL bindings, the WebIDL
type conversions and `DOMException` for the JavaScript engine
([phase-7.md](../../docs/phases/phase-7.md) items 7.12 and 7.13).

Tier 0, target tier 0. Item 7.1 vendored the IDL that the bindings generator
reads: see `tests/data/webref-idl/SOURCE.md`.

Item 7.12's first slice is in: `cargo xtask bindings` parses that IDL with our
own parser (`xtask/src/bindings/`, following the grammar of WebIDL §2), merges
partial interfaces, mixins and `includes`, and writes the resolved model as
plain data into `src/generated/` (the types are `src/model.rs`). `cargo xtask
check` fails if the committed files are stale. Not done yet: the JS-engine
glue (conversions, overload resolution, wrappers, `DOMException`), which needs
`clazel-js`'s embedding API (item 7.8) and is generated from this model.
