# TodoMVC: the vanilla JavaScript, React and Vue implementations

Upstream: https://github.com/tastejs/todomvc/tree/ff43b02e59dfa604386bb382034b2cd07c2bcd8a
Commit: ff43b02e59dfa604386bb382034b2cd07c2bcd8a
License: MIT (`LICENSE.md`, copied from `license.md` at the root of tastejs/todomvc: "Everything in this repo is MIT License unless otherwise specified.")

The commit is tastejs/todomvc's head on 2026-11-16 (committed 2026-05-03).
Copied byte for byte, with upstream's paths:

- `examples/javascript-es6/`: the vanilla JavaScript one (no framework).
  There is also `examples/javascript-es5/`; the ES6 one uses the modern
  features (classes, arrow functions, template literals, `const`) the engine
  must run. The ES5 one is not vendored.
- `examples/react/`
- `examples/vue/`
- `app-spec.md`: the behaviour all of them implement.

Each example's `dist/` is the built application (what a browser loads);
`src/` is the source it was built from, kept so that a failure in the
bundle can be read against it. Left out, as nothing runs them: every
`package-lock.json` (up to 400 kB each) and every source map (`*.map`, 1.4 MB
for React's).

`xtask/src/testdata/inventory.rs` writes `tests/generated/todomvc.rs`, the
inventory of every file's path, size and SHA-256. This directory is a tree
(`TREE_SUITES` in `xtask/src/testdata.rs`). Item 7.20 serves the `dist/`
directories from its in-process server. To update, copy the same directories
from a newer commit, change the commit above, and run `cargo xtask testdata`.
