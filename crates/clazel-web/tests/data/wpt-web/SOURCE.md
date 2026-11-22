# WPT testharness.js tests for the script-facing web platform

Upstream: https://github.com/web-platform-tests/wpt/tree/10dd48f8bc0c18d6b695c83dfa230880385dbf79
Commit: 10dd48f8bc0c18d6b695c83dfa230880385dbf79
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The same WPT commit `clazel-idna` pins (2026-10-20): the newest of the three
the repository vendors, so that every WPT suite is read at one commit or an
older one. Copied byte for byte, with the paths WPT has, these directories
(phase-7.md exit criterion 2) and one file:

- `dom/nodes/`, `dom/events/`, `dom/collections/`
- `html/webappapis/timers/`, `html/webappapis/microtask-queuing/`,
  `html/semantics/scripting-1/`
- `fetch/api/basic/`, `fetch/api/cors/`, `xhr/`
- `resources/testharness.js`

Whole directories are vendored, not the "listed subsets" the plan will run:
choosing the subset needs the engine, so it waits for item 7.15. The server
side (`.py` handlers, `.headers` files) and `WEB_FEATURES.yml` come with
them, as a runner that serves a test needs the handler beside it. Tests
include other WPT files by absolute URL (`/resources/testharnessreport.js`,
`/common/`, `/resources/WebIDLParser.js`, `/resources/idlharness.js`,
`/dom/common.js` and more); those are not vendored yet, and the runner (item
7.15) will name which it needs and add them here. `url/`, `cookies/` and
`webstorage/` of the same criterion are vendored by their Phase 1 and 2
suites (`wpt-url-*`, `wpt-cookies`, `wpt-webstorage`), as data; running them
as scripts is item 7.17.

`xtask/src/testdata/inventory.rs` writes `tests/generated/wpt_web.rs`, the
inventory of every file's path, size and SHA-256. This directory is a tree
(`TREE_SUITES` in `xtask/src/testdata.rs`), so the inventory is what fails
when a file is added, removed or changed. To update, copy the same
directories from a newer commit, change the commit above, and run
`cargo xtask testdata`.

The crate's attributes file turns line-ending conversion off for
`tests/data/`: some tests are about CR and LF.
