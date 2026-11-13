# HTML §15 "Rendering", whatwg/html at one commit

Commit: 4c54fae106900a24130da614b7ad29d85c6981c6 (2026-11-11, "Meta: update links to moved CSS definitions")
License: Creative Commons Attribution 4.0 International, with portions incorporated into source code under the BSD 3-Clause License (`LICENSE`, copied from the same commit)

`rendering.html` is an excerpt of the standard's single source file,
https://raw.githubusercontent.com/whatwg/html/4c54fae106900a24130da614b7ad29d85c6981c6/source
(SHA-256 `17d5541ac0f87fb8e9cba0ce19af64e9edc47563dd84fd779df188cd8f9aab4c`), byte for
byte: its lines 153937 to 155984, from `<h2 split-filename="rendering" id="rendering">`
(§15) to the line before `<h3 id="widgets">` (§15.5). To reproduce it:
`sed -n '153937,155984p' source`. That is §15.1 to §15.4: the introduction, "The CSS user
agent style sheet and presentational hints", the non-replaced elements and the replaced
elements, with every CSS block of the user agent style sheet the Phase 5 subset uses.

`cargo xtask check` hashes each file and fails if one differs from the line below, or if
the directory holds anything else:

SHA-256: 2b1dae776fd9cda6494d114f5e60d03b9b560943909b88f2ee4c53eabf6078d1 rendering.html

`xtask/src/ua_sheet.rs` reads the CSS blocks (`<pre><code class="css">`) of
`rendering.html` and writes them, with the markup inside them removed, to
`crates/clazel-style/data/ua.css`, `ua-quirks.css` and `hints.css` (`cargo xtask
tables`); its table `BLOCKS` says which block goes where and why, and `check` fails if a
block's section or the sentence that introduces it has changed, or if a generated file is
stale.
