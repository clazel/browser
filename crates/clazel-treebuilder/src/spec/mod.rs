//! Executable-style specification of HTML tree construction. Nothing here
//! runs; it defines what "correct" means. Every algorithm cites its section,
//! and each `// N.` comment is the step number in it; the insertion modes
//! number their cases in the standard's order.
//!
//! Source (pinned; a review is against exactly this text): HTML Standard,
//! Living Standard, `source` at commit
//! `939677714df7379fee3667040113b41c91c851e7` (26 October 2026),
//! <https://html.spec.whatwg.org/multipage/parsing.html>: §13.2.4 "Parse
//! state", §13.2.6 "Tree construction" (§13.2.6.1 to §13.2.6.5), §13.2.7
//! "The end" and §13.4 "Parsing HTML fragments"; the DOM operations are
//! `clazel-dom`'s (DOM Standard, commit snapshot `3c53f93a…`).
//!
//! The standard at this commit differs from the plan's description (Phase 4
//! item 4.9) in three ways, and this transcription follows the standard:
//! there are 21 insertion modes, not 23 ("in select" and "in select in
//! table" were removed, and `select` content is parsed by the "in body"
//! rules); the tokenizer emits processing instruction tokens, which the
//! modes insert as `ProcessingInstruction` nodes; and §13.2.4.5 adds a
//! sanitizer configuration, an insertion target redirection map, a
//! four-valued scripting mode and template "content patching".
//!
//! Modules:
//! - [`base::tags`]: the tag names the rules mention, as an enum.
//! - [`tables`]: the attribute and tag name adjustment tables.
//! - [`state`]: §13.2.4 parse state, tokens and actions, and §13.2.4's
//!   algorithms (scopes, "reset the insertion mode appropriately", the list
//!   of active formatting elements).
//! - [`insert`]: §13.2.6.1 to §13.2.6.3, and "reconstruct the active
//!   formatting elements".
//! - [`modes`]: §13.2.6.4's 21 insertion modes and §13.2.6.5 foreign
//!   content.
//! - [`dispatch`]: the tree construction dispatcher, reprocessing, the
//!   one-token step `dispatch`, the whole parser `parse` and §13.4
//!   `parse_fragment`.
//!
//! Modelling choices (each a difference in form, never in meaning, or a
//! stated restriction of what is modelled):
//! - **The step is a transducer.** `dispatch(env, parser, token) ->
//!   (parser, actions)` handles one token. `Action::ChangeEncoding` is
//!   §13.2.3.4 "change the encoding" (the "in head" `meta` rule), handed to
//!   the driver: every branch of that algorithm ends with the confidence
//!   *certain* (it either sets it or restarts the parse with it), so the
//!   parser sets its `tentative` flag to false when it emits the action.
//!   `Action::ScriptReady(node)` is "prepare the script element", which needs
//!   scripting (Phase 7), so the parser's own steps after it are those of a
//!   script that does nothing (the "text" mode's `script` end tag case).
//!   `Action::StopParsing` is §13.2.7 "stop parsing" (its step 4 is
//!   modelled; the rest is the driver's) or the node limit.
//! - **The node limit.** A node is created only while the arena has room
//!   (`clazel_dom::spec::max_nodes`); otherwise the parser stops parsing
//!   (`insert::create`). A stopped parser changes nothing, and every later
//!   step of the same token, and every later token, is a no-op.
//! - **Reprocessing** is a loop of rule applications ([`dispatch::run`]):
//!   "reprocess the token" applies the rules of the current insertion mode
//!   in HTML content (not the dispatcher: the standard's phrase in foreign
//!   content says so explicitly, and the dispatcher runs "as each token is
//!   emitted from the tokenizer"); "using the rules for m" applies m's
//!   rules. The loop has fuel, `fuel_bound(parser)` applications;
//!   `theorem_dispatch_total` proves the fuel is never exhausted, which is
//!   the standard's implicit claim that reprocessing ends.
//! - **Tokens.** The tree builder's input is `state::Token`, the tokenizer's
//!   token kinds with the same fields as `clazel-html`'s; a tag token's name
//!   is classified once into a [`tags::Tag`] (`state::classify`). Its
//!   attributes become DOM attributes with no namespace, so "adjust foreign
//!   attributes" can namespace them. A character token is one code point;
//!   "insert a character" appends it to an adjacent `Text` node.
//! - **The stack of open elements and the list of active formatting
//!   elements hold `state::Elem` records** (the node's id, namespace, local
//!   name and its `Tag`, and whether an `annotation-xml` start tag made it an
//!   HTML integration point), not bare nodes: these never change after the
//!   element is created, so the record is the node's own.
//! - **Every DOM call is guarded by its precondition** (`insert::dom_insert`,
//!   `insert::dom_remove`): "ensure pre-insert validity … does not throw" is
//!   an assertion of the standard, so the guard never changes the result on
//!   a call the parser makes; it makes the assertion explicit.
//! - **The tokenizer is a parameter** ([`dispatch::TokFns`]): its state is
//!   opaque, apart from the switches the tree builder asks for
//!   (`Parser::tokenizer`, applied by the driver before the next token) and
//!   the foreign-content flag the CDATA rule reads
//!   (`state::in_foreign_content`). Encoding §4.2 "get an encoding" and
//!   HTML's "extracting a character encoding from a meta element" are
//!   parameters too ([`state::EncFns`]).
//! - **Not modelled (restrictions):** the sanitizer configuration is always
//!   null (`setHTML` is Phase 7), so the redirection map's only entry is the
//!   fragment case's (root, fragment) of §13.4 step 15; "allow declarative
//!   shadow roots" is false, so a `template` with `shadowrootmode` is a
//!   plain template (shadow trees are not in `clazel-dom`); template
//!   content patching (a `template` with a `for` attribute, §13.2.6.4.4
//!   step 13.2) is not modelled and the template is inserted as a plain
//!   template, so a template's "insertion target" is always null; custom
//!   elements, "is", the speculative HTML parser, the insertion point and
//!   `document.write`, scripts (the parser pause flag is never set) and parse
//!   errors (the standard proceeds the same way with or without them) are
//!   not modelled. The scripting mode is reduced to the scripting flag the
//!   rules read (Normal, Fragment and Inert are "not Disabled"). The
//!   document is never an `iframe` `srcdoc` document, and the parser can
//!   always change the document's mode.
//! - **The fragment case** (§13.4) builds its own arena: the document node,
//!   the context element (no parent, so step 19 finds a form only if the
//!   context is one), the `html` root appended to the document, and the
//!   `DocumentFragment` the redirection map sends root's insertions to.
//!   Step 22's "adopt fragment into target's node document" changes nothing
//!   in one arena.

pub mod base;
pub mod modes;

#[cfg(verus_only)]
pub use crate::invariant::*;
pub use base::*;
#[cfg(verus_only)]
pub use clazel_dom::spec as dom;
pub use clazel_dom::spec::{Attr, Document, DocumentMode, Namespace, NodeId, NodeKind};
pub use modes::*;
