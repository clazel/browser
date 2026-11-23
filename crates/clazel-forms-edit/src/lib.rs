//! Form controls' behaviour (Phase 6 item 6.15): focus, text field editing,
//! checkbox and radio toggling, `select`, implicit submission and the
//! `required` constraint, over `clazel-forms`' control state table. The
//! controls' look and their text geometry are `clazel-layout`'s
//! (`controls`).
//!
//! Spec: HTML Standard, commit `0793d3d8544eee95a862e6637130a8106c3d11ca`
//! (as item 6.13 pins it); each module's header names its sections and lists
//! its modelling choices. Tier: 0 (see `[package.metadata.clazel]` in
//! `Cargo.toml` and `docs/VERIFICATION.md`); there is no spec file or proof
//! here, by decision 6.0(b).
//!
//! - [`field`]: one text control's value, caret and selection.
//! - [`focus`]: what is focusable and Tab's order.
//! - [`validate`]: the `required` constraint.
//! - [`editor`]: the state of a document's controls and what events do to it.
//! - [`input`]: `Input` messages to events.
//! - [`geometry`]: the editor's view of a laid-out page.
//!
//! Not here (listed in the modules): the clipboard, IME composition, `pattern`
//! and the other constraints, word and line selection, keyboard movement
//! between radio buttons, `label` activation, scripts.

pub mod dom;
pub mod editor;
pub mod field;
pub mod focus;
pub mod geometry;
pub mod input;
pub mod validate;
