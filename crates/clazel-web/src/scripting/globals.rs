//! The least the page's scripts need before item 7.12's WebIDL bindings
//! exist, added through `clazel-js`'s embedding API only (phase-7.md, "The
//! engine as a library"):
//! - `document`, an ordinary object with `write`, `writeln`, `open` and
//!   `close` (HTML §8.4†, "Dynamic markup insertion", in [`super::write`])
//!   and a `currentScript` data property that the page sets before and after
//!   each classic script (HTML §3.1.?† `document.currentScript`; the
//!   standard's attribute is read-only, and a data property is what the
//!   engine can define without accessors);
//! - `performance`, with `now()` ([`super::time`]);
//! - a wrapper per node for `currentScript` to name: a host object holding
//!   the node id ([`NodeRef`]), the same object for the same node.
//!
//! Item 7.12 replaces all of this with the generated `Document`,
//! `Performance` and `Element` interfaces; nothing else here depends on the
//! shapes.

use clazel_js::{HostObject, Key, Local, Realm, Result, Scope};

use super::state::state;
use super::time::performance_now_ms;

/// The host object behind a node's wrapper: the node's id in the document
/// of one generation (see [`super::state::PageState::generation`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeRef {
    /// The node's id in the arena.
    pub node: usize,
    /// The document generation it belongs to.
    pub generation: u64,
}

impl HostObject for NodeRef {}

/// Defines `document` and `performance` on the realm's global object.
pub(crate) fn install(scope: &mut Scope<'_>, realm: &Realm) -> Result<()> {
    let global = scope.global(realm)?;
    let document = scope.new_object()?;
    scope.define_method(document, "write", 1, |scope, args| {
        super::write::document_write(scope, args, false)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(document, "writeln", 1, |scope, args| {
        super::write::document_write(scope, args, true)?;
        Ok(scope.undefined())
    })?;
    scope.define_method(document, "open", 0, |scope, _args| {
        super::write::document_open(scope)?;
        document_object(scope)
    })?;
    scope.define_method(document, "close", 0, |scope, _args| {
        super::write::document_close(scope)?;
        Ok(scope.undefined())
    })?;
    let null = scope.null();
    scope.set(document, Key::from("currentScript"), null)?;
    scope.set(global, Key::from("document"), document)?;
    let handle = scope.persist(document);
    state(scope)?.document_object = Some(handle);

    let performance = scope.new_object()?;
    scope.define_method(performance, "now", 0, |scope, _args| {
        let st = state(scope)?;
        let now = st.clock.now_us();
        let ms = performance_now_ms(st.time_origin_us, now);
        Ok(scope.number(ms))
    })?;
    scope.set(global, Key::from("performance"), performance)?;
    Ok(())
}

/// The `document` object.
pub(crate) fn document_object<'s>(scope: &mut Scope<'s>) -> Result<Local<'s>> {
    match state(scope)?.document_object.clone() {
        Some(h) => scope.local(&h),
        None => Ok(scope.undefined()),
    }
}

/// The wrapper of `node`: made once per node and generation, then the same
/// object.
pub(crate) fn wrapper<'s>(scope: &mut Scope<'s>, node: usize) -> Result<Local<'s>> {
    let st = state(scope)?;
    if let Some(h) = st.wrappers.get(&node).cloned() {
        return scope.local(&h);
    }
    let generation = st.generation;
    let plain = scope.new_object()?;
    let prototype = scope.get_prototype_of(plain)?;
    let object = scope.new_host_object(Some(prototype), NodeRef { node, generation })?;
    let handle = scope.persist(object);
    state(scope)?.wrappers.insert(node, handle);
    Ok(object)
}

/// Sets `document.currentScript` to `node`'s wrapper, or null.
pub(crate) fn set_current_script(scope: &mut Scope<'_>, node: Option<usize>) -> Result<()> {
    state(scope)?.current_script = node;
    let document = document_object(scope)?;
    if scope.as_boolean(document).is_none()
        && scope.kind(document) == clazel_js::ValueKind::Undefined
    {
        return Ok(());
    }
    let value = match node {
        Some(n) => wrapper(scope, n)?,
        None => scope.null(),
    };
    scope.set(document, Key::from("currentScript"), value)
}

/// The node a wrapper names, if `value` is one of the current document's.
pub fn node_of(scope: &mut Scope<'_>, value: Local<'_>) -> Option<NodeRef> {
    scope.host_data::<NodeRef>(value).ok().copied()
}
