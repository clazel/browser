//! DOM event dispatch (§2.9†) and the listener lists (§2.7†) on trees built
//! by hand: each test names the step it covers. The ones marked "WPT" mirror
//! the expectation of a vendored `dom/events/` test that needs no JS engine
//! beyond its listeners' bodies (`tests/data/wpt-web/dom/events/`); they are
//! transcriptions, not runs of the suite, so no `clazel-conformance:` line is
//! printed.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_web::events::{
    AddOptions, DispatchError, Event, EventInit, EventPhase, Host, Invocation, ListenerId,
    Listeners, TargetId, build_path, dispatch, dispatch_event, dispatch_path,
};
use std::collections::BTreeMap;

fn u(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

struct Tree {
    arena: Arena,
}

impl Tree {
    fn new() -> Tree {
        Tree {
            arena: Arena::new(Vec::new()),
        }
    }

    fn make(&mut self, kind: ExecKind) -> usize {
        match self.arena.create(kind) {
            Some(n) => n,
            None => unreachable!("node limit"),
        }
    }

    fn el(&mut self, parent: usize, name: &str) -> usize {
        let e = self.make(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: u(name),
            attributes: Vec::<ExecAttr>::new(),
            template_contents: None,
            form_owner: None,
        });
        self.arena.append(parent, e);
        e
    }
}

/// `#0 document > html > body > div(p) > div(c)`, plus a loose `div`.
struct Doc {
    t: Tree,
    document: usize,
    html: usize,
    body: usize,
    p: usize,
    c: usize,
}

fn doc() -> Doc {
    let mut t = Tree::new();
    let document = 0;
    let html = t.el(document, "html");
    let body = t.el(html, "body");
    let p = t.el(body, "div");
    let c = t.el(p, "div");
    Doc {
        t,
        document,
        html,
        body,
        p,
        c,
    }
}

/// What a scripted callback does when called.
#[derive(Clone)]
enum Act {
    PreventDefault,
    StopPropagation,
    StopImmediate,
    SetCancelBubble,
    SetReturnValueFalse,
    /// Remove (target, type, callback, capture).
    Remove(TargetId, &'static str, u64, bool),
    /// Add (target, type, callback, options).
    Add(TargetId, &'static str, u64, AddOptions),
    /// `dispatchEvent` the same event again at the target; records the result.
    Redispatch(TargetId),
    /// Record `composedPath()`.
    RecordPath,
    /// `initEvent("other", false, true)`.
    InitEvent,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Rec {
    id: u64,
    current: Option<TargetId>,
    target: Option<TargetId>,
    phase: EventPhase,
    passive: bool,
}

struct TestHost<'a> {
    arena: &'a Arena,
    acts: BTreeMap<u64, Vec<Act>>,
    log: Vec<Rec>,
    windows: bool,
    redispatch: Vec<Result<bool, DispatchError>>,
    paths: Vec<Vec<TargetId>>,
}

impl<'a> TestHost<'a> {
    fn new(arena: &'a Arena) -> TestHost<'a> {
        TestHost {
            arena,
            acts: BTreeMap::new(),
            log: Vec::new(),
            windows: false,
            redispatch: Vec::new(),
            paths: Vec::new(),
        }
    }

    fn on(&mut self, id: u64, acts: &[Act]) {
        self.acts.insert(id, acts.to_vec());
    }

    fn ids(&self) -> Vec<u64> {
        self.log.iter().map(|r| r.id).collect()
    }
}

impl Host for TestHost<'_> {
    fn invoke(&mut self, call: Invocation<'_>) {
        let id = call.listener.0;
        self.log.push(Rec {
            id,
            current: call.event.current_target(),
            target: call.event.target(),
            phase: call.event.event_phase(),
            passive: call.event.in_passive_listener(),
        });
        let acts = self.acts.get(&id).cloned().unwrap_or_default();
        for a in acts {
            match a {
                Act::PreventDefault => call.event.prevent_default(),
                Act::StopPropagation => call.event.stop_propagation(),
                Act::StopImmediate => call.event.stop_immediate_propagation(),
                Act::SetCancelBubble => call.event.set_cancel_bubble(true),
                Act::SetReturnValueFalse => call.event.set_return_value(false),
                Act::Remove(t, ty, cb, cap) => {
                    call.listeners
                        .remove_event_listener(t, &u(ty), ListenerId(cb), cap);
                }
                Act::Add(t, ty, cb, opts) => {
                    call.listeners
                        .add_event_listener(self.arena, t, &u(ty), ListenerId(cb), opts);
                }
                Act::Redispatch(t) => {
                    let arena = self.arena;
                    let r = dispatch_event(arena, call.listeners, t, call.event, self);
                    self.redispatch.push(r);
                }
                Act::InitEvent => call.event.init_event(&u("other"), false, true),
                Act::RecordPath => self.paths.push(call.event.composed_path().to_vec()),
            }
        }
    }

    fn has_window(&self, _document: usize, _event: &Event) -> bool {
        self.windows
    }
}

fn node(n: usize) -> TargetId {
    TargetId::Node(n)
}

fn capture() -> AddOptions {
    AddOptions {
        capture: true,
        ..AddOptions::default()
    }
}

fn bubbling() -> Event {
    Event::new(
        &u("click"),
        EventInit {
            bubbles: true,
            ..EventInit::default()
        },
        0.0,
    )
}

fn add(l: &mut Listeners, d: &Doc, t: TargetId, ty: &str, id: u64, o: AddOptions) -> bool {
    l.add_event_listener(&d.t.arena, t, &u(ty), ListenerId(id), o)
}

// ---------- the event object ----------

#[test]
fn event_attributes() {
    let e = Event::new(
        &u("foo"),
        EventInit {
            bubbles: true,
            cancelable: false,
            composed: true,
        },
        12.5,
    );
    assert_eq!(e.type_(), u("foo").as_slice());
    assert!(e.bubbles() && !e.cancelable() && e.composed());
    assert!(!e.is_trusted());
    assert_eq!(e.time_stamp(), 12.5);
    assert_eq!(e.target(), None);
    assert_eq!(e.current_target(), None);
    assert_eq!(e.event_phase(), EventPhase::None);
    assert_eq!(e.event_phase().code(), 0);
    assert!(!e.default_prevented() && e.return_value());
    assert!(!e.cancel_bubble() && !e.is_dispatching());
    assert!(Event::new_trusted(&u("x"), EventInit::default(), 0.0).is_trusted());
    assert_eq!(
        [
            EventPhase::None.code(),
            EventPhase::Capturing.code(),
            EventPhase::AtTarget.code(),
            EventPhase::Bubbling.code()
        ],
        [0, 1, 2, 3]
    );
}

/// DOM §2.2† "set the canceled flag": only a cancelable event is canceled.
/// (WPT Event-defaultPrevented.html, Event-returnValue.html.)
#[test]
fn prevent_default_needs_cancelable() {
    let mut e = Event::new(&u("x"), EventInit::default(), 0.0);
    e.prevent_default();
    assert!(!e.default_prevented());
    e.set_return_value(false);
    assert!(!e.default_prevented());
    let mut e = Event::new(
        &u("x"),
        EventInit {
            cancelable: true,
            ..EventInit::default()
        },
        0.0,
    );
    e.set_return_value(true);
    assert!(!e.default_prevented());
    e.set_return_value(false);
    assert!(e.default_prevented() && !e.return_value());
}

/// `cancelBubble` only ever sets the stop propagation flag.
/// (WPT Event-cancelBubble.html.)
#[test]
fn cancel_bubble_setter() {
    let mut e = bubbling();
    e.set_cancel_bubble(false);
    assert!(!e.cancel_bubble());
    e.set_cancel_bubble(true);
    assert!(e.cancel_bubble() && !e.stop_immediate_propagation_flag());
    e.set_cancel_bubble(false);
    assert!(e.cancel_bubble());
}

/// `initEvent` while dispatching does nothing; after, it resets the flags.
/// (WPT Event-init-while-dispatching.html, Event-initEvent.html.)
#[test]
fn init_event() {
    let mut e = Event::new(
        &u("a"),
        EventInit {
            cancelable: true,
            ..EventInit::default()
        },
        0.0,
    );
    e.prevent_default();
    e.stop_immediate_propagation();
    e.init_event(&u("b"), true, false);
    assert_eq!(e.type_(), u("b").as_slice());
    assert!(e.bubbles() && !e.cancelable());
    assert!(!e.default_prevented() && !e.cancel_bubble());
    assert!(!e.stop_immediate_propagation_flag());
}

#[test]
fn init_event_while_dispatching_is_ignored() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 2, AddOptions::default());
    h.on(1, &[Act::InitEvent]);
    let mut e = bubbling();
    let r = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(r, Ok(true));
    // The type did not change, so the parent's listener still ran.
    assert_eq!(h.ids(), [1, 2]);
    assert_eq!(e.type_(), u("click").as_slice());
    assert!(e.bubbles() && !e.cancelable());
}

// ---------- the event path, phases ----------

/// WPT Event-dispatch-order.html: capture on the parent, then the child's
/// bubble listener, then the parent's bubble listener.
#[test]
fn phase_order() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.p), "click", 1, capture());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 3, AddOptions::default());
    let mut e = bubbling();
    let r = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(r, Ok(true));
    assert_eq!(h.ids(), [1, 2, 3]);
}

/// The path of a node is the node, its ancestors up to the root; a Document
/// with no Window ends there.
#[test]
fn path_without_window() {
    let d = doc();
    let e = bubbling();
    let path = build_path(&d.t.arena, node(d.c), &e, &|_, _| false).unwrap_or_default();
    let targets: Vec<TargetId> = path.iter().map(|i| i.invocation_target).collect();
    assert_eq!(
        targets,
        [
            node(d.c),
            node(d.p),
            node(d.body),
            node(d.html),
            node(d.document)
        ]
    );
    // Only the first item has a shadow-adjusted target.
    assert_eq!(
        path.first().and_then(|i| i.shadow_adjusted_target),
        Some(node(d.c))
    );
    assert!(
        path.iter()
            .skip(1)
            .all(|i| i.shadow_adjusted_target.is_none())
    );
}

/// "Get the parent" of a Document is the Window, except for `load` or
/// without a browsing context.
#[test]
fn document_to_window() {
    let d = doc();
    let e = bubbling();
    let path = build_path(&d.t.arena, node(d.c), &e, &|doc, _| doc == 0).unwrap_or_default();
    assert_eq!(
        path.last().map(|i| i.invocation_target),
        Some(TargetId::Window)
    );
    assert_eq!(path.len(), 6);
    let load = Event::new(&u("load"), EventInit::default(), 0.0);
    let path = build_path(&d.t.arena, node(d.c), &load, &|_, _| true).unwrap_or_default();
    assert_eq!(
        path.last().map(|i| i.invocation_target),
        Some(node(d.document))
    );
    // A Window target has no parent.
    let path = build_path(&d.t.arena, TargetId::Window, &e, &|_, _| true).unwrap_or_default();
    assert_eq!(path.len(), 1);
}

/// A Window listener runs first in capture and last in bubble, and `target`
/// stays the dispatch target. (Shape of WPT Event-dispatch-handlers-changed
/// and Event-dispatch-omitted-capture.)
#[test]
fn window_in_the_path() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    h.windows = true;
    add(&mut l, &d, TargetId::Window, "foo", 1, capture());
    add(
        &mut l,
        &d,
        TargetId::Window,
        "foo",
        2,
        AddOptions::default(),
    );
    add(
        &mut l,
        &d,
        node(d.document),
        "foo",
        3,
        AddOptions::default(),
    );
    add(&mut l, &d, node(d.c), "foo", 4, AddOptions::default());
    let mut e = Event::new(
        &u("foo"),
        EventInit {
            bubbles: true,
            ..EventInit::default()
        },
        0.0,
    );
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(true)
    );
    assert_eq!(h.ids(), [1, 4, 3, 2]);
    assert!(h.log.iter().all(|r| r.target == Some(node(d.c))));
    let phases: Vec<EventPhase> = h.log.iter().map(|r| r.phase).collect();
    assert_eq!(
        phases,
        [
            EventPhase::Capturing,
            EventPhase::AtTarget,
            EventPhase::Bubbling,
            EventPhase::Bubbling
        ]
    );
    let currents: Vec<Option<TargetId>> = h.log.iter().map(|r| r.current).collect();
    assert_eq!(
        currents,
        [
            Some(TargetId::Window),
            Some(node(d.c)),
            Some(node(d.document)),
            Some(TargetId::Window)
        ]
    );
    // After dispatch: phase none, no currentTarget, target kept.
    assert_eq!(e.event_phase(), EventPhase::None);
    assert_eq!(e.current_target(), None);
    assert_eq!(e.target(), Some(node(d.c)));
}

/// Without bubbles, ancestors' non-capture listeners do not run, capture
/// ones do, and the target runs both kinds.
#[test]
fn non_bubbling() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.p), "click", 1, capture());
    add(&mut l, &d, node(d.p), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 3, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 4, capture());
    let mut e = Event::new(&u("click"), EventInit::default(), 0.0);
    assert_eq!(
        dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(true)
    );
    // At the target the capture listener runs in the capture pass, first.
    assert_eq!(h.ids(), [1, 4, 3]);
}

/// WPT Event-dispatch-order-at-target.html: at the target, capturing
/// listeners come first whatever the registration order and `bubbles`.
#[test]
fn at_target_order() {
    let d = doc();
    for bubbles in [true, false] {
        let mut l = Listeners::new();
        let mut h = TestHost::new(&d.t.arena);
        add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
        add(&mut l, &d, node(d.c), "click", 2, capture());
        let mut e = Event::new(
            &u("click"),
            EventInit {
                bubbles,
                ..EventInit::default()
            },
            0.0,
        );
        let _ = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
        assert_eq!(h.ids(), [2, 1], "bubbles: {bubbles}");
        assert!(h.log.iter().all(|r| r.phase == EventPhase::AtTarget));
    }
}

/// `currentTarget`, `target` and `eventPhase` seen by each listener.
#[test]
fn per_listener_state() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.body), "click", 1, capture());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.body), "click", 3, AddOptions::default());
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    let want = [
        (1, d.body, EventPhase::Capturing),
        (2, d.c, EventPhase::AtTarget),
        (3, d.body, EventPhase::Bubbling),
    ];
    assert_eq!(h.log.len(), 3);
    for (r, (id, cur, ph)) in h.log.iter().zip(want) {
        assert_eq!(r.id, id);
        assert_eq!(r.current, Some(node(cur)));
        assert_eq!(r.target, Some(node(d.c)));
        assert_eq!(r.phase, ph);
    }
}

/// Only listeners of the event's type run; others are skipped.
#[test]
fn type_filter() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "keydown", 1, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [2]);
}

/// A detached node's path is itself.
#[test]
fn detached_target() {
    let mut d = doc();
    let frag = d.t.make(ExecKind::DocumentFragment { host: None });
    let lone = d.t.el(frag, "div");
    d.t.arena.remove(lone);
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(lone), "click", 1, AddOptions::default());
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(lone), &mut e, &mut h);
    assert_eq!(h.ids(), [1]);
}

/// Dispatching at the Window alone.
#[test]
fn window_target() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(
        &mut l,
        &d,
        TargetId::Window,
        "click",
        1,
        AddOptions::default(),
    );
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, TargetId::Window, &mut e, &mut h);
    assert_eq!(h.ids(), [1]);
    assert_eq!(h.log.first().map(|r| r.phase), Some(EventPhase::AtTarget));
}

#[test]
fn no_such_node() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let mut e = bubbling();
    assert_eq!(
        dispatch(&d.t.arena, &mut l, node(9999), &mut e, &mut h),
        Err(DispatchError::NoSuchNode)
    );
    assert!(!e.is_dispatching());
}

// ---------- propagation flags ----------

/// WPT Event-stopImmediatePropagation.html: later listeners of the same
/// target and every later target are skipped.
#[test]
fn stop_immediate_propagation() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 3, AddOptions::default());
    h.on(1, &[Act::StopImmediate]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1]);
    // The flags are unset when dispatch ends.
    assert!(!e.cancel_bubble() && !e.stop_immediate_propagation_flag());
}

/// WPT Event-dispatch-multiple-stopPropagation.html: the target's other
/// listeners still run, later targets do not.
#[test]
fn stop_propagation_finishes_the_target() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 3, AddOptions::default());
    h.on(1, &[Act::StopPropagation]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1, 2]);
}

/// Stopping in the capture pass at an ancestor stops the rest, including
/// the at-target and bubble passes.
#[test]
fn stop_propagation_in_capture() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.body), "click", 1, capture());
    add(&mut l, &d, node(d.p), "click", 2, capture());
    add(&mut l, &d, node(d.c), "click", 3, AddOptions::default());
    add(&mut l, &d, node(d.body), "click", 4, AddOptions::default());
    h.on(1, &[Act::StopPropagation]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1]);
}

/// `cancelBubble = true` is `stopPropagation()`. (WPT Event-cancelBubble.html.)
#[test]
fn cancel_bubble_stops() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 2, AddOptions::default());
    h.on(1, &[Act::SetCancelBubble]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1]);
}

/// The flags set before dispatch are not kept as "set" for a second
/// dispatch: dispatch ends by unsetting them.
#[test]
fn flags_reset_for_next_dispatch() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 2, AddOptions::default());
    h.on(1, &[Act::StopPropagation]);
    let mut e = bubbling();
    let _ = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    let _ = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1, 1]);
}

// ---------- canceled flag and the return value ----------

#[test]
fn return_value() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.p), "click", 1, AddOptions::default());
    h.on(1, &[Act::PreventDefault]);
    let cancelable = EventInit {
        bubbles: true,
        cancelable: true,
        composed: false,
    };
    // Canceled: false.
    let mut e = Event::new(&u("click"), cancelable, 0.0);
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(false)
    );
    assert!(e.default_prevented());
    // Not cancelable: true, and not canceled. (WPT EventTarget-dispatchEvent-returnvalue.html.)
    let mut e = bubbling();
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(true)
    );
    assert!(!e.default_prevented());
    // returnValue = false cancels the same way.
    h.on(1, &[Act::SetReturnValueFalse]);
    let mut e = Event::new(&u("click"), cancelable, 0.0);
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(false)
    );
}

/// WPT Event-dispatch-bubble-canceled.html: preventing default does not
/// stop propagation.
#[test]
fn prevent_default_does_not_stop() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    add(&mut l, &d, node(d.p), "click", 2, AddOptions::default());
    h.on(1, &[Act::PreventDefault]);
    let mut e = Event::new(
        &u("click"),
        EventInit {
            bubbles: true,
            cancelable: true,
            composed: false,
        },
        0.0,
    );
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [1, 2]);
}

// ---------- listener options ----------

/// "inner invoke": a passive listener cannot cancel, and the flag is unset
/// afterwards, so the next (non-passive) listener can.
#[test]
fn passive_listener() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let passive = AddOptions {
        passive: Some(true),
        ..AddOptions::default()
    };
    add(&mut l, &d, node(d.c), "click", 1, passive);
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    h.on(1, &[Act::PreventDefault]);
    let mut e = Event::new(
        &u("click"),
        EventInit {
            cancelable: true,
            ..EventInit::default()
        },
        0.0,
    );
    let r = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(r, Ok(true));
    assert!(!e.default_prevented());
    assert_eq!(
        h.log.iter().map(|r| r.passive).collect::<Vec<_>>(),
        [true, false]
    );
    assert!(!e.in_passive_listener());
    // A non-passive listener cancels.
    h.on(2, &[Act::PreventDefault]);
    let mut e = Event::new(
        &u("click"),
        EventInit {
            cancelable: true,
            ..EventInit::default()
        },
        0.0,
    );
    assert_eq!(
        dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(false)
    );
}

/// `once`: removed before the callback runs, so it runs once.
/// (WPT AddEventListenerOptions-once.any.js.)
#[test]
fn once_listener() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let once = AddOptions {
        once: true,
        ..AddOptions::default()
    };
    add(&mut l, &d, node(d.c), "click", 1, once);
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    for _ in 0..3 {
        let mut e = bubbling();
        let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    }
    assert_eq!(h.ids(), [1, 2, 2, 2]);
    assert_eq!(l.listeners(node(d.c)).len(), 1);
}

/// A `once` listener is gone while its own callback runs: a nested dispatch
/// from it does not re-enter it. (WPT AddEventListenerOptions-once.any.js,
/// "Once listener removed before the callback runs".)
#[test]
fn once_removed_before_callback() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let once = AddOptions {
        once: true,
        ..AddOptions::default()
    };
    add(&mut l, &d, node(d.c), "click", 1, once);
    // The callback dispatches a second event at the same node.
    h.on(1, &[Act::Redispatch(node(d.c))]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    // The nested dispatch of the same, still dispatching, event is refused.
    assert_eq!(h.redispatch, [Err(DispatchError::InvalidState)]);
    assert_eq!(h.ids(), [1]);
}

/// Duplicates (type, callback, capture) are ignored; capture differs.
#[test]
fn duplicates() {
    let d = doc();
    let mut l = Listeners::new();
    assert!(add(
        &mut l,
        &d,
        node(d.c),
        "click",
        1,
        AddOptions::default()
    ));
    assert!(!add(
        &mut l,
        &d,
        node(d.c),
        "click",
        1,
        AddOptions::default()
    ));
    // A later duplicate's other options do not replace the first.
    let once = AddOptions {
        once: true,
        ..AddOptions::default()
    };
    assert!(!add(&mut l, &d, node(d.c), "click", 1, once));
    assert!(add(&mut l, &d, node(d.c), "click", 1, capture()));
    assert!(add(
        &mut l,
        &d,
        node(d.c),
        "keydown",
        1,
        AddOptions::default()
    ));
    assert!(add(
        &mut l,
        &d,
        node(d.c),
        "click",
        2,
        AddOptions::default()
    ));
    assert_eq!(l.listeners(node(d.c)).len(), 4);
    assert!(!l.listeners(node(d.c)).iter().any(|x| x.once));
}

/// `removeEventListener` matches on capture. (WPT EventTarget-removeEventListener.any.js.)
#[test]
fn remove_matches_capture() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    assert!(!l.remove_event_listener(node(d.c), &u("click"), ListenerId(1), true));
    assert!(!l.remove_event_listener(node(d.c), &u("keydown"), ListenerId(1), false));
    assert!(!l.remove_event_listener(node(d.c), &u("click"), ListenerId(2), false));
    assert!(!l.remove_event_listener(node(d.p), &u("click"), ListenerId(1), false));
    assert!(l.remove_event_listener(node(d.c), &u("click"), ListenerId(1), false));
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert!(h.log.is_empty());
}

/// WPT AddEventListenerOptions-signal.any.js: aborting removes the
/// listeners added with the signal, on every target; an aborted signal
/// adds nothing.
#[test]
fn signal() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let s = l.new_signal();
    let other = l.new_signal();
    assert_ne!(s, other);
    let with = |signal| AddOptions {
        signal: Some(signal),
        ..AddOptions::default()
    };
    add(&mut l, &d, node(d.c), "click", 1, with(s));
    add(&mut l, &d, node(d.p), "click", 2, with(s));
    add(&mut l, &d, node(d.c), "click", 3, with(other));
    add(&mut l, &d, node(d.c), "click", 4, AddOptions::default());
    assert!(!l.is_aborted(s));
    l.abort(s);
    l.abort(s);
    assert!(l.is_aborted(s) && !l.is_aborted(other));
    assert!(!add(&mut l, &d, node(d.c), "click", 5, with(s)));
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), [3, 4]);
}

/// The default passive value (DOM §2.7†): `touchstart`, `touchmove`,
/// `wheel`, `mousewheel` on a Window, Document, document element or body;
/// not on other nodes, other types, or when `passive` is given.
#[test]
fn default_passive() {
    let d = doc();
    let mut l = Listeners::new();
    let targets = [
        (TargetId::Window, true),
        (node(d.document), true),
        (node(d.html), true),
        (node(d.body), true),
        (node(d.p), false),
    ];
    let mut id = 0;
    for ty in ["touchstart", "touchmove", "wheel", "mousewheel"] {
        for (t, want) in targets {
            id += 1;
            add(&mut l, &d, t, ty, id, AddOptions::default());
            let got = l.listeners(t).iter().find(|x| x.callback == ListenerId(id));
            assert_eq!(got.map(|x| x.passive), Some(want), "{ty} on {t:?}");
        }
    }
    add(
        &mut l,
        &d,
        TargetId::Window,
        "click",
        100,
        AddOptions::default(),
    );
    add(
        &mut l,
        &d,
        node(d.body),
        "wheel",
        101,
        AddOptions {
            passive: Some(false),
            ..AddOptions::default()
        },
    );
    let p = |t, id| {
        l.listeners(t)
            .iter()
            .find(|x| x.callback == ListenerId(id))
            .map(|x| x.passive)
    };
    assert_eq!(p(TargetId::Window, 100), Some(false));
    assert_eq!(p(node(d.body), 101), Some(false));
}

// ---------- listeners changing during dispatch ----------

/// A listener removed during dispatch before its turn does not run (its
/// "removed" flag); one added to the current target does not run in this
/// dispatch (the clone); one added to a later target does. (WPT
/// Event-dispatch-handlers-changed.html, remove-all-listeners.html.)
#[test]
fn listeners_changed_during_dispatch() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.body), "click", 1, capture());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.c), "click", 3, AddOptions::default());
    // 1 (capture at body) removes 2 and adds 9 at the target, 8 at the parent.
    h.on(
        1,
        &[
            Act::Remove(node(d.c), "click", 2, false),
            Act::Add(node(d.c), "click", 9, AddOptions::default()),
            Act::Add(node(d.p), "click", 8, AddOptions::default()),
        ],
    );
    // 3 adds 7 at the same target: not run now.
    h.on(3, &[Act::Add(node(d.c), "click", 7, AddOptions::default())]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    // 9 was added before the target's clone was taken, so it runs (the
    // clone is taken when the target is reached); 7 was added after.
    assert_eq!(h.ids(), [1, 3, 9, 8]);
}

/// The path is fixed before any listener runs: a listener cannot change
/// which nodes are visited (it can only change the listener lists).
#[test]
fn path_is_fixed_up_front() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    h.on(1, &[Act::RecordPath]);
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(
        h.paths,
        [vec![
            node(d.c),
            node(d.p),
            node(d.body),
            node(d.html),
            node(d.document)
        ]]
    );
    assert!(e.composed_path().is_empty());
}

// ---------- dispatchEvent's checks ----------

/// WPT Event-dispatch-redispatch.html and EventTarget-dispatchEvent.html:
/// an event being dispatched, or not initialized, is `InvalidStateError`.
#[test]
fn dispatch_event_checks() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let mut e = Event::new_uninitialized(0.0);
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Err(DispatchError::InvalidState)
    );
    e.init_event(&u("click"), true, false);
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(true)
    );
    // Redispatch from a listener.
    add(&mut l, &d, node(d.c), "click", 1, AddOptions::default());
    h.on(1, &[Act::Redispatch(node(d.p))]);
    let mut e = bubbling();
    let _ = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.redispatch, [Err(DispatchError::InvalidState)]);
    // After it ends, dispatching again is fine.
    assert_eq!(
        dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h),
        Ok(true)
    );
}

/// `dispatchEvent` sets `isTrusted` false; the user agent's `dispatch`
/// keeps it. (WPT Event-isTrusted.any.js.)
#[test]
fn is_trusted() {
    let d = doc();
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    let mut e = Event::new_trusted(&u("click"), EventInit::default(), 0.0);
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert!(e.is_trusted());
    let _ = dispatch_event(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert!(!e.is_trusted());
}

/// The two halves of `dispatch` give the same result as `dispatch`.
#[test]
fn build_then_run_matches_dispatch() {
    let d = doc();
    let mut l = Listeners::new();
    add(&mut l, &d, node(d.body), "click", 1, capture());
    add(&mut l, &d, node(d.c), "click", 2, AddOptions::default());
    add(&mut l, &d, node(d.html), "click", 3, AddOptions::default());
    let mut h1 = TestHost::new(&d.t.arena);
    let mut e1 = bubbling();
    let r1 = dispatch(&d.t.arena, &mut l, node(d.c), &mut e1, &mut h1);
    let mut h2 = TestHost::new(&d.t.arena);
    let mut e2 = bubbling();
    let path = build_path(&d.t.arena, node(d.c), &e2, &|_, _| false).unwrap_or_default();
    let r2 = dispatch_path(&path, &mut l, &mut e2, &mut h2);
    assert_eq!(r1, Ok(r2));
    assert_eq!(h1.log, h2.log);
}

// ---------- depth ----------

/// A deep tree is walked without recursion.
#[test]
fn deep_tree() {
    let depth: usize = if cfg!(miri) { 200 } else { 20_000 };
    let mut t = Tree::new();
    let mut parent = 0;
    for _ in 0..depth {
        parent = t.el(parent, "div");
    }
    let mut l = Listeners::new();
    let mut h = TestHost::new(&t.arena);
    l.add_event_listener(
        &t.arena,
        node(0),
        &u("click"),
        ListenerId(1),
        AddOptions::default(),
    );
    l.add_event_listener(&t.arena, node(0), &u("click"), ListenerId(2), capture());
    let mut e = bubbling();
    let r = dispatch(&t.arena, &mut l, node(parent), &mut e, &mut h);
    assert_eq!(r, Ok(true));
    assert_eq!(h.ids(), [2, 1]);
    let path = build_path(&t.arena, node(parent), &e, &|_, _| false).unwrap_or_default();
    assert_eq!(path.len(), depth.saturating_add(1));
}

/// Many listeners on one node run in registration order.
#[test]
fn many_listeners_in_order() {
    let d = doc();
    let n: u64 = if cfg!(miri) { 20 } else { 2_000 };
    let mut l = Listeners::new();
    let mut h = TestHost::new(&d.t.arena);
    for id in 0..n {
        add(&mut l, &d, node(d.c), "click", id, AddOptions::default());
    }
    let mut e = bubbling();
    let _ = dispatch(&d.t.arena, &mut l, node(d.c), &mut e, &mut h);
    assert_eq!(h.ids(), (0..n).collect::<Vec<_>>());
}
