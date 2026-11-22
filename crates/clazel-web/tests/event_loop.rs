//! The event loop (HTML §8.1.7†), the microtask queue and timers (§8.6†):
//! each test names the algorithm step it covers. The ones marked "WPT"
//! mirror the expectation of a vendored `html/webappapis/timers/` or
//! `microtask-queuing/` test (`tests/data/wpt-web/html/webappapis/`); they
//! are hand transcriptions of the ordering those tests check (the tests
//! themselves need a JS engine), not runs of the suite, so no
//! `clazel-conformance:` line is printed.
//!
//! Callbacks are scripts the test host holds, keyed by [`CallbackId`]; they
//! log what ran and when.

use clazel_web::event_loop::{
    CallbackId, EventLoop, Host, LimitError, Limits, TaskSource, TimerCall, TimerId,
};
use std::collections::BTreeMap;
use std::rc::Rc;

type Script = Rc<dyn Fn(&mut EventLoop, &mut TestHost)>;

#[derive(Default)]
struct TestHost {
    scripts: BTreeMap<u64, Script>,
    log: Vec<String>,
    rendering: bool,
    render_script: Option<Script>,
    checkpoints_done: u32,
    kept_cleared: u32,
    rejections_notified: u32,
    nesting_seen: Vec<u32>,
}

impl TestHost {
    fn on(&mut self, id: u64, f: impl Fn(&mut EventLoop, &mut TestHost) + 'static) -> CallbackId {
        self.scripts.insert(id, Rc::new(f));
        CallbackId(id)
    }

    /// A script that only logs `name`.
    fn logger(&mut self, id: u64, name: &'static str) -> CallbackId {
        self.on(id, move |_, h| h.log.push(name.to_string()))
    }

    /// A script that logs `name@now`.
    fn timed(&mut self, id: u64, name: &'static str) -> CallbackId {
        self.on(id, move |el, h| h.log.push(format!("{name}@{}", el.now())))
    }

    fn run(&mut self, el: &mut EventLoop, id: CallbackId) {
        if let Some(s) = self.scripts.get(&id.0).cloned() {
            s(el, self);
        }
    }

    fn log(&self) -> Vec<&str> {
        self.log.iter().map(String::as_str).collect()
    }
}

impl Host for TestHost {
    fn run_task(&mut self, el: &mut EventLoop, callback: CallbackId) {
        self.run(el, callback);
    }
    fn run_microtask(&mut self, el: &mut EventLoop, callback: CallbackId) {
        self.run(el, callback);
    }
    fn run_timer(&mut self, el: &mut EventLoop, call: TimerCall) {
        self.nesting_seen.push(call.nesting_level);
        self.run(el, call.handler);
    }
    fn rendering_opportunity(&mut self, _now: u64) -> bool {
        self.rendering
    }
    fn update_the_rendering(&mut self, el: &mut EventLoop, _now: u64) {
        self.log.push("render".to_string());
        if let Some(s) = self.render_script.clone() {
            s(el, self);
        }
    }
    fn notify_about_rejected_promises(&mut self, _el: &mut EventLoop) {
        self.rejections_notified = self.rejections_notified.saturating_add(1);
        self.checkpoints_done = self.checkpoints_done.saturating_add(1);
    }
    fn clear_kept_objects(&mut self) {
        self.kept_cleared = self.kept_cleared.saturating_add(1);
    }
}

/// Run the loop on virtual time until nothing is pending at or before
/// `until`, or `max` iterations.
fn drive(el: &mut EventLoop, host: &mut TestHost, until: u64, max: usize) -> usize {
    let mut n = 0;
    while n < max {
        let Some(t) = el.next_wake() else { break };
        if t > until {
            break;
        }
        el.run_iteration(host, t);
        n = n.saturating_add(1);
    }
    n
}

fn ok<T, E: std::fmt::Debug>(r: Result<T, E>) -> T {
    match r {
        Ok(v) => v,
        Err(e) => unreachable!("unexpected error {e:?}"),
    }
}

// ---- Task queues, "queue a task", the processing model -------------------

/// "Queue a task": tasks of one source run in the order queued, one per
/// iteration, with a microtask checkpoint after each.
#[test]
fn tasks_run_in_order_with_a_checkpoint_after_each() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let m1 = h.logger(10, "microtask-of-A");
    let a = h.on(1, move |el, h| {
        h.log.push("A".into());
        ok(el.queue_microtask(m1));
    });
    let b = h.logger(2, "B");
    ok(el.queue_task(TaskSource::DomManipulation, a));
    ok(el.queue_task(TaskSource::DomManipulation, b));
    assert_eq!(el.queued_task_count(), 2);
    let it = el.run_iteration(&mut h, 0);
    assert!(it.ran_task);
    assert_eq!(h.log(), ["A", "microtask-of-A"]);
    el.run_iteration(&mut h, 0);
    assert_eq!(h.log(), ["A", "microtask-of-A", "B"]);
    assert_eq!(el.queued_task_count(), 0);
    let it = el.run_iteration(&mut h, 0);
    assert!(!it.ran_task && !it.rendered);
}

/// "Choose a task queue": round-robin across sources, so a flood on one
/// source does not starve another; within a source, FIFO.
#[test]
fn queues_are_served_round_robin() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let ids = [
        (TaskSource::Networking, "n1"),
        (TaskSource::Networking, "n2"),
        (TaskSource::Networking, "n3"),
        (TaskSource::UserInteraction, "u1"),
        (TaskSource::UserInteraction, "u2"),
        (TaskSource::Other(7), "o1"),
    ];
    for (i, (src, name)) in ids.iter().enumerate() {
        let cb = h.logger(u64::try_from(i).unwrap_or(0), name);
        ok(el.queue_task(*src, cb));
    }
    ok(el.queue_task(TaskSource::Networking, CallbackId(999)));
    el.run_until_idle(&mut h, 0, 100);
    // Source order is UserInteraction < Networking < Other.
    assert_eq!(h.log(), ["u1", "n1", "o1", "u2", "n2", "n3"]);
}

/// The processing model's "run one task, then perform a microtask
/// checkpoint": a task queued by a task waits for the next iteration, and a
/// microtask queued with no task running runs at the next iteration's
/// checkpoint.
#[test]
fn a_task_queued_by_a_task_waits_for_the_next_iteration() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let inner = h.logger(2, "inner-task");
    let outer = h.on(1, move |el, h| {
        h.log.push("outer".into());
        ok(el.queue_task(TaskSource::DomManipulation, inner));
    });
    ok(el.queue_task(TaskSource::DomManipulation, outer));
    el.run_iteration(&mut h, 0);
    assert_eq!(h.log(), ["outer"]);
    assert_eq!(el.queued_task_count(), 1);
    let micro = h.logger(3, "between");
    ok(el.queue_microtask(micro));
    let it = el.run_iteration(&mut h, 0);
    assert!(it.ran_task);
    assert_eq!(h.log(), ["outer", "inner-task", "between"]);
    // With no task, a microtask still gets its checkpoint.
    let micro2 = h.logger(4, "alone");
    ok(el.queue_microtask(micro2));
    let it = el.run_iteration(&mut h, 0);
    assert!(!it.ran_task);
    assert_eq!(h.log(), ["outer", "inner-task", "between", "alone"]);
}

/// "Update the rendering" is the stand-in hook: it runs after the task and
/// its checkpoint, only when the host reports an opportunity, and a
/// microtask it queues runs in the checkpoint that follows.
#[test]
fn the_rendering_opportunity_hook() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let t = h.logger(1, "task");
    let m = h.logger(2, "microtask-from-render");
    h.render_script = Some(Rc::new(move |el, _| {
        ok(el.queue_microtask(m));
    }));
    ok(el.queue_task(TaskSource::DomManipulation, t));
    let it = el.run_iteration(&mut h, 0);
    assert!(it.ran_task && !it.rendered);
    assert_eq!(h.log(), ["task"]);
    h.rendering = true;
    let it = el.run_iteration(&mut h, 16);
    assert!(!it.ran_task && it.rendered);
    assert_eq!(h.log(), ["task", "render", "microtask-from-render"]);
}

/// The loop never lets the clock go back.
#[test]
fn time_is_monotonic() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    el.run_iteration(&mut h, 50);
    el.run_iteration(&mut h, 10);
    assert_eq!(el.now(), 50);
    let cb = h.timed(1, "t");
    ok(el.set_timeout(cb, 5, 20));
    assert_eq!(el.now(), 50);
    // Due at 55, not 25.
    assert_eq!(el.next_wake(), Some(55));
}

// ---- Microtask queue and checkpoint --------------------------------------

/// "Perform a microtask checkpoint": "while the microtask queue is not
/// empty", microtasks queued by microtasks run in the same checkpoint, after
/// those already queued; then rejected promises are notified and
/// ClearKeptObjects runs once.
#[test]
fn a_checkpoint_drains_the_queue_including_new_microtasks() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let c = h.logger(3, "c");
    let a = h.on(1, move |el, h| {
        h.log.push("a".into());
        ok(el.queue_microtask(c));
    });
    let b = h.logger(2, "b");
    ok(el.queue_microtask(a));
    ok(el.queue_microtask(b));
    el.perform_microtask_checkpoint(&mut h);
    assert_eq!(h.log(), ["a", "b", "c"]);
    assert_eq!(el.microtask_count(), 0);
    assert_eq!(h.rejections_notified, 1);
    assert_eq!(h.kept_cleared, 1);
}

/// The first step: "if the event loop's performing a microtask checkpoint
/// is true, then return". A checkpoint requested from a microtask (or from
/// the host's rejection notice) does nothing.
#[test]
fn a_nested_checkpoint_returns_at_once() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let inner = h.logger(3, "queued-by-first");
    let first = h.on(1, move |el, h| {
        h.log.push("first".into());
        assert!(el.performing_microtask_checkpoint());
        ok(el.queue_microtask(inner));
        el.perform_microtask_checkpoint(h);
        // Nothing ran inside the nested call.
        h.log.push("first-end".into());
    });
    let second = h.logger(2, "second");
    ok(el.queue_microtask(first));
    ok(el.queue_microtask(second));
    el.perform_microtask_checkpoint(&mut h);
    assert!(!el.performing_microtask_checkpoint());
    assert_eq!(h.log(), ["first", "first-end", "second", "queued-by-first"]);
    // One checkpoint ran its end steps, not two.
    assert_eq!(h.kept_cleared, 1);
}

/// "Clean up after running script": a host that checkpoints at the end of a
/// callback runs the microtasks before the task returns; the loop's own
/// checkpoint after the task then finds nothing.
#[test]
fn a_callback_may_checkpoint_itself() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let m = h.logger(2, "microtask");
    let t = h.on(1, move |el, h| {
        ok(el.queue_microtask(m));
        h.log.push("task-body".into());
        el.perform_microtask_checkpoint(h);
        h.log.push("task-end".into());
    });
    ok(el.queue_task(TaskSource::DomManipulation, t));
    el.run_iteration(&mut h, 0);
    assert_eq!(h.log(), ["task-body", "microtask", "task-end"]);
}

/// WPT `microtask-queuing/queue-microtask.window.js` (transcription): a
/// microtask runs before a `setTimeout(0)` callback, and a microtask queued
/// from a timer callback runs before the next timer callback.
#[test]
fn wpt_microtask_runs_before_timeout_0_and_between_timers() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let micro_in_t1 = h.logger(10, "microtask-in-t1");
    let t1 = h.on(1, move |el, h| {
        h.log.push("t1".into());
        ok(el.queue_microtask(micro_in_t1));
    });
    let t2 = h.logger(2, "t2");
    let main_micro = h.logger(3, "main-microtask");
    // The script that runs now, as a task: two timeouts, then a microtask.
    let script = h.on(4, move |el, _| {
        ok(el.set_timeout(t1, 0, el.now()));
        ok(el.set_timeout(t2, 0, el.now()));
        ok(el.queue_microtask(main_micro));
    });
    ok(el.queue_task(TaskSource::DomManipulation, script));
    drive(&mut el, &mut h, 0, 100);
    assert_eq!(h.log(), ["main-microtask", "t1", "microtask-in-t1", "t2"]);
}

/// WPT `microtask-queuing/evaluation-order.sub.html` and
/// `queue-microtask-exceptions` (transcription): an exception in a microtask
/// is the host's to report and later microtasks still run. The host's
/// callback here "reports" by logging and returning.
#[test]
fn wpt_a_throwing_microtask_does_not_stop_the_checkpoint() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let throws = h.on(1, |_, h| h.log.push("threw, reported".into()));
    let after = h.logger(2, "after");
    ok(el.queue_microtask(throws));
    ok(el.queue_microtask(after));
    el.perform_microtask_checkpoint(&mut h);
    assert_eq!(h.log(), ["threw, reported", "after"]);
}

/// A microtask that runs inside a timer's task is not "a task that was
/// created by this algorithm": a timer set from it has nesting level 1,
/// not 2 (the modelling choice at the top of the module).
#[test]
fn a_timer_set_in_a_microtask_starts_at_level_zero() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let leaf = h.logger(3, "leaf");
    let micro = h.on(2, move |el, _| {
        ok(el.set_timeout(leaf, 0, el.now()));
    });
    let direct_leaf = h.logger(4, "direct-leaf");
    let t = h.on(1, move |el, _| {
        ok(el.queue_microtask(micro));
        ok(el.set_timeout(direct_leaf, 0, el.now()));
    });
    ok(el.set_timeout(t, 0, 0));
    drive(&mut el, &mut h, 0, 100);
    // t (level 1), then the two it set, in the order set: one directly
    // (level 2) and one from the microtask (level 1).
    assert_eq!(h.nesting_seen, [1, 2, 1]);
    assert_eq!(h.log(), ["direct-leaf", "leaf"]);
}

// ---- Timers --------------------------------------------------------------

/// "Timer initialisation steps": ids are positive, unique among the active
/// timers and, here, increasing; `clearTimeout` and `clearInterval` share
/// one map; an unknown, zero or negative id does nothing.
#[test]
fn ids_are_positive_unique_and_shared_between_set_and_clear_kinds() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let cb = h.logger(1, "x");
    let a = ok(el.set_timeout(cb, 10, 0));
    let b = ok(el.set_interval(cb, 10, 0));
    let c = ok(el.set_timeout(cb, 10, 0));
    assert!(a.get() > 0 && b.get() > a.get() && c.get() > b.get());
    assert_eq!(el.active_timer_count(), 3);
    assert!(el.is_active_timer(a));
    // clearInterval on a timeout's id, clearTimeout on an interval's id.
    el.clear_timer(i32::try_from(a.get()).unwrap_or(0));
    el.clear_timer(i32::try_from(b.get()).unwrap_or(0));
    assert_eq!(el.active_timer_count(), 1);
    assert!(!el.is_active_timer(a) && !el.is_active_timer(b));
    for bad in [0, -1, i32::MIN, 12345] {
        el.clear_timer(bad);
    }
    assert_eq!(el.active_timer_count(), 1);
    assert_eq!(TimerId::from_script(0), None);
    assert_eq!(TimerId::from_script(-4), None);
    assert_eq!(TimerId::from_script(9).map(TimerId::get), Some(9));
    drive(&mut el, &mut h, 100, 100);
    assert_eq!(h.log(), ["x"]);
}

/// WPT `timers/negative-setTimeout.html` and `type-long-setTimeout.any.js`
/// (transcription): "if timeout is less than 0, then set timeout to 0"; the
/// largest `long` is accepted and does not fire early or panic.
#[test]
fn wpt_negative_and_huge_timeouts() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let neg = h.timed(1, "neg");
    let big = h.timed(2, "big");
    ok(el.set_timeout(neg, -1000, 7));
    ok(el.set_timeout(neg, i32::MIN, 7));
    ok(el.set_timeout(big, i32::MAX, 7));
    drive(&mut el, &mut h, 1000, 100);
    assert_eq!(h.log(), ["neg@7", "neg@7"]);
    let due = 7u64.saturating_add(u64::from(i32::MAX.unsigned_abs()));
    assert_eq!(el.next_wake(), Some(due));
    drive(&mut el, &mut h, due, 100);
    assert_eq!(h.log().last().copied(), Some(format!("big@{due}").as_str()));
    // Near the end of the clock the due time saturates instead of wrapping.
    ok(el.set_timeout(neg, 5, u64::MAX.saturating_sub(1)));
    assert_eq!(el.next_wake(), Some(u64::MAX));
}

/// "Wait until any invocations ... that started before this one, and whose
/// milliseconds is equal to or less than this one's, have completed":
/// timers fire by due time, ties in the order started. WPT
/// `timers/evil-spec-example.any.js` and `timers/clearTimeout-clearInterval`
/// ordering (transcription).
#[test]
fn wpt_timers_fire_by_due_time_then_start_order() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let a = h.timed(1, "a10");
    let b = h.timed(2, "b5");
    let c = h.timed(3, "c5");
    let d = h.timed(4, "d0");
    let e = h.timed(5, "e10");
    ok(el.set_timeout(a, 10, 0));
    ok(el.set_timeout(b, 5, 0));
    ok(el.set_timeout(c, 5, 0));
    ok(el.set_timeout(d, 0, 0));
    ok(el.set_timeout(e, 10, 0));
    drive(&mut el, &mut h, 100, 100);
    assert_eq!(h.log(), ["d0@0", "b5@5", "c5@5", "a10@10", "e10@10"]);
}

/// A timer started later with a shorter timeout can overtake an earlier,
/// longer one (the "wait until" only binds shorter-or-equal earlier ones).
#[test]
fn a_later_shorter_timer_overtakes_an_earlier_longer_one() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let a = h.timed(1, "a");
    let b = h.timed(2, "b");
    ok(el.set_timeout(a, 10, 0));
    ok(el.set_timeout(b, 1, 5));
    drive(&mut el, &mut h, 100, 100);
    assert_eq!(h.log(), ["b@6", "a@10"]);
}

/// Nothing fires early, and timers fire in the iteration that reaches them.
#[test]
fn a_timer_waits_for_its_time() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let a = h.timed(1, "a");
    let id = ok(el.set_timeout(a, 100, 0));
    el.run_iteration(&mut h, 99);
    assert!(h.log.is_empty() && el.is_active_timer(id));
    assert_eq!(el.next_wake(), Some(100));
    el.run_iteration(&mut h, 100);
    assert_eq!(h.log(), ["a@100"]);
    // A one-shot's id has left the map once it has run.
    assert!(!el.is_active_timer(id));
    assert_eq!(el.active_timer_count(), 0);
    assert_eq!(el.next_wake(), None);
}

/// WPT `timers/clearTimeout-clearInterval.any.js` (transcription): clearing
/// before the time cancels; clearing the id of a timer whose task is already
/// queued ("if id does not exist in global's map ... abort these steps")
/// cancels it too.
#[test]
fn wpt_cleared_timers_do_not_run() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let a = h.timed(1, "a");
    let id = ok(el.set_timeout(a, 10, 0));
    el.clear_timer(i32::try_from(id.get()).unwrap_or(0));
    assert_eq!(el.next_wake(), None);
    drive(&mut el, &mut h, 100, 100);
    assert!(h.log.is_empty());

    // Due and queued as a task, then cleared by an earlier task of another
    // source before it runs. (UserInteraction is served before Timer.)
    let victim = h.timed(2, "victim");
    let id = ok(el.set_timeout(victim, 0, 100));
    let raw = i32::try_from(id.get()).unwrap_or(0);
    let clearer = h.on(3, move |el, h| {
        h.log.push("clearer".into());
        el.clear_timer(raw);
    });
    ok(el.queue_task(TaskSource::UserInteraction, clearer));
    drive(&mut el, &mut h, 100, 100);
    assert_eq!(h.log(), ["clearer"]);
    assert_eq!(el.active_timer_count(), 0);
}

/// `setInterval`: the timer is started again with the same id after each
/// run, from the time the loop is at then (so a late run shifts the rest),
/// and `clearInterval` from its own handler stops it.
#[test]
fn intervals_reschedule_with_the_same_id() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let count = std::rc::Rc::new(std::cell::Cell::new(0u32));
    let c2 = count.clone();
    let id_cell = std::rc::Rc::new(std::cell::Cell::new(0i32));
    let i2 = id_cell.clone();
    let tick = h.on(1, move |el, h| {
        h.log.push(format!("tick@{}", el.now()));
        c2.set(c2.get().saturating_add(1));
        if c2.get() == 3 {
            el.clear_timer(i2.get());
        }
    });
    let id = ok(el.set_interval(tick, 10, 0));
    id_cell.set(i32::try_from(id.get()).unwrap_or(0));
    drive(&mut el, &mut h, 1000, 100);
    assert_eq!(h.log(), ["tick@10", "tick@20", "tick@30"]);
    assert!(!el.is_active_timer(id));
    assert_eq!(el.next_wake(), None);

    // A run that happens late (the loop was busy until 25) is followed by
    // one a full period after the late run.
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let tick = h.timed(1, "tick");
    let id = ok(el.set_interval(tick, 10, 0));
    el.run_iteration(&mut h, 25);
    assert_eq!(h.log(), ["tick@25"]);
    assert_eq!(el.next_wake(), Some(35));
    assert!(el.is_active_timer(id));
}

/// "If nesting level is greater than 5, and timeout is less than 4, then
/// set timeout to 4": a chain of `setTimeout(f, 0)` fires its first five
/// links at once and then every 4 ms. WPT
/// `timers/nested-timers.any.js`-style expectation (transcription).
#[test]
fn wpt_nested_set_timeout_clamps_to_4ms_after_5_levels() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let link = h.on(1, |el, h| {
        h.log.push(format!("{}", el.now()));
        if h.log.len() < 9 {
            ok(el.set_timeout(CallbackId(1), 0, el.now()));
        }
    });
    ok(el.set_timeout(link, 0, 0));
    drive(&mut el, &mut h, 1000, 100);
    assert_eq!(h.log(), ["0", "0", "0", "0", "0", "4", "8", "12", "16"]);
    assert_eq!(h.nesting_seen, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
}

/// The same for `setInterval(f, 0)`: the interval's repeat is "the timer
/// initialisation steps again" from the task, so its level grows each run.
#[test]
fn wpt_nested_set_interval_clamps_to_4ms_after_5_levels() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let id_cell = Rc::new(std::cell::Cell::new(0i32));
    let i2 = id_cell.clone();
    let tick = h.on(1, move |el, h| {
        h.log.push(format!("{}", el.now()));
        if h.log.len() >= 8 {
            el.clear_timer(i2.get());
        }
    });
    let id = ok(el.set_interval(tick, 0, 0));
    id_cell.set(i32::try_from(id.get()).unwrap_or(0));
    drive(&mut el, &mut h, 1000, 100);
    assert_eq!(h.log(), ["0", "0", "0", "0", "0", "4", "8", "12"]);
}

/// The clamp is a minimum of 4 only below 4, and only past level 5: a
/// timeout of 10 or of 4 is untouched, a timeout of 2 becomes 4.
#[test]
fn the_clamp_only_raises_timeouts_below_4() {
    for (timeout, expect_gap) in [(10, 10u64), (4, 4), (3, 4), (2, 4), (0, 4)] {
        let mut el = EventLoop::default();
        let mut h = TestHost::default();
        let link = h.on(1, move |el, h| {
            h.log.push(format!("{}", el.now()));
            if h.log.len() < 9 {
                ok(el.set_timeout(CallbackId(1), timeout, el.now()));
            }
        });
        ok(el.set_timeout(link, timeout, 0));
        drive(&mut el, &mut h, 10_000, 100);
        let times: Vec<u64> = h.log.iter().filter_map(|s| s.parse().ok()).collect();
        assert_eq!(times.len(), 9);
        // The gap between the last two links is past level 5.
        let last = times.last().copied().unwrap_or(0);
        let before = times
            .get(times.len().saturating_sub(2))
            .copied()
            .unwrap_or(0);
        assert_eq!(last.saturating_sub(before), expect_gap, "timeout {timeout}");
    }
}

/// A timer set from an ordinary task (not a timer's) starts at level 1
/// however deep an earlier chain went.
#[test]
fn a_timer_set_from_a_plain_task_starts_over() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let leaf = h.timed(2, "leaf");
    let task = h.on(1, move |el, _| {
        ok(el.set_timeout(leaf, 0, el.now()));
    });
    ok(el.queue_task(TaskSource::DomManipulation, task));
    drive(&mut el, &mut h, 10, 100);
    assert_eq!(h.nesting_seen, [1]);
    assert_eq!(h.log(), ["leaf@0"]);
}

// ---- Hostile pages (7.19) ------------------------------------------------

/// Timers past `max_timers` are refused and change nothing; clearing one
/// frees a slot; an interval's reschedule does not need a free slot.
#[test]
fn the_timer_cap_refuses_and_recovers() {
    let mut el = EventLoop::new(Limits {
        max_timers: 3,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let cb = h.timed(1, "t");
    let a = ok(el.set_timeout(cb, 10, 0));
    ok(el.set_interval(cb, 10, 0));
    ok(el.set_timeout(cb, 10, 0));
    assert_eq!(el.set_timeout(cb, 10, 0), Err(LimitError::TooManyTimers));
    assert_eq!(el.set_interval(cb, 0, 0), Err(LimitError::TooManyTimers));
    assert_eq!(el.active_timer_count(), 3);
    el.clear_timer(i32::try_from(a.get()).unwrap_or(0));
    ok(el.set_timeout(cb, 10, 0));
    assert_eq!(el.active_timer_count(), 3);

    // At the cap, an interval still reschedules, and a timer can be set
    // from a one-shot's handler (its slot is free while it runs).
    let mut el = EventLoop::new(Limits {
        max_timers: 1,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let tick = h.timed(1, "tick");
    ok(el.set_interval(tick, 10, 0));
    drive(&mut el, &mut h, 35, 100);
    assert_eq!(h.log(), ["tick@10", "tick@20", "tick@30"]);

    let mut el = EventLoop::new(Limits {
        max_timers: 1,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let second = h.timed(2, "second");
    let first = h.on(1, move |el, h| {
        h.log.push("first".into());
        assert!(el.set_timeout(second, 1, el.now()).is_ok());
    });
    ok(el.set_timeout(first, 1, 0));
    drive(&mut el, &mut h, 100, 100);
    assert_eq!(h.log(), ["first", "second@2"]);
}

/// Tasks past `max_tasks` are refused (all queues together); a due timer
/// that finds the queues full stays due and runs later, not lost.
#[test]
fn the_task_cap_refuses_and_a_due_timer_waits_for_room() {
    let mut el = EventLoop::new(Limits {
        max_tasks: 2,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let a = h.logger(1, "a");
    let b = h.logger(2, "b");
    ok(el.queue_task(TaskSource::Networking, a));
    ok(el.queue_task(TaskSource::DomManipulation, b));
    assert_eq!(
        el.queue_task(TaskSource::Other(1), a),
        Err(LimitError::TooManyTasks)
    );
    assert_eq!(el.queued_task_count(), 2);

    let t = h.logger(3, "timer");
    ok(el.set_timeout(t, 0, 0));
    // The queues are full: the timer is not queued, and stays active.
    el.run_iteration(&mut h, 0);
    assert_eq!(h.log(), ["b"]);
    assert_eq!(el.active_timer_count(), 1);
    // Room again: the timer is queued behind the rest and runs.
    el.run_until_idle(&mut h, 0, 100);
    assert_eq!(h.log(), ["b", "a", "timer"]);
    assert_eq!(el.active_timer_count(), 0);
}

/// Microtasks past `max_microtasks` are refused; the queue drains and takes
/// more.
#[test]
fn the_microtask_cap_refuses() {
    let mut el = EventLoop::new(Limits {
        max_microtasks: 2,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let m = h.logger(1, "m");
    ok(el.queue_microtask(m));
    ok(el.queue_microtask(m));
    assert_eq!(el.queue_microtask(m), Err(LimitError::TooManyMicrotasks));
    el.perform_microtask_checkpoint(&mut h);
    assert_eq!(h.log.len(), 2);
    ok(el.queue_microtask(m));
    // A microtask that keeps queueing itself is held to the cap's memory
    // bound (the loop itself is the host's kill to end, 7.0(g)); here it is
    // stopped by the refusal.
    let spin = h.on(2, |el, h| {
        h.log.push("spin".into());
        let _ = el.queue_microtask(CallbackId(2));
        let _ = el.queue_microtask(CallbackId(2));
        if h.log.len() > 50 {
            h.scripts.remove(&2);
        }
    });
    el.perform_microtask_checkpoint(&mut h);
    ok(el.queue_microtask(spin));
    el.perform_microtask_checkpoint(&mut h);
    assert!(el.microtask_count() <= 2);
}

/// `run_until_idle`'s bound ends a task that queues itself forever, with the
/// queue still within its cap.
#[test]
fn run_until_idle_is_bounded() {
    let mut el = EventLoop::default();
    let mut h = TestHost::default();
    let again = h.on(1, |el, _| {
        ok(el.queue_task(TaskSource::DomManipulation, CallbackId(1)));
    });
    ok(el.queue_task(TaskSource::DomManipulation, again));
    let n = el.run_until_idle(&mut h, 0, 50);
    assert_eq!(n, 50);
    assert_eq!(el.queued_task_count(), 1);
}

/// 7.19: a flood of timers (the page's 10^6) stays within the cap: the
/// surplus calls are refused, the accepted ones all fire exactly once, in
/// (time, start order), and the loop holds nothing afterwards.
#[test]
fn a_flood_of_timers_stays_within_the_caps() {
    let cap: usize = if cfg!(miri) { 300 } else { 20_000 };
    let attempts: usize = if cfg!(miri) { 1_000 } else { 1_000_000 };
    let mut el = EventLoop::new(Limits {
        max_timers: cap,
        max_tasks: cap,
        max_microtasks: cap,
    });
    let mut h = TestHost::default();
    let fired = Rc::new(std::cell::RefCell::new(Vec::<u64>::new()));
    let mut accepted = 0usize;
    let mut refused = 0usize;
    for i in 0..attempts {
        // The handler id is the index; the timeout cycles through 0..50.
        let id = u64::try_from(i).unwrap_or(0);
        let f = fired.clone();
        let cb = h.on(id, move |el, _| {
            f.borrow_mut().push(el.now());
        });
        let timeout = i32::try_from(i % 50).unwrap_or(0);
        match el.set_timeout(cb, timeout, 0) {
            Ok(_) => accepted = accepted.saturating_add(1),
            Err(LimitError::TooManyTimers) => {
                refused = refused.saturating_add(1);
                h.scripts.remove(&id);
            }
            Err(e) => unreachable!("{e:?}"),
        }
        assert!(el.active_timer_count() <= cap);
    }
    assert_eq!(accepted, cap);
    assert_eq!(refused, attempts.saturating_sub(cap));
    drive(&mut el, &mut h, 1000, usize::MAX);
    let times = fired.borrow();
    assert_eq!(times.len(), cap);
    assert!(times.windows(2).all(|w| w.first() <= w.get(1)));
    assert_eq!(el.active_timer_count(), 0);
    assert_eq!(el.queued_task_count(), 0);
    assert_eq!(el.next_wake(), None);
}

/// A flood of tasks and microtasks likewise: refused past the caps, all
/// accepted ones run in order.
#[test]
fn a_flood_of_tasks_and_microtasks_stays_within_the_caps() {
    let cap: usize = if cfg!(miri) { 100 } else { 10_000 };
    let mut el = EventLoop::new(Limits {
        max_timers: cap,
        max_tasks: cap,
        max_microtasks: cap,
    });
    let mut h = TestHost::default();
    let task = h.logger(1, "t");
    let micro = h.logger(2, "m");
    let mut tasks = 0usize;
    let mut micros = 0usize;
    for _ in 0..cap.saturating_mul(3) {
        if el.queue_task(TaskSource::PostedMessage, task).is_ok() {
            tasks = tasks.saturating_add(1);
        }
        if el.queue_microtask(micro).is_ok() {
            micros = micros.saturating_add(1);
        }
    }
    assert_eq!((tasks, micros), (cap, cap));
    el.run_until_idle(&mut h, 0, usize::MAX);
    assert_eq!(h.log.len(), cap.saturating_mul(2));
    assert_eq!(el.queued_task_count(), 0);
    assert_eq!(el.microtask_count(), 0);
}

/// Set and clear churn does not grow the loop: a million set/clear pairs
/// leave nothing behind (no stale queue entries).
#[test]
fn set_and_clear_churn_leaves_nothing() {
    let n: usize = if cfg!(miri) { 500 } else { 200_000 };
    let mut el = EventLoop::new(Limits {
        max_timers: 4,
        ..Limits::default()
    });
    let mut h = TestHost::default();
    let cb = h.logger(1, "never");
    for i in 0..n {
        let t = u64::try_from(i % 7).unwrap_or(0);
        let id = ok(el.set_timeout(cb, 5, t));
        el.clear_timer(i32::try_from(id.get()).unwrap_or(0));
    }
    assert_eq!(el.active_timer_count(), 0);
    assert_eq!(el.next_wake(), None);
    drive(&mut el, &mut h, 10_000, 10);
    assert!(h.log.is_empty());
}
