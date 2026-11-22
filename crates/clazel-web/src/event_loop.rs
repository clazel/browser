//! The HTML event loop (§8.1.7†): task sources and task queues, "queue a
//! task", the processing model's "run one task, then perform a microtask
//! checkpoint", the microtask queue, and the timers of §8.6†
//! (`setTimeout`, `setInterval`, `clearTimeout`, `clearInterval`).
//!
//! <https://html.spec.whatwg.org/multipage/webappapis.html#event-loops> and
//! <https://html.spec.whatwg.org/multipage/timers-and-user-prompts.html#timers>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit). Steps are quoted by their words, not their numbers,
//! because the numbers were not checked against a pinned text.
//!
//! Tier 0, not proven. Nothing here grows past the [`Limits`], and every
//! loop is bounded by a queue length or by an argument the caller gives.
//!
//! Modelling choices:
//! - **One event loop, one document, one thread** (phase-7.md 7.0(e)): the
//!   renderer is single-threaded, so there are no other event loops, no
//!   workers, no "wait for" that blocks. The spec's "wait until" in the timer
//!   steps is an ordered set of due times, and "in parallel" is the caller
//!   handing over the time.
//! - **Time is the caller's.** Every entry point that needs the time takes
//!   `now`, in whole milliseconds on a monotonic clock the caller owns.
//!   There is no wall clock in this module. A `now` earlier than one seen
//!   before is taken as the latest one seen (the clock never goes back).
//! - **Callbacks are ids the host supplies** ([`CallbackId`]), as listeners
//!   are in `events.rs`. The host runs the script, reports any exception
//!   itself ("report the exception") and the loop goes on. The arguments of
//!   `setTimeout(handler, timeout, ...arguments)` stay with the host,
//!   keyed by the handler id; a string handler is the host's to compile.
//!   This matches `clazel-js`'s `Host` hooks: a promise job or generic job
//!   the engine hands over is a microtask here, and the engine's timeout
//!   job (`HostEnqueueTimeoutJob`, which the browser does not use) would be
//!   a timer.
//! - **Task queues.** The standard has a set of task queues, each holding
//!   the tasks of one task source, and lets the user agent choose which
//!   non-empty queue to take from ("in an implementation-defined manner").
//!   This module has one FIFO queue per [`TaskSource`] and chooses
//!   round-robin, starting after the source last served, so no source
//!   starves another. (A user agent that wants input first would choose
//!   differently; the standard permits it.) Tasks of one source run in the
//!   order queued, as the standard requires.
//! - **Not modelled:** a task's document and the "fully active" check (there
//!   is one document; the host stops the loop when it unloads), the
//!   "currently running task" other than for timer nesting, `performance.now`
//!   and long-task timing, `requestIdleCallback`, `requestAnimationFrame`
//!   (the rendering opportunity is [`Host::rendering_opportunity`] and
//!   [`Host::update_the_rendering`], a stand-in the renderer fills), the
//!   checkpoint's "cleanup Indexed DB transactions" step, and background
//!   tabs' throttling. "Wait for timeout milliseconds" also ignores that a
//!   timer fires late when the loop is busy: the timer's task is queued by
//!   the first iteration whose `now` is at or past its due time.
//! - **Timer nesting level.** The standard's "if the surrounding agent's
//!   event loop's currently running task is a task that was created by this
//!   algorithm" is read literally: a microtask that runs inside a timer's
//!   task is not itself a task created by the timer steps, so a timer set
//!   from it starts at nesting level 0. (Browsers differ; the standard's
//!   words are followed.) The level of an interval's next run comes from its
//!   own task, as the standard's repeat step runs inside that task.
//! - **Clearing an interval from its own handler** stops it: the repeat step
//!   runs only while the id is still in the map of active timers.
//! - **The hostile-page bounds** (phase-7.md 7.19) are [`Limits`]: active
//!   timers, queued tasks (all queues together) and queued microtasks. Past
//!   one, the call that would exceed it returns an error and changes
//!   nothing; the host turns that into the script-visible error (a
//!   `QuotaExceededError`). A timer that is due when the task queues are
//!   full stays due and is queued by a later iteration; it is never lost.
//!   An interval's reschedule reuses its own slot and cannot fail. The one
//!   thing no bound here stops is a microtask or task that queues itself
//!   forever: that is an infinite loop in script, which the host's kill of
//!   7.0(g) ends. [`EventLoop::run_until_idle`] has an iteration bound for
//!   the same reason.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ops::Bound;

/// What a task or microtask runs: supplied by the host, one id for one
/// script function (or one internal action).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallbackId(pub u64);

/// A task source (HTML §8.1.7† "task source"): which kind of work a task is,
/// so the queues can be chosen between. The named ones are the standard's
/// list; [`TaskSource::Other`] is for the host's.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TaskSource {
    /// "The DOM manipulation task source".
    DomManipulation,
    /// "The user interaction task source".
    UserInteraction,
    /// "The networking task source".
    Networking,
    /// "The history traversal task source".
    HistoryTraversal,
    /// "The timer task source": the one [`EventLoop`]'s timers use.
    Timer,
    /// "The posted message task source".
    PostedMessage,
    /// A source the host defines.
    Other(u32),
}

/// The id `setTimeout` and `setInterval` return: positive, and at most
/// `i32::MAX` (a WebIDL `long`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TimerId(u32);

impl TimerId {
    /// The value script sees.
    pub fn get(self) -> u32 {
        self.0
    }

    /// The id for a value script passes to `clearTimeout`, or `None` if no
    /// timer can have it (zero or negative).
    pub fn from_script(value: i32) -> Option<TimerId> {
        u32::try_from(value).ok().filter(|v| *v > 0).map(TimerId)
    }
}

/// The caps on one document's event loop (7.19). Each is a count of items
/// held at once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Active timers: ids in the map of active timers, waiting, queued or
    /// running.
    pub max_timers: usize,
    /// Queued tasks, all task queues together (a due timer's task counts).
    pub max_tasks: usize,
    /// Queued microtasks.
    pub max_microtasks: usize,
}

impl Default for Limits {
    /// 65,536 timers, 65,536 tasks and 1,048,576 microtasks: far more than a
    /// page needs, and a few megabytes at most.
    fn default() -> Limits {
        Limits {
            max_timers: 1 << 16,
            max_tasks: 1 << 16,
            max_microtasks: 1 << 20,
        }
    }
}

/// A call that would pass a [`Limits`] cap, and was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LimitError {
    /// `max_timers` active timers already.
    TooManyTimers,
    /// `max_tasks` queued tasks already.
    TooManyTasks,
    /// `max_microtasks` queued microtasks already.
    TooManyMicrotasks,
}

impl core::fmt::Display for LimitError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LimitError::TooManyTimers => f.write_str("too many active timers"),
            LimitError::TooManyTasks => f.write_str("too many queued tasks"),
            LimitError::TooManyMicrotasks => f.write_str("too many queued microtasks"),
        }
    }
}

impl std::error::Error for LimitError {}

/// A timer's task, as the host sees it when it runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TimerCall {
    /// The id `setTimeout` or `setInterval` returned.
    pub id: TimerId,
    /// The handler the caller gave.
    pub handler: CallbackId,
    /// Whether this is an interval's run.
    pub repeat: bool,
    /// The task's "timer nesting level" (1 for a timer set outside any timer
    /// task).
    pub nesting_level: u32,
}

/// The script side of the loop: runs callbacks. Each method gets the loop,
/// so a callback can queue tasks and microtasks and set and clear timers; a
/// method may call [`EventLoop::perform_microtask_checkpoint`] itself ("clean
/// up after running script"), which the checkpoint's flag makes safe.
pub trait Host {
    /// Run a task queued with [`EventLoop::queue_task`].
    fn run_task(&mut self, event_loop: &mut EventLoop, callback: CallbackId);

    /// Run a microtask queued with [`EventLoop::queue_microtask`].
    fn run_microtask(&mut self, event_loop: &mut EventLoop, callback: CallbackId);

    /// Run a timer's handler (the "run steps after a timeout" body: call the
    /// handler with the arguments, reporting an exception).
    fn run_timer(&mut self, event_loop: &mut EventLoop, call: TimerCall);

    /// Whether there is "a rendering opportunity" this iteration. Stand-in:
    /// the renderer decides (its frame clock). Default: never.
    fn rendering_opportunity(&mut self, now: u64) -> bool {
        let _ = now;
        false
    }

    /// "Update the rendering", run when [`Host::rendering_opportunity`] was
    /// true. Stand-in for the standard's steps (resize and scroll events,
    /// animation frame callbacks, style and layout, paint). A microtask
    /// checkpoint follows.
    fn update_the_rendering(&mut self, event_loop: &mut EventLoop, now: u64) {
        let _ = (event_loop, now);
    }

    /// The checkpoint's "notify about rejected promises" step.
    fn notify_about_rejected_promises(&mut self, event_loop: &mut EventLoop) {
        let _ = event_loop;
    }

    /// The checkpoint's "perform ClearKeptObjects" step.
    fn clear_kept_objects(&mut self) {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TaskKind {
    Callback(CallbackId),
    /// A timer's task: the id, and the sequence number of the timer
    /// initialisation that made it (so a cleared and reused id is not
    /// mistaken for it).
    Timer(TimerId, u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TimerState {
    /// Waiting for its due time.
    Waiting(u64),
    /// Its task is in the timer queue.
    Queued,
    /// Its task is running (an interval only).
    Running,
}

#[derive(Debug, Clone, Copy)]
struct Timer {
    handler: CallbackId,
    timeout: u64,
    repeat: bool,
    /// The task's timer nesting level.
    level: u32,
    seq: u64,
    state: TimerState,
}

/// What one pass of [`EventLoop::run_iteration`] did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Iteration {
    /// A task ran (a timer task of a cleared timer counts: it was taken from
    /// the queue and did nothing).
    pub ran_task: bool,
    /// The rendering step ran.
    pub rendered: bool,
}

/// One document's event loop.
#[derive(Debug)]
pub struct EventLoop {
    limits: Limits,
    now: u64,
    queues: BTreeMap<TaskSource, VecDeque<TaskKind>>,
    queued_tasks: usize,
    last_served: Option<TaskSource>,
    microtasks: VecDeque<CallbackId>,
    performing_checkpoint: bool,
    timers: BTreeMap<TimerId, Timer>,
    /// `(due time, sequence number, id)` of every waiting timer: the order
    /// timers fire in.
    waiting: BTreeSet<(u64, u64, TimerId)>,
    next_id: u32,
    next_seq: u64,
    /// The timer nesting level of the running timer task, or 0 when the
    /// running task is not a timer's.
    current_level: u32,
}

impl Default for EventLoop {
    fn default() -> EventLoop {
        EventLoop::new(Limits::default())
    }
}

/// The largest timer id: a WebIDL `long`.
const MAX_ID: u32 = i32::MAX as u32;

impl EventLoop {
    /// An empty loop at time 0.
    pub fn new(limits: Limits) -> EventLoop {
        EventLoop {
            limits,
            now: 0,
            queues: BTreeMap::new(),
            queued_tasks: 0,
            last_served: None,
            microtasks: VecDeque::new(),
            performing_checkpoint: false,
            timers: BTreeMap::new(),
            waiting: BTreeSet::new(),
            next_id: 1,
            next_seq: 0,
            current_level: 0,
        }
    }

    /// The caps this loop holds to.
    pub fn limits(&self) -> Limits {
        self.limits
    }

    /// The latest time the caller has given.
    pub fn now(&self) -> u64 {
        self.now
    }

    /// Queued tasks, all queues together.
    pub fn queued_task_count(&self) -> usize {
        self.queued_tasks
    }

    /// Queued microtasks.
    pub fn microtask_count(&self) -> usize {
        self.microtasks.len()
    }

    /// Entries in the map of active timers.
    pub fn active_timer_count(&self) -> usize {
        self.timers.len()
    }

    /// Whether `id` is in the map of active timers.
    pub fn is_active_timer(&self, id: TimerId) -> bool {
        self.timers.contains_key(&id)
    }

    /// Whether a microtask checkpoint is running.
    pub fn performing_microtask_checkpoint(&self) -> bool {
        self.performing_checkpoint
    }

    fn tick(&mut self, now: u64) {
        self.now = self.now.max(now);
    }

    /// HTML §8.1.7† "queue a task": "Let `task` be a new task ... Append
    /// `task` to `taskSource`'s task queue." The host's callback runs once,
    /// in a later iteration, after the earlier tasks of the same source.
    pub fn queue_task(
        &mut self,
        source: TaskSource,
        callback: CallbackId,
    ) -> Result<(), LimitError> {
        self.push_task(source, TaskKind::Callback(callback))
    }

    fn push_task(&mut self, source: TaskSource, kind: TaskKind) -> Result<(), LimitError> {
        if self.queued_tasks >= self.limits.max_tasks {
            return Err(LimitError::TooManyTasks);
        }
        self.queues.entry(source).or_default().push_back(kind);
        self.queued_tasks = self.queued_tasks.saturating_add(1);
        Ok(())
    }

    /// HTML §8.1.7† "queue a microtask" (what `queueMicrotask` and a promise
    /// reaction do): "Append `microtask` to the event loop's microtask
    /// queue."
    pub fn queue_microtask(&mut self, callback: CallbackId) -> Result<(), LimitError> {
        if self.microtasks.len() >= self.limits.max_microtasks {
            return Err(LimitError::TooManyMicrotasks);
        }
        self.microtasks.push_back(callback);
        Ok(())
    }

    /// HTML §8.1.7† "perform a microtask checkpoint":
    ///
    /// - "If the event loop's performing a microtask checkpoint is true,
    ///   then return."
    /// - "Set the event loop's performing a microtask checkpoint to true."
    /// - "While the event loop's microtask queue is not empty": dequeue the
    ///   oldest, set the currently running task to it, run it (the host
    ///   reports an exception), and restore the running task.
    /// - "Notify about rejected promises" ([`Host::notify_about_rejected_promises`]).
    /// - (Cleanup Indexed DB transactions: not modelled.)
    /// - "Perform ClearKeptObjects" ([`Host::clear_kept_objects`]).
    /// - "Set the event loop's performing a microtask checkpoint to false."
    ///
    /// Microtasks queued by a microtask run in this same checkpoint, after
    /// those already queued.
    pub fn perform_microtask_checkpoint<H: Host + ?Sized>(&mut self, host: &mut H) {
        // "If the event loop's performing a microtask checkpoint is true,
        // then return."
        if self.performing_checkpoint {
            return;
        }
        // "Set ... performing a microtask checkpoint to true."
        self.performing_checkpoint = true;
        // "While the microtask queue is not empty". The running task becomes
        // the microtask, which no timer step created: nesting level 0 for
        // the duration.
        let saved_level = self.current_level;
        while let Some(callback) = self.microtasks.pop_front() {
            self.current_level = 0;
            host.run_microtask(self, callback);
        }
        self.current_level = saved_level;
        // "Notify about rejected promises". Script it runs may queue
        // microtasks; they wait for the next checkpoint, as the standard's
        // loop has ended.
        host.notify_about_rejected_promises(self);
        // (Indexed DB cleanup: not modelled.)
        // "Perform ClearKeptObjects."
        host.clear_kept_objects();
        // "Set ... performing a microtask checkpoint to false."
        self.performing_checkpoint = false;
    }

    /// HTML §8.6† "timer initialisation steps" for `setTimeout` (`repeat`
    /// false) and `setInterval` (`repeat` true): choose an id "greater than
    /// zero and ... not already" in the map, clamp the timeout, and start
    /// the timer. `timeout` is the WebIDL `long`; `now` is the caller's
    /// clock. Fails, changing nothing, when `max_timers` timers are active.
    pub fn set_timer(
        &mut self,
        handler: CallbackId,
        timeout: i32,
        repeat: bool,
        now: u64,
    ) -> Result<TimerId, LimitError> {
        self.tick(now);
        if self.timers.len() >= self.limits.max_timers {
            return Err(LimitError::TooManyTimers);
        }
        // "If previousId was given, let id be previousId; otherwise, let id
        // be an implementation-defined integer that is greater than zero and
        // does not already exist in global's map of setTimeout and
        // setInterval IDs." Ids count up and wrap at `i32::MAX`, skipping
        // those in the map. The map holds fewer ids than the loop below
        // tries, so a free one is found unless every id is taken (a limit
        // above `i32::MAX`), which is refused as too many timers.
        let mut id = None;
        let mut candidate = self.next_id;
        for _ in 0..=self.timers.len() {
            let c = TimerId(candidate);
            candidate = if candidate >= MAX_ID {
                1
            } else {
                candidate.saturating_add(1)
            };
            if !self.timers.contains_key(&c) {
                id = Some(c);
                break;
            }
        }
        let Some(id) = id else {
            return Err(LimitError::TooManyTimers);
        };
        self.next_id = candidate;
        // "If timeout is less than 0, then set timeout to 0."
        let timeout = u64::try_from(timeout).unwrap_or(0);
        self.start_timer(id, handler, timeout, repeat);
        Ok(id)
    }

    /// `setTimeout(handler, timeout)`: [`EventLoop::set_timer`] with
    /// `repeat` false.
    pub fn set_timeout(
        &mut self,
        handler: CallbackId,
        timeout: i32,
        now: u64,
    ) -> Result<TimerId, LimitError> {
        self.set_timer(handler, timeout, false, now)
    }

    /// `setInterval(handler, timeout)`: [`EventLoop::set_timer`] with
    /// `repeat` true.
    pub fn set_interval(
        &mut self,
        handler: CallbackId,
        timeout: i32,
        now: u64,
    ) -> Result<TimerId, LimitError> {
        self.set_timer(handler, timeout, true, now)
    }

    /// The part of the timer initialisation steps after the id is chosen,
    /// shared with an interval's repeat:
    ///
    /// - "If the surrounding agent's event loop's currently running task is
    ///   a task that was created by this algorithm, then let nesting level
    ///   be that task's timer nesting level. Otherwise, let nesting level be
    ///   zero."
    /// - "Increment nesting level by one", "set `task`'s timer nesting level
    ///   to nesting level".
    /// - "If nesting level is greater than 5, and timeout is less than 4,
    ///   then set timeout to 4."
    /// - "Wait until any invocations of this algorithm that had the same
    ///   global and orderingIdentifier, that started before this one, and
    ///   whose milliseconds is equal to or less than this one's, have
    ///   completed", then "wait for timeout milliseconds": the timer is due
    ///   at `now + timeout`, and timers fire by (due time, order started).
    ///   A timer started earlier with a timeout no longer than a later one's
    ///   is due no later, and ties go to the earlier start, so the "wait
    ///   until" holds.
    /// - "Set global's map of setTimeout and setInterval IDs[id] to
    ///   uniqueHandle."
    fn start_timer(&mut self, id: TimerId, handler: CallbackId, timeout: u64, repeat: bool) {
        let level = self.current_level.saturating_add(1);
        let timeout = if level > 5 && timeout < 4 { 4 } else { timeout };
        let due = self.now.saturating_add(timeout);
        let seq = self.next_seq;
        self.next_seq = self.next_seq.saturating_add(1);
        self.waiting.insert((due, seq, id));
        self.timers.insert(
            id,
            Timer {
                handler,
                timeout,
                repeat,
                level,
                seq,
                state: TimerState::Waiting(due),
            },
        );
    }

    /// HTML §8.6† `clearTimeout` and `clearInterval`: "Remove `global`'s map
    /// of setTimeout and setInterval IDs[id]", which cancels the timer. The
    /// two methods share one map: an id from either clears either. An id not
    /// in the map does nothing. A timer whose task is already queued does
    /// nothing when the task runs.
    pub fn clear_timer(&mut self, id: i32) {
        let Some(id) = TimerId::from_script(id) else {
            return;
        };
        if let Some(timer) = self.timers.remove(&id)
            && let TimerState::Waiting(due) = timer.state
        {
            self.waiting.remove(&(due, timer.seq, id));
        }
    }

    /// The earliest time something can run: `now` if a task or microtask is
    /// queued, otherwise the earliest waiting timer's due time (`now` if it
    /// is already due), or `None` if nothing is pending.
    pub fn next_wake(&self) -> Option<u64> {
        if self.queued_tasks > 0 || !self.microtasks.is_empty() {
            return Some(self.now);
        }
        self.waiting
            .iter()
            .next()
            .map(|(due, _, _)| (*due).max(self.now))
    }

    /// "Choose a task queue": the next non-empty queue after the one last
    /// served, wrapping; then "let `oldestTask` be the first runnable task
    /// in `taskQueue`" and remove it.
    fn take_task(&mut self) -> Option<TaskKind> {
        let after = match self.last_served {
            Some(s) => Bound::Excluded(s),
            None => Bound::Unbounded,
        };
        let source = self
            .queues
            .range((after, Bound::Unbounded))
            .find(|(_, q)| !q.is_empty())
            .map(|(s, _)| *s)
            .or_else(|| {
                self.queues
                    .iter()
                    .find(|(_, q)| !q.is_empty())
                    .map(|(s, _)| *s)
            })?;
        let queue = self.queues.get_mut(&source)?;
        let task = queue.pop_front();
        if queue.is_empty() {
            self.queues.remove(&source);
        }
        if task.is_some() {
            self.queued_tasks = self.queued_tasks.saturating_sub(1);
            self.last_served = Some(source);
        }
        task
    }

    /// The timer steps' "wait for timeout milliseconds ... then queue a
    /// global object task ... on the timer task source": every waiting timer
    /// due at `now` or before, in firing order, while the task queues have
    /// room.
    fn queue_due_timers(&mut self) {
        while let Some(&(due, seq, id)) = self.waiting.iter().next() {
            if due > self.now || self.queued_tasks >= self.limits.max_tasks {
                break;
            }
            self.waiting.remove(&(due, seq, id));
            if let Some(timer) = self.timers.get_mut(&id) {
                timer.state = TimerState::Queued;
            }
            if self
                .push_task(TaskSource::Timer, TaskKind::Timer(id, seq))
                .is_err()
            {
                break;
            }
        }
    }

    /// The task a timer runs: "If id does not exist in global's map of
    /// setTimeout and setInterval IDs, then abort these steps"; run the
    /// handler with the task's nesting level as the current one; then, "if
    /// repeat is true, then perform the timer initialisation steps again,
    /// given ... id" (while the id is still in the map). A one-shot's id
    /// leaves the map before the handler runs, so its slot is free for the
    /// handler's own timers.
    fn run_timer_task<H: Host + ?Sized>(&mut self, host: &mut H, id: TimerId, seq: u64) {
        let Some(timer) = self.timers.get_mut(&id) else {
            return;
        };
        if timer.seq != seq || timer.state != TimerState::Queued {
            return;
        }
        let call = TimerCall {
            id,
            handler: timer.handler,
            repeat: timer.repeat,
            nesting_level: timer.level,
        };
        let (timeout, level) = (timer.timeout, timer.level);
        if timer.repeat {
            timer.state = TimerState::Running;
        } else {
            self.timers.remove(&id);
        }
        self.current_level = level;
        host.run_timer(self, call);
        // The repeat step runs in the same task, so the same level.
        self.current_level = level;
        if call.repeat && self.timers.get(&id).is_some_and(|t| t.seq == seq) {
            self.start_timer(id, call.handler, timeout, true);
        }
        self.current_level = 0;
    }

    /// One iteration of the processing model (HTML §8.1.7† "event loop
    /// processing model"), at the caller's time `now`:
    ///
    /// - Timers due by `now` are queued as tasks on the timer task source.
    /// - "Choose a task queue" and run its "oldest task" (if any queue has
    ///   one), with it as "the currently running task".
    /// - "Perform a microtask checkpoint."
    /// - If [`Host::rendering_opportunity`]: [`Host::update_the_rendering`],
    ///   then a microtask checkpoint.
    pub fn run_iteration<H: Host + ?Sized>(&mut self, host: &mut H, now: u64) -> Iteration {
        self.tick(now);
        let now = self.now;
        self.queue_due_timers();
        let mut ran_task = false;
        if let Some(task) = self.take_task() {
            ran_task = true;
            match task {
                TaskKind::Callback(callback) => {
                    self.current_level = 0;
                    host.run_task(self, callback);
                }
                TaskKind::Timer(id, seq) => self.run_timer_task(host, id, seq),
            }
        }
        // Also with no task: microtasks the host queued between iterations
        // run at this iteration's checkpoint.
        self.perform_microtask_checkpoint(host);
        let rendered = host.rendering_opportunity(now);
        if rendered {
            host.update_the_rendering(self, now);
            self.perform_microtask_checkpoint(host);
        }
        Iteration { ran_task, rendered }
    }

    /// Run iterations at the fixed time `now` until no task or microtask is
    /// queued and no timer is due, or `max_iterations` have run. Returns the
    /// iterations run. Timers that are not due stay waiting.
    pub fn run_until_idle<H: Host + ?Sized>(
        &mut self,
        host: &mut H,
        now: u64,
        max_iterations: usize,
    ) -> usize {
        let mut n = 0;
        while n < max_iterations {
            self.tick(now);
            let due = self
                .waiting
                .iter()
                .next()
                .is_some_and(|(d, _, _)| *d <= self.now);
            if self.queued_tasks == 0 && self.microtasks.is_empty() && !due {
                break;
            }
            self.run_iteration(host, now);
            n = n.saturating_add(1);
        }
        n
    }
}
