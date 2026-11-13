//! The states of `text/`'s passes, their invariants, and the contracts of
//! the steps over them.
//!
//! Every pass over a text is a loop whose body is one step: a function of a
//! small state and the next unit (with, for UAX #14, at most two items of
//! right context), returning a decision and the next state. The drivers
//! (`uax14::breaks_with_rules`, `collapse::collapse_raw`,
//! `lines::break_lines`, `wrap::wraps_from_breaks`) only feed units to the
//! steps. A Kani harness over **any state satisfying the invariant** and any
//! next unit then covers texts of every length: the state a driver reaches
//! after any prefix satisfies the invariant (the start state does, and each
//! step preserves it), so no step on any text can panic or break the
//! properties the harness asserts.
//!
//! The steps are, with their sources:
//!
//! - **UAX #14** (`uax14::step`):
//!   `step(state: &BreakState, c: Props, next: Option<Props>,
//!   after_next: Option<Props>) -> (Break, Rule, BreakState)`. The decision at
//!   the position before `c` (between the previous character and `c`; for
//!   the first character, LB2's "sot ×"), by rules LB2 and LB4 to LB31 in
//!   order, and the state after `c`. `next` and `after_next` are the two
//!   items after `c`'s item (LB9), the most right context any rule reads:
//!   LB15b, LB15c, LB19a and LB28a read one item, LB25's "PO × OP IS NU" two.
//!   eot's decision is LB3's "! eot", which needs no state.
//! - **CSS Text 3 §4.1.1 Phase I** (`collapse::step`):
//!   `step(state: &CollapseState, raw: Raw, ws: WhiteSpace) -> (Emit,
//!   CollapseState)`: what becomes of the next character, given its
//!   `white-space`.
//! - **CSS Text 3 §5** (`wrap::wrap_at`): `wrap_at(here: &Side, next:
//!   Option<&Side>, b: Break, rule: Rule) -> Wrap`: the opportunity after a
//!   unit from the unit, the next one and UAX #14's decision there. It needs
//!   no state.
//! - **Choosing lines** (`lines::fit_step`): `fit_step(state: &FitState, i:
//!   usize, u: &Unit, advance: i32, wrap: Wrap, available: i32) -> Fit`:
//!   unit `i` added to the line being filled, which then ends or goes on.
//!   [`Measure::add`] is the measuring part, shared with the intrinsic sizes.
//!
//! Phase II (`lines::trim`) walks back from a line's end; it is not a step
//! over a state and is checked only on bounded inputs (README).

use super::classes::{Lb, Props};
use super::collapse::{Kind, Unit};

/// Whether `c` is a class in `set` (a mask of [`Lb::bit`]s).
fn in_set(c: Lb, set: u64) -> bool {
    set & c.bit() != 0
}

/// What UAX #14's rules remember of the text before a position: everything
/// LB4 to LB31 read to the left of it, summarised. "Items" are LB9's: the
/// characters LB9 did not absorb, with LB10's properties for a remaining CM
/// or ZWJ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct BreakState {
    /// The class (after LB1) of the character before the position; `None`
    /// at sot. LB4, LB5, LB8a and LB9 read it.
    pub raw_prev: Option<Lb>,
    /// LB8: the characters before the position are `ZW SP*`.
    pub zw_spaces: bool,
    /// The item before the position (LB11 to LB31's left side).
    pub a: Option<Props>,
    /// The item before `a` (LB19a's "sot | [^$EastAsian]", LB20a's and LB21a's
    /// first element, LB28a's "(AK | [◌] | AS) VI").
    pub a_prev: Option<Props>,
    /// The last item before the position that is not SP: the `X` of LB14's
    /// `OP SP*`, LB15a's `[\p{Pi}&QU] SP*`, LB16's `(CL | CP) SP*` and
    /// LB17's `B2 SP*`.
    pub before_spaces: Option<Props>,
    /// LB15a: the item before `before_spaces` is sot or one of `BK CR LF NL
    /// OP QU GL SP ZW`.
    pub lb15a_start: bool,
    /// LB25: the items before the position end in `NU ( SY | IS )*`.
    pub numeric: bool,
    /// LB25: the items before the position end in `NU ( SY | IS )* ( CL |
    /// CP )`.
    pub numeric_close: bool,
    /// LB30a: the items before the position end in an odd number of RI.
    pub ri_odd: bool,
}

/// LB15a's set of classes before the quotation mark.
pub const LB15A_START: u64 = lb_set![BK, CR, LF, NL, OP, QU, GL, SP, ZW];

impl BreakState {
    /// At sot: nothing before.
    pub const START: BreakState = BreakState {
        raw_prev: None,
        zw_spaces: false,
        a: None,
        a_prev: None,
        before_spaces: None,
        lb15a_start: false,
        numeric: false,
        numeric_close: false,
        ri_odd: false,
    };

    /// The invariant every state a driver reaches satisfies. Each clause is
    /// what the fields mean, as far as it can be said of the state alone:
    ///
    /// 1. there is an item before the position exactly when there is a
    ///    character, and an item before that only if there is one before;
    /// 2. at sot, every summary is empty;
    /// 3. no item is CM or ZWJ (LB9 absorbed it, or LB10 made it AL);
    /// 4. the character before the position is the item before it, or a CM
    ///    or ZWJ (absorbed into it, or made AL by LB10);
    /// 5. `before_spaces` is `a` when `a` is not SP, and is never SP;
    ///    `lb15a_start` is only set with a `before_spaces`;
    /// 6. `numeric` only after NU, SY or IS; `numeric_close` only after CL or
    ///    CP; `ri_odd` only after RI;
    /// 7. `zw_spaces` only after ZW or SP.
    pub fn invariant(&self) -> bool {
        let not_mark = |p: &Option<Props>| p.is_none_or(|p| !matches!(p.class, Lb::CM | Lb::ZWJ));
        let a_class = self.a.map(|p| p.class);
        // 1.
        self.raw_prev.is_some() == self.a.is_some()
            && (self.a_prev.is_none() || self.a.is_some())
            // 2.
            && (self.a.is_some()
                || (!self.zw_spaces
                    && self.before_spaces.is_none()
                    && !self.lb15a_start
                    && !self.numeric
                    && !self.numeric_close
                    && !self.ri_odd))
            // 3.
            && not_mark(&self.a)
            && not_mark(&self.a_prev)
            && not_mark(&self.before_spaces)
            // 4.
            && (self.raw_prev == a_class || matches!(self.raw_prev, Some(Lb::CM | Lb::ZWJ)))
            // 5.
            && (match self.a {
                Some(a) if a.class != Lb::SP => self.before_spaces == Some(a),
                _ => true,
            })
            && self.before_spaces.is_none_or(|p| p.class != Lb::SP)
            && (self.before_spaces.is_some() || !self.lb15a_start)
            // 6.
            && (!self.numeric || a_class.is_some_and(|c| in_set(c, lb_set![NU, SY, IS])))
            && (!self.numeric_close || a_class.is_some_and(|c| in_set(c, lb_set![CL, CP])))
            && (!self.ri_odd || a_class == Some(Lb::RI))
            // 7.
            && (!self.zw_spaces || matches!(self.raw_prev, Some(Lb::ZW | Lb::SP)))
    }
}

/// Phase I: what the last unit kept (bidi formatting characters aside) was.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Last {
    /// Nothing yet.
    Start,
    /// Anything that is not a collapsible space or a segment break.
    Other,
    /// A collapsible space from a space or a tab.
    Space,
    /// A collapsible segment break, transformed into a space (§4.1.3).
    ConvertedBreak,
    /// A preserved segment break.
    PreservedBreak,
}

/// What Phase I (CSS Text 3 §4.1.1, §4.1.3) remembers of the characters
/// before the next one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct CollapseState {
    /// The last unit kept, bidi formatting characters aside (they are "not
    /// there" for every step of Phase I).
    pub last: Last,
    /// Step 1's "preceding": the last unit kept is a collapsible space that
    /// a segment break would remove ("Any sequence of collapsible spaces and
    /// tabs immediately preceding … a segment break is removed"), with what
    /// `last` was before it.
    pub pending: Option<Last>,
    /// Step 1's "following": since the last segment break there have been
    /// only collapsible spaces and tabs (all removed) and bidi formatting
    /// characters.
    pub after_break: bool,
}

/// What Phase I's step does with the next character.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Emit {
    /// It is removed.
    Nothing,
    /// It is kept, as a unit of this kind.
    Push(Kind),
    /// The pending collapsible space is removed (step 1), and so is it.
    Retract,
    /// The pending collapsible space is removed (step 1), and it is kept as
    /// a unit of this kind.
    RetractAndPush(Kind),
}

impl CollapseState {
    /// Before the first character.
    pub const START: CollapseState = CollapseState {
        last: Last::Start,
        pending: None,
        after_break: false,
    };

    /// The invariant: a collapsible space is pending exactly when it is the
    /// last unit kept, and what it replaced was not a collapsible space or
    /// segment break (step 4 and step 1 would have removed it); the last
    /// unit kept is a segment break exactly when only collapsible spaces,
    /// tabs and bidi formatting characters have come since it
    /// (`after_break`), and then nothing is pending.
    pub fn invariant(&self) -> bool {
        (self.last == Last::Space) == self.pending.is_some()
            && matches!(self.pending, None | Some(Last::Start | Last::Other))
            && self.after_break == matches!(self.last, Last::ConvertedBreak | Last::PreservedBreak)
    }
}

/// One side of a position between two units, as `wrap::wrap_at` reads it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Side {
    /// The unit.
    pub unit: Unit,
    /// Its class after LB1 (`Props::css`).
    pub class: Lb,
    /// Whether LB9 absorbed it.
    pub absorbed: bool,
    /// Its class after LB9 and LB10.
    pub effective: Lb,
}

/// A line as it grows from its start: the pen, and the width for fit (the
/// pen after the last unit that Phase II neither removes nor hangs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Measure {
    /// The pen, from the line's start (26.6).
    pub pen: i32,
    /// The width measured for fit (26.6).
    pub fit: i32,
    /// Only collapsible spaces so far (Phase II step 1 removes them).
    pub leading: bool,
}

impl Measure {
    /// An empty line.
    pub const START: Measure = Measure {
        pen: 0,
        fit: 0,
        leading: true,
    };

    /// Whether unit `u` takes width: not a leading collapsible space (Phase
    /// II step 1) and not a forced break.
    pub fn takes_width(&self, u: &Unit) -> bool {
        !((self.leading && u.kind == Kind::CollapsibleSpace) || u.kind == Kind::ForcedBreak)
    }
}

/// The line being filled by `lines::break_lines`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct FitState {
    /// The line's first unit.
    pub start: usize,
    /// Its measure so far.
    pub m: Measure,
    /// The last soft wrap opportunity whose line fits: (end, width).
    pub soft: Option<(usize, i32)>,
    /// The last `overflow-wrap` opportunity whose line fits, if no soft one.
    pub emergency: Option<(usize, i32)>,
    /// The line overflows with no opportunity yet: it ends at the next.
    pub overflowed: bool,
}

/// What `lines::fit_step` makes of the line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fit {
    /// It goes on.
    Continue(FitState),
    /// It ends before unit `end`.
    End {
        /// One past its last unit.
        end: usize,
        /// Whether a forced break ends it.
        forced: bool,
        /// Its width for fit.
        width: i32,
    },
}

impl FitState {
    /// A line starting at unit `start`.
    pub fn new(start: usize) -> FitState {
        FitState {
            start,
            m: Measure::START,
            soft: None,
            emergency: None,
            overflowed: false,
        }
    }

    /// The invariant before unit `i` is added: the line started at or
    /// before `i`; every remembered opportunity ends the line after at
    /// least one unit and before `i`'s; and an overflowing line remembers
    /// none (it found none when it overflowed, and ends at the next).
    pub fn invariant(&self, i: usize) -> bool {
        let inside = |o: Option<(usize, i32)>| o.is_none_or(|(e, _)| self.start < e && e <= i);
        self.start <= i
            && inside(self.soft)
            && inside(self.emergency)
            && (!self.overflowed || (self.soft.is_none() && self.emergency.is_none()))
    }
}
