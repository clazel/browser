//! The backtrack stack: a `Vec` that refuses to grow past a stated number of
//! entries.
//!
//! The matcher (ECMA-262 §22.2.2†, continuation-passing) is run as a loop over
//! this stack, never by recursion. Every choice point and every change to a
//! register that a failure must undo is an [`Entry`]. The bound is the whole
//! of the matcher's heap use that depends on the input; exceeding it is
//! [`crate::MatchError::StackOverflow`], which the engine turns into a
//! `RangeError` (a listed deviation: phase-7.md item 7.10).

/// One entry of the backtrack stack. Three of the four kinds are 16 bytes;
/// [`Entry::Run`] makes the type 24.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Entry {
    /// A choice: on failure, resume at `pc` with the input position `pos`.
    Branch {
        /// The instruction to resume at.
        pc: u32,
        /// The input position.
        pos: usize,
    },
    /// An undo: on failure, put `old` back in register `reg`.
    Restore {
        /// The register.
        reg: u32,
        /// Its earlier value.
        old: usize,
    },
    /// The choices of a greedy loop over one character: on failure, resume at
    /// `pc` one character nearer to `limit` than `cur` (forward matching
    /// moves down to `limit`, backward matching up), and keep this entry until
    /// `limit` is reached.
    Run {
        /// The instruction to resume at.
        pc: u32,
        /// Whether the loop matches backwards (in a lookbehind).
        back: bool,
        /// The end of the longest run, or of the one tried last.
        cur: usize,
        /// The end of the shortest run.
        limit: usize,
    },
    /// The start of a lookaround's body. On failure it ends a negative
    /// lookaround as a success (resume at `pc`, position `pos`), and a
    /// positive one as a failure.
    LookMark {
        /// A negative lookaround.
        neg: bool,
        /// Where the instruction after the lookaround is.
        pc: u32,
        /// The input position the lookaround started at.
        pos: usize,
    },
}

/// The stack was full.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Full;

/// A stack of at most `max` entries.
#[derive(Debug)]
pub(crate) struct BtStack {
    items: Vec<Entry>,
    max: usize,
}

impl BtStack {
    /// An empty stack that holds at most `max` entries.
    pub(crate) fn new(max: usize) -> BtStack {
        BtStack {
            items: Vec::new(),
            max,
        }
    }

    /// The number of entries (the harnesses' view of the bound).
    #[cfg(kani)]
    pub(crate) fn len(&self) -> usize {
        self.items.len()
    }

    /// Pushes `e`, or says the stack is full (and leaves it as it was).
    pub(crate) fn push(&mut self, e: Entry) -> Result<(), Full> {
        if self.items.len() >= self.max {
            return Err(Full);
        }
        self.items.push(e);
        Ok(())
    }

    /// Pops the top entry.
    pub(crate) fn pop(&mut self) -> Option<Entry> {
        self.items.pop()
    }

    /// Removes every entry.
    pub(crate) fn clear(&mut self) {
        self.items.clear();
    }

    /// What a positive lookaround does when its body has matched: removes the
    /// topmost [`Entry::LookMark`] and every choice above it (the body is
    /// atomic), keeping the [`Entry::Restore`]s above it, so that backtracking
    /// past the lookaround still undoes the captures its body set. Returns the
    /// position the lookaround started at and the number of entries above the
    /// mark (the work done).
    pub(crate) fn commit_look(&mut self) -> Option<(usize, usize)> {
        let m = self
            .items
            .iter()
            .rposition(|e| matches!(e, Entry::LookMark { .. }))?;
        let Some(&Entry::LookMark { pos, .. }) = self.items.get(m) else {
            return None;
        };
        let len = self.items.len();
        let mut w = m;
        for r in m.saturating_add(1)..len {
            if matches!(self.items.get(r), Some(Entry::Restore { .. })) {
                self.items.swap(w, r);
                w = w.saturating_add(1);
            }
        }
        self.items.truncate(w);
        Some((pos, len.saturating_sub(m)))
    }
}
