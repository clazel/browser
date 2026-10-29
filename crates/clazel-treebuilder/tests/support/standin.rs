//! A test-only tokenizer stand-in for the tree-construction suite, until the
//! join with `clazel-html`'s tokenizer (Phase 4 item 4.11). It is not the
//! HTML tokenizer and never ships: it accepts only a small grammar on which
//! HTML §13.2.5's tokenizer behaves in one obvious way, and refuses
//! (`None`) everything else, so a case it accepts is tokenized exactly as
//! the standard would, and a case it refuses is counted as not run.
//!
//! Accepted: text without U+0000 and without `&` followed by an ASCII
//! alphanumeric or `#` (a lone `&` is itself, as the character reference
//! state's "anything else" makes it); CR and CR LF normalized to LF
//! (§13.2.3.5); start and end tags with ASCII names and attributes whose
//! names avoid `"`, `'`, `<` and `=` and whose values are quoted, or
//! unquoted without `"`, `'`, `<`, `=` and `` ` ``, and in either case
//! without a reference (`&` then an alphanumeric or `#`); `/>`; comments `<!--…-->`
//! whose body neither starts with `>` or `->` nor contains `--!`, `<!--` or
//! ends in `-`; `<!DOCTYPE name>` with a lowercase-able name and no
//! identifiers; a `<` not followed by an ASCII letter, `/`, `!` or `?`
//! (which is itself); and the RCDATA, RAWTEXT, script data (without
//! `<!--`) and PLAINTEXT states the tree builder switches to. Refused:
//! everything else (character references, `<?`, CDATA, bogus comments,
//! identifiers, end of file inside a tag or comment, …).

/// A token, as the tree builder's input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tok {
    /// DOCTYPE with a name and no identifiers.
    Doctype(Vec<u32>),
    /// Start tag: name, attributes, self-closing.
    Start(Vec<u32>, Vec<(Vec<u32>, Vec<u32>)>, bool),
    /// End tag: name.
    End(Vec<u32>),
    /// Comment.
    Comment(Vec<u32>),
    /// Character.
    Char(u32),
    /// End of file.
    Eof,
}

/// The states the tree builder switches the stand-in to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum State {
    /// Data state.
    Data,
    /// RCDATA state.
    Rcdata,
    /// RAWTEXT state.
    Rawtext,
    /// Script data state.
    ScriptData,
    /// PLAINTEXT state.
    Plaintext,
}

/// The stand-in tokenizer over a whole input.
pub struct StandIn {
    input: Vec<u32>,
    pos: usize,
    state: State,
    last_start: Option<Vec<u32>>,
    pending: std::collections::VecDeque<Tok>,
    done: bool,
}

fn is_alpha(c: u32) -> bool {
    (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c)
}

fn is_alnum(c: u32) -> bool {
    is_alpha(c) || (0x30..=0x39).contains(&c)
}

fn is_ws(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x20)
}

fn lower(c: u32) -> u32 {
    if (0x41..=0x5A).contains(&c) {
        c.saturating_add(0x20)
    } else {
        c
    }
}

impl StandIn {
    /// A stand-in over `text` (§13.2.3.5 newline normalization applied), or
    /// `None` if the text has a NUL.
    pub fn new(text: &str, state: State) -> Option<StandIn> {
        let mut input = Vec::new();
        let cps: Vec<u32> = text.chars().map(|c| c as u32).collect();
        let mut i = 0;
        while let Some(&c) = cps.get(i) {
            if c == 0 {
                return None;
            }
            if c == 0x0D {
                input.push(0x0A);
                if cps.get(i.saturating_add(1)) == Some(&0x0A) {
                    i = i.saturating_add(1);
                }
            } else {
                input.push(c);
            }
            i = i.saturating_add(1);
        }
        Some(StandIn {
            input,
            pos: 0,
            state,
            last_start: None,
            pending: Default::default(),
            done: false,
        })
    }

    /// The input after newline normalization.
    pub fn input(&self) -> &[u32] {
        &self.input
    }

    /// The position of the next token's first code point.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// The current state (the stand-in leaves a text state itself after an
    /// appropriate end tag).
    pub fn state(&self) -> State {
        self.state
    }

    /// Switch the state (the tree builder's request).
    pub fn set_state(&mut self, s: State) {
        self.state = s;
    }

    fn at(&self, i: usize) -> Option<u32> {
        self.input.get(i).copied()
    }

    /// The next token, or `None` if the input leaves the accepted grammar.
    pub fn next(&mut self) -> Option<Tok> {
        if let Some(t) = self.pending.pop_front() {
            return Some(t);
        }
        if self.done {
            return Some(Tok::Eof);
        }
        let Some(c) = self.at(self.pos) else {
            self.done = true;
            return Some(Tok::Eof);
        };
        match self.state {
            State::Plaintext => {
                self.pos = self.pos.saturating_add(1);
                Some(Tok::Char(c))
            }
            State::Data | State::Rcdata => {
                if c == 0x26 {
                    // '&' followed by an alphanumeric or '#' is a reference.
                    if self
                        .at(self.pos.saturating_add(1))
                        .is_some_and(|n| is_alnum(n) || n == 0x23)
                    {
                        return None;
                    }
                    self.pos = self.pos.saturating_add(1);
                    return Some(Tok::Char(c));
                }
                if c == 0x3C {
                    if self.state == State::Rcdata {
                        return self.text_end_tag();
                    }
                    return self.tag_open();
                }
                self.pos = self.pos.saturating_add(1);
                Some(Tok::Char(c))
            }
            State::Rawtext | State::ScriptData => {
                if c == 0x3C {
                    if self.state == State::ScriptData
                        && self.at(self.pos.saturating_add(1)) == Some(0x21)
                    {
                        return None;
                    }
                    return self.text_end_tag();
                }
                self.pos = self.pos.saturating_add(1);
                Some(Tok::Char(c))
            }
        }
    }

    /// In RCDATA, RAWTEXT and script data: `</name` with the last start
    /// tag's name followed by whitespace, `/` or `>` ends the text (an
    /// "appropriate end tag"); anything else is a `<` character.
    fn text_end_tag(&mut self) -> Option<Tok> {
        let start = self.pos;
        if self.at(start.saturating_add(1)) == Some(0x2F)
            && let Some(last) = self.last_start.clone()
        {
            {
                let mut j = start.saturating_add(2);
                let mut name = Vec::new();
                while let Some(c) = self.at(j) {
                    if !is_alpha(c) {
                        break;
                    }
                    name.push(lower(c));
                    j = j.saturating_add(1);
                }
                if name == last {
                    match self.at(j) {
                        Some(0x3E) => {
                            self.pos = j.saturating_add(1);
                            self.state = State::Data;
                            return Some(Tok::End(name));
                        }
                        Some(c) if is_ws(c) || c == 0x2F => return None,
                        _ => {}
                    }
                }
            }
        }
        self.pos = self.pos.saturating_add(1);
        Some(Tok::Char(0x3C))
    }

    fn tag_open(&mut self) -> Option<Tok> {
        let p = self.pos;
        match self.at(p.saturating_add(1)) {
            Some(c) if is_alpha(c) => self.tag(p.saturating_add(1), false),
            Some(0x2F) => match self.at(p.saturating_add(2)) {
                Some(c) if is_alpha(c) => self.tag(p.saturating_add(2), true),
                _ => None,
            },
            Some(0x21) => self.markup(p.saturating_add(2)),
            Some(0x3F) => None,
            // "<" followed by anything else (or end of file) is a character.
            _ => {
                self.pos = self.pos.saturating_add(1);
                Some(Tok::Char(0x3C))
            }
        }
    }

    fn tag(&mut self, mut j: usize, end: bool) -> Option<Tok> {
        let mut name = Vec::new();
        loop {
            let c = self.at(j)?;
            if is_ws(c) || c == 0x2F || c == 0x3E {
                break;
            }
            if c == 0x3C || c == 0x22 || c == 0x27 || c == 0x3D {
                return None;
            }
            name.push(lower(c));
            j = j.saturating_add(1);
        }
        let mut attrs: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
        let mut self_closing = false;
        loop {
            while self.at(j).is_some_and(is_ws) {
                j = j.saturating_add(1);
            }
            let c = self.at(j)?;
            if c == 0x3E {
                j = j.saturating_add(1);
                break;
            }
            if c == 0x2F {
                if self.at(j.saturating_add(1)) == Some(0x3E) {
                    self_closing = true;
                    j = j.saturating_add(2);
                    break;
                }
                return None;
            }
            let mut an = Vec::new();
            loop {
                let c = self.at(j)?;
                if is_ws(c) || c == 0x2F || c == 0x3E || c == 0x3D {
                    break;
                }
                if c == 0x22 || c == 0x27 || c == 0x3C {
                    return None;
                }
                an.push(lower(c));
                j = j.saturating_add(1);
            }
            if an.is_empty() {
                return None;
            }
            while self.at(j).is_some_and(is_ws) {
                j = j.saturating_add(1);
            }
            let mut value = Vec::new();
            if self.at(j) == Some(0x3D) {
                j = j.saturating_add(1);
                while self.at(j).is_some_and(is_ws) {
                    j = j.saturating_add(1);
                }
                match self.at(j)? {
                    q @ (0x22 | 0x27) => {
                        j = j.saturating_add(1);
                        loop {
                            let c = self.at(j)?;
                            j = j.saturating_add(1);
                            if c == q {
                                break;
                            }
                            // '&' then an alphanumeric or '#' is a
                            // reference; any other '&' is itself.
                            if c == 0x26 && self.at(j).is_some_and(|n| is_alnum(n) || n == 0x23) {
                                return None;
                            }
                            value.push(c);
                        }
                    }
                    0x3E => return None,
                    _ => loop {
                        let c = self.at(j)?;
                        if is_ws(c) || c == 0x3E {
                            break;
                        }
                        if matches!(c, 0x22 | 0x27 | 0x3C | 0x3D | 0x60) {
                            return None;
                        }
                        if c == 0x26
                            && self
                                .at(j.saturating_add(1))
                                .is_some_and(|n| is_alnum(n) || n == 0x23)
                        {
                            return None;
                        }
                        value.push(c);
                        j = j.saturating_add(1);
                    },
                }
            }
            // "If there is already an attribute on the token with the exact
            // same name", the new one is dropped.
            if !attrs.iter().any(|(n, _)| *n == an) {
                attrs.push((an, value));
            }
        }
        self.pos = j;
        if end {
            Some(Tok::End(name))
        } else {
            self.last_start = Some(name.clone());
            Some(Tok::Start(name, attrs, self_closing))
        }
    }

    fn markup(&mut self, j: usize) -> Option<Tok> {
        let rest: Vec<u32> = self.input.get(j..).map(|s| s.to_vec()).unwrap_or_default();
        let starts = |s: &str| {
            s.chars()
                .enumerate()
                .all(|(k, c)| rest.get(k).map(|&x| lower(x)) == Some(c as u32))
        };
        if rest.first() == Some(&0x2D) && rest.get(1) == Some(&0x2D) {
            let body_start = j.saturating_add(2);
            if matches!(self.at(body_start), Some(0x3E))
                || (self.at(body_start) == Some(0x2D)
                    && self.at(body_start.saturating_add(1)) == Some(0x3E))
            {
                return None;
            }
            let mut k = body_start;
            loop {
                let c = self.at(k)?;
                if c == 0x2D
                    && self.at(k.saturating_add(1)) == Some(0x2D)
                    && self.at(k.saturating_add(2)) == Some(0x3E)
                {
                    break;
                }
                k = k.saturating_add(1);
            }
            let body: Vec<u32> = self.input.get(body_start..k)?.to_vec();
            let s: String = body.iter().filter_map(|&c| char::from_u32(c)).collect();
            if s.contains("--!") || s.contains("<!--") || s.ends_with('-') {
                return None;
            }
            self.pos = k.saturating_add(3);
            return Some(Tok::Comment(body));
        }
        if starts("doctype") {
            let mut k = j.saturating_add(7);
            if !self.at(k).is_some_and(is_ws) {
                return None;
            }
            while self.at(k).is_some_and(is_ws) {
                k = k.saturating_add(1);
            }
            let mut name = Vec::new();
            loop {
                let c = self.at(k)?;
                if c == 0x3E {
                    break;
                }
                if is_ws(c) {
                    return None;
                }
                name.push(lower(c));
                k = k.saturating_add(1);
            }
            if name.is_empty() {
                return None;
            }
            self.pos = k.saturating_add(1);
            return Some(Tok::Doctype(name));
        }
        None
    }
}
