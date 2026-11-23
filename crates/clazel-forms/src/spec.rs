//! Executable-style specification of HTML's form owner and "constructing
//! the entry list" over a `clazel-dom` arena (Phase 6 item 6.13). Nothing
//! here runs; it defines what "correct" means. Every function cites its
//! algorithm, and each `// N.` comment is the step number in it.
//!
//! Source (pinned; a review is against exactly this text): HTML Standard,
//! Living Standard, commit `0793d3d8544eee95a862e6637130a8106c3d11ca`
//! (14 November 2026; the `source` file at that commit was read on
//! 16 November 2026, and the section numbers are those of the multipage
//! build of the same day):
//! - §4.10.18.3 "Association of controls and forms": "form owner", "reset
//!   the form owner" (steps 1 to 6), and the HTML insertion steps' form
//!   owner rule (§2.1.x "Common infrastructure", the insertion steps);
//!   §13.2.6.1 "create an element for the token", step 21, where the parser
//!   associates an element with the `form` element pointer;
//! - §4.10.18.5 "disabled" (a form control is disabled), §4.10.18.1 "a form
//!   control's value" and its dirty value flag;
//! - §4.10.22.4 "Constructing the entry list" (steps 1 to 5, 5.1 to 5.11,
//!   and the steps after), "create an entry";
//! - §4.10.5.1 the `input` element's `type` states and value modes, the
//!   value sanitization algorithms, §4.10.5.x "auto-directionality
//!   form-associated elements" (§3.2.6.x), §4.10.6 `button` value,
//!   §4.10.7 `select` "list of options" and §4.10.10 `option` "disabled" and
//!   "value", §4.10.11 `textarea` ("API value", "textarea wrapping
//!   transformation", `cols`, `wrap`), §4.10.20 `fieldset`;
//! - Infra "normalize newlines", "strip newlines", "strip leading and
//!   trailing ASCII whitespace", "ASCII case-insensitive", and HTML §2.3.4.2
//!   "rules for parsing non-negative integers".
//!
//! Modelling choices (each a deliberate difference in form, never in
//! meaning, or a stated restriction):
//! - **The DOM is a `clazel-dom` arena** ([`Document`]); an element is a
//!   [`NodeId`]. "Tree order" is the DOM's preorder walk, [`tree_order`],
//!   written with a depth fuel of the arena's size (the pattern of
//!   `clazel_dom::spec::is_inclusive_ancestor`): in a well-formed arena
//!   every chain of parents ends within `nodes.len()` steps, so the fuel
//!   never runs out. Ancestor walks ([`root`], [`nearest_form_ancestor`],
//!   [`has_datalist_ancestor`], [`fieldset_disables`], [`option_disabled`])
//!   use the same fuel.
//! - **Control state is a side table** ([`FormState`]), keyed by node id and
//!   a parameter of every algorithm, like Phase 5's computed style. A node
//!   beyond the table has the default state ([`default_control`]). The table
//!   holds what the standard keeps in the element: the internal `value`, the
//!   dirty value flag, `checkedness` and its dirty flag, and an option's
//!   `selectedness`, plus the coordinates of the click that submitted an
//!   image button ("selected coordinate"). While a dirty flag is false the
//!   standard says the value or checkedness mirrors the content attribute
//!   (HTML §4.10.18.1 and §4.10.5.1); [`control_value`] and [`checkedness`]
//!   read the attribute then. **An option's selectedness is read from the
//!   table alone**: the "selectedness setting algorithm" (which selects the
//!   first enabled option of a single-selection `select`) and the radio
//!   button group's exclusion are the editing layer's (item 6.15) and the
//!   caller's, not run here. Listed.
//! - **The form owner is the arena's `form_owner` as the parser set it, or
//!   the standard's "reset the form owner" on the final tree.** The tree
//!   builder associates an element with the `form` element pointer when it
//!   creates it and sets the element's "parser inserted flag"
//!   (§13.2.6.1 step 21); the arena has no flag, so a `Some` owner means the
//!   flag is set and the insertion steps leave the owner alone. A `None`
//!   owner means the flag is unset, so the insertion steps "reset the form
//!   owner" (the nearest ancestor `form`, or the `form` attribute's target);
//!   the arena runs no insertion steps, so [`form_owner`] runs that reset on
//!   the tree as it is, which is what the last insertion left, since a later
//!   insertion of the `form` named by an ID re-runs it ("reset the form
//!   owners with a form attribute"). Moves of nodes by the adoption agency
//!   and foster parenting keep one tree, so their removing steps do nothing.
//!   Listed.
//! - **The controls are those of the form's tree**: "a list of all the
//!   submittable elements whose form owner is form, in tree order" is read
//!   over the tree of `form` (the preorder walk from its root); a form
//!   owner is always in the element's own tree (the removing steps reset
//!   it otherwise).
//! - **The document's character encoding is a parameter** (`encoding`, the
//!   "name of encoding"), and the "constructing entry list" flag of the form
//!   is a parameter (`constructing`); steps 2 and the last step set and
//!   clear it around a computation nobody can observe (the `formdata` event
//!   is out, no script), so they are folded into the parameter's test.
//!   Steps "Let form data be a new FormData object …" and "Fire an event
//!   named formdata" need script and are skipped.
//! - **No `File` entries.** `type=file` is out (phase-6.md 6.0): a file
//!   input contributes no entry, where the standard adds an empty `File`
//!   (step 5.8). Listed. "Form-associated custom elements" (step 5.3) do
//!   not exist without script.
//! - **Entry values are strings** (`Seq<u32>` code points): every
//!   remaining entry's value is a string.
//! - **Coordinates are `nat`**: the selected coordinate of an image button
//!   is relative to the image and not negative; "x" and "y" are written in
//!   decimal.
//! - **`dirname` direction is always `ltr`** ("the directionality of the
//!   element" is 'ltr' until bidi, Phase 8). Listed.
//! - **An `option`'s value without a `value` attribute is the table's
//!   `value`**: HTML's "get HTML-aware text content" (descendant text,
//!   skipping `script` and `img`, whitespace stripped and collapsed) is not
//!   transcribed yet; the caller supplies it. Listed.
//! - **The textarea wrapping transformation's algorithm is
//!   implementation-defined** (§4.10.11: "using an implementation-defined
//!   algorithm so that each line has no more than character width
//!   characters"). [`wrap_hard`] breaks a line after every `cols` characters
//!   when more follow, which meets the requirement.
//! - **Input types the item does not list** (`date`, `time`, `color`,
//!   `range`, `number`, …) are [`InputType::Other`]: they read the table's
//!   value, or the `value` attribute while not dirty, with no sanitization
//!   (so `number` is text, as the item says). `email` is read as a single
//!   address (the `multiple` attribute's list sanitization is not run).
//! - **Attributes**: "has an attribute specified" and "the value of the
//!   attribute" read the first attribute in the element's list with a null
//!   namespace and that local name ([`find_attr`]); the parser lower-cases
//!   HTML attribute names, so a local name is the qualified name.
//! - **An element's ID** is its `id` attribute's value when not empty (DOM
//!   §4.9: an empty `id` unsets the ID).
//! - **`fieldset`'s disabled rule** says the control is "a descendant of a
//!   `fieldset` whose `disabled` attribute is specified, and not a
//!   descendant of that `fieldset`'s first `legend` child". The walk
//!   [`fieldset_disables`] goes up one parent at a time carrying the child it
//!   came from: in a tree an element lies under the `legend` exactly when
//!   the child of the `fieldset` on its chain is that `legend`.

#[cfg(verus_only)]
use clazel_dom::spec as dom;
pub use clazel_dom::spec::{Attr, Document, Namespace, NodeId};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Strings

/// ASCII bytes as code points.
pub open spec fn ascii(b: Seq<u8>) -> Seq<u32> {
    b.map_values(|c: u8| c as u32)
}

/// Infra "ASCII lower alpha" mapping of one code point.
pub open spec fn ascii_lower_cp(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// Every ASCII upper alpha of `s` replaced by its lowercase.
pub open spec fn ascii_lower(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| ascii_lower_cp(c))
}

/// Infra "ASCII case-insensitive match" of `s` with a lowercase ASCII
/// keyword `k`.
pub open spec fn ci_eq(s: Seq<u32>, k: Seq<u8>) -> bool {
    ascii_lower(s) == ascii(k)
}

/// Infra "ASCII whitespace": U+0009 TAB, U+000A LF, U+000C FF, U+000D CR,
/// U+0020 SPACE.
pub open spec fn is_ascii_whitespace(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// Infra "strip newlines": "remove all U+000A LF and U+000D CR code points
/// from string".
pub open spec fn strip_newlines(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 0x0A || s[0] == 0x0D {
        strip_newlines(s.drop_first())
    } else {
        seq![s[0]] + strip_newlines(s.drop_first())
    }
}

/// `s` without its leading ASCII whitespace.
pub open spec fn trim_start(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() > 0 && is_ascii_whitespace(s[0]) {
        trim_start(s.drop_first())
    } else {
        s
    }
}

/// `s` without its trailing ASCII whitespace.
pub open spec fn trim_end(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() > 0 && is_ascii_whitespace(s[s.len() - 1]) {
        trim_end(s.drop_last())
    } else {
        s
    }
}

/// Infra "strip leading and trailing ASCII whitespace".
pub open spec fn strip_whitespace(s: Seq<u32>) -> Seq<u32> {
    trim_end(trim_start(s))
}

/// Infra "normalize newlines": "replace every U+000D CR U+000A LF code
/// point pair with a single U+000A LF code point, and then replace every
/// remaining U+000D CR code point with a U+000A LF code point". One pass
/// gives the same string: a CR followed by LF becomes one LF, any other CR
/// becomes one LF.
pub open spec fn normalize_newlines(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 0x0D {
        if s.len() > 1 && s[1] == 0x0A {
            seq![0x0Au32] + normalize_newlines(s.skip(2))
        } else {
            seq![0x0Au32] + normalize_newlines(s.drop_first())
        }
    } else {
        seq![s[0]] + normalize_newlines(s.drop_first())
    }
}

/// HTML §2.3.4.2 "rules for parsing non-negative integers", the value as a
/// natural number, or none on error. "Rules for parsing integers": skip
/// leading ASCII whitespace; an optional sign ("-" gives a value that is
/// negative, or zero for "-0"); then at least one ASCII digit, collected
/// until a non-digit. A negative result is an error for the non-negative
/// rules, and "-0" is zero.
pub open spec fn digits_value(s: Seq<u32>, acc: nat) -> nat
    decreases s.len(),
{
    if s.len() > 0 && 0x30 <= s[0] <= 0x39 {
        digits_value(s.drop_first(), acc * 10 + (s[0] - 0x30) as nat)
    } else {
        acc
    }
}

/// Step "collect a sequence of code points that are ASCII digits" is
/// non-empty.
pub open spec fn starts_with_digit(s: Seq<u32>) -> bool {
    s.len() > 0 && 0x30 <= s[0] <= 0x39
}

/// [`parse_non_negative`] after the whitespace is skipped and the sign read.
pub open spec fn parse_after_sign(s: Seq<u32>, negative: bool) -> Option<nat> {
    if !starts_with_digit(s) {
        None
    } else {
        let v = digits_value(s, 0);
        if negative && v != 0 {
            None
        } else {
            Some(v)
        }
    }
}

/// The rules for parsing non-negative integers.
pub open spec fn parse_non_negative(s: Seq<u32>) -> Option<nat> {
    let t = trim_start(s);
    if t.len() > 0 && t[0] == 0x2D {
        parse_after_sign(t.drop_first(), true)
    } else if t.len() > 0 && t[0] == 0x2B {
        parse_after_sign(t.drop_first(), false)
    } else {
        parse_after_sign(t, false)
    }
}

/// A natural number in decimal ("the shortest string of ASCII digits").
pub open spec fn decimal(n: nat) -> Seq<u32>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u32]
    } else {
        decimal(n / 10) + seq![(0x30 + n % 10) as u32]
    }
}

// ---------------------------------------------------------------------
// Elements and attributes

/// The attribute list of an element.
pub open spec fn attrs(doc: Document, n: NodeId) -> Seq<Attr> {
    doc.nodes[n as int].kind->Element_attributes
}

/// The value of the first attribute in `list` with a null namespace and
/// local name `name`, or none ("has an attribute specified").
pub open spec fn find_attr(list: Seq<Attr>, name: Seq<u32>) -> Option<Seq<u32>>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else if list[0].namespace is None && list[0].local_name == name {
        Some(list[0].value)
    } else {
        find_attr(list.drop_first(), name)
    }
}

/// The value of attribute `name` of element `n`.
pub open spec fn attr(doc: Document, n: NodeId, name: Seq<u8>) -> Option<Seq<u32>> {
    find_attr(attrs(doc, n), ascii(name))
}

/// Element `n` has attribute `name` specified.
pub open spec fn has_attr(doc: Document, n: NodeId, name: Seq<u8>) -> bool {
    attr(doc, n, name) is Some
}

/// `n` is an element of the HTML namespace with local name `name`.
pub open spec fn is_html(doc: Document, n: NodeId, name: Seq<u8>) -> bool {
    &&& dom::valid(doc, n)
    &&& doc.nodes[n as int].kind is Element
    &&& doc.nodes[n as int].kind->Element_namespace == Some(Namespace::Html)
    &&& doc.nodes[n as int].kind->Element_local_name == ascii(name)
}

/// `n` is an element.
pub open spec fn is_element(doc: Document, n: NodeId) -> bool {
    dom::valid(doc, n) && doc.nodes[n as int].kind is Element
}

/// An element's ID (DOM §4.9): its `id` attribute's value if not empty.
pub open spec fn element_id(doc: Document, n: NodeId) -> Option<Seq<u32>> {
    match attr(doc, n, b"id"@) {
        Some(v) => if v.len() > 0 {
            Some(v)
        } else {
            None
        },
        None => None,
    }
}

/// The states of an `input` element's `type` attribute (HTML §4.10.5.1),
/// with the types of no consequence here as `Other`.
pub enum InputType {
    /// "hidden"
    Hidden,
    /// "text", and the missing and invalid value default
    Text,
    /// "search"
    Search,
    /// "tel"
    Tel,
    /// "url"
    Url,
    /// "email"
    Email,
    /// "password"
    Password,
    /// `number`, `date`, `month`, `week`, `time`, `datetime-local`, `range`,
    /// `color`: read as text (see the modelling choices).
    Other,
    /// "checkbox"
    Checkbox,
    /// "radio"
    Radio,
    /// "file"
    File,
    /// "submit"
    Submit,
    /// "image"
    Image,
    /// "reset"
    Reset,
    /// "button"
    Button,
}

/// The state of the `type` attribute of an `input` element: an enumerated
/// attribute, matched ASCII case-insensitively; the missing and invalid
/// value default is Text.
pub open spec fn input_type(doc: Document, n: NodeId) -> InputType {
    match attr(doc, n, b"type"@) {
        None => InputType::Text,
        Some(v) => if ci_eq(v, b"hidden"@) {
            InputType::Hidden
        } else if ci_eq(v, b"search"@) {
            InputType::Search
        } else if ci_eq(v, b"tel"@) {
            InputType::Tel
        } else if ci_eq(v, b"url"@) {
            InputType::Url
        } else if ci_eq(v, b"email"@) {
            InputType::Email
        } else if ci_eq(v, b"password"@) {
            InputType::Password
        } else if ci_eq(v, b"checkbox"@) {
            InputType::Checkbox
        } else if ci_eq(v, b"radio"@) {
            InputType::Radio
        } else if ci_eq(v, b"file"@) {
            InputType::File
        } else if ci_eq(v, b"submit"@) {
            InputType::Submit
        } else if ci_eq(v, b"image"@) {
            InputType::Image
        } else if ci_eq(v, b"reset"@) {
            InputType::Reset
        } else if ci_eq(v, b"button"@) {
            InputType::Button
        } else if ci_eq(v, b"number"@) || ci_eq(v, b"date"@) || ci_eq(v, b"month"@) || ci_eq(v, b"week"@) || ci_eq(
            v,
            b"time"@,
        ) || ci_eq(v, b"datetime-local"@) || ci_eq(v, b"range"@) || ci_eq(v, b"color"@) {
            InputType::Other
        } else {
            InputType::Text
        },
    }
}

/// HTML §4.10.2 "submittable elements" (category-submit): `button`,
/// `input`, `select`, `textarea` (form-associated custom elements are out).
pub open spec fn is_submittable(doc: Document, n: NodeId) -> bool {
    is_html(doc, n, b"button"@) || is_html(doc, n, b"input"@) || is_html(doc, n, b"select"@) || is_html(
        doc,
        n,
        b"textarea"@,
    )
}

/// HTML §4.10.2 "listed" elements: `button`, `fieldset`, `input`, `object`,
/// `output`, `select`, `textarea`.
pub open spec fn is_listed(doc: Document, n: NodeId) -> bool {
    is_submittable(doc, n) || is_html(doc, n, b"fieldset"@) || is_html(doc, n, b"object"@) || is_html(
        doc,
        n,
        b"output"@,
    )
}

/// HTML §4.10.2 "button" (concept-button): a `button` element, or an
/// `input` in the Submit, Image, Reset or Button state.
pub open spec fn is_button(doc: Document, n: NodeId) -> bool {
    is_html(doc, n, b"button"@) || (is_html(doc, n, b"input"@) && (input_type(doc, n) is Submit || input_type(
        doc,
        n,
    ) is Image || input_type(doc, n) is Reset || input_type(doc, n) is Button))
}

/// HTML §3.2.6.x "auto-directionality form-associated elements": `input`
/// in the Hidden, Text, Search, Telephone, URL, Email, Password, Submit,
/// Reset or Button state, and `textarea`.
pub open spec fn is_auto_directionality(doc: Document, n: NodeId) -> bool {
    is_html(doc, n, b"textarea"@) || (is_html(doc, n, b"input"@) && (input_type(doc, n) is Hidden
        || input_type(doc, n) is Text || input_type(doc, n) is Search || input_type(doc, n) is Tel
        || input_type(doc, n) is Url || input_type(doc, n) is Email || input_type(doc, n) is Password
        || input_type(doc, n) is Submit || input_type(doc, n) is Reset || input_type(doc, n) is Button))
}

// ---------------------------------------------------------------------
// Control state

/// What the standard keeps in a form control, and the click that submitted
/// an image button.
pub struct ControlState {
    /// "value" (§4.10.18.1): the internal value, used when the dirty value
    /// flag is true; for a `textarea` its raw value; for an `option` the
    /// text it has no `value` attribute for (see the modelling choices).
    pub value: Seq<u32>,
    /// "dirty value flag": false means the value mirrors the default value.
    pub dirty_value: bool,
    /// "checkedness" (§4.10.18.1), used when the dirty checkedness flag is
    /// true.
    pub checked: bool,
    /// "dirty checkedness flag".
    pub dirty_checked: bool,
    /// An `option`'s "selectedness".
    pub selected: bool,
    /// The "selected coordinate" of an image button, x.
    pub x: nat,
    /// The "selected coordinate" of an image button, y.
    pub y: nat,
}

/// The state of a control the table has no row for: clean and empty.
pub open spec fn default_control() -> ControlState {
    ControlState { value: Seq::empty(), dirty_value: false, checked: false, dirty_checked: false, selected: false, x: 0, y: 0 }
}

/// The side table: one row per node id, from 0.
pub struct FormState {
    /// The rows, by node id.
    pub rows: Seq<ControlState>,
}

/// The state of node `id`.
pub open spec fn control(st: FormState, id: NodeId) -> ControlState {
    if id < st.rows.len() {
        st.rows[id as int]
    } else {
        default_control()
    }
}

// ---------------------------------------------------------------------
// Tree order and ancestors

/// DOM "tree order" of the tree below `n` (preorder, depth-first): `n`,
/// then each child's tree in order. A node `fuel` levels deep is cut off.
pub open spec fn tree_order(doc: Document, n: NodeId, fuel: nat) -> Seq<NodeId>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        Seq::empty()
    } else {
        seq![n] + forest_order(doc, doc.nodes[n as int].children, (fuel - 1) as nat)
    }
}

/// The tree orders of `kids`, one after the other.
pub open spec fn forest_order(doc: Document, kids: Seq<NodeId>, fuel: nat) -> Seq<NodeId>
    decreases fuel, kids.len(),
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        tree_order(doc, kids[0], fuel) + forest_order(doc, kids.drop_first(), fuel)
    }
}

/// The root of `x`: the last node of the chain of parents, within `fuel`
/// steps.
pub open spec fn root_within(doc: Document, x: NodeId, fuel: nat) -> NodeId
    decreases fuel,
{
    match doc.nodes[x as int].parent {
        None => x,
        Some(p) => if fuel == 0 {
            x
        } else {
            root_within(doc, p, (fuel - 1) as nat)
        },
    }
}

/// DOM "root" of a node (§4.2): its farthest inclusive ancestor.
pub open spec fn root(doc: Document, x: NodeId) -> NodeId {
    root_within(doc, x, doc.nodes.len())
}

/// The nearest `form` ancestor of `x` within `fuel` steps up.
pub open spec fn nearest_form_within(doc: Document, x: NodeId, fuel: nat) -> Option<NodeId>
    decreases fuel,
{
    match doc.nodes[x as int].parent {
        None => None,
        Some(p) => if is_html(doc, p, b"form"@) {
            Some(p)
        } else if fuel == 0 {
            None
        } else {
            nearest_form_within(doc, p, (fuel - 1) as nat)
        },
    }
}

/// "the nearest such ancestor `form` element" (§4.10.18.3, reset the form
/// owner step 4).
pub open spec fn nearest_form_ancestor(doc: Document, x: NodeId) -> Option<NodeId> {
    nearest_form_within(doc, x, doc.nodes.len())
}

/// Some ancestor of `x`, within `fuel` steps, is an HTML `datalist`.
pub open spec fn datalist_within(doc: Document, x: NodeId, fuel: nat) -> bool
    decreases fuel,
{
    match doc.nodes[x as int].parent {
        None => false,
        Some(p) => if is_html(doc, p, b"datalist"@) {
            true
        } else if fuel == 0 {
            false
        } else {
            datalist_within(doc, p, (fuel - 1) as nat)
        },
    }
}

/// "field has a `datalist` element ancestor".
pub open spec fn has_datalist_ancestor(doc: Document, x: NodeId) -> bool {
    datalist_within(doc, x, doc.nodes.len())
}

/// The first child of `f` that is an HTML `legend` element.
pub open spec fn first_legend_in(doc: Document, kids: Seq<NodeId>) -> Option<NodeId>
    decreases kids.len(),
{
    if kids.len() == 0 {
        None
    } else if is_html(doc, kids[0], b"legend"@) {
        Some(kids[0])
    } else {
        first_legend_in(doc, kids.drop_first())
    }
}

/// `fieldset` `f`'s "first `legend` element child, if any".
pub open spec fn first_legend_child(doc: Document, f: NodeId) -> Option<NodeId> {
    first_legend_in(doc, doc.nodes[f as int].children)
}

/// §4.10.18.5 "disabled", second bullet: `x` (reached from the control by
/// going up through `child`) is a descendant of a `fieldset` whose
/// `disabled` attribute is specified, and the control is not a descendant
/// of that `fieldset`'s first `legend` child (see the modelling choices:
/// the control lies under the `legend` exactly when the child of the
/// `fieldset` on its chain is the `legend`).
pub open spec fn fieldset_disables(doc: Document, child: NodeId, fuel: nat) -> bool
    decreases fuel,
{
    match doc.nodes[child as int].parent {
        None => false,
        Some(p) => if is_html(doc, p, b"fieldset"@) && has_attr(doc, p, b"disabled"@) && first_legend_child(doc, p)
            != Some(child) {
            true
        } else if fuel == 0 {
            false
        } else {
            fieldset_disables(doc, p, (fuel - 1) as nat)
        },
    }
}

/// §4.10.18.5 "A form control is disabled if any of the following are
/// true": it is a `button`, `input`, `select` or `textarea` with the
/// `disabled` attribute specified, or it is under a disabled `fieldset`.
pub open spec fn is_disabled(doc: Document, f: NodeId) -> bool {
    (is_submittable(doc, f) && has_attr(doc, f, b"disabled"@)) || fieldset_disables(doc, f, doc.nodes.len())
}

// ---------------------------------------------------------------------
// §4.10.18.3 Association of controls and forms

/// The first element in `order` whose ID is `id`.
pub open spec fn first_with_id(doc: Document, order: Seq<NodeId>, id: Seq<u32>) -> Option<NodeId>
    decreases order.len(),
{
    if order.len() == 0 {
        None
    } else if is_element(doc, order[0]) && element_id(doc, order[0]) == Some(id) {
        Some(order[0])
    } else {
        first_with_id(doc, order.drop_first(), id)
    }
}

/// HTML §4.10.18.3 "reset the form owner", steps 2 to 4: the `newForm` the
/// steps compute for form-associated element `e`.
pub open spec fn reset_form_owner_target(doc: Document, e: NodeId) -> Option<NodeId> {
    // 2. "Let newForm be null."
    // 3. "If element is listed, has a form content attribute, and is
    // connected:"
    if is_listed(doc, e) && has_attr(doc, e, b"form"@) && dom::connected(doc, e) {
        // 3.1. "If the first element in element's tree, in tree order, to
        // have an ID that is identical to element's form content
        // attribute's value, is a form element, then set newForm to that
        // form element."
        let id = attr(doc, e, b"form"@)->Some_0;
        match first_with_id(doc, tree_order(doc, root(doc, e), doc.nodes.len()), id) {
            Some(f) => if is_html(doc, f, b"form"@) {
                Some(f)
            } else {
                None
            },
            None => None,
        }
    } else {
        // 4. "Otherwise, if element has an ancestor form element, then set
        // newForm to the nearest such ancestor form element."
        nearest_form_ancestor(doc, e)
    }
    // 1., 5., 6.: "Unset element's parser inserted flag", "If element's
    // form owner is newForm, then return" and "Set element's form owner to
    // newForm" are the state change of the algorithm; the form owner it
    // leaves is newForm.
}

/// HTML §4.10.18.3 "form owner" of form-associated element `e`: the owner
/// the parser associated it with (its parser inserted flag is then set, and
/// the insertion steps leave it alone), or else the result of the insertion
/// steps' "reset the form owner".
pub open spec fn form_owner(doc: Document, e: NodeId) -> Option<NodeId> {
    match doc.nodes[e as int].kind->Element_form_owner {
        Some(f) => Some(f),
        None => reset_form_owner_target(doc, e),
    }
}

// ---------------------------------------------------------------------
// §4.10.18.1 A form control's value

/// The `textarea`'s "child text content" (DOM): the data of its `Text`
/// children, concatenated, in order.
pub open spec fn child_text(doc: Document, kids: Seq<NodeId>) -> Seq<u32>
    decreases kids.len(),
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        let k = doc.nodes[kids[0] as int].kind;
        (if k is Text {
            k->Text_data
        } else {
            Seq::empty()
        }) + child_text(doc, kids.drop_first())
    }
}

/// The `textarea` "wrap" attribute is in the Hard state (an enumerated
/// attribute; the missing and invalid value default is Soft).
pub open spec fn wrap_is_hard(doc: Document, n: NodeId) -> bool {
    match attr(doc, n, b"wrap"@) {
        Some(v) => ci_eq(v, b"hard"@),
        None => false,
    }
}

/// A `cols` attribute's "character width": the value when the rules for
/// parsing non-negative integers give a number greater than zero;
/// otherwise 20.
pub open spec fn width_of(a: Option<Seq<u32>>) -> nat {
    match a {
        Some(v) => match parse_non_negative(v) {
            Some(w) => if w > 0 {
                w
            } else {
                20
            },
            None => 20,
        },
        None => 20,
    }
}

/// The `textarea`'s "character width" (§4.10.11, `cols`).
pub open spec fn character_width(doc: Document, n: NodeId) -> nat {
    width_of(attr(doc, n, b"cols"@))
}

/// The "textarea wrapping transformation", hard state: "insert U+000A LINE
/// FEED (LF) characters into the string using an implementation-defined
/// algorithm so that each line has no more than character width
/// characters". The choice here: a line (delimited by the start, the end
/// and LF) gets an LF after every `cols` characters when more follow.
/// `col` is the number of characters on the current line so far.
pub open spec fn wrap_from(s: Seq<u32>, cols: nat, col: nat) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s[0] == 0x0A {
        seq![0x0Au32] + wrap_from(s.drop_first(), cols, 0)
    } else if col >= cols {
        seq![0x0Au32, s[0]] + wrap_from(s.drop_first(), cols, 1)
    } else {
        seq![s[0]] + wrap_from(s.drop_first(), cols, col + 1)
    }
}

/// The textarea wrapping transformation (§4.10.11), step 1.
pub open spec fn textarea_wrapping(doc: Document, n: NodeId, s: Seq<u32>) -> Seq<u32> {
    // 1. "If the element's wrap attribute is in the Hard state, insert …"
    if wrap_is_hard(doc, n) {
        wrap_from(s, character_width(doc, n), 0)
    } else {
        s
    }
}

/// The `textarea`'s "raw value": its internal value if the dirty value
/// flag is true, else its default value, the child text content.
pub open spec fn textarea_raw_value(doc: Document, st: FormState, n: NodeId) -> Seq<u32> {
    if control(st, n).dirty_value {
        control(st, n).value
    } else {
        child_text(doc, doc.nodes[n as int].children)
    }
}

/// The `textarea`'s "value": its "API value" (the raw value with newlines
/// normalized) with the textarea wrapping transformation applied.
pub open spec fn textarea_value(doc: Document, st: FormState, n: NodeId) -> Seq<u32> {
    textarea_wrapping(doc, n, normalize_newlines(textarea_raw_value(doc, st, n)))
}

/// An `input`'s "value sanitization algorithm" in each state: Text,
/// Search, Telephone and Password strip newlines; URL and Email strip
/// newlines and then leading and trailing ASCII whitespace; the others
/// (read as text) have none here.
pub open spec fn sanitize(t: InputType, v: Seq<u32>) -> Seq<u32> {
    match t {
        InputType::Text | InputType::Search | InputType::Tel | InputType::Password => strip_newlines(v),
        InputType::Url | InputType::Email => strip_whitespace(strip_newlines(v)),
        _ => v,
    }
}

/// The "value" of an `input` element (concept-fe-value). In the value
/// mode "value" it is the internal value, which mirrors the `value`
/// attribute (sanitized) while the dirty value flag is false; in the value
/// mode "default" it is the `value` attribute, or the empty string. (For
/// the "default/on" mode, Checkbox and Radio, step 5.7 reads the attribute
/// itself.)
pub open spec fn input_value(doc: Document, st: FormState, n: NodeId) -> Seq<u32> {
    let default_value = match attr(doc, n, b"value"@) {
        Some(v) => v,
        None => Seq::empty(),
    };
    match input_type(doc, n) {
        InputType::Hidden | InputType::Submit | InputType::Image | InputType::Reset | InputType::Button
        | InputType::Checkbox | InputType::Radio | InputType::File => default_value,
        t => if control(st, n).dirty_value {
            control(st, n).value
        } else {
            sanitize(t, default_value)
        },
    }
}

/// The "value" of a `button` element: its `value` attribute, or the empty
/// string.
pub open spec fn button_value(doc: Document, n: NodeId) -> Seq<u32> {
    match attr(doc, n, b"value"@) {
        Some(v) => v,
        None => Seq::empty(),
    }
}

/// The "value" of a field (concept-fe-value), for the non-`select`
/// controls.
pub open spec fn control_value(doc: Document, st: FormState, f: NodeId) -> Seq<u32> {
    if is_html(doc, f, b"textarea"@) {
        textarea_value(doc, st, f)
    } else if is_html(doc, f, b"button"@) {
        button_value(doc, f)
    } else {
        input_value(doc, st, f)
    }
}

/// "checkedness" (concept-fe-checked): while the dirty checkedness flag is
/// false it mirrors the `checked` attribute.
pub open spec fn checkedness(doc: Document, st: FormState, n: NodeId) -> bool {
    if control(st, n).dirty_checked {
        control(st, n).checked
    } else {
        has_attr(doc, n, b"checked"@)
    }
}

// ---------------------------------------------------------------------
// §4.10.7 The select element

/// §4.10.7 "list of options", steps 3.1 and 3.2 as a walk: the options
/// among the children `kids` of a node already walked into, in tree order.
/// An `option` is appended; the descendants of a `select`, `hr`, `option`,
/// `datalist`, or of an `optgroup` that has an `optgroup` ancestor in
/// between itself and the `select`, are skipped ("excluding node's
/// descendants"); `in_group` says that an `optgroup` lies between the
/// `select` and these children.
pub open spec fn options_in(doc: Document, kids: Seq<NodeId>, in_group: bool, fuel: nat) -> Seq<NodeId>
    decreases fuel, kids.len(),
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        let c = kids[0];
        let here = if is_html(doc, c, b"option"@) {
            seq![c]
        } else {
            Seq::empty()
        };
        let skip = is_html(doc, c, b"select"@) || is_html(doc, c, b"hr"@) || is_html(doc, c, b"option"@)
            || is_html(doc, c, b"datalist"@) || (is_html(doc, c, b"optgroup"@) && in_group);
        let below = if skip || fuel == 0 {
            Seq::empty()
        } else {
            options_in(
                doc,
                doc.nodes[c as int].children,
                in_group || is_html(doc, c, b"optgroup"@),
                (fuel - 1) as nat,
            )
        };
        here + below + options_in(doc, kids.drop_first(), in_group, fuel)
    }
}

/// §4.10.7 "list of options" of `select`.
pub open spec fn list_of_options(doc: Document, sel: NodeId) -> Seq<NodeId> {
    // 1. "Let options be « »." 2. "Let node be the first child of select
    // in tree order." 3. "While node is not null: …" 4. "Return options."
    options_in(doc, doc.nodes[sel as int].children, false, doc.nodes.len())
}

/// §4.10.10 "An option element option is disabled if": walking `x`'s
/// ancestors, nearest first: a `select`, `hr`, `datalist` or `option`
/// ends with false, an `optgroup` ends with whether it has `disabled`.
pub open spec fn option_ancestors_disable(doc: Document, x: NodeId, fuel: nat) -> bool
    decreases fuel,
{
    match doc.nodes[x as int].parent {
        // 3. "Return false."
        None => false,
        Some(p) => if is_html(doc, p, b"select"@) || is_html(doc, p, b"hr"@) || is_html(doc, p, b"datalist"@)
            || is_html(doc, p, b"option"@) {
            // 2.1.
            false
        } else if is_html(doc, p, b"optgroup"@) {
            // 2.2.
            has_attr(doc, p, b"disabled"@)
        } else if fuel == 0 {
            false
        } else {
            option_ancestors_disable(doc, p, (fuel - 1) as nat)
        },
    }
}

/// §4.10.10 "option is disabled".
pub open spec fn option_disabled(doc: Document, o: NodeId) -> bool {
    // 1. "If option's disabled attribute is present, then return true."
    if has_attr(doc, o, b"disabled"@) {
        true
    } else {
        // 2., 3.
        option_ancestors_disable(doc, o, doc.nodes.len())
    }
}

/// §4.10.10 "The value of an option element": its `value` attribute, if
/// there is one; otherwise its text (the table, see the modelling choices).
pub open spec fn option_value(doc: Document, st: FormState, o: NodeId) -> Seq<u32> {
    match attr(doc, o, b"value"@) {
        Some(v) => v,
        None => control(st, o).value,
    }
}

// ---------------------------------------------------------------------
// §4.10.22.4 Constructing the entry list

/// An entry: a name and a value, both scalar value strings.
pub struct Entry {
    /// "name"
    pub name: Seq<u32>,
    /// "value"
    pub value: Seq<u32>,
}

/// "create an entry" given a name and a string value (steps 1 and 2 convert
/// to a scalar value string, which these already are; the `Blob` branch is
/// out).
pub open spec fn create_entry(name: Seq<u32>, value: Seq<u32>) -> Entry {
    Entry { name, value }
}

/// The entries of the options of `select` (step 5.6): one per `option` in
/// the list of options whose selectedness is true and that is not
/// disabled, in order.
pub open spec fn option_entries(doc: Document, st: FormState, name: Seq<u32>, opts: Seq<NodeId>) -> Seq<Entry>
    decreases opts.len(),
{
    if opts.len() == 0 {
        Seq::empty()
    } else {
        let o = opts.last();
        option_entries(doc, st, name, opts.drop_last()) + if control(st, o).selected && !option_disabled(doc, o) {
            seq![create_entry(name, option_value(doc, st, o))]
        } else {
            Seq::empty()
        }
    }
}

/// Step 5, the body for one `field`: the entries it adds to the entry
/// list. `submitter` is the submitter, `encoding` the "name of encoding".
pub open spec fn field_entries(
    doc: Document,
    st: FormState,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    field: NodeId,
) -> Seq<Entry> {
    let is_input = is_html(doc, field, b"input"@);
    let t = input_type(doc, field);
    if has_datalist_ancestor(doc, field) || is_disabled(doc, field) || (is_button(doc, field) && submitter != Some(field))
        || (is_input && t is Checkbox && !checkedness(doc, st, field)) || (is_input && t is Radio && !checkedness(
        doc,
        st,
        field,
    )) {
        // 5.1. "then continue."
        Seq::empty()
    } else if is_input && t is Image {
        // 5.2.
        if submitter != Some(field) {
            // 5.2.1. "If the field element is not submitter, then continue."
            Seq::empty()
        } else {
            // 5.2.2. "If the field element has a name attribute specified
            // and its value is not the empty string, let name be that value
            // followed by U+002E (.). Otherwise, let name be the empty
            // string."
            let name = match attr(doc, field, b"name"@) {
                Some(v) => if v.len() > 0 {
                    v + seq![0x2Eu32]
                } else {
                    Seq::empty()
                },
                None => Seq::empty(),
            };
            // 5.2.3., 5.2.4. namex and namey. 5.2.5. "Let (x, y) be the
            // selected coordinate." 5.2.6., 5.2.7. the two entries, appended.
            // 5.2.8. "Continue."
            seq![
                create_entry(name + seq![0x78u32], decimal(control(st, field).x)),
                create_entry(name + seq![0x79u32], decimal(control(st, field).y)),
            ]
        }
    } else {
        // 5.3. "If the field is a form-associated custom element, …": there
        // are none. 5.4. "If either the field element does not have a name
        // attribute specified, or its name attribute's value is the empty
        // string, then continue."
        match attr(doc, field, b"name"@) {
            None => Seq::empty(),
            Some(name) => if name.len() == 0 {
                Seq::empty()
            } else {
                // 5.5. "Let name be the value of the field element's name
                // attribute."
                let main: Seq<Entry> = if is_html(doc, field, b"select"@) {
                    // 5.6.
                    option_entries(doc, st, name, list_of_options(doc, field))
                } else if is_input && (t is Checkbox || t is Radio) {
                    // 5.7. 5.7.1. "If the field element has a value attribute
                    // specified, then let value be the value of that
                    // attribute; otherwise, let value be the string "on"."
                    // 5.7.2. "Create an entry with name and value, and append
                    // it to entry list."
                    seq![create_entry(name, match attr(doc, field, b"value"@) {
                        Some(v) => v,
                        None => ascii(b"on"@),
                    })]
                } else if is_input && t is File {
                    // 5.8.: no `File` entries (see the modelling choices).
                    Seq::empty()
                } else if is_input && t is Hidden && ci_eq(name, b"_charset_"@) {
                    // 5.9. "Let charset be the name of encoding. Create an
                    // entry with name and charset, and append it to entry
                    // list."
                    seq![create_entry(name, encoding)]
                } else {
                    // 5.10. "Otherwise, create an entry with name and the
                    // value of the field element, and append it to entry
                    // list."
                    seq![create_entry(name, control_value(doc, st, field))]
                };
                // 5.11. "If the element has a dirname attribute, that
                // attribute's value is not the empty string, and the element
                // is an auto-directionality form-associated element:" 5.11.1.
                // "Let dirname be the value of the element's dirname
                // attribute." 5.11.2. "Let dir be the string "ltr" if the
                // directionality of the element is 'ltr', and "rtl"
                // otherwise": always "ltr" here. 5.11.3. "Create an entry
                // with dirname and dir, and append it to entry list."
                main + match attr(doc, field, b"dirname"@) {
                    Some(d) => if d.len() > 0 && is_auto_directionality(doc, field) {
                        seq![create_entry(d, ascii(b"ltr"@))]
                    } else {
                        Seq::empty()
                    },
                    None => Seq::empty(),
                }
            },
        }
    }
}

/// `n` is a control of `form`: a submittable element whose form owner is
/// `form`.
pub open spec fn is_control_of(doc: Document, form: NodeId, n: NodeId) -> bool {
    is_submittable(doc, n) && form_owner(doc, n) == Some(form)
}

/// The elements of `order` that are controls of `form`, in order.
pub open spec fn controls_in(doc: Document, form: NodeId, order: Seq<NodeId>) -> Seq<NodeId>
    decreases order.len(),
{
    if order.len() == 0 {
        Seq::empty()
    } else {
        controls_in(doc, form, order.drop_last()) + if is_control_of(doc, form, order.last()) {
            seq![order.last()]
        } else {
            Seq::empty()
        }
    }
}

/// Step 3: "a list of all the submittable elements whose form owner is
/// form, in tree order".
pub open spec fn controls(doc: Document, form: NodeId) -> Seq<NodeId> {
    controls_in(doc, form, tree_order(doc, root(doc, form), doc.nodes.len()))
}

/// The entries of the fields `fields`, in order (step 5, "for each element
/// field in controls, in tree order").
pub open spec fn entries_of(
    doc: Document,
    st: FormState,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    fields: Seq<NodeId>,
) -> Seq<Entry>
    decreases fields.len(),
{
    if fields.len() == 0 {
        Seq::empty()
    } else {
        entries_of(doc, st, submitter, encoding, fields.drop_last()) + field_entries(
            doc,
            st,
            submitter,
            encoding,
            fields.last(),
        )
    }
}

/// HTML §4.10.22.4 "construct the entry list" given a `form`, an optional
/// `submitter` and an `encoding`'s name; `constructing` is the form's
/// "constructing entry list" flag.
pub open spec fn construct_entry_list(
    doc: Document,
    st: FormState,
    form: NodeId,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    constructing: bool,
) -> Option<Seq<Entry>> {
    // 1. "If form's constructing entry list is true, then return null."
    if constructing {
        None
    } else {
        // 2. "Set form's constructing entry list to true." (see the
        // modelling choices) 3. "Let controls be a list of all the
        // submittable elements whose form owner is form, in tree order."
        let ctrls = controls(doc, form);
        // 4. "Let entry list be a new empty entry list." 5. the loop.
        // 6. to 8. "Let form data be a new FormData object …", "Fire an
        // event named formdata …", "Set form's constructing entry list to
        // false": skipped (see the modelling choices). 9. "Return a clone
        // of entry list."
        Some(entries_of(doc, st, submitter, encoding, ctrls))
    }
}

} // verus!
