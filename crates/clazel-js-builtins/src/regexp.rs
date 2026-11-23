//! `RegExp` (§22.2†, the object half of phase-7.md item 7.10): the
//! constructor, `RegExp.escape`, `RegExp.prototype.exec`, `test`, `toString`,
//! `compile` (Annex B §B.2.4.1†), `@@match`, `@@matchAll`, `@@replace`,
//! `@@search` and `@@split`, and `%RegExpStringIteratorPrototype%`
//! (§22.2.9†), over `clazel-js-regexp`'s parser and matcher. The String
//! methods that use a pattern are in [`crate::string`], which calls
//! [`regexp_create`] and [`is_regexp`] and delegates to the `@@` methods here.
//!
//! A regular expression literal makes its object through `%RegExp%`
//! (`Vm`'s `NewRegExp` handler, RegExpCreate §22.2.3.1†).
//!
//! # Modelling choices
//!
//! - **Internal slots.** A RegExp is a host object ([`Vm::new_host_object`])
//!   with `[[OriginalSource]]` and `[[OriginalFlags]]` as slots, and
//!   `[[RegExpMatcher]]` (with `[[RegExpRecord]]`) as the compiled
//!   `clazel_js_regexp::Program` and its [`Flags`] in its Rust value.
//! - **Indices** are code unit indices (the matcher's own), so the standard's
//!   conversions between code point indices and code unit indices
//!   (RegExpBuiltinExec §22.2.7.2† steps 12.b and 14) are the matcher's.
//! - **The matcher's limits.** The backtrack stack holds at most
//!   [`backtrack_limit`] entries; a match that needs more throws a
//!   `RangeError` (phase-7.md item 7.10's listed deviation), and the
//!   embedder's termination flag stops a match at its next check.
//!
//! # Differences from the standard, all listed
//!
//! - **The flag accessors** (`flags`, `source`, `global`, `ignoreCase`,
//!   `multiline`, `dotAll`, `unicode`, `unicodeSets`, `sticky`, `hasIndices`,
//!   §22.2.6†) are accessor properties of `RegExp.prototype`, and the VM has
//!   none. Each RegExp instance instead has them as own, non-writable,
//!   non-enumerable, configurable data properties, set by RegExpInitialize.
//!   Reading `/a/g.global` and the generic algorithms that `Get` them
//!   (`@@replace` reads `flags`) work; `RegExp.prototype.global` is
//!   `undefined` (not a getter that returns `undefined`), `RegExp.prototype.flags`
//!   is `undefined` (the standard's `""`), and `Object.getOwnPropertyNames`
//!   of a RegExp lists these names after `lastIndex`.
//! - **`get RegExp [ @@species ]`** (§22.2.5.2†) is a data property holding
//!   `%RegExp%`, as for `Promise`.
//! - **The legacy static properties** (`RegExp.$1`, `RegExp.lastMatch`, ...,
//!   the proposal "legacy RegExp features") are absent.
//! - **A match copies the input** to a `Vec<u16>`, so a loop that runs `exec`
//!   over a long string many times (`replace` with the `g` flag) is quadratic
//!   in the string's length.
//! - **Case folding and `\p{..}`** are the matcher crate's, at the Unicode
//!   version of its tables.

use crate::iterator::{code_point_at, iter_result};
use crate::string::{NamedLookup, get_substitution};
use crate::symbol::to_string_tag;
use crate::util::{
    CONFIGURABLE_ONLY, METHOD, arg, constructor, get, js_string, method, number, same_value, set,
    species_constructor, string, to_integer_or_infinity,
};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::JsString;
use clazel_js_heap::symbol as wk;
use clazel_js_heap::value::Value;
use clazel_js_regexp::{Flags, Limits, MatchError, Program};
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};
use std::sync::Arc;

/// The tag of a RegExp, and of a RegExp String Iterator.
const TAG_REGEXP: u32 = 0x5201;
const TAG_ITERATOR: u32 = 0x5202;

/// Slots of a RegExp: `[[OriginalSource]]`, `[[OriginalFlags]]`.
const S_SOURCE: usize = 0;
const S_FLAGS: usize = 1;

/// Slots of a RegExp String Iterator: the matcher, the string, `global`,
/// `unicode` and `done`.
const I_MATCHER: usize = 0;
const I_STRING: usize = 1;
const I_GLOBAL: usize = 2;
const I_UNICODE: usize = 3;
const I_DONE: usize = 4;

/// A named group of a match: its name (code units) and its capture.
type NamedCapture = (Vec<u16>, Option<(usize, usize)>);

/// `[[RegExpMatcher]]` and `[[RegExpRecord]]`.
struct Compiled {
    program: Program,
    flags: Flags,
}

/// The most entries the matcher's backtrack stack may hold.
///
/// This is the one place the embedder's `Limits::regexp_backtrack_entries`
/// (`clazel-js`, the `claude/js-limits` pull request) reaches the matcher:
/// that branch adds `Vm::regexp_backtrack_limit`, and this function is then
/// `usize::try_from(vm.regexp_backtrack_limit()).unwrap_or(usize::MAX)`. Until
/// then it is the matcher's own default, a million entries.
#[must_use]
pub fn backtrack_limit(_vm: &Vm) -> usize {
    Limits::default().max_stack
}

/// Installs `RegExp`, `RegExp.prototype` and `%RegExpStringIteratorPrototype%`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    // §22.2.6†: %RegExp.prototype% is an ordinary object (it has no
    // [[RegExpMatcher]]).
    let proto = crate::util::new_object_with(vm, object_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::RegExpPrototype, proto);
    let ctor = constructor(vm, "RegExp", 2, regexp_constructor, proto)?;
    vm.set_intrinsic(Intrinsic::RegExpConstructor, ctor);
    method(vm, ctor, "escape", 1, escape)?;
    let ks = vm.well_known_key(wk::SPECIES)?;
    vm.heap_mut().define(ctor, ks, ctor, CONFIGURABLE_ONLY)?;

    method(vm, proto, "compile", 2, compile)?;
    method(vm, proto, "exec", 1, exec)?;
    method(vm, proto, "test", 1, test)?;
    method(vm, proto, "toString", 0, to_string)?;
    let symbols: [(
        &str,
        i32,
        clazel_js_vm::interp::NativeFn,
        clazel_js_heap::symbol::SymbolId,
    ); 5] = [
        ("[Symbol.match]", 1, symbol_match, wk::MATCH),
        ("[Symbol.matchAll]", 1, symbol_match_all, wk::MATCH_ALL),
        ("[Symbol.replace]", 2, symbol_replace, wk::REPLACE),
        ("[Symbol.search]", 1, symbol_search, wk::SEARCH),
        ("[Symbol.split]", 2, symbol_split, wk::SPLIT),
    ];
    for (name, len, f, id) in symbols {
        let func = vm.new_native(name, len, f)?;
        let k = vm.well_known_key(id)?;
        vm.heap_mut().define(proto, k, func, METHOD)?;
    }

    // §22.2.9.1†: %RegExpStringIteratorPrototype% has [[Prototype]]
    // %Iterator.prototype%, `next`, and @@toStringTag "RegExp String Iterator".
    let iter_proto = vm.intrinsic(Intrinsic::IteratorPrototype);
    let rsi = crate::util::new_object_with(vm, iter_proto, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::RegExpStringIteratorPrototype, rsi);
    method(vm, rsi, "next", 0, iterator_next)?;
    to_string_tag(vm, rsi, "RegExp String Iterator")?;
    crate::util::global(vm, "RegExp", ctor)
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

fn compiled_of(vm: &Vm, v: Value) -> Option<Arc<Compiled>> {
    if vm.host_tag(v) != Some(TAG_REGEXP) {
        return None;
    }
    vm.host_data(v)?.downcast::<Compiled>().ok()
}

/// Whether `v` has a `[[RegExpMatcher]]` internal slot.
#[must_use]
pub fn has_regexp_matcher(vm: &Vm, v: Value) -> bool {
    compiled_of(vm, v).is_some()
}

/// IsRegExp ( argument ), §7.2.8†:
/// 1. If argument is not an Object, return false.
/// 2. Let matcher be ? Get(argument, @@match).
/// 3. If matcher is not undefined, return ToBoolean(matcher).
/// 4. If argument has a [[RegExpMatcher]] internal slot, return true.
/// 5. Return false.
///
/// # Errors
/// What the lookup throws.
pub fn is_regexp(vm: &mut Vm, v: Value) -> Result<bool, Abrupt> {
    if !vm.heap().is_object(v) {
        return Ok(false);
    }
    let k = vm.well_known_key(wk::MATCH)?;
    let matcher = vm.get_value(v, k)?;
    if matcher != Value::UNDEFINED {
        return Ok(vm.to_boolean(matcher));
    }
    Ok(has_regexp_matcher(vm, v))
}

/// ToLength ( argument ), §7.1.20†:
/// 1. Let len be ? ToIntegerOrInfinity(argument).
/// 2. If len ≤ 0, return +0𝔽.
/// 3. Return 𝔽(min(len, 2^53 - 1)).
fn to_length(vm: &mut Vm, v: Value) -> Result<f64, Abrupt> {
    let len = to_integer_or_infinity(vm, v)?;
    Ok(len.clamp(0.0, 9_007_199_254_740_991.0))
}

/// LengthOfArrayLike ( obj ), §7.3.19†: ToLength(? Get(obj, "length")).
fn length_of_array_like(vm: &mut Vm, o: Value) -> Result<f64, Abrupt> {
    let l = get(vm, o, "length")?;
    to_length(vm, l)
}

/// The code units of a string.
fn units_of(s: &JsString) -> Vec<u16> {
    s.units().collect()
}

fn units_value(vm: &mut Vm, units: &[u16]) -> Result<Value, Abrupt> {
    match JsString::from_units(units) {
        Ok(s) => js_string(vm, s),
        Err(_) => Err(vm.range_error("Invalid string length")),
    }
}

fn is_unit(flags: &JsString, c: u8) -> bool {
    flags.units().any(|u| u == u16::from(c))
}

/// AdvanceStringIndex ( S, index, unicode ), §22.2.7.3†:
/// 1. Assert: index ≤ 2^53 - 1.
/// 2. If unicode is false, return index + 1.
/// 3. Let length be the length of S.
/// 4. If index + 1 ≥ length, return index + 1.
/// 5. Let cp be CodePointAt(S, index).
/// 6. Return index + cp.[[CodeUnitCount]].
fn advance_string_index(s: &JsString, index: f64, unicode: bool) -> f64 {
    if !unicode {
        return index + 1.0;
    }
    if index + 1.0 >= s.len() as f64 {
        return index + 1.0;
    }
    index + code_point_at(s, index as usize).1 as f64
}

// -----------------------------------------------------------------------
// §22.2.3 Abstract operations
// -----------------------------------------------------------------------

/// RegExpAlloc ( newTarget ), §22.2.3.2†:
/// 1. Let obj be ? OrdinaryCreateFromConstructor(newTarget,
///    "%RegExp.prototype%", « [[OriginalSource]], [[OriginalFlags]],
///    [[RegExpRecord]], [[RegExpMatcher]] »).
/// 2. Perform ! DefinePropertyOrThrow(obj, "lastIndex", PropertyDescriptor {
///    [[Writable]]: true, [[Enumerable]]: false, [[Configurable]]: false }).
/// 3. Return obj.
fn regexp_alloc(vm: &mut Vm, new_target: Value) -> Result<Value, Abrupt> {
    let obj = vm.create_from_constructor(new_target, Intrinsic::RegExpPrototype, ObjKind::Plain)?;
    vm.into_host_object(
        obj,
        TAG_REGEXP,
        vec![Value::UNDEFINED, Value::UNDEFINED],
        None,
    )?;
    let k = crate::util::key(vm, "lastIndex")?;
    vm.heap_mut()
        .define(obj, k, Value::int32(0), Attrs(Attrs::WRITABLE))?;
    Ok(obj)
}

/// RegExpInitialize ( obj, pattern, flags ), §22.2.3.3†:
/// 1. If pattern is undefined, let P be the empty String.
/// 2. Else, let P be ? ToString(pattern).
/// 3. If flags is undefined, let F be the empty String.
/// 4. Else, let F be ? ToString(flags).
/// 5. If F contains any code unit other than "d", "g", "i", "m", "s", "u",
///    "v", or "y", or if F contains any code unit more than once, throw a
///    SyntaxError exception.
/// 6. If F contains "i", let i be true; else let i be false.
/// 7. If F contains "m", let m be true; else let m be false.
/// 8. If F contains "s", let s be true; else let s be false.
/// 9. If F contains "u", let u be true; else let u be false.
/// 10. If F contains "v", let v be true; else let v be false.
/// 11. If u is true or v is true, then
///     a. Let patternText be StringToCodePoints(P).
/// 12. Else,
///     a. Let patternText be the result of interpreting each of P's 16-bit
///     elements as a Unicode BMP code point.
/// 13. Let parseResult be ParsePattern(patternText, u, v).
/// 14. If parseResult is a non-empty List of SyntaxError objects, throw a
///     SyntaxError exception.
/// 15. Assert: parseResult is a Parse Node.
/// 16. Set obj.[[OriginalSource]] to P.
/// 17. Set obj.[[OriginalFlags]] to F.
/// 18. Let capturingGroupsCount be CountLeftCapturingParensWithin(parseResult).
/// 19. Let rer be the RegExp Record { [[IgnoreCase]]: i, [[Multiline]]: m,
///     [[DotAll]]: s, [[Unicode]]: u, [[UnicodeSets]]: v,
///     [[CapturingGroupsCount]]: capturingGroupsCount }.
/// 20. Set obj.[[RegExpRecord]] to rer.
/// 21. Set obj.[[RegExpMatcher]] to CompilePattern of parseResult with
///     argument rer.
/// 22. Perform ? Set(obj, "lastIndex", +0𝔽, true).
/// 23. Return obj.
///
/// (The flag properties of the module header's first difference are defined
/// between steps 21 and 22.)
fn regexp_initialize(
    vm: &mut Vm,
    obj: Value,
    pattern: Value,
    flags: Value,
) -> Result<Value, Abrupt> {
    let p = if pattern == Value::UNDEFINED {
        JsString::empty()
    } else {
        vm.to_js_string(pattern)?
    };
    let f = if flags == Value::UNDEFINED {
        JsString::empty()
    } else {
        vm.to_js_string(flags)?
    };
    let (pu, fu) = (units_of(&p), units_of(&f));
    let parsed_flags = Flags::parse(&fu).map_err(|e| {
        vm.syntax_error(&format!(
            "Invalid flags supplied to RegExp constructor '{}': {e:?}",
            f.to_string_lossy()
        ))
    })?;
    let ast = clazel_js_regexp::parse(&pu, parsed_flags).map_err(|e| {
        vm.syntax_error(&format!(
            "Invalid regular expression: /{}/: {e}",
            p.to_string_lossy()
        ))
    })?;
    let program = clazel_js_regexp::compile(&ast, parsed_flags).map_err(|e| {
        vm.syntax_error(&format!(
            "Invalid regular expression: /{}/: {e:?}",
            p.to_string_lossy()
        ))
    })?;
    if vm.host_tag(obj) != Some(TAG_REGEXP) {
        return Err(Abrupt::Internal("RegExpInitialize of a non-RegExp"));
    }
    let (pv, fv) = (js_string(vm, p)?, js_string(vm, f)?);
    vm.set_host_slot(obj, S_SOURCE, pv);
    vm.set_host_slot(obj, S_FLAGS, fv);
    vm.set_host_data(
        obj,
        Some(Arc::new(Compiled {
            program,
            flags: parsed_flags,
        })),
    );
    define_flag_properties(vm, obj, parsed_flags, &pu, &fu)?;
    set(vm, obj, "lastIndex", Value::int32(0))?;
    Ok(obj)
}

/// The module header's first difference: the accessors of §22.2.6†
/// (`get RegExp.prototype.global` ... `get RegExp.prototype.flags`, `get
/// RegExp.prototype.source`) as own data properties.
fn define_flag_properties(
    vm: &mut Vm,
    obj: Value,
    f: Flags,
    pattern: &[u16],
    flags: &[u16],
) -> Result<(), Abrupt> {
    let attrs = Attrs(Attrs::CONFIGURABLE);
    let bools = [
        ("hasIndices", f.has_indices),
        ("global", f.global),
        ("ignoreCase", f.ignore_case),
        ("multiline", f.multiline),
        ("dotAll", f.dot_all),
        ("unicode", f.unicode),
        ("unicodeSets", f.unicode_sets),
        ("sticky", f.sticky),
    ];
    for (name, on) in bools {
        let k = crate::util::key(vm, name)?;
        vm.heap_mut().define(obj, k, Value::boolean(on), attrs)?;
    }
    // §22.2.6.4† `get RegExp.prototype.flags` step 4 onwards: the flags in
    // the order of Table 70, "dgimsuvy".
    let mut text = String::new();
    for (c, on) in [
        ('d', f.has_indices),
        ('g', f.global),
        ('i', f.ignore_case),
        ('m', f.multiline),
        ('s', f.dot_all),
        ('u', f.unicode),
        ('v', f.unicode_sets),
        ('y', f.sticky),
    ] {
        if on {
            text.push(c);
        }
    }
    let _ = flags;
    let fv = string(vm, &text)?;
    let k = crate::util::key(vm, "flags")?;
    vm.heap_mut().define(obj, k, fv, attrs)?;
    let src = escape_regexp_pattern(pattern);
    let sv = units_value(vm, &src)?;
    let k = crate::util::key(vm, "source")?;
    vm.heap_mut().define(obj, k, sv, attrs)?;
    Ok(())
}

/// EscapeRegExpPattern ( P, F ), §22.2.6.13.1†: a pattern text that, in a
/// `/.../` literal, reads as `P` (the standard leaves the choice to the
/// implementation within these rules): the empty pattern is `(?:)`, a `/`
/// outside a class and every line terminator is escaped.
fn escape_regexp_pattern(p: &[u16]) -> Vec<u16> {
    if p.is_empty() {
        return "(?:)".encode_utf16().collect();
    }
    let mut out = Vec::with_capacity(p.len());
    let (mut in_class, mut escaped) = (false, false);
    for &u in p {
        let line_terminator = matches!(u, 0x0A | 0x0D | 0x2028 | 0x2029);
        if escaped {
            escaped = false;
            // `\` followed by a line terminator: the terminator in its escaped form.
            match u {
                0x0A => out.extend("n".encode_utf16()),
                0x0D => out.extend("r".encode_utf16()),
                0x2028 => out.extend("u2028".encode_utf16()),
                0x2029 => out.extend("u2029".encode_utf16()),
                _ => out.push(u),
            }
            continue;
        }
        match u {
            0x5C => {
                escaped = true;
                out.push(u);
            }
            0x5B => {
                in_class = true;
                out.push(u);
            }
            0x5D => {
                in_class = false;
                out.push(u);
            }
            0x2F if !in_class => out.extend("\\/".encode_utf16()),
            _ if line_terminator => {
                let text = match u {
                    0x0A => "\\n",
                    0x0D => "\\r",
                    0x2028 => "\\u2028",
                    _ => "\\u2029",
                };
                out.extend(text.encode_utf16());
            }
            _ => out.push(u),
        }
    }
    out
}

/// RegExpCreate ( P, F ), §22.2.3.1†:
/// 1. Let obj be ? RegExpAlloc(%RegExp%).
/// 2. Return ? RegExpInitialize(obj, P, F).
///
/// # Errors
/// A `SyntaxError` for a pattern or flags that are not valid.
pub fn regexp_create(vm: &mut Vm, p: Value, f: Value) -> Result<Value, Abrupt> {
    let ctor = vm.intrinsic(Intrinsic::RegExpConstructor);
    let obj = regexp_alloc(vm, ctor)?;
    regexp_initialize(vm, obj, p, f)
}

/// `RegExp ( pattern, flags )`, §22.2.4.1†:
/// 1. Let patternIsRegExp be ? IsRegExp(pattern).
/// 2. If NewTarget is undefined, then
///    a. Let newTarget be the active function object.
///    b. If patternIsRegExp is true and flags is undefined, then
///    i. Let patternConstructor be ? Get(pattern, "constructor").
///    ii. If SameValue(newTarget, patternConstructor) is true, return
///    pattern.
/// 3. Else, let newTarget be NewTarget.
/// 4. If pattern is an Object and pattern has a [[RegExpMatcher]] internal
///    slot, then
///    a. Let P be pattern.[[OriginalSource]].
///    b. If flags is undefined, let F be pattern.[[OriginalFlags]].
///    c. Else, let F be flags.
/// 5. Else if patternIsRegExp is true, then
///    a. Let P be ? Get(pattern, "source").
///    b. If flags is undefined, then i. Let F be ? Get(pattern, "flags").
///    c. Else, let F be flags.
/// 6. Else,
///    a. Let P be pattern.
///    b. Let F be flags.
/// 7. Let O be ? RegExpAlloc(newTarget).
/// 8. Return ? RegExpInitialize(O, P, F).
fn regexp_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (pattern, flags) = (arg(args, 0), arg(args, 1));
    let pattern_is_regexp = is_regexp(vm, pattern)?;
    let nt = vm.new_target();
    let new_target = if nt == Value::UNDEFINED {
        let active = vm.active_function();
        if pattern_is_regexp && flags == Value::UNDEFINED {
            let pc = get(vm, pattern, "constructor")?;
            if same_value(vm, active, pc) {
                return Ok(pattern);
            }
        }
        active
    } else {
        nt
    };
    let (p, f) = if let Some(c) = compiled_of(vm, pattern) {
        let _ = c;
        let p = vm.host_slot(pattern, S_SOURCE).unwrap_or(Value::UNDEFINED);
        let f = if flags == Value::UNDEFINED {
            vm.host_slot(pattern, S_FLAGS).unwrap_or(Value::UNDEFINED)
        } else {
            flags
        };
        (p, f)
    } else if pattern_is_regexp {
        let p = get(vm, pattern, "source")?;
        let f = if flags == Value::UNDEFINED {
            get(vm, pattern, "flags")?
        } else {
            flags
        };
        (p, f)
    } else {
        (pattern, flags)
    };
    let o = regexp_alloc(vm, new_target)?;
    regexp_initialize(vm, o, p, f)
}

/// `RegExp.escape ( S )`, §22.2.5.1†:
/// 1. If S is not a String, throw a TypeError exception.
/// 2. Let escaped be the empty String.
/// 3. Let cpList be StringToCodePoints(S).
/// 4. For each code point c of cpList, do
///    a. If escaped is the empty String and c is matched by either
///    DecimalDigit or AsciiLetter, then
///    i. NOTE: Escaping a leading digit ensures that output corresponds with
///    pattern text which may be used after a \0 character escape or a
///    DecimalEscape such as \1 and still match S rather than be interpreted
///    as an extension of the preceding escape sequence. Escaping a leading
///    ASCII letter does the same for the context after \c.
///    ii. Let numericValue be the numeric value of c.
///    iii. Let hex be Number::toString(𝔽(numericValue), 16).
///    iv. Assert: The length of hex is 2.
///    v. Set escaped to the string-concatenation of the code unit 0x005C
///    (REVERSE SOLIDUS), "x", and hex.
///    b. Else,
///    i. Set escaped to the string-concatenation of escaped and
///    EncodeForRegExpEscape(c).
/// 5. Return escaped.
///
/// EncodeForRegExpEscape ( c ), §22.2.5.1.1†:
/// 1. If c is matched by SyntaxCharacter or c is U+002F (SOLIDUS), then
///    a. Return the string-concatenation of 0x005C (REVERSE SOLIDUS) and
///    UTF16EncodeCodePoint(c).
/// 2. Else if c is the code point listed in some cell of the "Code Point"
///    column of Table 67 (\t \n \v \f \r), then
///    a. Return the string-concatenation of 0x005C and the string in the
///    "ControlEscape" column of the row.
/// 3. Let otherPunctuators be the string-concatenation of ",-=<>#&!%:;@~'`"
///    and the code unit 0x0022 (QUOTATION MARK).
/// 4. Let toEscape be StringToCodePoints(otherPunctuators).
/// 5. If toEscape contains c, or c is matched by either WhiteSpace or
///    LineTerminator, or c has the same numeric value as a leading surrogate
///    or trailing surrogate, then
///    a. Let cNum be the numeric value of c.
///    b. If cNum ≤ 0xFF, then i. Let hex be Number::toString(𝔽(cNum), 16).
///    ii. Return the string-concatenation of the code unit 0x005C, "x", and
///    StringPad(hex, 2, "0", start).
///    c. Let escaped be the empty String.
///    d. Let codeUnits be UTF16EncodeCodePoint(c).
///    e. For each code unit cu of codeUnits, do i. Set escaped to the
///    string-concatenation of escaped and UnicodeEscape(cu).
///    f. Return escaped.
/// 6. Return UTF16EncodeCodePoint(c).
fn escape(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let Some(s) = vm.heap().string(arg(args, 0)).cloned() else {
        return Err(vm.type_error("RegExp.escape requires a string"));
    };
    let mut out: Vec<u16> = Vec::new();
    let mut i = 0usize;
    while i < s.len() {
        let (c, count) = code_point_at(&s, i);
        i = i.saturating_add(count.max(1));
        let ascii_alnum = u8::try_from(c).is_ok_and(|b| b.is_ascii_alphanumeric());
        if out.is_empty() && ascii_alnum {
            out.extend(format!("\\x{c:02x}").encode_utf16());
            continue;
        }
        let ch = char::from_u32(c);
        if ch.is_some_and(|ch| "^$\\.*+?()[]{}|/".contains(ch)) {
            out.push(0x5C);
            out.extend(ch.into_iter().flat_map(|ch| {
                let mut b = [0u16; 2];
                ch.encode_utf16(&mut b).to_vec()
            }));
            continue;
        }
        let control = match c {
            0x09 => Some("\\t"),
            0x0A => Some("\\n"),
            0x0B => Some("\\v"),
            0x0C => Some("\\f"),
            0x0D => Some("\\r"),
            _ => None,
        };
        if let Some(t) = control {
            out.extend(t.encode_utf16());
            continue;
        }
        let other_punctuator = ch.is_some_and(|ch| ",-=<>#&!%:;@~'`\"".contains(ch));
        let space = matches!(
            c,
            0x20 | 0xA0 | 0x1680 | 0x2000
                ..=0x200A | 0x2028 | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
        );
        let surrogate = (0xD800..=0xDFFF).contains(&c);
        if other_punctuator || space || surrogate {
            if c <= 0xFF {
                out.extend(format!("\\x{c:02x}").encode_utf16());
            } else {
                for cu in s.units().skip(i.saturating_sub(count)).take(count) {
                    out.extend(format!("\\u{cu:04x}").encode_utf16());
                }
            }
            continue;
        }
        out.extend(s.units().skip(i.saturating_sub(count)).take(count));
    }
    units_value(vm, &out)
}

// -----------------------------------------------------------------------
// §22.2.7 Abstract operations for exec
// -----------------------------------------------------------------------

/// RegExpExec ( R, S ), §22.2.7.1†:
/// 1. Let exec be ? Get(R, "exec").
/// 2. If IsCallable(exec) is true, then
///    a. Let result be ? Call(exec, R, « S »).
///    b. If result is not an Object and result is not null, throw a TypeError
///    exception.
///    c. Return result.
/// 3. Perform ? RequireInternalSlot(R, [[RegExpMatcher]]).
/// 4. Return ? RegExpBuiltinExec(R, S).
fn regexp_exec(vm: &mut Vm, r: Value, s: Value) -> Result<Value, Abrupt> {
    let exec = get(vm, r, "exec")?;
    if vm.heap().is_callable(exec) {
        let result = vm.call(exec, r, &[s])?;
        if !vm.heap().is_object(result) && result != Value::NULL {
            return Err(
                vm.type_error("RegExp exec method returned something other than an Object or null")
            );
        }
        return Ok(result);
    }
    if !has_regexp_matcher(vm, r) {
        return Err(vm.type_error("RegExp.prototype method called on an incompatible receiver"));
    }
    regexp_builtin_exec(vm, r, s)
}

/// RegExpBuiltinExec ( R, S ), §22.2.7.2†:
/// 1. Let length be the length of S.
/// 2. Let lastIndex be ℝ(? ToLength(? Get(R, "lastIndex"))).
/// 3. Let flags be R.[[OriginalFlags]].
/// 4. If flags contains "g", let global be true; else let global be false.
/// 5. If flags contains "y", let sticky be true; else let sticky be false.
/// 6. If flags contains "d", let hasIndices be true; else let hasIndices be
///    false.
/// 7. If global is false and sticky is false, set lastIndex to 0.
/// 8. Let matcher be R.[[RegExpMatcher]].
/// 9. If flags contains "u" or flags contains "v", let fullUnicode be true;
///    else let fullUnicode be false.
/// 10. Let matchSucceeded be false.
/// 11. If fullUnicode is true, let input be StringToCodePoints(S);
///     otherwise, let input be a List whose elements are the code units that
///     are the elements of S.
/// 12. NOTE: Each element of input is considered to be a character.
/// 13. Repeat, while matchSucceeded is false,
///     a. If lastIndex > length, then
///     i. If global is true or sticky is true, then 1. Perform ? Set(R,
///     "lastIndex", +0𝔽, true).
///     ii. Return null.
///     b. Let inputIndex be the index into input of the character that was
///     obtained from element lastIndex of S.
///     c. Let r be matcher(input, inputIndex).
///     d. If r is failure, then
///     i. If sticky is true, then 1. Perform ? Set(R, "lastIndex", +0𝔽,
///     true). 2. Return null.
///     ii. Set lastIndex to AdvanceStringIndex(S, lastIndex, fullUnicode).
///     e. Else, i. Assert: r is a MatchState. ii. Set matchSucceeded to true.
/// 14. Let e be r.[[EndIndex]].
/// 15. If fullUnicode is true, set e to GetStringIndex(S, e).
/// 16. If global is true or sticky is true, then
///     a. Perform ? Set(R, "lastIndex", 𝔽(e), true).
/// 17. Let n be the number of elements in r.[[Captures]].
/// 18. Assert: n = R.[[RegExpRecord]].[[CapturingGroupsCount]].
/// 19. Assert: n < 2^32 - 1.
/// 20. Let A be ! ArrayCreate(n + 1).
/// 21. Assert: The mathematical value of A's "length" property is n + 1.
/// 22. Perform ! CreateDataPropertyOrThrow(A, "index", 𝔽(lastIndex)).
/// 23. Perform ! CreateDataPropertyOrThrow(A, "input", S).
/// 24. Let match be the Match Record { [[StartIndex]]: lastIndex,
///     [[EndIndex]]: e }.
/// 25. Let indices be a new empty List.
/// 26. Let groupNames be a new empty List.
/// 27. Append match to indices.
/// 28. Let matchedSubstr be GetMatchString(S, match).
/// 29. Perform ! CreateDataPropertyOrThrow(A, "0", matchedSubstr).
/// 30. If R contains any GroupName, then
///     a. Let groups be OrdinaryObjectCreate(null).
///     b. Let hasGroups be true.
/// 31. Else,
///     a. Let groups be undefined.
///     b. Let hasGroups be false.
/// 32. Perform ! CreateDataPropertyOrThrow(A, "groups", groups).
/// 33. For each integer i such that 1 ≤ i ≤ n, in ascending order, do
///     a. Let captureI be ith element of r.[[Captures]].
///     b. If captureI is undefined, then i. Let capturedValue be undefined.
///     ii. Append undefined to indices.
///     c. Else, i. Let captureStart be captureI.[[StartIndex]]. ii. Let
///     captureEnd be captureI.[[EndIndex]]. iii. If fullUnicode is true,
///     then ... (the matcher's indices are code unit indices already).
///     iv. Let capture be the Match Record { [[StartIndex]]: captureStart,
///     [[EndIndex]]: captureEnd }. v. Let capturedValue be
///     GetMatchString(S, capture). vi. Append capture to indices.
///     d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)),
///     capturedValue).
///     e. If the ith capture of R was defined with a GroupName, then
///     i. Let s be the CapturingGroupName of that GroupName.
///     ii. If matchedGroupNames contains s, then 1. Assert: capturedValue is
///     undefined. 2. Append undefined to groupNames.
///     iii. Else, 1. If capturedValue is not undefined, append s to
///     matchedGroupNames. 2. NOTE: If there are multiple groups named s,
///     groups may already have an s property at this point. However, because
///     groups is an ordinary object whose properties are all writable data
///     properties, the call to CreateDataPropertyOrThrow is nevertheless
///     guaranteed to succeed. 3. Perform ! CreateDataPropertyOrThrow(groups,
///     s, capturedValue). 4. Append s to groupNames.
/// 34. If hasIndices is true, then
///     a. Let indicesArray be MakeMatchIndicesIndexPairArray(S, indices,
///     groupNames, hasGroups).
///     b. Perform ! CreateDataPropertyOrThrow(A, "indices", indicesArray).
/// 35. Return A.
fn regexp_builtin_exec(vm: &mut Vm, r: Value, sv: Value) -> Result<Value, Abrupt> {
    let Some(compiled) = compiled_of(vm, r) else {
        return Err(vm.type_error("RegExp.prototype.exec called on an incompatible receiver"));
    };
    let Some(s) = vm.heap().string(sv).cloned() else {
        return Err(Abrupt::Internal("RegExpBuiltinExec of a non-string"));
    };
    let length = s.len() as f64;
    let li = get(vm, r, "lastIndex")?;
    let mut last_index = to_length(vm, li)?;
    let f = compiled.flags;
    let (global, sticky) = (f.global, f.sticky);
    if !global && !sticky {
        last_index = 0.0;
    }
    if last_index > length {
        if global || sticky {
            set(vm, r, "lastIndex", Value::int32(0))?;
        }
        return Ok(Value::NULL);
    }
    let input = units_of(&s);
    let limits = Limits {
        max_stack: backtrack_limit(vm),
        max_steps: None,
    };
    let terminator = vm.terminator();
    let mut hook = move || terminator.is_set();
    let outcome = compiled.program.exec(
        &input,
        last_index as usize,
        sticky,
        &limits,
        Some(&mut hook),
    );
    let m = match outcome {
        Ok(Some(m)) => m,
        Ok(None) => {
            // Steps 13.a.i and 13.d.i: the match failed at every index the
            // loop would have tried (for `y`, at `lastIndex` alone).
            if global || sticky {
                set(vm, r, "lastIndex", Value::int32(0))?;
            }
            return Ok(Value::NULL);
        }
        Err(MatchError::StackOverflow) => {
            return Err(vm.range_error("Maximum regular expression backtracking depth exceeded"));
        }
        Err(MatchError::Interrupted | MatchError::StepLimit) => return Err(Abrupt::Terminated),
        Err(MatchError::Corrupt) => return Err(Abrupt::Internal("malformed regular expression")),
    };
    let (start, end) = m.get(0).ok_or(Abrupt::Internal("match without a match"))?;
    if global || sticky {
        set(vm, r, "lastIndex", number(end as f64))?;
    }
    let a = vm.array_create(m.captures.len() as f64, None)?;
    let create = |vm: &mut Vm, name: &str, v: Value| -> Result<(), Abrupt> {
        let k = crate::util::key(vm, name)?;
        vm.create_data_property_or_throw(a, k, v)
    };
    create(vm, "index", number(start as f64))?;
    create(vm, "input", sv)?;
    let piece = |vm: &mut Vm, c: Option<(usize, usize)>| -> Result<Value, Abrupt> {
        match c {
            Some((x, y)) => js_string(vm, s.substring(x, y)),
            None => Ok(Value::UNDEFINED),
        }
    };
    let matched = piece(vm, Some((start, end)))?;
    create(vm, "0", matched)?;
    let names = compiled.program.group_names();
    let has_groups = !names.is_empty();
    let groups = if has_groups {
        crate::util::new_object_with(vm, Value::NULL, ObjKind::Plain)?
    } else {
        Value::UNDEFINED
    };
    create(vm, "groups", groups)?;
    let mut indices: Vec<Option<(usize, usize)>> = vec![Some((start, end))];
    for i in 1..m.captures.len() {
        vm.charge_step()?;
        let cap = m.get(i);
        indices.push(cap);
        let v = piece(vm, cap)?;
        create(vm, &i.to_string(), v)?;
    }
    // Step 33.e: the named groups, in the order of the groups.
    let mut named: Vec<NamedCapture> = Vec::new();
    for (name, number_of) in names {
        let n16 = code_points_to_units(name);
        let idx = usize::try_from(*number_of).unwrap_or(usize::MAX);
        let cap = m.get(idx);
        let captured = piece(vm, cap)?;
        let key = vm
            .heap_mut()
            .intern(&JsString::from_units(&n16).map_err(|_| Abrupt::OutOfMemory)?)?;
        let exists = vm.heap().find(groups, key)?.is_some_and(|f| f.own);
        if cap.is_some() || !exists {
            vm.create_data_property_or_throw(groups, key, captured)?;
        }
        named.push((n16, cap));
    }
    if f.has_indices {
        let ia = make_match_indices_index_pair_array(vm, &indices, &named, has_groups)?;
        create(vm, "indices", ia)?;
    }
    Ok(a)
}

fn code_points_to_units(cps: &[u32]) -> Vec<u16> {
    let mut out = Vec::with_capacity(cps.len());
    for &c in cps {
        match char::from_u32(c) {
            Some(ch) => {
                let mut b = [0u16; 2];
                out.extend_from_slice(ch.encode_utf16(&mut b));
            }
            None => out.push(u16::try_from(c).unwrap_or(0xFFFD)),
        }
    }
    out
}

/// MakeMatchIndicesIndexPairArray ( S, indices, groupNames, hasGroups ),
/// §22.2.7.8†:
/// 1. Let n be the number of elements in indices.
/// 2. Assert: n < 2^32 - 1.
/// 3. Assert: groupNames has n - 1 elements.
/// 4. NOTE: The groupNames List contains elements aligned with the indices
///    List starting at indices[1].
/// 5. Let A be ! ArrayCreate(n).
/// 6. If hasGroups is true, then a. Let groups be OrdinaryObjectCreate(null).
/// 7. Else, a. Let groups be undefined.
/// 8. Perform ! CreateDataPropertyOrThrow(A, "groups", groups).
/// 9. For each integer i such that 0 ≤ i < n, in ascending order, do
///    a. Let matchIndices be indices[i].
///    b. If matchIndices is not undefined, then i. Let matchIndexPair be
///    GetMatchIndexPair(S, matchIndices).
///    c. Else, i. Let matchIndexPair be undefined.
///    d. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(i)),
///    matchIndexPair).
///    e. If i > 0 and groupNames[i - 1] is not undefined, then i. Assert:
///    groups is not undefined. ii. Perform ! CreateDataPropertyOrThrow(groups,
///    groupNames[i - 1], matchIndexPair).
/// 10. Return A.
fn make_match_indices_index_pair_array(
    vm: &mut Vm,
    indices: &[Option<(usize, usize)>],
    named: &[NamedCapture],
    has_groups: bool,
) -> Result<Value, Abrupt> {
    let a = vm.array_create(indices.len() as f64, None)?;
    let groups = if has_groups {
        crate::util::new_object_with(vm, Value::NULL, ObjKind::Plain)?
    } else {
        Value::UNDEFINED
    };
    let kg = crate::util::key(vm, "groups")?;
    vm.create_data_property_or_throw(a, kg, groups)?;
    let pair = |vm: &mut Vm, p: Option<(usize, usize)>| -> Result<Value, Abrupt> {
        match p {
            Some((x, y)) => vm.create_array_from_list(&[number(x as f64), number(y as f64)]),
            None => Ok(Value::UNDEFINED),
        }
    };
    for (i, p) in indices.iter().enumerate() {
        let v = pair(vm, *p)?;
        let k = vm.index_key(i as u64)?;
        vm.create_data_property_or_throw(a, k, v)?;
    }
    for (name, p) in named {
        let v = pair(vm, *p)?;
        let key = vm
            .heap_mut()
            .intern(&JsString::from_units(name).map_err(|_| Abrupt::OutOfMemory)?)?;
        let exists = vm.heap().find(groups, key)?.is_some_and(|f| f.own);
        if p.is_some() || !exists {
            vm.create_data_property_or_throw(groups, key, v)?;
        }
    }
    Ok(a)
}

// -----------------------------------------------------------------------
// §22.2.6 Properties of the RegExp prototype
// -----------------------------------------------------------------------

/// `RegExp.prototype.exec ( string )`, §22.2.6.2†:
/// 1. Let R be the this value.
/// 2. Perform ? RequireInternalSlot(R, [[RegExpMatcher]]).
/// 3. Let S be ? ToString(string).
/// 4. Return ? RegExpBuiltinExec(R, S).
fn exec(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !has_regexp_matcher(vm, this) {
        return Err(vm.type_error("RegExp.prototype.exec called on an incompatible receiver"));
    }
    let s = to_string_value(vm, arg(args, 0))?;
    regexp_builtin_exec(vm, this, s)
}

/// ToString as a string value.
fn to_string_value(vm: &mut Vm, v: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_string(v) {
        return Ok(v);
    }
    let s = vm.to_js_string(v)?;
    js_string(vm, s)
}

/// `RegExp.prototype.test ( S )`, §22.2.6.16†:
/// 1. Let R be the this value.
/// 2. If R is not an Object, throw a TypeError exception.
/// 3. Let string be ? ToString(S).
/// 4. Let match be ? RegExpExec(R, string).
/// 5. If match is not null, return true; else return false.
fn test(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype.test")?;
    let s = to_string_value(vm, arg(args, 0))?;
    let m = regexp_exec(vm, this, s)?;
    Ok(Value::boolean(m != Value::NULL))
}

fn require_object(vm: &mut Vm, v: Value, what: &str) -> Result<(), Abrupt> {
    if vm.heap().is_object(v) {
        Ok(())
    } else {
        Err(vm.type_error(&format!("{what} called on a non-object")))
    }
}

/// `RegExp.prototype.toString ( )`, §22.2.6.17†:
/// 1. Let R be the this value.
/// 2. If R is not an Object, throw a TypeError exception.
/// 3. Let pattern be ? ToString(? Get(R, "source")).
/// 4. Let flags be ? ToString(? Get(R, "flags")).
/// 5. Let result be the string-concatenation of "/", pattern, "/", and flags.
/// 6. Return result.
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype.toString")?;
    let sv = get(vm, this, "source")?;
    let pattern = vm.to_js_string(sv)?;
    let fv = get(vm, this, "flags")?;
    let flags = vm.to_js_string(fv)?;
    let mut out: Vec<u16> = vec![0x2F];
    out.extend(pattern.units());
    out.push(0x2F);
    out.extend(flags.units());
    units_value(vm, &out)
}

/// `RegExp.prototype.compile ( pattern, flags )`, §B.2.4.1†:
/// 1. Let O be the this value.
/// 2. Perform ? RequireInternalSlot(O, [[RegExpMatcher]]).
/// 3. If pattern is an Object and pattern has a [[RegExpMatcher]] internal
///    slot, then
///    a. If flags is not undefined, throw a TypeError exception.
///    b. Let P be pattern.[[OriginalSource]].
///    c. Let F be pattern.[[OriginalFlags]].
/// 4. Else,
///    a. Let P be pattern.
///    b. Let F be flags.
/// 5. Return ? RegExpInitialize(O, P, F).
fn compile(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if !has_regexp_matcher(vm, this) {
        return Err(vm.type_error("RegExp.prototype.compile called on an incompatible receiver"));
    }
    let (pattern, flags) = (arg(args, 0), arg(args, 1));
    let (p, f) = if has_regexp_matcher(vm, pattern) {
        if flags != Value::UNDEFINED {
            return Err(vm.type_error("flags must be undefined when the pattern is a RegExp"));
        }
        (
            vm.host_slot(pattern, S_SOURCE).unwrap_or(Value::UNDEFINED),
            vm.host_slot(pattern, S_FLAGS).unwrap_or(Value::UNDEFINED),
        )
    } else {
        (pattern, flags)
    };
    regexp_initialize(vm, this, p, f)
}

/// `RegExp.prototype [ @@match ] ( string )`, §22.2.6.8†:
/// 1. Let rx be the this value.
/// 2. If rx is not an Object, throw a TypeError exception.
/// 3. Let S be ? ToString(string).
/// 4. Let flags be ? ToString(? Get(rx, "flags")).
/// 5. If flags does not contain "g", then
///    a. Return ? RegExpExec(rx, S).
/// 6. Else,
///    a. If flags contains "u" or flags contains "v", let fullUnicode be
///    true; else let fullUnicode be false.
///    b. Perform ? Set(rx, "lastIndex", +0𝔽, true).
///    c. Let A be ! ArrayCreate(0).
///    d. Let n be 0.
///    e. Repeat,
///    i. Let result be ? RegExpExec(rx, S).
///    ii. If result is null, then 1. If n = 0, return null. 2. Return A.
///    iii. Else, 1. Let matchStr be ? ToString(? Get(result, "0")).
///    2. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(n)), matchStr).
///    3. If matchStr is the empty String, then a. Let thisIndex be
///    ℝ(? ToLength(? Get(rx, "lastIndex"))). b. Let nextIndex be
///    AdvanceStringIndex(S, thisIndex, fullUnicode). c. Perform ? Set(rx,
///    "lastIndex", 𝔽(nextIndex), true).
///    4. Set n to n + 1.
fn symbol_match(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype[@@match]")?;
    let sv = to_string_value(vm, arg(args, 0))?;
    let s = string_of(vm, sv)?;
    let flags = flags_of(vm, this)?;
    if !is_unit(&flags, b'g') {
        return regexp_exec(vm, this, sv);
    }
    let full_unicode = is_unit(&flags, b'u') || is_unit(&flags, b'v');
    set(vm, this, "lastIndex", Value::int32(0))?;
    let mut out: Vec<Value> = Vec::new();
    loop {
        vm.charge_step()?;
        let result = regexp_exec(vm, this, sv)?;
        if result == Value::NULL {
            if out.is_empty() {
                return Ok(Value::NULL);
            }
            return vm.create_array_from_list(&out);
        }
        let m0 = get(vm, result, "0")?;
        let match_str = vm.to_js_string(m0)?;
        let empty = match_str.is_empty();
        out.push(js_string(vm, match_str)?);
        if empty {
            advance_last_index(vm, this, &s, full_unicode)?;
        }
    }
}

/// The steps "Let thisIndex be ℝ(? ToLength(? Get(rx, "lastIndex"))). Let
/// nextIndex be AdvanceStringIndex(S, thisIndex, fullUnicode). Perform ?
/// Set(rx, "lastIndex", 𝔽(nextIndex), true)."
fn advance_last_index(
    vm: &mut Vm,
    rx: Value,
    s: &JsString,
    full_unicode: bool,
) -> Result<(), Abrupt> {
    let li = get(vm, rx, "lastIndex")?;
    let this_index = to_length(vm, li)?;
    let next = advance_string_index(s, this_index, full_unicode);
    set(vm, rx, "lastIndex", number(next))
}

fn string_of(vm: &Vm, sv: Value) -> Result<JsString, Abrupt> {
    vm.heap()
        .string(sv)
        .cloned()
        .ok_or(Abrupt::Internal("not a string"))
}

/// `? ToString(? Get(rx, "flags"))`.
fn flags_of(vm: &mut Vm, rx: Value) -> Result<JsString, Abrupt> {
    let f = get(vm, rx, "flags")?;
    vm.to_js_string(f)
}

/// `RegExp.prototype [ @@matchAll ] ( string )`, §22.2.6.9†:
/// 1. Let R be the this value.
/// 2. If R is not an Object, throw a TypeError exception.
/// 3. Let S be ? ToString(string).
/// 4. Let C be ? SpeciesConstructor(R, %RegExp%).
/// 5. Let flags be ? ToString(? Get(R, "flags")).
/// 6. Let matcher be ? Construct(C, « R, flags »).
/// 7. Let lastIndex be ? ToLength(? Get(R, "lastIndex")).
/// 8. Perform ? Set(matcher, "lastIndex", lastIndex, true).
/// 9. If flags contains "g", let global be true.
/// 10. Else, let global be false.
/// 11. If flags contains "u" or flags contains "v", let fullUnicode be true.
/// 12. Else, let fullUnicode be false.
/// 13. Return CreateRegExpStringIterator(matcher, S, global, fullUnicode).
///
/// CreateRegExpStringIterator ( R, S, global, fullUnicode ), §22.2.9.1†: an
/// iterator whose `next` is one step of the closure there.
fn symbol_match_all(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype[@@matchAll]")?;
    let sv = to_string_value(vm, arg(args, 0))?;
    let default = vm.intrinsic(Intrinsic::RegExpConstructor);
    let c = species_constructor(vm, this, default)?;
    let flags = flags_of(vm, this)?;
    let fv = js_string(vm, flags.clone())?;
    let matcher = vm.construct_value(c, &[this, fv])?;
    let li = get(vm, this, "lastIndex")?;
    let last_index = to_length(vm, li)?;
    set(vm, matcher, "lastIndex", number(last_index))?;
    let global = is_unit(&flags, b'g');
    let full_unicode = is_unit(&flags, b'u') || is_unit(&flags, b'v');
    let proto = vm.intrinsic(Intrinsic::RegExpStringIteratorPrototype);
    vm.new_host_object(
        proto,
        TAG_ITERATOR,
        vec![
            matcher,
            sv,
            Value::boolean(global),
            Value::boolean(full_unicode),
            Value::FALSE,
        ],
        None,
    )
}

/// `%RegExpStringIteratorPrototype%.next ( )`, §22.2.9.2.1†:
/// GeneratorResume(this value, empty, "%RegExpStringIteratorPrototype%") (a
/// TypeError if the this value is not a RegExp String Iterator), then one
/// step of the closure of CreateRegExpStringIterator, §22.2.9.1† step 1:
/// a. Repeat, i. Let match be ? RegExpExec(R, S).
///    ii. If match is null, return undefined (done).
///    iii. If global is false, then 1. Perform ? GeneratorYield(match).
///    2. Return undefined (done).
///    iv. Let matchStr be ? ToString(? Get(match, "0")).
///    v. If matchStr is the empty String, then 1. Let thisIndex be
///    ℝ(? ToLength(? Get(R, "lastIndex"))). 2. Let nextIndex be
///    AdvanceStringIndex(S, thisIndex, fullUnicode). 3. Perform ? Set(R,
///    "lastIndex", 𝔽(nextIndex), true).
///    vi. Perform ? GeneratorYield(match).
fn iterator_next(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    if vm.host_tag(this) != Some(TAG_ITERATOR) {
        return Err(vm.type_error("next called on an object that is not a RegExp String Iterator"));
    }
    let slot = |vm: &Vm, i: usize| {
        vm.host_slot(this, i)
            .ok_or(Abrupt::Internal("iterator slot"))
    };
    if slot(vm, I_DONE)? == Value::TRUE {
        return iter_result(vm, Value::UNDEFINED, true);
    }
    let (r, sv) = (slot(vm, I_MATCHER)?, slot(vm, I_STRING)?);
    let (global, full_unicode) = (
        slot(vm, I_GLOBAL)? == Value::TRUE,
        slot(vm, I_UNICODE)? == Value::TRUE,
    );
    let done = |vm: &mut Vm| -> Result<Value, Abrupt> {
        vm.set_host_slot(this, I_DONE, Value::TRUE);
        iter_result(vm, Value::UNDEFINED, true)
    };
    let step = (|| -> Result<Value, Abrupt> {
        let m = regexp_exec(vm, r, sv)?;
        if m == Value::NULL {
            return done(vm);
        }
        if !global {
            vm.set_host_slot(this, I_DONE, Value::TRUE);
            return iter_result(vm, m, false);
        }
        let m0 = get(vm, m, "0")?;
        let match_str = vm.to_js_string(m0)?;
        if match_str.is_empty() {
            let s = string_of(vm, sv)?;
            advance_last_index(vm, r, &s, full_unicode)?;
        }
        iter_result(vm, m, false)
    })();
    // An abrupt step leaves a generator finished.
    if step.is_err() {
        vm.set_host_slot(this, I_DONE, Value::TRUE);
    }
    step
}

/// `RegExp.prototype [ @@replace ] ( string, replaceValue )`, §22.2.6.11†:
/// 1. Let rx be the this value.
/// 2. If rx is not an Object, throw a TypeError exception.
/// 3. Let S be ? ToString(string).
/// 4. Let lengthS be the length of S.
/// 5. Let functionalReplace be IsCallable(replaceValue).
/// 6. If functionalReplace is false, then
///    a. Set replaceValue to ? ToString(replaceValue).
/// 7. Let flags be ? ToString(? Get(rx, "flags")).
/// 8. If flags contains "g", let global be true. Otherwise, let global be
///    false.
/// 9. If global is true, then
///    a. If flags contains "u" or flags contains "v", let fullUnicode be
///    true. Otherwise, let fullUnicode be false.
///    b. Perform ? Set(rx, "lastIndex", +0𝔽, true).
/// 10. Let results be a new empty List.
/// 11. Let done be false.
/// 12. Repeat, while done is false,
///     a. Let result be ? RegExpExec(rx, S).
///     b. If result is null, then i. Set done to true.
///     c. Else, i. Append result to results.
///     ii. If global is false, then 1. Set done to true.
///     iii. Else, 1. Let matchStr be ? ToString(? Get(result, "0")).
///     2. If matchStr is the empty String, then a. Let thisIndex be
///     ℝ(? ToLength(? Get(rx, "lastIndex"))). b. Let nextIndex be
///     AdvanceStringIndex(S, thisIndex, fullUnicode). c. Perform ? Set(rx,
///     "lastIndex", 𝔽(nextIndex), true).
/// 13. Let accumulatedResult be the empty String.
/// 14. Let nextSourcePosition be 0.
/// 15. For each element result of results, do
///     a. Let resultLength be ? LengthOfArrayLike(result).
///     b. Let nCaptures be max(resultLength - 1, 0).
///     c. Let matched be ? ToString(? Get(result, "0")).
///     d. Let matchLength be the length of matched.
///     e. Let position be ? ToIntegerOrInfinity(? Get(result, "index")).
///     f. Set position to the result of clamping position between 0 and
///     lengthS.
///     g. Let captures be a new empty List.
///     h. Let n be 1.
///     i. Repeat, while n ≤ nCaptures,
///     i. Let capN be ? Get(result, ! ToString(𝔽(n))).
///     ii. If capN is not undefined, then 1. Set capN to ? ToString(capN).
///     iii. Append capN to captures.
///     iv. NOTE: When n = 1, the preceding step puts the first element into
///     captures (at index 0). More generally, the nth capture (the
///     characters captured by the nth set of capturing parentheses) is at
///     captures[n - 1].
///     v. Set n to n + 1.
///     j. Let namedCaptures be ? Get(result, "groups").
///     k. If functionalReplace is true, then
///     i. Let replacerArgs be the list-concatenation of « matched », captures,
///     and « 𝔽(position), S ».
///     ii. If namedCaptures is not undefined, then 1. Append namedCaptures to
///     replacerArgs.
///     iii. Let replValue be ? Call(replaceValue, undefined, replacerArgs).
///     iv. Let replacement be ? ToString(replValue).
///     l. Else,
///     i. If namedCaptures is not undefined, then 1. Set namedCaptures to ?
///     ToObject(namedCaptures).
///     ii. Let replacement be ? GetSubstitution(matched, S, position,
///     captures, namedCaptures, replaceValue).
///     m. If position ≥ nextSourcePosition, then
///     i. NOTE: position should not normally move backwards. If it does, it
///     is an indication of an ill-behaving RegExp subclass or use of an
///     access triggered side-effect to change the global flag or other
///     characteristics of rx. In such cases, the corresponding substitution
///     is ignored.
///     ii. Set accumulatedResult to the string-concatenation of
///     accumulatedResult, the substring of S from nextSourcePosition to
///     position, and replacement.
///     iii. Set nextSourcePosition to position + matchLength.
/// 16. If nextSourcePosition ≥ lengthS, return accumulatedResult.
/// 17. Return the string-concatenation of accumulatedResult and the substring
///     of S from nextSourcePosition.
fn symbol_replace(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype[@@replace]")?;
    let sv = to_string_value(vm, arg(args, 0))?;
    let s = string_of(vm, sv)?;
    let su = units_of(&s);
    let length_s = su.len();
    let mut replace_value = arg(args, 1);
    let functional = vm.heap().is_callable(replace_value);
    if !functional {
        replace_value = to_string_value(vm, replace_value)?;
    }
    let flags = flags_of(vm, this)?;
    let global = is_unit(&flags, b'g');
    let mut full_unicode = false;
    if global {
        full_unicode = is_unit(&flags, b'u') || is_unit(&flags, b'v');
        set(vm, this, "lastIndex", Value::int32(0))?;
    }
    let mut results: Vec<Value> = Vec::new();
    loop {
        vm.charge_step()?;
        let result = regexp_exec(vm, this, sv)?;
        if result == Value::NULL {
            break;
        }
        results.push(result);
        if !global {
            break;
        }
        let m0 = get(vm, result, "0")?;
        let match_str = vm.to_js_string(m0)?;
        if match_str.is_empty() {
            advance_last_index(vm, this, &s, full_unicode)?;
        }
    }
    let template = if functional {
        Vec::new()
    } else {
        units_of(&string_of(vm, replace_value)?)
    };
    let mut accumulated: Vec<u16> = Vec::new();
    let mut next_source_position = 0usize;
    for result in results {
        vm.charge_step()?;
        let result_length = length_of_array_like(vm, result)?;
        let n_captures = (result_length - 1.0).max(0.0) as usize;
        let m0 = get(vm, result, "0")?;
        let matched = units_of(&vm.to_js_string(m0)?);
        let pv = get(vm, result, "index")?;
        let position = to_integer_or_infinity(vm, pv)?.clamp(0.0, length_s as f64) as usize;
        let mut captures: Vec<Option<Vec<u16>>> = Vec::new();
        for n in 1..=n_captures {
            let k = vm.index_key(n as u64)?;
            let cap = vm.get_value(result, k)?;
            captures.push(if cap == Value::UNDEFINED {
                None
            } else {
                Some(units_of(&vm.to_js_string(cap)?))
            });
        }
        let mut named_captures = get(vm, result, "groups")?;
        let replacement: Vec<u16> = if functional {
            let mut replacer_args: Vec<Value> = Vec::new();
            replacer_args.push(units_value(vm, &matched)?);
            for c in &captures {
                replacer_args.push(match c {
                    Some(u) => units_value(vm, u)?,
                    None => Value::UNDEFINED,
                });
            }
            replacer_args.push(number(position as f64));
            replacer_args.push(sv);
            if named_captures != Value::UNDEFINED {
                replacer_args.push(named_captures);
            }
            let repl_value = vm.call(replace_value, Value::UNDEFINED, &replacer_args)?;
            units_of(&vm.to_js_string(repl_value)?)
        } else {
            if named_captures != Value::UNDEFINED {
                named_captures = vm.to_object(named_captures)?;
            }
            let mut lookup = |vm_name: &[u16]| -> Result<Vec<u16>, Abrupt> {
                let key = vm
                    .heap_mut()
                    .intern(&JsString::from_units(vm_name).map_err(|_| Abrupt::OutOfMemory)?)?;
                let cap = vm.get_value(named_captures, key)?;
                if cap == Value::UNDEFINED {
                    Ok(Vec::new())
                } else {
                    Ok(units_of(&vm.to_js_string(cap)?))
                }
            };
            let named: Option<NamedLookup<'_>> = if named_captures == Value::UNDEFINED {
                None
            } else {
                Some(&mut lookup)
            };
            get_substitution(&matched, &su, position, &captures, named, &template)?
        };
        if position >= next_source_position {
            accumulated.extend_from_slice(su.get(next_source_position..position).unwrap_or(&[]));
            accumulated.extend(replacement);
            next_source_position = position.saturating_add(matched.len());
        }
    }
    if next_source_position < length_s {
        accumulated.extend_from_slice(su.get(next_source_position..).unwrap_or(&[]));
    }
    units_value(vm, &accumulated)
}

/// `RegExp.prototype [ @@search ] ( string )`, §22.2.6.12†:
/// 1. Let rx be the this value.
/// 2. If rx is not an Object, throw a TypeError exception.
/// 3. Let S be ? ToString(string).
/// 4. Let previousLastIndex be ? Get(rx, "lastIndex").
/// 5. If SameValue(previousLastIndex, +0𝔽) is false, then
///    a. Perform ? Set(rx, "lastIndex", +0𝔽, true).
/// 6. Let result be ? RegExpExec(rx, S).
/// 7. Let currentLastIndex be ? Get(rx, "lastIndex").
/// 8. If SameValue(currentLastIndex, previousLastIndex) is false, then
///    a. Perform ? Set(rx, "lastIndex", previousLastIndex, true).
/// 9. If result is null, return -1𝔽.
/// 10. Return ? Get(result, "index").
fn symbol_search(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype[@@search]")?;
    let sv = to_string_value(vm, arg(args, 0))?;
    let previous = get(vm, this, "lastIndex")?;
    if !same_value(vm, previous, Value::int32(0)) {
        set(vm, this, "lastIndex", Value::int32(0))?;
    }
    let result = regexp_exec(vm, this, sv)?;
    let current = get(vm, this, "lastIndex")?;
    if !same_value(vm, current, previous) {
        set(vm, this, "lastIndex", previous)?;
    }
    if result == Value::NULL {
        return Ok(Value::int32(-1));
    }
    get(vm, result, "index")
}

/// `RegExp.prototype [ @@split ] ( string, limit )`, §22.2.6.14†:
/// 1. Let rx be the this value.
/// 2. If rx is not an Object, throw a TypeError exception.
/// 3. Let S be ? ToString(string).
/// 4. Let C be ? SpeciesConstructor(rx, %RegExp%).
/// 5. Let flags be ? ToString(? Get(rx, "flags")).
/// 6. If flags contains "u" or flags contains "v", let unicodeMatching be
///    true.
/// 7. Else, let unicodeMatching be false.
/// 8. If flags contains "y", let newFlags be flags.
/// 9. Else, let newFlags be the string-concatenation of flags and "y".
/// 10. Let splitter be ? Construct(C, « rx, newFlags »).
/// 11. Let A be ! ArrayCreate(0).
/// 12. Let lengthA be 0.
/// 13. If limit is undefined, let lim be 2^32 - 1; else let lim be ℝ(?
///     ToUint32(limit)).
/// 14. If lim = 0, return A.
/// 15. If S is the empty String, then
///     a. Let z be ? RegExpExec(splitter, S).
///     b. If z is not null, return A.
///     c. Perform ! CreateDataPropertyOrThrow(A, "0", S).
///     d. Return A.
/// 16. Let size be the length of S.
/// 17. Let p be 0.
/// 18. Let q be p.
/// 19. Repeat, while q < size,
///     a. Perform ? Set(splitter, "lastIndex", 𝔽(q), true).
///     b. Let z be ? RegExpExec(splitter, S).
///     c. If z is null, then i. Set q to AdvanceStringIndex(S, q,
///     unicodeMatching).
///     d. Else,
///     i. Let e be ℝ(? ToLength(? Get(splitter, "lastIndex"))).
///     ii. Set e to min(e, size).
///     iii. If e = p, then 1. Set q to AdvanceStringIndex(S, q,
///     unicodeMatching).
///     iv. Else, (1) let T be the substring of S from p to q; (2) perform
///     ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(lengthA)), T); (3) set
///     lengthA to lengthA + 1; (4) if lengthA = lim, return A; (5) set p to
///     e; (6) let numberOfCaptures be ? LengthOfArrayLike(z); (7) set
///     numberOfCaptures to max(numberOfCaptures - 1, 0); (8) let i be 1; (9)
///     repeat, while i ≤ numberOfCaptures, (a) let nextCapture be ? Get(z, !
///     ToString(𝔽(i))); (b) perform ! CreateDataPropertyOrThrow(A, !
///     ToString(𝔽(lengthA)), nextCapture); (c) set i to i + 1; (d) set lengthA
///     to lengthA + 1; (e) if lengthA = lim, return A; (10) set q to p.
/// 20. Let T be the substring of S from p to size.
/// 21. Perform ! CreateDataPropertyOrThrow(A, ! ToString(𝔽(lengthA)), T).
/// 22. Return A.
fn symbol_split(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object(vm, this, "RegExp.prototype[@@split]")?;
    let sv = to_string_value(vm, arg(args, 0))?;
    let s = string_of(vm, sv)?;
    let default = vm.intrinsic(Intrinsic::RegExpConstructor);
    let c = species_constructor(vm, this, default)?;
    let flags = flags_of(vm, this)?;
    let unicode_matching = is_unit(&flags, b'u') || is_unit(&flags, b'v');
    let mut new_flags = units_of(&flags);
    if !is_unit(&flags, b'y') {
        new_flags.push(u16::from(b'y'));
    }
    let nf = units_value(vm, &new_flags)?;
    let splitter = vm.construct_value(c, &[this, nf])?;
    let a = vm.array_create(0.0, None)?;
    let mut length_a: u64 = 0;
    let limit = arg(args, 1);
    let lim: u64 = if limit == Value::UNDEFINED {
        4_294_967_295
    } else {
        let n = vm.to_number(limit)?;
        u64::from(clazel_js_vm::numeric::to_uint32(
            clazel_js_vm::numeric::narrow(n),
        ))
    };
    if lim == 0 {
        return Ok(a);
    }
    let push = |vm: &mut Vm, len: &mut u64, v: Value| -> Result<(), Abrupt> {
        let k = vm.index_key(*len)?;
        vm.create_data_property_or_throw(a, k, v)?;
        *len = len.saturating_add(1);
        Ok(())
    };
    let size = s.len();
    if size == 0 {
        let z = regexp_exec(vm, splitter, sv)?;
        if z == Value::NULL {
            push(vm, &mut length_a, sv)?;
        }
        return Ok(a);
    }
    let (mut p, mut q) = (0usize, 0usize);
    while q < size {
        vm.charge_step()?;
        set(vm, splitter, "lastIndex", number(q as f64))?;
        let z = regexp_exec(vm, splitter, sv)?;
        if z == Value::NULL {
            q = advance_string_index(&s, q as f64, unicode_matching) as usize;
            continue;
        }
        let li = get(vm, splitter, "lastIndex")?;
        let e = (to_length(vm, li)? as usize).min(size);
        if e == p {
            q = advance_string_index(&s, q as f64, unicode_matching) as usize;
            continue;
        }
        let t = js_string(vm, s.substring(p, q))?;
        push(vm, &mut length_a, t)?;
        if length_a == lim {
            return Ok(a);
        }
        p = e;
        let n_caps = (length_of_array_like(vm, z)? - 1.0).max(0.0) as usize;
        for i in 1..=n_caps {
            let k = vm.index_key(i as u64)?;
            let next_capture = vm.get_value(z, k)?;
            push(vm, &mut length_a, next_capture)?;
            if length_a == lim {
                return Ok(a);
            }
        }
        q = p;
    }
    let t = js_string(vm, s.substring(p, size))?;
    push(vm, &mut length_a, t)?;
    Ok(a)
}

/// Used by the String methods: `Invoke(rx, @@match, « S »)` and the like.
///
/// # Errors
/// What the lookup or the call throws.
pub fn invoke_symbol(
    vm: &mut Vm,
    rx: Value,
    id: wk::SymbolId,
    args: &[Value],
) -> Result<Value, Abrupt> {
    let k = vm.well_known_key(id)?;
    let f = vm.get_value(rx, k)?;
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Symbol method is not a function"));
    }
    vm.call(f, rx, args)
}
