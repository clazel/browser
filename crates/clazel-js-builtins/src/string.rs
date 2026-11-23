//! `String` (§22.1†): the constructor, `String.fromCharCode`,
//! `String.fromCodePoint`, `String.raw`, and `String.prototype`: `at`,
//! `charAt`, `charCodeAt`, `codePointAt`, `concat`, `endsWith`, `includes`,
//! `indexOf`, `isWellFormed`, `lastIndexOf`, `localeCompare`, `match`,
//! `matchAll`, `padEnd`, `padStart`, `repeat`, `replace`, `replaceAll`,
//! `search`, `slice`, `split`, `startsWith`, `substring`,
//! `toLocaleLowerCase`, `toLocaleUpperCase`, `toLowerCase`, `toString`,
//! `toUpperCase`, `toWellFormed`, `trim`, `trimEnd`, `trimStart`, `valueOf`
//! and `@@iterator`; and of Annex B (§B.2.2†), `substr`, `trimLeft` and
//! `trimRight`.
//!
//! # Differences from the standard, all listed
//!
//! - **`match`, `matchAll`, `search`, `replace`, `replaceAll` and `split`**
//!   call a pattern's `@@match`, `@@matchAll`, `@@search`, `@@replace` or
//!   `@@split` method as the standard says (a `RegExp`'s are in
//!   [`crate::regexp`]); `match`, `matchAll` and `search` with any other
//!   pattern make a RegExp with RegExpCreate and invoke its method.
//! - **Case conversion** (`toLowerCase`, `toUpperCase`, §22.1.3.28†) is
//!   Rust's `str::to_lowercase` and `to_uppercase`: the full Unicode Default
//!   Case Conversion with SpecialCasing's unconditional mappings and Final
//!   Sigma, at the Unicode version of the Rust toolchain, not the version the
//!   pinned ECMA-262 names. A lone surrogate is kept as it is and splits the
//!   text around it (so Final Sigma does not look across one). The locale
//!   variants are the same functions (no ECMA-402).
//! - **`localeCompare`** (§22.1.3.12†) compares code units: the standard
//!   allows any consistent order without ECMA-402, but asks that canonically
//!   equivalent strings compare equal, which this does not do (no
//!   normalization).
//! - **`normalize`** (§22.1.3.15†) is absent: the NFC/NFD/NFKC/NFKD data is a
//!   later slice of 7.9.
//! - **A String object has no index properties**, only `length` (the String
//!   exotic object's `[[GetOwnProperty]]`, §10.4.3.1†, is a later slice); a
//!   primitive string's indices are read by the VM directly.

use crate::iterator::{code_point_at, create_string_iterator};
use crate::regexp::{invoke_symbol, is_regexp, regexp_create};
use crate::util::{
    CONSTANT, arg, constructor, define, js_string, method, number, require_object_coercible,
    string, to_integer_or_infinity,
};
use clazel_js_heap::string::{JsString, MAX_LENGTH};
use clazel_js_heap::symbol::{self as wk, SymbolId};
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, NativeFn, Vm};

/// Installs `String` and `String.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §22.1.3†: the prototype is itself a String object whose [[StringData]]
    // is the empty String.
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let empty = string(vm, "")?;
    let proto = vm.new_wrapper(empty, object_proto)?;
    vm.set_intrinsic(Intrinsic::StringPrototype, proto);
    let ctor = constructor(vm, "String", 1, string_constructor, proto)?;
    method(vm, ctor, "fromCharCode", 1, from_char_code)?;
    method(vm, ctor, "fromCodePoint", 1, from_code_point)?;
    method(vm, ctor, "raw", 1, raw)?;
    let methods: [(&str, i32, NativeFn); 34] = [
        ("at", 1, at),
        ("charAt", 1, char_at),
        ("charCodeAt", 1, char_code_at),
        ("codePointAt", 1, code_point_at_fn),
        ("concat", 1, concat),
        ("endsWith", 1, ends_with),
        ("includes", 1, includes),
        ("indexOf", 1, index_of),
        ("isWellFormed", 0, is_well_formed),
        ("lastIndexOf", 1, last_index_of),
        ("localeCompare", 1, locale_compare),
        ("match", 1, match_fn),
        ("matchAll", 1, match_all),
        ("padEnd", 1, pad_end),
        ("padStart", 1, pad_start),
        ("repeat", 1, repeat),
        ("replace", 2, replace),
        ("replaceAll", 2, replace_all),
        ("search", 1, search),
        ("slice", 2, slice),
        ("split", 2, split),
        ("startsWith", 1, starts_with),
        ("substr", 2, substr),
        ("substring", 2, substring),
        ("toLocaleLowerCase", 0, to_lower_case),
        ("toLocaleUpperCase", 0, to_upper_case),
        ("toLowerCase", 0, to_lower_case),
        ("toString", 0, to_string),
        ("toUpperCase", 0, to_upper_case),
        ("toWellFormed", 0, to_well_formed),
        ("trim", 0, trim),
        ("valueOf", 0, value_of),
        ("trimEnd", 0, trim_end),
        ("trimStart", 0, trim_start),
    ];
    for (name, len, f) in methods {
        method(vm, proto, name, len, f)?;
    }
    // §B.2.2.15†, §B.2.2.16†: "The initial value of the "trimLeft" property is
    // %String.prototype.trimStart%" (likewise trimRight).
    for (alias, of) in [("trimLeft", "trimStart"), ("trimRight", "trimEnd")] {
        let f = vm.get_named(proto, of)?;
        define(vm, proto, alias, f, crate::util::METHOD)?;
    }
    // §22.1.3.36† `String.prototype [ @@iterator ] ( )`: its `name` is
    // "[Symbol.iterator]".
    let it = vm.new_native("[Symbol.iterator]", 0, iterator)?;
    let k = vm.well_known_key(wk::ITERATOR)?;
    vm.heap_mut().define(proto, k, it, crate::util::METHOD)?;
    crate::util::global(vm, "String", ctor)
}

/// `String ( value )`, §22.1.1.1†:
/// 1. If value is not present, let s be the empty String.
/// 2. Else,
///    a. If NewTarget is undefined and value is a Symbol, return
///    SymbolDescriptiveString(value).
///    b. Let s be ? ToString(value).
/// 3. If NewTarget is undefined, return s.
/// 4. Return StringCreate(s, ? GetPrototypeFromConstructor(NewTarget,
///    "%String.prototype%")).
fn string_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let nt = vm.new_target();
    let s = match args.first() {
        Some(v) if nt == Value::UNDEFINED && vm.heap().is_symbol(*v) => {
            let d = vm.symbol_descriptive_string(*v);
            return js_string(vm, d);
        }
        Some(v) => {
            let s = vm.to_js_string(*v)?;
            js_string(vm, s)?
        }
        None => string(vm, "")?,
    };
    if nt == Value::UNDEFINED {
        return Ok(s);
    }
    // StringCreate, §10.4.3.4†: the String exotic object, with `length`.
    let o = vm.create_from_constructor(nt, Intrinsic::StringPrototype, ObjKind::Primitive(s))?;
    let len = vm.heap().string(s).map_or(0, JsString::len);
    let len = i32::try_from(len).map_err(|_| Abrupt::OutOfMemory)?;
    define(vm, o, "length", Value::int32(len), CONSTANT)?;
    Ok(o)
}

/// A string of code units as a value, or the RangeError of a string past
/// the length limit (the standard's limit is 2^53 - 1; the heap's is
/// [`MAX_LENGTH`], and a longer result is an "Invalid string length", as
/// other engines report theirs).
fn units_value(vm: &mut Vm, units: &[u16]) -> Result<Value, Abrupt> {
    match JsString::from_units(units) {
        Ok(s) => js_string(vm, s),
        Err(_) => Err(vm.range_error("Invalid string length")),
    }
}

/// `String.fromCharCode ( ...codeUnits )`, §22.1.2.1†:
/// 1. Let result be the empty String.
/// 2. For each element next of codeUnits, do
///    a. Let nextCU be the code unit whose numeric value is ℝ(? ToUint16(next)).
///    b. Set result to the string-concatenation of result and nextCU.
/// 3. Return result.
fn from_char_code(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut units = Vec::with_capacity(args.len());
    for a in args {
        let n = vm.to_number(*a)?;
        // ToUint16, §7.1.9†: truncate, then modulo 2^16.
        let unit = if n.is_finite() {
            (n.trunc().rem_euclid(65536.0)) as u16
        } else {
            0
        };
        units.push(unit);
    }
    units_value(vm, &units)
}

/// UTF16EncodeCodePoint ( cp ), §11.1.1†: one unit below 0x10000, else the
/// surrogate pair.
fn push_code_point(out: &mut Vec<u16>, cp: u32) {
    match u16::try_from(cp) {
        Ok(u) => out.push(u),
        Err(_) => {
            // 2. Let cu1 be floor((cp - 0x10000) / 0x400) + 0xD800.
            // 3. Let cu2 be ((cp - 0x10000) modulo 0x400) + 0xDC00.
            let c = cp.saturating_sub(0x1_0000);
            let hi = u16::try_from((c >> 10).saturating_add(0xD800)).unwrap_or(0xFFFD);
            let lo = u16::try_from((c & 0x3FF).saturating_add(0xDC00)).unwrap_or(0xFFFD);
            out.push(hi);
            out.push(lo);
        }
    }
}

/// `String.fromCodePoint ( ...codePoints )`, §22.1.2.2†:
/// 1. Let result be the empty String.
/// 2. For each element next of codePoints, do
///    a. Let nextCP be ? ToNumber(next).
///    b. If IsIntegralNumber(nextCP) is false, throw a RangeError exception.
///    c. If ℝ(nextCP) < 0 or ℝ(nextCP) > 0x10FFFF, throw a RangeError
///    exception.
///    d. Set result to the string-concatenation of result and
///    UTF16EncodeCodePoint(ℝ(nextCP)).
/// 3. Assert: If codePoints is empty, then result is the empty String.
/// 4. Return result.
fn from_code_point(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let mut units = Vec::with_capacity(args.len());
    for a in args {
        let n = vm.to_number(*a)?;
        if !n.is_finite() || n.trunc() != n || !(0.0..=1_114_111.0).contains(&n) {
            let d = clazel_js_number::number_to_string(n);
            return Err(vm.range_error(&format!("Invalid code point {d}")));
        }
        push_code_point(&mut units, n as u32);
    }
    units_value(vm, &units)
}

/// `String.raw ( template, ...substitutions )`, §22.1.2.4†:
/// 1. Let substitutionCount be the number of elements in substitutions.
/// 2. Let cooked be ? ToObject(template).
/// 3. Let literals be ? ToObject(? Get(cooked, "raw")).
/// 4. Let literalCount be ? LengthOfArrayLike(literals).
/// 5. If literalCount ≤ 0, return the empty String.
/// 6. Let R be the empty String.
/// 7. Let nextIndex be 0.
/// 8. Repeat,
///    a. Let nextLiteralVal be ? Get(literals, ! ToString(𝔽(nextIndex))).
///    b. Let nextLiteral be ? ToString(nextLiteralVal).
///    c. Set R to the string-concatenation of R and nextLiteral.
///    d. If nextIndex + 1 = literalCount, return R.
///    e. If nextIndex < substitutionCount, then
///    i. Let nextSubVal be substitutions[nextIndex].
///    ii. Let nextSub be ? ToString(nextSubVal).
///    iii. Set R to the string-concatenation of R and nextSub.
///    f. Set nextIndex to nextIndex + 1.
fn raw(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let subs = args.get(1..).unwrap_or(&[]);
    let cooked = vm.to_object(arg(args, 0))?;
    let kr = crate::util::key(vm, "raw")?;
    let raw_v = vm.get_value(cooked, kr)?;
    let literals = vm.to_object(raw_v)?;
    let kl = crate::util::key(vm, "length")?;
    let lv = vm.get_value(literals, kl)?;
    let count = to_integer_or_infinity(vm, lv)?.min(9_007_199_254_740_991.0);
    if count <= 0.0 {
        return string(vm, "");
    }
    let mut r: Vec<u16> = Vec::new();
    let mut next: u64 = 0;
    loop {
        vm.charge_step()?;
        let k = vm.index_key(next)?;
        let lit = vm.get_value(literals, k)?;
        r.extend(vm.to_js_string(lit)?.units());
        if r.len() > MAX_LENGTH {
            return Err(vm.range_error("Invalid string length"));
        }
        let after = next.saturating_add(1);
        if after as f64 >= count {
            return units_value(vm, &r);
        }
        if let Some(sub) = usize::try_from(next).ok().and_then(|i| subs.get(i)) {
            r.extend(vm.to_js_string(*sub)?.units());
        }
        next = after;
    }
}

/// thisStringValue ( value ), §22.1.3.35.1†:
/// 1. If value is a String, return value.
/// 2. If value is an Object and value has a [[StringData]] internal slot,
///    then return value.[[StringData]].
/// 3. Throw a TypeError exception.
fn this_string_value(vm: &mut Vm, v: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_string(v) {
        return Ok(v);
    }
    if let Some(ObjKind::Primitive(p)) = vm.heap().obj(v).map(|o| o.kind)
        && vm.heap().is_string(p)
    {
        return Ok(p);
    }
    Err(vm.type_error("not a String"))
}

/// `String.prototype.toString ( )`, §22.1.3.29†:
/// 1. Return ? thisStringValue(this value).
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    this_string_value(vm, this)
}

/// `String.prototype.valueOf ( )`, §22.1.3.35†:
/// 1. Return ? thisStringValue(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    this_string_value(vm, this)
}

/// The first steps of most methods below:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. Let S be ? ToString(O).
fn this_string(vm: &mut Vm, this: Value, method: &str) -> Result<JsString, Abrupt> {
    require_object_coercible(vm, this, &format!("String.prototype.{method}"))?;
    vm.to_js_string(this)
}

/// ToString as a string value.
fn to_string_value(vm: &mut Vm, v: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_string(v) {
        return Ok(v);
    }
    let s = vm.to_js_string(v)?;
    js_string(vm, s)
}

/// The length of a string as `f64`.
fn len_of(s: &JsString) -> f64 {
    s.len() as f64
}

/// The code units of a string.
fn units(s: &JsString) -> Vec<u16> {
    s.units().collect()
}

/// StringIndexOf ( string, searchValue, fromIndex ), §6.1.4.1†:
/// 1. Let len be the length of string.
/// 2. If searchValue is the empty String and fromIndex ≤ len, return
///    fromIndex.
/// 3. Let searchLen be the length of searchValue.
/// 4. For each integer i such that fromIndex ≤ i ≤ len - searchLen, in
///    ascending order, do
///    a. Let candidate be the substring of string from i to i + searchLen.
///    b. If candidate is searchValue, return i.
/// 5. Return not-found.
fn string_index_of(hay: &[u16], needle: &[u16], from: usize) -> Option<usize> {
    if needle.is_empty() {
        return (from <= hay.len()).then_some(from);
    }
    let last = hay.len().checked_sub(needle.len())?;
    (from..=last).find(|&i| hay.get(i..i.saturating_add(needle.len())) == Some(needle))
}

/// StringLastIndexOf ( string, searchValue, fromIndex ), §6.1.4.2†:
/// 1. Let len be the length of string.
/// 2. Let searchLen be the length of searchValue.
/// 3. Assert: fromIndex + searchLen ≤ len.
/// 4. For each integer i such that 0 ≤ i ≤ fromIndex, in descending order, do
///    a. Let candidate be the substring of string from i to i + searchLen.
///    b. If candidate is searchValue, return i.
/// 5. Return not-found.
fn string_last_index_of(hay: &[u16], needle: &[u16], from: usize) -> Option<usize> {
    (0..=from)
        .rev()
        .find(|&i| hay.get(i..i.saturating_add(needle.len())) == Some(needle))
}

/// `String.prototype.at ( index )`, §22.1.3.1†:
/// 1 and 2. As above.
/// 3. Let len be the length of S.
/// 4. Let relativeIndex be ? ToIntegerOrInfinity(index).
/// 5. If relativeIndex ≥ 0, then a. Let k be relativeIndex.
/// 6. Else, a. Let k be len + relativeIndex.
/// 7. If k < 0 or k ≥ len, return undefined.
/// 8. Return the substring of S from k to k + 1.
fn at(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "at")?;
    let len = len_of(&s);
    let rel = to_integer_or_infinity(vm, arg(args, 0))?;
    let k = if rel >= 0.0 { rel } else { len + rel };
    if k < 0.0 || k >= len {
        return Ok(Value::UNDEFINED);
    }
    let i = k as usize;
    js_string(vm, s.substring(i, i.saturating_add(1)))
}

/// `String.prototype.charAt ( pos )`, §22.1.3.2†:
/// 1 and 2. As above.
/// 3. Let position be ? ToIntegerOrInfinity(pos).
/// 4. Let size be the length of S.
/// 5. If position < 0 or position ≥ size, return the empty String.
/// 6. Return the substring of S from position to position + 1.
fn char_at(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "charAt")?;
    let position = to_integer_or_infinity(vm, arg(args, 0))?;
    if position < 0.0 || position >= len_of(&s) {
        return string(vm, "");
    }
    let i = position as usize;
    js_string(vm, s.substring(i, i.saturating_add(1)))
}

/// `String.prototype.charCodeAt ( pos )`, §22.1.3.3†:
/// 1 and 2. As above.
/// 3. Let position be ? ToIntegerOrInfinity(pos).
/// 4. Let size be the length of S.
/// 5. If position < 0 or position ≥ size, return NaN.
/// 6. Return the Number value for the numeric value of the code unit at
///    index position within the String S.
fn char_code_at(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "charCodeAt")?;
    let position = to_integer_or_infinity(vm, arg(args, 0))?;
    if position < 0.0 || position >= len_of(&s) {
        return Ok(Value::double(f64::NAN));
    }
    let unit = s.unit(position as usize).unwrap_or(0);
    Ok(Value::int32(i32::from(unit)))
}

/// `String.prototype.codePointAt ( pos )`, §22.1.3.4†:
/// 1 and 2. As above.
/// 3. Let position be ? ToIntegerOrInfinity(pos).
/// 4. Let size be the length of S.
/// 5. If position < 0 or position ≥ size, return undefined.
/// 6. Let cp be CodePointAt(S, position).
/// 7. Return 𝔽(cp.[[CodePoint]]).
fn code_point_at_fn(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "codePointAt")?;
    let position = to_integer_or_infinity(vm, arg(args, 0))?;
    if position < 0.0 || position >= len_of(&s) {
        return Ok(Value::UNDEFINED);
    }
    let (cp, _) = code_point_at(&s, position as usize);
    Ok(number(f64::from(cp)))
}

/// `String.prototype.concat ( ...args )`, §22.1.3.5†:
/// 1 and 2. As above.
/// 3. Let R be S.
/// 4. For each element next of args, do
///    a. Let nextString be ? ToString(next).
///    b. Set R to the string-concatenation of R and nextString.
/// 5. Return R.
fn concat(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "concat")?;
    let mut r = units(&s);
    for a in args {
        r.extend(vm.to_js_string(*a)?.units());
        if r.len() > MAX_LENGTH {
            return Err(vm.range_error("Invalid string length"));
        }
    }
    units_value(vm, &r)
}

/// The search string of `startsWith`, `endsWith` and `includes` (their
/// steps 3 to 5): a TypeError if it IsRegExp, else ToString.
fn search_string(vm: &mut Vm, v: Value, method: &str) -> Result<JsString, Abrupt> {
    if is_regexp(vm, v)? {
        return Err(vm.type_error(&format!(
            "First argument to String.prototype.{method} must not be a regular expression"
        )));
    }
    vm.to_js_string(v)
}

/// `String.prototype.endsWith ( searchString [ , endPosition ] )`, §22.1.3.7†:
/// 1 and 2. As above.
/// 3. Let isRegExp be ? IsRegExp(searchString).
/// 4. If isRegExp is true, throw a TypeError exception.
/// 5. Let searchStr be ? ToString(searchString).
/// 6. Let len be the length of S.
/// 7. If endPosition is undefined, let pos be len; else let pos be ?
///    ToIntegerOrInfinity(endPosition).
/// 8. Let end be the result of clamping pos between 0 and len.
/// 9. Let searchLength be the length of searchStr.
/// 10. If searchLength = 0, return true.
/// 11. Let start be end - searchLength.
/// 12. If start < 0, return false.
/// 13. Let substring be the substring of S from start to end.
/// 14. If substring is searchStr, return true.
/// 15. Return false.
fn ends_with(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "endsWith")?;
    let search = search_string(vm, arg(args, 0), "endsWith")?;
    let len = len_of(&s);
    let pos = if arg(args, 1) == Value::UNDEFINED {
        len
    } else {
        to_integer_or_infinity(vm, arg(args, 1))?
    };
    let end = pos.clamp(0.0, len) as usize;
    let Some(start) = end.checked_sub(search.len()) else {
        return Ok(Value::FALSE);
    };
    Ok(Value::boolean(s.substring(start, end) == search))
}

/// `String.prototype.includes ( searchString [ , position ] )`, §22.1.3.8†:
/// 1 and 2. As above.
/// 3 to 5. As `endsWith`'s.
/// 6. Let pos be ? ToIntegerOrInfinity(position).
/// 7. Assert: If position is undefined, then pos is 0.
/// 8. Let len be the length of S.
/// 9. Let start be the result of clamping pos between 0 and len.
/// 10. Let index be StringIndexOf(S, searchStr, start).
/// 11. If index is not-found, return false.
/// 12. Return true.
fn includes(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "includes")?;
    let search = search_string(vm, arg(args, 0), "includes")?;
    let pos = to_integer_or_infinity(vm, arg(args, 1))?;
    let start = pos.clamp(0.0, len_of(&s)) as usize;
    Ok(Value::boolean(
        string_index_of(&units(&s), &units(&search), start).is_some(),
    ))
}

/// `String.prototype.indexOf ( searchString [ , position ] )`, §22.1.3.9†:
/// 1 and 2. As above.
/// 3. Let searchStr be ? ToString(searchString).
/// 4. Let pos be ? ToIntegerOrInfinity(position).
/// 5. Assert: If position is undefined, then pos is 0.
/// 6. Let len be the length of S.
/// 7. Let start be the result of clamping pos between 0 and len.
/// 8. Let result be StringIndexOf(S, searchStr, start).
/// 9. If result is not-found, return -1𝔽.
/// 10. Return 𝔽(result).
fn index_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "indexOf")?;
    let search = vm.to_js_string(arg(args, 0))?;
    let pos = to_integer_or_infinity(vm, arg(args, 1))?;
    let start = pos.clamp(0.0, len_of(&s)) as usize;
    Ok(match string_index_of(&units(&s), &units(&search), start) {
        Some(i) => number(i as f64),
        None => Value::int32(-1),
    })
}

/// Whether a string is well formed: no lone surrogate (IsStringWellFormedUnicode,
/// §7.2.9†, by CodePointAt over the string).
fn well_formed(s: &JsString) -> bool {
    let mut k = 0usize;
    while k < s.len() {
        let (cp, n) = code_point_at(s, k);
        if (0xD800..=0xDFFF).contains(&cp) {
            return false;
        }
        k = k.saturating_add(n.max(1));
    }
    true
}

/// `String.prototype.isWellFormed ( )`, §22.1.3.10†:
/// 1 and 2. As above.
/// 3. Return IsStringWellFormedUnicode(S).
fn is_well_formed(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "isWellFormed")?;
    Ok(Value::boolean(well_formed(&s)))
}

/// `String.prototype.toWellFormed ( )`, §22.1.3.32†:
/// 1 and 2. As above.
/// 3. Let strLen be the length of S.
/// 4. Let k be 0.
/// 5. Let result be the empty String.
/// 6. Repeat, while k < strLen,
///    a. Let cp be CodePointAt(S, k).
///    b. If cp.[[IsUnpairedSurrogate]] is true, then
///       i. Set result to the string-concatenation of result and 0xFFFD
///          (REPLACEMENT CHARACTER).
///    c. Else,
///       i. Set result to the string-concatenation of result and
///          UTF16EncodeCodePoint(cp.[[CodePoint]]).
///    d. Set k to k + cp.[[CodeUnitCount]].
/// 7. Return result.
fn to_well_formed(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "toWellFormed")?;
    let mut out = Vec::with_capacity(s.len());
    let mut k = 0usize;
    while k < s.len() {
        let (cp, n) = code_point_at(&s, k);
        if (0xD800..=0xDFFF).contains(&cp) {
            out.push(0xFFFD);
        } else {
            push_code_point(&mut out, cp);
        }
        k = k.saturating_add(n.max(1));
    }
    units_value(vm, &out)
}

/// `String.prototype.lastIndexOf ( searchString [ , position ] )`,
/// §22.1.3.11†:
/// 1 and 2. As above.
/// 3. Let searchStr be ? ToString(searchString).
/// 4. Let numPos be ? ToNumber(position).
/// 5. Assert: If position is undefined, then numPos is NaN.
/// 6. If numPos is NaN, let pos be +∞; otherwise, let pos be !
///    ToIntegerOrInfinity(numPos).
/// 7. Let len be the length of S.
/// 8. Let searchLen be the length of searchStr.
/// 9. Let start be the result of clamping pos between 0 and len - searchLen.
/// 10. If searchStr is the empty String, return 𝔽(start).
/// 11. Let result be StringLastIndexOf(S, searchStr, start).
/// 12. If result is not-found, return -1𝔽.
/// 13. Return 𝔽(result).
fn last_index_of(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "lastIndexOf")?;
    let search = vm.to_js_string(arg(args, 0))?;
    let num_pos = vm.to_number(arg(args, 1))?;
    let pos = if num_pos.is_nan() {
        f64::INFINITY
    } else {
        num_pos.trunc() + 0.0
    };
    let Some(room) = s.len().checked_sub(search.len()) else {
        return Ok(Value::int32(-1));
    };
    let start = pos.clamp(0.0, room as f64) as usize;
    if search.is_empty() {
        return Ok(number(start as f64));
    }
    Ok(
        match string_last_index_of(&units(&s), &units(&search), start) {
            Some(i) => number(i as f64),
            None => Value::int32(-1),
        },
    )
}

/// `String.prototype.localeCompare ( that [ , reserved1 [ , reserved2 ] ] )`,
/// §22.1.3.12† (without ECMA-402; see the module header):
/// 1 and 2. As above.
/// 3. Let thatValue be ? ToString(that).
/// 4. The result is a Number that is negative, zero or positive as S comes
///    before, is equal to or comes after thatValue: here by code units.
fn locale_compare(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "localeCompare")?;
    let that = vm.to_js_string(arg(args, 0))?;
    Ok(Value::int32(match s.compare(&that) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }))
}

/// GetMethod ( V, P ), §7.3.11†, for a well-known Symbol `P`: `None` when
/// the value is `undefined` or `null`.
fn get_symbol_method(vm: &mut Vm, v: Value, id: SymbolId) -> Result<Option<Value>, Abrupt> {
    let k = vm.well_known_key(id)?;
    let f = vm.get_value(v, k)?;
    if f == Value::UNDEFINED || f == Value::NULL {
        return Ok(None);
    }
    if !vm.heap().is_callable(f) {
        return Err(vm.type_error("Symbol method is not a function"));
    }
    Ok(Some(f))
}

/// The delegation that opens `match`, `matchAll`, `search`, `replace`,
/// `replaceAll` and `split` (their step 2): if the pattern is neither
/// undefined nor null and has the method `id`, the result of calling it
/// with « O, ...rest ».
fn delegate(
    vm: &mut Vm,
    pattern: Value,
    id: SymbolId,
    this: Value,
    rest: &[Value],
) -> Result<Option<Value>, Abrupt> {
    if pattern == Value::UNDEFINED || pattern == Value::NULL {
        return Ok(None);
    }
    match get_symbol_method(vm, pattern, id)? {
        Some(f) => {
            let mut a = vec![this];
            a.extend_from_slice(rest);
            Ok(Some(vm.call(f, pattern, &a)?))
        }
        None => Ok(None),
    }
}

/// `String.prototype.match ( regexp )`, §22.1.3.13†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If regexp is neither undefined nor null, then
///    a. Let matcher be ? GetMethod(regexp, @@match).
///    b. If matcher is not undefined, then
///    i. Return ? Call(matcher, regexp, « O »).
/// 3. Let S be ? ToString(O).
/// 4. Let rx be ? RegExpCreate(regexp, undefined).
/// 5. Return ? Invoke(rx, @@match, « S »).
fn match_fn(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.match")?;
    if let Some(v) = delegate(vm, arg(args, 0), wk::MATCH, this, &[])? {
        return Ok(v);
    }
    let sv = to_string_value(vm, this)?;
    let rx = regexp_create(vm, arg(args, 0), Value::UNDEFINED)?;
    invoke_symbol(vm, rx, wk::MATCH, &[sv])
}

/// `String.prototype.matchAll ( regexp )`, §22.1.3.14†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If regexp is neither undefined nor null, then
///    a. Let isRegExp be ? IsRegExp(regexp).
///    b. If isRegExp is true, then
///    i. Let flags be ? Get(regexp, "flags").
///    ii. Perform ? RequireObjectCoercible(flags).
///    iii. If ? ToString(flags) does not contain "g", throw a TypeError
///    exception.
///    c. Let matcher be ? GetMethod(regexp, @@matchAll).
///    d. If matcher is not undefined, then
///    i. Return ? Call(matcher, regexp, « O »).
/// 3. Let S be ? ToString(O).
/// 4. Let rx be ? RegExpCreate(regexp, "g").
/// 5. Return ? Invoke(rx, @@matchAll, « S »).
fn match_all(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.matchAll")?;
    let re = arg(args, 0);
    if re != Value::UNDEFINED && re != Value::NULL {
        require_global_flag(vm, re, "matchAll")?;
    }
    if let Some(v) = delegate(vm, re, wk::MATCH_ALL, this, &[])? {
        return Ok(v);
    }
    let sv = to_string_value(vm, this)?;
    let g = string(vm, "g")?;
    let rx = regexp_create(vm, re, g)?;
    invoke_symbol(vm, rx, wk::MATCH_ALL, &[sv])
}

/// Step 2.a and 2.b of `matchAll` and `replaceAll`: a RegExp pattern must
/// have the `g` flag.
fn require_global_flag(vm: &mut Vm, re: Value, method: &str) -> Result<(), Abrupt> {
    if is_regexp(vm, re)? {
        let kf = crate::util::key(vm, "flags")?;
        let flags = vm.get_value(re, kf)?;
        require_object_coercible(vm, flags, "flags")?;
        let f = vm.to_js_string(flags)?;
        if !f.units().any(|u| u == u16::from(b'g')) {
            return Err(vm.type_error(&format!(
                "String.prototype.{method} called with a non-global RegExp argument"
            )));
        }
    }
    Ok(())
}

/// `String.prototype.search ( regexp )`, §22.1.3.22†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If regexp is neither undefined nor null, then
///    a. Let searcher be ? GetMethod(regexp, @@search).
///    b. If searcher is not undefined, then
///    i. Return ? Call(searcher, regexp, « O »).
/// 3. Let string be ? ToString(O).
/// 4. Let rx be ? RegExpCreate(regexp, undefined).
/// 5. Return ? Invoke(rx, @@search, « string »).
fn search(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.search")?;
    if let Some(v) = delegate(vm, arg(args, 0), wk::SEARCH, this, &[])? {
        return Ok(v);
    }
    let sv = to_string_value(vm, this)?;
    let rx = regexp_create(vm, arg(args, 0), Value::UNDEFINED)?;
    invoke_symbol(vm, rx, wk::SEARCH, &[sv])
}

/// The placement of StringPad.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Placement {
    Start,
    End,
}

/// StringPaddingBuiltinsImpl ( O, maxLength, fillString, placement ),
/// §22.1.3.17.1†:
/// 1. Let S be ? ToString(O).
/// 2. Let intMaxLength be ℝ(? ToLength(maxLength)).
/// 3. Let stringLength be the length of S.
/// 4. If intMaxLength ≤ stringLength, return S.
/// 5. If fillString is undefined, set fillString to the String value
///    consisting solely of the code unit 0x0020 (SPACE).
/// 6. Else, set fillString to ? ToString(fillString).
/// 7. Return StringPad(S, intMaxLength, fillString, placement).
///
/// StringPad ( S, maxLength, fillString, placement ), §22.1.3.17.2†:
/// 1. Let stringLength be the length of S.
/// 2. If maxLength ≤ stringLength, return S.
/// 3. If fillString is the empty String, return S.
/// 4. Let fillLen be maxLength - stringLength.
/// 5. Let truncatedStringFiller be the String value consisting of repeated
///    concatenations of fillString truncated to length fillLen.
/// 6. If placement is start, return the string-concatenation of
///    truncatedStringFiller and S.
/// 7. Else, return the string-concatenation of S and truncatedStringFiller.
fn pad(vm: &mut Vm, this: Value, args: &[Value], placement: Placement) -> Result<Value, Abrupt> {
    let name = if placement == Placement::Start {
        "padStart"
    } else {
        "padEnd"
    };
    let s = this_string(vm, this, name)?;
    // ToLength, §7.1.20†.
    let max = to_integer_or_infinity(vm, arg(args, 0))?.clamp(0.0, 9_007_199_254_740_991.0);
    let len = len_of(&s);
    if max <= len {
        return js_string(vm, s);
    }
    let fill: Vec<u16> = if arg(args, 1) == Value::UNDEFINED {
        vec![0x20]
    } else {
        units(&vm.to_js_string(arg(args, 1))?)
    };
    if fill.is_empty() {
        return js_string(vm, s);
    }
    if max > MAX_LENGTH as f64 {
        return Err(vm.range_error("Invalid string length"));
    }
    let fill_len = (max - len) as usize;
    let filler: Vec<u16> = fill.iter().copied().cycle().take(fill_len).collect();
    let mut out = Vec::with_capacity(max as usize);
    if placement == Placement::Start {
        out.extend(filler);
        out.extend(s.units());
    } else {
        out.extend(s.units());
        out.extend(filler);
    }
    units_value(vm, &out)
}

/// `String.prototype.padEnd ( maxLength [ , fillString ] )`, §22.1.3.16†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. Return ? StringPaddingBuiltinsImpl(O, maxLength, fillString, end).
fn pad_end(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    pad(vm, this, args, Placement::End)
}

/// `String.prototype.padStart ( maxLength [ , fillString ] )`, §22.1.3.17†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. Return ? StringPaddingBuiltinsImpl(O, maxLength, fillString, start).
fn pad_start(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    pad(vm, this, args, Placement::Start)
}

/// `String.prototype.repeat ( count )`, §22.1.3.18†:
/// 1 and 2. As above.
/// 3. Let n be ? ToIntegerOrInfinity(count).
/// 4. If n < 0 or n = +∞, throw a RangeError exception.
/// 5. If n = 0, return the empty String.
/// 6. Return the String value that is made from n copies of S appended
///    together.
fn repeat(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "repeat")?;
    let n = to_integer_or_infinity(vm, arg(args, 0))?;
    if n < 0.0 || n == f64::INFINITY {
        return Err(vm.range_error("Invalid count value"));
    }
    if n == 0.0 || s.is_empty() {
        return string(vm, "");
    }
    if n * len_of(&s) > MAX_LENGTH as f64 {
        return Err(vm.range_error("Invalid string length"));
    }
    let one = units(&s);
    let mut out = Vec::with_capacity((n * len_of(&s)) as usize);
    for _ in 0..(n as usize) {
        out.extend_from_slice(&one);
    }
    units_value(vm, &out)
}

/// The lookup of a group name in GetSubstitution's namedCaptures.
pub type NamedLookup<'a> = &'a mut dyn FnMut(&[u16]) -> Result<Vec<u16>, Abrupt>;

/// GetSubstitution ( matched, str, position, captures, namedCaptures,
/// replacementTemplate ), §22.1.3.19.1†:
/// 1. Let stringLength be the length of str.
/// 2. Assert: position ≤ stringLength.
/// 3. Let result be the empty String.
/// 4. Let templateRemainder be replacementTemplate.
/// 5. Repeat, while templateRemainder is not the empty String,
///    a. NOTE: The following steps isolate ref (a prefix of
///    templateRemainder), determine refReplacement (its replacement), and
///    then append that replacement to result.
///    b. If templateRemainder starts with "$$", then
///    i. Let ref be "$$". ii. Let refReplacement be "$".
///    c. Else if templateRemainder starts with "$`", then
///    i. Let ref be "$`". ii. Let refReplacement be the substring of str
///    from 0 to position.
///    d. Else if templateRemainder starts with "$&", then
///    i. Let ref be "$&". ii. Let refReplacement be matched.
///    e. Else if templateRemainder starts with "$'" (0x0024 (DOLLAR SIGN)
///    followed by 0x0027 (APOSTROPHE)), then
///    i. Let ref be "$'". ii. Let matchLength be the length of matched.
///    iii. Let tailPos be position + matchLength. iv. Let refReplacement
///    be the substring of str from min(tailPos, stringLength).
///    f. Else if templateRemainder starts with "$" followed by 1 or more
///    decimal digits, then
///    i. If templateRemainder starts with "$" followed by 2 or more
///    decimal digits, let digitCount be 2. Otherwise, let digitCount be
///    1.
///    ii. Let digits be the substring of templateRemainder from 1 to 1 +
///    digitCount.
///    iii. Let index be ℝ(StringToNumber(digits)).
///    iv. Assert: 0 ≤ index ≤ 99.
///    v. Let captureLen be the number of elements in captures.
///    vi. If index > captureLen and digitCount = 2, then 1. NOTE: When a
///    two-digit replacement pattern specifies an index exceeding the count
///    of capturing groups, it is reinterpreted as a one-digit replacement
///    pattern followed by a literal digit. 2. Set digitCount to 1. 3. Set
///    digits to the substring of digits from 0 to 1. 4. Set index to
///    ℝ(StringToNumber(digits)).
///    vii. Let ref be the substring of templateRemainder from 0 to 1 +
///    digitCount.
///    viii. If 1 ≤ index ≤ captureLen, then 1. Let capture be
///    captures[index - 1]. 2. If capture is undefined, then a. Let
///    refReplacement be the empty String. 3. Else, a. Let refReplacement
///    be capture.
///    ix. Else, 1. Let refReplacement be ref.
///    g. Else if templateRemainder starts with "$<", then
///    i. Let gtPos be StringIndexOf(templateRemainder, ">", 0).
///    ii. If gtPos is not-found or namedCaptures is undefined, then 1. Let
///    ref be "$<". 2. Let refReplacement be ref.
///    iii. Else, 1. Let ref be the substring of templateRemainder from 0 to
///    gtPos + 1. 2. Let groupName be the substring of templateRemainder from
///    2 to gtPos. 3. Assert: namedCaptures is an Object. 4. Let capture be ?
///    Get(namedCaptures, groupName). 5. If capture is undefined, then a. Let
///    refReplacement be the empty String. 6. Else, a. Let refReplacement be ?
///    ToString(capture).
///    h. Else,
///    i. Let ref be the substring of templateRemainder from 0 to 1.
///    ii. Let refReplacement be ref.
///    i. Let refLength be the length of ref.
///    j. Set templateRemainder to the substring of templateRemainder from
///    refLength.
///    k. Set result to the string-concatenation of result and refReplacement.
/// 6. Return result.
///
/// `captures` holds each capture, `None` for undefined. `named` is `None` for
/// an undefined namedCaptures, else the lookup `? Get(namedCaptures,
/// groupName)` then ToString (the empty string for `undefined`).
///
/// # Errors
/// What `named` returns.
pub fn get_substitution(
    matched: &[u16],
    str_units: &[u16],
    position: usize,
    captures: &[Option<Vec<u16>>],
    mut named: Option<NamedLookup<'_>>,
    template: &[u16],
) -> Result<Vec<u16>, Abrupt> {
    const DOLLAR: u16 = 0x24;
    let digit = |u: Option<&u16>| -> Option<usize> {
        u.and_then(|d| d.checked_sub(0x30))
            .filter(|d| *d < 10)
            .map(usize::from)
    };
    let mut result = Vec::new();
    let mut i = 0usize;
    while let Some(&c) = template.get(i) {
        let next = template.get(i.saturating_add(1));
        if c != DOLLAR {
            result.push(c);
            i = i.saturating_add(1);
            continue;
        }
        match next.copied() {
            Some(0x24) => {
                result.push(DOLLAR);
                i = i.saturating_add(2);
            }
            Some(0x60) => {
                result.extend_from_slice(str_units.get(..position).unwrap_or(&[]));
                i = i.saturating_add(2);
            }
            Some(0x26) => {
                result.extend_from_slice(matched);
                i = i.saturating_add(2);
            }
            Some(0x27) => {
                let tail = position.saturating_add(matched.len()).min(str_units.len());
                result.extend_from_slice(str_units.get(tail..).unwrap_or(&[]));
                i = i.saturating_add(2);
            }
            Some(0x3C) if named.is_some() => {
                let gt = template
                    .iter()
                    .skip(i)
                    .position(|u| *u == 0x3E)
                    .map(|p| p.saturating_add(i));
                match (gt, named.as_mut()) {
                    (Some(gt), Some(lookup)) => {
                        let name = template.get(i.saturating_add(2)..gt).unwrap_or(&[]);
                        result.extend(lookup(name)?);
                        i = gt.saturating_add(1);
                    }
                    _ => {
                        result.push(DOLLAR);
                        i = i.saturating_add(1);
                    }
                }
            }
            _ => {
                if let Some(d1) = digit(next) {
                    let d2 = digit(template.get(i.saturating_add(2)));
                    let (mut count, mut index) = match d2 {
                        Some(d2) => (2usize, d1.saturating_mul(10).saturating_add(d2)),
                        None => (1usize, d1),
                    };
                    if index > captures.len() && count == 2 {
                        count = 1;
                        index = d1;
                    }
                    let end = i.saturating_add(1).saturating_add(count);
                    if (1..=captures.len()).contains(&index) {
                        if let Some(Some(cap)) = captures.get(index.saturating_sub(1)) {
                            result.extend_from_slice(cap);
                        }
                    } else {
                        result.extend_from_slice(template.get(i..end).unwrap_or(&[]));
                    }
                    i = end;
                } else {
                    // "$<" without named captures, and a lone "$": the
                    // dollar sign itself (steps 5.g.ii and 5.h).
                    result.push(DOLLAR);
                    i = i.saturating_add(1);
                }
            }
        }
    }
    Ok(result)
}

/// `String.prototype.replace ( searchValue, replaceValue )`, §22.1.3.19†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If searchValue is neither undefined nor null, then
///    a. Let replacer be ? GetMethod(searchValue, @@replace).
///    b. If replacer is not undefined, then
///    i. Return ? Call(replacer, searchValue, « O, replaceValue »).
/// 3. Let string be ? ToString(O).
/// 4. Let searchString be ? ToString(searchValue).
/// 5. Let functionalReplace be IsCallable(replaceValue).
/// 6. If functionalReplace is false, then
///    a. Set replaceValue to ? ToString(replaceValue).
/// 7. Let searchLength be the length of searchString.
/// 8. Let position be StringIndexOf(string, searchString, 0).
/// 9. If position is not-found, return string.
/// 10. Let preceding be the substring of string from 0 to position.
/// 11. Let following be the substring of string from position + searchLength.
/// 12. If functionalReplace is true, then
///     a. Let replacement be ? ToString(? Call(replaceValue, undefined, «
///     searchString, 𝔽(position), string »)).
/// 13. Else,
///     a. Assert: replaceValue is a String.
///     b. Let captures be a new empty List.
///     c. Let replacement be ! GetSubstitution(searchString, string,
///     position, captures, undefined, replaceValue).
/// 14. Return the string-concatenation of preceding, replacement, and
///     following.
fn replace(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.replace")?;
    let (search_value, replace_value) = (arg(args, 0), arg(args, 1));
    if let Some(v) = delegate(vm, search_value, wk::REPLACE, this, &[replace_value])? {
        return Ok(v);
    }
    let s = vm.to_js_string(this)?;
    let search = vm.to_js_string(search_value)?;
    let functional = vm.heap().is_callable(replace_value);
    let template = if functional {
        Vec::new()
    } else {
        units(&vm.to_js_string(replace_value)?)
    };
    let (su, needle) = (units(&s), units(&search));
    let Some(position) = string_index_of(&su, &needle, 0) else {
        return js_string(vm, s);
    };
    let replacement = replacement_at(
        vm,
        (&su, s.clone()),
        (&needle, search),
        position,
        (functional, replace_value, &template),
    )?;
    let mut out = su.get(..position).unwrap_or(&[]).to_vec();
    out.extend(replacement);
    out.extend_from_slice(
        su.get(position.saturating_add(needle.len())..)
            .unwrap_or(&[]),
    );
    units_value(vm, &out)
}

/// The replacement of one match at `position` (step 12 or 13 of `replace`,
/// step 14.b or 14.c of `replaceAll`).
fn replacement_at(
    vm: &mut Vm,
    (su, s): (&[u16], JsString),
    (needle, search): (&[u16], JsString),
    position: usize,
    (functional, replace_value, template): (bool, Value, &[u16]),
) -> Result<Vec<u16>, Abrupt> {
    if functional {
        let sv = js_string(vm, search)?;
        let whole = js_string(vm, s)?;
        let r = vm.call(
            replace_value,
            Value::UNDEFINED,
            &[sv, number(position as f64), whole],
        )?;
        Ok(units(&vm.to_js_string(r)?))
    } else {
        get_substitution(needle, su, position, &[], None, template)
    }
}

/// `String.prototype.replaceAll ( searchValue, replaceValue )`, §22.1.3.20†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If searchValue is neither undefined nor null, then
///    a. Let isRegExp be ? IsRegExp(searchValue).
///    b. If isRegExp is true, then
///    i. Let flags be ? Get(searchValue, "flags").
///    ii. Perform ? RequireObjectCoercible(flags).
///    iii. If ? ToString(flags) does not contain "g", throw a TypeError
///    exception.
///    c. Let replacer be ? GetMethod(searchValue, @@replace).
///    d. If replacer is not undefined, then
///    i. Return ? Call(replacer, searchValue, « O, replaceValue »).
/// 3. Let string be ? ToString(O).
/// 4. Let searchString be ? ToString(searchValue).
/// 5. Let functionalReplace be IsCallable(replaceValue).
/// 6. If functionalReplace is false, then
///    a. Set replaceValue to ? ToString(replaceValue).
/// 7. Let searchLength be the length of searchString.
/// 8. Let advanceBy be max(1, searchLength).
/// 9. Let matchPositions be a new empty List.
/// 10. Let position be StringIndexOf(string, searchString, 0).
/// 11. Repeat, while position is not not-found,
///     a. Append position to matchPositions.
///     b. Set position to StringIndexOf(string, searchString, position +
///     advanceBy).
/// 12. Let endOfLastMatch be 0.
/// 13. Let result be the empty String.
/// 14. For each element p of matchPositions, do
///     a. Let preserved be the substring of string from endOfLastMatch to p.
///     b. If functionalReplace is true, then
///     i. Let replacement be ? ToString(? Call(replaceValue, undefined, «
///     searchString, 𝔽(p), string »)).
///     c. Else,
///     i. Assert: replaceValue is a String.
///     ii. Let captures be a new empty List.
///     iii. Let replacement be ! GetSubstitution(searchString, string, p,
///     captures, undefined, replaceValue).
///     d. Set result to the string-concatenation of result, preserved, and
///     replacement.
///     e. Set endOfLastMatch to p + searchLength.
/// 15. If endOfLastMatch < the length of string, then
///     a. Set result to the string-concatenation of result and the substring
///     of string from endOfLastMatch.
/// 16. Return result.
fn replace_all(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.replaceAll")?;
    let (search_value, replace_value) = (arg(args, 0), arg(args, 1));
    if search_value != Value::UNDEFINED && search_value != Value::NULL {
        require_global_flag(vm, search_value, "replaceAll")?;
    }
    if let Some(v) = delegate(vm, search_value, wk::REPLACE, this, &[replace_value])? {
        return Ok(v);
    }
    let s = vm.to_js_string(this)?;
    let search = vm.to_js_string(search_value)?;
    let functional = vm.heap().is_callable(replace_value);
    let template = if functional {
        Vec::new()
    } else {
        units(&vm.to_js_string(replace_value)?)
    };
    let (su, needle) = (units(&s), units(&search));
    let advance = needle.len().max(1);
    let mut positions = Vec::new();
    let mut pos = string_index_of(&su, &needle, 0);
    while let Some(p) = pos {
        positions.push(p);
        pos = string_index_of(&su, &needle, p.saturating_add(advance));
    }
    let mut end_of_last = 0usize;
    let mut result: Vec<u16> = Vec::new();
    for p in positions {
        vm.charge_step()?;
        result.extend_from_slice(su.get(end_of_last..p).unwrap_or(&[]));
        let r = replacement_at(
            vm,
            (&su, s.clone()),
            (&needle, search.clone()),
            p,
            (functional, replace_value, &template),
        )?;
        result.extend(r);
        if result.len() > MAX_LENGTH {
            return Err(vm.range_error("Invalid string length"));
        }
        end_of_last = p.saturating_add(needle.len());
    }
    if end_of_last < su.len() {
        result.extend_from_slice(su.get(end_of_last..).unwrap_or(&[]));
    }
    units_value(vm, &result)
}

/// `String.prototype.slice ( start, end )`, §22.1.3.21†:
/// 1 and 2. As above.
/// 3. Let len be the length of S.
/// 4. Let intStart be ? ToIntegerOrInfinity(start).
/// 5. If intStart = -∞, let from be 0.
/// 6. Else if intStart < 0, let from be max(len + intStart, 0).
/// 7. Else, let from be min(intStart, len).
/// 8. If end is undefined, let intEnd be len; else let intEnd be ?
///    ToIntegerOrInfinity(end).
/// 9. If intEnd = -∞, let to be 0.
/// 10. Else if intEnd < 0, let to be max(len + intEnd, 0).
/// 11. Else, let to be min(intEnd, len).
/// 12. If from ≥ to, return the empty String.
/// 13. Return the substring of S from from to to.
fn slice(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "slice")?;
    let len = len_of(&s);
    let relative = |n: f64| -> f64 {
        if n == f64::NEG_INFINITY {
            0.0
        } else if n < 0.0 {
            (len + n).max(0.0)
        } else {
            n.min(len)
        }
    };
    let int_start = to_integer_or_infinity(vm, arg(args, 0))?;
    let from = relative(int_start);
    let end = arg(args, 1);
    let to = if end == Value::UNDEFINED {
        len
    } else {
        relative(to_integer_or_infinity(vm, end)?)
    };
    if from >= to {
        return string(vm, "");
    }
    js_string(vm, s.substring(from as usize, to as usize))
}

/// `String.prototype.split ( separator, limit )`, §22.1.3.23†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. If separator is neither undefined nor null, then
///    a. Let splitter be ? GetMethod(separator, @@split).
///    b. If splitter is not undefined, then
///    i. Return ? Call(splitter, separator, « O, limit »).
/// 3. Let S be ? ToString(O).
/// 4. If limit is undefined, let lim be 2^32 - 1; else let lim be ℝ(?
///    ToUint32(limit)).
/// 5. Let R be ? ToString(separator).
/// 6. If lim = 0, then
///    a. Return CreateArrayFromList(« »).
/// 7. If separator is undefined, then
///    a. Return CreateArrayFromList(« S »).
/// 8. Let separatorLength be the length of R.
/// 9. If separatorLength = 0, then
///    a. Let strLen be the length of S.
///    b. Let outLen be the result of clamping lim between 0 and strLen.
///    c. Let head be the substring of S from 0 to outLen.
///    d. Let codeUnits be a List consisting of the sequence of code units
///    that are the elements of head.
///    e. Return CreateArrayFromList(codeUnits).
/// 10. If S is the empty String, return CreateArrayFromList(« S »).
/// 11. Let substrings be a new empty List.
/// 12. Let i be 0.
/// 13. Let j be StringIndexOf(S, R, 0).
/// 14. Repeat, while j is not not-found,
///     a. Let T be the substring of S from i to j.
///     b. Append T to substrings.
///     c. If the number of elements in substrings is lim, return
///     CreateArrayFromList(substrings).
///     d. Set i to j + separatorLength.
///     e. Set j to StringIndexOf(S, R, i).
/// 15. Let T be the substring of S from i.
/// 16. Append T to substrings.
/// 17. Return CreateArrayFromList(substrings).
fn split(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    require_object_coercible(vm, this, "String.prototype.split")?;
    let (separator, limit) = (arg(args, 0), arg(args, 1));
    if let Some(v) = delegate(vm, separator, wk::SPLIT, this, &[limit])? {
        return Ok(v);
    }
    let s = vm.to_js_string(this)?;
    let lim: u64 = if limit == Value::UNDEFINED {
        4_294_967_295
    } else {
        let n = vm.to_number(limit)?;
        u64::from(clazel_js_vm::numeric::to_uint32(
            clazel_js_vm::numeric::narrow(n),
        ))
    };
    let r = vm.to_js_string(separator)?;
    if lim == 0 {
        return vm.create_array_from_list(&[]);
    }
    if separator == Value::UNDEFINED {
        let sv = js_string(vm, s)?;
        return vm.create_array_from_list(&[sv]);
    }
    let su = units(&s);
    let ru = units(&r);
    let mut out: Vec<Value> = Vec::new();
    if ru.is_empty() {
        let n = usize::try_from(lim).unwrap_or(usize::MAX).min(su.len());
        for u in su.iter().take(n) {
            vm.charge_step()?;
            let one = JsString::from_units(&[*u]).map_err(|_| Abrupt::OutOfMemory)?;
            out.push(js_string(vm, one)?);
        }
        return vm.create_array_from_list(&out);
    }
    if su.is_empty() {
        let sv = js_string(vm, s)?;
        return vm.create_array_from_list(&[sv]);
    }
    let mut i = 0usize;
    let mut j = string_index_of(&su, &ru, 0);
    while let Some(jj) = j {
        vm.charge_step()?;
        let t = s.substring(i, jj);
        out.push(js_string(vm, t)?);
        if out.len() as u64 == lim {
            return vm.create_array_from_list(&out);
        }
        i = jj.saturating_add(ru.len());
        j = string_index_of(&su, &ru, i);
    }
    let t = s.substring(i, su.len());
    out.push(js_string(vm, t)?);
    vm.create_array_from_list(&out)
}

/// `String.prototype.startsWith ( searchString [ , position ] )`,
/// §22.1.3.24†:
/// 1 and 2. As above.
/// 3 to 5. As `endsWith`'s.
/// 6. Let len be the length of S.
/// 7. If position is undefined, let pos be 0; else let pos be ?
///    ToIntegerOrInfinity(position).
/// 8. Let start be the result of clamping pos between 0 and len.
/// 9. Let searchLength be the length of searchStr.
/// 10. If searchLength = 0, return true.
/// 11. Let end be start + searchLength.
/// 12. If end > len, return false.
/// 13. Let substring be the substring of S from start to end.
/// 14. If substring is searchStr, return true.
/// 15. Return false.
fn starts_with(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "startsWith")?;
    let search = search_string(vm, arg(args, 0), "startsWith")?;
    let len = len_of(&s);
    let pos = to_integer_or_infinity(vm, arg(args, 1))?;
    let start = pos.clamp(0.0, len) as usize;
    let end = start.saturating_add(search.len());
    if end > s.len() {
        return Ok(Value::FALSE);
    }
    Ok(Value::boolean(s.substring(start, end) == search))
}

/// `String.prototype.substr ( start, length )`, Annex B §B.2.2.1†:
/// 1 and 2. As above.
/// 3. Let size be the length of S.
/// 4. Let intStart be ? ToIntegerOrInfinity(start).
/// 5. If intStart = -∞, set intStart to 0.
/// 6. Else if intStart < 0, set intStart to max(size + intStart, 0).
/// 7. Else, set intStart to min(intStart, size).
/// 8. If length is undefined, let intLength be size; otherwise let intLength
///    be ? ToIntegerOrInfinity(length).
/// 9. Set intLength to the result of clamping intLength between 0 and size.
/// 10. Let intEnd be min(intStart + intLength, size).
/// 11. Return the substring of S from intStart to intEnd.
fn substr(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "substr")?;
    let size = len_of(&s);
    let int_start = to_integer_or_infinity(vm, arg(args, 0))?;
    let int_start = if int_start == f64::NEG_INFINITY {
        0.0
    } else if int_start < 0.0 {
        (size + int_start).max(0.0)
    } else {
        int_start.min(size)
    };
    let int_length = if arg(args, 1) == Value::UNDEFINED {
        size
    } else {
        to_integer_or_infinity(vm, arg(args, 1))?
    }
    .clamp(0.0, size);
    let int_end = (int_start + int_length).min(size);
    if int_start >= int_end {
        return string(vm, "");
    }
    js_string(vm, s.substring(int_start as usize, int_end as usize))
}

/// `String.prototype.substring ( start, end )`, §22.1.3.25†:
/// 1 and 2. As above.
/// 3. Let len be the length of S.
/// 4. Let intStart be ? ToIntegerOrInfinity(start).
/// 5. If end is undefined, let intEnd be len; else let intEnd be ?
///    ToIntegerOrInfinity(end).
/// 6. Let finalStart be the result of clamping intStart between 0 and len.
/// 7. Let finalEnd be the result of clamping intEnd between 0 and len.
/// 8. Let from be min(finalStart, finalEnd).
/// 9. Let to be max(finalStart, finalEnd).
/// 10. Return the substring of S from from to to.
fn substring(vm: &mut Vm, this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "substring")?;
    let len = len_of(&s);
    let int_start = to_integer_or_infinity(vm, arg(args, 0))?;
    let end = arg(args, 1);
    let int_end = if end == Value::UNDEFINED {
        len
    } else {
        to_integer_or_infinity(vm, end)?
    };
    let final_start = int_start.clamp(0.0, len);
    let final_end = int_end.clamp(0.0, len);
    let (from, to) = (final_start.min(final_end), final_start.max(final_end));
    js_string(vm, s.substring(from as usize, to as usize))
}

/// The case conversion of `toLowerCase` and `toUpperCase` (§22.1.3.28†,
/// §22.1.3.31†):
/// 1 and 2. As above.
/// 3. Let sText be StringToCodePoints(S).
/// 4. Let lowerText be toLowercase(sText) according to the Unicode Default
///    Case Conversion algorithm.
/// 5. Let L be CodePointsToString(lowerText).
/// 6. Return L.
///
/// The runs of well-formed text go through Rust's conversion (see the module
/// header); each lone surrogate is copied as it is.
fn convert_case(vm: &mut Vm, this: Value, method: &str, upper: bool) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, method)?;
    let mut out: Vec<u16> = Vec::with_capacity(s.len());
    let mut run = String::new();
    let flush = |run: &mut String, out: &mut Vec<u16>| {
        let conv = if upper {
            run.to_uppercase()
        } else {
            run.to_lowercase()
        };
        out.extend(conv.encode_utf16());
        run.clear();
    };
    let mut k = 0usize;
    while k < s.len() {
        let (cp, n) = code_point_at(&s, k);
        match char::from_u32(cp) {
            Some(c) => run.push(c),
            None => {
                flush(&mut run, &mut out);
                // A lone surrogate: CodePointAt gave its one unit.
                out.push(u16::try_from(cp).unwrap_or(0xFFFD));
            }
        }
        k = k.saturating_add(n.max(1));
    }
    flush(&mut run, &mut out);
    units_value(vm, &out)
}

fn to_lower_case(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    convert_case(vm, this, "toLowerCase", false)
}

fn to_upper_case(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    convert_case(vm, this, "toUpperCase", true)
}

/// Whether a code unit is WhiteSpace (§12.2†: TAB, VT, FF, ZWNBSP and the
/// Space_Separator code points) or a LineTerminator (§12.3†: LF, CR, LS,
/// PS). Every such code point is in the BMP, so a unit test suffices.
fn is_trim_space(u: u16) -> bool {
    matches!(
        u,
        0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000
            ..=0x200A | 0x2028 | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
    )
}

/// TrimString ( string, where ), §22.1.3.32.1†:
/// 1. Let str be ? RequireObjectCoercible(string).
/// 2. Let S be ? ToString(str).
/// 3. If where is start, then
///    a. Let T be the String value that is a copy of S with leading white
///    space removed.
/// 4. Else if where is end, then
///    a. Let T be the String value that is a copy of S with trailing white
///    space removed.
/// 5. Else,
///    a. Assert: where is start+end.
///    b. Let T be the String value that is a copy of S with both leading and
///    trailing white space removed.
/// 6. Return T.
///
/// "White space" is WhiteSpace and LineTerminator ([`is_trim_space`]).
fn trim_string(
    vm: &mut Vm,
    this: Value,
    method: &str,
    start: bool,
    end: bool,
) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, method)?;
    let u = units(&s);
    let mut from = 0usize;
    let mut to = u.len();
    if start {
        while u.get(from).is_some_and(|c| is_trim_space(*c)) {
            from = from.saturating_add(1);
        }
    }
    if end {
        while to > from
            && u.get(to.saturating_sub(1))
                .is_some_and(|c| is_trim_space(*c))
        {
            to = to.saturating_sub(1);
        }
    }
    js_string(vm, s.substring(from, to))
}

/// `String.prototype.trim ( )`, §22.1.3.33†:
/// 1. Let S be the this value.
/// 2. Return ? TrimString(S, start+end).
fn trim(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    trim_string(vm, this, "trim", true, true)
}

/// `String.prototype.trimEnd ( )`, §22.1.3.34†:
/// 1. Let S be the this value.
/// 2. Return ? TrimString(S, end).
fn trim_end(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    trim_string(vm, this, "trimEnd", false, true)
}

/// `String.prototype.trimStart ( )`, §22.1.3.35†:
/// 1. Let S be the this value.
/// 2. Return ? TrimString(S, start).
fn trim_start(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    trim_string(vm, this, "trimStart", true, false)
}

/// `String.prototype [ @@iterator ] ( )`, §22.1.3.36†:
/// 1. Let O be ? RequireObjectCoercible(this value).
/// 2. Let s be ? ToString(O).
/// 3. Let closure be a new Abstract Closure ... (the code point steps of
///    [`crate::iterator`]'s `next`).
/// 4. Return CreateIteratorFromClosure(closure, "%StringIteratorPrototype%",
///    %StringIteratorPrototype%).
fn iterator(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let s = this_string(vm, this, "[Symbol.iterator]")?;
    let sv = js_string(vm, s)?;
    create_string_iterator(vm, sv)
}
