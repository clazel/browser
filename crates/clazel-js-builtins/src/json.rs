//! `JSON` (§25.5†): `JSON.parse` and `JSON.stringify`, over `clazel-json`.
//!
//! `JSON.parse` reads the text with `clazel-json`'s parser (ECMA-404, and the
//! parse step of §25.5.1† `JSON.parse`, proven against the grammar there);
//! this module builds the values and runs the reviver. `JSON.stringify` quotes
//! strings with `clazel-json`'s `quote` (QuoteJSONString, §25.5.2.3†) and
//! implements §25.5.2† itself.
//!
//! Listed deviations:
//!
//! - **The nesting bound.** `clazel-json` reads at most 512 levels of arrays
//!   and objects; deeper text is a `SyntaxError` (phase-7.md 7.11, listed).
//!   `JSON.stringify` stops at 128 levels with a `RangeError`, where the
//!   standard has no bound (it recurses on the host stack, which must not
//!   overflow; an unoptimised frame is several KB, and tests run on 2 MB).
//!   The embedder's nesting limit (`Vm::nesting_depth_limit`, phase-7.md
//!   7.19) lowers both: a parsed text deeper than it is the same
//!   `SyntaxError`, and `JSON.stringify` stops at the smaller of the two.
//! - No `BigInt` (`toJSON` is looked up on Objects only) and no Symbols (a
//!   Symbol is never a value here), so those steps of the algorithms do not
//!   exist yet.
//! - The reviver's third argument (the source text context of the JSON
//!   parse-with-source proposal) is not passed.

use crate::util::{arg, js_string, method, number, to_integer_or_infinity};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::value::{Decoded, Value};
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Vm};
use clazel_json::tree::Json;

/// The deepest nesting `JSON.stringify` serializes.
const MAX_DEPTH: usize = 128;

/// Installs `JSON`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let json = vm.new_object()?;
    method(vm, json, "parse", 2, parse)?;
    method(vm, json, "stringify", 3, stringify)?;
    // §25.5.3†: `JSON[@@toStringTag]` is "JSON" (no Symbols yet, so absent).
    crate::util::global(vm, "JSON", json)
}

fn units_of(vm: &mut Vm, v: Value) -> Result<Vec<u16>, Abrupt> {
    Ok(vm.to_js_string(v)?.units().collect())
}

fn key_of(vm: &mut Vm, units: &[u16]) -> Result<Key, Abrupt> {
    let s = JsString::from_units(units).map_err(|_| Abrupt::OutOfMemory)?;
    Ok(vm.heap_mut().intern(&s)?)
}

fn str_value(vm: &mut Vm, units: &[u16]) -> Result<Value, Abrupt> {
    let s = JsString::from_units(units).map_err(|_| Abrupt::OutOfMemory)?;
    js_string(vm, s)
}

// ---------------------------------------------------------------------
// JSON.parse
// ---------------------------------------------------------------------

/// `JSON.parse ( text [ , reviver ] )`, §25.5.1†:
/// 1. Let jsonString be ? ToString(text).
/// 2. Parse StringToCodePoints(jsonString) as a JSON text as specified in
///    ECMA-404. Throw a SyntaxError exception if it is not a valid JSON text
///    as defined in that specification.
/// 3. to 5. (The script-goal evaluation of the standard's text is replaced by
///    building the value of the JSON text directly: each JSON object member
///    is CreateDataProperty on a new ordinary object, a later duplicate name
///    replacing an earlier value; an array is ArrayCreate and
///    CreateDataProperty of each element; a number is StringToNumber of its
///    text; a string is its code units.)
/// 6. Let unfiltered be the result.
/// 7. If IsCallable(reviver) is true, then a. Let root be
///    OrdinaryObjectCreate(%Object.prototype%). b. Let rootName be the empty
///    String. c. Perform ! CreateDataPropertyOrThrow(root, rootName,
///    unfiltered). d. Return ? InternalizeJSONProperty(root, rootName,
///    reviver).
/// 8. Else, a. Return unfiltered.
fn parse(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let text = units_of(vm, arg(args, 0))?;
    let cps = code_points(&text);
    let Some(tree) = clazel_json::parse::parse(&cps) else {
        return Err(vm.syntax_error("Unexpected token in JSON, or nesting too deep"));
    };
    // The embedder's nesting limit (phase-7.md 7.19), below `clazel-json`'s
    // own fixed bound: past it, the same SyntaxError as past that bound
    // (phase-7.md 7.11's listed deviation).
    let limit = usize::try_from(vm.nesting_depth_limit()).unwrap_or(usize::MAX);
    if tree_depth(&tree) > limit {
        return Err(vm.syntax_error("JSON.parse: nesting too deep"));
    }
    let unfiltered = build(vm, &tree)?;
    let reviver = arg(args, 1);
    if vm.heap().is_callable(reviver) {
        let root = vm.new_object()?;
        let name = key_of(vm, &[])?;
        vm.create_data_property_or_throw(root, name, unfiltered)?;
        return internalize(vm, root, name, reviver);
    }
    Ok(unfiltered)
}

/// How many arrays and objects deep a parsed text nests (a scalar is 0), with
/// an explicit stack rather than recursion.
fn tree_depth(root: &Json) -> usize {
    let mut deepest = 0usize;
    let mut stack: Vec<(&Json, usize)> = vec![(root, 0)];
    while let Some((j, above)) = stack.pop() {
        match j {
            Json::Array(items) => {
                let here = above.saturating_add(1);
                deepest = deepest.max(here);
                stack.extend(items.iter().map(|item| (item, here)));
            }
            Json::Object(members) => {
                let here = above.saturating_add(1);
                deepest = deepest.max(here);
                stack.extend(members.iter().map(|m| (&m.value, here)));
            }
            Json::Null | Json::Bool(_) | Json::Number(_) | Json::String(_) => {}
        }
    }
    deepest
}

/// StringToCodePoints (§6.1.4†): surrogate pairs join; a lone surrogate is
/// its own code point.
fn code_points(units: &[u16]) -> Vec<u32> {
    let mut out = Vec::with_capacity(units.len());
    let mut i = 0usize;
    while let Some(&u) = units.get(i) {
        let next = units.get(i.saturating_add(1)).copied();
        match next {
            Some(lo) if (0xD800..0xDC00).contains(&u) && (0xDC00..0xE000).contains(&lo) => {
                let hi = u32::from(u).saturating_sub(0xD800);
                let lo = u32::from(lo).saturating_sub(0xDC00);
                out.push(
                    hi.saturating_mul(0x400)
                        .saturating_add(lo)
                        .saturating_add(0x10000),
                );
                i = i.saturating_add(2);
            }
            _ => {
                out.push(u32::from(u));
                i = i.saturating_add(1);
            }
        }
    }
    out
}

/// The value of a parsed JSON text.
fn build(vm: &mut Vm, j: &Json) -> Result<Value, Abrupt> {
    match j {
        Json::Null => Ok(Value::NULL),
        Json::Bool(b) => Ok(Value::boolean(*b)),
        Json::Number(text) => {
            let s: String = text.iter().filter_map(|c| char::from_u32(*c)).collect();
            Ok(number(clazel_js_number::string_to_number(&s)))
        }
        Json::String(u) => str_value(vm, u),
        Json::Array(items) => {
            let a = vm.array_create(0.0, None)?;
            for (i, item) in items.iter().enumerate() {
                let v = build(vm, item)?;
                let k = vm.index_key(i as u64)?;
                vm.create_data_property_or_throw(a, k, v)?;
            }
            Ok(a)
        }
        Json::Object(members) => {
            let o = vm.new_object()?;
            for m in members {
                let v = build(vm, &m.value)?;
                let k = key_of(vm, &m.key)?;
                vm.create_data_property_or_throw(o, k, v)?;
            }
            Ok(o)
        }
    }
}

/// EnumerableOwnProperties ( O, key ), §7.3.23†, as a list of keys.
fn enumerable_keys(vm: &Vm, o: Value) -> Vec<Key> {
    vm.heap()
        .own_properties(o)
        .into_iter()
        .filter(|(_, a, _)| a.0 & Attrs::ENUMERABLE != 0)
        .map(|(k, _, _)| k)
        .collect()
}

/// InternalizeJSONProperty ( holder, name, reviver ), §25.5.1.1†:
/// 1. Let val be ? Get(holder, name).
/// 2. If val is an Object, then
///    a. Let isArray be ? IsArray(val).
///    b. If isArray is true, then i. Let len be ? LengthOfArrayLike(val).
///    ii. Let I be 0. iii. Repeat, while I < len, 1. Let prop be !
///    ToString(𝔽(I)). 2. Let newElement be ? InternalizeJSONProperty(val,
///    prop, reviver). 3. If newElement is undefined, then a. Perform ?
///    val.[[Delete]](prop). 4. Else, a. Perform ? CreateDataProperty(val,
///    prop, newElement). 5. Set I to I + 1.
///    c. Else, i. Let keys be ? EnumerableOwnProperties(val, key). ii. For
///    each String P of keys, do 1. Let newElement be ?
///    InternalizeJSONProperty(val, P, reviver). 2. If newElement is
///    undefined, then a. Perform ? val.[[Delete]](P). 3. Else, a. Perform ?
///    CreateDataProperty(val, P, newElement).
/// 3. Return ? Call(reviver, holder, « name, val »).
fn internalize(vm: &mut Vm, holder: Value, name: Key, reviver: Value) -> Result<Value, Abrupt> {
    vm.charge_step()?;
    let val = vm.get_value(holder, name)?;
    if vm.heap().is_object(val) {
        let keys: Vec<Key> = if vm.is_array(val) {
            let lk = key_of(vm, &"length".encode_utf16().collect::<Vec<_>>())?;
            let lv = vm.get_value(val, lk)?;
            let len = to_integer_or_infinity(vm, lv)?.clamp(0.0, 9_007_199_254_740_991.0);
            let mut ks = Vec::new();
            let mut i = 0.0f64;
            while i < len {
                vm.charge_step()?;
                ks.push(vm.index_key(i as u64)?);
                i += 1.0;
            }
            ks
        } else {
            enumerable_keys(vm, val)
        };
        for p in keys {
            let new_element = internalize(vm, val, p, reviver)?;
            if new_element == Value::UNDEFINED {
                vm.delete_property(val, p)?;
            } else {
                vm.create_data_property(val, p, new_element)?;
            }
        }
    }
    let name_v = {
        let s = vm
            .heap()
            .key_string(name)
            .cloned()
            .ok_or(Abrupt::Internal("key"))?;
        js_string(vm, s)?
    };
    vm.call(reviver, holder, &[name_v, val])
}

// ---------------------------------------------------------------------
// JSON.stringify
// ---------------------------------------------------------------------

/// The state of a stringify (§25.5.2†): the ReplacerFunction, the
/// PropertyList, the gap, the indent and the stack.
struct State {
    replacer: Value,
    property_list: Option<Vec<Key>>,
    gap: Vec<u16>,
    indent: Vec<u16>,
    stack: Vec<Value>,
}

/// The primitive inside a Boolean, Number or String wrapper object.
fn wrapped(vm: &Vm, v: Value) -> Option<Value> {
    match vm.heap().obj(v).map(|o| o.kind) {
        Some(ObjKind::Primitive(p)) => Some(p),
        _ => None,
    }
}

/// `JSON.stringify ( value [ , replacer [ , space ] ] )`, §25.5.2†:
/// 1. Let stack be a new empty List.
/// 2. Let indent be the empty String.
/// 3. Let PropertyList be undefined.
/// 4. Let ReplacerFunction be undefined.
/// 5. If replacer is an Object, then
///    a. If IsCallable(replacer) is true, then i. Set ReplacerFunction to
///    replacer.
///    b. Else, i. Let isArray be ? IsArray(replacer). ii. If isArray is true,
///    then 1. Set PropertyList to a new empty List. 2. Let len be ?
///    LengthOfArrayLike(replacer). 3. Let k be 0. 4. Repeat, while k < len, a.
///    Let prop be ! ToString(𝔽(k)). b. Let v be ? Get(replacer, prop). c. Let
///    item be undefined. d. If v is a String, then i. Set item to v. e. Else
///    if v is a Number, then i. Set item to ! ToString(v). f. Else if v is an
///    Object, then i. If v has a [[StringData]] or [[NumberData]] internal
///    slot, set item to ? ToString(v). g. If item is not undefined and
///    PropertyList does not contain item, then i. Append item to
///    PropertyList. h. Set k to k + 1.
/// 6. If space is an Object, then a. If space has a [[NumberData]] internal
///    slot, then i. Set space to ? ToNumber(space). b. Else if space has a
///    [[StringData]] internal slot, then i. Set space to ? ToString(space).
/// 7. If space is a Number, then a. Let spaceMV be ! ToIntegerOrInfinity(space).
///    b. Set spaceMV to min(10, spaceMV). c. If spaceMV < 1, let gap be the
///    empty String; otherwise let gap be the String value containing spaceMV
///    occurrences of the code unit 0x0020 (SPACE).
/// 8. Else if space is a String, then a. If the length of space is 10 or less,
///    let gap be space; otherwise let gap be the substring of space from 0 to
///    10.
/// 9. Else, a. Let gap be the empty String.
/// 10. Let wrapper be OrdinaryObjectCreate(%Object.prototype%).
/// 11. Perform ! CreateDataPropertyOrThrow(wrapper, the empty String, value).
/// 12. Let state be the JSON Serialization Record { [[ReplacerFunction]],
///     [[Stack]], [[Indent]], [[Gap]], [[PropertyList]] }.
/// 13. Return ? SerializeJSONProperty(state, the empty String, wrapper).
fn stringify(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (value, replacer, mut space) = (arg(args, 0), arg(args, 1), arg(args, 2));
    let mut state = State {
        replacer: Value::UNDEFINED,
        property_list: None,
        gap: Vec::new(),
        indent: Vec::new(),
        stack: Vec::new(),
    };
    if vm.heap().is_object(replacer) {
        if vm.heap().is_callable(replacer) {
            state.replacer = replacer;
        } else if vm.is_array(replacer) {
            let lk = key_of(vm, &"length".encode_utf16().collect::<Vec<_>>())?;
            let lv = vm.get_value(replacer, lk)?;
            let len = to_integer_or_infinity(vm, lv)?.clamp(0.0, 9_007_199_254_740_991.0);
            let mut list: Vec<Key> = Vec::new();
            let mut k = 0.0f64;
            while k < len {
                vm.charge_step()?;
                let pk = vm.index_key(k as u64)?;
                let v = vm.get_value(replacer, pk)?;
                let item = if vm.heap().is_string(v) || crate::util::as_number(v).is_some() {
                    Some(units_of(vm, v)?)
                } else if let Some(p) = wrapped(vm, v)
                    && !matches!(p.decode(), Decoded::Bool(_))
                {
                    Some(units_of(vm, v)?)
                } else {
                    None
                };
                if let Some(u) = item {
                    let key = key_of(vm, &u)?;
                    if !list.contains(&key) {
                        list.push(key);
                    }
                }
                k += 1.0;
            }
            state.property_list = Some(list);
        }
    }
    if let Some(p) = wrapped(vm, space) {
        if crate::util::as_number(p).is_some() {
            let n = vm.to_number(space)?;
            space = number(n);
        } else if vm.heap().is_string(p) {
            let s = vm.to_js_string(space)?;
            space = js_string(vm, s)?;
        }
    }
    if let Some(n) = crate::util::as_number(space) {
        let mv = if n.is_nan() { 0.0 } else { n.trunc() }.min(10.0);
        let count = if mv < 1.0 { 0 } else { mv as usize };
        state.gap = vec![0x20; count];
    } else if vm.heap().is_string(space) {
        state.gap = units_of(vm, space)?.into_iter().take(10).collect();
    }
    let wrapper = vm.new_object()?;
    let empty = key_of(vm, &[])?;
    vm.create_data_property_or_throw(wrapper, empty, value)?;
    match serialize_property(vm, &mut state, empty, wrapper)? {
        Some(units) => str_value(vm, &units),
        None => Ok(Value::UNDEFINED),
    }
}

/// SerializeJSONProperty ( state, key, holder ), §25.5.2.2†: the text, or
/// `None` for undefined.
/// 1. Let value be ? Get(holder, key).
/// 2. If value is an Object, then a. Let toJSON be ? GetV(value, "toJSON").
///    b. If IsCallable(toJSON) is true, then i. Set value to ? Call(toJSON,
///    value, « key »).
/// 3. If state.[[ReplacerFunction]] is not undefined, then a. Set value to ?
///    Call(state.[[ReplacerFunction]], holder, « key, value »).
/// 4. If value is an Object, then a. If value has a [[NumberData]] internal
///    slot, then i. Set value to ? ToNumber(value). b. Else if value has a
///    [[StringData]] internal slot, then i. Set value to ? ToString(value).
///    c. Else if value has a [[BooleanData]] internal slot, then i. Set value
///    to value.[[BooleanData]].
/// 5. If value is null, return "null".
/// 6. If value is true, return "true".
/// 7. If value is false, return "false".
/// 8. If value is a String, return QuoteJSONString(value).
/// 9. If value is a Number, then a. If value is finite, return !
///    ToString(value). b. Return "null".
/// 11. If value is an Object and IsCallable(value) is false, then a. Let
///     isArray be ? IsArray(value). b. If isArray is true, return ?
///     SerializeJSONArray(state, value). c. Return ? SerializeJSONObject(state,
///     value).
/// 12. Return undefined.
fn serialize_property(
    vm: &mut Vm,
    state: &mut State,
    key: Key,
    holder: Value,
) -> Result<Option<Vec<u16>>, Abrupt> {
    vm.charge_step()?;
    let mut value = vm.get_value(holder, key)?;
    let key_v = {
        let s = vm
            .heap()
            .key_string(key)
            .cloned()
            .ok_or(Abrupt::Internal("key"))?;
        js_string(vm, s)?
    };
    if vm.heap().is_object(value) {
        let to_json = vm.get_named(value, "toJSON")?;
        if vm.heap().is_callable(to_json) {
            value = vm.call(to_json, value, &[key_v])?;
        }
    }
    if state.replacer != Value::UNDEFINED {
        value = vm.call(state.replacer, holder, &[key_v, value])?;
    }
    if let Some(p) = wrapped(vm, value) {
        value = match p.decode() {
            Decoded::Bool(_) => p,
            Decoded::Int32(_) | Decoded::Double(_) => number(vm.to_number(value)?),
            _ => {
                let s = vm.to_js_string(value)?;
                js_string(vm, s)?
            }
        };
    }
    if value == Value::NULL {
        return Ok(Some("null".encode_utf16().collect()));
    }
    if value == Value::TRUE {
        return Ok(Some("true".encode_utf16().collect()));
    }
    if value == Value::FALSE {
        return Ok(Some("false".encode_utf16().collect()));
    }
    if let Some(s) = vm.heap().string(value) {
        let units: Vec<u16> = s.units().collect();
        return Ok(Some(clazel_json::quote::quote(&units)));
    }
    if let Some(n) = crate::util::as_number(value) {
        return Ok(Some(if n.is_finite() {
            vm.to_js_string(value)?.units().collect()
        } else {
            "null".encode_utf16().collect()
        }));
    }
    if vm.heap().is_object(value) && !vm.heap().is_callable(value) {
        return if vm.is_array(value) {
            serialize_array(vm, state, value).map(Some)
        } else {
            serialize_object(vm, state, value).map(Some)
        };
    }
    Ok(None)
}

/// Pushes `value` on the stack, TypeError for a cycle (§25.5.2.4† step 1,
/// §25.5.2.5† step 1), RangeError past [`MAX_DEPTH`] or the embedder's
/// nesting limit, whichever is smaller (listed deviation; phase-7.md 7.19).
fn enter(vm: &mut Vm, state: &mut State, value: Value) -> Result<(), Abrupt> {
    if state.stack.contains(&value) {
        return Err(vm.type_error("Converting circular structure to JSON"));
    }
    let limit = usize::try_from(vm.nesting_depth_limit())
        .unwrap_or(usize::MAX)
        .min(MAX_DEPTH);
    if state.stack.len() >= limit {
        return Err(vm.range_error("JSON.stringify: nesting too deep"));
    }
    state.stack.push(value);
    Ok(())
}

/// SerializeJSONObject ( state, value ), §25.5.2.4†:
/// 1. If state.[[Stack]] contains value, throw a TypeError exception because
///    the structure is cyclical.
/// 2. Append value to state.[[Stack]].
/// 3. Let stepback be state.[[Indent]].
/// 4. Set state.[[Indent]] to the string-concatenation of state.[[Indent]] and
///    state.[[Gap]].
/// 5. If state.[[PropertyList]] is not undefined, then a. Let K be
///    state.[[PropertyList]].
/// 6. Else, a. Let K be ? EnumerableOwnProperties(value, key).
/// 7. Let partial be a new empty List.
/// 8. For each element P of K, do a. Let strP be ? SerializeJSONProperty(state,
///    P, value). b. If strP is not undefined, then i. Let member be
///    QuoteJSONString(P). ii. Set member to the string-concatenation of member
///    and ":". iii. If state.[[Gap]] is not the empty String, then 1. Set
///    member to the string-concatenation of member and the code unit 0x0020
///    (SPACE). iv. Set member to the string-concatenation of member and strP.
///    v. Append member to partial.
/// 9. If partial is empty, then a. Let final be "{}".
/// 10. Else, a. If state.[[Gap]] is the empty String, then i. Let properties
///     be the String value formed by concatenating all the element Strings of
///     partial with each adjacent pair of Strings separated with the code unit
///     0x002C (COMMA). ii. Let final be the string-concatenation of "{",
///     properties, and "}". b. Else, i. Let separator be the string-concatenation
///     of the code unit 0x002C (COMMA), the code unit 0x000A (LINE FEED), and
///     state.[[Indent]]. ii. Let properties be the String value formed by
///     concatenating all the element Strings of partial with each adjacent pair
///     separated with separator. iii. Let final be the string-concatenation of
///     "{", the code unit 0x000A (LINE FEED), state.[[Indent]], properties, the
///     code unit 0x000A (LINE FEED), stepback, and "}".
/// 11. Remove the last element of state.[[Stack]].
/// 12. Set state.[[Indent]] to stepback.
/// 13. Return final.
fn serialize_object(vm: &mut Vm, state: &mut State, value: Value) -> Result<Vec<u16>, Abrupt> {
    enter(vm, state, value)?;
    let stepback = state.indent.clone();
    state.indent.extend_from_slice(&state.gap.clone());
    let keys: Vec<Key> = match &state.property_list {
        Some(l) => l.clone(),
        None => enumerable_keys(vm, value),
    };
    let mut partial: Vec<Vec<u16>> = Vec::new();
    for p in keys {
        if let Some(str_p) = serialize_property(vm, state, p, value)? {
            let name: Vec<u16> = vm
                .heap()
                .key_string(p)
                .map(|s| s.units().collect())
                .ok_or(Abrupt::Internal("key"))?;
            let mut member = clazel_json::quote::quote(&name);
            member.push(u16::from(b':'));
            if !state.gap.is_empty() {
                member.push(0x20);
            }
            member.extend(str_p);
            partial.push(member);
        }
    }
    let out = wrap(&partial, state, &stepback, b'{', b'}');
    state.stack.pop();
    state.indent = stepback;
    Ok(out)
}

/// Steps 9 and 10 of both serializers: `open`, the members and `close`.
fn wrap(partial: &[Vec<u16>], state: &State, stepback: &[u16], open: u8, close: u8) -> Vec<u16> {
    let (open, close) = (u16::from(open), u16::from(close));
    if partial.is_empty() {
        return vec![open, close];
    }
    let mut out = vec![open];
    let sep: Vec<u16> = if state.gap.is_empty() {
        vec![u16::from(b',')]
    } else {
        let mut s = vec![u16::from(b','), 0x0A];
        s.extend_from_slice(&state.indent);
        s
    };
    if !state.gap.is_empty() {
        out.push(0x0A);
        out.extend_from_slice(&state.indent);
    }
    for (i, m) in partial.iter().enumerate() {
        if i > 0 {
            out.extend_from_slice(&sep);
        }
        out.extend_from_slice(m);
    }
    if !state.gap.is_empty() {
        out.push(0x0A);
        out.extend_from_slice(stepback);
    }
    out.push(close);
    out
}

/// SerializeJSONArray ( state, value ), §25.5.2.6†:
/// 1. If state.[[Stack]] contains value, throw a TypeError exception because
///    the structure is cyclical.
/// 2. Append value to state.[[Stack]].
/// 3. Let stepback be state.[[Indent]].
/// 4. Set state.[[Indent]] to the string-concatenation of state.[[Indent]] and
///    state.[[Gap]].
/// 5. Let partial be a new empty List.
/// 6. Let len be ? LengthOfArrayLike(value).
/// 7. Let index be 0.
/// 8. Repeat, while index < len, a. Let strP be ? SerializeJSONProperty(state,
///    ! ToString(𝔽(index)), value). b. If strP is undefined, then i. Append
///    "null" to partial. c. Else, i. Append strP to partial. d. Set index to
///    index + 1.
/// 9. If partial is empty, then a. Let final be "[]".
/// 10. Else, as step 10 of SerializeJSONObject with "[" and "]" and the
///     elements without names.
/// 11. Remove the last element of state.[[Stack]].
/// 12. Set state.[[Indent]] to stepback.
/// 13. Return final.
fn serialize_array(vm: &mut Vm, state: &mut State, value: Value) -> Result<Vec<u16>, Abrupt> {
    enter(vm, state, value)?;
    let stepback = state.indent.clone();
    state.indent.extend_from_slice(&state.gap.clone());
    let lk = key_of(vm, &"length".encode_utf16().collect::<Vec<_>>())?;
    let lv = vm.get_value(value, lk)?;
    let len = to_integer_or_infinity(vm, lv)?.clamp(0.0, 9_007_199_254_740_991.0);
    let mut partial: Vec<Vec<u16>> = Vec::new();
    let mut index = 0.0f64;
    while index < len {
        let k = vm.index_key(index as u64)?;
        match serialize_property(vm, state, k, value)? {
            Some(s) => partial.push(s),
            None => partial.push("null".encode_utf16().collect()),
        }
        index += 1.0;
    }
    let out = wrap(&partial, state, &stepback, b'[', b']');
    state.stack.pop();
    state.indent = stepback;
    Ok(out)
}
