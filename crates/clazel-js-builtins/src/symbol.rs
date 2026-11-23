//! `Symbol` (§20.4†): the constructor, `Symbol.for`, `Symbol.keyFor`, the
//! well-known symbols as properties of the constructor, and
//! `Symbol.prototype.toString`, `valueOf`, `@@toPrimitive` and
//! `@@toStringTag`.
//!
//! The Symbol values themselves are the VM's ([`Vm::new_symbol`],
//! [`Vm::well_known_symbol`]). `Symbol.prototype.description` is the accessor
//! property of §20.4.3.2†. The GlobalSymbolRegistry (§20.4.2.2.1†) is an object without a prototype,
//! keyed by the registered strings, that only the VM's intrinsics table
//! holds ([`Intrinsic::SymbolRegistry`]).

use crate::util::{CONSTANT, arg, constructor, define, js_string, method, string};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::symbol::{self as wk, SymbolId};
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// The names of the well-known symbols, as properties of `Symbol`
/// (§20.4.2†), with their ids.
const WELL_KNOWN: [(&str, SymbolId); 13] = [
    ("asyncIterator", wk::ASYNC_ITERATOR),
    ("hasInstance", wk::HAS_INSTANCE),
    ("isConcatSpreadable", wk::IS_CONCAT_SPREADABLE),
    ("iterator", wk::ITERATOR),
    ("match", wk::MATCH),
    ("matchAll", wk::MATCH_ALL),
    ("replace", wk::REPLACE),
    ("search", wk::SEARCH),
    ("species", wk::SPECIES),
    ("split", wk::SPLIT),
    ("toPrimitive", wk::TO_PRIMITIVE),
    ("toStringTag", wk::TO_STRING_TAG),
    ("unscopables", wk::UNSCOPABLES),
];

/// Installs `Symbol` and `Symbol.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §20.4.3†: the prototype is an ordinary object (not a Symbol object).
    let proto = vm.new_object()?;
    vm.set_intrinsic(Intrinsic::SymbolPrototype, proto);
    let ctor = constructor(vm, "Symbol", 0, symbol, proto)?;
    // §20.4.2†: each well-known symbol is { [[Writable]]: false,
    // [[Enumerable]]: false, [[Configurable]]: false }.
    for (name, id) in WELL_KNOWN {
        let s = vm.well_known_symbol(id);
        define(vm, ctor, name, s, CONSTANT)?;
    }
    method(vm, ctor, "for", 1, symbol_for)?;
    method(vm, ctor, "keyFor", 1, key_for)?;
    method(vm, proto, "toString", 0, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    let kd = crate::util::key(vm, "description")?;
    crate::util::accessor(vm, proto, kd, "description", Some(get_description), None)?;
    // §20.4.3.5† `Symbol.prototype [ @@toPrimitive ] ( hint )`: its `name`
    // is "[Symbol.toPrimitive]"; { [[Writable]]: false, [[Configurable]]:
    // true }.
    let tp = vm.new_native("[Symbol.toPrimitive]", 1, value_of)?;
    let ktp = vm.well_known_key(wk::TO_PRIMITIVE)?;
    vm.heap_mut()
        .define(proto, ktp, tp, Attrs(Attrs::CONFIGURABLE))?;
    // §20.4.3.6† `Symbol.prototype [ @@toStringTag ]`: "Symbol",
    // { [[Writable]]: false, [[Enumerable]]: false, [[Configurable]]: true }.
    to_string_tag(vm, proto, "Symbol")?;
    let registry = vm.heap_mut().new_object(Value::NULL, ObjKind::Plain)?;
    vm.set_intrinsic(Intrinsic::SymbolRegistry, registry);
    crate::util::global(vm, "Symbol", ctor)
}

/// Defines `obj[@@toStringTag]` as `tag`, { [[Writable]]: false,
/// [[Enumerable]]: false, [[Configurable]]: true }, as every built-in tag is.
///
/// # Errors
/// As [`crate::install`].
pub fn to_string_tag(vm: &mut Vm, obj: Value, tag: &str) -> Result<(), Abrupt> {
    let k = vm.well_known_key(wk::TO_STRING_TAG)?;
    let t = string(vm, tag)?;
    Ok(vm
        .heap_mut()
        .define(obj, k, t, Attrs(Attrs::CONFIGURABLE))?)
}

/// `Symbol ( [ description ] )`, §20.4.1.1†:
/// 1. If NewTarget is not undefined, throw a TypeError exception.
/// 2. If description is undefined, let descString be undefined.
/// 3. Else, let descString be ? ToString(description).
/// 4. Return a new Symbol whose [[Description]] is descString.
fn symbol(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if vm.new_target() != Value::UNDEFINED {
        return Err(vm.type_error("Symbol is not a constructor"));
    }
    let d = arg(args, 0);
    let desc = if d == Value::UNDEFINED {
        Value::UNDEFINED
    } else {
        let s = vm.to_js_string(d)?;
        js_string(vm, s)?
    };
    vm.new_symbol(desc)
}

/// The registry object (see the module header).
fn registry(vm: &mut Vm) -> Result<Value, Abrupt> {
    let r = vm.intrinsic(Intrinsic::SymbolRegistry);
    if vm.heap().is_object(r) {
        Ok(r)
    } else {
        Err(Abrupt::Internal(
            "the global symbol registry is not installed",
        ))
    }
}

/// `Symbol.for ( key )`, §20.4.2.2†:
/// 1. Let stringKey be ? ToString(key).
/// 2. For each element e of the GlobalSymbolRegistry List, do
///    a. If e.[[Key]] is stringKey, return e.[[Symbol]].
/// 3. Assert: The GlobalSymbolRegistry List does not currently contain an
///    entry for stringKey.
/// 4. Let newSymbol be a new Symbol whose [[Description]] is stringKey.
/// 5. Append the GlobalSymbolRegistry Record { [[Key]]: stringKey,
///    [[Symbol]]: newSymbol } to the GlobalSymbolRegistry List.
/// 6. Return newSymbol.
fn symbol_for(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let s = vm.to_js_string(arg(args, 0))?;
    let reg = registry(vm)?;
    let k = vm.heap_mut().intern(&s)?;
    if let Some(f) = vm.heap().find(reg, k)? {
        return vm
            .heap()
            .slot(f.holder, f.slot)
            .ok_or(Abrupt::Internal("registry slot"));
    }
    let desc = js_string(vm, s)?;
    let sym = vm.new_symbol(desc)?;
    vm.heap_mut().define(reg, k, sym, Attrs(0))?;
    Ok(sym)
}

/// `Symbol.keyFor ( sym )`, §20.4.2.6†:
/// 1. If sym is not a Symbol, throw a TypeError exception.
/// 2. Return KeyForSymbol(sym): for each element e of the
///    GlobalSymbolRegistry List, if SameValue(e.[[Symbol]], sym) is true,
///    return e.[[Key]]; else undefined.
fn key_for(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let sym = arg(args, 0);
    if !vm.heap().is_symbol(sym) {
        return Err(vm.type_error("Symbol.keyFor: not a symbol"));
    }
    let reg = registry(vm)?;
    for (k, _, v) in vm.heap().own_properties(reg) {
        if v == sym {
            return vm.key_value(k);
        }
    }
    Ok(Value::UNDEFINED)
}

/// ThisSymbolValue ( value ), §20.4.3.4.1†:
/// 1. If value is a Symbol, return value.
/// 2. If value is an Object and value has a [[SymbolData]] internal slot,
///    then a. Let s be value.[[SymbolData]]. b. Assert: s is a Symbol.
///    c. Return s.
/// 3. Throw a TypeError exception.
fn this_symbol_value(vm: &mut Vm, v: Value) -> Result<Value, Abrupt> {
    if vm.heap().is_symbol(v) {
        return Ok(v);
    }
    if let Some(ObjKind::Primitive(p)) = vm.heap().obj(v).map(|o| o.kind)
        && vm.heap().is_symbol(p)
    {
        return Ok(p);
    }
    Err(vm.type_error("not a Symbol"))
}

/// `Symbol.prototype.toString ( )`, §20.4.3.3†:
/// 1. Let sym be ? ThisSymbolValue(this value).
/// 2. Return SymbolDescriptiveString(sym).
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let sym = this_symbol_value(vm, this)?;
    let s = vm.symbol_descriptive_string(sym);
    js_string(vm, s)
}

/// `Symbol.prototype.valueOf ( )`, §20.4.3.4†, and `Symbol.prototype [
/// @@toPrimitive ] ( hint )`, §20.4.3.5† (which ignores the hint):
/// 1. Return ? ThisSymbolValue(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    this_symbol_value(vm, this)
}

/// `get Symbol.prototype.description`, §20.4.3.2†:
/// 1. Let s be the this value.
/// 2. Let sym be ? ThisSymbolValue(s).
/// 3. Return sym.[[Description]].
fn get_description(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let sym = this_symbol_value(vm, this)?;
    Ok(vm
        .heap()
        .symbol(sym)
        .map_or(Value::UNDEFINED, |s| s.description))
}
