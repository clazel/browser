//! `Boolean` (§20.3†).

use crate::util::{arg, constructor, method, string};
use clazel_js_heap::value::{Decoded, Value};
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs `Boolean` and `Boolean.prototype`.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    // §20.3.4†: the prototype is itself a Boolean object whose [[BooleanData]]
    // is false.
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    let proto = vm.new_wrapper(Value::FALSE, object_proto)?;
    vm.set_intrinsic(Intrinsic::BooleanPrototype, proto);
    let ctor = constructor(vm, "Boolean", 1, boolean, proto)?;
    method(vm, proto, "toString", 0, to_string)?;
    method(vm, proto, "valueOf", 0, value_of)?;
    crate::util::global(vm, "Boolean", ctor)
}

/// `Boolean ( value )`, §20.3.1.1†:
/// 1. Let b be ToBoolean(value).
/// 2. If NewTarget is undefined, return b.
/// 3. Let O be ? OrdinaryCreateFromConstructor(NewTarget,
///    "%Boolean.prototype%", « [[BooleanData]] »).
/// 4. Set O.[[BooleanData]] to b.
/// 5. Return O.
fn boolean(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let b = Value::boolean(vm.to_boolean(arg(args, 0)));
    let nt = vm.new_target();
    if nt == Value::UNDEFINED {
        return Ok(b);
    }
    vm.create_from_constructor(nt, Intrinsic::BooleanPrototype, ObjKind::Primitive(b))
}

/// thisBooleanValue ( value ), §20.3.3.3.1†:
/// 1. If value is a Boolean, return value.
/// 2. If value is an Object and value has a [[BooleanData]] internal slot,
///    then return value.[[BooleanData]].
/// 3. Throw a TypeError exception.
fn this_boolean_value(vm: &mut Vm, v: Value) -> Result<bool, Abrupt> {
    if let Decoded::Bool(b) = v.decode() {
        return Ok(b);
    }
    if let Some(ObjKind::Primitive(p)) = vm.heap().obj(v).map(|o| o.kind)
        && let Decoded::Bool(b) = p.decode()
    {
        return Ok(b);
    }
    Err(vm.type_error("not a Boolean"))
}

/// `Boolean.prototype.toString ( )`, §20.3.3.2†:
/// 1. Let b be ? thisBooleanValue(this value).
/// 2. If b is true, return "true"; else return "false".
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    let b = this_boolean_value(vm, this)?;
    string(vm, if b { "true" } else { "false" })
}

/// `Boolean.prototype.valueOf ( )`, §20.3.3.3†:
/// 1. Return ? thisBooleanValue(this value).
fn value_of(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::boolean(this_boolean_value(vm, this)?))
}
