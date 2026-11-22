//! `Error` and the native errors (§20.5†): `TypeError`, `RangeError`,
//! `SyntaxError`, `ReferenceError`. The VM's own throws
//! (`Vm::type_error`, ...) build the same objects, from the prototypes
//! installed here.

use crate::util::{METHOD, arg, constructor, define, has_property, key, new_object_with, string};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::value::Value;
use clazel_js_vm::heap::ObjKind;
use clazel_js_vm::interp::{Abrupt, Intrinsic, Vm};

/// Installs the five error constructors and their prototypes.
///
/// # Errors
/// As [`crate::install`].
pub fn install(vm: &mut Vm) -> Result<(), Abrupt> {
    let object_proto = vm.intrinsic(Intrinsic::ObjectPrototype);
    // §20.5.3†: %Error.prototype% is an ordinary object (it has no
    // [[ErrorData]]) with `name` "Error" and `message` "".
    let error_proto = new_object_with(vm, object_proto, ObjKind::Plain)?;
    let error = constructor(vm, "Error", 1, error_constructor, error_proto)?;
    describe(vm, error_proto, "Error")?;
    crate::util::method(vm, error_proto, "toString", 0, to_string)?;
    vm.set_intrinsic(Intrinsic::ErrorPrototype, error_proto);
    crate::util::global(vm, "Error", error)?;
    for (name, which) in [
        ("TypeError", Intrinsic::TypeErrorPrototype),
        ("RangeError", Intrinsic::RangeErrorPrototype),
        ("SyntaxError", Intrinsic::SyntaxErrorPrototype),
        ("ReferenceError", Intrinsic::ReferenceErrorPrototype),
    ] {
        // §20.5.6.2†: the prototype's [[Prototype]] is %Error.prototype%;
        // §20.5.6.1†: the constructor's is %Error%.
        let proto = new_object_with(vm, error_proto, ObjKind::Plain)?;
        let ctor = constructor(vm, name, 1, error_constructor, proto)?;
        vm.heap_mut().set_proto(ctor, error)?;
        describe(vm, proto, name)?;
        vm.set_intrinsic(which, proto);
        crate::util::global(vm, name, ctor)?;
    }
    Ok(())
}

/// The `name` and `message` properties of a prototype (§20.5.3.3†,
/// §20.5.3.2†, §20.5.6.3†, §20.5.6.4†).
fn describe(vm: &mut Vm, proto: Value, name: &str) -> Result<(), Abrupt> {
    let n = string(vm, name)?;
    define(vm, proto, "name", n, METHOD)?;
    let m = string(vm, "")?;
    define(vm, proto, "message", m, METHOD)
}

/// `Error ( message [ , options ] )`, §20.5.1.1†, and
/// `NativeError ( message [ , options ] )`, §20.5.6.1.1† (one function
/// serves all five: the running constructor says which):
/// 1. If NewTarget is undefined, let newTarget be the active function
///    object; else let newTarget be NewTarget.
/// 2. Let O be ? OrdinaryCreateFromConstructor(newTarget, "%Error.prototype%"
///    (or the native error's), « [[ErrorData]] »).
/// 3. If message is not undefined, then
///    a. Let msg be ? ToString(message).
///    b. Perform CreateNonEnumerableDataPropertyOrThrow(O, "message", msg).
/// 4. Perform ? InstallErrorCause(O, options).
/// 5. Return O.
fn error_constructor(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let active = vm.active_function();
    let nt = if vm.new_target() == Value::UNDEFINED {
        active
    } else {
        vm.new_target()
    };
    // The fallback prototype is the running constructor's own `prototype`
    // (the intrinsic of its error type).
    let kp = key(vm, "prototype")?;
    let fallback = vm.get_value(active, kp)?;
    let from_nt = if vm.heap().is_object(nt) {
        vm.get_value(nt, kp)?
    } else {
        Value::UNDEFINED
    };
    let proto = if vm.heap().is_object(from_nt) {
        from_nt
    } else {
        fallback
    };
    let o = new_object_with(vm, proto, ObjKind::Error)?;
    let message = arg(args, 0);
    if message != Value::UNDEFINED {
        let msg = vm.to_js_string(message)?;
        let msg = crate::util::js_string(vm, msg)?;
        define(vm, o, "message", msg, METHOD)?;
    }
    // InstallErrorCause ( O, options ), §20.5.8.1†:
    // 1. If options is an Object and ? HasProperty(options, "cause") is
    //    true, then a. Let cause be ? Get(options, "cause").
    //    b. Perform CreateNonEnumerableDataPropertyOrThrow(O, "cause", cause).
    let options = arg(args, 1);
    if vm.heap().is_object(options) {
        let kc = key(vm, "cause")?;
        if has_property(vm, options, kc)? {
            let cause = vm.get_value(options, kc)?;
            define(
                vm,
                o,
                "cause",
                cause,
                Attrs(Attrs::WRITABLE | Attrs::CONFIGURABLE),
            )?;
        }
    }
    Ok(o)
}

/// `Error.prototype.toString ( )`, §20.5.3.4†:
/// 1. Let O be the this value.
/// 2. If O is not an Object, throw a TypeError exception.
/// 3. Let name be ? Get(O, "name").
/// 4. If name is undefined, set name to "Error"; otherwise set name to ?
///    ToString(name).
/// 5. Let msg be ? Get(O, "message").
/// 6. If msg is undefined, set msg to the empty String; otherwise set msg to
///    ? ToString(msg).
/// 7. If name is the empty String, return msg.
/// 8. If msg is the empty String, return name.
/// 9. Return the string-concatenation of name, the code unit 0x003A (COLON),
///    the code unit 0x0020 (SPACE), and msg.
fn to_string(vm: &mut Vm, this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    if !vm.heap().is_object(this) {
        return Err(vm.type_error("Error.prototype.toString called on a non-object"));
    }
    let kn = key(vm, "name")?;
    let name = vm.get_value(this, kn)?;
    let name = if name == Value::UNDEFINED {
        "Error".to_string()
    } else {
        vm.to_js_string(name)?.to_string_lossy()
    };
    let km = key(vm, "message")?;
    let msg = vm.get_value(this, km)?;
    let msg = if msg == Value::UNDEFINED {
        String::new()
    } else {
        vm.to_js_string(msg)?.to_string_lossy()
    };
    if name.is_empty() {
        return string(vm, &msg);
    }
    if msg.is_empty() {
        return string(vm, &name);
    }
    string(vm, &format!("{name}: {msg}"))
}
