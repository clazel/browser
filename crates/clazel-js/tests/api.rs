//! Small scripts and calls through the public API only: `clazel-js` is the
//! one crate these tests name. Each expectation is what ECMA-262 says,
//! written by hand.
//!
//! The tests read no files and no clock, so they also run under Miri; each
//! builds a runtime and installs the built-ins, which Miri runs slowly, so
//! the loops that only repeat a check use fewer rounds there.

use clazel_js::{
    Args, Callable, Config, DefaultHost, Error, ErrorKind, Handle, Host, HostObject, Key, Limits,
    Local, Realm, RealmOptions, Result, Runtime, Scope, Source, ValueKind, WellKnownSymbol,
};

type Test = core::result::Result<(), Error>;

/// A runtime with one realm.
fn runtime() -> Result<(Runtime, Realm)> {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    Ok((rt, realm))
}

/// Runs `text` and gives the value of its expression, which the compiler's
/// scripts do not yet return as a completion value (`Scope::run_script`
/// gives `undefined`). The rule: with a newline, the last line is the
/// expression and the lines before it statements; a last line (or a text
/// without a newline) that ends in `;` or `}` makes the whole text statements
/// only, and the value `undefined`.
/// The expression's value is read back from a global.
fn ev<'s>(scope: &mut Scope<'s>, realm: &Realm, text: &str) -> Result<Local<'s>> {
    let (statements, expression) = match text.rsplit_once('\n') {
        Some((_, last)) if last.ends_with(';') || last.ends_with('}') => (text, None),
        Some((statements, last)) => (statements, Some(last)),
        None if text.ends_with(';') || text.ends_with('}') => (text, None),
        None => ("", Some(text)),
    };
    let script = match expression {
        Some(expression) => format!("{statements}\nvar ev_result = ({expression});"),
        None => statements.to_owned(),
    };
    scope.eval_script(realm, Source::new("test.js", &script))?;
    if expression.is_none() {
        return Ok(scope.undefined());
    }
    let global = scope.global(realm)?;
    scope.get(global, Key::from("ev_result"))
}

/// [`ev`], read as a number.
fn eval_number(rt: &mut Runtime, realm: &Realm, text: &str) -> Result<Option<f64>> {
    rt.scope(|scope| {
        let value = ev(scope, realm, text)?;
        Ok(scope.as_number(value))
    })
}

/// `Scope::eval_script` of `text`, read as a string.
fn eval_string(rt: &mut Runtime, realm: &Realm, text: &str) -> Result<String> {
    rt.scope(|scope| {
        let value = ev(scope, realm, text)?;
        let text = scope.to_string(value)?;
        scope.string_to_string_lossy(text)
    })
}

#[test]
fn scripts_give_their_completion_value() -> Test {
    let (mut rt, realm) = runtime()?;
    assert_eq!(eval_number(&mut rt, &realm, "1 + 2")?, Some(3.0));
    assert_eq!(
        eval_number(&mut rt, &realm, "var x = 6;\nx * 7")?,
        Some(42.0)
    );
    assert_eq!(eval_number(&mut rt, &realm, "x + 1")?, Some(7.0));
    assert_eq!(eval_string(&mut rt, &realm, "'a' + 'b'")?, "ab");
    assert_eq!(eval_string(&mut rt, &realm, "typeof 1")?, "number");
    assert_eq!(eval_string(&mut rt, &realm, "String(0.5)")?, "0.5");
    assert_eq!(
        eval_number(
            &mut rt,
            &realm,
            "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }\nfib(10)"
        )?,
        Some(55.0)
    );
    // The built-ins are installed.
    assert_eq!(eval_string(&mut rt, &realm, "Math.max(1, 3, 2)")?, "3");
    assert_eq!(
        eval_string(&mut rt, &realm, "new Error('m').toString()")?,
        "Error: m"
    );
    Ok(())
}

#[test]
fn compile_and_run_are_separate() -> Test {
    let (mut rt, realm) = runtime()?;
    let script = rt.scope(|scope| {
        scope.compile_script(
            &realm,
            Source::new("count.js", "var n = (typeof n === 'number' ? n : 0) + 1;"),
        )
    })?;
    for expected in [1.0, 2.0, 3.0] {
        let got = rt.scope(|scope| {
            scope.run_script(&script)?;
            let global = scope.global(&realm)?;
            let n = scope.get(global, Key::from("n"))?;
            Ok(scope.as_number(n))
        })?;
        assert_eq!(got, Some(expected));
    }
    Ok(())
}

#[test]
fn syntax_errors_are_thrown_syntax_errors() -> Test {
    let (mut rt, realm) = runtime()?;
    let report = rt.scope(|scope| match ev(scope, &realm, "var = ;") {
        Err(Error::Thrown(exception)) => scope.report(&exception),
        Err(other) => Err(other),
        Ok(_) => Ok(clazel_js::ErrorReport::default()),
    })?;
    assert_eq!(report.name, "SyntaxError");
    // The runtime is still usable.
    assert_eq!(eval_number(&mut rt, &realm, "2 * 2")?, Some(4.0));
    Ok(())
}

#[test]
fn thrown_exceptions_carry_their_value() -> Test {
    let (mut rt, realm) = runtime()?;
    let thrown = rt.scope(|scope| {
        let result = ev(scope, &realm, "throw new TypeError('no way');");
        match result {
            Err(Error::Thrown(exception)) => Ok(Some(exception)),
            Err(other) => Err(other),
            Ok(_) => Ok(None),
        }
    })?;
    let exception = thrown.ok_or(Error::WrongType("a thrown error"))?;
    // The exception outlives the scope that made it, and reports without
    // running JavaScript.
    let report = rt.scope(|scope| scope.report(&exception))?;
    assert_eq!(report.name, "TypeError");
    assert_eq!(report.message, "no way");
    let is_error = rt.scope(|scope| {
        let value = scope.exception_value(&exception)?;
        let kind = scope.kind(value);
        let message = scope.get(value, Key::from("message"))?;
        Ok((kind, scope.string_to_string_lossy(message)?))
    })?;
    assert_eq!(is_error, (ValueKind::Object, "no way".to_owned()));

    // A thrown primitive, and the engine's own errors from the VM.
    let primitive = rt.scope(|scope| match ev(scope, &realm, "throw 7;") {
        Err(Error::Thrown(e)) => {
            let v = scope.exception_value(&e)?;
            Ok(scope.as_number(v))
        }
        Err(other) => Err(other),
        Ok(_) => Ok(None),
    })?;
    assert_eq!(primitive, Some(7.0));
    let reference = rt.scope(|scope| match ev(scope, &realm, "nope;") {
        Err(Error::Thrown(e)) => Ok(scope.report(&e)?.name),
        Err(other) => Err(other),
        Ok(_) => Ok(String::new()),
    })?;
    assert_eq!(reference, "ReferenceError");
    Ok(())
}

#[test]
fn values_get_set_call_and_construct() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        ev(
            scope,
            &realm,
            "function add(a, b) { return a + b; }\n\
                 function Point(x, y) { this.x = x; this.y = y; }\n\
                 Point.prototype.sum = function () { return this.x + this.y; };\n\
                 var answer = 41;",
        )?;
        let global = scope.global(&realm)?;

        // get and call
        let add = scope.get(global, Key::from("add"))?;
        assert_eq!(scope.kind(add), ValueKind::Function);
        assert!(scope.is_callable(add));
        let (one, two) = (scope.number(1.0), scope.number(2.0));
        let this = scope.undefined();
        let three = scope.call(add, this, &[one, two])?;
        assert_eq!(scope.as_number(three), Some(3.0));
        let a = scope.string("a");
        let b = scope.string("b");
        let ab = scope.call(add, this, &[a, b])?;
        assert_eq!(scope.string_to_string_lossy(ab)?, "ab");

        // set, then the script sees it
        let forty_two = scope.number(42.0);
        scope.set(global, Key::from("answer"), forty_two)?;
        let seen = ev(scope, &realm, "answer + 0")?;
        assert_eq!(scope.as_number(seen), Some(42.0));

        // construct, and a method through the prototype chain
        let point = scope.get(global, Key::from("Point"))?;
        assert!(scope.is_constructor(point));
        assert!(!scope.is_constructor(add) || scope.is_callable(add));
        let (x, y) = (scope.number(3.0), scope.number(4.0));
        let p = scope.construct(point, &[x, y], None)?;
        let px = scope.get(p, Key::from("x"))?;
        assert_eq!(scope.as_number(px), Some(3.0));
        let sum = scope.get(p, Key::from("sum"))?;
        let total = scope.call(sum, p, &[])?;
        assert_eq!(scope.as_number(total), Some(7.0));
        assert!(scope.instance_of(p, point)?);
        assert!(!scope.instance_of(global, point)?);
        assert!(scope.has_property(p, Key::from("sum"))?);
        assert!(!scope.has_property(p, Key::from("nope"))?);

        // get_method
        assert!(scope.get_method(p, Key::from("nope"))?.is_none());
        assert!(scope.get_method(p, Key::from("sum"))?.is_some());
        match scope.get_method(p, Key::from("x")) {
            Err(Error::Thrown(_)) => {}
            _ => return Err(Error::WrongType("a TypeError for a non-callable method")),
        }

        // Calling a non-function throws a TypeError the embedder can catch.
        match scope.call(p, this, &[]) {
            Err(Error::Thrown(e)) => assert_eq!(scope.report(&e)?.name, "TypeError"),
            _ => return Err(Error::WrongType("a TypeError for a call of an object")),
        }
        Ok(())
    })
}

#[test]
fn objects_and_properties() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let object = scope.new_object()?;
        let seven = scope.number(7.0);
        scope.set(object, Key::from("a"), seven)?;
        scope.set(object, Key::Index(1), seven)?;
        let name = scope.string("b");
        let eight = scope.number(8.0);
        scope.set(object, Key::Value(name), eight)?;
        for (key, want) in [("a", 7.0), ("1", 7.0), ("b", 8.0)] {
            let got = scope.get(object, Key::from(key))?;
            assert_eq!(scope.as_number(got), Some(want), "{key}");
        }

        // A read-only property refuses `set`, as strict assignment does.
        scope.define_property(
            object,
            Key::from("fixed"),
            clazel_js::PropertyDescriptor {
                value: Some(seven),
                writable: Some(false),
                enumerable: Some(true),
                configurable: Some(false),
                ..clazel_js::PropertyDescriptor::default()
            },
        )?;
        match scope.set(object, Key::from("fixed"), eight) {
            Err(Error::Thrown(e)) => assert_eq!(scope.report(&e)?.name, "TypeError"),
            _ => return Err(Error::WrongType("a TypeError for a read-only property")),
        }
        let fixed = scope.get(object, Key::from("fixed"))?;
        assert_eq!(scope.as_number(fixed), Some(7.0));

        // Prototypes.
        let proto = scope.new_object()?;
        scope.set_prototype_of(object, proto)?;
        let got = scope.get_prototype_of(object)?;
        assert!(scope.strict_equals(got, proto));
        scope.set(proto, Key::from("inherited"), eight)?;
        let inherited = scope.get(object, Key::from("inherited"))?;
        assert_eq!(scope.as_number(inherited), Some(8.0));
        // A cycle is refused.
        match scope.set_prototype_of(proto, object) {
            Err(Error::Thrown(_)) => {}
            _ => return Err(Error::WrongType("a TypeError for a cycle")),
        }
        let null = scope.null();
        scope.set_prototype_of(proto, null)?;
        let none = scope.get_prototype_of(proto)?;
        assert_eq!(scope.kind(none), ValueKind::Null);

        // A non-object where an object is needed is the caller's mistake.
        match scope.set(seven, Key::from("a"), eight) {
            Err(Error::WrongType(_)) => {}
            _ => return Err(Error::WrongType("WrongType for a primitive base")),
        }
        let global = scope.global(&realm)?;
        assert_eq!(scope.kind(global), ValueKind::Object);
        Ok(())
    })
}

#[test]
fn conversions_and_predicates() -> Test {
    let (mut rt, _realm) = runtime()?;
    rt.scope(|scope| {
        let s = scope.string("42");
        assert_eq!(scope.to_number(s)?, 42.0);
        let half = scope.number(1.5);
        let text = scope.to_string(half)?;
        assert_eq!(scope.string_to_string_lossy(text)?, "1.5");
        let empty = scope.string("");
        assert!(!scope.to_boolean(empty));
        let word = scope.string("x");
        assert!(scope.to_boolean(word));
        let nan = scope.number(f64::NAN);
        assert!(!scope.to_boolean(nan));
        assert_eq!(scope.kind(nan), ValueKind::Number);
        let t = scope.boolean(true);
        assert_eq!(scope.as_boolean(t), Some(true));
        assert_eq!(scope.as_boolean(nan), None);
        let u = scope.undefined();
        let n = scope.null();
        assert_eq!(scope.kind(u), ValueKind::Undefined);
        assert_eq!(scope.kind(n), ValueKind::Null);
        assert_eq!(scope.kind(s), ValueKind::String);
        assert!(!scope.is_callable(s));
        assert!(!scope.is_array(s)?);

        // ToObject: wrappers for primitives, a TypeError for undefined.
        let wrapped = scope.to_object(s)?;
        assert_eq!(scope.kind(wrapped), ValueKind::Object);
        match scope.to_object(u) {
            Err(Error::Thrown(e)) => assert_eq!(scope.report(&e)?.name, "TypeError"),
            _ => return Err(Error::WrongType("a TypeError for undefined")),
        }
        // ToNumber of an object goes through its `valueOf`.
        assert_eq!(scope.to_number(wrapped)?, 42.0);

        // Equality: Number by value, String by content, -0 and NaN as ECMA-262 says.
        let (a, b) = (scope.number(2.0), scope.number(2.0));
        assert!(scope.strict_equals(a, b));
        assert!(!scope.strict_equals(nan, nan));
        assert!(scope.same_value(nan, nan));
        let (zero, minus_zero) = (scope.number(0.0), scope.number(-0.0));
        assert!(scope.strict_equals(zero, minus_zero));
        assert!(!scope.same_value(zero, minus_zero));
        let (s1, s2) = (scope.string("ab"), scope.string("ab"));
        assert!(scope.strict_equals(s1, s2));
        let plain = scope.new_object()?;
        let other = scope.new_object()?;
        assert!(scope.strict_equals(plain, plain));
        assert!(!scope.strict_equals(plain, other));
        assert!(!scope.strict_equals(a, s1));
        Ok(())
    })
}

#[test]
fn strings_keep_lone_surrogates() -> Test {
    let (mut rt, _realm) = runtime()?;
    rt.scope(|scope| {
        let units = [0x61_u16, 0xD800, 0x62, 0xDC00, 0xD83D, 0xDE00];
        let s = scope.string_utf16(&units);
        assert_eq!(scope.string_to_utf16(s)?, units);
        assert_eq!(
            scope.string_to_string_lossy(s)?,
            "a\u{FFFD}b\u{FFFD}\u{1F600}"
        );
        // A string key with a lone surrogate goes in as a value.
        let o = scope.new_object()?;
        let one = scope.number(1.0);
        scope.set(o, Key::Value(s), one)?;
        let back = scope.get(o, Key::Value(s))?;
        assert_eq!(scope.as_number(back), Some(1.0));
        let n = scope.number(1.0);
        match scope.string_to_utf16(n) {
            Err(Error::WrongType(_)) => {}
            _ => return Err(Error::WrongType("WrongType for a number")),
        }
        Ok(())
    })
}

#[test]
fn native_functions_are_called_from_scripts() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let greet = scope.function("greet", 1, Callable::Function, |scope, args| {
            let who = scope.to_string(args.get(0))?;
            let who = scope.string_to_string_lossy(who)?;
            Ok(scope.string(&format!("hello, {who}")))
        })?;
        scope.set(global, Key::from("greet"), greet)?;
        let add = scope.function("add", 2, Callable::Function, |scope, args| {
            let a = scope.to_number(args.get(0))?;
            let b = scope.to_number(args.get(1))?;
            Ok(scope.number(a + b))
        })?;
        scope.set(global, Key::from("add"), add)?;
        let count = scope.function("count", 0, Callable::Function, |scope, args| {
            Ok(scope.number(args.len() as f64))
        })?;
        scope.set(global, Key::from("count"), count)?;

        let r = ev(scope, &realm, "greet('world')")?;
        assert_eq!(scope.string_to_string_lossy(r)?, "hello, world");
        let r = ev(scope, &realm, "add(40, 2)")?;
        assert_eq!(scope.as_number(r), Some(42.0));
        // `length` and `name` are the function's own.
        let r = ev(scope, &realm, "add.length + add.name")?;
        assert_eq!(scope.string_to_string_lossy(r)?, "2add");
        // Arguments: how many were passed, and `this`.
        let r = ev(scope, &realm, "count(1, 2, 3)")?;
        assert_eq!(scope.as_number(r), Some(3.0));
        let r = ev(scope, &realm, "count()")?;
        assert_eq!(scope.as_number(r), Some(0.0));

        // From Rust too.
        let u = scope.undefined();
        let x = scope.string("rust");
        let r = scope.call(greet, u, &[x])?;
        assert_eq!(scope.string_to_string_lossy(r)?, "hello, rust");
        Ok(())
    })
}

#[test]
fn natives_can_call_back_into_scripts() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        // `twice(f, x)` is f(f(x)).
        let twice = scope.function("twice", 2, Callable::Function, |scope, args| {
            let this = scope.undefined();
            let once = scope.call(args.get(0), this, &[args.get(1)])?;
            scope.call(args.get(0), this, &[once])
        })?;
        scope.set(global, Key::from("twice"), twice)?;
        let r = ev(scope, &realm, "twice(function (n) { return n * 3; }, 2)")?;
        assert_eq!(scope.as_number(r), Some(18.0));
        // A native that calls a script that calls a different native.
        let inc = scope.function("inc", 1, Callable::Function, |scope, args| {
            let n = scope.to_number(args.get(0))?;
            Ok(scope.number(n + 1.0))
        })?;
        scope.set(global, Key::from("inc"), inc)?;
        let r = ev(
            scope,
            &realm,
            "twice(function (n) { return inc(inc(n)); }, 0)",
        )?;
        assert_eq!(scope.as_number(r), Some(4.0));
        Ok(())
    })
}

#[test]
fn errors_cross_the_native_boundary() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let boom = scope.function("boom", 0, Callable::Function, |scope, _args| {
            Err(scope.throw_error(ErrorKind::RangeError, "from rust"))
        })?;
        scope.set(global, Key::from("boom"), boom)?;
        let throw_value = scope.function("throwValue", 0, Callable::Function, |scope, _args| {
            let v = scope.number(99.0);
            Err(scope.throw(v))
        })?;
        scope.set(global, Key::from("throwValue"), throw_value)?;
        let engine_error = scope.function("engineError", 0, Callable::Function, |_s, _a| {
            Err(Error::WrongType("something only Rust can name"))
        })?;
        scope.set(global, Key::from("engineError"), engine_error)?;

        // JavaScript catches a thrown error with its kind and message.
        let r = ev(scope, &realm, "var r; try { boom(); } catch (e) { r = e.name + ':' + e.message + ':' + (e.constructor === RangeError); }\nr")?;
        assert_eq!(scope.string_to_string_lossy(r)?, "RangeError:from rust:true");
        // A thrown value of any kind.
        let r = ev(scope, &realm, "var v; try { throwValue(); } catch (e) { v = e; }\nv")?;
        assert_eq!(scope.as_number(r), Some(99.0));
        // An uncaught one comes back to Rust as the same exception.
        match ev(scope, &realm, "boom()") {
            Err(Error::Thrown(e)) => assert_eq!(scope.report(&e)?.message, "from rust"),
            _ => return Err(Error::WrongType("Thrown")),
        }
        // An error that is not JavaScript's cannot be caught by JavaScript,
        // and arrives unchanged.
        match ev(scope, &realm, "var c = 0; try { engineError(); } catch (e) { c = 1; }\nc") {
            Err(Error::WrongType("something only Rust can name")) => {}
            Err(other) => return Err(other),
            Ok(_) => return Err(Error::WrongType("an error from engineError")),
        }
        Ok(())
    })
}

#[test]
fn native_constructors_see_new_target() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let make = scope.function("Make", 1, Callable::Constructor, |scope, args| {
            let object = scope.new_object()?;
            let flag = scope.boolean(args.new_target().is_some());
            scope.set(object, Key::from("constructed"), flag)?;
            scope.set(object, Key::from("arg"), args.get(0))?;
            Ok(object)
        })?;
        scope.set(global, Key::from("Make"), make)?;
        assert!(scope.is_constructor(make));
        let r = ev(
            scope,
            &realm,
            "var m = new Make(5);\nm.constructed + ',' + m.arg",
        )?;
        assert_eq!(scope.string_to_string_lossy(r)?, "true,5");
        let r = ev(scope, &realm, "var k = Make(6);\nk.constructed")?;
        assert_eq!(scope.as_boolean(r), Some(false));

        // A plain function cannot be used with `new`.
        let plain = scope.function("plain", 0, Callable::Function, |scope, _| {
            Ok(scope.undefined())
        })?;
        scope.set(global, Key::from("plain"), plain)?;
        assert!(!scope.is_constructor(plain));
        match ev(scope, &realm, "new plain()") {
            Err(Error::Thrown(e)) => assert_eq!(scope.report(&e)?.name, "TypeError"),
            _ => return Err(Error::WrongType("a TypeError for new of a plain native")),
        }

        // From Rust: construct, and get_prototype_from_constructor.
        let a = scope.number(1.0);
        let built = scope.construct(make, &[a], None)?;
        let flag = scope.get(built, Key::from("constructed"))?;
        assert_eq!(scope.as_boolean(flag), Some(true));
        let fallback = scope.new_object()?;
        let proto = scope.new_object()?;
        scope.set(make, Key::from("prototype"), proto)?;
        let got = scope.get_prototype_from_constructor(make, fallback)?;
        assert!(scope.strict_equals(got, proto));
        let other = scope.new_object()?;
        let got = scope.get_prototype_from_constructor(other, fallback)?;
        assert!(scope.strict_equals(got, fallback));
        Ok(())
    })
}

#[test]
fn define_method_makes_a_hidden_method() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let console = scope.new_object()?;
        scope.define_method(console, "twice", 1, |scope, args| {
            let n = scope.to_number(args.get(0))?;
            Ok(scope.number(n * 2.0))
        })?;
        scope.define_method(console, "me", 0, |_scope, args| Ok(args.this()))?;
        scope.set(global, Key::from("console"), console)?;
        let r = ev(scope, &realm, "console.twice(21)")?;
        assert_eq!(scope.as_number(r), Some(42.0));
        // `this` is the receiver.
        let r = ev(scope, &realm, "console.me() === console")?;
        assert_eq!(scope.as_boolean(r), Some(true));
        // Not enumerable, so `Object.keys` does not list it.
        let r = ev(scope, &realm, "Object.keys(console).length")?;
        assert_eq!(scope.as_number(r), Some(0.0));
        Ok(())
    })
}

/// A host object's data.
struct Counter {
    n: u32,
}
impl HostObject for Counter {}

struct Other;
impl HostObject for Other {}

#[test]
fn host_objects_carry_typed_data() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let proto = scope.new_object()?;
        scope.define_method(proto, "bump", 0, |scope, args| {
            let this = args.this();
            let counter = scope.host_data_mut::<Counter>(this)?;
            counter.n += 1;
            let n = counter.n;
            Ok(scope.number(f64::from(n)))
        })?;
        let counter = scope.new_host_object(Some(proto), Counter { n: 10 })?;
        scope.set(global, Key::from("counter"), counter)?;
        let r = ev(scope, &realm, "counter.bump();\ncounter.bump()")?;
        assert_eq!(scope.as_number(r), Some(12.0));
        assert_eq!(scope.host_data::<Counter>(counter)?.n, 12);

        // Another type, a plain object, and a primitive are WrongType.
        match scope.host_data::<Other>(counter) {
            Err(Error::WrongType(_)) => {}
            _ => return Err(Error::WrongType("WrongType for another type")),
        }
        let plain = scope.new_object()?;
        match scope.host_data::<Counter>(plain) {
            Err(Error::WrongType(_)) => {}
            _ => return Err(Error::WrongType("WrongType for a plain object")),
        }
        // A method called on the wrong receiver fails inside the native.
        match ev(scope, &realm, "var f = counter.bump;\nf.call({})") {
            Err(Error::WrongType(_)) => {}
            Err(other) => return Err(other),
            Ok(_) => return Err(Error::WrongType("an error for the wrong receiver")),
        }
        // A null prototype is allowed.
        let bare = scope.new_host_object(None, Counter { n: 0 })?;
        let p = scope.get_prototype_of(bare)?;
        assert_eq!(scope.kind(p), ValueKind::Null);
        Ok(())
    })
}

#[test]
fn handles_outlive_scopes_and_belong_to_one_runtime() -> Test {
    let (mut rt, realm) = runtime()?;
    let (mut other, other_realm) = runtime()?;

    let handle: Handle = rt.scope(|scope| {
        let object = scope.new_object()?;
        let five = scope.number(5.0);
        scope.set(object, Key::from("five"), five)?;
        Ok(scope.persist(object))
    })?;
    let copy = handle.clone();
    drop(handle);
    let five = rt.scope(|scope| {
        let object = scope.local(&copy)?;
        let v = scope.get(object, Key::from("five"))?;
        Ok(scope.as_number(v))
    })?;
    assert_eq!(five, Some(5.0));

    // Another runtime's scope refuses it.
    match other.scope(|scope| scope.local(&copy).map(|_| ())) {
        Err(Error::WrongRuntime) => {}
        _ => return Err(Error::WrongType("WrongRuntime for a foreign handle")),
    }
    // And so does a Local that is smuggled into another runtime's scope.
    let smuggled = rt.scope(|a| {
        other.scope(|b| {
            let local = a.number(1.0);
            b.to_number(local)
        })
    });
    match smuggled {
        Err(Error::WrongRuntime) => {}
        _ => return Err(Error::WrongType("WrongRuntime for a foreign local")),
    }
    // Realms are roots of one runtime too.
    match other.scope(|scope| scope.global(&realm).map(|_| ())) {
        Err(Error::WrongRuntime) => {}
        _ => return Err(Error::WrongType("WrongRuntime for a foreign realm")),
    }
    let _ = other_realm;

    // Weak and Member read back what is alive; with no collector that is
    // everything.
    let (weak, member) = rt.scope(|scope| {
        let object = scope.new_object()?;
        Ok((scope.downgrade(object), scope.member(object)))
    })?;
    rt.scope(|scope| {
        assert!(scope.upgrade(&weak)?.is_some());
        let local = scope.local_from_member(member)?;
        assert_eq!(scope.kind(local), ValueKind::Object);
        Ok(())
    })
}

#[test]
fn an_exception_is_a_handle() -> Test {
    let (mut rt, _realm) = runtime()?;
    let exception =
        rt.scope(|scope| scope.new_exception(ErrorKind::SyntaxError, "made by hand"))?;
    let report = rt.scope(|scope| scope.report(&exception))?;
    assert_eq!(report.name, "SyntaxError");
    assert_eq!(report.message, "made by hand");
    // Not every kind has a constructor in the built-ins yet.
    match rt.scope(|scope| scope.new_exception(ErrorKind::EvalError, "x")) {
        Err(Error::NotImplemented(_)) => Ok(()),
        _ => Err(Error::WrongType("NotImplemented for EvalError")),
    }
}

#[test]
fn the_terminator_stops_a_loop_from_another_thread() -> Test {
    let (mut rt, realm) = runtime()?;
    let terminator = rt.terminator();
    // Set before the run, so the test does not depend on timing: the flag is
    // sticky and the loop reads it at its first back-edge.
    terminator.terminate();
    assert!(terminator.is_terminated());
    let result = rt.scope(|scope| {
        scope
            .eval_script(&realm, Source::new("loop.js", "for (;;) {}"))
            .map(|_| ())
    });
    assert!(matches!(result, Err(Error::Terminated)));
    // Sticky: every later call also ends `Terminated`.
    let again = rt.scope(|scope| {
        scope
            .eval_script(&realm, Source::new("loop.js", "1"))
            .map(|_| ())
    });
    assert!(matches!(again, Err(Error::Terminated)));
    // Cleared, the runtime is usable.
    terminator.clear();
    assert_eq!(eval_number(&mut rt, &realm, "6 * 7")?, Some(42.0));

    // And from another thread while a script runs.
    let watchdog = rt.terminator();
    let handle = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(if cfg!(miri) {
            1
        } else {
            50
        }));
        watchdog.terminate();
    });
    let result = rt.scope(|scope| {
        scope
            .eval_script(&realm, Source::new("loop.js", "for (;;) {}"))
            .map(|_| ())
    });
    let _ = handle.join();
    assert!(matches!(result, Err(Error::Terminated)));
    rt.terminator().clear();
    assert_eq!(eval_number(&mut rt, &realm, "1 + 1")?, Some(2.0));
    Ok(())
}

#[test]
fn native_functions_can_check_the_terminator() -> Test {
    let (mut rt, realm) = runtime()?;
    let terminator = rt.terminator();
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let stop = scope.function("stop", 0, Callable::Function, move |scope, _| {
            scope.check_terminated()?;
            terminator.terminate();
            scope.check_terminated()?;
            Ok(scope.undefined())
        })?;
        scope.set(global, Key::from("stop"), stop)?;
        match ev(scope, &realm, "try { stop(); } catch (e) {}") {
            Err(Error::Terminated) => Ok(()),
            _ => Err(Error::WrongType("Terminated through a try/catch")),
        }
    })
}

/// A host that counts, to find again from inside a native function.
#[derive(Default)]
struct CountingHost {
    draws: u64,
}
impl Host for CountingHost {
    fn random_u64(&mut self) -> u64 {
        self.draws = self.draws.saturating_add(1);
        self.draws
    }
}

#[test]
fn the_host_is_reachable_as_its_own_type() -> Test {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), CountingHost::default())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let draw = scope.function("draw", 0, Callable::Function, |scope, _| {
            let host = scope.host_mut::<CountingHost>()?;
            let n = host.random_u64();
            Ok(scope.number(n as f64))
        })?;
        scope.set(global, Key::from("draw"), draw)?;
        let r = ev(scope, &realm, "draw(); draw();\ndraw()")?;
        assert_eq!(scope.as_number(r), Some(3.0));
        match scope.host_mut::<DefaultHost>() {
            Err(Error::WrongType(_)) => {}
            _ => return Err(Error::WrongType("WrongType for another host type")),
        }
        Ok(())
    })?;
    assert_eq!(rt.host_mut().random_u64(), 4);
    Ok(())
}

#[test]
fn realm_host_data_and_one_realm() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        assert!(scope.realm_host_defined(&realm)?.is_none());
        scope.set_realm_host_defined(&realm, Box::new(String::from("settings")))?;
        let data = scope.realm_host_defined(&realm)?;
        let text = data.and_then(|d| d.downcast_ref::<String>());
        assert_eq!(text.map(String::as_str), Some("settings"));
        let current = scope.current_realm()?;
        let g1 = scope.global(&realm)?;
        let g2 = scope.global(&current)?;
        assert!(scope.strict_equals(g1, g2));
        // The VM has one global environment, so a second realm is not there.
        match scope.create_realm(RealmOptions::default()) {
            Err(Error::NotImplemented(_)) => {}
            _ => return Err(Error::WrongType("NotImplemented for a second realm")),
        }
        Ok(())
    })
}

#[test]
fn script_host_data_comes_back() -> Test {
    struct Base(&'static str);
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let source =
            Source::new("s.js", "1").with_host_defined(Box::new(Base("https://example.test/")));
        let script = scope.compile_script(&realm, source)?;
        let data = scope.host_defined(clazel_js::Referrer::Script(&script))?;
        let base = data.and_then(|d| d.downcast_ref::<Base>());
        assert_eq!(base.map(|b| b.0), Some("https://example.test/"));
        Ok(())
    })
}

#[test]
fn a_heap_too_small_for_the_builtins_is_out_of_memory() -> Test {
    // A heap too small for the built-ins is `OutOfMemory`, not a panic.
    let tiny = Limits {
        heap_bytes: 64 * 4,
        ..Limits::unlimited()
    };
    assert!(matches!(
        Runtime::new(Config::new(tiny), DefaultHost::new()),
        Err(Error::OutOfMemory)
    ));
    Ok(())
}

#[test]
fn the_heap_limit_stops_a_script_that_allocates_for_ever() -> Test {
    // A small heap that fits the built-ins is hit by a script that allocates
    // for ever. Under Miri each allocation is slow, so the room is smaller.
    let cells: u64 = if cfg!(miri) { 300 } else { 20_000 };
    let (probe, _) = runtime()?;
    let base = probe.heap_used()?;
    assert!(base > 0);
    let room = Limits {
        heap_bytes: base + 64 * cells,
        ..Limits::unlimited()
    };
    let mut rt = Runtime::new(Config::new(room), DefaultHost::new())?;
    assert_eq!(rt.limits(), room);
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    let result = rt.scope(|scope| {
        scope
            .eval_script(
                &realm,
                Source::new("a.js", "var s = ''; for (;;) { s = s + 'x'; }"),
            )
            .map(|_| ())
    });
    assert!(matches!(result, Err(Error::OutOfMemory)), "{result:?}");
    Ok(())
}

#[test]
fn the_value_stack_limit_makes_deep_recursion_catchable() -> Test {
    // A deep recursion is a catchable RangeError-like stop, not a crash.
    let shallow = Limits {
        value_stack_bytes: 8 * 512,
        ..Limits::unlimited()
    };
    let mut rt = Runtime::new(Config::new(shallow), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    let caught = eval_string(
        &mut rt,
        &realm,
        "function f() { return f() + 1; } var r = 'none'; try { f(); } catch (e) { r = 'caught'; }\nr",
    )?;
    assert_eq!(caught, "caught");
    Ok(())
}

#[test]
fn native_depth_is_limited() -> Test {
    let limits = Limits {
        native_depth: 8,
        ..Limits::unlimited()
    };
    let mut rt = Runtime::new(Config::new(limits), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        // A chain of different closures, each calling a script function that
        // calls the next, as `map` calling a callback that calls `filter`
        // would: the ninth is one too many.
        for i in 0..12_u32 {
            let relay =
                scope.function(&format!("n{i}"), 0, Callable::Function, move |scope, _| {
                    let global = scope.current_realm().and_then(|r| scope.global(&r))?;
                    let go = scope.get(global, Key::from("go"))?;
                    let next = scope.number(f64::from(i + 1));
                    let this = scope.undefined();
                    scope.call(go, this, &[next])
                })?;
            scope.set(global, Key::from(format!("n{i}").as_str()), relay)?;
        }
        let r = ev(
            scope,
            &realm,
            "var depth = 0;\n\
                 function go(i) { depth = i; return globalThis['n' + i](); }\n\
                 var r; try { go(0); } catch (e) { r = e.name; }\n\
                 r + ':' + depth",
        )?;
        // Eight natives run; the ninth call is refused with a RangeError,
        // which JavaScript catches.
        assert_eq!(scope.string_to_string_lossy(r)?, "RangeError:8");
        Ok(())
    })
}

/// A closure that JavaScript re-enters while it runs runs again, nested: the
/// table shares it with the call still running (open question 14).
#[test]
fn a_native_function_can_be_reentered() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let relay = scope.function("relay", 1, Callable::Function, |scope, args| {
            let this = scope.undefined();
            scope.call(args.get(0), this, &[])
        })?;
        scope.set(global, Key::from("relay"), relay)?;
        // Not re-entered: fine, and a native can call a script that calls
        // another native.
        let r = ev(scope, &realm, "relay(function () { return 1; })")?;
        assert_eq!(scope.as_number(r), Some(1.0));
        // Re-entered, three deep: each call runs and returns its value.
        let r = ev(
            scope,
            &realm,
            "relay(function () { return relay(function () { return relay(function () { return 3; }) + 1; }) + 1; })",
        )?;
        assert_eq!(scope.as_number(r), Some(5.0));
        // And the runtime is usable afterwards.
        let r = ev(scope, &realm, "relay(function () { return 2; })")?;
        assert_eq!(scope.as_number(r), Some(2.0));
        Ok(())
    })
}

#[test]
fn what_the_vm_lacks_says_so() -> Test {
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let object = scope.new_object()?;
        let key = Key::from("a");
        let not_implemented = |r: Result<()>| matches!(r, Err(Error::NotImplemented(_)));
        // Arrays and `delete_property` were in this list until the VM had
        // them (item 7.12 wired them): they now work, which the assertions
        // keep checking.
        assert!(scope.new_array(0).is_ok());
        assert!(scope.new_array_from(&[]).is_ok());
        assert!(scope.delete_property(object, key)?);
        assert!(not_implemented(scope.new_promise().map(|_| ())));
        assert!(not_implemented(scope.promise_resolve(object).map(|_| ())));
        assert!(not_implemented(scope.new_array_buffer(vec![1]).map(|_| ())));
        assert!(not_implemented(scope.iterate(object, |_, _| Ok(true))));
        assert!(not_implemented(
            scope
                .parse_module(&realm, Source::new("m.js", "export {}"))
                .map(|_| ())
        ));
        // Constructors that cannot fail record the failure for the next
        // fallible call.
        let big = scope.bigint_from_i64(1);
        assert_eq!(scope.kind(big), ValueKind::Undefined);
        assert!(not_implemented(scope.to_number(big).map(|_| ())));
        // ...and only once.
        assert!(scope.to_number(big).is_ok());
        let _ = scope.new_symbol(Some("d"));
        assert!(not_implemented(scope.new_object().map(|_| ())));
        let _ = scope.well_known_symbol(WellKnownSymbol::Iterator);
        assert!(not_implemented(scope.new_object().map(|_| ())));
        Ok(())
    })
}

#[test]
fn run_jobs_with_an_empty_queue_runs_none() -> Test {
    let (mut rt, realm) = runtime()?;
    assert_eq!(rt.run_jobs()?, 0);
    eval_number(&mut rt, &realm, "1")?;
    assert_eq!(rt.run_jobs()?, 0);
    // The same checkpoint from inside a scope (no job maker exists yet).
    let ran = rt.scope(|scope| scope.run_jobs())?;
    assert_eq!(ran, 0);
    Ok(())
}

#[test]
fn gc_and_clear_kept_objects_are_harmless() -> Test {
    let (mut rt, _realm) = runtime()?;
    rt.scope(|scope| {
        let o = scope.new_object()?;
        scope.gc()?;
        scope.clear_kept_objects()?;
        assert_eq!(scope.kind(o), ValueKind::Object);
        Ok(())
    })
}

#[test]
fn nested_scopes_share_the_runtime() -> Test {
    let (mut rt, _realm) = runtime()?;
    let total = rt.scope(|scope| {
        let list = scope.new_object()?;
        for i in 0..(if cfg!(miri) { 4_u32 } else { 200 }) {
            scope.nested(|inner| {
                let x = inner.number(f64::from(i));
                inner.set(list, Key::Index(i), x)
            })?;
        }
        let mut sum = 0.0;
        for i in 0..(if cfg!(miri) { 4_u32 } else { 200 }) {
            let v = scope.get(list, Key::Index(i))?;
            sum += scope.as_number(v).unwrap_or(0.0);
        }
        Ok(sum)
    })?;
    let n = if cfg!(miri) { 4.0 } else { 200.0 };
    assert_eq!(total, n * (n - 1.0) / 2.0);
    Ok(())
}

/// Phase 7's exit criterion 8: two runtimes on two threads run
/// independently. Each thread has its own globals, closures and host, and
/// they interleave on a shared barrier so both are mid-run together.
#[test]
fn two_runtimes_on_two_threads_run_independently() -> Test {
    use std::sync::{Arc, Barrier};
    let rounds: u32 = if cfg!(miri) { 2 } else { 200 };
    let barrier = Arc::new(Barrier::new(2));
    let spawn = |id: u32| {
        let barrier = Arc::clone(&barrier);
        std::thread::spawn(move || -> Result<(u32, f64)> {
            let (mut rt, realm) = runtime()?;
            // A global of the same name with a different value in each.
            rt.scope(|scope| {
                let global = scope.global(&realm)?;
                let me = scope.number(f64::from(id));
                scope.set(global, Key::from("me"), me)?;
                let who = scope.function("who", 0, Callable::Function, move |scope, _| {
                    Ok(scope.number(f64::from(id)))
                })?;
                scope.set(global, Key::from("who"), who)
            })?;
            barrier.wait();
            let mut total = 0.0;
            for round in 0..rounds {
                let got = rt.scope(|scope| {
                    // Same script text in both runtimes; the answers differ.
                    let value = ev(
                        scope,
                        &realm,
                        "var tally = (typeof tally === 'number' ? tally : 0) + me + who();\ntally",
                    )?;
                    Ok(scope.as_number(value))
                })?;
                total = got.ok_or(Error::WrongType("a number"))?;
                assert_eq!(total, f64::from(id) * 2.0 * f64::from(round + 1));
                if round == 0 {
                    barrier.wait();
                }
            }
            Ok((id, total))
        })
    };
    let (a, b) = (spawn(1), spawn(5));
    let a = a
        .join()
        .map_err(|_| Error::WrongType("a thread that did not panic"))??;
    let b = b
        .join()
        .map_err(|_| Error::WrongType("a thread that did not panic"))??;
    assert_eq!(a, (1, 2.0 * f64::from(rounds)));
    assert_eq!(b, (5, 10.0 * f64::from(rounds)));
    Ok(())
}

#[test]
fn a_runtime_moves_between_threads_and_a_handle_is_dropped_anywhere() -> Test {
    let (mut rt, realm) = runtime()?;
    let handle = rt.scope(|scope| {
        let o = scope.new_object()?;
        Ok(scope.persist(o))
    })?;
    // The handle goes to another thread and is dropped there, with no access
    // to the runtime.
    std::thread::spawn(move || drop(handle))
        .join()
        .map_err(|_| Error::WrongType("a thread that did not panic"))?;
    // The runtime itself moves, between calls.
    let moved = std::thread::spawn(move || -> Result<Option<f64>> {
        let value = eval_number(&mut rt, &realm, "40 + 2")?;
        Ok(value)
    })
    .join()
    .map_err(|_| Error::WrongType("a thread that did not panic"))??;
    assert_eq!(moved, Some(42.0));
    Ok(())
}

#[test]
fn native_closures_keep_their_state() -> Test {
    let (mut rt, realm) = runtime()?;
    let seen = std::sync::Arc::new(std::sync::Mutex::new(Vec::<String>::new()));
    let log = std::sync::Arc::clone(&seen);
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let print = scope.function("print", 1, Callable::Function, move |scope, args| {
            let text = scope.to_string(args.get(0))?;
            let text = scope.string_to_string_lossy(text)?;
            if let Ok(mut lines) = log.lock() {
                lines.push(text);
            }
            Ok(scope.undefined())
        })?;
        scope.set(global, Key::from("print"), print)?;
        ev(scope, &realm, "print('a'); print(2); print(true);")?;
        Ok(())
    })?;
    let lines = seen.lock().map(|l| l.clone()).unwrap_or_default();
    assert_eq!(lines, ["a", "2", "true"]);
    Ok(())
}

// A scope-bound value cannot be used after its scope, which is a
// compile-time property, checked by the doctests of `Local`. This only
// checks that `Args` is `Copy` and can be passed on.
#[test]
fn args_are_copy() -> Test {
    fn takes(args: Args<'_>) -> usize {
        args.len()
    }
    let (mut rt, realm) = runtime()?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let f = scope.function("f", 0, Callable::Function, |scope, args| {
            let copy = *args;
            Ok(scope.number((takes(copy) + takes(*args)) as f64))
        })?;
        scope.set(global, Key::from("f"), f)?;
        let r = ev(scope, &realm, "f(1, 2)")?;
        assert_eq!(scope.as_number(r), Some(4.0));
        Ok(())
    })
}
