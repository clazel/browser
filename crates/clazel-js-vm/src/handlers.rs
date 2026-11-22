//! The handlers of item 7.8's first slice: plain methods over the frame
//! region and the heap, which the interpreter loop ([`crate::interp`]) calls
//! for every op that can allocate, call out or throw, and which jit.md's
//! exits will call too.
//!
//! The handlers here cover: the slow paths of the arithmetic, comparison,
//! equality and truthiness ops on primitives; string concatenation with `+`
//! and Number to String through `clazel-js-number`; `typeof`; property get
//! and set on ordinary objects with inline caches; globals (the global object
//! and the global declarative record, `DeclareGlobals`); closures; and the
//! creation of the errors the VM throws. An operation that needs an object
//! converted to a primitive (`ToPrimitive`, which calls `valueOf` and
//! `toString`: the built-ins) is [`Abrupt::NotYet`], never a wrong answer.
//!
//! Each handler's contract is the clause of ECMA-262 it cites; the evidence is
//! the Test262 run in `tests/test262_run.rs`.

use crate::bytecode::{Const, ErrorKind, FunctionKind, VarScoped};
use crate::heap::{Cell, ObjKind};
use crate::interp::{Abrupt, ArithOp, Rel, Vm};
use crate::numeric::{self, Num, num};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::value::{Decoded, Value};

/// A property made by a function declaration or a `var` of the global
/// environment: writable and enumerable, not configurable (§9.1.1.4.17†
/// CreateGlobalVarBinding with `D` false).
const GLOBAL_VAR: Attrs = Attrs(Attrs::WRITABLE | Attrs::ENUMERABLE);
/// Attributes of `length` and `name` of a function (§10.2.9†, §10.2.10†).
const CONFIGURABLE_ONLY: Attrs = Attrs(Attrs::CONFIGURABLE);
/// Attributes of the `name` and `message` of an error the VM throws.
const WRITABLE_CONFIGURABLE: Attrs = Attrs(Attrs::WRITABLE | Attrs::CONFIGURABLE);

impl Vm {
    // -----------------------------------------------------------------
    // Errors
    // -----------------------------------------------------------------

    /// The abrupt completion of throwing a new error of `kind`: an ordinary
    /// object with `name` and `message` (the error constructors are
    /// built-ins, 7.9).
    pub(crate) fn throw_kind(&mut self, kind: ErrorKind, msg: &str) -> Abrupt {
        let name = match kind {
            ErrorKind::TypeError => "TypeError",
            ErrorKind::ReferenceError => "ReferenceError",
            ErrorKind::SyntaxError => "SyntaxError",
            ErrorKind::RangeError => "RangeError",
        };
        match self.make_error(name, msg) {
            Ok(v) => Abrupt::Throw(v),
            Err(e) => e,
        }
    }

    fn make_error(&mut self, name: &str, msg: &str) -> Result<Value, Abrupt> {
        let proto = self.atoms.object_proto;
        let o = self.heap.new_object(proto, ObjKind::Plain)?;
        let name_v = self.heap.new_str(name)?;
        let msg_v = self.heap.new_str(msg)?;
        let (kn, km) = (self.atoms.k_name, self.atoms.k_message);
        self.heap.define(o, kn, name_v, WRITABLE_CONFIGURABLE)?;
        self.heap.define(o, km, msg_v, WRITABLE_CONFIGURABLE)?;
        Ok(o)
    }

    /// A thrown `TypeError`.
    pub(crate) fn type_error(&mut self, msg: &str) -> Abrupt {
        self.throw_kind(ErrorKind::TypeError, msg)
    }

    /// A thrown `ReferenceError`.
    pub(crate) fn reference_error(&mut self, msg: &str) -> Abrupt {
        self.throw_kind(ErrorKind::ReferenceError, msg)
    }

    /// A thrown `RangeError`.
    pub(crate) fn range_error(&mut self, msg: &str) -> Abrupt {
        self.throw_kind(ErrorKind::RangeError, msg)
    }

    /// A thrown `SyntaxError`.
    pub(crate) fn syntax_error(&mut self, msg: &str) -> Abrupt {
        self.throw_kind(ErrorKind::SyntaxError, msg)
    }

    // -----------------------------------------------------------------
    // Type conversions (§7.1), on primitives
    // -----------------------------------------------------------------

    /// ToBoolean, §7.1.2.
    pub(crate) fn to_boolean(&self, v: Value) -> bool {
        match v.decode() {
            Decoded::Undefined | Decoded::Null | Decoded::Hole | Decoded::Raw(_) => false,
            Decoded::Bool(b) => b,
            Decoded::Int32(i) => i != 0,
            Decoded::Double(d) => !(d == 0.0 || d.is_nan()),
            Decoded::Ref(_) => self.heap.string(v).is_none_or(|s| !s.is_empty()),
        }
    }

    /// ToNumber, §7.1.4†, for primitives; an object needs ToPrimitive.
    pub(crate) fn coerce_number(&mut self, v: Value) -> Result<Num, Abrupt> {
        match v.decode() {
            Decoded::Int32(i) => Ok(Num::I(i)),
            Decoded::Double(d) => Ok(Num::D(d)),
            Decoded::Undefined => Ok(Num::D(f64::NAN)),
            Decoded::Null => Ok(Num::I(0)),
            Decoded::Bool(b) => Ok(Num::I(i32::from(b))),
            Decoded::Ref(_) => match self.heap.string(v) {
                Some(s) => Ok(numeric::narrow(clazel_js_number::string_to_number(
                    &s.to_string_lossy(),
                ))),
                None => Err(Abrupt::NotYet("ToPrimitive of an object".into())),
            },
            Decoded::Hole | Decoded::Raw(_) => {
                Err(Abrupt::Internal("an internal value reached ToNumber"))
            }
        }
    }

    /// The Number in register `r`, converted if need be.
    pub(crate) fn number_in_reg(&mut self, r: u32) -> Result<Num, Abrupt> {
        let v = self.r(r)?;
        match num(v) {
            Some(n) => Ok(n),
            None => self.coerce_number(v),
        }
    }

    /// ToString, §7.1.17†, for primitives.
    pub(crate) fn coerce_js_string(&mut self, v: Value) -> Result<JsString, Abrupt> {
        let text = match v.decode() {
            Decoded::Undefined => "undefined".to_string(),
            Decoded::Null => "null".to_string(),
            Decoded::Bool(b) => if b { "true" } else { "false" }.to_string(),
            Decoded::Int32(i) => i.to_string(),
            Decoded::Double(d) => clazel_js_number::number_to_string(d),
            Decoded::Ref(_) => {
                return match self.heap.string(v) {
                    Some(s) => Ok(s.clone()),
                    None => Err(Abrupt::NotYet("ToPrimitive of an object".into())),
                };
            }
            Decoded::Hole | Decoded::Raw(_) => {
                return Err(Abrupt::Internal("an internal value reached ToString"));
            }
        };
        JsString::from_rust_str(&text).map_err(|_| Abrupt::OutOfMemory)
    }

    /// ToString as a value (the string itself when it is one).
    pub(crate) fn coerce_string_value(&mut self, v: Value) -> Result<Value, Abrupt> {
        if self.heap.is_string(v) {
            return Ok(v);
        }
        let s = self.coerce_js_string(v)?;
        Ok(self.heap.new_string(s)?)
    }

    /// ToPropertyKey, §7.1.19†, for primitives (no Symbols yet).
    pub(crate) fn coerce_property_key(&mut self, v: Value) -> Result<Key, Abrupt> {
        let s = self.coerce_js_string(v)?;
        Ok(self.heap.intern(&s)?)
    }

    // -----------------------------------------------------------------
    // Operators
    // -----------------------------------------------------------------

    /// `+` off the Number path, §13.15.3 ApplyStringOrNumericBinaryOperator:
    /// a string on either side concatenates the two ToStrings.
    pub(crate) fn add_slow(&mut self, x: Value, y: Value) -> Result<Value, Abrupt> {
        if self.heap.is_object(x) || self.heap.is_object(y) {
            return Err(Abrupt::NotYet("ToPrimitive of an object".into()));
        }
        if self.heap.is_string(x) || self.heap.is_string(y) {
            let (a, b) = (self.coerce_js_string(x)?, self.coerce_js_string(y)?);
            return match a.concat(&b) {
                Ok(s) => Ok(self.heap.new_string(s)?),
                Err(_) => Err(self.range_error("Invalid string length")),
            };
        }
        let (p, q) = (self.coerce_number(x)?, self.coerce_number(y)?);
        Ok(numeric::add(p, q))
    }

    /// The other binary arithmetic operators off the Number path: ToNumeric
    /// on both operands, then the Number operation.
    pub(crate) fn arith_slow(&mut self, op: ArithOp, x: Value, y: Value) -> Result<Value, Abrupt> {
        let p = self.coerce_number(x)?;
        let q = self.coerce_number(y)?;
        Ok(op.apply(p, q))
    }

    /// `<`, `<=`, `>`, `>=` off the Number path: IsLessThan, §7.2.12.
    pub(crate) fn relational(&mut self, op: Rel, x: Value, y: Value) -> Result<bool, Abrupt> {
        if self.heap.is_object(x) || self.heap.is_object(y) {
            return Err(Abrupt::NotYet("ToPrimitive of an object".into()));
        }
        if let (Some(a), Some(b)) = (self.heap.string(x), self.heap.string(y)) {
            // Step 3: both Strings: code unit order.
            let ord = a.compare(b);
            return Ok(match op {
                Rel::Lt => ord.is_lt(),
                Rel::Le => ord.is_le(),
                Rel::Gt => ord.is_gt(),
                Rel::Ge => ord.is_ge(),
            });
        }
        let (p, q) = (self.coerce_number(x)?, self.coerce_number(y)?);
        Ok(match op {
            Rel::Lt => numeric::lt(p, q),
            Rel::Le => numeric::le(p, q),
            Rel::Gt => numeric::gt(p, q),
            Rel::Ge => numeric::ge(p, q),
        })
    }

    /// IsStrictlyEqual, §7.2.14.
    pub(crate) fn strict_equals(&self, x: Value, y: Value) -> bool {
        if let (Some(a), Some(b)) = (num(x), num(y)) {
            return numeric::equal(a, b);
        }
        if let (Some(a), Some(b)) = (self.heap.string(x), self.heap.string(y)) {
            return a == b;
        }
        x == y
    }

    /// IsLooselyEqual, §7.2.13, for primitives; an object against a
    /// primitive needs ToPrimitive.
    pub(crate) fn loose_equals(&mut self, x: Value, y: Value) -> Result<bool, Abrupt> {
        let nullish = |v: Value| v == Value::UNDEFINED || v == Value::NULL;
        let (ox, oy) = (self.heap.is_object(x), self.heap.is_object(y));
        if ox && oy {
            return Ok(x == y); // Step 1.a, SameType: IsStrictlyEqual.
        }
        if nullish(x) || nullish(y) {
            return Ok(nullish(x) && nullish(y)); // Steps 2 to 4.
        }
        if ox || oy {
            return Err(Abrupt::NotYet("ToPrimitive of an object".into()));
        }
        let (sx, sy) = (self.heap.is_string(x), self.heap.is_string(y));
        if sx && sy {
            return Ok(self.strict_equals(x, y));
        }
        // Steps 6 to 12 on primitives: Booleans, Strings and Numbers all
        // meet at Numbers.
        let (p, q) = (self.coerce_number(x)?, self.coerce_number(y)?);
        Ok(numeric::equal(p, q))
    }

    /// `typeof`, §13.5.3.1.
    pub(crate) fn type_of(&self, v: Value) -> Value {
        match v.decode() {
            Decoded::Undefined | Decoded::Hole | Decoded::Raw(_) => self.atoms.undefined,
            Decoded::Null => self.atoms.object,
            Decoded::Bool(_) => self.atoms.boolean,
            Decoded::Int32(_) | Decoded::Double(_) => self.atoms.number,
            Decoded::Ref(_) => {
                if self.heap.is_string(v) {
                    self.atoms.string
                } else if self.heap.is_callable(v) {
                    self.atoms.function
                } else {
                    self.atoms.object
                }
            }
        }
    }

    // -----------------------------------------------------------------
    // Properties
    // -----------------------------------------------------------------

    /// An inline-cache hit for a get: the value, or `None` for a miss.
    pub(crate) fn ic_get(&self, base: Value, ic: u32) -> Option<Value> {
        let e = *self
            .codes
            .get(self.cur)?
            .ics
            .get(usize::try_from(ic).ok()?)?;
        if e.shape == 0 {
            return None;
        }
        let o = self.heap.obj(base)?;
        if o.shape.0 != e.shape {
            return None;
        }
        o.slots.get(usize::try_from(e.slot).ok()?).copied()
    }

    /// An inline-cache hit for a set: stores and returns true, or false for
    /// a miss.
    pub(crate) fn ic_set(&mut self, base: Value, ic: u32, v: Value) -> bool {
        let Some(e) = usize::try_from(ic)
            .ok()
            .and_then(|i| self.codes.get(self.cur)?.ics.get(i).copied())
        else {
            return false;
        };
        if e.shape == 0 {
            return false;
        }
        let Some(o) = self.heap.obj_mut(base) else {
            return false;
        };
        if o.shape.0 != e.shape {
            return false;
        }
        let Some(slot) = usize::try_from(e.slot)
            .ok()
            .and_then(|i| o.slots.get_mut(i))
        else {
            return false;
        };
        *slot = v;
        true
    }

    fn ic_install(&mut self, ic: Option<u32>, shape: u32, slot: u32) {
        let Some(ic) = ic.and_then(|i| usize::try_from(i).ok()) else {
            return;
        };
        if let Some(e) = self.codes.get_mut(self.cur).and_then(|f| f.ics.get_mut(ic)) {
            e.shape = shape;
            e.slot = slot;
        }
    }

    /// `[[Get]]` of `key` on a value, §6.2.5.5 GetValue step 3 and §10.1.8:
    /// an own or inherited data property of an object, `length` and the
    /// indices of a string, and a TypeError for `undefined` and `null`.
    pub(crate) fn get_property(
        &mut self,
        base: Value,
        key: Key,
        ic: Option<u32>,
    ) -> Result<Value, Abrupt> {
        match base.decode() {
            Decoded::Undefined | Decoded::Null => {
                let name = self.key_text(key);
                let what = if base == Value::NULL {
                    "null"
                } else {
                    "undefined"
                };
                Err(self.type_error(&format!(
                    "Cannot read properties of {what} (reading '{name}')"
                )))
            }
            Decoded::Ref(_) => match self.heap.cell(base) {
                Some(Cell::Object(_)) => match self.heap.find(base, key)? {
                    Some(f) => {
                        if f.own && !self.heap.is_dictionary(f.shape) {
                            self.ic_install(ic, f.shape.0, f.slot);
                        }
                        self.heap
                            .slot(f.holder, f.slot)
                            .ok_or(Abrupt::Internal("property slot"))
                    }
                    None => Ok(Value::UNDEFINED),
                },
                Some(Cell::Str(s)) => {
                    if key == self.atoms.k_length {
                        let n = i32::try_from(s.len()).map_err(|_| Abrupt::OutOfMemory)?;
                        return Ok(Value::int32(n));
                    }
                    let unit = self
                        .heap
                        .key_string(key)
                        .and_then(array_index)
                        .and_then(|i| s.unit(i));
                    match unit {
                        Some(u) => {
                            let c = JsString::from_units(&[u]).map_err(|_| Abrupt::OutOfMemory)?;
                            Ok(self.heap.new_string(c)?)
                        }
                        None => Err(Abrupt::NotYet("property of a String primitive".into())),
                    }
                }
                _ => Err(Abrupt::Internal("property get on an internal cell")),
            },
            _ => Err(Abrupt::NotYet("property of a primitive".into())),
        }
    }

    /// `obj[idx]`: a string's character at an integer index, else
    /// ToPropertyKey and `[[Get]]`.
    pub(crate) fn get_element(&mut self, base: Value, idx: Value) -> Result<Value, Abrupt> {
        if let (Some(s), Some(n)) = (self.heap.string(base), num(idx)) {
            let d = n.to_f64();
            if d >= 0.0 && d == d.trunc() && d < 4_294_967_295.0 {
                // Integral and in range: exact.
                if let Some(u) = s.unit(d as usize) {
                    let c = JsString::from_units(&[u]).map_err(|_| Abrupt::OutOfMemory)?;
                    return Ok(self.heap.new_string(c)?);
                }
            }
        }
        if base == Value::UNDEFINED || base == Value::NULL {
            let what = if base == Value::NULL {
                "null"
            } else {
                "undefined"
            };
            return Err(self.type_error(&format!("Cannot read properties of {what}")));
        }
        let key = self.coerce_property_key(idx)?;
        self.get_property(base, key, None)
    }

    /// `[[Set]]` of `key` on a value (PutValue §6.2.5.6, OrdinarySet
    /// §10.1.9.2 for data properties): sets an own writable property, adds a
    /// property when none is found (or an inherited writable one is shadowed),
    /// and fails on a read-only one: a TypeError in strict code, nothing in
    /// sloppy code.
    pub(crate) fn set_property(
        &mut self,
        base: Value,
        key: Key,
        v: Value,
        ic: Option<u32>,
    ) -> Result<(), Abrupt> {
        if base == Value::UNDEFINED || base == Value::NULL {
            let name = self.key_text(key);
            return Err(self.type_error(&format!(
                "Cannot set properties of {} (setting '{name}')",
                if base == Value::NULL {
                    "null"
                } else {
                    "undefined"
                }
            )));
        }
        if !self.heap.is_object(base) {
            // A primitive receiver: OrdinarySet step 2.d.i "If Receiver is
            // not an Object, return false".
            if self.strict() {
                let name = self.key_text(key);
                return Err(
                    self.type_error(&format!("Cannot create property '{name}' on a primitive"))
                );
            }
            return Ok(());
        }
        let ok = match self.heap.find(base, key)? {
            Some(f) if f.attrs.0 & Attrs::WRITABLE == 0 => false,
            Some(f) if f.own => {
                self.heap.set_slot(base, f.slot, v)?;
                if !self.heap.is_dictionary(f.shape) {
                    self.ic_install(ic, f.shape.0, f.slot);
                }
                true
            }
            _ => {
                self.heap.define(base, key, v, Attrs::ALL)?;
                true
            }
        };
        if !ok && self.strict() {
            let name = self.key_text(key);
            return Err(self.type_error(&format!("Cannot assign to read only property '{name}'")));
        }
        Ok(())
    }

    /// The text of a key, for messages.
    pub(crate) fn key_text(&self, key: Key) -> String {
        self.heap
            .key_string(key)
            .map(JsString::to_string_lossy)
            .unwrap_or_default()
    }

    // -----------------------------------------------------------------
    // Closures
    // -----------------------------------------------------------------

    /// OrdinaryFunctionCreate §10.2.3 and SetFunctionLength, SetFunctionName
    /// (§10.2.10†): a closure over `env` of function `code`, with `length` and
    /// `name`. (`prototype` comes with `[[Construct]]`, not yet.)
    pub(crate) fn new_closure(&mut self, code: usize, env: Value) -> Result<Value, Abrupt> {
        let (length, name_value, name_units, code_kind) = {
            let f = self
                .codes
                .get(code)
                .ok_or(Abrupt::Internal("closure of an unknown function"))?;
            (
                f.code.length,
                f.name_value,
                f.code.name.clone(),
                f.code.kind,
            )
        };
        let name_value = match name_value {
            Some(v) => v,
            None => {
                let s = JsString::from_units(&name_units).map_err(|_| Abrupt::OutOfMemory)?;
                let v = self.heap.new_string(s)?;
                if let Some(f) = self.codes.get_mut(code) {
                    f.name_value = Some(v);
                }
                v
            }
        };
        let code_u32 = u32::try_from(code).map_err(|_| Abrupt::Internal("function index"))?;
        let proto = self.atoms.function_proto;
        let f = self.heap.new_object(
            proto,
            ObjKind::Closure {
                code: code_u32,
                env,
            },
        )?;
        let len = i32::try_from(length).map_err(|_| Abrupt::Internal("function length"))?;
        let (kl, kn) = (self.atoms.k_length, self.atoms.k_name);
        self.heap
            .define(f, kl, Value::int32(len), CONFIGURABLE_ONLY)?;
        self.heap.define(f, kn, name_value, CONFIGURABLE_ONLY)?;
        if is_constructor_kind(code_kind) {
            // MakeConstructor, §10.2.5†: `prototype` is a fresh object whose
            // `constructor` is the function (writable, not enumerable, not
            // configurable on the function; writable and configurable on the
            // prototype).
            let object_proto = self.atoms.object_proto;
            let p = self.heap.new_object(object_proto, ObjKind::Plain)?;
            let (kc, kp) = (self.atoms.k_constructor, self.atoms.k_prototype);
            self.heap.define(p, kc, f, WRITABLE_CONFIGURABLE)?;
            self.heap.define(f, kp, p, Attrs(Attrs::WRITABLE))?;
        }
        Ok(f)
    }

    /// `[[Construct]]` of a function value, §10.2.2, for a base constructor
    /// (`function`): `this` is a new object whose prototype is the function's
    /// `prototype` property when that is an object, else `%Object.prototype%`
    /// (OrdinaryCreateFromConstructor, §10.1.13); the body runs in a frame of
    /// kind construct, whose return gives the object. Class constructors and
    /// native constructors are not yet.
    pub(crate) fn construct(
        &mut self,
        f: Value,
        args: &[Value],
        ret: Option<usize>,
    ) -> Result<(), Abrupt> {
        let code = match self.heap.obj(f).map(|o| o.kind) {
            Some(ObjKind::Closure { code, .. }) => code,
            Some(ObjKind::Native(_)) => {
                return Err(Abrupt::NotYet("constructing a native function".into()));
            }
            _ => return Err(self.type_error("value is not a constructor")),
        };
        let kind = self
            .codes
            .get(usize::try_from(code).map_err(|_| Abrupt::Internal("code index"))?)
            .map(|c| c.code.kind)
            .ok_or(Abrupt::Internal("code index"))?;
        match kind {
            FunctionKind::Normal => {}
            FunctionKind::Class | FunctionKind::Derived => {
                return Err(Abrupt::NotYet("class constructors".into()));
            }
            _ => return Err(self.type_error("value is not a constructor")),
        }
        let kp = self.atoms.k_prototype;
        let proto = match self.heap.find(f, kp)? {
            Some(found) => self.heap.slot(found.holder, found.slot),
            None => None,
        };
        let proto = match proto {
            Some(p) if self.heap.is_object(p) => p,
            _ => self.atoms.object_proto,
        };
        let this = self.heap.new_object(proto, ObjKind::Plain)?;
        self.enter_closure(f, code, this, args, ret, crate::frame::KIND_CONSTRUCT)
    }

    // -----------------------------------------------------------------
    // Globals
    // -----------------------------------------------------------------

    /// GetValue of an identifier reference that resolved in the global
    /// environment (§9.1.1.4.1† HasBinding, §9.1.1.4.6† GetBindingValue): the
    /// declarative record first (a hole is the temporal dead zone), then the
    /// global object. An unresolvable reference is a ReferenceError when
    /// `throw_unresolvable`, else `undefined` (`typeof`'s operand).
    pub(crate) fn get_global(
        &mut self,
        key: Key,
        throw_unresolvable: bool,
    ) -> Result<Value, Abrupt> {
        if let Some(&(v, _)) = self.global_lex.get(&key) {
            if v == Value::HOLE {
                let name = self.key_text(key);
                return Err(
                    self.reference_error(&format!("Cannot access '{name}' before initialization"))
                );
            }
            return Ok(v);
        }
        let global = self.global;
        match self.heap.find(global, key)? {
            Some(f) => self
                .heap
                .slot(f.holder, f.slot)
                .ok_or(Abrupt::Internal("global property slot")),
            None if throw_unresolvable => {
                let name = self.key_text(key);
                Err(self.reference_error(&format!("{name} is not defined")))
            }
            None => Ok(Value::UNDEFINED),
        }
    }

    /// PutValue on an identifier reference resolved in the global
    /// environment (§9.1.1.4.5† SetMutableBinding).
    pub(crate) fn set_global(&mut self, key: Key, v: Value) -> Result<(), Abrupt> {
        if let Some(&(old, is_const)) = self.global_lex.get(&key) {
            let name = self.key_text(key);
            if old == Value::HOLE {
                return Err(
                    self.reference_error(&format!("Cannot access '{name}' before initialization"))
                );
            }
            if is_const {
                return Err(self.type_error("Assignment to constant variable."));
            }
            if let Some(entry) = self.global_lex.get_mut(&key) {
                entry.0 = v;
            }
            return Ok(());
        }
        let global = self.global;
        if self.heap.find(global, key)?.is_none() && self.strict() {
            // §9.1.1.2.5† step 4 on an unresolvable reference in strict code.
            let name = self.key_text(key);
            return Err(self.reference_error(&format!("{name} is not defined")));
        }
        self.set_property(global, key, v, None)
    }

    /// GlobalDeclarationInstantiation, §16.1.7†, steps 1 to 18 (see
    /// [`crate::ops::Op::DeclareGlobals`]). The checks come before any
    /// binding is created.
    pub(crate) fn declare_globals(&mut self, k: u32) -> Result<(), Abrupt> {
        let (decls, base) = {
            let f = self
                .codes
                .get(self.cur)
                .ok_or(Abrupt::Internal("code index"))?;
            let i = usize::try_from(k).map_err(|_| Abrupt::Internal("constant index"))?;
            match f.code.consts.get(i) {
                Some(Const::GlobalDeclarations(d)) => (d.clone(), f.base),
                _ => {
                    return Err(Abrupt::Internal(
                        "DeclareGlobals without a declaration record",
                    ));
                }
            }
        };
        let global = self.global;
        let mut lexical = Vec::new();
        for (name, is_const) in &decls.lexical {
            lexical.push((self.name_key(name)?, *is_const));
        }
        let mut var_names = Vec::new();
        let mut functions = Vec::new();
        for d in &decls.var_scoped {
            match d {
                VarScoped::Var(n) => var_names.push(self.name_key(n)?),
                VarScoped::Function { name, func } => {
                    let key = self.name_key(name)?;
                    var_names.push(key);
                    functions.push((key, *func));
                }
            }
        }
        let mut annexb = Vec::new();
        for n in &decls.annexb {
            annexb.push(self.name_key(n)?);
        }
        // Steps 3 and 4: a lexical name may not clash with a var name or a
        // lexical binding (HasVarDeclaration, HasLexicalDeclaration), nor with
        // a non-configurable global property (HasRestrictedGlobalProperty).
        for (key, _) in &lexical {
            let restricted = match self.heap.find(global, *key)? {
                Some(f) => f.own && f.attrs.0 & Attrs::CONFIGURABLE == 0,
                None => false,
            };
            if self.var_names.contains(key) || self.global_lex.contains_key(key) || restricted {
                let name = self.key_text(*key);
                return Err(
                    self.syntax_error(&format!("Identifier '{name}' has already been declared"))
                );
            }
        }
        // Step 5: a var name may not clash with a lexical binding.
        for key in &var_names {
            if self.global_lex.contains_key(key) {
                let name = self.key_text(*key);
                return Err(
                    self.syntax_error(&format!("Identifier '{name}' has already been declared"))
                );
            }
        }
        // Step 8 and 10: CanDeclareGlobalFunction: an existing property must be
        // configurable, or a writable enumerable data property (the global
        // object is extensible).
        for (key, _) in &functions {
            if let Some(f) = self.heap.find(global, *key)? {
                let ok = f.own
                    && (f.attrs.0 & Attrs::CONFIGURABLE != 0
                        || f.attrs.0 & (Attrs::WRITABLE | Attrs::ENUMERABLE)
                            == (Attrs::WRITABLE | Attrs::ENUMERABLE));
                if f.own && !ok {
                    let name = self.key_text(*key);
                    return Err(
                        self.type_error(&format!("Cannot declare global function '{name}'"))
                    );
                }
            }
        }
        // Step 15: the lexical bindings, uninitialized.
        for (key, is_const) in &lexical {
            self.global_lex.insert(*key, (Value::HOLE, *is_const));
        }
        // Step 16: the function objects (the last declaration of a name wins).
        for (key, func) in &functions {
            let code = base
                .checked_add(*func)
                .ok_or(Abrupt::Internal("function index"))?;
            let code = usize::try_from(code).map_err(|_| Abrupt::Internal("function index"))?;
            let f = self.new_closure(code, Value::UNDEFINED)?;
            self.heap.define(global, *key, f, GLOBAL_VAR)?;
            self.var_names.insert(*key);
        }
        // Step 17: the variables.
        for key in &var_names {
            if self.heap.find(global, *key)?.is_none() {
                self.heap
                    .define(global, *key, Value::UNDEFINED, GLOBAL_VAR)?;
            }
            self.var_names.insert(*key);
        }
        // Step 12 (Annex B.3.2.2†): functions in blocks, when no lexical
        // binding of the name exists.
        for key in &annexb {
            if !self.global_lex.contains_key(key) && self.heap.find(global, *key)?.is_none() {
                self.heap
                    .define(global, *key, Value::UNDEFINED, GLOBAL_VAR)?;
                self.var_names.insert(*key);
            }
        }
        Ok(())
    }

    fn name_key(&mut self, units: &[u16]) -> Result<Key, Abrupt> {
        let s = JsString::from_units(units).map_err(|_| Abrupt::OutOfMemory)?;
        Ok(self.heap.intern(&s)?)
    }

    // -----------------------------------------------------------------
    // Embedding helpers (used by natives and by hosts)
    // -----------------------------------------------------------------

    /// A new string value.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn new_string(&mut self, s: &str) -> Result<Value, Abrupt> {
        Ok(self.heap.new_str(s)?)
    }

    /// The text of a string value, if it is one.
    #[must_use]
    pub fn string_text(&self, v: Value) -> Option<String> {
        self.heap.string(v).map(JsString::to_string_lossy)
    }

    /// A new ordinary object.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn new_object(&mut self) -> Result<Value, Abrupt> {
        let proto = self.atoms.object_proto;
        Ok(self.heap.new_object(proto, ObjKind::Plain)?)
    }

    /// A new native function with `length` and `name`.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn new_native(
        &mut self,
        name: &str,
        length: i32,
        f: crate::interp::NativeFn,
    ) -> Result<Value, Abrupt> {
        let index = u32::try_from(self.natives.len()).map_err(|_| Abrupt::OutOfMemory)?;
        self.natives.push(f);
        let proto = self.atoms.function_proto;
        let o = self.heap.new_object(proto, ObjKind::Native(index))?;
        let name_v = self.heap.new_str(name)?;
        let (kl, kn) = (self.atoms.k_length, self.atoms.k_name);
        self.heap
            .define(o, kl, Value::int32(length), CONFIGURABLE_ONLY)?;
        self.heap.define(o, kn, name_v, CONFIGURABLE_ONLY)?;
        Ok(o)
    }

    /// Defines (or overwrites) a writable, enumerable, configurable data
    /// property `name` of `obj`.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`] or [`Abrupt::Internal`] if `obj` is not an
    /// object.
    pub fn define_property(&mut self, obj: Value, name: &str, v: Value) -> Result<(), Abrupt> {
        let key = self.heap.intern_str(name)?;
        Ok(self.heap.define(obj, key, v, Attrs::ALL)?)
    }

    /// Defines a property of the global object.
    ///
    /// # Errors
    /// As [`Vm::define_property`].
    pub fn define_global(&mut self, name: &str, v: Value) -> Result<(), Abrupt> {
        let g = self.global;
        self.define_property(g, name, v)
    }

    /// `obj[name]`, for an own or inherited data property: `undefined` when
    /// there is none.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`] or [`Abrupt::Internal`].
    pub fn get_named(&mut self, obj: Value, name: &str) -> Result<Value, Abrupt> {
        let key = self.heap.intern_str(name)?;
        match self.heap.find(obj, key)? {
            Some(f) => self
                .heap
                .slot(f.holder, f.slot)
                .ok_or(Abrupt::Internal("slot")),
            None => Ok(Value::UNDEFINED),
        }
    }

    /// A short description of a value, for failure reports: a string's text,
    /// a Number, or an error object's `name: message`.
    pub fn describe(&mut self, v: Value) -> String {
        match v.decode() {
            Decoded::Ref(_) => {
                if let Some(s) = self.string_text(v) {
                    return format!("{s:?}");
                }
                let name = self
                    .get_named(v, "name")
                    .ok()
                    .and_then(|n| self.string_text(n));
                let message = self
                    .get_named(v, "message")
                    .ok()
                    .and_then(|m| self.string_text(m));
                match (name, message) {
                    (Some(n), Some(m)) => format!("{n}: {m}"),
                    (None, Some(m)) => m,
                    _ => "[object]".to_string(),
                }
            }
            _ => self
                .coerce_js_string(v)
                .map(|s| s.to_string_lossy())
                .unwrap_or_default(),
        }
    }
}

/// The array index a canonical numeric string names: decimal digits, no
/// leading zero (except `0`), below 2^32 - 1 (§6.1.7).
fn array_index(s: &JsString) -> Option<usize> {
    let mut n: u64 = 0;
    let mut len = 0usize;
    let mut first = 0u16;
    for u in s.units() {
        let d = u.checked_sub(u16::from(b'0')).filter(|d| *d < 10)?;
        if len == 0 {
            first = u;
        }
        n = n.checked_mul(10)?.checked_add(u64::from(d))?;
        len = len.checked_add(1)?;
    }
    if len == 0 || (len > 1 && first == u16::from(b'0')) || n >= 4_294_967_295 {
        return None;
    }
    usize::try_from(n).ok()
}

/// Whether a closure of this kind has a `prototype` (§10.2.3† step 4:
/// OrdinaryFunctionCreate then MakeConstructor for a `function`; arrows and
/// methods have none; a class's `prototype` is made by `ClassSetup`).
fn is_constructor_kind(k: FunctionKind) -> bool {
    k == FunctionKind::Normal
}
