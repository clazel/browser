//! The handlers of the class ops (phase-7.md item 7.8; the ops are specified in
//! [`crate::ops`], and the compiler emits them in `compile/classes.rs`):
//! `ClassSetup`, `SetHomeObject`, `SetInstanceInit`, `InitInstance`,
//! `SuperCall`, `SuperCallSpread`, `GetSuperBase`, `GetSuper`, `SetSuper`,
//! `GetNewTarget`, `ConstructResult`, `NewPrivateName`, `GetPrivate`,
//! `SetPrivate`, `DefinePrivate`, `HasPrivate`, and `[[Construct]]` of class
//! constructors (§10.2.2†).
//!
//! # Modelling choices
//!
//! - **`[[HomeObject]]`, the instance initializer and the private elements**
//!   are tables of the VM ([`ClassState`]), keyed by the function or object
//!   they belong to, not slots of the heap cells: no cell has a place for
//!   them. A private element of an object is the entry of the pair (object,
//!   Private Name); a Private Name is a Symbol cell that no script can name
//!   (it is never a property key, so `Object.getOwnPropertySymbols` does not
//!   see the elements). Nothing is collected in this VM (item 7.6), so the
//!   tables hold no object alive that was not.
//! - **`new.target` of a closure** is kept for each construct frame in a stack
//!   of (frame base, value) pairs ([`ClassState::new_targets`]): the frame
//!   header has four slots (`spec::hdr_slots`) and none is free. The target of
//!   a call by `new` is the function itself, so the entry is only needed when
//!   `super(...)` passes another one.
//! - **`super(...)` constructs to completion**, re-entering the interpreter
//!   as a native does (`construct_value`), so the checks of §13.3.7.1† steps 8
//!   and 9 (BindThisValue's "already initialized" error after the
//!   construction) run when the base constructor has returned.

use crate::heap::{ACCESSOR, ObjKind};
use crate::interp::{Abrupt, Intrinsic, Vm};
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::Key;
use clazel_js_heap::value::Value;
use std::collections::HashMap;

/// A private element of an object (§6.2.12† PrivateElement): a field, a
/// method or an accessor.
#[derive(Clone, Copy, Debug)]
pub(crate) enum PrivateElement {
    /// `[[Kind]]` field: `[[Value]]`.
    Field(Value),
    /// `[[Kind]]` method: `[[Value]]`, a function.
    Method(Value),
    /// `[[Kind]]` accessor: `[[Get]]` and `[[Set]]`, each a function or
    /// `undefined`.
    Accessor { get: Value, set: Value },
}

/// What the class ops add to a [`Vm`] (see the module header).
#[derive(Debug, Default)]
pub(crate) struct ClassState {
    /// `[[HomeObject]]` of a method, by the function.
    pub(crate) home_objects: HashMap<Value, Value>,
    /// The instance initializer of a class constructor (its `[[Fields]]` and
    /// `[[PrivateMethods]]`), by the constructor.
    pub(crate) instance_inits: HashMap<Value, Value>,
    /// `[[PrivateElements]]`, by (object, Private Name).
    pub(crate) private: HashMap<(Value, Value), PrivateElement>,
    /// The `new.target` of construct frames, by frame base.
    pub(crate) new_targets: Vec<(usize, Value)>,
}

impl Vm {
    /// Records the `new.target` of the running (just entered) construct frame.
    pub(crate) fn register_new_target(&mut self, new_target: Value) {
        let fp = self.fp;
        let st = &mut self.host.class;
        while st.new_targets.last().is_some_and(|(b, _)| *b >= fp) {
            st.new_targets.pop();
        }
        st.new_targets.push((fp, new_target));
    }

    /// `GetNewTarget`, §9.4.4† and §13.3.12.1†: the running closure's
    /// `new.target`, `undefined` for a call.
    pub(crate) fn current_new_target(&self) -> Result<Value, Abrupt> {
        let (_, kind) =
            crate::frame::dec_argc(self.region.header(self.fp, crate::frame::HDR_ARGC)?)
                .ok_or(Abrupt::Internal("argument count slot"))?;
        if kind != crate::frame::KIND_CONSTRUCT {
            return Ok(Value::UNDEFINED);
        }
        let found = self
            .host
            .class
            .new_targets
            .iter()
            .rev()
            .find(|(b, _)| *b == self.fp)
            .map(|(_, v)| *v);
        match found {
            Some(v) => Ok(v),
            None => Ok(self.region.header(self.fp, crate::frame::HDR_CALLEE)?),
        }
    }

    /// `[[Construct]] ( argumentsList, newTarget )` of a function value that
    /// is a closure of kind Class or Derived, or a plain `function`, §10.2.2†:
    /// 1. Let callerContext be the running execution context.
    /// 2. Let kind be F.[[ConstructorKind]].
    /// 3. If kind is base, then a. Let thisArgument be ?
    ///    OrdinaryCreateFromConstructor(newTarget, "%Object.prototype%").
    /// 4. Let calleeContext be PrepareForOrdinaryCall(F, newTarget).
    /// 5. (Assert: calleeContext is now the running execution context.)
    /// 6. If kind is base, then a. Perform OrdinaryCallBindThis(F, calleeContext,
    ///    thisArgument). b. Let initializeResult be Completion(
    ///    InitializeInstanceElements(thisArgument, F)). (The class
    ///    constructor's own prologue runs `InitInstance`.)
    /// 7. Let constructorEnv be the LexicalEnvironment of calleeContext.
    /// 8. Let result be Completion(OrdinaryCallEvaluateBody(F, argumentsList)).
    /// 9. to 12. (The result, in `do_return` and `ConstructResult`.)
    ///
    /// The frame is entered; the return writes the call op's `dst`.
    pub(crate) fn construct_closure(
        &mut self,
        f: Value,
        code: u32,
        args: &[Value],
        ret: Option<usize>,
        new_target: Value,
        derived: bool,
    ) -> Result<(), Abrupt> {
        let this = if derived {
            Value::HOLE
        } else {
            self.create_from_constructor(new_target, Intrinsic::ObjectPrototype, ObjKind::Plain)?
        };
        self.enter_closure(f, code, this, args, ret, crate::frame::KIND_CONSTRUCT)?;
        self.register_new_target(new_target);
        Ok(())
    }

    // -----------------------------------------------------------------
    // ClassSetup, SetHomeObject, SetInstanceInit, InitInstance
    // -----------------------------------------------------------------

    /// `ClassSetup`: ClassDefinitionEvaluation §15.7.14† steps 5 to 14 and 16
    /// to 17, and MakeClassConstructor §10.2.5†:
    /// 5. If ClassHeritage is not present, then a. Let protoParent be
    ///    %Object.prototype%. b. Let constructorParent be %Function.prototype%.
    /// 6. Else, ... a. Let superclass be ? GetValue(?
    ///    Evaluation of ClassHeritage). b. If superclass is null, then i. Let
    ///    protoParent be null. ii. Let constructorParent be
    ///    %Function.prototype%. c. Else if IsConstructor(superclass) is false,
    ///    throw a TypeError exception. d. Else, i. Let protoParent be ?
    ///    Get(superclass, "prototype"). ii. If protoParent is not an Object and
    ///    protoParent is not null, throw a TypeError exception. iii. Let
    ///    constructorParent be superclass.
    /// 7. Let proto be OrdinaryObjectCreate(protoParent).
    /// 14. (SetFunctionLength and the rest, by the closure itself.) Perform
    ///    MakeConstructor(F, false, proto): `prototype` is { [[Writable]]:
    ///    false, [[Enumerable]]: false, [[Configurable]]: false }.
    /// 16. Perform MakeClassConstructor(F). 17. Perform CreateMethodProperty(
    ///    proto, "constructor", F).
    pub(crate) fn class_setup(
        &mut self,
        ctor: Value,
        heritage: Value,
        derived: bool,
    ) -> Result<Value, Abrupt> {
        let (proto_parent, ctor_parent) = if !derived {
            (self.atoms.object_proto, self.atoms.function_proto)
        } else if heritage == Value::NULL {
            (Value::NULL, self.atoms.function_proto)
        } else {
            if !self.is_constructor(heritage) {
                let text = self.describe(heritage);
                return Err(self.type_error(&format!(
                    "Class extends value {text} is not a constructor or null"
                )));
            }
            let kp = self.atoms.k_prototype;
            let pp = self.get_property(heritage, kp, None)?;
            if pp != Value::NULL && !self.heap.is_object(pp) {
                return Err(
                    self.type_error("Class extends value does not have valid prototype property")
                );
            }
            (pp, heritage)
        };
        let proto = self.heap.new_object(proto_parent, ObjKind::Plain)?;
        self.heap.set_proto(ctor, ctor_parent)?;
        let (kp, kc) = (self.atoms.k_prototype, self.atoms.k_constructor);
        self.heap.redefine(ctor, kp, proto, Attrs(0))?;
        self.heap.define(
            proto,
            kc,
            ctor,
            Attrs(Attrs::WRITABLE | Attrs::CONFIGURABLE),
        )?;
        self.host.class.home_objects.insert(ctor, proto);
        Ok(proto)
    }

    /// `SuperCall`, §13.3.7.1† (Runtime Semantics: Evaluation, SuperCall :
    /// `super` Arguments):
    /// 1. Let newTarget be GetNewTarget(). 2. Assert: newTarget is an Object.
    /// 3. Let func be GetSuperConstructor(). 4. Let argList be ? ArgumentListEvaluation
    ///    of Arguments. 5. If IsConstructor(func) is false, throw a TypeError
    ///    exception. 6. Let result be ? Construct(func, argList, newTarget).
    /// 7. Let thisER be GetThisEnvironment(). 8. Perform ? thisER.BindThisValue(result)
    ///    (BindThisValue §9.1.1.3.1† step 1: if the this binding is already
    ///    initialized, throw a ReferenceError). 9. Let F be thisER.[[FunctionObject]].
    ///    10. Perform ? InitializeInstanceElements(result, F). 11. Return result.
    ///
    /// GetSuperConstructor (§13.3.7.2†): `activeFunction.[[GetPrototypeOf]]()`.
    /// Steps 8 and 10 are the next ops of the compiled code (the `this`
    /// binding's initialization and `InitInstance`).
    pub(crate) fn super_call(
        &mut self,
        func: Value,
        new_target: Value,
        this: Value,
        args: &[Value],
    ) -> Result<Value, Abrupt> {
        let sc = self.heap.proto_of(func).unwrap_or(Value::NULL);
        if !self.is_constructor(sc) {
            return Err(self.type_error("Super constructor is not a constructor"));
        }
        let result = self.construct_with_target(sc, args, new_target)?;
        if this != Value::HOLE {
            return Err(self.reference_error("Super constructor may only be called once"));
        }
        Ok(result)
    }

    /// InitializeInstanceElements ( O, constructor ), §7.3.34†:
    /// 1. If constructor.[[PrivateMethods]] ... 2. For each PrivateElement
    ///    method of methods, do a. Perform ? PrivateMethodOrAccessorAdd(O,
    ///    method). 3. Let fields be constructor.[[Fields]]. 4. For each
    ///    element fieldRecord of fields, do a. Perform ? DefineField(O,
    ///    fieldRecord). 5. Return unused.
    ///
    /// The instance initializer is one closure that does steps 2 to 4 with `O`
    /// as its `this`.
    pub(crate) fn initialize_instance(&mut self, obj: Value, func: Value) -> Result<(), Abrupt> {
        if let Some(init) = self.host.class.instance_inits.get(&func).copied() {
            self.call(init, obj, &[])?;
        }
        Ok(())
    }

    /// `GetSuperBase`, §9.1.1.3.5†: 1. Let home be envRec.[[FunctionObject]].[[HomeObject]].
    /// 2. If home is undefined, return undefined. 3. Assert: home is an
    /// Object. 4. Return ? home.[[GetPrototypeOf]]().
    pub(crate) fn super_base(&self, func: Value) -> Result<Value, Abrupt> {
        let Some(home) = self.host.class.home_objects.get(&func).copied() else {
            return Ok(Value::UNDEFINED);
        };
        Ok(self.heap.proto_of(home).unwrap_or(Value::NULL))
    }

    /// GetValue of a super reference, §6.2.5.5† step 3.b: `baseObj.[[Get]](key,
    /// this)`, with `baseObj` = ? ToObject(base) (a `null` base is a
    /// TypeError). OrdinaryGet §10.1.8.1†: the getter is called with `this`.
    pub(crate) fn get_super(
        &mut self,
        base: Value,
        key: Value,
        this: Value,
    ) -> Result<Value, Abrupt> {
        let k = self.coerce_property_key(key)?;
        if !self.heap.is_object(base) {
            return Err(self.type_error("Cannot read properties of a null super base"));
        }
        match self.heap.find(base, k)? {
            Some(f) => self.found_value(f, this),
            None => Ok(Value::UNDEFINED),
        }
    }

    /// PutValue of a super reference, §6.2.5.6† steps 5.b to 5.d:
    /// `baseObj.[[Set]](key, value, this)`, OrdinarySet (§10.1.9.1†) with
    /// receiver `this`, which in strict code throws a TypeError for false.
    ///
    /// OrdinarySetWithOwnDescriptor (§10.1.9.2†) with the descriptor found on
    /// the base's chain (step 1.b "ownDesc is the parent's"):
    /// 2. If IsDataDescriptor(ownDesc) is true, then a. If ownDesc.[[Writable]]
    ///    is false, return false. b. If Receiver is not an Object, return
    ///    false. c. Let existingDescriptor be ? Receiver.[[GetOwnProperty]](P).
    ///    d. If existingDescriptor is not undefined, then i. If
    ///    IsAccessorDescriptor(existingDescriptor) is true, return false. ii.
    ///    If existingDescriptor.[[Writable]] is false, return false. iii. Let
    ///    valueDesc be the PropertyDescriptor { [[Value]]: V }. iv. Return ?
    ///    Receiver.[[DefineOwnProperty]](P, valueDesc). e. Else, i. Return ?
    ///    CreateDataProperty(Receiver, P, V).
    /// 3. (accessors) the setter is called with Receiver; no setter is false.
    pub(crate) fn set_super(
        &mut self,
        base: Value,
        key: Value,
        v: Value,
        this: Value,
    ) -> Result<(), Abrupt> {
        let k = self.coerce_property_key(key)?;
        if !self.heap.is_object(base) {
            return Err(self.type_error("Cannot set properties of a null super base"));
        }
        let ok = self.ordinary_set(base, k, v, this)?;
        if !ok && self.strict() {
            let name = self.key_text(k);
            return Err(self.type_error(&format!("Cannot assign to read only property '{name}'")));
        }
        Ok(())
    }

    /// `[[Get]] ( P, Receiver )` of an ordinary (or Array exotic) object,
    /// OrdinaryGet §10.1.8.1†: the property found on the chain of `obj`, its
    /// getter called with `receiver`.
    ///
    /// # Errors
    /// What a getter throws.
    pub fn get_with_receiver(
        &mut self,
        obj: Value,
        key: Key,
        receiver: Value,
    ) -> Result<Value, Abrupt> {
        match self.heap.find(obj, key)? {
            Some(f) => self.found_value(f, receiver),
            None => Ok(Value::UNDEFINED),
        }
    }

    /// `[[Set]] ( P, V, Receiver )` of an ordinary (or Array exotic) object,
    /// OrdinarySet §10.1.9.1† with OrdinarySetWithOwnDescriptor §10.1.9.2†,
    /// the descriptor being the one found on the chain of `obj`:
    /// 2. If IsDataDescriptor(ownDesc) is true, then a. If ownDesc.[[Writable]]
    ///    is false, return false. b. If Receiver is not an Object, return
    ///    false. c. Let existingDescriptor be ? Receiver.[[GetOwnProperty]](P).
    ///    d. If existingDescriptor is not undefined, then i. If
    ///    IsAccessorDescriptor(existingDescriptor) is true, return false. ii.
    ///    If existingDescriptor.[[Writable]] is false, return false. iii. Let
    ///    valueDesc be the PropertyDescriptor { [[Value]]: V }. iv. Return ?
    ///    Receiver.[[DefineOwnProperty]](P, valueDesc). e. Else, i. Return ?
    ///    CreateDataProperty(Receiver, P, V).
    /// 3. (An accessor) 4. Let setter be ownDesc.[[Set]]. 5. If setter is
    ///    undefined, return false. 6. Perform ? Call(setter, Receiver, « V »).
    ///    7. Return true.
    ///
    /// A property that is not found is the writable data property of step 1.b.
    ///
    /// # Errors
    /// What a setter or the definition throws.
    pub fn ordinary_set(
        &mut self,
        obj: Value,
        k: Key,
        v: Value,
        receiver: Value,
    ) -> Result<bool, Abrupt> {
        match self.heap.find(obj, k)? {
            Some(f) if f.attrs.0 & ACCESSOR != 0 => {
                let pair = self
                    .heap
                    .slot(f.holder, f.slot)
                    .ok_or(Abrupt::Internal("property slot"))?;
                let (_, setter) = self.accessor_pair(pair)?;
                if setter == Value::UNDEFINED {
                    Ok(false)
                } else {
                    self.call(setter, receiver, &[v])?;
                    Ok(true)
                }
            }
            Some(f) if f.attrs.0 & Attrs::WRITABLE == 0 => Ok(false),
            _ => self.set_on_receiver(receiver, k, v),
        }
    }

    /// Steps 2.b to 2.e of OrdinarySetWithOwnDescriptor (see [`Vm::set_super`]).
    fn set_on_receiver(&mut self, receiver: Value, k: Key, v: Value) -> Result<bool, Abrupt> {
        if !self.heap.is_object(receiver) {
            return Ok(false);
        }
        match self.own_property_descriptor(receiver, k)? {
            Some(existing) => {
                if existing.is_accessor() || existing.writable != Some(true) {
                    return Ok(false);
                }
                let d = crate::props::PropDesc {
                    value: Some(v),
                    ..crate::props::PropDesc::default()
                };
                self.define_own_property(receiver, k, &d)
            }
            None => self.create_data_property(receiver, k, v),
        }
    }

    /// ConstructResult: §10.2.2† [[Construct]] steps 10 to 12 for a derived
    /// constructor:
    /// 10. If result is a return completion, then a. If result.[[Value]] is an
    ///     Object, return result.[[Value]]. b. If kind is base, return
    ///     thisArgument. c. If result.[[Value]] is not undefined, throw a
    ///     TypeError exception.
    /// 11. (A normal completion.) 12. Let thisBinding be ?
    ///     constructorEnv.GetThisBinding() (§9.1.1.3.4†: the hole is a
    ///     ReferenceError). 13. Assert: thisBinding is an Object. 14. Return
    ///     thisBinding.
    pub(crate) fn construct_result(&mut self, val: Value, this: Value) -> Result<Value, Abrupt> {
        if self.heap.is_object(val) {
            return Ok(val);
        }
        if val != Value::UNDEFINED {
            return Err(self.type_error("Derived constructors may only return object or undefined"));
        }
        if this == Value::HOLE {
            return Err(self.reference_error(
                "Must call super constructor in derived class before accessing 'this' or returning from derived constructor",
            ));
        }
        Ok(this)
    }

    // -----------------------------------------------------------------
    // Private names
    // -----------------------------------------------------------------

    /// `NewPrivateName`, §6.2.12†: a new Private Name with description `desc`
    /// (a string value).
    pub(crate) fn new_private_name(&mut self, desc: Value) -> Result<Value, Abrupt> {
        self.new_symbol(desc)
    }

    fn private_text(&self, name: Value) -> String {
        self.heap
            .symbol(name)
            .and_then(|s| self.heap.string(s.description).map(|d| d.to_string_lossy()))
            .unwrap_or_default()
    }

    /// PrivateElementFind ( O, P ), §7.3.28†: the element of `O` named `P`.
    fn private_find(&self, obj: Value, name: Value) -> Option<PrivateElement> {
        self.host.class.private.get(&(obj, name)).copied()
    }

    /// PrivateGet ( O, P ), §7.3.31†:
    /// 1. Let entry be PrivateElementFind(O, P).
    /// 2. If entry is empty, throw a TypeError exception.
    /// 3. If entry.[[Kind]] is either field or method, then a. Return
    ///    entry.[[Value]].
    /// 4. Assert: entry.[[Kind]] is accessor.
    /// 5. If entry.[[Get]] is undefined, throw a TypeError exception.
    /// 6. Let getter be entry.[[Get]].
    /// 7. Return ? Call(getter, O).
    pub(crate) fn private_get(&mut self, obj: Value, name: Value) -> Result<Value, Abrupt> {
        let text = self.private_text(name);
        if !self.heap.is_object(obj) {
            return Err(self.type_error(&format!(
                "Cannot read private member {text} from a non-object"
            )));
        }
        match self.private_find(obj, name) {
            None => Err(self.type_error(&format!(
                "Cannot read private member {text} from an object whose class did not declare it"
            ))),
            Some(PrivateElement::Field(v) | PrivateElement::Method(v)) => Ok(v),
            Some(PrivateElement::Accessor { get, .. }) => {
                if get == Value::UNDEFINED {
                    return Err(self.type_error(&format!("'{text}' was defined without a getter")));
                }
                self.call(get, obj, &[])
            }
        }
    }

    /// PrivateSet ( O, P, value ), §7.3.32†:
    /// 1. Let entry be PrivateElementFind(O, P).
    /// 2. If entry is empty, throw a TypeError exception.
    /// 3. If entry.[[Kind]] is field, then a. Set entry.[[Value]] to value.
    /// 4. Else if entry.[[Kind]] is method, then a. Throw a TypeError exception.
    /// 5. Else, a. Assert: entry.[[Kind]] is accessor. b. If entry.[[Set]] is
    ///    undefined, throw a TypeError exception. c. Let setter be
    ///    entry.[[Set]]. d. Perform ? Call(setter, O, « value »).
    pub(crate) fn private_set(&mut self, obj: Value, name: Value, v: Value) -> Result<(), Abrupt> {
        let text = self.private_text(name);
        if !self.heap.is_object(obj) {
            return Err(self.type_error(&format!(
                "Cannot write private member {text} to a non-object"
            )));
        }
        match self.private_find(obj, name) {
            None => Err(self.type_error(&format!(
                "Cannot write private member {text} to an object whose class did not declare it"
            ))),
            Some(PrivateElement::Field(_)) => {
                self.host
                    .class
                    .private
                    .insert((obj, name), PrivateElement::Field(v));
                Ok(())
            }
            Some(PrivateElement::Method(_)) => {
                Err(self.type_error(&format!("Private method '{text}' is not writable")))
            }
            Some(PrivateElement::Accessor { set, .. }) => {
                if set == Value::UNDEFINED {
                    return Err(self.type_error(&format!("'{text}' was defined without a setter")));
                }
                self.call(set, obj, &[v])?;
                Ok(())
            }
        }
    }

    /// PrivateFieldAdd ( O, P, value ), §7.3.30†, and PrivateMethodOrAccessorAdd
    /// ( O, method ), §7.3.31† (`form` 0 field, 1 method, 2 getter, 3 setter):
    /// 1. (Proxy check.) 2. Let entry be PrivateElementFind(O, P). 3. If entry
    ///    is not empty, throw a TypeError exception. 4. Append the element to
    ///    O.[[PrivateElements]].
    ///
    /// A getter and a setter of one name make one accessor element: the
    /// second finds the first, and is added to it when its own half is empty.
    ///
    /// A method's name is "#x" (SetFunctionName §10.2.9† with a Private
    /// Name: the description), a getter's "get #x", a setter's "set #x".
    pub(crate) fn define_private(
        &mut self,
        obj: Value,
        name: Value,
        val: Value,
        form: u32,
    ) -> Result<(), Abrupt> {
        let text = self.private_text(name);
        if !self.heap.is_object(obj) {
            return Err(self.type_error("Cannot define a private member on a non-object"));
        }
        let existing = self.private_find(obj, name);
        let twice = || format!("Cannot initialize {text} twice on the same object");
        let element = match (form, existing) {
            (0, None) => PrivateElement::Field(val),
            (1, None) => PrivateElement::Method(val),
            (2, None) => PrivateElement::Accessor {
                get: val,
                set: Value::UNDEFINED,
            },
            (3, None) => PrivateElement::Accessor {
                get: Value::UNDEFINED,
                set: val,
            },
            (2, Some(PrivateElement::Accessor { get, set })) if get == Value::UNDEFINED => {
                PrivateElement::Accessor { get: val, set }
            }
            (3, Some(PrivateElement::Accessor { get, set })) if set == Value::UNDEFINED => {
                PrivateElement::Accessor { get, set: val }
            }
            _ => return Err(self.type_error(&twice())),
        };
        if form != 0 && existing.is_none() || matches!(form, 2 | 3) {
            let prefix = match form {
                2 => "get ",
                3 => "set ",
                _ => "",
            };
            let desc = self.private_text(name);
            let n = self.heap.new_str(&format!("{prefix}{desc}"))?;
            let kn = self.atoms.k_name;
            self.heap.define(val, kn, n, Attrs(Attrs::CONFIGURABLE))?;
        }
        self.host.class.private.insert((obj, name), element);
        Ok(())
    }

    /// `#x in obj`, §13.10.1† step 5 onwards: 5. If rval is not an Object,
    /// throw a TypeError exception. 6. Let privateEnv be the running
    /// execution context's PrivateEnvironment. 7. Let privateName be
    /// ResolvePrivateIdentifier(privateEnv, privateIdentifier). 8. If
    /// PrivateElementFind(rval, privateName) is not empty, return true. 9.
    /// Return false.
    pub(crate) fn has_private(&mut self, name: Value, obj: Value) -> Result<bool, Abrupt> {
        if !self.heap.is_object(obj) {
            return Err(self.type_error(
                "Cannot use 'in' operator to search for a private field in a non-object",
            ));
        }
        Ok(self.private_find(obj, name).is_some())
    }
}
