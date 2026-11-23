//! Symbols and the iteration ops (phase-7.md item 7.9, "iteration"): the
//! Symbol values the VM keeps ([`crate::heap::Sym`]), the iterator protocol
//! (§7.4†) behind the `GetIterator`, `IterNext` and `IterClose` ops, the
//! `for`-`in` iterator (`ForInIterator`, §14.7.5.9† EnumerateObjectProperties),
//! and the spread calls (`CallSpread`, `NewSpread`), whose arguments the
//! compiler has already collected in an array.
//!
//! The iterator objects themselves (`%ArrayIteratorPrototype%`, ...) are
//! built-ins (`clazel-js-builtins`); the VM only runs the protocol, so an
//! array is iterated through whatever `Array.prototype[@@iterator]` is, as
//! the standard says, and a realm without the built-ins has no iterable
//! values.
//!
//! # Differences from the standard, all listed
//!
//! - **`for`-`in` takes its keys when the loop starts.** EnumerateObjectProperties
//!   (§14.7.5.9†) leaves the order and the effect of changes during the loop
//!   to the implementation within its rules; here the enumerable string keys
//!   of the object and of each prototype (each name once, a name shadowed by
//!   a nearer property left out, enumerable or not) are listed at the start,
//!   and a key is skipped if it is no longer a property of the object when
//!   reached. Keys added during the loop are not visited, which the rules
//!   allow.

use crate::heap::{Cell, Heap, IterRecord, ObjKind, Sym};
use crate::interp::{Abrupt, Vm};
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::symbol::SymbolId;
use clazel_js_heap::value::Value;
use std::collections::HashSet;

impl Vm {
    // -----------------------------------------------------------------
    // Symbols
    // -----------------------------------------------------------------

    /// The well-known Symbol `id` (`clazel_js_heap::symbol::ITERATOR`, ...),
    /// or `undefined` for an id that is not one.
    #[must_use]
    pub fn well_known_symbol(&self, id: SymbolId) -> Value {
        usize::try_from(id.0)
            .ok()
            .filter(|_| id.0 < clazel_js_heap::symbol::contract::WELL_KNOWN_COUNT)
            .and_then(|i| self.symbols.get(i))
            .copied()
            .unwrap_or(Value::UNDEFINED)
    }

    /// The property key of the well-known Symbol `id`.
    ///
    /// # Errors
    /// [`Abrupt::Internal`] if `id` is out of the encoding's range.
    pub fn well_known_key(&self, id: SymbolId) -> Result<Key, Abrupt> {
        Heap::symbol_key(id).ok_or(Abrupt::Internal("symbol id"))
    }

    /// A new Symbol whose `[[Description]]` is `description` (a string value
    /// or `undefined`): §20.4.1.1† `Symbol ( [ description ] )` step 4.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`] when the heap or the symbol table is full.
    pub fn new_symbol(&mut self, description: Value) -> Result<Value, Abrupt> {
        let id = u32::try_from(self.symbols.len()).map_err(|_| Abrupt::OutOfMemory)?;
        let id = SymbolId(id);
        if Heap::symbol_key(id).is_none() {
            return Err(Abrupt::OutOfMemory);
        }
        let v = self.heap.alloc(Cell::Symbol(Sym { id, description }))?;
        self.symbols.push(v);
        Ok(v)
    }

    /// The property key of a value that is a Symbol, `None` otherwise.
    #[must_use]
    pub fn symbol_property_key(&self, v: Value) -> Option<Key> {
        self.heap.symbol(v).and_then(|s| Heap::symbol_key(s.id))
    }

    /// The value a property key stands for: the String (a new string value)
    /// or the Symbol.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`], or [`Abrupt::Internal`] for a key that names
    /// nothing.
    pub fn key_value(&mut self, k: Key) -> Result<Value, Abrupt> {
        if let Some(id) = Heap::key_symbol(k) {
            return usize::try_from(id.0)
                .ok()
                .and_then(|i| self.symbols.get(i))
                .copied()
                .ok_or(Abrupt::Internal("symbol key names no symbol"));
        }
        let s = self
            .heap
            .key_string(k)
            .cloned()
            .ok_or(Abrupt::Internal("key names no string"))?;
        Ok(self.heap.new_string(s)?)
    }

    /// SymbolDescriptiveString ( sym ), §20.4.3.3.1†:
    /// 1. Let desc be sym's [[Description]] value.
    /// 2. If desc is undefined, set desc to the empty String.
    /// 3. Assert: desc is a String.
    /// 4. Return the string-concatenation of "Symbol(", desc, and ")".
    ///
    /// (The empty string for a value that is not a Symbol.)
    #[must_use]
    pub fn symbol_descriptive_string(&self, sym: Value) -> JsString {
        let desc = self
            .heap
            .symbol(sym)
            .and_then(|s| self.heap.string(s.description))
            .map(|d| d.units().collect::<Vec<u16>>())
            .unwrap_or_default();
        let mut units: Vec<u16> = "Symbol(".encode_utf16().collect();
        units.extend(desc);
        units.push(u16::from(b')'));
        JsString::from_units(&units).unwrap_or_else(|_| JsString::empty())
    }

    /// The name SetFunctionName (§10.2.9†) gives a function for a property
    /// key value: a String is itself; for a Symbol (step 2), the empty
    /// String if its description is undefined, else "[", the description
    /// and "]".
    pub(crate) fn function_name_for_key(&mut self, key: Value) -> Result<Value, Abrupt> {
        let Some(sym) = self.heap.symbol(key) else {
            return self.coerce_string_value(key);
        };
        let Some(desc) = self.heap.string(sym.description) else {
            return Ok(self.heap.new_str("")?);
        };
        let mut units = vec![u16::from(b'[')];
        units.extend(desc.units());
        units.push(u16::from(b']'));
        let s = JsString::from_units(&units).map_err(|_| Abrupt::OutOfMemory)?;
        Ok(self.heap.new_string(s)?)
    }

    // -----------------------------------------------------------------
    // instanceof
    // -----------------------------------------------------------------

    /// InstanceofOperator ( V, target ), §13.10.2†:
    /// 1. If target is not an Object, throw a TypeError exception.
    /// 2. Let instOfHandler be ? GetMethod(target, @@hasInstance).
    /// 3. If instOfHandler is not undefined, then
    ///    a. Return ToBoolean(? Call(instOfHandler, target, « V »)).
    /// 4. If IsCallable(target) is false, throw a TypeError exception.
    /// 5. Return ? OrdinaryHasInstance(target, V).
    ///
    /// # Errors
    /// The `TypeError`s above, or what the handler throws.
    pub fn instance_of(&mut self, v: Value, target: Value) -> Result<bool, Abrupt> {
        if !self.heap.is_object(target) {
            return Err(self.type_error("Right-hand side of 'instanceof' is not an object"));
        }
        let key = self.well_known_key(clazel_js_heap::symbol::HAS_INSTANCE)?;
        let handler = self.get_property(target, key, None)?;
        if handler != Value::UNDEFINED && handler != Value::NULL {
            if !self.heap.is_callable(handler) {
                return Err(self.type_error("Symbol.hasInstance is not a function"));
            }
            let r = self.call(handler, target, &[v])?;
            return Ok(self.to_boolean(r));
        }
        if !self.heap.is_callable(target) {
            return Err(self.type_error("Right-hand side of 'instanceof' is not callable"));
        }
        self.ordinary_has_instance(target, v)
    }

    /// OrdinaryHasInstance ( C, O ), §7.3.21†:
    /// 1. If IsCallable(C) is false, return false.
    /// 2. If C has a [[BoundTargetFunction]] internal slot, then
    ///    a. Let BC be C.[[BoundTargetFunction]].
    ///    b. Return ? InstanceofOperator(O, BC).
    /// 3. If O is not an Object, return false.
    /// 4. Let P be ? Get(C, "prototype").
    /// 5. If P is not an Object, throw a TypeError exception.
    /// 6. Repeat,
    ///    a. Set O to ? O.[[GetPrototypeOf]]().
    ///    b. If O is null, return false.
    ///    c. If SameValue(P, O) is true, return true.
    ///
    /// # Errors
    /// The `TypeError` of step 5, or what `Get` throws.
    pub fn ordinary_has_instance(&mut self, c: Value, o: Value) -> Result<bool, Abrupt> {
        if !self.heap.is_callable(c) {
            return Ok(false);
        }
        if let Some(ObjKind::Bound(i)) = self.heap.obj(c).map(|x| x.kind) {
            let target = self.bound_fn(i)?.target;
            return self.instance_of(o, target);
        }
        if !self.heap.is_object(o) {
            return Ok(false);
        }
        let kp = self.atoms.k_prototype;
        let p = self.get_property(c, kp, None)?;
        if !self.heap.is_object(p) {
            return Err(self.type_error("Function has non-object prototype in instanceof check"));
        }
        let mut cur = o;
        for _ in 0..crate::heap::MAX_PROTO_DEPTH {
            cur = self.heap.proto_of(cur).unwrap_or(Value::NULL);
            if cur == Value::NULL {
                return Ok(false);
            }
            if cur == p {
                return Ok(true);
            }
        }
        Err(Abrupt::Internal("prototype chain too long"))
    }

    // -----------------------------------------------------------------
    // The iterator protocol (§7.4†)
    // -----------------------------------------------------------------

    /// GetIterator ( obj, sync ), §7.4.4†, with GetIteratorFromMethod,
    /// §7.4.3†:
    /// 1 and 2. Let method be ? GetMethod(obj, @@iterator).
    /// 3. If method is undefined, throw a TypeError exception.
    /// 4. Return ? GetIteratorFromMethod(obj, method):
    ///    1. Let iterator be ? Call(method, obj).
    ///    2. If iterator is not an Object, throw a TypeError exception.
    ///    3. Let nextMethod be ? Get(iterator, "next").
    ///    4. Let iteratorRecord be the Iterator Record { [[Iterator]]:
    ///       iterator, [[NextMethod]]: nextMethod, [[Done]]: false }.
    ///    5. Return iteratorRecord.
    ///
    /// The record is a heap cell only registers hold ([`IterRecord`]).
    ///
    /// # Errors
    /// The `TypeError`s above, or what the method throws.
    pub fn get_iterator(&mut self, obj: Value) -> Result<Value, Abrupt> {
        let key = self.well_known_key(clazel_js_heap::symbol::ITERATOR)?;
        if obj == Value::UNDEFINED || obj == Value::NULL {
            let what = if obj == Value::NULL {
                "null"
            } else {
                "undefined"
            };
            return Err(self.type_error(&format!("{what} is not iterable")));
        }
        let method = self.get_property(obj, key, None)?;
        // GetMethod, §7.3.10†: undefined and null are "no method"; a value
        // that is not callable is a TypeError.
        if method == Value::UNDEFINED || method == Value::NULL {
            return Err(self.type_error("object is not iterable"));
        }
        if !self.heap.is_callable(method) {
            return Err(self.type_error("Symbol.iterator is not a function"));
        }
        self.get_iterator_from_method(obj, method)
    }

    /// GetIteratorFromMethod ( obj, method ), §7.4.3† (see
    /// [`Vm::get_iterator`]).
    ///
    /// # Errors
    /// The `TypeError` of step 2, or what the method or the `next` getter
    /// throws.
    pub fn get_iterator_from_method(&mut self, obj: Value, method: Value) -> Result<Value, Abrupt> {
        let iterator = self.call(method, obj, &[])?;
        if !self.heap.is_object(iterator) {
            return Err(self.type_error("Result of the Symbol.iterator method is not an object"));
        }
        let kn = self.atoms.k_next;
        let next = self.get_property(iterator, kn, None)?;
        Ok(self.heap.alloc(Cell::Iter(IterRecord::Protocol {
            iterator,
            next,
            done: false,
        }))?)
    }

    /// IteratorStepValue ( iteratorRecord ), §7.4.8†, on a record of
    /// [`Vm::get_iterator`] (or of `ForInIterator`): `None` when the
    /// iterator is done.
    /// 1. Let result be Completion(IteratorStep(iteratorRecord)).
    /// 2. If result is a throw completion, then
    ///    a. Set iteratorRecord.[[Done]] to true.
    ///    b. Return ? result.
    /// 3. Set result to ! result.
    /// 4. If result is done, then
    ///    a. Return done.
    /// 5. Let value be Completion(IteratorValue(result)).
    /// 6. If value is a throw completion, then
    ///    a. Set iteratorRecord.[[Done]] to true.
    /// 7. Return ? value.
    ///
    /// IteratorStep ( iteratorRecord ), §7.4.7†, with IteratorNext, §7.4.5†
    /// and IteratorComplete, §7.4.6†:
    /// 1. Let result be ? IteratorNext(iteratorRecord): Call([[NextMethod]],
    ///    [[Iterator]]), and a TypeError if the result is not an Object.
    /// 2. Let done be Completion(IteratorComplete(result)): ToBoolean(?
    ///    Get(result, "done")).
    /// 3. If done is a throw completion, then
    ///    a. Set iteratorRecord.[[Done]] to true.
    /// 4. Set done to ? done.
    /// 5. If done is true, then
    ///    a. Set iteratorRecord.[[Done]] to true.
    ///    b. Return done.
    /// 6. Return result.
    ///
    /// A record whose `[[Done]]` is already true gives `None` without a
    /// call (the destructuring ops keep their own flag and do not ask again,
    /// but a native that does gets done).
    ///
    /// # Errors
    /// What `next` throws, or a `TypeError` for a result that is not an
    /// object.
    pub fn iterator_step_value(&mut self, record: Value) -> Result<Option<Value>, Abrupt> {
        let (iterator, next) = match self.heap.iter_record(record) {
            Some(IterRecord::Protocol { done: true, .. }) => return Ok(None),
            Some(IterRecord::Protocol { iterator, next, .. }) => (*iterator, *next),
            Some(IterRecord::ForIn { .. }) => return self.for_in_step(record),
            None => return Err(Abrupt::Internal("IterNext without an iterator record")),
        };
        match self.iterator_step_inner(iterator, next) {
            Ok(Some(v)) => Ok(Some(v)),
            Ok(None) => {
                self.set_record_done(record);
                Ok(None)
            }
            Err(e) => {
                self.set_record_done(record);
                Err(e)
            }
        }
    }

    fn iterator_step_inner(
        &mut self,
        iterator: Value,
        next: Value,
    ) -> Result<Option<Value>, Abrupt> {
        // IteratorNext, §7.4.5† steps 1 to 3.
        if !self.heap.is_callable(next) {
            return Err(self.type_error("iterator.next is not a function"));
        }
        let result = self.call(next, iterator, &[])?;
        if !self.heap.is_object(result) {
            return Err(self.type_error("Iterator result is not an object"));
        }
        // IteratorComplete, §7.4.6†.
        let kd = self.atoms.k_done;
        let done = self.get_property(result, kd, None)?;
        if self.to_boolean(done) {
            return Ok(None);
        }
        // IteratorValue, §7.4.7†: ? Get(iterResult, "value").
        let kv = self.atoms.k_value;
        Ok(Some(self.get_property(result, kv, None)?))
    }

    fn set_record_done(&mut self, record: Value) {
        if let Some(IterRecord::Protocol { done, .. }) = self.heap.iter_record_mut(record) {
            *done = true;
        }
    }

    /// Whether an iterator record's `[[Done]]` is true.
    #[must_use]
    pub fn iterator_done(&self, record: Value) -> bool {
        matches!(
            self.heap.iter_record(record),
            Some(IterRecord::Protocol { done: true, .. })
        )
    }

    /// IteratorClose ( iteratorRecord, completion ), §7.4.11†, for a normal
    /// completion:
    /// 1 and 2. Let iterator be iteratorRecord.[[Iterator]].
    /// 3. Let innerResult be Completion(GetMethod(iterator, "return")).
    /// 4. If innerResult is a normal completion, then
    ///    a. Let return be innerResult.[[Value]].
    ///    b. If return is undefined, return ? completion.
    ///    c. Set innerResult to Completion(Call(return, iterator)).
    /// 5. If completion is a throw completion, return ? completion.
    /// 6. If innerResult is a throw completion, return ? innerResult.
    /// 7. If innerResult.[[Value]] is not an Object, throw a TypeError
    ///    exception.
    /// 8. Return ? completion.
    ///
    /// For a throw completion (step 5) the caller ignores this result and
    /// throws its own: the compiler's exception-table entries do that around
    /// the op, and [`Vm::iterator_close_on_throw`] for natives. A `for`-`in`
    /// iterator has nothing to close.
    ///
    /// # Errors
    /// What `return` throws, or the `TypeError` of step 7.
    pub fn iterator_close(&mut self, record: Value) -> Result<(), Abrupt> {
        let iterator = match self.heap.iter_record(record) {
            Some(IterRecord::Protocol { iterator, .. }) => *iterator,
            Some(IterRecord::ForIn { .. }) => return Ok(()),
            None => return Err(Abrupt::Internal("IterClose without an iterator record")),
        };
        let kr = self.atoms.k_return;
        let ret = self.get_property(iterator, kr, None)?;
        if ret == Value::UNDEFINED || ret == Value::NULL {
            return Ok(());
        }
        if !self.heap.is_callable(ret) {
            return Err(self.type_error("iterator.return is not a function"));
        }
        let inner = self.call(ret, iterator, &[])?;
        if !self.heap.is_object(inner) {
            return Err(self.type_error("Iterator result is not an object"));
        }
        Ok(())
    }

    /// IteratorClose with a throw completion (§7.4.11† step 5): closes the
    /// iterator, then gives back `completion` whatever the close did (an
    /// abrupt completion that is not a JS throw, such as termination, still
    /// wins over it).
    pub fn iterator_close_on_throw(&mut self, record: Value, completion: Abrupt) -> Abrupt {
        match self.iterator_close(record) {
            Ok(()) | Err(Abrupt::Throw(_)) => completion,
            Err(other) => other,
        }
    }

    /// IteratorToList ( iteratorRecord ), §7.4.13†:
    /// 1. Let values be a new empty List.
    /// 2. Repeat,
    ///    a. Let next be ? IteratorStepValue(iteratorRecord).
    ///    b. If next is done, return values.
    ///    c. Append next to values.
    ///
    /// # Errors
    /// What the iterator throws.
    pub fn iterator_to_list(&mut self, record: Value) -> Result<Vec<Value>, Abrupt> {
        let mut values = Vec::new();
        while let Some(v) = self.iterator_step_value(record)? {
            self.charge()?;
            values.push(v);
        }
        Ok(values)
    }

    // -----------------------------------------------------------------
    // for-in
    // -----------------------------------------------------------------

    /// The `for`-`in` iterator of `ForInIterator` (§14.7.5.6†
    /// ForIn/OfHeadEvaluation step 6): done at once for `undefined` and
    /// `null` (step 6.a), else EnumerateObjectProperties(! ToObject(exprValue))
    /// (§14.7.5.9†; see the module header for how its freedom is used).
    pub(crate) fn for_in_iterator(&mut self, v: Value) -> Result<Value, Abrupt> {
        let (object, keys) = if v == Value::UNDEFINED || v == Value::NULL {
            (Value::UNDEFINED, Vec::new())
        } else {
            let o = self.to_object(v)?;
            (o, self.enumerable_keys(o)?)
        };
        Ok(self.heap.alloc(Cell::Iter(IterRecord::ForIn {
            object,
            keys,
            pos: 0,
        }))?)
    }

    /// The enumerable string keys of `o` and its prototype chain, each once:
    /// EnumerateObjectProperties's rules (§14.7.5.9†): "A property of a
    /// prototype is not processed if it has the same name as a property that
    /// has already been processed", and a non-enumerable property shadows
    /// too. A String wrapper's indices come first, as its
    /// `[[OwnPropertyKeys]]` (§10.4.3.3†) lists them.
    fn enumerable_keys(&mut self, o: Value) -> Result<Vec<Key>, Abrupt> {
        let mut seen: HashSet<Key> = HashSet::new();
        let mut out = Vec::new();
        let mut cur = o;
        for _ in 0..crate::heap::MAX_PROTO_DEPTH {
            if !self.heap.is_object(cur) {
                break;
            }
            if let Some(ObjKind::Primitive(p)) = self.heap.obj(cur).map(|x| x.kind)
                && let Some(len) = self.heap.string(p).map(JsString::len)
            {
                for i in 0..len {
                    let k = self.heap.intern_str(&i.to_string())?;
                    if seen.insert(k) {
                        out.push(k);
                    }
                }
            }
            for (k, attrs, _) in self.heap.own_properties(cur) {
                if seen.insert(k) && attrs.0 & clazel_js_heap::shape::Attrs::ENUMERABLE != 0 {
                    out.push(k);
                }
            }
            cur = self.heap.proto_of(cur).unwrap_or(Value::NULL);
        }
        Ok(out)
    }

    /// The next key of a `for`-`in` iterator that is still a property of the
    /// object (a deleted one is skipped, as §14.7.5.9† requires), as a
    /// string value.
    fn for_in_step(&mut self, record: Value) -> Result<Option<Value>, Abrupt> {
        loop {
            let (object, key) = match self.heap.iter_record_mut(record) {
                Some(IterRecord::ForIn { object, keys, pos }) => {
                    let Some(k) = keys.get(*pos).copied() else {
                        return Ok(None);
                    };
                    *pos = pos.saturating_add(1);
                    (*object, k)
                }
                _ => return Err(Abrupt::Internal("for-in step on another record")),
            };
            let present = self.heap.find(object, key)?.is_some()
                || self.heap.key_index(key).is_some_and(|i| {
                    self.heap
                        .obj(object)
                        .and_then(|o| match o.kind {
                            ObjKind::Primitive(p) => self.heap.string(p),
                            _ => None,
                        })
                        .is_some_and(|s| usize::try_from(i).is_ok_and(|i| i < s.len()))
                });
            if present {
                return Ok(Some(self.key_value(key)?));
            }
        }
    }

    // -----------------------------------------------------------------
    // Spread calls
    // -----------------------------------------------------------------

    /// The elements of the argument array the compiler built for a spread
    /// call (`CallSpread`, `NewSpread`): an array of this VM's own making,
    /// read from index 0 to its `length`.
    pub(crate) fn spread_arguments(&mut self, arr: Value) -> Result<Vec<Value>, Abrupt> {
        let (len, _) = self
            .heap
            .array_length(arr)
            .ok_or(Abrupt::Internal("spread arguments are not an array"))?;
        let mut out = Vec::with_capacity(usize::try_from(len).unwrap_or(0));
        for i in 0..len {
            let k = self.heap.intern_str(&i.to_string())?;
            let v = match self.heap.find(arr, k)? {
                Some(f) => self.heap.slot(f.holder, f.slot).unwrap_or(Value::UNDEFINED),
                None => Value::UNDEFINED,
            };
            out.push(v);
        }
        Ok(out)
    }
}
