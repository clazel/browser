//! Property descriptors, `[[DefineOwnProperty]]`, `[[Delete]]` and Array
//! exotic objects (item 7.9, second group: arrays).
//!
//! The VM's objects hold data properties by shape (`crate::heap`); this module
//! is the standard's property-level operations over them:
//!
//! - [`PropDesc`], a Property Descriptor Specification Type (§6.2.6†) for data
//!   properties (each field present or absent);
//! - [`Vm::define_own_property`]: `OrdinaryDefineOwnProperty` (§10.1.6.1†) with
//!   `ValidateAndApplyPropertyDescriptor` (§10.1.6.3†), and the Array exotic
//!   object's `[[DefineOwnProperty]]` (§10.4.2.1†) with `ArraySetLength`
//!   (§10.4.2.4†);
//! - [`Vm::array_create`] (§10.4.2.2†) and [`Vm::create_array_from_list`]
//!   (§7.3.18†);
//! - `CreateDataProperty` (§7.3.5†), `DefinePropertyOrThrow` (§7.3.8†),
//!   `[[Delete]]` (§10.1.10.1†) and `DeletePropertyOrThrow` (§7.3.10†).
//!
//! Objects are always extensible in this slice (no `Object.preventExtensions`
//! yet). Accessor properties are kept as `crate::heap` describes (an
//! [`ACCESSOR`] bit and a pair cell in the slot).

use crate::heap::{ACCESSOR, length_value};
use crate::interp::{Abrupt, Intrinsic, Vm};
use crate::numeric::to_uint32;
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::Key;
use clazel_js_heap::value::Value;

/// A Property Descriptor (§6.2.6†): each field is present (`Some`) or absent
/// (`None`).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct PropDesc {
    /// `[[Value]]`.
    pub value: Option<Value>,
    /// `[[Writable]]`.
    pub writable: Option<bool>,
    /// `[[Get]]`: a function object or `undefined`.
    pub get: Option<Value>,
    /// `[[Set]]`: a function object or `undefined`.
    pub set: Option<Value>,
    /// `[[Enumerable]]`.
    pub enumerable: Option<bool>,
    /// `[[Configurable]]`.
    pub configurable: Option<bool>,
}

impl PropDesc {
    /// A complete descriptor: `value` with the attributes `attrs`.
    #[must_use]
    pub fn data(value: Value, attrs: Attrs) -> Self {
        Self {
            value: Some(value),
            writable: Some(attrs.0 & Attrs::WRITABLE != 0),
            get: None,
            set: None,
            enumerable: Some(attrs.0 & Attrs::ENUMERABLE != 0),
            configurable: Some(attrs.0 & Attrs::CONFIGURABLE != 0),
        }
    }

    /// A complete accessor descriptor: `get` and `set` (each a function or
    /// `undefined`) with the enumerable and configurable bits of `attrs`.
    #[must_use]
    pub fn accessor(get: Value, set: Value, attrs: Attrs) -> Self {
        Self {
            value: None,
            writable: None,
            get: Some(get),
            set: Some(set),
            enumerable: Some(attrs.0 & Attrs::ENUMERABLE != 0),
            configurable: Some(attrs.0 & Attrs::CONFIGURABLE != 0),
        }
    }

    /// IsAccessorDescriptor ( Desc ), §6.2.6.1†: it has `[[Get]]` or `[[Set]]`.
    #[must_use]
    pub fn is_accessor(&self) -> bool {
        self.get.is_some() || self.set.is_some()
    }

    /// IsDataDescriptor ( Desc ), §6.2.6.2†: it has `[[Value]]` or
    /// `[[Writable]]`.
    #[must_use]
    pub fn is_data(&self) -> bool {
        self.value.is_some() || self.writable.is_some()
    }

    /// `{ [[Value]]: value, [[Writable]]: true, [[Enumerable]]: true,
    /// [[Configurable]]: true }`, the descriptor of `CreateDataProperty`
    /// (§7.3.5† step 1).
    #[must_use]
    pub fn all(value: Value) -> Self {
        Self::data(value, Attrs::ALL)
    }
}

impl Vm {
    /// SameValue, §7.2.10†: Numbers by value with NaN equal to itself and `+0`
    /// distinct from `-0`, Strings by code units, everything else by identity.
    #[must_use]
    pub fn same_value(&self, a: Value, b: Value) -> bool {
        if let (Some(x), Some(y)) = (crate::numeric::num(a), crate::numeric::num(b)) {
            let (x, y) = (x.to_f64(), y.to_f64());
            return if x.is_nan() || y.is_nan() {
                x.is_nan() && y.is_nan()
            } else {
                x.to_bits() == y.to_bits()
            };
        }
        if let (Some(x), Some(y)) = (self.heap.string(a), self.heap.string(b)) {
            return x == y;
        }
        a == b
    }

    /// The own data property `key` of `obj` (`OrdinaryGetOwnProperty`,
    /// §10.1.5.1†): its attributes and value.
    ///
    /// # Errors
    /// [`Abrupt::Internal`] if the heap is corrupt.
    pub fn get_own_property(&self, obj: Value, key: Key) -> Result<Option<(Attrs, Value)>, Abrupt> {
        let Some(f) = self.heap.find(obj, key)?.filter(|f| f.own) else {
            return Ok(None);
        };
        let v = self
            .heap
            .slot(f.holder, f.slot)
            .ok_or(Abrupt::Internal("property slot"))?;
        Ok(Some((f.attrs, v)))
    }

    /// `ValidateAndApplyPropertyDescriptor` (§10.1.6.3†) for an extensible
    /// object and data properties, as `OrdinaryDefineOwnProperty` (§10.1.6.1†)
    /// calls it:
    /// 1. (Assert: key is a property key.)
    /// 2. If current is undefined, then a. (extensible is true) b. create the
    ///    data property: each absent field is its default (`undefined`,
    ///    `false`). c. Return true.
    /// 3. (Assert: current is a fully populated Property Descriptor.)
    /// 4. If every field of Desc is absent, return true.
    /// 5. If current.[[Configurable]] is false, then a. If Desc has
    ///    [[Configurable]] and it is true, return false. b. If Desc has
    ///    [[Enumerable]] and it differs from current's, return false. (c, d:
    ///    the generic and accessor cases, not reachable with data properties.)
    ///    e. If current.[[Writable]] is false, then i. If Desc has [[Writable]]
    ///    and it is true, return false. ii. If Desc has [[Value]] and
    ///    SameValue(Desc.[[Value]], current.[[Value]]) is false, return false.
    /// 6. (Accessor/data conversion: not reachable.) The fields of Desc
    ///    replace those of the property.
    /// 7. Return true.
    fn ordinary_define_own_property(
        &mut self,
        obj: Value,
        key: Key,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        let current = self.get_own_property(obj, key)?;
        if desc.is_accessor() || current.is_some_and(|(a, _)| a.0 & ACCESSOR != 0) {
            return self.validate_and_apply_accessor(obj, key, desc);
        }
        let Some((cur_attrs, cur_value)) = current else {
            let mut bits = 0;
            for (flag, bit) in [
                (desc.writable, Attrs::WRITABLE),
                (desc.enumerable, Attrs::ENUMERABLE),
                (desc.configurable, Attrs::CONFIGURABLE),
            ] {
                if flag == Some(true) {
                    bits |= bit;
                }
            }
            let v = desc.value.unwrap_or(Value::UNDEFINED);
            self.heap.define(obj, key, v, Attrs(bits))?;
            return Ok(true);
        };
        let flag = |bit: u8| cur_attrs.0 & bit != 0;
        if !flag(Attrs::CONFIGURABLE) {
            let bad = desc.configurable == Some(true)
                || desc
                    .enumerable
                    .is_some_and(|e| e != flag(Attrs::ENUMERABLE))
                || (!flag(Attrs::WRITABLE)
                    && (desc.writable == Some(true)
                        || desc.value.is_some_and(|v| !self.same_value(v, cur_value))));
            if bad {
                return Ok(false);
            }
        }
        let mut bits = 0;
        for (new, bit) in [
            (desc.writable, Attrs::WRITABLE),
            (desc.enumerable, Attrs::ENUMERABLE),
            (desc.configurable, Attrs::CONFIGURABLE),
        ] {
            if new.unwrap_or_else(|| flag(bit)) {
                bits |= bit;
            }
        }
        let v = desc.value.unwrap_or(cur_value);
        self.heap.redefine(obj, key, v, Attrs(bits))?;
        Ok(true)
    }

    /// `OrdinaryGetOwnProperty` (§10.1.5.1†) as a complete descriptor: a data
    /// descriptor, or for an accessor property its `[[Get]]` and `[[Set]]`.
    ///
    /// # Errors
    /// [`Abrupt::Internal`] if the heap is corrupt.
    pub fn own_property_descriptor(
        &self,
        obj: Value,
        key: Key,
    ) -> Result<Option<PropDesc>, Abrupt> {
        let Some((attrs, v)) = self.get_own_property(obj, key)? else {
            return Ok(None);
        };
        if attrs.0 & ACCESSOR == 0 {
            return Ok(Some(PropDesc::data(v, attrs)));
        }
        let (get, set) = self
            .heap
            .accessor(v)
            .ok_or(Abrupt::Internal("accessor pair"))?;
        Ok(Some(PropDesc::accessor(get, set, attrs)))
    }

    /// `ValidateAndApplyPropertyDescriptor` (§10.1.6.3†) when Desc or the
    /// current property is an accessor (O is never undefined here, and the
    /// object is extensible):
    /// 2. If current is undefined, then c. If IsAccessorDescriptor(Desc) is
    ///    true, create an own accessor property whose [[Get]], [[Set]],
    ///    [[Enumerable]] and [[Configurable]] are Desc's or their defaults
    ///    (`undefined`, `false`). e. Return true.
    /// 4. If every field in Desc is absent, return true.
    /// 5. If current.[[Configurable]] is false, then a. If Desc has
    ///    [[Configurable]] and it is true, return false. b. If Desc has
    ///    [[Enumerable]] and it differs from current's, return false. c. If
    ///    IsGenericDescriptor(Desc) is false and IsAccessorDescriptor(Desc)
    ///    differs from IsAccessorDescriptor(current), return false. d. If
    ///    IsAccessorDescriptor(current) is true, then i. If Desc has [[Get]]
    ///    and SameValue(Desc.[[Get]], current.[[Get]]) is false, return
    ///    false. ii. The same for [[Set]]. e. Else if current.[[Writable]] is
    ///    false, then i. If Desc has [[Writable]] and it is true, return false.
    ///    ii. If Desc has [[Value]] and SameValue(Desc.[[Value]],
    ///    current.[[Value]]) is false, return false.
    /// 6. a. If IsDataDescriptor(current) and IsAccessorDescriptor(Desc), let
    ///    configurable and enumerable be Desc's if present, else current's,
    ///    and replace the property by an accessor property with them and
    ///    Desc's [[Get]] and [[Set]] or their defaults. b. If
    ///    IsAccessorDescriptor(current) and IsDataDescriptor(Desc), replace it
    ///    by a data property in the same way, with Desc's [[Value]] and
    ///    [[Writable]] or their defaults. c. Else, set each field of Desc.
    /// 7. Return true.
    fn validate_and_apply_accessor(
        &mut self,
        obj: Value,
        key: Key,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        let bits = |enumerable: bool, configurable: bool, writable: bool| {
            let mut b = 0;
            if enumerable {
                b |= Attrs::ENUMERABLE;
            }
            if configurable {
                b |= Attrs::CONFIGURABLE;
            }
            if writable {
                b |= Attrs::WRITABLE;
            }
            b
        };
        let Some(current) = self.own_property_descriptor(obj, key)? else {
            // Step 2.c (Desc is an accessor descriptor here).
            let pair = self.heap.new_accessor(
                desc.get.unwrap_or(Value::UNDEFINED),
                desc.set.unwrap_or(Value::UNDEFINED),
            )?;
            let b = bits(
                desc.enumerable == Some(true),
                desc.configurable == Some(true),
                false,
            );
            self.heap.define(obj, key, pair, Attrs(b | ACCESSOR))?;
            return Ok(true);
        };
        if *desc == PropDesc::default() {
            return Ok(true);
        }
        let cur_enumerable = current.enumerable == Some(true);
        let cur_configurable = current.configurable == Some(true);
        if !cur_configurable {
            if desc.configurable == Some(true)
                || desc.enumerable.is_some_and(|e| e != cur_enumerable)
            {
                return Ok(false);
            }
            let generic = !desc.is_accessor() && !desc.is_data();
            if !generic && desc.is_accessor() != current.is_accessor() {
                return Ok(false);
            }
            if current.is_accessor() {
                let differs = |new: Option<Value>, old: Option<Value>| {
                    new.is_some_and(|n| !self.same_value(n, old.unwrap_or(Value::UNDEFINED)))
                };
                if differs(desc.get, current.get) || differs(desc.set, current.set) {
                    return Ok(false);
                }
            } else if current.writable != Some(true)
                && (desc.writable == Some(true)
                    || desc.value.is_some_and(|v| {
                        !self.same_value(v, current.value.unwrap_or(Value::UNDEFINED))
                    }))
            {
                return Ok(false);
            }
        }
        let enumerable = desc.enumerable.unwrap_or(cur_enumerable);
        let configurable = desc.configurable.unwrap_or(cur_configurable);
        let to_accessor = if current.is_accessor() {
            !desc.is_data()
        } else {
            desc.is_accessor()
        };
        if to_accessor {
            // Steps 6.a and 6.c: Desc's halves, else current's (`undefined`
            // when current was a data property).
            let get = desc.get.or(current.get).unwrap_or(Value::UNDEFINED);
            let set = desc.set.or(current.set).unwrap_or(Value::UNDEFINED);
            let pair = self.heap.new_accessor(get, set)?;
            let b = bits(enumerable, configurable, false);
            self.heap.redefine(obj, key, pair, Attrs(b | ACCESSOR))?;
        } else {
            // Step 6.b: an accessor becomes a data property.
            let value = desc.value.unwrap_or(Value::UNDEFINED);
            let b = bits(enumerable, configurable, desc.writable == Some(true));
            self.heap.redefine(obj, key, value, Attrs(b))?;
        }
        Ok(true)
    }

    /// `[[DefineOwnProperty]]` (P, Desc) of an object: for an Array exotic
    /// object §10.4.2.1†, else `OrdinaryDefineOwnProperty` (§10.1.6.1†).
    /// 1. If P is "length", return ? ArraySetLength(A, Desc).
    /// 2. Else if P is an array index, then
    ///    a. Let lengthDesc be OrdinaryGetOwnProperty(A, "length").
    ///    b. (Assert: it is a data descriptor.) c. Let length be
    ///    lengthDesc.[[Value]]. d. Let index be ! ToUint32(P).
    ///    e. If index >= length and lengthDesc.[[Writable]] is false, return
    ///    false.
    ///    f. Let succeeded be ! OrdinaryDefineOwnProperty(A, P, Desc).
    ///    g. If succeeded is false, return false.
    ///    h. If index >= length, then i. Set lengthDesc.[[Value]] to
    ///    index + 1. ii. Set succeeded to ! OrdinaryDefineOwnProperty(A,
    ///    "length", lengthDesc). iii. (Assert: succeeded is true.)
    ///    j. Return true.
    /// 3. Return ? OrdinaryDefineOwnProperty(A, P, Desc).
    ///
    /// # Errors
    /// A `RangeError` (ArraySetLength step 5), the exceptions of ToNumber, or
    /// [`Abrupt::OutOfMemory`].
    pub fn define_own_property(
        &mut self,
        obj: Value,
        key: Key,
        desc: &PropDesc,
    ) -> Result<bool, Abrupt> {
        if !self.heap.is_array_object(obj) {
            return self.ordinary_define_own_property(obj, key, desc);
        }
        if key == self.atoms.k_length {
            return self.array_set_length(obj, desc);
        }
        let Some(index) = self.heap.key_index(key) else {
            return self.ordinary_define_own_property(obj, key, desc);
        };
        let (length, writable) = self
            .heap
            .array_length(obj)
            .ok_or(Abrupt::Internal("array length"))?;
        if index >= length && !writable {
            return Ok(false);
        }
        if !self.ordinary_define_own_property(obj, key, desc)? {
            return Ok(false);
        }
        if index >= length {
            let new_len = index
                .checked_add(1)
                .ok_or(Abrupt::Internal("array index"))?;
            self.heap.set_array_length(obj, new_len)?;
        }
        Ok(true)
    }

    /// ArraySetLength ( A, Desc ), §10.4.2.4†:
    /// 1. If Desc does not have a [[Value]] field, then a. Return !
    ///    OrdinaryDefineOwnProperty(A, "length", Desc).
    /// 2. Let newLenDesc be a copy of Desc.
    /// 3. Let newLen be ? ToUint32(Desc.[[Value]]).
    /// 4. Let numberLen be ? ToNumber(Desc.[[Value]]).
    /// 5. If SameValueZero(newLen, numberLen) is false, throw a RangeError.
    /// 6. Set newLenDesc.[[Value]] to newLen.
    /// 7. Let oldLenDesc be OrdinaryGetOwnProperty(A, "length").
    /// 9. Let oldLen be oldLenDesc.[[Value]].
    /// 10. If newLen >= oldLen, then a. Return ! OrdinaryDefineOwnProperty(A,
    ///     "length", newLenDesc).
    /// 11. If oldLenDesc.[[Writable]] is false, return false.
    /// 12. If newLenDesc does not have a [[Writable]] field or
    ///     newLenDesc.[[Writable]] is true, let newWritable be true.
    /// 13. Else, a. (Need to defer setting the [[Writable]] attribute to false
    ///     in case any elements cannot be deleted.) b. Let newWritable be
    ///     false. c. Set newLenDesc.[[Writable]] to true.
    /// 14. Let succeeded be ! OrdinaryDefineOwnProperty(A, "length",
    ///     newLenDesc).
    /// 15. If succeeded is false, return false.
    /// 16. For each own property key P of A such that P is an array index and
    ///     ! ToUint32(P) >= newLen, in descending numeric index order, do
    ///     a. Let deleteSucceeded be ! A.[[Delete]](P).
    ///     b. If deleteSucceeded is false, then i. Set newLenDesc.[[Value]] to
    ///     ! ToUint32(P) + 1. ii. If newWritable is false, set
    ///     newLenDesc.[[Writable]] to false. iii. Perform !
    ///     OrdinaryDefineOwnProperty(A, "length", newLenDesc). iv. Return
    ///     false.
    /// 17. If newWritable is false, then a. Set succeeded to !
    ///     OrdinaryDefineOwnProperty(A, "length", { [[Writable]]: false }).
    /// 18. Return true.
    fn array_set_length(&mut self, a: Value, desc: &PropDesc) -> Result<bool, Abrupt> {
        let k_length = self.atoms.k_length;
        let Some(v) = desc.value else {
            return self.ordinary_define_own_property(a, k_length, desc);
        };
        let mut new_len_desc = *desc;
        let new_len = to_uint32(self.coerce_number(v)?);
        let number_len = self.to_number(v)?;
        if f64::from(new_len) != number_len {
            return Err(self.range_error("Invalid array length"));
        }
        new_len_desc.value = Some(length_value(new_len));
        let (old_len, old_writable) = self
            .heap
            .array_length(a)
            .ok_or(Abrupt::Internal("array length"))?;
        if new_len >= old_len {
            return self.ordinary_define_own_property(a, k_length, &new_len_desc);
        }
        if !old_writable {
            return Ok(false);
        }
        let new_writable = new_len_desc.writable != Some(false);
        if !new_writable {
            new_len_desc.writable = Some(true);
        }
        if !self.ordinary_define_own_property(a, k_length, &new_len_desc)? {
            return Ok(false);
        }
        // Step 16: the indices at or above newLen, in descending order.
        let mut doomed: Vec<(u32, Key)> = self
            .heap
            .own_properties(a)
            .into_iter()
            .filter_map(|(k, _, _)| self.heap.key_index(k).map(|i| (i, k)))
            .filter(|(i, _)| *i >= new_len)
            .collect();
        doomed.sort_by_key(|x| std::cmp::Reverse(x.0));
        for (i, k) in &doomed {
            let configurable = self
                .get_own_property(a, *k)?
                .is_some_and(|(at, _)| at.0 & Attrs::CONFIGURABLE != 0);
            if !configurable {
                // The properties above this one are already gone.
                let keep = i.checked_add(1).ok_or(Abrupt::Internal("array index"))?;
                new_len_desc.value = Some(length_value(keep));
                if !new_writable {
                    new_len_desc.writable = Some(false);
                }
                self.ordinary_define_own_property(a, k_length, &new_len_desc)?;
                self.remove_doomed(a, &doomed, Some(*i))?;
                return Ok(false);
            }
        }
        self.remove_doomed(a, &doomed, None)?;
        if !new_writable {
            let w = PropDesc {
                writable: Some(false),
                ..PropDesc::default()
            };
            self.ordinary_define_own_property(a, k_length, &w)?;
        }
        Ok(true)
    }

    /// Removes the doomed indices above `stop` (all of them when `stop` is
    /// `None`): the deletions of step 16.a that happened before the one that
    /// failed.
    fn remove_doomed(
        &mut self,
        a: Value,
        doomed: &[(u32, Key)],
        stop: Option<u32>,
    ) -> Result<(), Abrupt> {
        let keys: Vec<Key> = doomed
            .iter()
            .filter(|(i, _)| stop.is_none_or(|s| *i > s))
            .map(|(_, k)| *k)
            .collect();
        Ok(self.heap.remove_properties(a, &keys)?)
    }

    /// ArrayCreate ( length [ , proto ] ), §10.4.2.2†:
    /// 1. If length > 2^32 - 1, throw a RangeError exception.
    /// 2. If proto is not present, set proto to %Array.prototype%.
    /// 3. Let A be MakeBasicObject(<<[[Prototype]], [[Extensible]]>>).
    /// 4. Set A.[[Prototype]] to proto.
    /// 5. Set A.[[DefineOwnProperty]] to the definition in §10.4.2.1†.
    /// 6. Perform ! OrdinaryDefineOwnProperty(A, "length", { [[Value]]: length,
    ///    [[Writable]]: true, [[Enumerable]]: false, [[Configurable]]: false
    ///    }).
    /// 7. Return A.
    ///
    /// # Errors
    /// A `RangeError`, [`Abrupt::OutOfMemory`].
    pub fn array_create(&mut self, length: f64, proto: Option<Value>) -> Result<Value, Abrupt> {
        if length > 4_294_967_295.0 || length < 0.0 || length.is_nan() {
            return Err(self.range_error("Invalid array length"));
        }
        let proto = match proto {
            Some(p) => p,
            None => self.array_prototype(),
        };
        Ok(self.heap.new_array(proto, length as u32)?)
    }

    /// `%Array.prototype%`, or `%Object.prototype%` while the realm has no
    /// `Array` built-in.
    #[must_use]
    pub fn array_prototype(&self) -> Value {
        let p = self.intrinsic(Intrinsic::ArrayPrototype);
        if self.heap.is_object(p) {
            p
        } else {
            self.atoms.object_proto
        }
    }

    /// CreateArrayFromList ( elements ), §7.3.18†:
    /// 1. (Assert: each element is an ECMAScript language value.)
    /// 2. Let array be ! ArrayCreate(0).
    /// 3. Let n be 0.
    /// 4. For each element e of elements, do a. Perform !
    ///    CreateDataPropertyOrThrow(array, ! ToString(𝔽(n)), e). b. Set n to n + 1.
    /// 5. Return array.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn create_array_from_list(&mut self, items: &[Value]) -> Result<Value, Abrupt> {
        let a = self.array_create(0.0, None)?;
        for (i, v) in items.iter().enumerate() {
            let k = self.index_key(i as u64)?;
            self.create_data_property(a, k, *v)?;
        }
        Ok(a)
    }

    /// The interned key for the integer `i` (ToString of a Number that is an
    /// integer, §6.1.6.1.20†).
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn index_key(&mut self, i: u64) -> Result<Key, Abrupt> {
        Ok(self.heap.intern_str(&i.to_string())?)
    }

    /// Whether `v` is an Array exotic object (IsArray, §7.2.2† steps 1 to 3;
    /// no Proxies).
    #[must_use]
    pub fn is_array(&self, v: Value) -> bool {
        self.heap.is_array_object(v)
    }

    /// CreateDataProperty ( O, P, V ), §7.3.5†:
    /// 1. Let newDesc be the PropertyDescriptor { [[Value]]: V, [[Writable]]:
    ///    true, [[Enumerable]]: true, [[Configurable]]: true }.
    /// 2. Return ? O.[[DefineOwnProperty]](P, newDesc).
    ///
    /// # Errors
    /// As [`Vm::define_own_property`].
    pub fn create_data_property(&mut self, o: Value, k: Key, v: Value) -> Result<bool, Abrupt> {
        self.define_own_property(o, k, &PropDesc::all(v))
    }

    /// CreateDataPropertyOrThrow ( O, P, V ), §7.3.7†:
    /// 1. Let success be ? CreateDataProperty(O, P, V).
    /// 2. If success is false, throw a TypeError exception.
    /// 3. Return unused.
    ///
    /// # Errors
    /// A `TypeError`, or as [`Vm::define_own_property`].
    pub fn create_data_property_or_throw(
        &mut self,
        o: Value,
        k: Key,
        v: Value,
    ) -> Result<(), Abrupt> {
        if self.create_data_property(o, k, v)? {
            Ok(())
        } else {
            let name = self.key_text(k);
            Err(self.type_error(&format!("Cannot define property {name}")))
        }
    }

    /// DefinePropertyOrThrow ( O, P, desc ), §7.3.8†:
    /// 1. Let success be ? O.[[DefineOwnProperty]](P, desc).
    /// 2. If success is false, throw a TypeError exception.
    ///
    /// # Errors
    /// A `TypeError`, or as [`Vm::define_own_property`].
    pub fn define_property_or_throw(
        &mut self,
        o: Value,
        k: Key,
        desc: &PropDesc,
    ) -> Result<(), Abrupt> {
        if self.define_own_property(o, k, desc)? {
            Ok(())
        } else {
            let name = self.key_text(k);
            Err(self.type_error(&format!("Cannot redefine property: {name}")))
        }
    }

    /// `[[Delete]]` ( P ), OrdinaryDelete §10.1.10.1†:
    /// 1. Let desc be ? O.[[GetOwnProperty]](P).
    /// 2. If desc is undefined, return true.
    /// 3. If desc.[[Configurable]] is true, then a. Remove the own property
    ///    with name P from O. b. Return true.
    /// 4. Return false.
    ///
    /// The `length` of an array is not configurable, so it is never removed.
    ///
    /// # Errors
    /// [`Abrupt::OutOfMemory`].
    pub fn delete_property(&mut self, o: Value, k: Key) -> Result<bool, Abrupt> {
        let Some((attrs, _)) = self.get_own_property(o, k)? else {
            return Ok(true);
        };
        if attrs.0 & Attrs::CONFIGURABLE != 0 {
            self.heap.remove_properties(o, &[k])?;
            return Ok(true);
        }
        Ok(false)
    }

    /// DeletePropertyOrThrow ( O, P ), §7.3.10†:
    /// 1. Let success be ? O.[[Delete]](P).
    /// 2. If success is false, throw a TypeError exception.
    ///
    /// # Errors
    /// A `TypeError`, [`Abrupt::OutOfMemory`].
    pub fn delete_property_or_throw(&mut self, o: Value, k: Key) -> Result<(), Abrupt> {
        if self.delete_property(o, k)? {
            Ok(())
        } else {
            let name = self.key_text(k);
            Err(self.type_error(&format!("Cannot delete property '{name}'")))
        }
    }

    /// The step budget's check, for a native's long loops: one unit per call.
    ///
    /// # Errors
    /// [`Abrupt::Terminated`] when the budget is spent or the terminator set.
    pub fn charge_step(&mut self) -> Result<(), Abrupt> {
        self.charge()
    }
}
