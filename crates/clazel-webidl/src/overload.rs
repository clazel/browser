//! Overload resolution (WebIDL §2.5.8† "effective overload set" and §3.6†
//! "overload resolution algorithm").
//!
//! <https://webidl.spec.whatwg.org/#es-overloads>
//!
//! The generator writes, for each overloaded operation or constructor, the
//! overloads' argument lists as data ([`Overload`]); [`resolve`] computes the
//! effective overload set for the number of arguments given and picks the
//! overload. The generated glue then converts the arguments with the chosen
//! overload's types.
//!
//! Modelling choices:
//! - **Conversion happens after the choice.** §3.6† converts the arguments
//!   before the distinguishing index while it chooses (step 11). Those
//!   arguments have the same type in every remaining entry, so their values
//!   do not depend on the choice; only the order of their side effects
//!   against the choice's own `TypeError` (step 12.21) differs, when no
//!   overload matches and an earlier conversion would throw too.
//! - Buffer source types, `bigint` and `symbol` are absent (no exposed
//!   overload uses them), so steps 12.5 to 12.9, 12.15 and 12.18 are not
//!   written. Step 12.11's iterator check is the Array check of
//!   `crate::convert::sequence`.

use clazel_js::{ErrorKind, Local, Result, Scope, ValueKind};

use crate::generated::bindings::InterfaceId;
use crate::platform::{Platform, Wrapper};

/// The kinds of type at one position of an overload, for choosing (the
/// categories of §2.5.8.1† "distinguishable"). A union counts as each of its
/// flattened member types.
#[derive(Clone, Copy, Debug, Default)]
pub struct TypeSet {
    /// Interface types.
    pub interfaces: &'static [InterfaceId],
    /// A nullable type, or a union with one.
    pub nullable: bool,
    /// A dictionary type.
    pub dictionary: bool,
    /// A callback function type.
    pub callback_function: bool,
    /// A callback interface type.
    pub callback_interface: bool,
    /// A sequence or frozen array type.
    pub sequence: bool,
    /// `object`.
    pub object: bool,
    /// `boolean`.
    pub boolean: bool,
    /// A numeric type.
    pub numeric: bool,
    /// A string type or an enumeration.
    pub string: bool,
    /// `any`.
    pub any: bool,
    /// `undefined`.
    pub undefined: bool,
}

/// An argument of an overload.
#[derive(Clone, Copy, Debug)]
pub struct Arg {
    /// Its type.
    pub types: TypeSet,
    /// `optional` (or with a default).
    pub optional: bool,
    /// `...`.
    pub variadic: bool,
}

/// One overload: its arguments.
#[derive(Clone, Copy, Debug)]
pub struct Overload {
    /// The arguments, in order.
    pub args: &'static [Arg],
}

/// An entry of the effective overload set: the overload, its type list and
/// its optionality list (§2.5.8†).
struct Entry {
    overload: usize,
    types: Vec<TypeSet>,
    optional: Vec<bool>,
}

/// The effective overload set for `n` arguments (§2.5.8†):
/// 1. Let S be an ordered set.
/// 2. Let F be an ordered set with the overloads.
/// 3. Let maxarg be the maximum number of arguments the operations, legacy
///    factory functions, or callback functions in F are declared to take.
///    For variadic operations and legacy factory functions, the argument on
///    which the ellipsis appears counts as a single argument.
/// 4. Let max be max(maxarg, N).
/// 5. For each operation or extended attribute X in F: 1. Let arguments be
///    the list of arguments X is declared to take. 2. Let n be the size of
///    arguments. 3. Let types be a type list. 4. Let optionalityValues be an
///    optionality list. 5. For each argument in arguments: append its type
///    and "variadic", "optional" or "required". 6. Append the tuple (X,
///    types, optionalityValues) to S. 7. If X is declared to be variadic,
///    then: 1. For each i in the range n to max − 1, inclusive: append to S
///    the tuple with types and optionality values extended by the last
///    argument's, up to i + 1 of them. 8. Let i be n − 1. 9. While i ≥ 0:
///    (a) If arguments\[i\] is not optional (it is not marked "optional"
///    and is not a final, variadic argument), then break. (b) Let t be the
///    first i types and o the first i optionality values. (c) Append
///    (X, t, o). (d) Set i to i − 1.
/// 6. Return S.
fn effective_set(overloads: &[Overload], n: usize) -> Vec<Entry> {
    let maxarg = overloads.iter().map(|o| o.args.len()).max().unwrap_or(0);
    let max = maxarg.max(n);
    let mut s = Vec::new();
    for (x, o) in overloads.iter().enumerate() {
        let types: Vec<TypeSet> = o.args.iter().map(|a| a.types).collect();
        let optional: Vec<bool> = o.args.iter().map(|a| a.optional || a.variadic).collect();
        s.push(Entry {
            overload: x,
            types: types.clone(),
            optional: optional.clone(),
        });
        if let Some(last) = o.args.last().filter(|a| a.variadic) {
            let mut t = types.clone();
            let mut opt = optional.clone();
            while t.len() < max {
                t.push(last.types);
                opt.push(true);
                s.push(Entry {
                    overload: x,
                    types: t.clone(),
                    optional: opt.clone(),
                });
            }
        }
        // Step 5.8 and 5.9: the prefixes that drop trailing optional
        // arguments, longest first.
        for (i, a) in o.args.iter().enumerate().rev() {
            if !(a.optional || a.variadic) {
                break;
            }
            s.push(Entry {
                overload: x,
                types: types.iter().take(i).copied().collect(),
                optional: optional.iter().take(i).copied().collect(),
            });
        }
    }
    s
}

/// The distinguishing argument index of entries of the same length
/// (§2.5.8†: "the index of the first argument whose types are
/// distinguishable"; the generator has checked that the overloads are
/// valid, so the first position where the type sets differ is it).
fn distinguishing_index(s: &[Entry]) -> usize {
    let Some(first) = s.first() else {
        return 0;
    };
    for (i, t) in first.types.iter().enumerate() {
        let key = format!("{t:?}");
        if s.iter()
            .any(|e| e.types.get(i).map(|u| format!("{u:?}")) != Some(key.clone()))
        {
            return i;
        }
    }
    0
}

/// The overload resolution algorithm (§3.6†), up to choosing the overload:
/// 1. Let maxarg be the length of the longest type list of the entries in S.
/// 2. Let n be the size of args.
/// 3. Initialize argcount to be min(maxarg, n).
/// 4. Remove from S all entries whose type list is not of length argcount.
/// 5. If S is empty, then throw a TypeError.
/// 6. Initialize d to −1.
/// 8. If there is more than one entry in S, then set d to be the
///    distinguishing argument index for the entries of S.
/// 12. If i = d, then: 1. Let V be args[i]. 2. If V is undefined, and there
///     is an entry in S whose list of optionality values has "optional" at
///     index i, then remove from S all other entries. 3. Otherwise: if V is
///     null or undefined, and there is an entry in S that has a nullable
///     type, a dictionary type, or a union type that includes a nullable
///     type or has a dictionary type in its flattened members at position
///     i, then remove from S all other entries. 4. Otherwise: if V is a
///     platform object, and there is an entry in S that has an interface
///     type that V implements at position i, then remove from S all other
///     entries. 10. Otherwise: if V is an Object and IsCallable(V) is true,
///     and there is an entry in S that has a callback function type at
///     position i, then remove from S all other entries. 11. Otherwise: if
///     V is an Object and there is an entry in S that has a sequence type
///     at position i (and V is iterable), then remove all other entries. 12.
///     Otherwise: if V is an Object and there is an entry in S that has a
///     callback interface type, a dictionary type, a record type or
///     `object` at position i, then remove from S all other entries. 13.
///     Otherwise: if V is a Boolean and there is an entry in S that has
///     `boolean` at position i, then remove from S all other entries. 14.
///     Otherwise: if V is a Number and there is an entry in S that has a
///     numeric type at position i, then remove from S all other entries. 16.
///     Otherwise: if there is an entry in S that has a string type at
///     position i, then remove from S all other entries. 17. Otherwise: if
///     there is an entry in S that has a numeric type at position i, then
///     remove from S all other entries. 19. Otherwise: if there is an entry
///     in S that has `boolean` at position i, then remove from S all other
///     entries. 20. Otherwise: if there is an entry in S that has `any` at
///     position i, then remove from S all other entries. 21. Otherwise:
///     throw a TypeError.
/// 13. Let callable be the operation of the single entry in S.
///
/// Returns the chosen overload's index.
///
/// # Errors
/// The TypeErrors of steps 5 and 12.21.
pub fn resolve<P: Platform>(
    scope: &mut Scope<'_>,
    overloads: &[Overload],
    args: &[Local<'_>],
) -> Result<usize> {
    let n = args.len();
    let mut s = effective_set(overloads, n);
    let maxarg = s.iter().map(|e| e.types.len()).max().unwrap_or(0);
    let argcount = maxarg.min(n);
    s.retain(|e| e.types.len() == argcount);
    if s.is_empty() {
        return Err(scope.throw_error(
            ErrorKind::TypeError,
            "Not enough arguments, or no overload takes this many",
        ));
    }
    let only = s.first().map_or(0, |e| e.overload);
    if s.iter().all(|e| e.overload == only) {
        return Ok(only);
    }
    let d = distinguishing_index(&s);
    let Some(v) = args.get(d).copied() else {
        return Ok(only);
    };
    let kind = scope.kind(v);
    let pick =
        |s: &[Entry], f: &dyn Fn(&Entry) -> bool| s.iter().find(|e| f(e)).map(|e| e.overload);
    let at = |e: &Entry| e.types.get(d).copied().unwrap_or_default();
    if kind == ValueKind::Undefined
        && let Some(o) = pick(&s, &|e| e.optional.get(d).copied().unwrap_or(false))
    {
        return Ok(o);
    }
    if matches!(kind, ValueKind::Undefined | ValueKind::Null)
        && let Some(o) = pick(&s, &|e| at(e).nullable || at(e).dictionary)
    {
        return Ok(o);
    }
    let is_object = matches!(kind, ValueKind::Object | ValueKind::Function);
    if is_object {
        // Step 12.4: a platform object implementing one of the interfaces.
        let platform_interface = match scope.host_data::<Wrapper>(v) {
            Ok(w) => Some(w.interface),
            Err(_) => {
                let global = crate::platform::global::<P>(scope)?;
                scope
                    .strict_equals(v, global)
                    .then_some(InterfaceId::Window)
            }
        };
        if let Some(pi) = platform_interface
            && let Some(o) = pick(&s, &|e| at(e).interfaces.iter().any(|i| pi.inherits(*i)))
        {
            return Ok(o);
        }
        if scope.is_callable(v)
            && let Some(o) = pick(&s, &|e| at(e).callback_function)
        {
            return Ok(o);
        }
        if scope.is_array(v)?
            && let Some(o) = pick(&s, &|e| at(e).sequence)
        {
            return Ok(o);
        }
        if let Some(o) = pick(&s, &|e| {
            let t = at(e);
            t.callback_interface || t.dictionary || t.object
        }) {
            return Ok(o);
        }
    }
    if kind == ValueKind::Boolean
        && let Some(o) = pick(&s, &|e| at(e).boolean)
    {
        return Ok(o);
    }
    if kind == ValueKind::Number
        && let Some(o) = pick(&s, &|e| at(e).numeric)
    {
        return Ok(o);
    }
    for f in [
        (&|t: TypeSet| t.string) as &dyn Fn(TypeSet) -> bool,
        &|t: TypeSet| t.numeric,
        &|t: TypeSet| t.boolean,
        &|t: TypeSet| t.any,
    ] {
        if let Some(o) = pick(&s, &|e| f(at(e))) {
            return Ok(o);
        }
    }
    Err(scope.throw_error(ErrorKind::TypeError, "No overload matches the arguments"))
}
