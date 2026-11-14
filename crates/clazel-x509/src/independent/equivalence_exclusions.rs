//! Narrowing `equivalence.rs`'s exclusions. Each entry says which side of a
//! disagreement holds, and for three of them that the disagreement is a
//! predicate of the transcription, not a difference between the two.
//!
//! Conditions 1 to 3 appear only in the `_fwd` theorems and 4 to 13 only in the
//! `_back` ones, so each is already one-directional: where a condition fails,
//! the other direction still holds. What this file adds:
//!
//! - **Conditions 5, 8, 9** are `requirements.rs` predicates. The transcription
//!   is `decode_certificate` together with them, and against that pair they are
//!   no exclusion: what the crate reads satisfies them
//!   (`theorem_one_signature`, `theorem_version_rules`,
//!   `theorem_issuer_non_empty`), and `_back` asks for exactly them.
//! - **Condition 13, duplicates,** with `no_duplicate_extensions` is narrowed to
//!   extensions X.509 does not define ([`theorem_duplicates_are_foreign`]).
//! - **The iPAddress size in a subjectAltName** is `subject_alt_name_rules`.
//! - **The RSA NULL disagreement** is exactly that and nothing wider:
//!   [`theorem_prepare_signature_same`] says two identifiers
//!   `prepare_signature` takes are equal, or have one RSA object identifier and
//!   differ only between NULL and absent.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::leaf::spec as lf;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;

verus! {

/// `no_duplicate_extensions` reaches every pair.
pub proof fn lemma_no_duplicates_at(v: Seq<e::Extension>, k: nat, a: int, b: int)
    requires
        r::no_duplicate_extensions(v, k),
        k <= a < b < v.len(),
    ensures
        r::defined_in_this_specification(v[a].extn_id) ==> v[a].extn_id != v[b].extn_id,
    decreases a - k,
{
    if k < a {
        lemma_no_duplicates_at(v, k + 1, a, b);
    } else if r::defined_in_this_specification(v[a].extn_id) {
        lemma_find_absent(v, k + 1, v[a].extn_id, b);
    }
}

/// `absent_from` reaches every later extension.
pub proof fn lemma_find_absent(v: Seq<e::Extension>, k: nat, id: Seq<nat>, b: int)
    requires
        r::find_extension(v, k, id) is None,
        k <= b < v.len(),
    ensures
        v[b].extn_id != id,
    decreases b - k,
{
    if k < b {
        lemma_find_absent(v, k + 1, id, b);
    }
}

/// **`theorem_duplicates_are_foreign`.** With `no_duplicate_extensions`, what is
/// left of condition 13 is an extension X.509 does not define.
pub proof fn theorem_duplicates_are_foreign(v: Seq<e::Extension>, a: int, b: int)
    requires
        r::no_duplicate_extensions(v, 0),
        0 <= a < b < v.len(),
        v[a].extn_id == v[b].extn_id,
    ensures
        !r::defined_in_this_specification(v[a].extn_id),
{
    lemma_no_duplicates_at(v, 0, a, b);
}

/// `leaf/spec.rs`'s `find_extension` is `requirements.rs`'s, on lists that agree.
pub proof fn lemma_leaf_find(a: Seq<x::Extension>, v: Seq<e::Extension>, oid: Seq<nat>, k: int)
    requires
        a.len() == v.len(),
        forall|m: int| 0 <= m < a.len() ==> (#[trigger] a[m]).oid == v[m].extn_id,
        0 <= k <= a.len(),
    ensures
        (lf::find_extension(a, oid, k) is Some) == (r::find_extension(v, k as nat, oid) is Some),
    decreases a.len() - k,
{
    if k < a.len() {
        assert(a[k].oid == v[k].extn_id);
        if !(a[k].oid =~= oid) {
            lemma_leaf_find(a, v, oid, k + 1);
        }
    }
}

/// The two RSA parameter forms: absent and NULL.
pub open spec fn null_or_absent(p: Option<Seq<u8>>) -> bool {
    p is None || p == Some(seq![0x05u8, 0x00])
}

/// **`theorem_prepare_signature_same`.** What `prepare_signature` takes is one
/// value, except RSA with NULL on one side and absent on the other.
pub proof fn theorem_prepare_signature_same(
    a: c::AlgorithmIdentifier,
    b: c::AlgorithmIdentifier,
    tbs: Seq<u8>,
    bits: Seq<u8>,
    unused: u8,
)
    requires
        g::prepare_signature(a, b, tbs, bits, unused) is Some,
    ensures
        a.oid == b.oid,
        a == b || (null_or_absent(a.parameters_der) && null_or_absent(b.parameters_der) && (g::is_sha256_with_rsa(a.oid)
            || g::is_sha384_with_rsa(a.oid) || g::is_sha512_with_rsa(a.oid))),
{
    let (ca, cb) = (g::classify(a)->Some_0, g::classify(b)->Some_0);
    assert(a.oid =~= b.oid);
}

} // verus!
