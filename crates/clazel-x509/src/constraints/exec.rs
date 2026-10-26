//! Executable RFC 5280 constraint extension decoders.

use super::spec as constraint_spec;
use clazel_der::decode as der;
use clazel_der::spec::{Class, Tag};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

fn is_universal_tag(tag: Tag, number: u32, constructed: bool) -> (result: bool)
    ensures result == (tag == if constructed {
        clazel_der::spec::universal_constructed(number)
    } else {
        clazel_der::spec::universal_primitive(number)
    })
{
    match tag.class {
        Class::Universal => tag.number == number && tag.constructed == constructed,
        _ => false,
    }
}

fn pow2_u16(exponent: u8) -> (result: u16)
    requires exponent <= 7
    ensures result as nat == clazel_der::spec::pow2_unused(exponent)
{
    match exponent {
        0 => 1,
        1 => 2,
        2 => 4,
        3 => 8,
        4 => 16,
        5 => 32,
        6 => 64,
        _ => 128,
    }
}

/// Borrowed BasicConstraints value. pathLenConstraint uses canonical unsigned
/// magnitude octets so values larger than a machine integer remain intact.
#[derive(Clone, Copy)]
pub struct BasicConstraints<'a> {
    /// Whether the certificate subject may act as a CA.
    pub ca: bool,
    /// Nonnegative path length in big-endian magnitude form, if present.
    pub path_len_constraint: Option<&'a [u8]>,
}

impl View for BasicConstraints<'_> {
    type V = constraint_spec::BasicConstraints;
    closed spec fn view(&self) -> Self::V {
        constraint_spec::BasicConstraints {
            ca: self.ca,
            path_len_constraint: match self.path_len_constraint {
                Some(bytes) => Some(bytes@),
                None => None,
            },
        }
    }
}

/// Borrowed KeyUsage named BIT STRING data.
#[derive(Clone, Copy)]
pub struct KeyUsage<'a> {
    /// Data octets, excluding the initial unused-bits count.
    pub bits: &'a [u8],
    /// Number of meaningful named bits (1 through 9).
    pub bit_count: usize,
}

impl View for KeyUsage<'_> {
    type V = constraint_spec::KeyUsage;
    closed spec fn view(&self) -> Self::V {
        constraint_spec::KeyUsage { bits: self.bits@, bit_count: self.bit_count as nat }
    }
}

/// Names of the nine RFC 5280 KeyUsage bits.
#[derive(Clone, Copy)]
pub enum KeyUsageBit {
    /// digitalSignature (0).
    DigitalSignature,
    /// nonRepudiation/contentCommitment (1).
    ContentCommitment,
    /// keyEncipherment (2).
    KeyEncipherment,
    /// dataEncipherment (3).
    DataEncipherment,
    /// keyAgreement (4).
    KeyAgreement,
    /// keyCertSign (5).
    KeyCertSign,
    /// cRLSign (6).
    CrlSign,
    /// encipherOnly (7).
    EncipherOnly,
    /// decipherOnly (8).
    DecipherOnly,
}

impl View for KeyUsageBit {
    type V = constraint_spec::KeyUsageBit;
    closed spec fn view(&self) -> Self::V {
        match self {
            KeyUsageBit::DigitalSignature => constraint_spec::KeyUsageBit::DigitalSignature,
            KeyUsageBit::ContentCommitment => constraint_spec::KeyUsageBit::ContentCommitment,
            KeyUsageBit::KeyEncipherment => constraint_spec::KeyUsageBit::KeyEncipherment,
            KeyUsageBit::DataEncipherment => constraint_spec::KeyUsageBit::DataEncipherment,
            KeyUsageBit::KeyAgreement => constraint_spec::KeyUsageBit::KeyAgreement,
            KeyUsageBit::KeyCertSign => constraint_spec::KeyUsageBit::KeyCertSign,
            KeyUsageBit::CrlSign => constraint_spec::KeyUsageBit::CrlSign,
            KeyUsageBit::EncipherOnly => constraint_spec::KeyUsageBit::EncipherOnly,
            KeyUsageBit::DecipherOnly => constraint_spec::KeyUsageBit::DecipherOnly,
        }
    }
}

/// OID list in an ExtendedKeyUsage value.
pub struct ExtendedKeyUsage {
    /// Purpose OIDs in encoded order.
    pub purposes: Vec<Vec<u64>>,
}

pub open spec fn view_oid_list(items: Seq<Vec<u64>>) -> Seq<Seq<nat>> {
    items.map(|_i: int, oid: Vec<u64>| der::nats(oid@))
}

impl View for ExtendedKeyUsage {
    type V = constraint_spec::ExtendedKeyUsage;
    closed spec fn view(&self) -> Self::V {
        constraint_spec::ExtendedKeyUsage { purposes: view_oid_list(self.purposes@) }
    }
}

pub open spec fn view_basic_result(result: Option<BasicConstraints<'_>>) -> Option<constraint_spec::BasicConstraints> {
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn view_key_usage_result(result: Option<KeyUsage<'_>>) -> Option<constraint_spec::KeyUsage> {
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn view_eku_result(result: Option<ExtendedKeyUsage>) -> Option<constraint_spec::ExtendedKeyUsage> {
    match result { Some(value) => Some(value@), None => None }
}

pub open spec fn view_basic_option(
    value: Option<BasicConstraints<'_>>,
) -> Option<constraint_spec::BasicConstraints> {
    match value { Some(item) => Some(item@), None => None }
}

pub open spec fn view_key_usage_option(
    value: Option<KeyUsage<'_>>,
) -> Option<constraint_spec::KeyUsage> {
    match value { Some(item) => Some(item@), None => None }
}

/// RFC 5280 §4.2.1.9: decode the complete BasicConstraints SEQUENCE.
pub fn parse_basic_constraints(input: &[u8]) -> (result: Option<BasicConstraints<'_>>)
    ensures super::contract::parse_basic_constraints_ensures(input@, view_basic_result(result))
{
    let (start, end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if !is_universal_tag(outer.tag, 16, true) || outer.cstart != start
        || outer.cend != end || end != input.len() { return None; }
    let mut pos = start;
    let mut ca = false;
    if pos < end {
        let first = der::read_tlv(input, pos, end)?;
        if is_universal_tag(first.tag, 1, false) {
            let (value, next) = der::read_boolean(input, pos, end)?;
            if !value { return None; }
            ca = true;
            pos = next;
        }
    }
    let path_len_constraint = if pos == end {
        None
    } else {
        if !ca { return None; }
        let (negative, magnitude_start, magnitude_end, next) = der::read_integer(input, pos, end)?;
        if negative || next != end { return None; }
        Some(input.get(magnitude_start..magnitude_end)?)
    };
    Some(BasicConstraints { ca, path_len_constraint })
}

/// RFC 5280 §4.2.1.3: decode named KeyUsage bits 0 through 8.
pub fn parse_key_usage(input: &[u8]) -> (result: Option<KeyUsage<'_>>)
    ensures super::contract::parse_key_usage_ensures(input@, view_key_usage_result(result))
{
    let (unused, start, end, next) = der::read_bit_string(input, 0, input.len())?;
    if next != input.len() { return None; }
    let bit_octets = input.get(start..end)?;
    let total = bit_octets.len().checked_mul(8)?;
    let bit_count = total.checked_sub(unused as usize)?;
    if bit_count == 0 || bit_count > 9 { return None; }
    let last = *bit_octets.last()?;
    assert(unused <= 7);
    let divisor = pow2_u16(unused);
    let last_value = last as u16;
    if last_value.checked_rem(divisor)? != 0 { return None; }
    if last_value.checked_div(divisor)?.checked_rem(2)? != 1 { return None; }
    proof {
        assert(clazel_der::spec::read_bit_string(input@, 0, input@.len())
            == der::view_bit_string(Some((unused, start, end, next))));
        assert(bit_octets@ == input@.subrange(start as int, end as int));
        reveal(constraint_spec::parse_key_usage);
    }
    Some(KeyUsage { bits: bit_octets, bit_count })
}

fn key_usage_index(bit: KeyUsageBit) -> (result: usize)
    ensures result as nat == constraint_spec::key_usage_bit_index(bit@)
{
    match bit {
        KeyUsageBit::DigitalSignature => 0,
        KeyUsageBit::ContentCommitment => 1,
        KeyUsageBit::KeyEncipherment => 2,
        KeyUsageBit::DataEncipherment => 3,
        KeyUsageBit::KeyAgreement => 4,
        KeyUsageBit::KeyCertSign => 5,
        KeyUsageBit::CrlSign => 6,
        KeyUsageBit::EncipherOnly => 7,
        KeyUsageBit::DecipherOnly => 8,
    }
}

/// Query one of the nine named KeyUsage bits.
pub fn key_usage_has(usage: KeyUsage<'_>, bit: KeyUsageBit) -> (result: bool)
    ensures result == constraint_spec::key_usage_has(usage@, bit@)
{
    let index = key_usage_index(bit);
    assert(index <= 8);
    if index >= usage.bit_count || index / 8 >= usage.bits.len() { return false; }
    let byte = match usage.bits.get(index / 8) { Some(value) => *value, None => return false };
    let exponent = match 7usize.checked_sub(index % 8) {
        Some(value) => match u8::try_from(value) {
            Ok(value) => value,
            Err(_) => return false,
        },
        None => return false,
    };
    let divisor = pow2_u16(exponent);
    let quotient = match (byte as u16).checked_div(divisor) {
        Some(value) => value,
        None => return false,
    };
    let remainder = match quotient.checked_rem(2) {
        Some(value) => value,
        None => return false,
    };
    proof {
        assert(divisor as nat == clazel_der::spec::pow2_unused(exponent));
        assert(quotient as nat == (byte as nat) / clazel_der::spec::pow2_unused(exponent));
        assert(remainder as nat
            == ((byte as nat) / clazel_der::spec::pow2_unused(exponent)) % 2);
        assert(index as nat == constraint_spec::key_usage_bit_index(bit@));
        assert((index as nat) < usage.bits@.len() * 8);
        reveal(constraint_spec::key_usage_has);
    }
    remainder == 1
}

/// Cross-extension cA/keyCertSign and pathLen profile conditions.
pub fn basic_constraints_compatible(
    basic: Option<BasicConstraints<'_>>, key_usage: Option<KeyUsage<'_>>,
) -> (result: bool)
    ensures result == constraint_spec::basic_constraints_compatible(
        view_basic_option(basic), view_key_usage_option(key_usage))
{
    let cert_sign = match key_usage {
        Some(usage) => key_usage_has(usage, KeyUsageBit::KeyCertSign),
        None => false,
    };
    match basic {
        Some(value) => (!cert_sign || value.ca)
            && (value.path_len_constraint.is_none() || value.ca && cert_sign),
        None => !cert_sign,
    }
}

fn oid_equal(left: &[u64], right: &[u64]) -> (result: bool)
    ensures result == (der::nats(left@) =~= der::nats(right@))
{
    if left.len() != right.len() { return false; }
    let mut i = 0;
    while i < left.len()
        invariant i <= left.len(), left.len() == right.len(),
            forall|j: int| 0 <= j < i as int ==> left@[j] == right@[j]
        decreases left.len() - i
    {
        let left_arc = match left.get(i) { Some(value) => *value, None => return false };
        let right_arc = match right.get(i) { Some(value) => *value, None => return false };
        if left_arc != right_arc {
            proof {
                assert(der::nats(left@)[i as int] == left_arc as nat) by { reveal(der::nats); }
                assert(der::nats(right@)[i as int] == right_arc as nat) by { reveal(der::nats); }
                assert(der::nats(left@) !~= der::nats(right@));
            }
            return false;
        }
        proof {
            assert(der::nats(left@)[i as int] == der::nats(right@)[i as int]) by { reveal(der::nats); }
        }
        i = i.saturating_add(1);
    }
    true
}

proof fn lemma_view_oid_list_index(items: Seq<Vec<u64>>, index: int)
    requires 0 <= index < items.len()
    ensures view_oid_list(items)[index] =~= der::nats(items[index]@)
{
    reveal(view_oid_list);
}

fn oid_seen_exec(seen: &[Vec<u64>], candidate: &[u64]) -> (result: bool)
    ensures result == constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), 0)
{
    let mut i = 0;
    while i < seen.len()
        invariant
            i <= seen.len(),
            seen@.len() == seen.len(),
            view_oid_list(seen@).len() == seen.len(),
            constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), 0)
                == constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), i as int),
        decreases seen.len() - i
    {
        let current = match seen.get(i) { Some(value) => value, None => return false };
        if oid_equal(current, candidate) {
            proof {
                let ghost mapped_current = der::nats(current@);
                lemma_view_oid_list_index(seen@, i as int);
                assert(view_oid_list(seen@)[i as int] =~= mapped_current);
                assert(mapped_current =~= der::nats(candidate@));
                reveal_with_fuel(constraint_spec::oid_in, 1);
                assert(constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), i as int));
                assert(constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), 0));
            }
            return true;
        }
        proof {
            let ghost mapped_current = der::nats(current@);
            lemma_view_oid_list_index(seen@, i as int);
            assert(view_oid_list(seen@)[i as int] =~= mapped_current);
            assert(!(mapped_current =~= der::nats(candidate@)));
            assert(!(view_oid_list(seen@)[i as int] =~= der::nats(candidate@)));
            reveal_with_fuel(constraint_spec::oid_in, 1);
            assert(constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), i as int)
                == constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), i as int + 1));
        }
        i = i.saturating_add(1);
    }
    proof {
        reveal_with_fuel(constraint_spec::oid_in, 1);
        assert(!constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), i as int));
        assert(!constraint_spec::oid_in(view_oid_list(seen@), der::nats(candidate@), 0));
    }
    false
}

/// RFC 5280 §4.2.1.12: decode a nonempty Extensions KeyPurposeId sequence.
pub fn parse_extended_key_usage(input: &[u8]) -> (result: Option<ExtendedKeyUsage>)
    ensures super::contract::parse_extended_key_usage_ensures(input@, view_eku_result(result))
{
    let (start, end) = der::expect_sequence(input, 0, input.len())?;
    let outer = der::read_tlv(input, 0, input.len())?;
    if !is_universal_tag(outer.tag, 16, true) || outer.cstart != start
        || outer.cend != end || end != input.len() || start == end {
        proof {
            reveal(constraint_spec::parse_extended_key_usage);
            assert(constraint_spec::parse_extended_key_usage(input@) is None);
        }
        return None;
    }
    let empty_seen: Vec<Vec<u64>> = Vec::new();
    let parsed = parse_eku_items(input, start, end, empty_seen.clone());
    let (purposes, final_pos) = match parsed {
        Some(value) => value,
        None => {
            proof {
                reveal(view_oid_list);
                assert(view_oid_list(empty_seen@) =~= seq![]);
                reveal(constraint_spec::parse_extended_key_usage);
                assert(constraint_spec::parse_eku_items(input@, start as nat, end as nat,
                    seq![], seq![]) is None);
                assert(constraint_spec::parse_extended_key_usage(input@) is None);
            }
            return None;
        }
    };
    if final_pos != end || purposes.is_empty() {
        proof {
            reveal(view_oid_list);
            assert(view_oid_list(empty_seen@) =~= seq![]);
            reveal(constraint_spec::parse_extended_key_usage);
            assert(constraint_spec::parse_extended_key_usage(input@) is None);
        }
        return None;
    }
    proof {
        reveal(view_oid_list);
        assert(view_oid_list(empty_seen@) =~= seq![]);
        reveal(constraint_spec::parse_extended_key_usage);
        assert(constraint_spec::parse_extended_key_usage(input@)
            == Some(constraint_spec::ExtendedKeyUsage { purposes: view_oid_list(purposes@) }));
    }
    Some(ExtendedKeyUsage { purposes })
}

/// Iterative OID scan refined against the accumulator specification.
fn parse_eku_items(input: &[u8], start: usize, end: usize, seen: Vec<Vec<u64>>)
    -> (result: Option<(Vec<Vec<u64>>, usize)>)
    requires start <= end, end <= input.len()
    ensures view_eku_items_result(result)
        == constraint_spec::parse_eku_items(input@, start as nat, end as nat,
            view_oid_list(seen@), seq![])
{
    let mut purposes = Vec::new();
    let mut seen_oids = seen.clone();
    let ghost initial_seen = view_oid_list(seen@);
    let ghost mut spec_seen = initial_seen;
    let mut pos = start;
    proof {
        reveal(view_oid_list);
        assert(view_oid_list(purposes@) =~= seq![]);
        assert(initial_seen == view_oid_list(seen_oids@));
        assert(spec_seen == initial_seen);
        assert(constraint_spec::parse_eku_items(
            input@, start as nat, end as nat, initial_seen, seq![])
            == constraint_spec::parse_eku_items(
                input@, pos as nat, end as nat, spec_seen, view_oid_list(purposes@)));
    }
    while pos < end
        invariant
            start <= pos <= end,
            end <= input.len(),
            initial_seen == view_oid_list(seen@),
            spec_seen == initial_seen + view_oid_list(purposes@),
            view_oid_list(seen_oids@) == spec_seen,
            constraint_spec::parse_eku_items(
                input@, start as nat, end as nat, initial_seen, seq![])
                == constraint_spec::parse_eku_items(
                    input@, pos as nat, end as nat, spec_seen, view_oid_list(purposes@)),
        decreases end - pos
    {
        let (oid, next) = match der::read_oid(input, pos, end) {
            Some(pair) => pair,
            None => {
                proof {
                    reveal_with_fuel(constraint_spec::parse_eku_items, 1);
                    assert(constraint_spec::parse_eku_items(input@, pos as nat, end as nat,
                        spec_seen, view_oid_list(purposes@)) is None);
                    assert(constraint_spec::parse_eku_items(
                        input@, start as nat, end as nat, initial_seen, seq![]) is None);
                }
                return None;
            }
        };
        if next <= pos || next > end {
            proof {
                reveal_with_fuel(constraint_spec::parse_eku_items, 1);
                assert(constraint_spec::parse_eku_items(input@, pos as nat, end as nat,
                    spec_seen, view_oid_list(purposes@)) is None);
                assert(constraint_spec::parse_eku_items(
                    input@, start as nat, end as nat, initial_seen, seq![]) is None);
            }
            return None;
        }
        if oid_seen_exec(&seen_oids, &oid) {
            proof {
                assert(constraint_spec::oid_in(spec_seen, der::nats(oid@), 0));
                reveal_with_fuel(constraint_spec::parse_eku_items, 1);
                assert(constraint_spec::parse_eku_items(input@, pos as nat, end as nat,
                    spec_seen, view_oid_list(purposes@)) is None);
                assert(constraint_spec::parse_eku_items(
                    input@, start as nat, end as nat, initial_seen, seq![]) is None);
            }
            return None;
        }
        let ghost oid_view = der::nats(oid@);
        let ghost old_purposes = view_oid_list(purposes@);
        proof {
            reveal_with_fuel(constraint_spec::parse_eku_items, 1);
            assert(constraint_spec::parse_eku_items(
                input@, start as nat, end as nat, initial_seen, seq![])
                == constraint_spec::parse_eku_items(
                    input@, next as nat, end as nat,
                    spec_seen.push(oid_view), old_purposes.push(oid_view)));
        }
        purposes.push(oid.clone());
        seen_oids.push(oid);
        pos = next;
        proof {
            spec_seen = spec_seen.push(oid_view);
            reveal(view_oid_list);
            assert(view_oid_list(purposes@) == old_purposes.push(oid_view));
            assert(view_oid_list(seen_oids@) == spec_seen);
        }
    }
    proof {
        reveal_with_fuel(constraint_spec::parse_eku_items, 1);
        assert(constraint_spec::parse_eku_items(
            input@, start as nat, end as nat, initial_seen, seq![])
            == Some((view_oid_list(purposes@), end as nat)));
    }
    Some((purposes, end))
}

pub open spec fn view_eku_items_result(
    result: Option<(Vec<Vec<u64>>, usize)>,
) -> Option<(Seq<Seq<nat>>, nat)> {
    match result {
        Some((purposes, next)) => Some((view_oid_list(purposes@), next as nat)),
        None => None,
    }
}

/// Explicit application policy for serverAuth and anyExtendedKeyUsage.
pub fn eku_allows_server_auth(eku: ExtendedKeyUsage, allow_any: bool) -> (result: bool)
    ensures result == constraint_spec::eku_allows_server_auth(eku@, allow_any)
{
    let server_auth = vec![1u64, 3, 6, 1, 5, 5, 7, 3, 1];
    let any_eku = vec![2u64, 5, 29, 37, 0];
    let has_server_auth = oid_seen_exec(&eku.purposes, &server_auth);
    let has_any = oid_seen_exec(&eku.purposes, &any_eku);
    proof {
        reveal(der::nats);
        assert(der::nats(server_auth@) =~= constraint_spec::server_auth_oid()) by { reveal(der::nats); }
        assert(der::nats(any_eku@) =~= constraint_spec::any_extended_key_usage_oid()) by { reveal(der::nats); }
        assert(view_oid_list(eku.purposes@) == eku@.purposes);
        reveal(constraint_spec::eku_allows_server_auth);
    }
    has_server_auth || allow_any && has_any
}

} // verus!
