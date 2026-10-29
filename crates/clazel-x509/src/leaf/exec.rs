//! Executable, refinement-checked composition of supported leaf checks.

use crate::constraints::exec as constraints;
use crate::extensions::exec as extensions;
use crate::matcher::{PresentedIdentity, ReferenceIdentity};
use crate::time::exec::CertificateTime;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Explicit anyExtendedKeyUsage policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LeafPolicy {
    /// Allow anyExtendedKeyUsage when serverAuth is absent.
    pub allow_any_extended_key_usage: bool,
}

impl View for LeafPolicy {
    type V = super::spec::LeafPolicy;
    closed spec fn view(&self) -> Self::V {
        super::spec::LeafPolicy { allow_any_extended_key_usage: self.allow_any_extended_key_usage }
    }
}

/// Partial-validation state exposed to make the validation boundary explicit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PartialValidationState {
    /// Signature, path, trust, revocation, and remaining policy checks remain.
    NeedsPathValidation,
}

impl View for PartialValidationState {
    type V = super::spec::PartialValidationState;
    closed spec fn view(&self) -> Self::V {
        match self {
            PartialValidationState::NeedsPathValidation => super::spec::PartialValidationState::NeedsPathValidation,
        }
    }
}

/// Successful evidence from the explicitly partial server-leaf checker.
pub struct PartialLeafChecks<'a> {
    /// Captured reference identifier used for SAN matching.
    pub reference: ReferenceIdentity<'a>,
    /// Captured time used for inclusive validity checking.
    pub now: CertificateTime,
    /// Decoded validity lower endpoint.
    pub not_before: CertificateTime,
    /// Decoded validity upper endpoint.
    pub not_after: CertificateTime,
    /// A same-type subjectAltName DNS-ID/IP-ID matched the reference.
    pub identity_matched: bool,
    /// The captured time lies within the certificate's inclusive interval.
    pub valid_at_captured_time: bool,
    /// EKU was absent or permitted server authentication.
    pub server_auth_purpose_allowed: bool,
    /// KeyUsage was absent or included digitalSignature.
    pub digital_signature_allowed: bool,
    /// BasicConstraints and keyCertSign semantics permit an end entity.
    pub leaf_role_allowed: bool,
    /// Whether KeyUsage was present.
    pub key_usage_present: bool,
    /// Whether ExtendedKeyUsage was present.
    pub extended_key_usage_present: bool,
    /// Whether BasicConstraints was present.
    pub basic_constraints_present: bool,
    /// This partial result always requires later path and signature validation.
    pub state: PartialValidationState,
}

fn copy_time(value: &CertificateTime) -> (result: CertificateTime)
    ensures result@ == value@
{
    CertificateTime {
        year: value.year, month: value.month, day: value.day,
        hour: value.hour, minute: value.minute, second: value.second,
    }
}

impl View for PartialLeafChecks<'_> {
    type V = super::spec::PartialLeafChecks;
    closed spec fn view(&self) -> Self::V {
        super::spec::PartialLeafChecks {
            reference: crate::exec::view_reference_identity(&self.reference),
            now: self.now@,
            not_before: self.not_before@,
            not_after: self.not_after@,
            identity_matched: self.identity_matched,
            valid_at_captured_time: self.valid_at_captured_time,
            server_auth_purpose_allowed: self.server_auth_purpose_allowed,
            digital_signature_allowed: self.digital_signature_allowed,
            leaf_role_allowed: self.leaf_role_allowed,
            key_usage_present: self.key_usage_present,
            extended_key_usage_present: self.extended_key_usage_present,
            basic_constraints_present: self.basic_constraints_present,
            state: self.state@,
        }
    }
}

/// View of the optional executable result.
pub open spec fn view_leaf_result(result: Option<PartialLeafChecks<'_>>)
    -> Option<super::spec::PartialLeafChecks> {
    match result { Some(value) => Some(value@), None => None }
}

pub(crate) fn oid_arcs_equal(left: &[u64], right: &[u64]) -> (result: bool)
    ensures result == (clazel_der::decode::nats(left@) =~= clazel_der::decode::nats(right@))
{
    if left.len() != right.len() { return false; }
    let mut index = 0;
    while index < left.len()
        invariant
            index <= left.len(), left.len() == right.len(),
            forall|j: int| 0 <= j < index ==> clazel_der::decode::nats(left@)[j] == clazel_der::decode::nats(right@)[j],
        decreases left.len() - index
    {
        let a = match left.get(index) { Some(value) => *value, None => return false };
        let b = match right.get(index) { Some(value) => *value, None => return false };
        if a != b {
            proof {
                assert(clazel_der::decode::nats(left@)[index as int] == a as nat) by { reveal(clazel_der::decode::nats); }
                assert(clazel_der::decode::nats(right@)[index as int] == b as nat) by { reveal(clazel_der::decode::nats); }
                assert(clazel_der::decode::nats(left@) !~= clazel_der::decode::nats(right@));
            }
            return false;
        }
        proof { assert(clazel_der::decode::nats(left@)[index as int] == clazel_der::decode::nats(right@)[index as int]) by { reveal(clazel_der::decode::nats); } }
        index = index.saturating_add(1);
    }
    assert(clazel_der::decode::nats(left@) =~= clazel_der::decode::nats(right@)) by { reveal(clazel_der::decode::nats); }
    true
}

/// Decode the fixed subjectAltName OID through the same DER reader used for input values.
pub(crate) fn san_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= crate::extensions::spec::subject_alt_name_oid()
{
    let arcs = vec![2u64, 5, 29, 17];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= crate::extensions::spec::subject_alt_name_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(crate::extensions::spec::subject_alt_name_oid);
        }
    }
    arcs
}

pub(crate) fn basic_constraints_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= super::spec::basic_constraints_oid()
{
    let arcs = vec![2u64, 5, 29, 19];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= super::spec::basic_constraints_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(super::spec::basic_constraints_oid);
        }
    }
    arcs
}

pub(crate) fn key_usage_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= super::spec::key_usage_oid()
{
    let arcs = vec![2u64, 5, 29, 15];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= super::spec::key_usage_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(super::spec::key_usage_oid);
        }
    }
    arcs
}

pub(crate) fn extended_key_usage_oid() -> (result: Vec<u64>)
    ensures clazel_der::decode::nats(result@) =~= super::spec::extended_key_usage_extension_oid()
{
    let arcs = vec![2u64, 5, 29, 37];
    proof {
        assert(clazel_der::decode::nats(arcs@) =~= super::spec::extended_key_usage_extension_oid()) by {
            reveal(clazel_der::decode::nats);
            reveal(super::spec::extended_key_usage_extension_oid);
        }
    }
    arcs
}

/// First occurrence of an extension OID; extension decoding guarantees uniqueness.
pub(crate) fn find_extension_index(input: &[extensions::Extension<'_>], oid: &[u64]) -> (result: Option<usize>)
    ensures match result {
        Some(index) => index < input.len()
            && clazel_der::decode::nats(input@[index as int].oid@) =~= clazel_der::decode::nats(oid@)
            && super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) == Some(index as int),
        None => super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) is None,
    }
{
    let mut index = 0;
    while index < input.len()
        invariant
            index <= input.len(),
            input@.len() == input.len(),
            super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0)
                == super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), index as int),
        decreases input.len() - index
    {
        let extension = input.get(index)?;
        if oid_arcs_equal(&extension.oid, oid) {
            proof {
                reveal_with_fuel(super::spec::find_extension_index, 1);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int]
                    == extensions::view_extension(&input@[index as int]));
                assert(extensions::view_extensions(input@)[index as int].oid =~= clazel_der::decode::nats(extension.oid@));
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), index as int) == Some(index as int));
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) == Some(index as int));
            }
            return Some(index);
        }
        proof {
            reveal_with_fuel(super::spec::find_extension_index, 1);
            reveal(extensions::view_extensions);
            reveal(extensions::view_extension);
            assert(extensions::view_extensions(input@)[index as int]
                == extensions::view_extension(&input@[index as int]));
            assert(!(extensions::view_extensions(input@)[index as int].oid =~= clazel_der::decode::nats(oid@)));
            assert(super::spec::find_extension_index(
                extensions::view_extensions(input@), clazel_der::decode::nats(oid@), index as int)
                == super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), (index + 1) as int));
        }
        index = index.saturating_add(1);
    }
    proof {
        reveal_with_fuel(super::spec::find_extension_index, 1);
        assert(super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), index as int) is None);
        assert(super::spec::find_extension_index(extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) is None);
    }
    None
}

/// View conversion for the optional BasicConstraints decoder.
pub open spec fn view_optional_basic_result(
    result: Option<Option<constraints::BasicConstraints<'_>>>,
) -> Option<Option<crate::constraints::spec::BasicConstraints>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(constraints::view_basic_constraints(&value))),
    }
}

pub(crate) fn parse_optional_basic_constraints<'b>(
    input: &[extensions::Extension<'b>], oid: &[u64],
) -> (result: Option<Option<constraints::BasicConstraints<'b>>>)
    requires clazel_der::decode::nats(oid@) =~= super::spec::basic_constraints_oid()
    ensures view_optional_basic_result(result)
        == super::spec::optional_basic_constraints(extensions::view_extensions(input@))
{
    match find_extension_index(input, oid) {
        None => {
            proof {
                reveal(super::spec::optional_basic_constraints);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) is None);
            }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = constraints::parse_basic_constraints(extension.value)?;
            proof {
                reveal(super::spec::optional_basic_constraints);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) == Some(index as int));
            }
            Some(Some(value))
        },
    }
}

/// View conversion for the optional KeyUsage decoder.
pub open spec fn view_optional_key_usage_result(
    result: Option<Option<constraints::KeyUsage<'_>>>,
) -> Option<Option<crate::constraints::spec::KeyUsage>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(constraints::view_key_usage(&value))),
    }
}

pub(crate) fn parse_optional_key_usage<'b>(
    input: &[extensions::Extension<'b>], oid: &[u64],
) -> (result: Option<Option<constraints::KeyUsage<'b>>>)
    requires clazel_der::decode::nats(oid@) =~= super::spec::key_usage_oid()
    ensures view_optional_key_usage_result(result)
        == super::spec::optional_key_usage(extensions::view_extensions(input@))
{
    match find_extension_index(input, oid) {
        None => {
            proof {
                reveal(super::spec::optional_key_usage);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) is None);
            }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = constraints::parse_key_usage(extension.value)?;
            proof {
                reveal(super::spec::optional_key_usage);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) == Some(index as int));
            }
            Some(Some(value))
        },
    }
}

/// View conversion for the optional ExtendedKeyUsage decoder.
pub open spec fn view_optional_eku_result(
    result: Option<Option<constraints::ExtendedKeyUsage>>,
) -> Option<Option<crate::constraints::spec::ExtendedKeyUsage>> {
    match result {
        None => None,
        Some(None) => Some(None),
        Some(Some(value)) => Some(Some(value@)),
    }
}

pub(crate) fn parse_optional_eku(
    input: &[extensions::Extension<'_>], oid: &[u64],
) -> (result: Option<Option<constraints::ExtendedKeyUsage>>)
    requires clazel_der::decode::nats(oid@) =~= super::spec::extended_key_usage_extension_oid()
    ensures view_optional_eku_result(result)
        == super::spec::optional_extended_key_usage(extensions::view_extensions(input@))
{
    match find_extension_index(input, oid) {
        None => {
            proof {
                reveal(super::spec::optional_extended_key_usage);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) is None);
            }
            Some(None)
        },
        Some(index) => {
            let extension = input.get(index)?;
            let value = constraints::parse_extended_key_usage(extension.value)?;
            proof {
                reveal(super::spec::optional_extended_key_usage);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int].value == extension.value@);
                assert(super::spec::find_extension_index(
                    extensions::view_extensions(input@), clazel_der::decode::nats(oid@), 0) == Some(index as int));
            }
            Some(Some(value))
        },
    }
}

/// Every critical extension is one of the four whose semantics this checker processes.
fn critical_extensions_supported(input: &[extensions::Extension<'_>]) -> (result: bool)
    ensures result == super::spec::supported_critical_extensions(extensions::view_extensions(input@), 0)
{
    let san_oid = san_oid();
    let basic_oid = basic_constraints_oid();
    let usage_oid = key_usage_oid();
    let eku_oid = extended_key_usage_oid();
    let mut index = 0;
    while index < input.len()
        invariant index <= input.len(), input@.len() == input.len(),
            clazel_der::decode::nats(san_oid@) =~= crate::extensions::spec::subject_alt_name_oid(),
            clazel_der::decode::nats(basic_oid@) =~= super::spec::basic_constraints_oid(),
            clazel_der::decode::nats(usage_oid@) =~= super::spec::key_usage_oid(),
            clazel_der::decode::nats(eku_oid@) =~= super::spec::extended_key_usage_extension_oid(),
            super::spec::supported_critical_extensions(extensions::view_extensions(input@), 0)
                == super::spec::supported_critical_extensions(extensions::view_extensions(input@), index as int),
        decreases input.len() - index
    {
        let extension = match input.get(index) { Some(value) => value, None => return false };
        let san_supported = oid_arcs_equal(&extension.oid, &san_oid);
        let basic_supported = oid_arcs_equal(&extension.oid, &basic_oid);
        let usage_supported = oid_arcs_equal(&extension.oid, &usage_oid);
        let eku_supported = oid_arcs_equal(&extension.oid, &eku_oid);
        let current_supported = !extension.critical || san_supported || basic_supported || usage_supported || eku_supported;
        proof {
            assert(san_supported == (clazel_der::decode::nats(extension.oid@) =~= clazel_der::decode::nats(san_oid@)));
            assert(basic_supported == (clazel_der::decode::nats(extension.oid@) =~= clazel_der::decode::nats(basic_oid@)));
            assert(usage_supported == (clazel_der::decode::nats(extension.oid@) =~= clazel_der::decode::nats(usage_oid@)));
            assert(eku_supported == (clazel_der::decode::nats(extension.oid@) =~= clazel_der::decode::nats(eku_oid@)));
            assert(clazel_der::decode::nats(san_oid@) =~= crate::extensions::spec::subject_alt_name_oid());
            assert(clazel_der::decode::nats(basic_oid@) =~= super::spec::basic_constraints_oid());
            assert(clazel_der::decode::nats(usage_oid@) =~= super::spec::key_usage_oid());
            assert(clazel_der::decode::nats(eku_oid@) =~= super::spec::extended_key_usage_extension_oid());
            assert(san_supported == (clazel_der::decode::nats(extension.oid@) =~= crate::extensions::spec::subject_alt_name_oid()));
            assert(basic_supported == (clazel_der::decode::nats(extension.oid@) =~= super::spec::basic_constraints_oid()));
            assert(usage_supported == (clazel_der::decode::nats(extension.oid@) =~= super::spec::key_usage_oid()));
            assert(eku_supported == (clazel_der::decode::nats(extension.oid@) =~= super::spec::extended_key_usage_extension_oid()));
        }
        if !current_supported {
            proof {
                reveal_with_fuel(super::spec::supported_critical_extensions, 1);
                reveal(extensions::view_extensions);
                reveal(extensions::view_extension);
                assert(extensions::view_extensions(input@)[index as int]
                    == extensions::view_extension(&input@[index as int]));
                assert(super::spec::supported_critical_extensions(
                    extensions::view_extensions(input@), index as int) == (current_supported
                    && super::spec::supported_critical_extensions(
                        extensions::view_extensions(input@), (index + 1) as int)));
                assert(!super::spec::supported_critical_extensions(
                    extensions::view_extensions(input@), index as int));
                assert(!super::spec::supported_critical_extensions(
                    extensions::view_extensions(input@), 0));
            }
            return false;
        }
        proof {
            reveal_with_fuel(super::spec::supported_critical_extensions, 1);
            reveal(extensions::view_extensions);
            reveal(extensions::view_extension);
            assert(extensions::view_extensions(input@)[index as int]
                == extensions::view_extension(&input@[index as int]));
            assert(super::spec::supported_critical_extensions(
                extensions::view_extensions(input@), index as int) == (current_supported
                && super::spec::supported_critical_extensions(
                    extensions::view_extensions(input@), (index + 1) as int)));
            assert(super::spec::supported_critical_extensions(
                extensions::view_extensions(input@), index as int)
                == super::spec::supported_critical_extensions(
                    extensions::view_extensions(input@), (index + 1) as int));
        }
        index = index.saturating_add(1);
    }
    true
}

fn only_supported_general_names(input: &[extensions::GeneralName<'_>]) -> (result: bool)
    ensures result == super::spec::only_supported_general_names(extensions::view_general_names(input@), 0)
{
    let mut index = 0;
    while index < input.len()
        invariant index <= input.len(), input@.len() == input.len(),
            super::spec::only_supported_general_names(extensions::view_general_names(input@), 0)
                == super::spec::only_supported_general_names(extensions::view_general_names(input@), index as int),
        decreases input.len() - index
    {
        let name = match input.get(index) { Some(value) => value, None => return false };
        let supported = !matches!(name, extensions::GeneralName::Other(_, _));
        if !supported {
            proof {
                reveal_with_fuel(super::spec::only_supported_general_names, 1);
                reveal(extensions::view_general_names);
                reveal(extensions::view_general_name);
                assert(extensions::view_general_names(input@)[index as int]
                    == extensions::view_general_name(&input@[index as int]));
                assert(!super::spec::only_supported_general_names(
                    extensions::view_general_names(input@), index as int));
                assert(!super::spec::only_supported_general_names(
                    extensions::view_general_names(input@), 0));
            }
            return false;
        }
        proof {
            reveal_with_fuel(super::spec::only_supported_general_names, 1);
            reveal(extensions::view_general_name);
            reveal(extensions::view_general_names);
            assert(extensions::view_general_names(input@)[index as int]
                == extensions::view_general_name(&input@[index as int]));
            assert(super::spec::only_supported_general_names(
                extensions::view_general_names(input@), index as int)
                == super::spec::only_supported_general_names(
                    extensions::view_general_names(input@), (index + 1) as int));
            assert(super::spec::only_supported_general_names(
                extensions::view_general_names(input@), index as int)
                == super::spec::only_supported_general_names(
                    extensions::view_general_names(input@), (index + 1) as int));
        }
        index = index.saturating_add(1);
    }
    true
}

fn general_name_matches_reference(name: &extensions::GeneralName<'_>, reference: ReferenceIdentity<'_>)
    -> (result: bool)
    ensures result == super::spec::general_name_matches_reference(
        extensions::view_general_name(name), crate::exec::view_reference_identity(&reference))
{
    match name {
        extensions::GeneralName::DnsName(value) => {
            let result = crate::exec::service_identity_matches_exec(
                reference, PresentedIdentity::Dns(value));
            proof {
                reveal(super::spec::general_name_matches_reference);
                reveal(extensions::view_general_name);
                reveal(crate::exec::view_reference_identity);
                reveal(crate::exec::view_presented_identity);
                reveal(crate::spec::service_identity_match);
                assert(result == crate::spec::service_identity_match(
                    crate::exec::view_reference_identity(&reference),
                    crate::spec::PresentedIdentity::Dns(value@)));
            }
            result
        },
        extensions::GeneralName::IpAddress(value) => {
            let result = crate::exec::service_identity_matches_exec(
                reference, PresentedIdentity::Ip(value));
            proof {
                reveal(super::spec::general_name_matches_reference);
                reveal(extensions::view_general_name);
                reveal(crate::exec::view_reference_identity);
                reveal(crate::exec::view_presented_identity);
                reveal(crate::spec::service_identity_match);
                assert(result == crate::spec::service_identity_match(
                    crate::exec::view_reference_identity(&reference),
                    crate::spec::PresentedIdentity::Ip(value@)));
            }
            result
        },
        extensions::GeneralName::Other(_, _) => {
            proof { reveal(super::spec::general_name_matches_reference); }
            false
        },
    }
}

fn san_matches_reference(names: &[extensions::GeneralName<'_>], reference: ReferenceIdentity<'_>)
    -> (result: bool)
    ensures result == super::spec::san_matches_reference(
        extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), 0)
{
    let mut index = 0;
    let mut found = false;
    while index < names.len()
        invariant index <= names.len(), names@.len() == names.len(),
            super::spec::san_matches_reference(
                extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), 0)
                == (found || super::spec::san_matches_reference(
                    extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), index as int)),
        decreases names.len() - index
    {
        let name = match names.get(index) { Some(value) => value, None => return false };
        let matched = general_name_matches_reference(name, reference);
        let ghost previous = found;
        found = found || matched;
        proof {
            reveal_with_fuel(super::spec::san_matches_reference, 1);
            assert(super::spec::san_matches_reference(
                extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), index as int)
                == (matched || super::spec::san_matches_reference(
                    extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), (index + 1) as int)));
            assert((previous || matched || super::spec::san_matches_reference(
                extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), (index + 1) as int))
                == (found || super::spec::san_matches_reference(
                    extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), (index + 1) as int)));
        }
        index = index.saturating_add(1);
    }
    proof {
        reveal_with_fuel(super::spec::san_matches_reference, 1);
        assert(super::spec::san_matches_reference(
            extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), index as int) == false);
        assert(super::spec::san_matches_reference(
            extensions::view_general_names(names@), crate::exec::view_reference_identity(&reference), 0) == found);
    }
    found
}

/// Check already decoded extensions against parsed TBS fields. This isolates
/// leaf policy refinement from the outer envelope/TBS parser composition.
fn check_parsed_leaf_extensions<'a, 'b>(
    input: &[extensions::Extension<'b>], tbs: &crate::tbs::exec::TbsCertificate<'_>,
    reference: ReferenceIdentity<'a>, now: &CertificateTime, policy: LeafPolicy,
) -> (result: Option<PartialLeafChecks<'a>>)
    ensures view_leaf_result(result) == super::spec::check_extensions(
        extensions::view_extensions(input@), crate::tbs::exec::view_tbs_certificate(tbs),
        crate::exec::view_reference_identity(&reference), now@, policy@)
{
    hide(crate::extensions::spec::parse_subject_alt_name);
    hide(crate::constraints::spec::parse_basic_constraints);
    hide(crate::constraints::spec::parse_key_usage);
    hide(crate::constraints::spec::parse_extended_key_usage);
    hide(crate::time::spec::validity_contains);
    hide(crate::spec::service_identity_match);
    hide(crate::spec::dns_match);
    hide(crate::spec::ip_match);
    hide(clazel_der::spec::read_tlv);
    hide(clazel_der::spec::read_oid);
    hide(clazel_der::spec::expect_sequence);
    hide(clazel_der::spec::read_boolean);
    hide(clazel_der::spec::read_octet_string);
    hide(clazel_der::spec::read_bit_string);
    hide(clazel_der::spec::expect_constructed);
    if !critical_extensions_supported(input) { return None; }
    let san_oid = san_oid();
    let san_index = find_extension_index(input, &san_oid)?;
    let san_extension = input.get(san_index)?;
    let san = extensions::parse_subject_alt_name(san_extension.value)?;
    proof {
        reveal(extensions::view_subject_alt_name);
        assert(extensions::view_subject_alt_name(&san).names
            == extensions::view_general_names(san.names@));
        reveal(extensions::view_subject_alt_name_result);
        reveal(extensions::view_extensions);
        reveal(extensions::view_extension);
        assert(extensions::view_extensions(input@)[san_index as int].value == san_extension.value@);
        assert(Some(extensions::view_subject_alt_name(&san))
            == crate::extensions::spec::parse_subject_alt_name(
                extensions::view_extensions(input@)[san_index as int].value));
    }
    if !only_supported_general_names(&san.names) || !san_matches_reference(&san.names, reference) { return None; }

    let basic_oid = basic_constraints_oid();
    let usage_oid = key_usage_oid();
    let eku_oid = extended_key_usage_oid();
    let basic_result = parse_optional_basic_constraints(input, &basic_oid);
    let basic = basic_result?;
    let usage_result = parse_optional_key_usage(input, &usage_oid);
    let usage = usage_result?;
    let digital_signature_allowed = match usage {
        Some(value) => constraints::key_usage_has(value, constraints::KeyUsageBit::DigitalSignature),
        None => true,
    };
    if !digital_signature_allowed {
        proof {
            reveal(super::spec::check_extensions);
            reveal(super::spec::optional_key_usage);
            reveal(constraints::view_key_usage);
            reveal(constraints::view_key_usage_bit);
            assert(view_optional_key_usage_result(usage_result)
                == super::spec::optional_key_usage(extensions::view_extensions(input@)));
            assert(usage.is_some());
            match usage {
                Some(value) => {
                    assert(view_optional_key_usage_result(usage_result)
                        == Some(Some(constraints::view_key_usage(&value))));
                    assert(digital_signature_allowed
                        == crate::constraints::spec::key_usage_has(
                            constraints::view_key_usage(&value),
                            crate::constraints::spec::KeyUsageBit::DigitalSignature));
                },
                None => {},
            }
        }
        return None;
    }
    if !constraints::basic_constraints_compatible(basic, usage) { return None; }
    if matches!(basic, Some(value) if value.ca) {
        proof {
            reveal(super::spec::check_extensions);
            reveal(super::spec::optional_basic_constraints);
            match basic {
                Some(value) => {
                    assert(view_optional_basic_result(basic_result)
                        == Some(Some(constraints::view_basic_constraints(&value))));
                    assert(value.ca);
                },
                None => assert(false),
            }
        }
        return None;
    }

    let eku = parse_optional_eku(input, &eku_oid)?;
    let extended_key_usage_present = eku.is_some();
    let server_auth_allowed = match eku {
        Some(value) => constraints::eku_allows_server_auth(value, policy.allow_any_extended_key_usage),
        None => true,
    };
    if !server_auth_allowed { return None; }

    let validity_option = crate::time::exec::make_validity(
        copy_time(&tbs.not_before), copy_time(&tbs.not_after));
    let validity = match validity_option {
        Some(value) => value,
        None => {
            proof {
                assert(crate::time::spec::make_validity(tbs.not_before@, tbs.not_after@) is None);
                crate::time::lemmas::lemma_make_validity_none_excludes_time(
                    tbs.not_before@, tbs.not_after@, now@);
            }
            return None;
        },
    };
    if !crate::time::exec::validity_contains(validity, copy_time(now)) { return None; }

    Some(PartialLeafChecks {
        reference,
        now: copy_time(now),
        not_before: copy_time(&tbs.not_before),
        not_after: copy_time(&tbs.not_after),
        identity_matched: true,
        valid_at_captured_time: true,
        server_auth_purpose_allowed: true,
        digital_signature_allowed: true,
        leaf_role_allowed: true,
        key_usage_present: usage.is_some(),
        extended_key_usage_present,
        basic_constraints_present: basic.is_some(),
        state: PartialValidationState::NeedsPathValidation,
    })
}

/// Compose certificate envelope, TBS, extensions, and partial server-leaf checks.
/// A result still requires signature, path, trust, revocation, and remaining policy validation.
pub fn check_leaf_certificate<'a>(
    input: &[u8], reference: ReferenceIdentity<'a>, now: &CertificateTime, policy: LeafPolicy,
) -> (result: Option<PartialLeafChecks<'a>>)
    ensures super::contract::check_leaf_certificate_ensures(
        input@, crate::exec::view_reference_identity(&reference), now@, policy@, view_leaf_result(result))
{
    hide(super::spec::check_leaf_certificate);
    hide(crate::certificate::spec::parse_certificate);
    hide(crate::tbs::spec::parse_tbs_certificate);
    hide(crate::extensions::spec::parse_extensions);
    let envelope = match crate::certificate::exec::parse_certificate(input) {
        Some(value) => value,
        None => {
            proof { reveal(super::spec::check_leaf_certificate); }
            return None;
        },
    };
    let tbs = match crate::tbs::exec::parse_tbs_certificate(envelope.tbs_certificate_der) {
        Some(value) => value,
        None => {
            proof { reveal(super::spec::check_leaf_certificate); }
            return None;
        },
    };
    let encoded_extensions = match tbs.extensions_sequence_der {
        Some(value) => value,
        None => {
            proof {
                reveal(super::spec::check_leaf_certificate);
                reveal(crate::tbs::exec::view_tbs_certificate);
                reveal(crate::certificate::contract::view_certificate_result);
                assert(Some(crate::certificate::exec::view_certificate_envelope(&envelope))
                    == crate::certificate::spec::parse_certificate(input@));
                assert(Some(crate::tbs::exec::view_tbs_certificate(&tbs))
                    == crate::tbs::spec::parse_tbs_certificate(envelope.tbs_certificate_der@));
            }
            return None;
        },
    };
    let parsed_extensions = match extensions::parse_extensions(encoded_extensions) {
        Some(value) => value,
        None => {
            proof { reveal(super::spec::check_leaf_certificate); }
            return None;
        },
    };
    let result = check_parsed_leaf_extensions(&parsed_extensions, &tbs, reference, now, policy);
    proof { reveal(super::spec::check_leaf_certificate); }
    result
}

} // verus!
