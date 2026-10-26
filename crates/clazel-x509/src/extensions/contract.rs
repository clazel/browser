//! Contracts for RFC 5280 extension and subjectAltName parsing.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The executable Extensions parser returns exactly the unique-OID records
/// modeled by `parse_extensions`.
pub open spec fn parse_extensions_ensures(
    input: Seq<u8>, output: Option<Seq<super::exec::Extension<'_>>>,
) -> bool {
    super::exec::view_extensions_result(output) == parse_extensions(input)
}

/// The executable SAN parser returns exactly the modeled nonempty GeneralNames
/// list, preserving unsupported alternatives as opaque TLVs.
pub open spec fn parse_subject_alt_name_ensures(
    input: Seq<u8>, output: Option<super::exec::SubjectAltName<'_>>,
) -> bool {
    super::exec::view_subject_alt_name_result(output) == parse_subject_alt_name(input)
}

} // verus!
