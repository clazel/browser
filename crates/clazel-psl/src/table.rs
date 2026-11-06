//! The spec view of the generated tables: [`psl_rules`] is the Public
//! Suffix List `cargo xtask tables` generated (`xtask/src/psl.rs` says how
//! `public_suffix_list.dat` becomes the tables), as the [`Rule`]s of
//! [`super::spec`].

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A label row's characters, as a string.
pub open spec fn label_row_text(row: super::tables::LabelRow) -> Seq<u32> {
    Seq::new(row.len as nat, |c: int| super::data::psl_chars_at(row.start as int + c) as u32)
}

/// A rule row's rule: its labels are rows `first .. first + count` of the
/// labels table.
pub open spec fn rule_of_row(row: super::tables::RuleRow) -> super::spec::Rule {
    super::spec::Rule {
        labels: Seq::new(row.count as nat, |j: int| label_row_text(super::data::psl_labels_at(row.first as int + j))),
        exception: row.exception,
    }
}

/// Rule `i` of the list.
pub open spec fn table_rule(i: int) -> super::spec::Rule {
    rule_of_row(super::data::psl_rules_at(i))
}

/// The Public Suffix List, rule by rule, in file order.
pub open spec fn psl_rules() -> Seq<super::spec::Rule> {
    Seq::new(super::data::PSL_RULES_LEN as nat, |i: int| table_rule(i))
}

/// The list's ICANN section, its first rows: the rules without the private
/// section's. A domain under a suffix only the private section lists has the
/// public suffix these rules give, as if that entry were not there.
pub open spec fn psl_icann_rules() -> Seq<super::spec::Rule> {
    psl_rules().take(super::data::PSL_ICANN_RULES_LEN as int)
}

} // verus!
