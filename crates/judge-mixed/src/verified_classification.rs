//! Classification of one changed path from its two registered endpoint surfaces.
#![allow(unexpected_cfgs)]
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

pub struct Surfaces {
    pub whole_rule: bool,
    pub product: bool,
}

pub open spec fn rule_label(s: Seq<char>) -> bool {
    s == "judge-policy"@ || s == "judge-implementation"@
}

pub open spec fn product_label(s: Seq<char>) -> bool {
    s == "product"@ || s == "test"@
}

pub open spec fn endpoint_rule(s: Option<&str>) -> bool {
    match s { Some(label) => rule_label(label@), None => false }
}

pub open spec fn endpoint_product(s: Option<&str>) -> bool {
    match s { Some(label) => product_label(label@), None => false }
}

fn one(surface: Option<&str>) -> (out: Surfaces)
    ensures out.whole_rule == endpoint_rule(surface), out.product == endpoint_product(surface),
{
    match surface {
        None => Surfaces { whole_rule: false, product: false },
        Some(label) => Surfaces {
            whole_rule: <&str>::exec_eq(label, "judge-policy")
                || <&str>::exec_eq(label, "judge-implementation"),
            product: <&str>::exec_eq(label, "product") || <&str>::exec_eq(label, "test"),
        },
    }
}

pub fn endpoints(before: Option<&str>, after: Option<&str>) -> (out: Option<Surfaces>)
    ensures
        out.is_none() == (before.is_none() && after.is_none()),
        out matches Some(s) ==> s.whole_rule == (endpoint_rule(before) || endpoint_rule(after))
            && s.product == (endpoint_product(before) || endpoint_product(after)),
{
    if before.is_none() && after.is_none() { return None; }
    let previous = one(before);
    let current = one(after);
    Some(Surfaces {
        whole_rule: previous.whole_rule || current.whole_rule,
        product: previous.product || current.product,
    })
}

impl Surfaces {
    pub fn changes_rule(&self, has_changed_field: bool) -> (changed: bool)
        ensures changed == (self.whole_rule || has_changed_field),
    { self.whole_rule || has_changed_field }
}

pub fn mixed(rule_count: usize, product_count: usize) -> (warn: bool)
    ensures warn == (rule_count > 0 && product_count > 0),
{ rule_count > 0 && product_count > 0 }

}
