//! Independent expectations for additions, removals, surface changes and mixed reports.
#![allow(unexpected_cfgs)]
#[path = "../../judge-mixed/src/verified_classification.rs"]
mod policy;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {

#[cfg_attr(not(verus_keep_ghost), test)]
fn semantic_identity_precedence_and_duplicate_selections() {
    use policy::IdentityField::{Invalid, Missing, Text};
    use policy::RowIdentity::{Id, Path, Retirement};
    proof { reveal_strlit(""); reveal_strlit("x"); reveal_strlit("job");
        assert("x"@.len() > 0); assert("job"@.len() > 0); assert(""@.len() == 0); }
    expect(matches!(policy::row_identity(Text("x"),Invalid,Missing,false),Ok(Id(_))));
    expect(matches!(policy::row_identity(Missing,Text("x"),Missing,false),Ok(Path(_))));
    expect(matches!(policy::row_identity(Text("x"),Missing,Text("job"),true),Ok(Retirement(_,_))));
    expect(matches!(policy::row_identity(Invalid,Text("x"),Text("job"),false),Err(_)));
    expect(matches!(policy::row_identity(Missing,Text("x"),Missing,true),Err(_)));
    expect(matches!(policy::row_identity(Missing,Text("x"),Text("job"),true),Err(_)));
    let mut rows=std::collections::BTreeSet::<u64>::new();
    expect(policy::new_row(&mut rows,4));
    expect(!policy::new_row(&mut rows,4));
    let mut selections=std::collections::BTreeMap::<u64,u64>::new();
    expect(policy::record_selection(&mut selections,4,1).is_ok());
    expect(policy::record_selection(&mut selections,4,2).is_err());
}

fn expect(value: bool) requires value {
    if !value { panic!(); }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn surface_changes_preserve_both_endpoints_and_only_named_semantics() {
    proof {
        reveal_strlit("judge-policy"); reveal_strlit("judge-implementation");
        reveal_strlit("test"); reveal_strlit("product"); reveal_strlit("documentation");
        assert("judge-implementation"@.len() != "product"@.len());
        assert("judge-implementation"@.len() != "test"@.len());
        assert("product"@.len() != "judge-policy"@.len());
        assert("documentation"@.len() != "product"@.len());
        assert("documentation"@.len() != "test"@.len());
        assert("documentation"@.len() != "judge-policy"@.len());
        assert("documentation"@.len() != "judge-implementation"@.len());
    }
    let moved = policy::endpoints(Some("judge-policy"), Some("test")).unwrap();
    expect(moved.whole_rule && moved.product && moved.changes_rule(false));
    let deleted = policy::endpoints(Some("judge-implementation"), None).unwrap();
    expect(deleted.whole_rule && !deleted.product);
    let added = policy::endpoints(None, Some("product")).unwrap();
    expect(!added.whole_rule && added.product);
    expect(!added.changes_rule(false) && added.changes_rule(true));
    let docs = policy::endpoints(Some("documentation"), None).unwrap();
    expect(!docs.product && !docs.changes_rule(false) && docs.changes_rule(true));
    expect(policy::endpoints(None, None).is_none());
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn mixed_warning_requires_both_a_rule_and_a_product() {
    expect(!policy::mixed(0,0));
    expect(!policy::mixed(0,3));
    expect(!policy::mixed(2,0));
    expect(policy::mixed(2,3));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn costs_require_both_endpoint_maps_and_the_first_missing_side_in_delta_order() {
    proof { reveal_strlit("chrono-costs/v1"); }
    expect(policy::cost_report_shape(Some("chrono-costs/v1"), true, true));
    expect(!policy::cost_report_shape(Some("chrono-costs/v1"), true, false));
    expect(!policy::cost_report_shape(None, true, true));
    let presence = |i: usize| -> (r: (bool, bool))
        ensures r == (i != 2, i == 0),
    { (i != 2, i == 0) };
    expect(matches!(policy::first_missing_cost(0, presence), None));
    expect(matches!(policy::first_missing_cost(1, presence), None));
    let gap = policy::first_missing_cost(3, presence);
    match gap {
        Some((i, policy::CostSide::After)) => expect(i == 1),
        _ => { proof {
            assert(presence.ensures((1usize,), (true, true)) == false);
        } expect(false); }
    }
    let both = |_i: usize| -> (r: (bool, bool)) ensures r == (false, false), { (false, false) };
    let missing = policy::first_missing_cost(1, both);
    match missing {
        Some((i, policy::CostSide::Before)) => expect(i == 0),
        None => { assert(!both.ensures((0usize,), (true, true))); expect(false); }
        Some((i, policy::CostSide::After)) => {
            assert(!both.ensures((i,), (true, false)));
            expect(false);
        }
    }
}

}
