//! Independent expectations for additions, removals, surface changes and mixed reports.
#![allow(unexpected_cfgs)]
#[path = "../../judge-mixed/src/verified_classification.rs"]
mod policy;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {

#[cfg_attr(not(verus_keep_ghost), test)]
fn semantic_change_modes_compare_existing_fields_and_distinguish_additions() {
    let all = "add-modify-delete";
    let existing = "modify-delete-existing";
    proof {
        reveal_strlit("add-modify-delete");
        reveal_strlit("modify-delete-existing");
        assert("add-modify-delete"@.len() != "modify-delete-existing"@.len());
    }
    expect(policy::field_changed(all, false, true, true));
    expect(!policy::field_changed(existing, false, true, false));
    expect(policy::field_changed(existing, true, true, false));
    expect(policy::field_changed(all, true, true, false));
    expect(!policy::field_changed(all, true, true, true));
    expect(!policy::field_changed(existing, true, true, true));
    expect(policy::field_changed(all, true, false, true));
    expect(policy::field_changed(existing, true, false, false));
    expect(!policy::field_changed(existing, false, false, false));
    expect(!policy::field_changed(all, false, false, false));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn document_fields_and_blob_sides_determine_exact_distinct_paths() {
    let mut named = std::collections::BTreeSet::<u64>::new();
    let mut before = std::collections::BTreeSet::new();
    let mut after = std::collections::BTreeSet::new();
    policy::register_document(&mut named, 9, 0);
    policy::register_document(&mut named, 1, 1);
    policy::register_document(&mut named, 1, 0);
    policy::register_document(&mut named, 1, 2);
    policy::register_document(&mut named, 2, 1);
    policy::register_document(&mut named, 3, 1);
    policy::register_document(&mut named, 4, 1);
    policy::select_document(&named, &mut before, &mut after, 1, true, false);
    policy::select_document(&named, &mut before, &mut after, 2, false, true);
    policy::select_document(&named, &mut before, &mut after, 3, true, true);
    policy::select_document(&named, &mut before, &mut after, 3, true, true);
    policy::select_document(&named, &mut before, &mut after, 4, false, false);
    policy::select_document(&named, &mut before, &mut after, 9, true, true);
    expect(before.len() == 2 && before.contains(&1) && before.contains(&3));
    expect(after.len() == 2 && after.contains(&2) && after.contains(&3));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn agreement_requires_a_predecessor_and_every_comparison() {
    let agrees = |_i: usize| -> (b: bool) ensures b, { true };
    let except_second = |i: usize| -> (b: bool) ensures b == (i != 1), { i != 1 };
    expect(!policy::matching_predecessors(0, agrees));
    expect(policy::matching_predecessors(2, agrees));
    expect(policy::matching_predecessors(1, except_second));
    let bad = policy::matching_predecessors(2, except_second);
    proof {
        if bad { assert(except_second.ensures((1usize,), true)); }
    }
    expect(!bad);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn plan_admits_the_first_cost_only_after_impact_delta_costs_and_binding_agree() {
    let yes = || -> (b: bool) ensures b, { true };
    let no = || -> (b: bool) ensures !b, { false };
    let equal = |_i: usize| -> (b: bool) ensures b, { true };
    let disagree = |_i: usize| -> (b: bool) ensures !b, { false };
    let empty: [u8; 0] = [];
    let costs = [19u8, 19u8];

    match policy::plan_predecessors(0, equal, yes, &empty, equal, no) {
        Err(e) => expect(<&str>::exec_eq(e, "E_IMPACT: missing or conflicting bound FILEMAP output")),
        Ok(_) => expect(false),
    }
    match policy::plan_predecessors(1, equal, no, &empty, equal, no) {
        Err(e) => expect(<&str>::exec_eq(e, "E_IMPACT: missing or conflicting bound FILEMAP output")),
        Ok(_) => expect(false),
    }
    match policy::plan_predecessors(1, equal, yes, &empty, equal, no) {
        Err(e) => expect(<&str>::exec_eq(e, "E_COST_INPUT: missing predecessor costs")),
        Ok(_) => expect(false),
    }
    match policy::plan_predecessors(1, equal, yes, &costs, disagree, yes) {
        Err(e) => expect(<&str>::exec_eq(e, "E_COST_INPUT: conflicting costs or mismatched endpoint/context binding")),
        Ok(_) => { assert(!disagree.ensures((0usize,),true)); expect(false); }
    }
    match policy::plan_predecessors(1, equal, yes, &costs, equal, no) {
        Err(e) => expect(<&str>::exec_eq(e, "E_COST_INPUT: conflicting costs or mismatched endpoint/context binding")),
        Ok(_) => expect(false),
    }
    match policy::plan_predecessors(2, equal, yes, &costs, equal, yes) {
        Ok(first) => expect(*first == 19),
        Err(_) => expect(false),
    }
}

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
fn report_preserves_rule_then_product_references_and_status() {
    let rules = [1u8, 2u8];
    let products = [2u8, 3u8];
    let (pass, none) = policy::report_finding(&rules, &[]);
    expect(pass == "pass" && none.is_none());
    let (pass, none) = policy::report_finding(&[], &products);
    expect(pass == "pass" && none.is_none());
    let (warn, refs) = policy::report_finding(&rules, &products);
    expect(warn == "warn" && refs.is_some());
    let refs = refs.unwrap();
    expect(refs.len() == 4);
    expect(*refs[0] == 1 && *refs[1] == 2 && *refs[2] == 2 && *refs[3] == 3);
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
