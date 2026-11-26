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

#[cfg(verus_keep_ghost)]
fn plan_checks_whole_endpoint_before_schema_or_deserialization(
    a: &std::collections::BTreeMap<String,String>, ar: &[policy::Rule],
    b: &std::collections::BTreeMap<String,String>, br: &[policy::Rule],
)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    let fail=|| -> (r:Result<Vec<policy::Delta>,u8>) ensures r==Err::<Vec<policy::Delta>,u8>(17), {Err(17)};
    let bad = policy::plan_delta(a,ar,b,br,None,fail);
    let ghost good_a=policy::valid_surfaces(a@) && policy::valid_modes(ar@);
    let ghost good_b=policy::valid_surfaces(b@) && policy::valid_modes(br@);
    proof {
        if good_a && good_b {
            assert(bad matches Err(policy::PlanFailure::Contract(e)) && e@=="E_IMPACT: unsupported schema"@);
        }
        if !policy::valid_surfaces(a@) || (good_a && !policy::valid_surfaces(b@)) {
            assert(bad matches Err(policy::PlanFailure::Contract(e)) && e@=="E_SURFACE_REFERENCE: unknown surface"@);
        }
        if policy::valid_surfaces(a@) && !policy::valid_modes(ar@) {
            assert(bad matches Err(policy::PlanFailure::Contract(e)) && e@=="E_SEMANTIC_INPUT: unknown semantic change mode"@);
        }
    }
    let parsed=policy::plan_delta(a,ar,b,br,Some("chrono-filemap-impact/v6"),fail);
    proof { if good_a && good_b {assert(parsed matches Err(policy::PlanFailure::Decode(17u8)));} }
}

#[cfg(verus_keep_ghost)]
fn delta_compares_every_side_and_preserves_order(a:&[policy::Delta],b:&[policy::Delta]) {
    let same=policy::same_delta(a,b);
    proof {
        assert(same == (a.len()==b.len() && forall|i:int| 0<=i<a.len() ==> {
            let left=#[trigger] a@[i]; let right=#[trigger] b@[i];
            &&& left.kind@ == right.kind@ && left.path@ == right.path@
            &&& policy::same_text(left.old_blob,right.old_blob) && policy::same_text(left.new_blob,right.new_blob)
            &&& policy::same_text(left.old_mode,right.old_mode) && policy::same_text(left.new_mode,right.new_mode)
        }));
    }
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn costs_and_binding_are_distinct_plan_fields() {
    let documents=policy::DocumentPaths{base:std::collections::BTreeSet::new(),candidate:std::collections::BTreeSet::new()};
    let binding=5u8; let cost=9u8;
    let out=policy::bound_plan(documents,&binding,&cost);
    expect(*out.context.binding==5 && *out.context.costs==9);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn version_and_preparation_require_a_single_argument() {
    proof { reveal_strlit("--version"); reveal_strlit("prepare-classification-v1"); }
    expect(matches!(policy::route(None,0),policy::Route::Pipeline));
    expect(matches!(policy::route(None,2),policy::Route::Pipeline));
    expect(matches!(policy::route(Some("--version"),0),policy::Route::Version));
    expect(matches!(policy::route(Some("--version"),1),policy::Route::Pipeline));
    expect(matches!(policy::route(Some("prepare-classification-v1"),0),policy::Route::Prepare));
    expect(matches!(policy::route(Some("prepare-classification-v1"),1),policy::Route::Pipeline));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn native_programs_receive_the_exact_prefix_and_original_arguments() {
    let executable = 42u8;
    let forwarded = [0xffu8,0,2];
    let prepare = policy::invocation(true,&executable,"version",&forwarded);
    expect(<&str>::exec_eq(prepare.program,"chrono-judge-registration"));
    expect(prepare.forwarded.len()==0 && prepare.prefix.len()==2);
    use policy::Argument::{Text,Executable};
    expect(matches!(&prepare.prefix[0],Text(text) if <&str>::exec_eq(text,"classification-inputs-v1")));
    expect(matches!(&prepare.prefix[1],Executable(path) if **path == 42));
    let pipeline=policy::invocation(false,&executable,"version",&forwarded);
    expect(<&str>::exec_eq(pipeline.program,"chrono-harness"));
    expect(pipeline.prefix.len()==7 && pipeline.forwarded.len()==3);
    expect(pipeline.forwarded[0]==255 && pipeline.forwarded[1]==0 && pipeline.forwarded[2]==2);
    expect(matches!(&pipeline.prefix[0],Text(t) if <&str>::exec_eq(t,"judge-pipeline")));
    expect(matches!(&pipeline.prefix[1],Text(t) if <&str>::exec_eq(t,"chrono-judge-mixed")));
    expect(matches!(&pipeline.prefix[2],Text(t) if <&str>::exec_eq(t,"version")));
    expect(matches!(&pipeline.prefix[3],Executable(path) if **path==42));
    expect(matches!(&pipeline.prefix[4],Text(t) if <&str>::exec_eq(t,"prepare-classification-v1")));
    expect(matches!(&pipeline.prefix[5],Executable(path) if **path==42));
    expect(matches!(&pipeline.prefix[6],Text(t) if <&str>::exec_eq(t,"report-v1")));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn process_location_and_returned_exec_preserve_the_actual_error() {
    let no_path=|| -> (r:Result<u8,u8>) ensures r==Err::<u8,u8>(19), {Err(19)};
    let path=|| -> (r:Result<u8,u8>) ensures r==Ok::<u8,u8>(47), {Ok(47)};
    let exec=|p:u8| -> (r:(&'static str,u8)) ensures r.0@=="target"@ && r.1==p, {("target",p)};
    let (s,n,e)=policy::delegation_failure(no_path,exec);
    expect(s==2 && <&str>::exec_eq(n,"chrono-judge-mixed") && e==19);
    let (s,n,e)=policy::delegation_failure(path,exec);
    expect(s==2 && <&str>::exec_eq(n,"target") && e==47);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn document_io_returns_the_first_diagnostic_and_requires_a_successful_flush() {
    let failed_read = || -> (r: Result<Vec<u8>,u8>) ensures r == Err::<Vec<u8>,u8>(4), { Err(4) };
    let empty = || -> (r: Result<Vec<u8>,u8>) ensures r matches Ok(v) && v.len() == 0, { Ok(Vec::new()) };
    let decode_error = |_bytes: Vec<u8>| -> (r: Result<u8,u8>) ensures r == Err::<u8,u8>(5), { Err(5) };
    let too_large = || -> (e: u8) ensures e == 6, { 6 };
    expect(matches!(policy::decode_input(failed_read,decode_error,too_large), Err(4)));
    expect(matches!(policy::decode_input(empty,decode_error,too_large), Err(5)));

    let write = |v:u8| -> (r:Result<u8,u8>) ensures r == (if v == 1 { Ok::<u8,u8>(9) } else { Err::<u8,u8>(7) }), {
        if v == 1 { Ok(9) } else { Err(7) }
    };
    let flush = |writer:u8| -> (r:Result<(),u8>) ensures r == (if writer == 9 { Err::<(),u8>(8) } else { Ok::<(),u8>(()) }), {
        if writer == 9 { Err(8) } else { Ok(()) }
    };
    let (status, error) = policy::data_exit(policy::on_success(policy::on_success(Err(4),write),flush));
    expect(status == 2 && matches!(error,Some(4)));
    let (status, error) = policy::data_exit(policy::on_success(policy::on_success(Ok(0),write),flush));
    expect(status == 2 && matches!(error,Some(7)));
    let (status, error) = policy::data_exit(policy::on_success(policy::on_success(Ok(1),write),flush));
    expect(status == 2 && matches!(error,Some(8)));
    let (status, error) = policy::data_exit(policy::on_success(Ok(0),flush));
    expect(status == 0 && error.is_none());
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn document_command_is_selected_only_without_extra_arguments() {
    proof {
        reveal_strlit("document-paths-v1"); reveal_strlit("classify-v1");
        reveal_strlit("report-v1"); reveal_strlit("plan-classification-v1");
    }
    expect(matches!(policy::data_command("document-paths-v1", 0), Some(Ok(policy::DataCommand::Documents))));
    match policy::data_command("document-paths-v1", 1) {
        Some(Err(label)) => expect(<&str>::exec_eq(label, "document-paths-v1")),
        _ => expect(false),
    }
}

/// Field values taken from the actual two request arrays must name every path
/// with a declaration and every blob on that side, including repeated paths.
#[cfg(verus_keep_ghost)]
fn complete_document_paths_have_no_missing_or_extra_members<'a>(
    base: &'a [policy::Rule], candidate: &'a [policy::Rule], delta: &'a [policy::Delta],
)
    requires vstd::laws_cmp::obeys_cmp::<&String>(),
{
    let paths = policy::required_paths(base, candidate, delta);
    assert forall|path: &String| {
        let declared = (exists|i: int| 0 <= i < base.len() && #[trigger] base@[i].path == *path && base@[i].pointers.len() != 0)
            || (exists|i: int| 0 <= i < candidate.len() && #[trigger] candidate@[i].path == *path && candidate@[i].pointers.len() != 0);
        let before = exists|i: int| 0 <= i < delta.len() && #[trigger] delta@[i].path == *path && delta@[i].old_blob.is_some();
        let after = exists|i: int| 0 <= i < delta.len() && #[trigger] delta@[i].path == *path && delta@[i].new_blob.is_some();
        &&& #[trigger] paths.base@.contains(path) == (declared && before)
        &&& #[trigger] paths.candidate@.contains(path) == (declared && after)
    } by {}
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn one_json_value_can_fill_the_entire_input_limit() {
    expect(policy::admits_input(67_108_864));
    expect(!policy::admits_input(67_108_865));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn pointer_components_and_physical_keys_use_the_two_literal_escapes() {
    let text = "/~1";
    proof {
        reveal_strlit("/~1");
        assert(text@ =~= seq!['/', '~', '1']);
        assert(policy::scanned(text@, 1).unwrap().current == Seq::<char>::empty());
        assert(policy::scanned(text@, 2).unwrap().escaped);
        let s = policy::scanned(text@, 3).unwrap();
        assert(s.current =~= seq!['/']);
        assert(s.parts == Seq::<Seq<char>>::empty() && !s.escaped);
    }
    match policy::decode_pointer(text) {
        Ok(parts) => {
            proof {
                assert(text@.len() == 3);
                let s = policy::scanned(text@, 3).unwrap();
                assert(policy::component_views(parts@) == s.parts.push(s.current));
                assert(policy::component_views(parts@).len() == parts@.len());
                assert(s.parts.len() == 0);
                assert(policy::component_views(parts@)[0] == parts@[0]@);
            }
            expect(parts.len() == 1);
            expect(parts[0].len() == 1 && parts[0][0] == '/');
        },
        Err(_) => expect(false),
    }
    proof {
        reveal_strlit("a"); reveal_strlit("~/");
        assert("a"@ =~= seq!['a']);
        assert("~/"@ =~= seq!['~', '/']);
        assert(policy::escaped_prefix("~/"@, 0) == Seq::<char>::empty());
        assert(policy::escaped_prefix("~/"@, 1) =~= seq!['~', '0']);
        assert(policy::escaped_prefix("~/"@, 2) =~= seq!['~', '0', '~', '1']);
    }
    let path = policy::child_pointer("a", "~/");
    expect(path.len() == 6);
    expect(path[0] == 'a' && path[1] == '/' && path[2] == '~' && path[3] == '0'
        && path[4] == '~' && path[5] == '1');
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn pointer_errors_keep_the_prefix_and_escape_failures_distinct() {
    proof {
        reveal_strlit(""); reveal_strlit("x"); reveal_strlit("/~"); reveal_strlit("/~2/a");
        reveal_with_fuel(policy::scanned, 8);
    }
    expect(matches!(policy::decode_pointer(""), Err(policy::PointerError::Prefix)));
    expect(matches!(policy::decode_pointer("x"), Err(policy::PointerError::Prefix)));
    expect(matches!(policy::decode_pointer("/~"), Err(policy::PointerError::Escape)));
    expect(matches!(policy::decode_pointer("/~2/a"), Err(policy::PointerError::Escape)));
}


#[cfg_attr(not(verus_keep_ghost), test)]
fn child_names_are_literal_except_for_the_single_wildcard() {
    proof {
        reveal_strlit("*"); reveal_strlit("00"); reveal_strlit("0"); reveal_strlit("");
        assert("*"@.len() == 1 && "00"@.len() == 2 && "0"@.len() == 1 && ""@.len() == 0);
    }
    expect(policy::matches_child("*", ""));
    expect(policy::matches_child("", ""));
    expect(policy::matches_child("规则", "规则"));
    expect(policy::matches_child("0", "0"));
    expect(!policy::matches_child("00", "0"));
    expect(!policy::matches_child("", "0"));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn any_named_row_requires_identity_for_the_entire_array() {
    let missing = |_i: usize| -> (b: bool) ensures !b, { false };
    let last = |i: usize| -> (b: bool) ensures b == (i == 2), { i == 2 };
    expect(!policy::requires_row_identity(0, last));
    expect(!policy::requires_row_identity(3, missing));
    let required = policy::requires_row_identity(3, last);
    proof { if !required { assert(last.ensures((2usize,), false)); } }
    expect(required);
}

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
    let empty: [u8; 0] = [];
    let rules = [1u8, 2u8];
    let products = [2u8, 3u8];
    let (pass, none) = policy::report_finding(&rules, &empty);
    expect(<&str>::exec_eq(pass, "pass") && none.is_none());
    let (pass, none) = policy::report_finding(&empty, &products);
    expect(<&str>::exec_eq(pass, "pass") && none.is_none());
    let (warn, refs) = policy::report_finding(&rules, &products);
    expect(<&str>::exec_eq(warn, "warn") && refs.is_some());
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
