//! Independent expectations for additions, removals, surface changes and mixed reports.
#![allow(unexpected_cfgs)]
#[path = "../../judge-mixed/src/verified_classification.rs"]
mod policy;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::string::StringExecFns;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {
#[cfg_attr(not(verus_keep_ghost),test)]
fn both_document_sides_and_all_projected_changes_survive()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    let path=String::from_str("one");
    let mut old=std::collections::BTreeMap::<String,u8>::new();
    let mut new=std::collections::BTreeMap::<String,u8>::new();
    old.insert(path.clone(),5);new.insert(path.clone(),9);
    let (left,right)=policy::document_pair(&old,&new,&path);
    expect(matches!(left,Some(x) if *x==5) && matches!(right,Some(x) if *x==9));
    let candidate=|flag:&u8| -> (out:Option<u8>) ensures out==(if *flag==1 {None} else {Some(*flag)}), {
        if *flag==1 {None} else {Some(*flag)}
    };
    let keys=[3u8,1u8,8u8];let changes=policy::changed_items(&keys,candidate);
    proof {
        let items=choose|items:Seq<Option<u8>>| #[trigger] policy::projected(keys@,3,candidate,items) && changes@==policy::some_items(items);
        assert(candidate.ensures((&keys@[0],),items[0]));assert(candidate.ensures((&keys@[1],),items[1]));
        assert(candidate.ensures((&keys@[2],),items[2]));
        assert(items =~= seq![Some(3u8),None,Some(8u8)]);
        reveal_with_fuel(policy::some_items,4);
    }
    expect(changes.len()==2 && changes[0]==3 && changes[1]==8);
}

#[cfg(verus_keep_ghost)]
fn one_rule_receives_the_old_and_new_documents_and_preserves_the_other_path<T>(
    path:&String, other:&String, pointer:&String, on:&String, first:&T, second:&T,
)
    requires path@!=other@,
{
    let rules=vec![(other.clone(),pointer.clone(),on.clone()),(path.clone(),pointer.clone(),on.clone())];
    let evaluate=|a:Option<&T>,b:Option<&T>,p:&String,m:&String,left:bool,right:bool| -> (out:Result<Vec<u8>,u8>)
        ensures (a==Some(first) && b==Some(second) && p==pointer && m==on && left && !right)
            ==> (out matches Ok(v) && v@==seq![4u8,9u8]),
        { Ok(vec![4u8,9u8]) };
    let err=|_p:&String| ->(x:u8) ensures x==3, {3u8};
    let output=policy::fields_for_path(&rules,path,Some(first),Some(second),true,false,true,evaluate,err);
    proof { if let Ok(values)=output {
        let batches=choose|batches:Seq<Vec<u8>>| #[trigger] policy::visited_patterns(rules@,2,path,Some(first),Some(second),true,false,true,evaluate,batches)
            && values@==policy::flattened(batches);
        assert(policy::field_batch(rules@[0],path,Some(first),Some(second),true,false,true,evaluate,batches[0]));
        assert(policy::field_batch(rules@[1],path,Some(first),Some(second),true,false,true,evaluate,batches[1]));
        assert(batches[0].len()==0 && batches[1]@==seq![4u8,9u8]);
        reveal_with_fuel(policy::flattened,3);
        assert(values@ =~= seq![4u8,9u8]);
    } else if let Err(e)=output {
        let (i,batches)=choose|i:int,batches:Seq<Vec<u8>>| 0<=i<2 && rules@[i].0@==path@
            && #[trigger] policy::visited_patterns(rules@,i,path,Some(first),Some(second),true,false,true,evaluate,batches)
            && evaluate.ensures((Some(first),Some(second),&rules@[i].1,&rules@[i].2,true,false),Err::<Vec<u8>,u8>(e));
        assert(i==1);assert(false);
    } }
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn typed_classification_and_report_keep_every_distinct_source_field() {
    let path=String::from_str("p");let old=String::from_str("old");let new=String::from_str("new");
    let change=policy::semantic_change("/v","add-modify-delete",policy::Difference {key:&path,before:Some(&3u8),after:Some(&8u8)});
    expect(<&str>::exec_eq(change.identity.as_str(),path.as_str()) && matches!(change.before,Some(x) if *x==3) && matches!(change.after,Some(x) if *x==8));
    expect(<&str>::exec_eq(change.pattern,"/v") && <&str>::exec_eq(change.on,"add-modify-delete"));
    let row=policy::surface_row(&path,Some(&old),Some(&new),policy::Surfaces{whole_rule:false,product:true},vec![4u8,9u8]);
    let r=row.rule.unwrap();let p=row.product.unwrap();
    expect(!r.whole_file && r.semantic.len()==2 && r.semantic[0]==4 && r.semantic[1]==9);
    expect(<&str>::exec_eq(r.surfaces.path.as_str(),path.as_str()) && <&str>::exec_eq(p.path.as_str(),path.as_str()));
    expect(<&str>::exec_eq(r.surfaces.before_surface.unwrap().as_str(),old.as_str()) && <&str>::exec_eq(r.surfaces.after_surface.unwrap().as_str(),new.as_str()));
    expect(<&str>::exec_eq(p.before_surface.unwrap().as_str(),old.as_str()) && <&str>::exec_eq(p.after_surface.unwrap().as_str(),new.as_str()));
    let out=policy::classification(vec![&path],vec![1u8],vec![&new],vec![2u8]);
    expect(out.mixed && !out.requires_acknowledgement && <&str>::exec_eq(out.rule_paths[0].as_str(),path.as_str()) && <&str>::exec_eq(out.product_paths[0].as_str(),new.as_str()));
    expect(out.changes[0]==1 && out.product_changes[0]==2);
    let costed=policy::costed(out);
    expect(<&str>::exec_eq(costed.schema,"chrono-rule-changes/v2"));
    let bound=policy::bind_report(costed,10u8);
    expect(bound.binding==10 && bound.changes.classification.changes[0]==1);
}


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

pub struct PairCursor<'a> { pub items:&'a [(&'a String,&'a u8)], pub at:usize }

impl<'a> policy::ObjectCursor<'a,u8> for PairCursor<'a> {
    open spec fn remaining(&self)->Seq<(&'a String,&'a u8)> {
        if self.at<=self.items.len() {self.items@.skip(self.at as int)} else {Seq::empty()}
    }
    fn next_pair(&mut self)->(entry:Option<(&'a String,&'a u8)>) {
        if self.at>=self.items.len() {return None;}
        let item=self.items[self.at];self.at=self.at+1;
        assert(self.items@.skip(self.at as int) =~= old(self).items@.skip(old(self).at as int).drop_first());
        Some(item)
    }
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn literal_object_members_skip_non_matches_and_keep_the_recursive_result() {
    use policy::ObjectCursor;
    let a=String::from_str("a");let b=String::from_str("b");let x=1u8;let y=2u8;
    let entries=[(&a,&x),(&b,&y)];
    let visit=|_k:&String,v:&u8,_s:u8| -> (r:Result<u8,u8>) ensures r==Ok::<u8,u8>(*v), {Ok(*v)};
    let cursor=PairCursor{items:&entries,at:0};
    let ghost source=cursor.remaining();
    let chosen=policy::object_members(cursor,Some("a"),0u8,visit);
    proof {
        reveal_strlit("a");reveal_strlit("b");reveal_strlit("*");
        assert("a"@[0]=='a' && "b"@[0]=='b' && "*"@[0]=='*');
        assert(source.len()==2);
        assert(source[0]==entries@[0] && source[1]==entries@[1]);
        if let Ok(result)=chosen {
            let trace=choose|states:Seq<u8>| #[trigger] policy::folded(source,2,Some("a"),visit,states)
                && states[0]==0 && states.last()==result;
            assert(policy::folded(source,2,Some("a"),visit,trace));
            assert(policy::accepts_object(Some("a"),source[0].0));
            assert(!policy::accepts_object(Some("a"),source[1].0));
            assert(visit.ensures((source[0].0,source[0].1,trace[0]),Ok::<u8,u8>(trace[1])));
            assert(trace[2]==trace[1]);
        }
    }
    expect(matches!(chosen,Ok(1)));
}

#[cfg(verus_keep_ghost)]
fn every_returned_pattern_has_a_nonempty_declaration_at_an_input_endpoint(a:&[policy::Rule],b:&[policy::Rule])
    requires vstd::laws_cmp::obeys_cmp::<policy::Pattern>(),
{
    let result=policy::patterns(a,b);
    assert forall|p:policy::Pattern| #[trigger] result@.contains(p)==(
        (exists|i:int,j:int| 0<=i<a.len() && 0<=j<a@[i].pointers.len() &&
            (#[trigger] a@[i].pointers[j])==p.1 && a@[i].path==p.0 && a@[i].on==p.2)
        || (exists|i:int,j:int| 0<=i<b.len() && 0<=j<b@[i].pointers.len() &&
            (#[trigger] b@[i].pointers[j])==p.1 && b@[i].path==p.0 && b@[i].on==p.2)
    ) by {}
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn blob_presence_is_checked_on_each_side() {
    expect(policy::documents_available(false,false,false,false));
    expect(policy::documents_available(true,true,false,false));
    expect(!policy::documents_available(true,false,true,true));
    expect(!policy::documents_available(false,true,true,false));
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn normalized_arrays_keep_positions_or_exact_row_keys() {
    let vals=vec![3u8,5u8];
    match policy::array_form(None::<Vec<u64>>,vals) {
        policy::ArrayForm::Array((tag,v))=>expect(<&str>::exec_eq(tag,"array") && v.len()==2 && v[0]==3 && v[1]==5),
        _=>expect(false),
    }
    let name=8u64;
    let rows=vec![name];
    proof {assert(rows@.no_duplicates());}
    match policy::array_form(Some(rows),vec![4u8]) {
        policy::ArrayForm::Rows((tag,map))=>{
            expect(<&str>::exec_eq(tag,"rows"));expect(matches!(map.get(&name),Some(x) if *x==4));
        },
        _=>expect(false),
    }
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn each_child_is_visited_in_order_and_only_the_first_error_is_returned() {
    let first_two=|i:usize| -> (r:Result<usize,u8>) ensures r==(if i<2 {Ok::<usize,u8>(i)} else if i==2 {Err::<usize,u8>(7)} else {Err::<usize,u8>(9)}), {
        if i<2 {Ok(i)} else if i==2 {Err(7)} else {Err(9)}
    };
    match policy::children(2,first_two) {Ok(v)=>expect(v.len()==2 && v[0]==0 && v[1]==1),_=>expect(false)}
    let r=policy::children(4,first_two);
    proof {
        if let Err(e)=r {
            let (i,prefix)=choose|i:usize,prefix:Seq<usize>| i<4
                && first_two.ensures((i,),Err::<usize,u8>(e))
                && #[trigger] policy::processed(first_two,prefix,i as int);
            if i>2 {assert(first_two.ensures((2usize,),Ok::<usize,u8>(prefix[2])));}
        } else if let Ok(v)=&r {assert(first_two.ensures((2usize,),Ok::<usize,u8>(v@[2])));}
    }
    expect(matches!(r,Err(7)));
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn report_wraps_original_classification_and_both_sets_of_references() {
    let message=|| -> (v:String) ensures v@=="text"@, {String::from_str("text")};
    let r=[1u8]; let p=[2u8]; let input=7u8;
    let output=policy::report_envelope(&r,&p,&input,"HOST",message);
    expect(<&str>::exec_eq(output.status,"warn") && *output.outputs.rule_changes==7 && output.findings.len()==1);
    let f=&output.findings[0];expect(<&str>::exec_eq(f.code,"HOST") && <&str>::exec_eq(f.level,"warning"));
    expect(<&str>::exec_eq(f.message.as_str(),"text") && <&str>::exec_eq(f.causes[0],"/outputs/rule_changes"));
    expect(f.delta_refs.len()==2 && *f.delta_refs[0]==1 && *f.delta_refs[1]==2);
    let empty:[u8;0]=[];let output=policy::report_envelope(&r,&empty,&input,"unused",message);
    expect(<&str>::exec_eq(output.status,"pass") && output.findings.len()==0 && *output.outputs.rule_changes==7);
}

#[cfg_attr(not(verus_keep_ghost),test)]
fn stable_identity_union_and_original_values_survive_comparison() {
    let mut old=std::collections::BTreeMap::<u64,u8>::new();
    let mut new=std::collections::BTreeMap::<u64,u8>::new();
    old.insert(1,7); old.insert(2,8); new.insert(2,9); new.insert(3,7);
    let key1=1u64; let key2=2u64; let key3=3u64;
    let keys=policy::selection_keys(&old,&new);
    proof {
        assert(keys@ =~= set![&key1,&key2,&key3]);
        assert(set![&key1,&key2,&key3].len()==3);
    }
    expect(keys.len()==3 && keys.contains(&&key1) && keys.contains(&&key2) && keys.contains(&&key3));
    let eq=|a:&u8,b:&u8| -> (same:bool) ensures same == (*a==*b), { *a==*b };
    let a=8u8;let b=9u8;
    match policy::difference(&key2,Some(&a),Some(&b),"add-modify-delete",eq) {
        Some(d)=>{ expect(*d.key==2); expect(matches!(d.before, Some(x) if *x==8));
                   expect(matches!(d.after,Some(x) if *x==9)); },
        None=>expect(false),
    }
    expect(policy::difference(&key2,Some(&a),Some(&a),"add-modify-delete",eq).is_none());
    expect(policy::difference(&key3,None,Some(&b),"modify-delete-existing",eq).is_none());
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
