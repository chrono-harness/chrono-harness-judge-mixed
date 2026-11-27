//! Classification of one changed path from its two registered endpoint surfaces.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
#[path = "classification.rs"]
pub mod classification;
#[cfg(verus_keep_ghost)]
#[path = "native.rs"]
pub mod native;
#[cfg(verus_keep_ghost)]
pub use native::{PlanFailure, plan_delta};
#[cfg(verus_keep_ghost)]
#[path = "main.rs"]
pub mod cli;
#[cfg(verus_keep_ghost)]
#[path = "lib.rs"]
pub mod cost_input;
#[cfg(verus_keep_ghost)]
#[path = "semantic.rs"]
pub mod semantic;
use std::collections::{BTreeMap, BTreeSet};
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::string::StringExecFns;

verus! {

/// A binding needs at least one producer. Stop at the first different result.
pub fn matching_predecessors<F: Fn(usize) -> bool>(count: usize, agrees: F) -> (ok: bool)
    requires forall|i: usize| i < count ==> agrees.requires((i,)),
    ensures
        ok ==> count > 0 && forall|i: usize| i < count ==> agrees.ensures((i,), true),
        !ok ==> count == 0 || exists|i: usize| i < count && agrees.ensures((i,), false),
{
    if count == 0 { return false; }
    let mut i = 0;
    while i < count
        invariant i <= count,
            forall|j: usize| j < count ==> agrees.requires((j,)),
            forall|j: usize| j < i ==> agrees.ensures((j,), true),
        decreases count - i,
    {
        if !agrees(i) { return false; }
        i += 1;
    }
    true
}

/// The first admitted cost is the exact borrowed predecessor passed into the report.
pub fn plan_predecessors<'a, T, I, D, C, B>(
    impact_count: usize, impact_matches: I, delta_matches: D,
    costs: &'a [T], cost_matches: C, binding_matches: B,
) -> (result: Result<&'a T, &'static str>)
    where I: Fn(usize) -> bool, D: Fn() -> bool, C: Fn(usize) -> bool, B: Fn() -> bool,
    requires
        forall|i: usize| i < impact_count ==> impact_matches.requires((i,)),
        forall|i: usize| i < costs.len() ==> cost_matches.requires((i,)),
        delta_matches.requires(()), costs.len() > 0 ==> binding_matches.requires(()),
    ensures match result {
        Ok(value) => {
            &&& impact_count > 0 && costs.len() > 0 && *value == costs@[0]
            &&& delta_matches.ensures((),true) && binding_matches.ensures((),true)
            &&& forall|i:usize| i < impact_count ==> impact_matches.ensures((i,),true)
            &&& forall|i:usize| i < costs.len() ==> cost_matches.ensures((i,),true)
        }
        Err(e) => ({
            &&& e@ == "E_IMPACT: missing or conflicting bound FILEMAP output"@
            &&& impact_count == 0 || delta_matches.ensures((), false)
                || exists|i:usize| i < impact_count && impact_matches.ensures((i,),false)
        } || {
            &&& impact_count > 0 && delta_matches.ensures((), true)
            &&& forall|i:usize| i < impact_count ==> impact_matches.ensures((i,),true)
            &&& if costs.len() == 0 { e@ == "E_COST_INPUT: missing predecessor costs"@ }
                else { e@ == "E_COST_INPUT: conflicting costs or mismatched endpoint/context binding"@
                    && (binding_matches.ensures((),false)
                        || exists|i:usize| i < costs.len() && cost_matches.ensures((i,),false)) }
        }),
    },
{
    if !matching_predecessors(impact_count, impact_matches) || !delta_matches() {
        return Err("E_IMPACT: missing or conflicting bound FILEMAP output");
    }
    if costs.len() == 0 { return Err("E_COST_INPUT: missing predecessor costs"); }
    if !matching_predecessors(costs.len(), cost_matches) || !binding_matches() {
        return Err("E_COST_INPUT: conflicting costs or mismatched endpoint/context binding");
    }
    Ok(&costs[0])
}

/// A present non-string and a missing key have different precedence in JSON rows.
pub enum IdentityField<'a> { Missing, Invalid, Text(&'a str) }

pub enum RowIdentity<'a> { Id(&'a str), Path(&'a str), Retirement(&'a str, &'a str) }

/// Views the ordered list of decoded segments, including empty segments.
pub open spec fn component_views(parts: Seq<Vec<char>>) -> Seq<Seq<char>> {
    parts.map(|_i: int, part: Vec<char>| part@)
}

pub ghost struct PointerScan {
    pub parts: Seq<Seq<char>>,
    pub current: Seq<char>,
    pub escaped: bool,
}

/// State after the leading slash and the next characters, up to end (exclusive).
pub open spec fn scanned(source: Seq<char>, end: int) -> Option<PointerScan>
    decreases end,
{
    if end <= 1 {
        Some(PointerScan { parts: Seq::empty(), current: Seq::empty(), escaped: false })
    } else {
        match scanned(source, end - 1) {
            None => None,
            Some(s) => {
                let c = source[end - 1];
                if s.escaped {
                    if c == '0' || c == '1' {
                        Some(PointerScan { parts: s.parts, current: s.current.push(
                            if c == '0' { '~' } else { '/' }), escaped: false })
                    } else { None }
                } else if c == '/' {
                    Some(PointerScan { parts: s.parts.push(s.current), current: Seq::empty(), escaped: false })
                } else if c == '~' {
                    Some(PointerScan { parts: s.parts, current: s.current, escaped: true })
                } else {
                    Some(PointerScan { parts: s.parts, current: s.current.push(c), escaped: false })
                }
            }
        }
    }
}

proof fn invalid_suffix(source: Seq<char>, bad: int, end: int)
    requires 1 < bad <= end <= source.len(), scanned(source, bad).is_none(),
    ensures scanned(source, end).is_none(),
    decreases end - bad,
{
    if end > bad { invalid_suffix(source, bad, end - 1); }
}

pub enum PointerError { Prefix, Escape }

pub fn decode_pointer(pointer: &str) -> (out: Result<Vec<Vec<char>>, PointerError>)
    ensures match out {
        Err(PointerError::Prefix) => pointer@.len() == 0 || pointer@[0] != '/',
        Err(PointerError::Escape) => pointer@.len() > 0 && pointer@[0] == '/' &&
            match scanned(pointer@, pointer@.len() as int) { None => true, Some(s) => s.escaped },
        Ok(parts) => pointer@.len() > 0 && pointer@[0] == '/' &&
            match scanned(pointer@, pointer@.len() as int) {
                None => false,
                Some(s) => !s.escaped && component_views(parts@) == s.parts.push(s.current),
            },
    },
{
    let mut chars = pointer.chars();
    if chars.next() != Some('/') { return Err(PointerError::Prefix); }
    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    let mut escaped = false;
    loop
        invariant pointer@.len() > 0, pointer@[0] == '/', chars@.1 == pointer@, 1 <= chars@.0 <= pointer@.len(),
            scanned(pointer@, chars@.0).is_some(),
            ({ let s = scanned(pointer@, chars@.0).unwrap();
               s.parts == component_views(parts@) && s.current == current@ && s.escaped == escaped }),
        decreases pointer@.len() - chars@.0,
    {
        let Some(c) = chars.next() else {
            if escaped { return Err(PointerError::Escape); }
            let ghost prior = parts@;
            parts.push(current);
            assert(component_views(parts@) =~= component_views(prior).push(current@));
            return Ok(parts);
        };
        if escaped {
            let decoded = match c {
                '0' => '~',
                '1' => '/',
                _ => {
                    proof { invalid_suffix(pointer@, chars@.0, pointer@.len() as int); }
                    return Err(PointerError::Escape);
                }
            };
            current.push(decoded);
            escaped = false;
        } else if c == '/' {
            let ghost prior = parts@;
            parts.push(current);
            assert(component_views(parts@) =~= component_views(prior).push(current@));
            current = Vec::new();
        } else if c == '~' {
            escaped = true;
        } else {
            current.push(c);
        }
    }
}

pub open spec fn escaped_prefix(key: Seq<char>, end: int) -> Seq<char>
    decreases end,
{
    if end <= 0 { Seq::empty() } else {
        let prefix = escaped_prefix(key, end - 1);
        match key[end - 1] {
            '~' => prefix.push('~').push('0'),
            '/' => prefix.push('~').push('1'),
            c => prefix.push(c),
        }
    }
}

/// The parent is already encoded. Only the appended component is escaped.
pub fn child_pointer(parent: &str, key: &str) -> (out: Vec<char>)
    ensures out@ == parent@.push('/') + escaped_prefix(key@, key@.len() as int),
{
    let mut out = Vec::new();
    let mut parents = parent.chars();
    loop
        invariant parents@.1 == parent@, 0 <= parents@.0 <= parent@.len(),
            out@ == parent@.take(parents@.0),
        ensures out@ == parent@,
        decreases parent@.len() - parents@.0,
    {
        let Some(c) = parents.next() else { assert(out@ =~= parent@); break; };
        out.push(c);
        assert(out@ =~= parent@.take(parents@.0));
    }
    assert(out@ =~= parent@);
    out.push('/');
    let mut chars = key.chars();
    loop
        invariant chars@.1 == key@, 0 <= chars@.0 <= key@.len(),
            out@ == parent@.push('/') + escaped_prefix(key@, chars@.0),
        decreases key@.len() - chars@.0,
    {
        let Some(c) = chars.next() else { return out; };
        match c {
            '~' => { out.push('~'); out.push('0'); }
            '/' => { out.push('~'); out.push('1'); }
            c => out.push(c),
        }
        assert(out@ =~= parent@.push('/') + escaped_prefix(key@, chars@.0));
    }
}

/// A decoded pointer component selects every child for "*" and otherwise only the exact key.
pub fn matches_child(token: &str, key: &str) -> (selected: bool)
    ensures selected == (token@ == "*"@ || token@ == key@),
{
    <&str>::exec_eq(token, "*") || <&str>::exec_eq(token, key)
}

/// A single row with an id or path switches the whole array to stable row identities.
pub fn requires_row_identity<F: Fn(usize) -> bool>(count: usize, named: F) -> (required: bool)
    requires forall|i: usize| i < count ==> named.requires((i,)),
    ensures
        required ==> exists|i: usize| i < count && named.ensures((i,), true),
        !required ==> forall|i: usize| i < count ==> named.ensures((i,), false),
{
    let mut i = 0;
    while i < count
        invariant
            i <= count,
            forall|j: usize| j < count ==> named.requires((j,)),
            forall|j: usize| j < i ==> named.ensures((j,), false),
        decreases count - i,
    {
        if named(i) { return true; }
        i += 1;
    }
    false
}

pub open spec fn nonempty(field: IdentityField) -> Option<Seq<char>> {
    match field { IdentityField::Text(s) if s@ != ""@ => Some(s@), _ => None }
}

pub fn retirement_rows(workflow: bool, pointer: &str) -> (typed: bool)
    ensures typed == (workflow && pointer@ == "/retirements"@),
{
    workflow && <&str>::exec_eq(pointer, "/retirements")
}

/// Ordinary rows prefer a present id. Workflow retirements also require a kind.
pub fn row_identity<'a>(id: IdentityField<'a>, path: IdentityField<'a>, kind: IdentityField<'a>, retirement: bool)
    -> (result: Result<RowIdentity<'a>, &'static str>)
    ensures ({
        let has_id = !(id is Missing);
        let value = if has_id { nonempty(id) } else { nonempty(path) };
        match result {
            Ok(RowIdentity::Id(s)) => !retirement && has_id && value == Some(s@),
            Ok(RowIdentity::Path(s)) => !retirement && !has_id && value == Some(s@),
            Ok(RowIdentity::Retirement(k,s)) => retirement && has_id && nonempty(kind) == Some(k@) && value == Some(s@),
            Err(e) => if value.is_none() { e@ == "E_SEMANTIC_IDENTITY: mixed or invalid path/id rows"@ }
                else if retirement && nonempty(kind).is_none() { e@ == "E_SEMANTIC_IDENTITY: invalid retirement kind"@ }
                else { retirement && !has_id && e@ == "E_SEMANTIC_IDENTITY: retirement requires id"@ },
        }
    }),
{
    let has_id = !matches!(id, IdentityField::Missing);
    let value = match if has_id { id } else { path } {
        IdentityField::Text(s) if !<&str>::exec_eq(s,"") => s,
        _ => return Err("E_SEMANTIC_IDENTITY: mixed or invalid path/id rows"),
    };
    if retirement {
        let k = match kind {
            IdentityField::Text(s) if !<&str>::exec_eq(s,"") => s,
            _ => return Err("E_SEMANTIC_IDENTITY: invalid retirement kind"),
        };
        if !has_id { return Err("E_SEMANTIC_IDENTITY: retirement requires id"); }
        Ok(RowIdentity::Retirement(k,value))
    } else if has_id { Ok(RowIdentity::Id(value)) } else { Ok(RowIdentity::Path(value)) }
}

/// Compare a field at the same stable identity in the two documents.
/// An absent field differs from a present field holding JSON null.
pub fn field_changed(
    mode: &str, before: bool, after: bool, equal_values: bool,
) -> (changed: bool)
    ensures changed == selected_change(mode@,before,after,equal_values),
{
    if !before { return after && !<&str>::exec_eq(mode, "modify-delete-existing"); }
    !after || !equal_values
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(deny_unknown_fields))]
pub struct Rule {
    pub path: String,
    pub pointers: Vec<String>,
    pub on: String,
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize, serde::Deserialize, PartialEq, Eq))]
#[cfg_attr(not(verus_keep_ghost), serde(deny_unknown_fields))]
pub struct Delta {
    pub kind: String,
    pub path: String,
    pub old_blob: Option<String>,
    pub new_blob: Option<String>,
    pub old_mode: Option<String>,
    pub new_mode: Option<String>,
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct DocumentPaths<'a> {
    pub base: BTreeSet<&'a String>,
    pub candidate: BTreeSet<&'a String>,
}

pub open spec fn named_by(rules: Seq<Rule>, end: int, path: &String) -> bool {
    exists|i: int| 0 <= i < end && #[trigger] rules[i].path == *path && rules[i].pointers.len() > 0
}

pub open spec fn present_on(delta: Seq<Delta>, end: int, path: &String, base: bool) -> bool {
    exists|i: int| 0 <= i < end && #[trigger] delta[i].path == *path
        && (if base { delta[i].old_blob.is_some() } else { delta[i].new_blob.is_some() })
}

fn register_rules<'a>(named: &mut BTreeSet<&'a String>, rules: &'a [Rule])
    requires vstd::laws_cmp::obeys_cmp::<&String>(),
    ensures forall|p: &String| #[trigger] named@.contains(p)
        == (old(named)@.contains(p) || named_by(rules@, rules.len() as int, p)),
{
    let mut i = 0;
    while i < rules.len()
        invariant i <= rules.len(), vstd::laws_cmp::obeys_cmp::<&String>(),
            forall|p: &String| #[trigger] named@.contains(p)
                == (old(named)@.contains(p) || named_by(rules@, i as int, p)),
        decreases rules.len() - i,
    {
        let rule = &rules[i];
        register_document(named, &rule.path, rule.pointers.len());
        assert forall|p: &String| #[trigger] named@.contains(p)
            == (old(named)@.contains(p) || named_by(rules@, i+1, p)) by {
            if p == &rule.path && rule.pointers.len() > 0 { assert(rules@[i as int].path == *p); }
        }
        i += 1;
    }
}

pub fn required_paths<'a>(base: &'a [Rule], candidate: &'a [Rule], delta: &'a [Delta])
    -> (paths: DocumentPaths<'a>)
    requires vstd::laws_cmp::obeys_cmp::<&String>(),
    ensures
        forall|p: &String| #[trigger] paths.base@.contains(p)
            == ((named_by(base@, base.len() as int, p) || named_by(candidate@, candidate.len() as int, p))
                && present_on(delta@, delta.len() as int, p, true)),
        forall|p: &String| #[trigger] paths.candidate@.contains(p)
            == ((named_by(base@, base.len() as int, p) || named_by(candidate@, candidate.len() as int, p))
                && present_on(delta@, delta.len() as int, p, false)),
{
    let mut named = BTreeSet::new();
    register_rules(&mut named, base);
    register_rules(&mut named, candidate);
    let mut before = BTreeSet::new();
    let mut after = BTreeSet::new();
    let mut i = 0;
    while i < delta.len()
        invariant i <= delta.len(), vstd::laws_cmp::obeys_cmp::<&String>(),
            forall|p: &String| #[trigger] named@.contains(p)
                == (named_by(base@, base.len() as int, p) || named_by(candidate@, candidate.len() as int, p)),
            forall|p: &String| #[trigger] before@.contains(p) == (named@.contains(p) && present_on(delta@, i as int, p, true)),
            forall|p: &String| #[trigger] after@.contains(p) == (named@.contains(p) && present_on(delta@, i as int, p, false)),
        decreases delta.len() - i,
    {
        let row = &delta[i];
        select_document(&named, &mut before, &mut after, &row.path, row.old_blob.is_some(), row.new_blob.is_some());
        assert forall|p: &String| #[trigger] before@.contains(p) == (named@.contains(p) && present_on(delta@, i+1, p, true)) by {
            if p == &row.path && row.old_blob.is_some() { assert(delta@[i as int].path == *p); }
        }
        assert forall|p: &String| #[trigger] after@.contains(p) == (named@.contains(p) && present_on(delta@, i+1, p, false)) by {
            if p == &row.path && row.new_blob.is_some() { assert(delta@[i as int].path == *p); }
        }
        i += 1;
    }
    DocumentPaths { base: before, candidate: after }
}

pub enum DataCommand { Classify, Documents, Plan, Report }

pub fn data_command(name: &str, extra: usize) -> (selected: Option<Result<DataCommand, &str>>)
    ensures
        selected.is_some() == (name@ == "classify-v1"@ || name@ == "document-paths-v1"@
            || name@ == "plan-classification-v1"@ || name@ == "report-v1"@),
        selected matches Some(Err(command)) ==> extra > 0 && command@ == name@,
        selected matches Some(Ok(command)) ==> extra == 0 && match command {
            DataCommand::Classify => name@ == "classify-v1"@,
            DataCommand::Documents => name@ == "document-paths-v1"@,
            DataCommand::Plan => name@ == "plan-classification-v1"@,
            DataCommand::Report => name@ == "report-v1"@,
        },
{
    let command = if <&str>::exec_eq(name, "classify-v1") {
        DataCommand::Classify
    } else if <&str>::exec_eq(name, "document-paths-v1") {
        DataCommand::Documents
    } else if <&str>::exec_eq(name, "plan-classification-v1") {
        DataCommand::Plan
    } else if <&str>::exec_eq(name, "report-v1") {
        DataCommand::Report
    } else {
        return None;
    };
    Some(if extra == 0 { Ok(command) } else { Err(name) })
}

pub enum Route<'a> {
    Version,
    Data(Result<DataCommand, &'a str>),
    Prepare,
    Pipeline,
}

pub open spec fn is_data(s: Seq<char>) -> bool {
    s == "document-paths-v1"@ || s == "classify-v1"@ || s == "plan-classification-v1"@ || s == "report-v1"@
}

pub fn route(operation: Option<&str>, extra: usize) -> (selected: Route<'_>)
    ensures match operation {
        None => selected is Pipeline,
        Some(s) => {
            &&& (selected is Version) == (extra == 0 && s@ == "--version"@)
            &&& (selected is Prepare) == (extra == 0 && s@ == "prepare-classification-v1"@)
            &&& (selected is Data) == is_data(s@)
            &&& (selected is Pipeline) == (!is_data(s@) && (extra > 0 || (s@ != "--version"@ && s@ != "prepare-classification-v1"@)))
            &&& selected matches Route::Data(Err(label)) ==> extra > 0 && label@ == s@
            &&& selected matches Route::Data(Ok(command)) ==> extra == 0 && match command {
                DataCommand::Classify => s@ == "classify-v1"@,
                DataCommand::Documents => s@ == "document-paths-v1"@,
                DataCommand::Plan => s@ == "plan-classification-v1"@,
                DataCommand::Report => s@ == "report-v1"@,
            }
        },
    },
{
    proof {
        reveal_strlit("--version"); reveal_strlit("prepare-classification-v1");
        reveal_strlit("document-paths-v1"); reveal_strlit("classify-v1");
        reveal_strlit("plan-classification-v1"); reveal_strlit("report-v1");
    }
    let name = match operation { None => return Route::Pipeline, Some(name) => name };
    if extra == 0 && <&str>::exec_eq(name,"--version") {
        assert(name@[0] == '-');
        assert("document-paths-v1"@[0] == 'd' && "classify-v1"@[0] == 'c'
            && "plan-classification-v1"@[0] == 'p' && "report-v1"@[0] == 'r');
        assert(!is_data(name@));
        assert(name@ != "prepare-classification-v1"@);
        return Route::Version;
    }
    if let Some(selected) = data_command(name,extra) { return Route::Data(selected); }
    if extra == 0 && <&str>::exec_eq(name,"prepare-classification-v1") { Route::Prepare }
    else { Route::Pipeline }
}

pub enum Argument<'a,A> { Text(&'a str), Executable(&'a A) }

pub struct Invocation<'a,A,T> {
    pub program: &'static str,
    pub prefix: Vec<Argument<'a,A>>,
    pub forwarded: &'a [T],
}

pub fn invocation<'a,A,T>(prepare: bool, executable: &'a A, version: &'a str, arguments: &'a [T])
    -> (result: Invocation<'a,A,T>)
    ensures
        prepare ==> result.program@ == "chrono-judge-registration"@ && result.forwarded.len() == 0
            && result.prefix@ == seq![Argument::<A>::Text("classification-inputs-v1"), Argument::Executable(executable)],
        !prepare ==> result.program@ == "chrono-harness"@ && result.forwarded@ == arguments@
            && result.prefix@ == seq![Argument::<A>::Text("judge-pipeline"), Argument::Text("chrono-judge-mixed"),
                Argument::Text(version), Argument::Executable(executable), Argument::Text("prepare-classification-v1"),
                Argument::Executable(executable), Argument::Text("report-v1")],
{
    if prepare {
        Invocation { program: "chrono-judge-registration",
            prefix: vec![Argument::Text("classification-inputs-v1"), Argument::Executable(executable)], forwarded: &[] }
    } else {
        Invocation { program: "chrono-harness", prefix: vec![Argument::Text("judge-pipeline"),
            Argument::Text("chrono-judge-mixed"), Argument::Text(version), Argument::Executable(executable),
            Argument::Text("prepare-classification-v1"), Argument::Executable(executable), Argument::Text("report-v1")],
            forwarded: arguments }
    }
}

/// Successful exec replaces this process. Both callbacks can supply actual
/// platform errors; only a returned exec can produce the destination's error.
pub fn delegation_failure<P,E,L,X>(locate:L, execute:X)
    -> (failure:(u8,&'static str,E))
    where L:FnOnce()->Result<P,E>, X:FnOnce(P)->(&'static str,E),
    requires locate.requires(()), forall|p:P| execute.requires((p,)),
    ensures failure.0 == 2 && (
        (locate.ensures((),Err::<P,E>(failure.2)) && failure.1@ == "chrono-judge-mixed"@)
        || exists|p:P| #[trigger] locate.ensures((),Ok::<P,E>(p))
            && execute.ensures((p,), (failure.1,failure.2))
    ),
{
    let path = match locate() { Ok(path) => path, Err(e) => return (2,"chrono-judge-mixed",e) };
    let (program,error) = execute(path);
    (2,program,error)
}

pub const INPUT_LIMIT: usize = 64 * 1024 * 1024;

pub fn admits_input(bytes: usize) -> (allowed: bool)
    ensures allowed == (bytes <= 67_108_864),
{ bytes <= INPUT_LIMIT }

/// A bounded read returns its own error first. Decode receives exactly the
/// bytes observed by the reader and can run only for an admitted length.
pub fn decode_input<T,E,R,D,L>(read: R, decode: D, too_large: L) -> (out: Result<T,E>)
    where R: FnOnce() -> Result<Vec<u8>,E>, D: FnOnce(Vec<u8>) -> Result<T,E>, L: FnOnce() -> E,
    requires read.requires(()), too_large.requires(()),
        forall|bytes: Vec<u8>| bytes.len() <= INPUT_LIMIT ==> decode.requires((bytes,)),
    ensures
        (exists|error:E| #[trigger] read.ensures((), Err(error)) && out == Err::<T,E>(error))
        || (exists|bytes:Vec<u8>| #[trigger] read.ensures((),Ok(bytes))
            && if bytes.len() <= INPUT_LIMIT { decode.ensures((bytes,),out) }
                else { exists|e:E| #[trigger] too_large.ensures((),e) && out == Err::<T,E>(e) }),
{
    let bytes = match read() { Ok(bytes) => bytes, Err(e) => return Err(e) };
    if !admits_input(bytes.len()) { return Err(too_large()); }
    decode(bytes)
}

/// Pass the original error through, or give the next stage the exact value.
pub fn on_success<T,U,E,F>(result: Result<T,E>, next: F) -> (out: Result<U,E>)
    where F: FnOnce(T) -> Result<U,E>,
    requires forall|v:T| next.requires((v,)),
    ensures match result {
        Err(e) => out == Err::<U,E>(e),
        Ok(v) => next.ensures((v,),out),
    },
{
    match result { Err(e) => Err(e), Ok(v) => next(v) }
}

pub fn data_exit<E>(result: Result<(),E>) -> (out: (u8,Option<E>))
    ensures match result { Ok(()) => out == (0u8,None::<E>), Err(e) => out == (2u8,Some(e)) },
{
    match result { Ok(()) => (0,None), Err(e) => (2,Some(e)) }
}

pub open spec fn known_surface(value: Seq<char>) -> bool {
    value == "product"@ || value == "test"@ || value == "documentation"@ || value == "membership"@
        || value == "instruction-policy"@ || value == "judge-policy"@ || value == "judge-implementation"@
}

fn admits_surface(s: &str) -> (admitted: bool)
    ensures admitted == known_surface(s@),
{
    <&str>::exec_eq(s,"product") || <&str>::exec_eq(s,"test") || <&str>::exec_eq(s,"documentation")
        || <&str>::exec_eq(s,"membership") || <&str>::exec_eq(s,"instruction-policy")
        || <&str>::exec_eq(s,"judge-policy") || <&str>::exec_eq(s,"judge-implementation")
}

pub open spec fn known_mode(mode: Seq<char>) -> bool {
    mode == "add-modify-delete"@ || mode == "modify-delete-existing"@
}

pub open spec fn valid_surfaces(surfaces: Map<String,String>) -> bool {
    forall|v:String| #[trigger] surfaces.values().contains(v) ==> known_surface(v@)
}

pub open spec fn valid_modes(rules: Seq<Rule>) -> bool {
    forall|i:int| 0 <= i < rules.len() ==> known_mode(#[trigger] rules[i].on@)
}

pub fn validate_endpoint(surfaces: &BTreeMap<String,String>, rules: &[Rule]) -> (r:Result<(),&'static str>)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures match r {
        Ok(()) => valid_surfaces(surfaces@) && valid_modes(rules@),
        Err(e) => if valid_surfaces(surfaces@) {
            !valid_modes(rules@) && e@ == "E_SEMANTIC_INPUT: unknown semantic change mode"@
        } else { e@ == "E_SURFACE_REFERENCE: unknown surface"@ },
    },
{
    let mut values=surfaces.values();
    let ghost sequence=values@.1;
    loop
        invariant 0<=values@.0<=sequence.len(), values@.1 == sequence, sequence.to_set() == surfaces@.values(),
             forall|i:int| 0<=i<values@.0 ==> known_surface(#[trigger] sequence[i]@),
        ensures valid_surfaces(surfaces@),
        decreases sequence.len()-values@.0,
    {
        let ghost previous=values@.0;
        let value=match values.next() {
            Some(v)=>v,
            None=>{
                assert forall|v:String| #[trigger] surfaces@.values().contains(v) implies known_surface(v@) by {
                    assert(sequence.contains(v));
                    let j=choose|j:int| 0<=j<sequence.len() && sequence[j]==v;
                    assert(known_surface(sequence[j]@));
                }
                break
            }
        };
        if !admits_surface(value.as_str()) {
            assert(sequence[previous] == *value);
            assert(sequence.contains(*value));
            assert(surfaces@.values().contains(*value));
            assert(!valid_surfaces(surfaces@));
            return Err("E_SURFACE_REFERENCE: unknown surface");
        }
    }
    let mut i=0;
    while i<rules.len()
        invariant valid_surfaces(surfaces@), i<=rules.len(), forall|j:int| 0<=j<i ==> known_mode(#[trigger] rules@[j].on@),
        decreases rules.len()-i,
    {
        let s=rules[i].on.as_str();
        if !(<&str>::exec_eq(s,"add-modify-delete") || <&str>::exec_eq(s,"modify-delete-existing")) {
            assert(!known_mode(rules@[i as int].on@));
            return Err("E_SEMANTIC_INPUT: unknown semantic change mode");
        }
        i+=1;
    }
    Ok(())
}

pub fn impact_schema(actual: Option<&str>) -> (valid:bool)
    ensures valid == match actual {Some(s)=>s@=="chrono-filemap-impact/v6"@, None=>false},
{
    match actual { Some(s)=><&str>::exec_eq(s,"chrono-filemap-impact/v6"), None=>false }
}

pub open spec fn same_text(a: Option<String>, b: Option<String>) -> bool {
    match (a,b) {
        (None,None) => true,
        (Some(x),Some(y)) => x@ == y@,
        _ => false,
    }
}

fn same_optional(a: &Option<String>, b: &Option<String>) -> (same: bool)
    ensures same == same_text(*a,*b),
{
    match (a,b) {
        (None,None) => true,
        (Some(x),Some(y)) => <&str>::exec_eq(x.as_str(), y.as_str()),
        _ => false,
    }
}

pub open spec fn same_row(a: Delta, b: Delta) -> bool {
    a.kind@ == b.kind@ && a.path@ == b.path@ && same_text(a.old_blob,b.old_blob)
        && same_text(a.new_blob,b.new_blob) && same_text(a.old_mode,b.old_mode)
        && same_text(a.new_mode,b.new_mode)
}

pub fn same_delta(a: &[Delta], b: &[Delta]) -> (same:bool)
    ensures same == (a.len() == b.len()
        && forall|i:int| 0<=i<a.len() ==> same_row(#[trigger] a@[i], #[trigger] b@[i])),
{
    if a.len()!=b.len() { return false; }
    let mut i=0;
    while i<a.len()
        invariant i<=a.len(), a.len()==b.len(), forall|j:int| 0<=j<i ==> same_row(#[trigger] a@[j], #[trigger] b@[j]),
        decreases a.len()-i,
    {
        let x=&a[i]; let y=&b[i];
        if !(<&str>::exec_eq(x.kind.as_str(),y.kind.as_str()) && <&str>::exec_eq(x.path.as_str(),y.path.as_str())
            && same_optional(&x.old_blob,&y.old_blob) && same_optional(&x.new_blob,&y.new_blob)
            && same_optional(&x.old_mode,&y.old_mode) && same_optional(&x.new_mode,&y.new_mode)) {
            assert(!same_row(a@[i as int],b@[i as int]));
            return false;
        }
        i+=1;
    }
    true
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct PlanContext<'a,T> { pub binding:&'a T, pub costs:&'a T }

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct Plan<'a,T> {
    #[cfg_attr(not(verus_keep_ghost), serde(flatten))]
    pub paths:DocumentPaths<'a>,
    pub context:PlanContext<'a,T>,
}

pub fn bound_plan<'a,T>(paths:DocumentPaths<'a>, binding:&'a T, costs:&'a T) -> (plan:Plan<'a,T>)
    ensures plan.paths == paths, plan.context.binding == binding, plan.context.costs == costs,
{
    Plan { paths,context:PlanContext {binding,costs} }
}

/// A rule on either endpoint names a document only when it selects a field.
pub fn register_document<K: Ord>(named: &mut BTreeSet<K>, path: K, pointers: usize)
    requires vstd::laws_cmp::obeys_cmp::<K>(),
    ensures named@ == if pointers > 0 { old(named)@.insert(path) } else { old(named)@ },
{
    if pointers != 0 {
        named.insert(path);
    }
}

/// Accumulate exactly the existing endpoints of a named changed document.
pub fn select_document<K: Ord + Copy>(
    named: &BTreeSet<K>, before: &mut BTreeSet<K>, after: &mut BTreeSet<K>,
    path: K, old_blob: bool, new_blob: bool,
)
    requires vstd::laws_cmp::obeys_cmp::<K>(),
    ensures
        before@ == if named@.contains(path) && old_blob {
            old(before)@.insert(path)
        } else { old(before)@ },
        after@ == if named@.contains(path) && new_blob {
            old(after)@.insert(path)
        } else { old(after)@ },
{
    if named.contains(&path) {
        if old_blob { before.insert(path); }
        if new_blob { after.insert(path); }
    }
}

/// Return all mapped children in their original order, or the first error.
/// The callback is the actual recursive traversal invoked by both data commands.
pub open spec fn processed<T,E,F:Fn(usize)->Result<T,E>>(visit:F, items:Seq<T>, n:int) -> bool {
    items.len()==n && forall|i:usize| i<n ==> visit.ensures((i,),Ok::<T,E>(#[trigger] items[i as int]))
}

pub fn children<T,E,F>(length:usize, visit:F) -> (result:Result<Vec<T>,E>)
    where F:Fn(usize)->Result<T,E>,
    requires forall|i:usize| i<length ==> visit.requires((i,)),
    ensures match result {
        Ok(values) => processed(visit,values@,length as int),
        Err(error) => exists|i:usize, prefix:Seq<T>| i<length && visit.ensures((i,),Err::<T,E>(error))
            && #[trigger] processed(visit,prefix,i as int),
    },
{
    let mut accumulated=Vec::new();
    let mut i=0;
    while i<length
        invariant i<=length, forall|j:usize| j<length ==> visit.requires((j,)), processed(visit,accumulated@,i as int),
        decreases length-i,
    {
        let value=match visit(i) {Ok(value)=>value,Err(e)=>{
            assert(processed(visit,accumulated@,i as int));
            return Err(e)
        }};
        accumulated.push(value);
        i+=1;
    }
    Ok(accumulated)
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
#[cfg_attr(not(verus_keep_ghost),serde(untagged))]
pub enum ArrayForm<K,T> {
    Array((&'static str,Vec<T>)),
    Rows((&'static str,BTreeMap<K,T>)),
}

/// Row identities come from the same input array. Keep positional results for
/// ordinary arrays and associate each stable identity with its exact value.
pub fn array_form<K:Ord,T>(ids:Option<Vec<K>>, values:Vec<T>) -> (out:ArrayForm<K,T>)
    requires ids matches Some(keys) ==> keys.len()==values.len() && keys@.no_duplicates(),
        vstd::laws_cmp::obeys_cmp::<K>(),
    ensures match (ids,out) {
        (None,ArrayForm::Array((tag,items))) => tag@=="array"@ && items@==values@,
        (Some(keys),ArrayForm::Rows((tag,map))) =>
            tag@=="rows"@ && map@.dom()==keys@.to_set()
            && forall|i:int| 0<=i<keys.len() ==> map@[keys@[i]]==#[trigger] values@[i],
        _=>false,
    },
{
    let keys=match ids {None=>return ArrayForm::Array(("array",values)),Some(keys)=>keys};
    let mut map=BTreeMap::new();
    let count=keys.len();
    let ghost all_keys=keys@;
    let ghost all_values=values@;
    let mut keys=keys.into_iter();
    let mut values=values.into_iter();
    let mut i=0;
    while i<count
        invariant count==all_keys.len(), i<=all_keys.len(), all_keys.no_duplicates(), all_keys.len()==all_values.len(),
            keys@==(i as int,all_keys),values@==(i as int,all_values),
            vstd::laws_cmp::obeys_cmp::<K>(),
            forall|k:K| #[trigger] map@.contains_key(k) == (exists|j:int| 0<=j<i && #[trigger] all_keys[j]==k),
            forall|j:int| 0<=j<i ==> map@[all_keys[j]] == #[trigger] all_values[j],
        decreases all_keys.len()-i,
    {
        let key=keys.next().unwrap();
        let value=values.next().unwrap();
        map.insert(key,value);
        assert forall|k:K| #[trigger] map@.contains_key(k)==(exists|j:int| 0<=j<i+1 && #[trigger] all_keys[j]==k) by {
            if k==all_keys[i as int] {assert(all_keys[i as int]==k);}
        }
        i+=1;
    }
    assert(map@.dom() =~= all_keys.to_set());
    ArrayForm::Rows(("rows",map))
}

/// The first invalid or duplicate row ends this array. Successful identities
/// line up one-to-one with all input slots.
pub fn row_keys<E,R,D>(n:usize, render:R, duplicate:D) -> (out:Result<Vec<String>,E>)
    where R:Fn(usize)->Result<String,E>, D:FnOnce(&String)->E,
    requires forall|i:usize| i<n ==> render.requires((i,)), forall|s:&String| duplicate.requires((s,)),
        vstd::laws_cmp::obeys_cmp::<String>(),
    ensures match out {
        Ok(keys) => keys@.no_duplicates() && processed(render,keys@,n as int),
        Err(e) => exists|i:usize, prefix:Seq<String>| i<n && prefix.no_duplicates()
            && #[trigger] processed(render,prefix,i as int) && (
                render.ensures((i,),Err::<String,E>(e))
                || exists|s:String| #[trigger] render.ensures((i,),Ok::<String,E>(s))
                    && prefix.contains(s) && duplicate.ensures((&s,),e)),
    },
{
    let mut keys:Vec<String>=Vec::new();
    let mut seen=BTreeSet::new();
    let mut i=0;
    while i<n
        invariant i<=n, processed(render,keys@,i as int), keys@.no_duplicates(), seen@==keys@.to_set(),
            vstd::laws_cmp::obeys_cmp::<String>(), forall|k:usize| k<n ==> render.requires((k,)),
            forall|s:&String| duplicate.requires((s,)),
        decreases n-i,
    {
        let key=match render(i) {
            Ok(key)=>key,
            Err(e)=>{assert(processed(render,keys@,i as int)); return Err(e)},
        };
        if !new_row(&mut seen,key.clone()) {
            assert(keys@.contains(key));
            let e=duplicate(&key);
            assert(processed(render,keys@,i as int));
            return Err(e);
        }
        assert(!keys@.contains(key));
        let ghost prior=keys@;
        keys.push(key);
        assert(keys@.to_set() =~= prior.to_set().insert(key)) by {
            assert forall|item:String| #[trigger] keys@.to_set().contains(item) == (prior.contains(item)||item==key) by {
                if keys@.contains(item) {
                    let j=choose|j:int| 0<=j<keys.len() && keys@[j]==item;
                    if j<prior.len() {assert(prior[j]==item);}
                }
                if prior.contains(item) {
                    let j=choose|j:int| 0<=j<prior.len() && prior[j]==item;
                    assert(keys@[j]==item);
                    assert(keys@.contains(item));
                }
                if item==key {assert(keys@[i as int]==item);assert(keys@.contains(item));}
            }
        }

        i+=1;
    }
    Ok(keys)
}

pub enum Step<'a> { Leaf, Child(&'a str, usize) }

/// The recursion consumes exactly one token at each descent. A value is
/// selected at its current physical path only after the full pattern.
pub fn step(parts:&[String], depth:usize) -> (next:Step<'_>)
    requires depth <= parts.len(),
    ensures match next {
        Step::Leaf => depth == parts.len(),
        Step::Child(token,child) => depth < parts.len() && token@ == parts@[depth as int]@ && child == depth + 1,
    },
{
    if depth == parts.len() {Step::Leaf} else { Step::Child(parts[depth].as_str(),depth+1) }
}

pub open spec fn identity_prefix(object:bool) -> Seq<char> {
    if object {"key:"@} else {"index:"@}
}

/// A physical array index is used as identity only for an unnamed array.
pub fn selection_identity(object:bool, component:&str, named:Option<&str>) -> (identity:String)
    ensures identity@ == if !object && named.is_some() {named.unwrap()@}
        else {identity_prefix(object) + component@},
{
    if !object {
        if let Some(name)=named {return String::from_str(name);}
    }
    let mut out=if object {String::from_str("key:")} else {String::from_str("index:")};
    out.append(component);out
}

/// Each projected difference retains the borrowed key and both original
/// selections so the serializer cannot substitute normalized values or paths.
pub struct Difference<'a,K,V> { pub key:&'a K, pub before:Option<&'a V>, pub after:Option<&'a V> }

pub open spec fn selected_change(mode:Seq<char>, old:bool, new:bool, same:bool) -> bool {
    (old || mode != "modify-delete-existing"@) && (old != new || (old && new && !same))
}

pub fn difference<'a,K,V,F>(key:&'a K, before:Option<&'a V>, after:Option<&'a V>, mode:&str, equal:F)
    -> (out:Option<Difference<'a,K,V>>)
    where F:FnOnce(&V,&V)->bool,
    requires forall|a:&V,b:&V| equal.requires((a,b)),
    ensures ({
        let selected = match (before,after) {
            (Some(a),Some(b)) => exists|same:bool| #[trigger] equal.ensures((a,b),same)
                && out.is_some()==selected_change(mode@,true,true,same),
            _ => out.is_some() == selected_change(mode@,before.is_some(),after.is_some(),false),
        };
        selected && (out matches Some(d) ==> d.key==key && d.before==before && d.after==after)
    }),
{
    let same=match (before,after) { (Some(a),Some(b))=>equal(a,b), _=>false };
    if field_changed(mode,before.is_some(),after.is_some(),same) {
        Some(Difference{key,before,after})
    } else { None }
}

/// Include every identity from both selections exactly once. The native BTreeSet
/// iterator supplies its standard total order to classify-v1 and report-v1.
pub fn selection_keys<'a,K:Ord,V>(before:&'a BTreeMap<K,V>,after:&'a BTreeMap<K,V>)
    -> (keys:BTreeSet<&'a K>)
    requires vstd::laws_cmp::obeys_cmp::<K>(), vstd::laws_cmp::obeys_cmp::<&K>(),
    ensures forall|key:&K| #[trigger] keys@.contains(key) == (before@.contains_key(*key)||after@.contains_key(*key)),
{
    let mut keys=BTreeSet::new();
    add_keys(&mut keys,before);
    add_keys(&mut keys,after);
    keys
}

fn add_keys<'a,K:Ord,V>(out:&mut BTreeSet<&'a K>,source:&'a BTreeMap<K,V>)
    requires vstd::laws_cmp::obeys_cmp::<K>(), vstd::laws_cmp::obeys_cmp::<&K>(),
    ensures forall|key:&K| #[trigger] out@.contains(key)==(old(out)@.contains(key)||source@.contains_key(*key)),
{
    let mut iter=source.keys();
    let ghost declared=iter@.1;
    loop
        invariant iter@.1==declared, 0<=iter@.0<=declared.len(), declared.to_set()==source@.dom(),
            vstd::laws_cmp::obeys_cmp::<&K>(),
            forall|k:&K| #[trigger] out@.contains(k) == (old(out)@.contains(k) ||
                    exists|i:int| 0<=i<iter@.0 && #[trigger] declared[i]==*k),
        ensures forall|k:&K| #[trigger] out@.contains(k) == (old(out)@.contains(k)||source@.contains_key(*k)),
        decreases declared.len()-iter@.0,
    {
        let ghost previous=iter@.0;
        let key=match iter.next() {Some(k)=>k,None=>{
            assert forall|k:&K| #[trigger] out@.contains(k) == (old(out)@.contains(k)||source@.contains_key(*k)) by {
                if source@.contains_key(*k) { assert(declared.contains(*k)); }
                if exists|i:int| 0<=i<iter@.0 && #[trigger] declared[i]==*k { assert(declared.contains(*k)); }
            }
            break;
        }};
        out.insert(key);
        assert forall|k:&K| #[trigger] out@.contains(k) == (old(out)@.contains(k) ||
                exists|i:int| 0<=i<iter@.0 && #[trigger] declared[i]==*k) by {
            if k==key { assert(declared[previous]==*k); }
        }
    }
}

/// Adapter for serde_json::Map::iter. Its remaining sequence is the external
/// iterator's ordered (key, value) pairs, including the current next pair.
pub trait ObjectCursor<'a,V:'a>: Sized {
    spec fn remaining(&self) -> Seq<(&'a String,&'a V)>;
    fn next_pair(&mut self) -> (entry:Option<(&'a String,&'a V)>)
        ensures match entry {
            None => old(self).remaining().len()==0,
            Some(pair) => old(self).remaining().len()>0 && pair == old(self).remaining()[0]
                && self.remaining()==old(self).remaining().drop_first(),
        };
}

pub open spec fn accepts_object(token:Option<&str>, key:&String) -> bool {
    match token { None=>true, Some(s)=>s@=="*"@ || s@==key@ }
}

pub open spec fn folded<'a,V,S,E,F:Fn(&'a String,&'a V,S)->Result<S,E>>(
    items:Seq<(&'a String,&'a V)>, n:int, token:Option<&str>, step:F, states:Seq<S>,
) -> bool {
    &&& 0<=n<=items.len() && states.len()==n+1
    &&& forall|i:int| #![trigger items[i],states[i]] 0<=i<n ==> if accepts_object(token,items[i].0) {
        step.ensures((items[i].0,items[i].1,states[i]),Ok::<S,E>(states[i+1]))
    } else {states[i+1]==states[i]}
}

/// Normalization walks every member; selection walks only exact or wildcard
/// matches. Passing the state by value preserves every accepted child update.
pub fn object_members<'a,V:'a,I,S,E,F>(source:I, token:Option<&str>, initial:S, visit:F)
    -> (out:Result<S,E>)
    where I:ObjectCursor<'a,V>, F:Fn(&'a String,&'a V,S)->Result<S,E>,
    requires forall|k:&'a String,v:&'a V,s:S| visit.requires((k,v,s)),
    ensures match out {
        Ok(end)=>exists|states:Seq<S>| #[trigger] folded(source.remaining(),source.remaining().len() as int,token,visit,states)
            && states[0]==initial && states.last()==end,
        Err(error)=>exists|i:int,states:Seq<S>| 0<=i<source.remaining().len()
            && #[trigger] folded(source.remaining(),i,token,visit,states) && states[0]==initial
            && accepts_object(token,source.remaining()[i].0)
            && visit.ensures((source.remaining()[i].0,source.remaining()[i].1,states.last()),Err::<S,E>(error)),
    },
{
    let ghost all=source.remaining();
    let mut cursor=source;
    let ghost mut index:int=0;
    let ghost mut states=seq![initial];
    let mut state=initial;
    loop
        invariant all==source.remaining(), 0<=index<=all.len(), cursor.remaining()==all.skip(index),
            folded(all,index,token,visit,states),states[0]==initial,states.last()==state,
            forall|k:&'a String,v:&'a V,s:S| visit.requires((k,v,s)),
        decreases all.len()-index,
    {
        let (key,child)=match cursor.next_pair() {
            None=>{assert(index==all.len());assert(folded(source.remaining(),source.remaining().len() as int,token,visit,states));return Ok(state)},
            Some(pair)=>pair,
        };
        assert((key,child)==all[index]);
        let selected=match token {None=>true,Some(t)=>matches_child(t,key.as_str())};
        if selected {
            state=match visit(key,child,state) {
                Ok(next)=>next,
                Err(e)=>{assert(visit.ensures((all[index].0,all[index].1,states.last()),Err::<S,E>(e)));assert(folded(source.remaining(),index,token,visit,states));return Err(e)},
            };
        }
        proof {
            let extended=states.push(state);
            assert(folded(all,index+1,token,visit,extended)) by {
                assert forall|i:int| 0<=i<index+1 implies
                    if accepts_object(token,all[i].0) { visit.ensures((all[i].0,all[i].1,extended[i]),Ok::<S,E>(#[trigger] extended[i+1])) }
                    else { #[trigger] extended[i+1]==extended[i] } by {
                    if i<index {assert(extended[i+1]==states[i+1]);}
                }
            }
            states=extended;
            index=index+1;
            assert(cursor.remaining() =~= all.skip(index));
        }
    }
}

pub open spec fn applied<S,E,F:Fn(usize,S)->Result<S,E>>(n:int,visit:F,states:Seq<S>) -> bool {
    states.len()==n+1 && forall|i:usize| i<n ==> visit.ensures((i,states[i as int]),Ok::<S,E>(#[trigger] states[i+1]))
}

pub fn indices<S,E,F>(count:usize, initial:S, visit:F) -> (out:Result<S,E>)
    where F:Fn(usize,S)->Result<S,E>,
    requires forall|i:usize,s:S| i<count ==> visit.requires((i,s)),
    ensures match out {
        Ok(end)=>exists|states:Seq<S>| #[trigger] applied(count as int,visit,states) && states[0]==initial && states.last()==end,
        Err(e)=>exists|i:usize,states:Seq<S>| i<count && #[trigger] applied(i as int,visit,states)
            && states[0]==initial && visit.ensures((i,states.last()),Err::<S,E>(e)),
    },
{
    let mut state=initial;let ghost mut states=seq![initial];let mut i=0;
    while i<count
        invariant i<=count,applied(i as int,visit,states),states[0]==initial,states.last()==state,
            forall|j:usize,s:S| j<count ==> visit.requires((j,s)),
        decreases count-i,
    {
        state=match visit(i,state) {
            Ok(v)=>v,
            Err(e)=>{assert(applied(i as int,visit,states));return Err(e)}
        };
        proof {
            let extended=states.push(state);
            assert forall|j:usize| j<i+1 implies visit.ensures((j,extended[j as int]),Ok::<S,E>(#[trigger] extended[j+1])) by {
                if j<i {assert(extended[j+1]==states[j+1]);}
            }
            states=extended;
        }
        i+=1;
    }
    Ok(state)
}

pub struct ClassifiedPath<'a,R,P> {
    pub path:&'a String, pub rule:Option<R>, pub product:Option<P>,
}

pub struct ClassifiedPaths<'a,R,P> {
    pub rules:BTreeMap<&'a String,R>,
    pub products:BTreeMap<&'a String,P>,
}

pub open spec fn rule_map<'a,R,P>(rows:Seq<ClassifiedPath<'a,R,P>>) -> Map<&'a String,R>
    decreases rows.len(),
{
    if rows.len()==0 {Map::empty()} else {
        let previous=rule_map(rows.drop_last());let row=rows.last();
        match row.rule { Some(r)=>previous.insert(row.path,r),None=>previous }
    }
}

pub open spec fn product_map<'a,R,P>(rows:Seq<ClassifiedPath<'a,R,P>>) -> Map<&'a String,P>
    decreases rows.len(),
{
    if rows.len()==0 {Map::empty()} else {
        let previous=product_map(rows.drop_last());let row=rows.last();
        match row.product { Some(p)=>previous.insert(row.path,p),None=>previous }
    }
}

/// Consume each actual DELTA row once, preserving the first diagnostic.
pub fn classified_paths<'a,R,P,E,F>(n:usize, classify:F) -> (result:Result<ClassifiedPaths<'a,R,P>,E>)
    where F:Fn(usize)->Result<ClassifiedPath<'a,R,P>,E>,
    requires forall|i:usize| i<n ==> classify.requires((i,)), vstd::laws_cmp::obeys_cmp::<&String>(),
    ensures match result {
        Ok(out) => exists|rows:Seq<ClassifiedPath<'a,R,P>>| #[trigger] processed(classify,rows,n as int)
            && out.rules@==rule_map(rows) && out.products@==product_map(rows),
        Err(e) => exists|i:usize,rows:Seq<ClassifiedPath<'a,R,P>>| i<n && #[trigger] processed(classify,rows,i as int)
            && classify.ensures((i,),Err::<ClassifiedPath<'a,R,P>,E>(e)),
    },
{
    let mut rules=BTreeMap::new();let mut products=BTreeMap::new();
    let ghost mut rows:Seq<ClassifiedPath<'a,R,P>>=Seq::empty();
    let mut i=0;
    while i<n
        invariant i<=n,processed(classify,rows,i as int),rules@==rule_map(rows),products@==product_map(rows),
            forall|j:usize| j<n ==> classify.requires((j,)),vstd::laws_cmp::obeys_cmp::<&String>(),
        decreases n-i,
    {
        let row=match classify(i) {
            Ok(row)=>row,Err(e)=>{assert(processed(classify,rows,i as int));return Err(e)}
        };
        let ghost extended=rows.push(row);
        assert(extended.drop_last() =~= rows);
        if let Some(r)=row.rule {rules.insert(row.path,r);}
        if let Some(p)=row.product {products.insert(row.path,p);}
        proof {rows=extended;}
        i+=1;
    }
    Ok(ClassifiedPaths{rules,products})
}

pub fn documents_available(old_blob:bool, old_doc:bool, new_blob:bool, new_doc:bool) -> (valid:bool)
    ensures valid==((!old_blob || old_doc) && (!new_blob || new_doc)),
{ (!old_blob || old_doc) && (!new_blob || new_doc) }

pub type Pattern=(String,String,String);

pub open spec fn registered(rules:Seq<Rule>,n:int,p:Pattern) -> bool {
    exists|i:int,j:int| 0<=i<n && 0<=j<rules[i].pointers.len()
        && (#[trigger] rules[i].pointers[j])==p.1 && rules[i].path==p.0 && rules[i].on==p.2
}

fn add_patterns(out:&mut BTreeSet<Pattern>,rules:&[Rule])
    requires vstd::laws_cmp::obeys_cmp::<Pattern>(),
    ensures forall|p:Pattern| #[trigger] out@.contains(p)==(old(out)@.contains(p)||registered(rules@,rules.len() as int,p)),
{
    let mut i=0;
    while i<rules.len()
        invariant i<=rules.len(),vstd::laws_cmp::obeys_cmp::<Pattern>(),forall|p:Pattern| #[trigger] out@.contains(p)==(old(out)@.contains(p)||registered(rules@,i as int,p)),
        decreases rules.len()-i,
    {
        let r=&rules[i];
        let ghost before=out@;
        let mut j=0;
        while j<r.pointers.len()
            invariant j<=r.pointers.len(),vstd::laws_cmp::obeys_cmp::<Pattern>(),
                forall|p:Pattern| #[trigger] out@.contains(p)==(before.contains(p) ||
                    (p.0==r.path && p.2==r.on && exists|k:int| 0<=k<j && #[trigger] r.pointers[k]==p.1)),
            decreases r.pointers.len()-j,
        {
            out.insert((r.path.clone(),r.pointers[j].clone(),r.on.clone()));
            assert forall|p:Pattern| #[trigger] out@.contains(p)==(before.contains(p) ||
                (p.0==r.path && p.2==r.on && exists|k:int| 0<=k<j+1 && #[trigger] r.pointers[k]==p.1)) by {
                if p.1==r.pointers[j as int] { assert(r.pointers[j as int]==p.1); }
            }
            j+=1;
        }
        assert forall|p:Pattern| #[trigger] out@.contains(p)==(old(out)@.contains(p)||registered(rules@,i+1,p)) by {
            if p.0==r.path && p.2==r.on && exists|k:int| 0<=k<j && #[trigger] r.pointers[k]==p.1 {
                let k=choose|k:int| 0<=k<j && #[trigger] r.pointers[k]==p.1;assert(rules@[i as int].pointers[k]==p.1);
            }
        }
        i+=1;
    }
}

pub fn patterns(before:&[Rule],after:&[Rule]) -> (out:BTreeSet<Pattern>)
    requires vstd::laws_cmp::obeys_cmp::<Pattern>(),
    ensures forall|p:Pattern| #[trigger] out@.contains(p) == (registered(before@,before.len() as int,p)||registered(after@,after.len() as int,p)),
{
    let mut set=BTreeSet::new();add_patterns(&mut set,before);add_patterns(&mut set,after);set
}

pub fn new_row<K: Ord>(seen: &mut BTreeSet<K>, id: K) -> (fresh: bool)
    requires vstd::laws_cmp::obeys_cmp::<K>(),
    ensures fresh == !old(seen)@.contains(id), seen@ == old(seen)@.insert(id),
{ seen.insert(id) }

pub fn record_selection<K: Ord,V>(entries: &mut BTreeMap<K,V>, id: K, value: V)
    -> (result: Result<(), &'static str>)
    requires vstd::laws_cmp::obeys_cmp::<K>(),
    ensures entries@ == old(entries)@.insert(id,value),
        match result {
            Ok(()) => !old(entries)@.contains_key(id),
            Err(e) => old(entries)@.contains_key(id) && e@ == "E_SEMANTIC_IDENTITY: ambiguous selection"@,
        },
{
    if entries.insert(id,value).is_some() { Err("E_SEMANTIC_IDENTITY: ambiguous selection") } else { Ok(()) }
}

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

/// Serialize a warning only for a mixed DELTA. References retain their two
/// published path orders, including a path classified on both sides.
pub fn report_finding<'a, T>(rules: &'a [T], products: &'a [T])
    -> (out: (&'static str, Option<Vec<&'a T>>))
    ensures
        (out.1 is Some) == (rules.len() > 0 && products.len() > 0),
        match out.1 {
            None => out.0@ == "pass"@,
            Some(refs) => {
                &&& out.0@ == "warn"@
                &&& refs.len() == rules.len() + products.len()
                &&& forall|i:int| 0 <= i < rules.len() ==> *(#[trigger] refs[i]) == rules[i]
                &&& forall|i:int| 0 <= i < products.len() ==> *(#[trigger] refs[rules.len()+i]) == products[i]
            },
        },
{
    if !mixed(rules.len(), products.len()) { return ("pass", None); }
    let mut refs: Vec<&'a T> = Vec::new();
    let mut i = 0;
    while i < rules.len()
        invariant
            i <= rules.len(), refs.len() == i,
            forall|j:int| 0 <= j < i ==> *(#[trigger] refs[j]) == rules[j],
        decreases rules.len() - i,
    {
        refs.push(&rules[i]);
        i += 1;
    }
    let mut i = 0;
    while i < products.len()
        invariant
            i <= products.len(), refs.len() == rules.len() + i,
            forall|j:int| 0 <= j < rules.len() ==> *(#[trigger] refs[j]) == rules[j],
            forall|j:int| 0 <= j < i ==> *(#[trigger] refs[rules.len()+j]) == products[j],
        decreases products.len() - i,
    {
        refs.push(&products[i]);
        i += 1;
    }
    ("warn", Some(refs))
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Finding<'a,T> {
    pub code:&'a str,
    pub level:&'static str,
    pub message:String,
    pub delta_refs:Vec<&'a T>,
    pub causes:[&'static str;1],
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Outputs<'a,R> { pub rule_changes:&'a R }

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct ReportEnvelope<'a,T,R> {
    pub status:&'static str,
    pub findings:Vec<Finding<'a,T>>,
    pub outputs:Outputs<'a,R>,
}

/// The only warning is attached to the actual classification with the host's
/// code. Only a mixed report evaluates the diagnostic formatter.
pub fn report_envelope<'a,T,R,M>(rules:&'a [T], products:&'a [T], changes:&'a R, code:&'a str, message:M)
    -> (out:ReportEnvelope<'a,T,R>)
    where M:FnOnce()->String,
    requires message.requires(()),
    ensures out.outputs.rule_changes==changes,
        if rules.len()==0 || products.len()==0 {out.status@=="pass"@ && out.findings.len()==0}
        else {
            let item=out.findings@[0];
            &&& out.status@=="warn"@ && out.findings.len()==1
            &&& item.code@==code@ && item.level@=="warning"@ && message.ensures((),item.message)
            &&& item.causes@[0]@=="/outputs/rule_changes"@
            &&& item.delta_refs.len()==rules.len()+products.len()
            &&& forall|i:int| 0<=i<rules.len() ==> *(#[trigger] item.delta_refs[i])==rules@[i]
            &&& forall|i:int| 0<=i<products.len() ==> *(#[trigger] item.delta_refs[rules.len()+i])==products@[i]
        },
{
    let (status,refs)=report_finding(rules,products);
    let mut findings=Vec::new();
    if let Some(delta_refs)=refs {
        findings.push(Finding {code,level:"warning",message:message(),delta_refs,causes:["/outputs/rule_changes"]});
    }
    ReportEnvelope {status,findings,outputs:Outputs {rule_changes:changes}}
}

pub fn cost_report_shape(schema: Option<&str>, before_object: bool, after_object: bool) -> (valid: bool)
    ensures valid == (before_object && after_object && match schema {
        Some(value) => value@ == "chrono-costs/v1"@, None => false,
    }),
{
    match schema {
        Some(value) => <&str>::exec_eq(value, "chrono-costs/v1") && before_object && after_object,
        None => false,
    }
}

pub enum CostSide { Before, After }

impl CostSide {
    pub fn field(&self) -> (name: &'static str)
        ensures match self {
            Self::Before => name@ == "declared_before"@,
            Self::After => name@ == "declared_after"@,
        },
    { match self { Self::Before => "declared_before", Self::After => "declared_after" } }
}

/// Only look up a row when all preceding DELTA rows have both endpoint entries.
pub fn first_missing_cost<F: Fn(usize) -> (bool, bool)>(count: usize, lookup: F)
    -> (missing: Option<(usize, CostSide)>)
    requires forall|i: usize| i < count ==> lookup.requires((i,)),
    ensures match missing {
        None => forall|i: usize| i < count ==> lookup.ensures((i,), (true, true)),
        Some((i, side)) => i < count
            && (forall|j: usize| j < i ==> lookup.ensures((j,), (true, true)))
            && match side {
                CostSide::Before => exists|after: bool| lookup.ensures((i,), (false, after)),
                CostSide::After => lookup.ensures((i,), (true, false)),
            },
    },
{
    let mut i = 0;
    while i < count
        invariant i <= count, forall|j: usize| j < count ==> lookup.requires((j,)),
            forall|j: usize| j < i ==> lookup.ensures((j,), (true, true)),
        decreases count - i,
    {
        let (before, after) = lookup(i);
        if !before { return Some((i, CostSide::Before)); }
        if !after { return Some((i, CostSide::After)); }
        i += 1;
    }
    None
}

/// Evaluate only declarations for this DELTA path. Each callback receives
/// the actual old and new documents and the matching endpoint's workflow flag.
pub open spec fn field_batch<'a,T,V:'a,E,F:Fn(Option<&'a V>,Option<&'a V>,&String,&String,bool,bool)->Result<Vec<T>,E>>(
    p:Pattern,path:&String,a:Option<&'a V>,b:Option<&'a V>,ow:bool,nw:bool,valid:bool,visit:F,batch:Vec<T>,
)->bool {
    if p.0@==path@ {valid && visit.ensures((a,b,&p.1,&p.2,ow,nw),Ok::<Vec<T>,E>(batch))}
    else {batch.len()==0}
}
pub open spec fn flattened<T>(batches:Seq<Vec<T>>)->Seq<T>
    decreases batches.len(),
{ if batches.len()==0 {Seq::empty()} else {flattened(batches.drop_last())+batches.last()@} }

pub open spec fn visited_patterns<'a,T,V:'a,E,F:Fn(Option<&'a V>,Option<&'a V>,&String,&String,bool,bool)->Result<Vec<T>,E>>(
    ps:Seq<Pattern>,n:int,path:&String,a:Option<&'a V>,b:Option<&'a V>,ow:bool,nw:bool,valid:bool,visit:F,batches:Seq<Vec<T>>,
)->bool {
    batches.len()==n && forall|i:int| 0<=i<n ==> #[trigger] field_batch(ps[i],path,a,b,ow,nw,valid,visit,batches[i])
}

pub fn fields_for_path<'a,T,V,E,F,M>(ps:&[Pattern],path:&String,a:Option<&'a V>,b:Option<&'a V>,
    ow:bool,nw:bool,valid:bool,visit:F,missing:M)->(out:Result<Vec<T>,E>)
    where F:Fn(Option<&'a V>,Option<&'a V>,&String,&String,bool,bool)->Result<Vec<T>,E>, M:FnOnce(&String)->E,
    requires missing.requires((path,)), forall|a:Option<&'a V>,b:Option<&'a V>,s:&String,t:&String,x:bool,y:bool|visit.requires((a,b,s,t,x,y)),
    ensures match out {
        Ok(values)=>exists|batches:Seq<Vec<T>>| #[trigger] visited_patterns(ps@,ps.len() as int,path,a,b,ow,nw,valid,visit,batches)
            && values@==flattened(batches),
        Err(e)=>exists|i:int,batches:Seq<Vec<T>>| 0<=i<ps.len() && ps@[i].0@==path@
            && #[trigger] visited_patterns(ps@,i,path,a,b,ow,nw,valid,visit,batches)
            && (if valid {visit.ensures((a,b,&ps@[i].1,&ps@[i].2,ow,nw),Err::<Vec<T>,E>(e))} else {missing.ensures((path,),e)}),
    },
{
    let mut values=Vec::new();let mut i=0;let ghost mut batches:Seq<Vec<T>>=Seq::empty();
    while i<ps.len()
        invariant i<=ps.len(),visited_patterns(ps@,i as int,path,a,b,ow,nw,valid,visit,batches),values@==flattened(batches),
            missing.requires((path,)),forall|a:Option<&'a V>,b:Option<&'a V>,s:&String,t:&String,x:bool,y:bool|visit.requires((a,b,s,t,x,y)),
        decreases ps.len()-i,
    {
        let p=&ps[i];
        let ghost mut batch:Vec<T>;
        if <&str>::exec_eq(p.0.as_str(),path.as_str()) {
            assert(ps@[i as int].0@==path@);
            if !valid {let e=missing(path);assert(missing.ensures((path,),e));assert(visited_patterns(ps@,i as int,path,a,b,ow,nw,valid,visit,batches));return Err(e)}
            let mut next=match visit(a,b,&p.1,&p.2,ow,nw) {
                Ok(items)=>items,
                Err(e)=>{assert(visit.ensures((a,b,&ps@[i as int].1,&ps@[i as int].2,ow,nw),Err::<Vec<T>,E>(e)));assert(visited_patterns(ps@,i as int,path,a,b,ow,nw,valid,visit,batches));return Err(e)}
            };
            proof {batch=next;}
            values.append(&mut next);
        } else { let empty:Vec<T>=Vec::new(); proof {batch=empty;} }
        proof {
            let extended=batches.push(batch);
            assert(extended.drop_last() =~= batches);
            assert(field_batch(ps@[i as int],path,a,b,ow,nw,valid,visit,batch));
            assert forall|j:int| 0<=j<i+1 implies #[trigger] field_batch(ps@[j],path,a,b,ow,nw,valid,visit,extended[j]) by {
                if j<i {assert(extended[j]==batches[j]);}
                else {assert(extended[j]==batch);}
            }
            assert(visited_patterns(ps@,i+1,path,a,b,ow,nw,valid,visit,extended));
            batches=extended;
        }
        i+=1;
    }
    assert(visited_patterns(ps@,ps.len() as int,path,a,b,ow,nw,valid,visit,batches));
    Ok(values)
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Selection<T> {
    pub pointer:String, pub value:T,
    #[cfg_attr(not(verus_keep_ghost),serde(skip))]
    pub normalized:T,
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct SemanticChange<'a,K,V> {
    pub pattern:&'a str, pub on:&'a str, pub identity:&'a K,
    pub before:Option<&'a V>, pub after:Option<&'a V>,
}

pub fn semantic_change<'a,K,V>(pattern:&'a str, on:&'a str, d:Difference<'a,K,V>)
    -> (out:SemanticChange<'a,K,V>)
    ensures out.pattern==pattern && out.on==on && out.identity==d.key && out.before==d.before && out.after==d.after,
{ SemanticChange {pattern,on,identity:d.key,before:d.before,after:d.after} }

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct PathSurfaces<'a> {
    pub path:&'a String, pub before_surface:Option<&'a String>, pub after_surface:Option<&'a String>,
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct RuleChange<'a,T> {
    #[cfg_attr(not(verus_keep_ghost),serde(flatten))]
    pub surfaces:PathSurfaces<'a>, pub whole_file:bool, pub semantic:Vec<T>,
}

pub fn surface_row<'a,T>(path:&'a String, before:Option<&'a String>, after:Option<&'a String>,
    mask:Surfaces, fields:Vec<T>) -> (out:ClassifiedPath<'a,RuleChange<'a,T>,PathSurfaces<'a>>)
    ensures out.path==path,
        out.rule.is_some()==(mask.whole_rule || fields.len()>0),out.product.is_some()==mask.product,
        out.rule matches Some(r) ==> r.surfaces.path==path && r.surfaces.before_surface==before
            && r.surfaces.after_surface==after && r.whole_file==mask.whole_rule && r.semantic==fields,
        out.product matches Some(p) ==> p.path==path && p.before_surface==before && p.after_surface==after,
{
    let rule=if mask.changes_rule(fields.len()>0) {
        Some(RuleChange {surfaces:PathSurfaces {path,before_surface:before,after_surface:after},whole_file:mask.whole_rule,semantic:fields})
    } else {None};
    let product=if mask.product {Some(PathSurfaces {path,before_surface:before,after_surface:after})} else {None};
    ClassifiedPath {path,rule,product}
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Classification<'a,R,P> {
    pub mixed:bool,pub rule_paths:Vec<&'a String>,pub product_paths:Vec<&'a String>,
    pub changes:Vec<R>,pub product_changes:Vec<P>,pub requires_acknowledgement:bool,
}

pub fn classification<'a,R,P>(rule_paths:Vec<&'a String>,changes:Vec<R>,product_paths:Vec<&'a String>,product_changes:Vec<P>)
    -> (out:Classification<'a,R,P>)
    ensures out.mixed==(rule_paths.len()>0 && product_paths.len()>0),
        !out.requires_acknowledgement && out.rule_paths==rule_paths && out.product_paths==product_paths
        && out.changes==changes && out.product_changes==product_changes,
{
    Classification {mixed:mixed(rule_paths.len(),product_paths.len()),rule_paths,product_paths,changes,product_changes,requires_acknowledgement:false}
}

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct Costed<T> {
    pub schema:&'static str,
    #[cfg_attr(not(verus_keep_ghost),serde(flatten))]
    pub classification:T,
}
pub fn costed<T>(classification:T)->(out:Costed<T>)
    ensures out.schema@=="chrono-rule-changes/v2"@ && out.classification==classification,
{ Costed {schema:"chrono-rule-changes/v2",classification} }

#[cfg_attr(not(verus_keep_ghost),derive(serde::Serialize))]
pub struct BoundReport<T,B> {
    #[cfg_attr(not(verus_keep_ghost),serde(flatten))]
    pub changes:T, pub binding:B,
}
pub fn bind_report<T,B>(changes:T,binding:B)->(out:BoundReport<T,B>)
    ensures out.changes==changes && out.binding==binding,
{ BoundReport {changes,binding} }

pub fn warning_message(rules:&str,products:&str) -> (out:String)
    ensures out@=="Rule and product changes share this DELTA. Rules: "@ + rules@ + "; products: "@ + products@
        + ". Before/after costs: predecessor outputs.costs (full report: /costs; provenance: /sources/~1costs); unknown coordinates remain unknown."@,
{
    let mut out=String::from_str("Rule and product changes share this DELTA. Rules: ");
    out.append(rules);
    out.append("; products: ");
    out.append(products);
    out.append(". Before/after costs: predecessor outputs.costs (full report: /costs; provenance: /sources/~1costs); unknown coordinates remain unknown.");
    out
}
pub open spec fn some_items<T>(items:Seq<Option<T>>) -> Seq<T>
    decreases items.len(),
{ if items.len()==0 {Seq::empty()} else {
    let prefix=some_items(items.drop_last());match items.last() {None=>prefix,Some(v)=>prefix.push(v)}
} }

/// Preserve all selected changes in the identity iterator's exact order.
pub fn changed_items<K,T,F>(keys:&[K], project:F)->(out:Vec<T>)
    where F:Fn(&K)->Option<T>,
    requires forall|k:&K| project.requires((k,)),
    ensures exists|items:Seq<Option<T>>| #[trigger] projected(keys@,keys.len() as int,project,items) && out@==some_items(items),
{
    let mut out=Vec::new();let mut i=0;let ghost mut items=Seq::empty();
    while i<keys.len()
        invariant i<=keys.len(),projected(keys@,i as int,project,items),out@==some_items(items),
            forall|k:&K| project.requires((k,)),
        decreases keys.len()-i,
    {
        let value=project(&keys[i]);let ghost next=items.push(value);
        assert(next.drop_last() =~= items);
        if let Some(x)=value {out.push(x);}
        assert forall|j:int| 0<=j<i+1 implies project.ensures((&keys@[j],),#[trigger] next[j]) by {
            if j<i {assert(next[j]==items[j]);}
        }
        proof {items=next;}
        i+=1;
    }
    assert(projected(keys@,keys.len() as int,project,items));
    out
}
pub open spec fn projected<K,T,F:Fn(&K)->Option<T>>(keys:Seq<K>,n:int,project:F,items:Seq<Option<T>>)->bool {
    items.len()==n && forall|j:int| 0<=j<n ==> project.ensures((&keys[j],),#[trigger] items[j])
}
pub fn document_pair<'a,V>(before:&'a BTreeMap<String,V>,after:&'a BTreeMap<String,V>,path:&String)
    -> (out:(Option<&'a V>,Option<&'a V>))
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures match out.0 {Some(v)=>before@.contains_key(*path) && *v==before@[*path],None=>!before@.contains_key(*path)},
        match out.1 {Some(v)=>after@.contains_key(*path) && *v==after@[*path],None=>!after@.contains_key(*path)},
{ (before.get(path),after.get(path)) }

pub open spec fn side_result<V,K,S,E,F:Fn(&V,bool)->Result<BTreeMap<K,S>,E>>(
    source:Option<&V>,workflow:bool,select:F,out:Result<BTreeMap<K,S>,E>,
)->bool {
    match source {None=>out matches Ok(entries) && entries@==Map::<K,S>::empty(),Some(v)=>select.ensures((v,workflow),out)}
}
fn select_side<V,K:Ord,S,E,F:Fn(&V,bool)->Result<BTreeMap<K,S>,E>>(
    source:Option<&V>,workflow:bool,select:&F,
)->(out:Result<BTreeMap<K,S>,E>)
    requires forall|v:&V,w:bool| select.requires((v,w)),
    ensures side_result(source,workflow,*select,out),
{
    match source {None=>Ok(BTreeMap::new()),Some(v)=>select(v,workflow)}
}
pub fn selected_sides<V,K:Ord,S,E,F:Fn(&V,bool)->Result<BTreeMap<K,S>,E>>(
    before:Option<&V>,after:Option<&V>,old_workflow:bool,new_workflow:bool,select:F,
)->(out:Result<(BTreeMap<K,S>,BTreeMap<K,S>),E>)
    requires forall|v:&V,w:bool| select.requires((v,w)),
    ensures match out {
        Ok((old,new))=>side_result(before,old_workflow,select,Ok::<BTreeMap<K,S>,E>(old))
            && side_result(after,new_workflow,select,Ok::<BTreeMap<K,S>,E>(new)),
        Err(e)=>side_result(before,old_workflow,select,Err::<BTreeMap<K,S>,E>(e))
            || ((exists|old:BTreeMap<K,S>| #[trigger] side_result(before,old_workflow,select,Ok::<BTreeMap<K,S>,E>(old)))
              && side_result(after,new_workflow,select,Err::<BTreeMap<K,S>,E>(e))),
    },
{
    let old=select_side(before,old_workflow,&select)?;
    let new=select_side(after,new_workflow,&select)?;
    Ok((old,new))
}

}
