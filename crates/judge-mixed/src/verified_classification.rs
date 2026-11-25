//! Classification of one changed path from its two registered endpoint surfaces.
#![allow(unexpected_cfgs)]
use std::collections::{BTreeMap, BTreeSet};
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

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
    ensures changed == (
        (before || mode@ != "modify-delete-existing"@)
        && (before != after || (before && after && !equal_values))
    ),
{
    if !before { return after && !<&str>::exec_eq(mode, "modify-delete-existing"); }
    !after || !equal_values
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

}
