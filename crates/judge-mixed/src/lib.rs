//! Explicit rule/product DELTA classification. Warnings neither authorize nor block work.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::{Costed, costed};
#[cfg(not(verus_keep_ghost))]
use verified_classification::{Costed, costed};
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// The report first admits its cost schema, then classifies changes, then checks their costs.
pub fn checked_costs<T,E,B,C,M>(valid: bool, invalid: B, classify: C, coverage: M) -> (out: Result<Costed<T>,E>)
    where B: FnOnce()->E, C: FnOnce()->Result<T,E>, M: FnOnce()->Result<(),E>,
    requires invalid.requires(()), classify.requires(()), coverage.requires(()),
    ensures match out {
        Ok(row) => valid && classify.ensures((), Ok::<T,E>(row.classification))
            && coverage.ensures((), Ok::<(),E>(())) && row.schema@ == "chrono-rule-changes/v2"@,
        Err(e) => if !valid { invalid.ensures((), e) } else {
            classify.ensures((), Err::<T,E>(e)) || ((exists|v:T| classify.ensures((), Ok::<T,E>(v))) && coverage.ensures((), Err::<(),E>(e)))
        },
    },
{
    if !valid { return Err(invalid()); }
    let classification = classify()?;
    coverage()?;
    Ok(costed(classification))
}
}

#[cfg(not(verus_keep_ghost))]
pub mod native;
#[cfg(not(verus_keep_ghost))]
mod semantic;
#[cfg(not(verus_keep_ghost))]
mod verified_classification;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeMap;
#[cfg(not(verus_keep_ghost))]
use verified_classification as policy;
#[cfg(not(verus_keep_ghost))]
pub const MIXED_SCHEMA: &str = "chrono-rule-changes/v2";
#[cfg(not(verus_keep_ghost))]
pub type Documents = BTreeMap<String, Value>;
#[cfg(not(verus_keep_ghost))]
pub use verified_classification::{
    Argument, DataCommand, Delta, Route, data_command, data_exit, delegation_failure, invocation,
    on_success, route,
};
#[cfg(not(verus_keep_ghost))]
mod classification;
#[cfg(not(verus_keep_ghost))]
pub use classification::Endpoint;
#[cfg(not(verus_keep_ghost))]
pub use classification::{document_paths, query as classify_query};

#[cfg(not(verus_keep_ghost))]
type Classification<'a> =
    policy::Classification<'a, policy::RuleChange<'a, Value>, policy::PathSurfaces<'a>>;

#[cfg(not(verus_keep_ghost))]
fn classify_endpoints<'a>(
    a: &'a Endpoint,
    b: &'a Endpoint,
    delta: &'a [Delta],
    before: &Documents,
    after: &Documents,
) -> Result<Classification<'a>, String> {
    let patterns: Vec<_> = a.patterns(b).into_iter().collect();
    let accumulated = verified_classification::classified_paths(delta.len(), |i| {
        let d = &delta[i];
        let old = a.surfaces.get(&d.path);
        let new = b.surfaces.get(&d.path);
        let Some(surfaces) =
            verified_classification::endpoints(old.map(String::as_str), new.map(String::as_str))
        else {
            return Err(format!(
                "E_SURFACE_REFERENCE: no registration for {}",
                d.path
            ));
        };
        let (old_doc, new_doc) = policy::document_pair(before, after, &d.path);
        let fields = policy::fields_for_path(
            &patterns,
            &d.path,
            old_doc,
            new_doc,
            a.workflow == d.path,
            b.workflow == d.path,
            policy::documents_available(
                d.old_blob.is_some(),
                old_doc.is_some(),
                d.new_blob.is_some(),
                new_doc.is_some(),
            ),
            |previous, current, pointer, on, left, right| {
                semantic::changes(previous, current, pointer, on, left, right)
            },
            |path| format!("E_SEMANTIC_INPUT: missing named document {path}"),
        )?;
        Ok(policy::surface_row(&d.path, old, new, surfaces, fields))
    })?;
    let (rule_paths, changes) = accumulated.rules.into_iter().unzip();
    let (product_paths, product_changes) = accumulated.products.into_iter().unzip();
    Ok(policy::classification(
        rule_paths,
        changes,
        product_paths,
        product_changes,
    ))
}
/// Publish the classification for the same interpreted inputs used by classify-v1.
#[cfg(not(verus_keep_ghost))]
pub fn produce(
    a: &Endpoint,
    b: &Endpoint,
    delta: &[Delta],
    before: &Documents,
    after: &Documents,
    costs: &Value,
) -> Result<Value, String> {
    serde_json::to_value(costed_classification(a, b, delta, before, after, costs)?)
        .map_err(|err| err.to_string())
}

#[cfg(not(verus_keep_ghost))]
fn costed_classification<'a>(
    a: &'a Endpoint,
    b: &'a Endpoint,
    delta: &'a [Delta],
    before: &Documents,
    after: &Documents,
    costs: &Value,
) -> Result<policy::Costed<Classification<'a>>, String> {
    let previous = &costs["declared_before"];
    let current = &costs["declared_after"];
    let valid = policy::cost_report_shape(
        costs["schema"].as_str(),
        previous.is_object(),
        current.is_object(),
    );
    checked_costs(
        valid,
        || "E_COST_INPUT: missing or unsupported cost report".to_owned(),
        || classify_endpoints(a, b, delta, before, after),
        || {
            let missing = policy::first_missing_cost(delta.len(), |i| {
                let node = format!("file:{}", delta[i].path);
                (previous.get(&node).is_some(), current.get(&node).is_some())
            });
            match missing {
                Some((index, side)) => Err(format!(
                    "E_COST_INPUT: {} lacks changed path file:{}",
                    side.field(),
                    delta[index].path
                )),
                None => Ok(()),
            }
        },
    )
}
