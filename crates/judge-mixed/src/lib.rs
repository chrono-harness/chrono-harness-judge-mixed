//! Explicit rule/product DELTA classification. Warnings neither authorize nor block work.
pub mod native;
mod semantic;
mod verified_classification;
use serde_json::Value;
use std::collections::BTreeMap;
use verified_classification as policy;
pub const MIXED_SCHEMA: &str = "chrono-rule-changes/v2";
pub type Documents = BTreeMap<String, Value>;
pub use verified_classification::{
    Argument, DataCommand, Delta, Route, data_command, data_exit, delegation_failure, invocation,
    on_success, route,
};
mod classification;
pub use classification::Endpoint;
pub use classification::{document_paths, query as classify_query};

type Classification<'a> =
    policy::Classification<'a, policy::RuleChange<'a, Value>, policy::PathSurfaces<'a>>;

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
    if !verified_classification::cost_report_shape(
        costs["schema"].as_str(),
        previous.is_object(),
        current.is_object(),
    ) {
        return Err("E_COST_INPUT: missing or unsupported cost report".into());
    }
    let output = classify_endpoints(a, b, delta, before, after)?;
    if let Some((index, side)) = verified_classification::first_missing_cost(delta.len(), |i| {
        let node = format!("file:{}", delta[i].path);
        (previous.get(&node).is_some(), current.get(&node).is_some())
    }) {
        return Err(format!(
            "E_COST_INPUT: {} lacks changed path file:{}",
            side.field(),
            delta[index].path
        ));
    }
    Ok(policy::costed(output))
}
