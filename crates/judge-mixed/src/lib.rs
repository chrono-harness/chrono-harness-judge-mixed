//! Explicit rule/product DELTA classification. Warnings neither authorize nor block work.
pub mod native;
mod semantic;
mod verified_classification;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeMap;
pub const MIXED_SCHEMA: &str = "chrono-rule-changes/v2";
pub type Documents = BTreeMap<String, Value>;
/// Serializable DELTA entries accepted by the versioned classification commands.
#[derive(Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Delta {
    pub kind: String,
    pub path: String,
    pub old_blob: Option<String>,
    pub new_blob: Option<String>,
    pub old_mode: Option<String>,
    pub new_mode: Option<String>,
}
mod classification;
pub use classification::Endpoint;
pub use classification::{document_paths, query as classify_query};

fn classify_endpoints(
    a: &Endpoint,
    b: &Endpoint,
    delta: &[Delta],
    before: &Documents,
    after: &Documents,
) -> Result<Value, String> {
    let patterns = a.patterns(b);
    let mut changes = BTreeMap::new();
    let mut products = BTreeMap::new();
    for d in delta {
        let old = a.surfaces.get(&d.path).cloned();
        let new = b.surfaces.get(&d.path).cloned();
        let Some(surfaces) = verified_classification::endpoints(old.as_deref(), new.as_deref())
        else {
            return Err(format!(
                "E_SURFACE_REFERENCE: no registration for {}",
                d.path
            ));
        };
        let mut fields = vec![];
        for (path, pointer, on) in patterns.iter().filter(|(p, _, _)| p == &d.path) {
            for (exists, docs) in [
                (d.old_blob.is_some(), before),
                (d.new_blob.is_some(), after),
            ] {
                if exists && !docs.contains_key(path) {
                    return Err(format!("E_SEMANTIC_INPUT: missing named document {path}"));
                }
            }
            fields.extend(semantic::changes(
                before.get(path),
                after.get(path),
                pointer,
                on,
                a.workflow == *path,
                b.workflow == *path,
            )?);
        }
        let classification = json!({"path":d.path,"before_surface":old,"after_surface":new});
        if surfaces.product {
            products.insert(d.path.clone(), classification.clone());
        }
        if surfaces.changes_rule(!fields.is_empty()) {
            let mut rule = classification;
            rule["whole_file"] = surfaces.whole_rule.into();
            rule["semantic"] = fields.into();
            changes.insert(d.path.clone(), rule);
        }
    }
    Ok(
        json!({"mixed":verified_classification::mixed(changes.len(), products.len()),
        "rule_paths":changes.keys().collect::<Vec<_>>(),"product_paths":products.keys().collect::<Vec<_>>(),
        "changes":changes.values().collect::<Vec<_>>(),"product_changes":products.values().collect::<Vec<_>>(),
        "requires_acknowledgement":false}),
    )
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
    if costs["schema"] != "chrono-costs/v1"
        || !costs["declared_before"].is_object()
        || !costs["declared_after"].is_object()
    {
        return Err("E_COST_INPUT: missing or unsupported cost report".into());
    }
    let mut output = classify_endpoints(a, b, delta, before, after)?;
    for d in delta {
        let node = format!("file:{}", d.path);
        for key in ["declared_before", "declared_after"] {
            if costs[key].get(&node).is_none() {
                return Err(format!("E_COST_INPUT: {key} lacks changed path {node}"));
            }
        }
    }
    output["schema"] = MIXED_SCHEMA.into();
    Ok(output)
}
