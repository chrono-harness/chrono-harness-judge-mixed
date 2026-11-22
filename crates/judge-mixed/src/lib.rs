//! Explicit rule/product DELTA classification. Warnings neither authorize nor block work.
mod git_observations;
mod registration;
mod semantic;
use chrono_harness::{
    facts,
    wire::{Delta, Finding, Request, Response, Status},
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
pub const MIXED_SCHEMA: &str = "chrono-rule-changes/v2";
pub type Documents = BTreeMap<String, Value>;
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
        let surfaces: BTreeSet<_> = old.iter().chain(new.iter()).map(String::as_str).collect();
        if surfaces.is_empty() {
            return Err(format!(
                "E_SURFACE_REFERENCE: no registration for {}",
                d.path
            ));
        }
        let executable_rule = surfaces
            .iter()
            .any(|s| matches!(*s, "judge-policy" | "judge-implementation"));
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
        let is_product = surfaces.iter().any(|s| matches!(*s, "product" | "test"));
        let classification = json!({"path":d.path,"before_surface":old,"after_surface":new});
        if is_product {
            products.insert(d.path.clone(), classification.clone());
        }
        if executable_rule || !fields.is_empty() {
            let mut rule = classification;
            rule["whole_file"] = executable_rule.into();
            rule["semantic"] = fields.into();
            changes.insert(d.path.clone(), rule);
        }
    }
    Ok(json!({"mixed":!changes.is_empty()&&!products.is_empty(),
        "rule_paths":changes.keys().collect::<Vec<_>>(),"product_paths":products.keys().collect::<Vec<_>>(),
        "changes":changes.values().collect::<Vec<_>>(),"product_changes":products.values().collect::<Vec<_>>(),
        "requires_acknowledgement":false}))
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
fn evaluate(req: &Request, response: &mut Response) -> Result<(Value, String), String> {
    req.validate()?;
    let (mut base, mut candidate) = registration::query(req, response)?;
    base.endpoint.validate()?;
    candidate.endpoint.validate()?;
    if req.impact["schema"] != "chrono-filemap-impact/v6" {
        return Err("E_IMPACT: unsupported schema".into());
    }
    let delta: Vec<Delta> = serde_json::from_value(req.impact["delta"].clone())
        .map_err(|e| format!("E_IMPACT: {e}"))?;
    let sources: Vec<_> = req
        .prior_results
        .iter()
        .filter_map(|r| r.outputs.get("impact"))
        .collect();
    if sources.is_empty() || sources.iter().any(|v| **v != req.impact) || delta != req.delta {
        return Err("E_IMPACT: missing or conflicting bound FILEMAP output".into());
    }
    let binding = json!({"base":req.base.commit,"candidate":req.candidate.commit,
        "candidate_tree":req.candidate.tree,"registry_digest":req.registries.digest,"context_digest":req.context.sha256});
    let sources: Vec<_> = req
        .prior_results
        .iter()
        .filter_map(|r| r.outputs.get("costs"))
        .collect();
    let costs = *sources
        .first()
        .ok_or("E_COST_INPUT: missing predecessor costs")?;
    if sources.iter().any(|c| **c != *costs) || costs["binding"] != binding {
        return Err(
            "E_COST_INPUT: conflicting costs or mismatched endpoint/context binding".into(),
        );
    }
    let [old_paths, new_paths] =
        classification::endpoint_paths(&base.endpoint, &candidate.endpoint, &delta);
    let mut reader = None;
    let mut read = |commit: &str, path: &str| {
        if reader.is_none() {
            reader = Some(facts::Reader::for_request(req)?);
        }
        reader
            .as_ref()
            .unwrap()
            .blob(&req.candidate.root, commit, path)
    };
    let docs = (|| {
        let before = base.documents(old_paths, |p| read(&req.base.commit, p))?;
        let after = candidate.documents(new_paths, |p| read(&req.candidate.commit, p))?;
        Ok::<_, String>((before, after))
    })();
    if let Some(reader) = reader {
        git_observations::append(response.outputs.get_mut("git_facts"), reader.observation())?;
    }
    let (before, after) = docs?;
    let mut output = produce(
        &base.endpoint,
        &candidate.endpoint,
        &req.delta,
        &before,
        &after,
        costs,
    )?;
    output["binding"] = binding;
    Ok((output, candidate.warning_code))
}
pub fn judge(req: &Request) -> Response {
    let mut response = req.response(Status::Pass);
    let result = evaluate(req, &mut response);
    match result {
        Ok((output, code)) => {
            if output["mixed"] == true {
                chrono_harness::wire::append_finding(
                    &mut response.status,
                    &mut response.findings,
                    Status::Warn,
                    Finding {
                        code,
                        level: "warning".into(),
                        message: format!(
                            "Rule and product changes share this DELTA. Rules: {}; products: {}. Before/after costs: predecessor outputs.costs (full report: /costs; provenance: /sources/~1costs); unknown coordinates remain unknown.",
                            output["rule_paths"], output["product_paths"]
                        ),
                        delta_refs: output["rule_paths"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .chain(output["product_paths"].as_array().unwrap())
                            .map(|v| v.as_str().unwrap().into())
                            .collect(),
                        causes: vec!["/outputs/rule_changes".into()],
                    },
                );
            }
            response.outputs.insert("rule_changes".into(), output);
        }
        Err(message) => {
            chrono_harness::wire::append_finding(
                &mut response.status,
                &mut response.findings,
                Status::Error,
                Finding {
                    code: message
                        .split(':')
                        .next()
                        .filter(|c| c.starts_with("E_"))
                        .unwrap_or("E_INPUT")
                        .into(),
                    level: "error".into(),
                    message,
                    delta_refs: vec!["/request".into()],
                    causes: vec![],
                },
            );
        }
    }
    response
}
