//! Native judge data operations. The runner admits the sealed request and registration owns the Git reader.
use crate::{Delta, Documents, Endpoint, classification, produce};
use serde::Deserialize;
use serde_json::{Value, json};
use std::io::Read;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PlanInput {
    base: Endpoint,
    candidate: Endpoint,
    delta: Vec<Delta>,
    impact: Value,
    prior_impacts: Vec<Value>,
    prior_costs: Vec<Value>,
    binding: Value,
}

pub fn plan(input: impl Read) -> Result<Value, String> {
    let q: PlanInput = classification::read(input)?;
    q.base.validate()?;
    q.candidate.validate()?;
    if q.impact["schema"] != "chrono-filemap-impact/v6" {
        return Err("E_IMPACT: unsupported schema".into());
    }
    let delta: Vec<Delta> =
        serde_json::from_value(q.impact["delta"].clone()).map_err(|e| format!("E_IMPACT: {e}"))?;
    if q.prior_impacts.is_empty()
        || q.prior_impacts.iter().any(|impact| *impact != q.impact)
        || delta != q.delta
    {
        return Err("E_IMPACT: missing or conflicting bound FILEMAP output".into());
    }
    let costs = q
        .prior_costs
        .first()
        .ok_or("E_COST_INPUT: missing predecessor costs")?;
    if q.prior_costs.iter().any(|other| other != costs) || costs["binding"] != q.binding {
        return Err(
            "E_COST_INPUT: conflicting costs or mismatched endpoint/context binding".into(),
        );
    }
    let [base, candidate] = classification::endpoint_paths(&q.base, &q.candidate, &q.delta);
    Ok(json!({"base":base,"candidate":candidate,"context":{"binding":q.binding,"costs":costs}}))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Report {
    base: Endpoint,
    candidate: Endpoint,
    delta: Vec<Delta>,
    before: Documents,
    after: Documents,
    warning_code: String,
    context: CostContext,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CostContext {
    binding: Value,
    costs: Value,
}

pub fn report(input: impl Read) -> Result<Value, String> {
    let q: Report = classification::read(input)?;
    let mut output = produce(
        &q.base,
        &q.candidate,
        &q.delta,
        &q.before,
        &q.after,
        &q.context.costs,
    )?;
    output["binding"] = q.context.binding;
    let mut findings = vec![];
    if output["mixed"] == true {
        let rules = output["rule_paths"].as_array().unwrap();
        let products = output["product_paths"].as_array().unwrap();
        findings.push(json!({"code":q.warning_code,"level":"warning","message":format!(
            "Rule and product changes share this DELTA. Rules: {}; products: {}. Before/after costs: predecessor outputs.costs (full report: /costs; provenance: /sources/~1costs); unknown coordinates remain unknown.",
            output["rule_paths"], output["product_paths"]
        ),"delta_refs":rules.iter().chain(products).collect::<Vec<_>>(),"causes":["/outputs/rule_changes"]}));
    }
    Ok(
        json!({"status":if findings.is_empty(){"pass"}else{"warn"},"findings":findings,"outputs":{"rule_changes":output}}),
    )
}
