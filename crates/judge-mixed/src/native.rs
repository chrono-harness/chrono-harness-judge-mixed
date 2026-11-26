//! Native judge data operations. The runner admits the sealed request and registration owns the Git reader.
use crate::{Delta, Documents, Endpoint, classification, costed_classification};
use serde::Deserialize;
use serde_json::Value;
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
    use crate::verified_classification::{PlanFailure, bound_plan, plan_delta, same_delta};
    let delta = plan_delta(
        &q.base.surfaces,
        &q.base.semantic_fields,
        &q.candidate.surfaces,
        &q.candidate.semantic_fields,
        q.impact["schema"].as_str(),
        || serde_json::from_value(q.impact["delta"].clone()),
    )
    .map_err(|failure| match failure {
        PlanFailure::Contract(reason) => reason.to_owned(),
        PlanFailure::Decode(error) => format!("E_IMPACT: {error}"),
    })?;
    let costs = crate::verified_classification::plan_predecessors(
        q.prior_impacts.len(),
        |i| q.prior_impacts[i] == q.impact,
        || same_delta(&delta, &q.delta),
        &q.prior_costs,
        |i| q.prior_costs[i] == q.prior_costs[0],
        || q.prior_costs[0]["binding"] == q.binding,
    )?;
    let paths = classification::endpoint_paths(&q.base, &q.candidate, &q.delta);
    serde_json::to_value(bound_plan(paths, &q.binding, costs)).map_err(|e| e.to_string())
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
    let costed = costed_classification(
        &q.base,
        &q.candidate,
        &q.delta,
        &q.before,
        &q.after,
        &q.context.costs,
    )?;
    let output = crate::verified_classification::bind_report(costed, q.context.binding);
    let rules = &output.changes.classification.rule_paths;
    let products = &output.changes.classification.product_paths;
    let report = crate::verified_classification::report_envelope(
        rules,
        products,
        &output,
        &q.warning_code,
        || {
            crate::verified_classification::warning_message(
                &serde_json::json!(rules).to_string(),
                &serde_json::json!(products).to_string(),
            )
        },
    );
    serde_json::to_value(report).map_err(|e| e.to_string())
}
