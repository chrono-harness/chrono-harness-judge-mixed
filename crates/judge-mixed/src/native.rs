//! Native judge data operations. The runner admits the sealed request and registration owns the Git reader.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::{Delta, Rule, classification, impact_schema, valid_modes, valid_surfaces};
#[cfg(not(verus_keep_ghost))]
use crate::{
    classification,
    verified_classification::{Delta, Rule, impact_schema},
};
use std::collections::BTreeMap;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub enum PlanFailure<E> { Contract(&'static str), Decode(E) }

/// Validate each entire endpoint, then the schema, before invoking the JSON
/// adapter. A successful value is the adapter's exact decoded DELTA.
pub fn plan_delta<E,D>(
    base_surface:&BTreeMap<String,String>, base_rules:&[Rule],
    candidate_surface:&BTreeMap<String,String>, candidate_rules:&[Rule],
    schema:Option<&str>, decode:D,
) -> (out:Result<Vec<Delta>,PlanFailure<E>>)
    where D:FnOnce()->Result<Vec<Delta>,E>,
    requires vstd::laws_cmp::obeys_cmp::<String>(), decode.requires(()),
    ensures ({
        let bs=valid_surfaces(base_surface@); let bm=valid_modes(base_rules@);
        let cs=valid_surfaces(candidate_surface@); let cm=valid_modes(candidate_rules@);
        let good_schema=match schema { Some(s)=>s@=="chrono-filemap-impact/v6"@, None=>false };
        if !(bs && bm && cs && cm && good_schema) {
            out matches Err(PlanFailure::Contract(e)) && (
                if !bs { e@=="E_SURFACE_REFERENCE: unknown surface"@ }
                else if !bm { e@=="E_SEMANTIC_INPUT: unknown semantic change mode"@ }
                else if !cs { e@=="E_SURFACE_REFERENCE: unknown surface"@ }
                else if !cm { e@=="E_SEMANTIC_INPUT: unknown semantic change mode"@ }
                else { e@=="E_IMPACT: unsupported schema"@ })
        } else {
            match out {
                Ok(delta)=>decode.ensures((),Ok::<Vec<Delta>,E>(delta)),
                Err(PlanFailure::Decode(error))=>decode.ensures((),Err::<Vec<Delta>,E>(error)),
                _=>false,
            }
        }
    }),
{
    if let Err(e) = classification::validate_endpoints(base_surface, base_rules, candidate_surface, candidate_rules) {
        return Err(PlanFailure::Contract(e));
    }
    if !impact_schema(schema) {return Err(PlanFailure::Contract("E_IMPACT: unsupported schema"));}
    match decode() { Ok(delta)=>Ok(delta), Err(e)=>Err(PlanFailure::Decode(e)) }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::{Documents, Endpoint, costed_classification};
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::io::Read;

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
pub fn plan(input: impl Read) -> Result<Value, String> {
    let q: PlanInput = classification::read(input)?;
    use crate::verified_classification::{bound_plan, same_delta};
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

#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CostContext {
    binding: Value,
    costs: Value,
}

#[cfg(not(verus_keep_ghost))]
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
