//! Explicit inputs to the classification used by the FILEMAP workflow selector.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::{Rule, valid_modes, valid_surfaces, validate_endpoint};
#[cfg(not(verus_keep_ghost))]
use crate::verified_classification::{Rule, validate_endpoint};
use std::collections::BTreeMap;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Both consumers report the first invalid endpoint in baseline, candidate order.
pub fn validate_endpoints(base: &BTreeMap<String, String>, base_rules: &[Rule],
    candidate: &BTreeMap<String, String>, candidate_rules: &[Rule]) -> (out: Result<(), &'static str>)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures
        out.is_ok() == (valid_surfaces(base@) && valid_modes(base_rules@)
            && valid_surfaces(candidate@) && valid_modes(candidate_rules@)),
        out matches Err(e) ==> e@ == (
            if !valid_surfaces(base@) { "E_SURFACE_REFERENCE: unknown surface"@ }
            else if !valid_modes(base_rules@) { "E_SEMANTIC_INPUT: unknown semantic change mode"@ }
            else if !valid_surfaces(candidate@) { "E_SURFACE_REFERENCE: unknown surface"@ }
            else { "E_SEMANTIC_INPUT: unknown semantic change mode"@ }),
{
    validate_endpoint(base, base_rules)?;
    validate_endpoint(candidate, candidate_rules)
}
}

#[cfg(not(verus_keep_ghost))]
use super::{Documents, classify_endpoints};
#[cfg(not(verus_keep_ghost))]
use crate::Delta;
#[cfg(not(verus_keep_ghost))]
use crate::verified_classification::{DocumentPaths, required_paths};
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeSet;
#[cfg(not(verus_keep_ghost))]
use std::io::Read;

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Endpoint {
    pub(super) workflow: String,
    pub(super) surfaces: BTreeMap<String, String>,
    pub(super) semantic_fields: Vec<Rule>,
}

#[cfg(not(verus_keep_ghost))]
impl Endpoint {
    pub(super) fn patterns(&self, other: &Self) -> BTreeSet<(String, String, String)> {
        crate::verified_classification::patterns(&self.semantic_fields, &other.semantic_fields)
    }
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Query {
    base: Endpoint,
    candidate: Endpoint,
    delta: Vec<Delta>,
    before: Documents,
    after: Documents,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DocumentSelection {
    base: Vec<Rule>,
    candidate: Vec<Rule>,
    delta: Vec<Delta>,
}

#[cfg(not(verus_keep_ghost))]
pub(super) fn endpoint_paths<'a>(
    a: &'a Endpoint,
    b: &'a Endpoint,
    delta: &'a [Delta],
) -> DocumentPaths<'a> {
    required_paths(&a.semantic_fields, &b.semantic_fields, delta)
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn read<T: serde::de::DeserializeOwned>(input: impl Read) -> Result<T, String> {
    crate::verified_classification::decode_input(
        || {
            let mut bytes = Vec::new();
            input
                .take(crate::verified_classification::INPUT_LIMIT as u64 + 1)
                .read_to_end(&mut bytes)
                .map_err(|e| e.to_string())?;
            Ok(bytes)
        },
        |bytes| serde_json::from_slice(&bytes).map_err(|e| format!("E_SEMANTIC_INPUT: {e}")),
        || "E_SEMANTIC_INPUT: input exceeds 64 MiB".to_owned(),
    )
}

#[cfg(not(verus_keep_ghost))]
pub fn document_paths(input: impl Read) -> Result<Value, String> {
    let request: DocumentSelection = read(input)?;
    let paths = required_paths(&request.base, &request.candidate, &request.delta);
    serde_json::to_value(paths).map_err(|e| e.to_string())
}

/// Evaluate caller-provided endpoint data without inspecting the filesystem.
#[cfg(not(verus_keep_ghost))]
pub fn query(input: impl Read) -> Result<Value, String> {
    let q: Query = read(input)?;
    validate_endpoints(
        &q.base.surfaces,
        &q.base.semantic_fields,
        &q.candidate.surfaces,
        &q.candidate.semantic_fields,
    )?;
    serde_json::to_value(classify_endpoints(
        &q.base,
        &q.candidate,
        &q.delta,
        &q.before,
        &q.after,
    )?)
    .map_err(|e| e.to_string())
}
