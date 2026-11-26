//! Explicit inputs to the classification used by the FILEMAP workflow selector.
use super::{Documents, classify_endpoints};
use crate::Delta;
use crate::verified_classification::{DocumentPaths, Rule, required_paths};
use serde::Deserialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Endpoint {
    pub(super) workflow: String,
    pub(super) surfaces: BTreeMap<String, String>,
    semantic_fields: Vec<Rule>,
}

impl Endpoint {
    pub(super) fn patterns(&self, other: &Self) -> BTreeSet<(String, String, String)> {
        self.semantic_fields
            .iter()
            .chain(&other.semantic_fields)
            .flat_map(|rule| {
                rule.pointers
                    .iter()
                    .map(|p| (rule.path.clone(), p.clone(), rule.on.clone()))
            })
            .collect()
    }

    pub(super) fn validate(&self) -> Result<(), String> {
        if self.surfaces.values().any(|s| {
            !matches!(
                s.as_str(),
                "product"
                    | "test"
                    | "documentation"
                    | "membership"
                    | "instruction-policy"
                    | "judge-policy"
                    | "judge-implementation"
            )
        }) {
            return Err("E_SURFACE_REFERENCE: unknown surface".into());
        }
        if self.semantic_fields.iter().any(|r| {
            !matches!(
                r.on.as_str(),
                "add-modify-delete" | "modify-delete-existing"
            )
        }) {
            return Err("E_SEMANTIC_INPUT: unknown semantic change mode".into());
        }
        Ok(())
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Query {
    base: Endpoint,
    candidate: Endpoint,
    delta: Vec<Delta>,
    before: Documents,
    after: Documents,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DocumentSelection {
    base: Vec<Rule>,
    candidate: Vec<Rule>,
    delta: Vec<Delta>,
}

pub(super) fn endpoint_paths<'a>(
    a: &'a Endpoint,
    b: &'a Endpoint,
    delta: &'a [Delta],
) -> DocumentPaths<'a> {
    required_paths(&a.semantic_fields, &b.semantic_fields, delta)
}

pub(crate) fn read<T: serde::de::DeserializeOwned>(input: impl Read) -> Result<T, String> {
    let mut bytes = Vec::new();
    input
        .take(crate::verified_classification::INPUT_LIMIT as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if !crate::verified_classification::admits_input(bytes.len()) {
        return Err("E_SEMANTIC_INPUT: input exceeds 64 MiB".into());
    }
    serde_json::from_slice(&bytes).map_err(|e| format!("E_SEMANTIC_INPUT: {e}"))
}

pub fn document_paths(input: impl Read) -> Result<Value, String> {
    let request: DocumentSelection = read(input)?;
    let paths = required_paths(&request.base, &request.candidate, &request.delta);
    serde_json::to_value(paths).map_err(|e| e.to_string())
}

/// Evaluate caller-provided endpoint data without inspecting the filesystem.
pub fn query(input: impl Read) -> Result<Value, String> {
    let q: Query = read(input)?;
    q.base.validate()?;
    q.candidate.validate()?;
    classify_endpoints(&q.base, &q.candidate, &q.delta, &q.before, &q.after)
}
