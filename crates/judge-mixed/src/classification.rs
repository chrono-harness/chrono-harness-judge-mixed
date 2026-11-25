//! Explicit inputs to the classification used by the FILEMAP workflow selector.
use super::{Documents, classify_endpoints};
use crate::Delta;
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

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Rule {
    path: String,
    pointers: Vec<String>,
    on: String,
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

fn required_paths<'a>(
    base: &'a [Rule],
    candidate: &'a [Rule],
    delta: &'a [Delta],
) -> [BTreeSet<&'a str>; 2] {
    let mut named = BTreeSet::new();
    for rule in base.iter().chain(candidate) {
        crate::verified_classification::register_document(
            &mut named,
            rule.path.as_str(),
            rule.pointers.len(),
        );
    }
    let mut before = BTreeSet::new();
    let mut after = BTreeSet::new();
    for change in delta {
        crate::verified_classification::select_document(
            &named,
            &mut before,
            &mut after,
            change.path.as_str(),
            change.old_blob.is_some(),
            change.new_blob.is_some(),
        );
    }
    [before, after]
}

pub(super) fn endpoint_paths<'a>(
    a: &'a Endpoint,
    b: &'a Endpoint,
    delta: &'a [Delta],
) -> [BTreeSet<&'a str>; 2] {
    required_paths(&a.semantic_fields, &b.semantic_fields, delta)
}

pub(crate) fn read<T: serde::de::DeserializeOwned>(input: impl Read) -> Result<T, String> {
    let mut bytes = Vec::new();
    const LIMIT: u64 = 64 * 1024 * 1024;
    input
        .take(LIMIT + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() as u64 > LIMIT {
        return Err("E_SEMANTIC_INPUT: input exceeds 64 MiB".into());
    }
    serde_json::from_slice(&bytes).map_err(|e| format!("E_SEMANTIC_INPUT: {e}"))
}

pub fn document_paths(input: impl Read) -> Result<Value, String> {
    let request: DocumentSelection = read(input)?;
    let [base, candidate] = required_paths(&request.base, &request.candidate, &request.delta);
    Ok(serde_json::json!({"base":base,"candidate":candidate}))
}

/// Evaluate caller-provided endpoint data without inspecting the filesystem.
pub fn query(input: impl Read) -> Result<Value, String> {
    let q: Query = read(input)?;
    q.base.validate()?;
    q.candidate.validate()?;
    classify_endpoints(&q.base, &q.candidate, &q.delta, &q.before, &q.after)
}
