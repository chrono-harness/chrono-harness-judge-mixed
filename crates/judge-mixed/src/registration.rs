//! Read interpreted endpoints from the host-selected registration release.
use crate::{Documents, Endpoint};
use chrono_harness::{
    CommandSpec,
    wire::{Request, Response},
};
use serde::Deserialize;
use serde_json::Value;
use std::collections::BTreeSet;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Registered {
    pub endpoint: Endpoint,
    documents: Documents,
    pub warning_code: String,
}

impl Registered {
    pub fn documents(
        &mut self,
        paths: BTreeSet<String>,
        mut read: impl FnMut(&str) -> Result<Vec<u8>, String>,
    ) -> Result<Documents, String> {
        let mut selected = Documents::new();
        for path in paths {
            let value = match self.documents.remove(&path) {
                Some(value) => value,
                None => chrono_harness::decode(&read(&path)?)
                    .map_err(|error| format!("E_SEMANTIC_INPUT: {path}: {error}"))?,
            };
            selected.insert(path, value);
        }
        Ok(selected)
    }
}

#[derive(Deserialize)]
struct Reply {
    request_id: String,
    git_facts: Option<Value>,
    #[serde(flatten)]
    result: Outcome,
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Outcome {
    Rejected {
        error: String,
    },
    Ready {
        base: Registered,
        candidate: Registered,
    },
}

pub(super) fn query(
    req: &Request,
    response: &mut Response,
) -> Result<(Registered, Registered), String> {
    let config = chrono_harness::load_selected_config(&req.candidate.root, &req.config_path)?;
    let protocol = &config["protocol"];
    let env = req.observations["environment"]
        .get("effective")
        .map(|values| serde_json::from_value(values.clone()))
        .transpose()
        .map_err(|error| error.to_string())?
        .unwrap_or_default();
    let spec = CommandSpec {
        program: "chrono-judge-registration".into(),
        args: vec!["classification-views-v1".into()],
        env,
        timeout_seconds: protocol["timeout_seconds"]
            .as_u64()
            .ok_or("invalid registration timeout")?,
        output_limit_bytes: serde_json::from_value(protocol["stdout_limit_bytes"].clone())
            .map_err(|error| error.to_string())?,
    };
    let result = chrono_harness::run_process(&req.candidate.root, &spec, &req.canonical()?)?;
    if result.exit_code != 0 {
        return Err(format!(
            "registration classification-views-v1 exited {}: {}",
            result.exit_code,
            result.stderr.trim_end()
        ));
    }
    let reply: Reply = chrono_harness::decode(&result.stdout_bytes)?;
    if reply.request_id != req.request_id {
        return Err("E_PROTOCOL: registration query identity".into());
    }
    if let Some(facts) = reply.git_facts {
        response.outputs.insert("git_facts".into(), facts);
    }
    match reply.result {
        Outcome::Ready { base, candidate } => Ok((base, candidate)),
        Outcome::Rejected { error } => Err(error),
    }
}
