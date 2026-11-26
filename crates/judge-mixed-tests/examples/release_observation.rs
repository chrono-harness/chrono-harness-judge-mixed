//! Admission of the actual version, classification, and document-path outputs of the release binary.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub fn accepts(version: bool, mixed: Option<bool>, rules_empty: bool, products_empty: bool,
    doc_fields: usize, base_empty: bool, candidate_empty: bool) -> (ok: bool)
    ensures ok == (version && mixed == Some(false) && rules_empty && products_empty
        && doc_fields == 2 && base_empty && candidate_empty),
{
    version && matches!(mixed, Some(false)) && rules_empty && products_empty
        && doc_fields == 2 && base_empty && candidate_empty
}
}

#[cfg(not(verus_keep_ghost))]
fn empty_array(value: &serde_json::Value) -> bool {
    value.as_array().is_some_and(Vec::is_empty)
}

#[cfg(not(verus_keep_ghost))]
fn admitted(
    expected: &str,
    stdout: &[u8],
    classification: &serde_json::Value,
    documents: &serde_json::Value,
) -> bool {
    // grep -Fx accepted a complete version line anywhere in stdout, including an unterminated last line.
    let version = stdout
        .split(|b| *b == b'\n')
        .any(|line| line == expected.as_bytes());
    let Some(fields) = documents.as_object() else {
        return false;
    };
    accepts(
        version,
        classification["mixed"].as_bool(),
        empty_array(&classification["rule_paths"]),
        empty_array(&classification["product_paths"]),
        fields.len(),
        empty_array(&documents["base"]),
        empty_array(&documents["candidate"]),
    )
}

#[cfg(not(verus_keep_ghost))]
fn main() -> Result<(), String> {
    use std::fs;
    let args: Vec<_> = std::env::args().skip(1).collect();
    let [expected, version, classification, documents] = args.as_slice() else {
        return Err("usage: release_observation EXPECTED_VERSION VERSION_STDOUT CLASSIFICATION_STDOUT DOCUMENT_STDOUT".into());
    };
    let bytes = |path: &str| fs::read(path).map_err(|err| err.to_string());
    let json = |path: &str| serde_json::from_slice(&bytes(path)?).map_err(|err| err.to_string());
    if !admitted(
        expected,
        &bytes(version)?,
        &json(classification)?,
        &json(documents)?,
    ) {
        return Err("unexpected judge-mixed release output".into());
    }
    Ok(())
}

#[cfg(all(test, not(verus_keep_ghost)))]
#[test]
fn actual_fields_and_version_lines_determine_release_acceptance() {
    use serde_json::json;
    let class = json!({"mixed":false,"rule_paths":[],"product_paths":[],"other":"allowed"});
    let docs = json!({"base":[],"candidate":[]});
    assert!(admitted("v", b"prefix\nv\nsuffix", &class, &docs));
    assert!(admitted("v", b"v", &class, &docs));
    assert!(!admitted("v", b"xv", &class, &docs));
    assert!(!admitted("v", b"v\r\n", &class, &docs));
    for (key, bad) in [
        ("mixed", json!(true)),
        ("mixed", json!(null)),
        ("rule_paths", json!({})),
        ("product_paths", json!(["x"])),
    ] {
        let mut wrong = class.clone();
        wrong[key] = bad;
        assert!(!admitted("v", b"v", &wrong, &docs));
    }
    for wrong in [
        json!({"base":[]}),
        json!({"base":[],"candidate":["x"]}),
        json!({"base":{},"candidate":[]}),
        json!({"base":[],"candidate":[],"other":[]}),
    ] {
        assert!(!admitted("v", b"v", &class, &wrong));
    }
}
