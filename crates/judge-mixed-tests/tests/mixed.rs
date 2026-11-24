use chrono_judge_mixed::{Delta, Documents, Endpoint, produce};
use serde_json::{Value, json};

type Values = Documents;
const CONFIG: &str = "config.json";
const FM: &str = "files.json";
const PROJECTS: &str = "projects.json";
const WORKFLOW: &str = "workflow.json";

fn fixture() -> Values {
    let files: Vec<Value> = [
        ("src.bin", "product"),
        ("doc.txt", "documentation"),
        (CONFIG, "judge-policy"),
        (FM, "membership"),
        (PROJECTS, "membership"),
        (WORKFLOW, "judge-policy"),
    ]
    .iter()
    .map(|(path, surface)| json!({"path":path, "surface":surface, "edges":[]}))
    .collect();
    let project = |id| json!({"id":id, "actions":{"execute":{"argv":["build",id]}}});
    Documents::from([
        (
            CONFIG.into(),
            json!({"semantic_fields":[
                {"path":PROJECTS,"pointers":["/projects/*/actions","/scripts/*/actions"],"on":"add-modify-delete"},
                {"path":FM,"pointers":["/files/*/surface"],"on":"modify-delete-existing"}
            ]}),
        ),
        (FM.into(), json!({"files":files})),
        (
            PROJECTS.into(),
            json!({"projects":[project("app"),project("tests")],"scripts":[]}),
        ),
        (WORKFLOW.into(), json!({"retirements":[]})),
    ])
}

fn endpoint(docs: &Values) -> Endpoint {
    let surfaces: serde_json::Map<String, Value> = docs[FM]["files"]
        .as_array()
        .unwrap()
        .iter()
        .map(|file| {
            (
                file["path"].as_str().unwrap().to_owned(),
                file["surface"].clone(),
            )
        })
        .collect();
    serde_json::from_value(json!({"workflow":WORKFLOW,"surfaces":surfaces,
        "semantic_fields":docs[CONFIG]["semantic_fields"]}))
    .unwrap()
}

fn add_scripts(docs: &mut Values) {
    docs.get_mut(PROJECTS).unwrap()["scripts"] = json!([
        {"id":"script","path":"run.sh","actions":{"execute":{"argv":["run.sh"]}}},
        {"id":"test","path":"test.sh","actions":{"execute":{"argv":["test.sh"]}}}
    ]);
}
fn report(a: &Values, b: &Values, paths: &[&str]) -> Result<Value, String> {
    let old = endpoint(a);
    let new = endpoint(b);
    let changes = paths
        .iter()
        .map(|p| serde_json::from_value(delta(p)).unwrap())
        .collect::<Vec<_>>();
    let costs = fixture_costs(paths);
    let classified = produce(&old, &new, &changes, a, b, &costs)?;
    assert_eq!(classified["schema"], "chrono-rule-changes/v2");
    assert!(classified.get("costs").is_none());
    Ok(classified)
}

fn fixture_costs(paths: &[&str]) -> Value {
    let entries: serde_json::Map<String, Value> = paths
        .iter()
        .map(|p| (format!("file:{p}"), Value::Null))
        .collect();
    json!({"schema":"chrono-costs/v1","declared_before":entries,"declared_after":entries})
}
fn delta(path: &str) -> Value {
    json!({"kind":"M","path":path,"old_blob":"a".repeat(40),"new_blob":"b".repeat(40),
           "old_mode":"100644","new_mode":"100644"})
}

#[test]
fn ordinary_code_membership_and_edges_do_not_change_rules() {
    let a = fixture();
    let mut b = a.clone();
    b.get_mut(FM).unwrap()["files"]
        .as_array_mut()
        .unwrap()
        .push(json!({"path":"new.rs","surface":"product","edges":[]}));
    b.get_mut(FM).unwrap()["files"][0]["edges"]
        .as_array_mut()
        .unwrap()
        .push(json!({"kind":"runtime-input","to":"project:p"}));
    let r = report(&a, &b, &["src.bin", FM]).unwrap();
    assert_eq!(r["mixed"], false);
    assert_eq!(r["rule_paths"], json!([]));
    assert_eq!(r["product_paths"], json!(["src.bin"]));
}

#[test]
fn true_action_change_is_mixed() {
    let a = fixture();
    let mut b = a.clone();
    b.get_mut(PROJECTS).unwrap()["projects"][0]["actions"]["execute"]["argv"] =
        json!(["-c", "exit 1"]);
    let r = report(&a, &b, &["src.bin", PROJECTS]).unwrap();
    assert_eq!(r["mixed"], true);
    assert_eq!(r["rule_paths"], json!([PROJECTS]));
    assert_eq!(r["product_paths"], json!(["src.bin"]));
    assert_eq!(
        r["changes"][0]["semantic"][0]["before"]["pointer"],
        "/projects/0/actions"
    );
}

#[test]
fn policy_only_product_only_and_empty_are_not_mixed() {
    let a = fixture();
    for (paths, rules, products) in [
        (vec![CONFIG], vec![CONFIG], vec![]),
        (vec!["src.bin"], vec![], vec!["src.bin"]),
        (vec![], vec![], vec![]),
    ] {
        let r = report(&a, &a, &paths).unwrap();
        assert_eq!(r["mixed"], false);
        assert_eq!(r["rule_paths"], json!(rules));
        assert_eq!(r["product_paths"], json!(products));
    }
}

#[test]
fn old_surfaces_survive_reclassification_and_deleted_files() {
    let mut a = fixture();
    a.get_mut(FM).unwrap()["files"][0]["surface"] = "judge-implementation".into();
    let mut b = a.clone();
    b.get_mut(FM).unwrap()["files"][0]["surface"] = "product".into();
    let r = report(&a, &b, &["src.bin", FM]).unwrap();
    assert!(
        r["rule_paths"]
            .as_array()
            .unwrap()
            .contains(&json!("src.bin"))
    );
    assert_eq!(r["mixed"], true);
    b.get_mut(FM).unwrap()["files"]
        .as_array_mut()
        .unwrap()
        .retain(|f| f["path"] != "src.bin");
    let r = report(&a, &b, &["src.bin", FM]).unwrap();
    assert!(
        r["rule_paths"]
            .as_array()
            .unwrap()
            .contains(&json!("src.bin"))
    );
}

#[test]
fn row_reorder_is_neutral_but_ordered_arguments_change_rules() {
    let a = fixture();
    let mut b = a.clone();
    b.get_mut(PROJECTS).unwrap()["projects"]
        .as_array_mut()
        .unwrap()
        .reverse();
    b.get_mut(FM).unwrap()["files"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let r = report(&a, &b, &["src.bin", FM, PROJECTS]).unwrap();
    assert_eq!(r["rule_paths"], json!([]));
    b.get_mut(PROJECTS).unwrap()["projects"][0]["actions"]["execute"]["argv"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let r = report(&a, &b, &["src.bin", PROJECTS]).unwrap();
    assert_eq!(r["mixed"], true);
    assert_eq!(
        r["changes"][0]["semantic"][0]["before"]["pointer"],
        "/projects/1/actions"
    );
    assert_eq!(
        r["changes"][0]["semantic"][0]["after"]["pointer"],
        "/projects/0/actions"
    );
}

#[test]
fn script_identity_precedes_path_and_actions_added_are_semantic() {
    let mut a = fixture();
    add_scripts(&mut a);
    let mut b = a.clone();
    b.get_mut(PROJECTS).unwrap()["scripts"][0]["path"] = "other.sh".into();
    b.get_mut(PROJECTS).unwrap()["scripts"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let r = report(&a, &b, &["src.bin", PROJECTS]).unwrap();
    assert_eq!(r["rule_paths"], json!([]));
    b.get_mut(PROJECTS).unwrap()["scripts"][0]["actions"]["execute"]["argv"] =
        json!(["changed.sh"]);
    assert_eq!(
        report(&a, &b, &["src.bin", PROJECTS]).unwrap()["mixed"],
        true
    );
    let a = fixture();
    let mut b = a.clone();
    add_scripts(&mut b);
    assert_eq!(
        report(&a, &b, &["src.bin", PROJECTS]).unwrap()["mixed"],
        true
    );
}

#[test]
fn explicit_wildcards_escaped_keys_null_removal_and_named_documents() {
    let mut a = fixture();
    a.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([{"path":"rules.json","pointers":["/a~1b/~0key/*/value"],"on":"modify-delete-existing"}]);
    let f = json!({"path":"rules.json","surface":"membership"});
    a.get_mut(FM).unwrap()["files"]
        .as_array_mut()
        .unwrap()
        .push(f);
    a.insert(
        "rules.json".into(),
        json!({"a/b":{"~key":{"one":{"value":null},"two":{"nested":{"value":1}}}}}),
    );
    let mut b = a.clone();
    b.get_mut("rules.json").unwrap()["a/b"]["~key"]["two"]["nested"]["value"] = 2.into();
    b.get_mut("rules.json").unwrap()["a/b"]["~key"]["new"] = json!({"value":2});
    assert_eq!(
        report(&a, &b, &["src.bin", "rules.json"]).unwrap()["mixed"],
        false
    );
    b.get_mut("rules.json").unwrap()["a/b"]["~key"]["one"]
        .as_object_mut()
        .unwrap()
        .remove("value");
    let r = report(&a, &b, &["src.bin", "rules.json"]).unwrap();
    assert_eq!(r["mixed"], true);
    assert_eq!(
        r["changes"][0]["semantic"][0]["before"]["pointer"],
        "/a~1b/~0key/one/value"
    );
    assert!(r["changes"][0]["semantic"][0]["before"]["value"].is_null());
    assert!(r["changes"][0]["semantic"][0]["after"].is_null());
}

#[test]
fn old_patterns_survive_removal_and_invalid_pointers_or_ambiguous_rows_fail() {
    let a = fixture();
    let mut b = a.clone();
    b.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([]);
    b.get_mut(PROJECTS).unwrap()["projects"][0]["actions"]["execute"]["argv"] =
        json!(["different"]);
    assert_eq!(
        report(&a, &b, &["src.bin", PROJECTS]).unwrap()["mixed"],
        true
    );
    let mut a = fixture();
    a.get_mut(CONFIG).unwrap()["semantic_fields"][0]["pointers"] = json!(["/projects/~2bad"]);
    assert!(
        report(&a, &a, &[PROJECTS])
            .unwrap_err()
            .contains("E_SEMANTIC_POINTER")
    );
    let mut a = fixture();
    a.get_mut(CONFIG).unwrap()["semantic_fields"] =
        json!([{"path":"doc.txt","pointers":["/rows"],"on":"add-modify-delete"}]);
    a.insert(
        "doc.txt".into(),
        json!({"rows":[{"id":"same","x":1},{"id":"same","x":2}]}),
    );
    assert!(
        report(&a, &a, &["doc.txt"])
            .unwrap_err()
            .contains("E_SEMANTIC_IDENTITY")
    );
}

#[test]
fn workflow_retirements_use_typed_identity_without_losing_either_obligation() {
    for pointer in [
        "/retirements",
        "/retirements/*",
        "/retirements/*/replacement",
    ] {
        let mut a = fixture();
        a.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([
            {"path":WORKFLOW,"pointers":[pointer],"on":"add-modify-delete"}
        ]);
        a.get_mut(WORKFLOW).unwrap()["retirements"] = json!([
            {"kind":"test","id":"shared","replacement":"t","reason":"test obligation"},
            {"kind":"script","id":"shared","replacement":"s","reason":"script obligation"}
        ]);
        let classify = |b: &Values| report(&a, b, &[WORKFLOW]);
        let mut reordered = a.clone();
        reordered.get_mut(WORKFLOW).unwrap()["retirements"]
            .as_array_mut()
            .unwrap()
            .reverse();
        assert!(
            classify(&reordered).unwrap()["changes"][0]["semantic"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        for index in 0..2 {
            let mut changed = a.clone();
            changed.get_mut(WORKFLOW).unwrap()["retirements"][index]["replacement"] =
                json!("other");
            assert_eq!(
                classify(&changed).unwrap()["changes"][0]["semantic"]
                    .as_array()
                    .unwrap()
                    .len(),
                1
            );
            let mut removed = a.clone();
            removed.get_mut(WORKFLOW).unwrap()["retirements"]
                .as_array_mut()
                .unwrap()
                .remove(index);
            let result = classify(&removed).unwrap();
            let fields = result["changes"][0]["semantic"].as_array().unwrap();
            assert_eq!(fields.len(), 1);
            assert!(fields[0]["after"].is_null() || pointer == "/retirements");
            let mut duplicate = a.clone();
            let row = duplicate[WORKFLOW]["retirements"][index].clone();
            duplicate.get_mut(WORKFLOW).unwrap()["retirements"]
                .as_array_mut()
                .unwrap()
                .push(row);
            assert!(
                classify(&duplicate)
                    .unwrap_err()
                    .contains("E_SEMANTIC_IDENTITY")
            );
        }
    }
}

#[test]
fn retirement_key_errors_preserve_the_first_diagnostic() {
    let mut base = fixture();
    base.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([
        {"path":WORKFLOW,"pointers":["/retirements"],"on":"add-modify-delete"}
    ]);
    for (row, diagnostic) in [
        (
            json!({"id":null,"path":"fallback","kind":"test"}),
            "mixed or invalid path/id rows",
        ),
        (
            json!({"id":"","kind":null}),
            "mixed or invalid path/id rows",
        ),
        (json!({"path":"x","kind":""}), "invalid retirement kind"),
        (json!({"path":"x","kind":"test"}), "retirement requires id"),
    ] {
        base.get_mut(WORKFLOW).unwrap()["retirements"] = json!([row]);
        assert_eq!(
            report(&base, &base, &[WORKFLOW]).unwrap_err(),
            format!("E_SEMANTIC_IDENTITY: {diagnostic}")
        );
    }
}

#[test]
fn kind_fields_do_not_weaken_id_uniqueness_outside_workflow_retirements() {
    let mut a = fixture();
    a.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([
        {"path":"doc.txt","pointers":["/retirements"],"on":"add-modify-delete"}
    ]);
    a.insert(
        "doc.txt".into(),
        json!({"retirements":[
            {"kind":"test","id":"shared"}, {"kind":"script","id":"shared"}
        ]}),
    );
    assert!(
        report(&a, &a, &["doc.txt"])
            .unwrap_err()
            .contains("E_SEMANTIC_IDENTITY")
    );
}

#[test]
fn selected_row_subtrees_ignore_reordering_but_operation_sequences_keep_order() {
    let mut a = fixture();
    a.get_mut(CONFIG).unwrap()["semantic_fields"] = json!([{
        "path":"doc.txt","pointers":["/rows","/operations"],"on":"add-modify-delete"}]);
    a.insert("doc.txt".into(), json!({"rows":[{"path":"one","mode":1},{"path":"two","mode":2}],"operations":["build","test"]}));
    let mut b = a.clone();
    b.get_mut("doc.txt").unwrap()["rows"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(
        report(&a, &b, &["src.bin", "doc.txt"]).unwrap()["mixed"],
        false
    );
    b.get_mut("doc.txt").unwrap()["operations"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let r = report(&a, &b, &["src.bin", "doc.txt"]).unwrap();
    assert_eq!(r["mixed"], true);
    assert_eq!(r["changes"][0]["semantic"][0]["pattern"], "/operations");
}

#[test]
fn missing_named_documents_and_incomplete_costs_are_errors_without_fallback() {
    let a = fixture();
    let old = endpoint(&a);
    let changes = [serde_json::from_value(delta(PROJECTS)).unwrap()];
    let mut costs = fixture_costs(&[PROJECTS]);
    let mut missing = a.clone();
    missing.remove(PROJECTS);
    assert!(
        produce(&old, &old, &changes, &a, &missing, &costs)
            .unwrap_err()
            .contains("E_SEMANTIC_INPUT")
    );
    costs["declared_after"]
        .as_object_mut()
        .unwrap()
        .remove(&format!("file:{PROJECTS}"));
    assert!(
        produce(&old, &old, &changes, &a, &a, &costs)
            .unwrap_err()
            .contains("E_COST_INPUT")
    );
}

#[test]
fn costs_report_the_first_missing_endpoint_in_delta_order() {
    let docs = fixture();
    let end = endpoint(&docs);
    let paths = [PROJECTS, WORKFLOW];
    let changes: Vec<_> = paths
        .iter()
        .map(|path| serde_json::from_value(delta(path)).unwrap())
        .collect();
    let base = fixture_costs(&paths);
    let run = |costs: &Value, items: &[Delta]| produce(&end, &end, items, &docs, &docs, costs);
    assert!(run(&base, &changes).is_ok());
    assert!(run(&base, &[]).is_ok());
    for (before, after, expected) in [
        (
            vec![PROJECTS],
            vec![],
            format!("declared_before lacks changed path file:{PROJECTS}"),
        ),
        (
            vec![],
            vec![WORKFLOW],
            format!("declared_after lacks changed path file:{WORKFLOW}"),
        ),
        (
            vec![PROJECTS],
            vec![PROJECTS],
            format!("declared_before lacks changed path file:{PROJECTS}"),
        ),
        (
            vec![WORKFLOW],
            vec![PROJECTS],
            format!("declared_after lacks changed path file:{PROJECTS}"),
        ),
    ] {
        let mut costs = base.clone();
        for (side, missing) in [("declared_before", before), ("declared_after", after)] {
            for path in missing {
                costs[side]
                    .as_object_mut()
                    .unwrap()
                    .remove(&format!("file:{path}"));
            }
        }
        assert_eq!(
            run(&costs, &changes).unwrap_err(),
            format!("E_COST_INPUT: {expected}")
        );
    }
    for field in ["schema", "declared_before", "declared_after"] {
        let mut invalid = base.clone();
        invalid[field] = Value::Null;
        assert_eq!(
            run(&invalid, &[]).unwrap_err(),
            "E_COST_INPUT: missing or unsupported cost report"
        );
    }
}

#[test]
fn data_query_classifies_only_declared_changes_and_rejects_missing_inputs() {
    let endpoint = json!({
        "workflow": "workflow.json",
        "surfaces": {"a.rs": "product", "settings.json": "membership"},
        "semantic_fields": [
            {"path":"settings.json", "pointers":["/rule"], "on":"add-modify-delete"}
        ],
    });
    let mut input = json!({
        "base": endpoint, "candidate": endpoint, "delta": [delta("settings.json"), delta("a.rs")],
        "before": {"settings.json":{"rule":"old"}}, "after": {"settings.json":{"rule":"new"}},
    });
    let query = |input: &Value| {
        let raw = serde_json::to_vec(input).unwrap();
        chrono_judge_mixed::classify_query(raw.as_slice())
    };
    let result = query(&input).unwrap();
    assert_eq!(result["mixed"], true);
    assert_eq!(result["rule_paths"], json!(["settings.json"]));
    assert_eq!(result["product_paths"], json!(["a.rs"]));
    assert_eq!(
        result["changes"][0]["semantic"][0]["before"]["value"],
        "old"
    );
    input["after"] = json!({});
    assert!(
        query(&input)
            .unwrap_err()
            .contains("missing named document settings.json")
    );
    input["candidate"]["semantic_fields"][0]["on"] = json!("unknown");
    assert!(
        query(&input)
            .unwrap_err()
            .contains("unknown semantic change mode")
    );
}

#[test]
fn document_selection_uses_rules_from_both_ends_and_present_blobs() {
    let mut removed = delta("old");
    removed["new_blob"] = Value::Null;
    let mut added = delta("new");
    added["old_blob"] = Value::Null;
    let rule = |path| json!({"path":path, "pointers":["/value"], "on":"modify-delete-existing"});
    let raw = serde_json::to_vec(&json!({
        "base":[rule("old")], "candidate":[rule("new")],
        "delta":[removed, added, delta("unrelated")],
    }))
    .unwrap();
    assert_eq!(
        chrono_judge_mixed::document_paths(raw.as_slice()).unwrap(),
        json!({"base":["old"],"candidate":["new"]})
    );
}

#[test]
fn native_plan_requires_matching_predecessors_before_selecting_documents() {
    let change = delta(PROJECTS);
    let fields = fixture()[CONFIG]["semantic_fields"].clone();
    let end =
        json!({"workflow":WORKFLOW,"surfaces":{PROJECTS:"membership"},"semantic_fields":fields});
    let impact = json!({"schema":"chrono-filemap-impact/v6","delta":[change]});
    let binding = json!({"base":"a","candidate":"b","candidate_tree":"c","registry_digest":"d","context_digest":"e"});
    let mut costs = fixture_costs(&[PROJECTS]);
    costs["binding"] = binding.clone();
    let q = json!({"base":end,"candidate":end,"delta":[change],"impact":impact,
        "prior_impacts":[impact],"prior_costs":[costs],"binding":binding});
    let plan =
        |q: &Value| chrono_judge_mixed::native::plan(serde_json::to_vec(q).unwrap().as_slice());
    assert_eq!(
        plan(&q).unwrap(),
        json!({"base":[PROJECTS],"candidate":[PROJECTS],"context":{"binding":binding,"costs":costs}})
    );
    for (field, value, error) in [
        ("prior_impacts", json!([]), "E_IMPACT"),
        ("prior_costs", json!([]), "E_COST_INPUT"),
        ("binding", json!({}), "E_COST_INPUT"),
    ] {
        let mut bad = q.clone();
        bad[field] = value;
        assert!(plan(&bad).unwrap_err().starts_with(error));
    }
    for (field, value) in [
        ("kind", json!("D")),
        ("path", json!("other")),
        ("old_blob", Value::Null),
        ("new_blob", Value::Null),
        ("old_mode", Value::Null),
        ("new_mode", Value::Null),
    ] {
        let mut bad = q.clone();
        bad["delta"][0][field] = value;
        assert!(plan(&bad).unwrap_err().starts_with("E_IMPACT"));
    }
}
