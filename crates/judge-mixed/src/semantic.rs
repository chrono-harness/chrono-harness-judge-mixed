//! Stable row identities are separate from physical JSON pointers.
use crate::verified_classification::{
    IdentityField, RowIdentity, matches_child, new_row, record_selection, requires_row_identity,
    retirement_rows, row_identity,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
fn escape(s: &str) -> String {
    s.replace('~', "~0").replace('/', "~1")
}
fn tokens(pointer: &str) -> Result<Vec<String>, String> {
    let tail = pointer
        .strip_prefix('/')
        .ok_or("E_SEMANTIC_POINTER: expected / prefix")?;
    tail.split('/')
        .map(|part| {
            let mut decoded = String::new();
            let mut chars = part.chars();
            while let Some(c) = chars.next() {
                decoded.push(if c == '~' {
                    match chars.next() {
                        Some('0') => '~',
                        Some('1') => '/',
                        _ => {
                            return Err(format!("E_SEMANTIC_POINTER: invalid escape in {pointer}"));
                        }
                    }
                } else {
                    c
                });
            }
            Ok(decoded)
        })
        .collect()
}
fn field<'a>(row: &'a Value, name: &str) -> IdentityField<'a> {
    match row.get(name) {
        None => IdentityField::Missing,
        Some(Value::String(s)) => IdentityField::Text(s),
        Some(_) => IdentityField::Invalid,
    }
}

fn row_ids(rows: &[Value], workflow_retirements: bool) -> Result<Option<Vec<String>>, String> {
    if !requires_row_identity(rows.len(), |i| {
        rows[i].get("id").is_some() || rows[i].get("path").is_some()
    }) {
        return Ok(None);
    }
    let mut seen = BTreeSet::new();
    let mut ids = vec![];
    for row in rows {
        let id = match row_identity(
            field(row, "id"),
            field(row, "path"),
            field(row, "kind"),
            workflow_retirements,
        )? {
            RowIdentity::Id(value) => format!("id:{value}"),
            RowIdentity::Path(value) => format!("path:{value}"),
            RowIdentity::Retirement(kind, value) => format!("retirement:{}", json!([kind, value])),
        };
        if !new_row(&mut seen, id.clone()) {
            return Err(format!("E_SEMANTIC_IDENTITY: duplicate {id}"));
        }
        ids.push(id);
    }
    Ok(Some(ids))
}
// Kind tags keep user objects distinct from the internal row-map representation.
fn normalized(value: &Value, pointer: &str, workflow: bool) -> Result<Value, String> {
    match value {
        Value::Object(map) => Ok(json!([
            "object",
            map.iter()
                .map(|(k, v)| Ok((
                    k.clone(),
                    normalized(v, &format!("{pointer}/{}", escape(k)), workflow)?
                )))
                .collect::<Result<BTreeMap<_, _>, String>>()?
        ])),
        Value::Array(rows) => {
            let values = rows
                .iter()
                .enumerate()
                .map(|(i, v)| normalized(v, &format!("{pointer}/{i}"), workflow))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(
                if let Some(ids) = row_ids(rows, retirement_rows(workflow, pointer))? {
                    json!([
                        "rows",
                        ids.into_iter().zip(values).collect::<BTreeMap<_, _>>()
                    ])
                } else {
                    json!(["array", values])
                },
            )
        }
        _ => Ok(json!(["scalar", value])),
    }
}
struct Selection {
    pointer: String,
    value: Value,
    normalized: Value,
}
type Selections = BTreeMap<Vec<String>, Selection>;
fn select(
    value: &Value,
    rest: &[String],
    pointer: String,
    identity: Vec<String>,
    out: &mut Selections,
    workflow: bool,
) -> Result<(), String> {
    if rest.is_empty() {
        let entry = Selection {
            normalized: normalized(value, &pointer, workflow)?,
            pointer,
            value: value.clone(),
        };
        return record_selection(out, identity, entry).map_err(String::from);
    }
    let token = &rest[0];
    match value {
        Value::Object(map) => {
            for (key, child) in map {
                if matches_child(token, key) {
                    let mut next = identity.clone();
                    next.push(format!("key:{key}"));
                    select(
                        child,
                        &rest[1..],
                        format!("{pointer}/{}", escape(key)),
                        next,
                        out,
                        workflow,
                    )?;
                }
            }
        }
        Value::Array(rows) => {
            let ids = row_ids(rows, retirement_rows(workflow, &pointer))?;
            for (i, child) in rows.iter().enumerate() {
                let index = i.to_string();
                if matches_child(token, &index) {
                    let mut next = identity.clone();
                    next.push(
                        ids.as_ref()
                            .map(|ids| ids[i].clone())
                            .unwrap_or_else(|| format!("index:{index}")),
                    );
                    select(
                        child,
                        &rest[1..],
                        format!("{pointer}/{index}"),
                        next,
                        out,
                        workflow,
                    )?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}
pub fn changes(
    before: Option<&Value>,
    after: Option<&Value>,
    pattern: &str,
    on: &str,
    before_workflow: bool,
    after_workflow: bool,
) -> Result<Vec<Value>, String> {
    let parts = tokens(pattern)?;
    let mut old = Selections::new();
    let mut new = Selections::new();
    if let Some(v) = before {
        select(v, &parts, String::new(), vec![], &mut old, before_workflow)?;
    }
    if let Some(v) = after {
        select(v, &parts, String::new(), vec![], &mut new, after_workflow)?;
    }
    let keys: BTreeSet<_> = old.keys().chain(new.keys()).collect();
    let mut changes = vec![];
    for key in keys {
        let a = old.get(key);
        let b = new.get(key);
        let equal_values =
            matches!((a, b), (Some(old), Some(new)) if old.normalized == new.normalized);
        if !crate::verified_classification::field_changed(
            on,
            a.is_some(),
            b.is_some(),
            equal_values,
        ) {
            continue;
        }
        let encode = |s: &Selection| json!({"pointer":s.pointer,"value":s.value});
        changes.push(json!({"pattern":pattern,"on":on,"identity":key,"before":a.map(encode),"after":b.map(encode)}));
    }
    Ok(changes)
}
