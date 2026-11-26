//! Stable row identities are separate from physical JSON pointers.
use crate::verified_classification::{
    IdentityField, RowIdentity, matches_child, record_selection, requires_row_identity,
    retirement_rows, row_identity,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

struct Members<'a>(serde_json::map::Iter<'a>);

impl<'a> crate::verified_classification::ObjectCursor<'a, Value> for Members<'a> {
    fn next_pair(&mut self) -> Option<(&'a String, &'a Value)> {
        self.0.next()
    }
}

fn child_pointer(parent: &str, key: &str) -> String {
    crate::verified_classification::child_pointer(parent, key)
        .into_iter()
        .collect()
}
fn tokens(pointer: &str) -> Result<Vec<String>, String> {
    use crate::verified_classification::{PointerError, decode_pointer};
    match decode_pointer(pointer) {
        Ok(parts) => Ok(parts.into_iter().map(String::from_iter).collect()),
        Err(PointerError::Prefix) => Err("E_SEMANTIC_POINTER: expected / prefix".into()),
        Err(PointerError::Escape) => {
            Err(format!("E_SEMANTIC_POINTER: invalid escape in {pointer}"))
        }
    }
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
    let ids = crate::verified_classification::row_keys(
        rows.len(),
        |i| {
            let row = &rows[i];
            Ok(
                match row_identity(
                    field(row, "id"),
                    field(row, "path"),
                    field(row, "kind"),
                    workflow_retirements,
                )? {
                    RowIdentity::Id(value) => format!("id:{value}"),
                    RowIdentity::Path(value) => format!("path:{value}"),
                    RowIdentity::Retirement(kind, value) => {
                        format!("retirement:{}", json!([kind, value]))
                    }
                },
            )
        },
        |key| format!("E_SEMANTIC_IDENTITY: duplicate {key}"),
    )?;
    Ok(Some(ids))
}
// Kind tags keep user objects distinct from the internal row-map representation.
fn normalized(value: &Value, pointer: &str, workflow: bool) -> Result<Value, String> {
    match value {
        Value::Object(map) => {
            let members = crate::verified_classification::object_members(
                Members(map.iter()),
                None,
                BTreeMap::new(),
                |key, child, mut members| {
                    let value = normalized(child, &child_pointer(pointer, key), workflow)?;
                    members.insert(key, value);
                    Ok::<_, String>(members)
                },
            )?;
            Ok(json!(["object", members]))
        }
        Value::Array(rows) => {
            let values = crate::verified_classification::children(rows.len(), |i| {
                normalized(&rows[i], &child_pointer(pointer, &i.to_string()), workflow)
            })?;
            let ids = row_ids(rows, retirement_rows(workflow, pointer))?;
            serde_json::to_value(crate::verified_classification::array_form(ids, values))
                .map_err(|e| e.to_string())
        }
        _ => Ok(json!(["scalar", value])),
    }
}
use crate::verified_classification::Selection;
type Selections = BTreeMap<Vec<String>, Selection<Value>>;
fn select(
    value: &Value,
    parts: &[String],
    depth: usize,
    pointer: String,
    identity: Vec<String>,
    out: &mut Selections,
    workflow: bool,
) -> Result<(), String> {
    let crate::verified_classification::Step::Child(token, next_depth) =
        crate::verified_classification::step(parts, depth)
    else {
        let entry = Selection {
            normalized: normalized(value, &pointer, workflow)?,
            pointer,
            value: value.clone(),
        };
        return record_selection(out, identity, entry).map_err(String::from);
    };
    match value {
        Value::Object(map) => {
            *out = crate::verified_classification::object_members(
                Members(map.iter()),
                Some(token),
                std::mem::take(out),
                |key, child, mut entries| {
                    let mut next = identity.clone();
                    next.push(crate::verified_classification::selection_identity(
                        true, key, None,
                    ));
                    select(
                        child,
                        parts,
                        next_depth,
                        child_pointer(&pointer, key),
                        next,
                        &mut entries,
                        workflow,
                    )?;
                    Ok::<_, String>(entries)
                },
            )?;
        }
        Value::Array(rows) => {
            let ids = row_ids(rows, retirement_rows(workflow, &pointer))?;
            *out = crate::verified_classification::indices(
                rows.len(),
                std::mem::take(out),
                |i, mut entries| {
                    let index = i.to_string();
                    if matches_child(token, &index) {
                        let mut next = identity.clone();
                        next.push(crate::verified_classification::selection_identity(
                            false,
                            &index,
                            ids.as_ref().map(|keys| keys[i].as_str()),
                        ));
                        select(
                            &rows[i],
                            parts,
                            next_depth,
                            child_pointer(&pointer, &index),
                            next,
                            &mut entries,
                            workflow,
                        )?;
                    }
                    Ok::<_, String>(entries)
                },
            )?;
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
    let (old, new) = crate::verified_classification::selected_sides(
        before,
        after,
        before_workflow,
        after_workflow,
        |value, workflow| {
            let mut selected = Selections::new();
            select(
                value,
                &parts,
                0,
                String::new(),
                vec![],
                &mut selected,
                workflow,
            )?;
            Ok::<_, String>(selected)
        },
    )?;
    let keys: Vec<_> = crate::verified_classification::selection_keys(&old, &new)
        .into_iter()
        .collect();
    Ok(crate::verified_classification::changed_items(
        &keys,
        |&key| {
            let difference = crate::verified_classification::difference(
                key,
                old.get(key),
                new.get(key),
                on,
                |before, after| before.normalized == after.normalized,
            )?;
            Some(json!(crate::verified_classification::semantic_change(
                pattern, on, difference
            )))
        },
    ))
}
