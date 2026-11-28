//! Stable row identities are separate from physical JSON pointers.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::IdentityField;
#[cfg(not(verus_keep_ghost))]
use crate::verified_classification::IdentityField;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use vstd::string::StringExecFns;

#[cfg(verus_keep_ghost)]
use super::{
    ArrayForm, ObjectCursor, RowIdentity, Step, array_form, children, indices, matches_child,
    matching_predecessors, object_members, processed, requires_row_identity, retirement_rows,
    row_identity, row_keys, selection_identity, step,
};
#[cfg(not(verus_keep_ghost))]
use crate::verified_classification::{
    ArrayForm, Step, array_form, children, indices, matches_child, matching_predecessors,
    object_members, requires_row_identity, retirement_rows, row_identity, row_keys,
    selection_identity, step,
};
use std::collections::BTreeMap;

verus! {
/// Keep missing, present non-string, and actual text distinct at the JSON row boundary.
pub fn identity_field(value: Option<Option<&str>>) -> (out: IdentityField<'_>)
    ensures match value {
        None => out is Missing,
        Some(None) => out is Invalid,
        Some(Some(text)) => out matches IdentityField::Text(actual) && actual == text,
    },
{
    match value {
        None => IdentityField::Missing,
        Some(None) => IdentityField::Invalid,
        Some(Some(text)) => IdentityField::Text(text),
    }
}
// The JSON adapter lends the actual node and its children without deciding how to visit them.
pub enum Node<'a, C, V> {
    Object(C),
    Array(&'a [V]),
    Scalar(&'a V),
}

/// Render the namespace independently from JSON escaping of the retirement pair.
pub fn identity_key<'a, R>(id: RowIdentity<'a>, encode_pair: &R) -> (key: String)
    where R: Fn(&'a str, &'a str) -> String,
    requires forall|kind: &'a str, id: &'a str| encode_pair.requires((kind, id)),
    ensures match id {
        RowIdentity::Id(value) => key@ == "id:"@ + value@,
        RowIdentity::Path(value) => key@ == "path:"@ + value@,
        RowIdentity::Retirement(kind, value) => exists|encoded: String|
            #[trigger] encode_pair.ensures((kind, value), encoded)
                && key@ == "retirement:"@ + encoded@,
    },
{
    let (prefix, value) = match id {
        RowIdentity::Id(value) => ("id:", value),
        RowIdentity::Path(value) => ("path:", value),
        RowIdentity::Retirement(kind, value) => {
            let suffix = encode_pair(kind, value);
            let mut key = String::from_str("retirement:");
            key.append(suffix.as_str());
            return key;
        }
    };
    let mut key = String::from_str(prefix);
    key.append(value);
    key
}

pub fn row_ids_from<'a, V, E, F, R, I, D>(
    rows: &'a [V], pointer: &str, workflow: bool, lookup: F, render: R, invalid: I, duplicate: D,
) -> (out: Result<Option<Vec<String>>, E>)
    where
        F: Fn(&'a V, &'static str) -> Option<Option<&'a str>> + Copy,
        R: Fn(&'a str, &'a str) -> String,
        I: Fn(&'static str) -> E,
        D: FnOnce(&String) -> E,
    requires
        vstd::laws_cmp::obeys_cmp::<String>(),
        forall|row: &'a V, field: &'static str| lookup.requires((row, field)),
        forall|kind: &'a str, id: &'a str| render.requires((kind, id)),
        forall|error: &'static str| invalid.requires((error,)),
        forall|key: &String| duplicate.requires((key,)),
    ensures
        out matches Ok(Some(keys)) ==> keys.len() == rows.len() && keys@.no_duplicates(),
        out matches Ok(None) ==> forall|i: int| 0 <= i < rows.len()
            ==> lookup.ensures((&rows@[i], "id"), None) && lookup.ensures((&rows@[i], "path"), None),
{
    let ghost input = lookup;
    let named = |i: usize| -> (named: bool)
        requires i < rows.len()
        ensures !named ==> input.ensures((&rows@[i as int], "id"), None)
            && input.ensures((&rows@[i as int], "path"), None)
    {
        lookup(&rows[i], "id").is_some() || lookup(&rows[i], "path").is_some()
    };
    if !requires_row_identity(rows.len(), named) {
        assert forall|i: int| 0 <= i < rows.len() implies
            input.ensures((&rows@[i], "id"), None) && input.ensures((&rows@[i], "path"), None)
        by { assert(named.ensures((i as usize,), false)); }
        return Ok(None);
    }
    let retirement = retirement_rows(workflow, pointer);
    let keys = row_keys(rows.len(), |i: usize| -> Result<String, E>
        requires i < rows.len()
    {
        let row = &rows[i];
        let id = identity_field(lookup(row, "id"));
        let path = identity_field(lookup(row, "path"));
        let kind = identity_field(lookup(row, "kind"));
        match row_identity(id, path, kind, retirement) {
            Ok(identity) => Ok(identity_key(identity, &render)),
            Err(error) => Err(invalid(error)),
        }
    }, duplicate)?;
    Ok(Some(keys))
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
#[cfg_attr(not(verus_keep_ghost), serde(untagged))]
pub enum Normalized<'a, T, V> {
    Object((&'static str, BTreeMap<&'a String, T>)),
    Array(ArrayForm<String, T>),
    Scalar((&'static str, &'a V)),
}

pub fn normalize_node<'a, V: 'a, C, T, E, O, A, R>(
    node: Node<'a, C, V>, object_child: O, array_child: A, row_ids: R,
) -> (out: Result<Normalized<'a, T, V>, E>)
    where
        C: ObjectCursor<'a, V>,
        O: Fn(&'a String, &'a V) -> Result<T, E>,
        A: Fn(usize, &'a V) -> Result<T, E> + Copy,
        R: FnOnce(&'a [V]) -> Result<Option<Vec<String>>, E>,
    requires
        vstd::laws_cmp::obeys_cmp::<String>(),
        vstd::laws_cmp::obeys_cmp::<&String>(),
        forall|key: &'a String, v: &'a V| object_child.requires((key, v)),
        forall|i: usize, v: &'a V| array_child.requires((i, v)),
        forall|rows: &'a [V]| row_ids.requires((rows,)),
        forall|rows: &'a [V], keys: Vec<String>| row_ids.ensures((rows,), Ok(Some(keys)))
            ==> keys.len() == rows.len() && keys@.no_duplicates(),
    ensures match node {
        Node::Object(_) => out.is_err() || (out matches Ok(Normalized::Object((tag, _)))
            && tag@ == "object"@),
        Node::Array(rows) => match out {
            Ok(Normalized::Array(ArrayForm::Array((tag, items)))) =>
                tag@ == "array"@ && row_ids.ensures((rows,), Ok(None))
                    && normalized_children(rows, array_child, items@, rows.len() as int),
            Ok(Normalized::Array(ArrayForm::Rows((tag, items)))) =>
                tag@ == "rows"@ && (exists|keys: Vec<String>, values: Seq<T>|
                    #![trigger row_ids.ensures((rows,), Ok(Some(keys))), normalized_children(rows, array_child, values, rows.len() as int)]
                    row_ids.ensures((rows,), Ok(Some(keys)))
                        && normalized_children(rows, array_child, values, rows.len() as int)
                        && items@.dom() == keys@.to_set()
                        && (forall|i: int| 0 <= i < keys.len() ==> items@[keys@[i]] == #[trigger] values[i])),
            Err(error) => (exists|i: usize, prefix: Seq<T>| i < rows.len()
                && #[trigger] normalized_children(rows, array_child, prefix, i as int)
                && array_child.ensures((i, &rows@[i as int]), Err(error)))
                || (row_ids.ensures((rows,), Err(error)) && exists|all: Seq<T>|
                    #[trigger] normalized_children(rows, array_child, all, rows.len() as int)),
            _ => false,
        },
        Node::Scalar(value) => out matches Ok(Normalized::Scalar((tag, original)))
            && tag@ == "scalar"@ && original == value,
    },
{
    match node {
        Node::Object(members) => {
            let mapped = object_members(members, None, BTreeMap::new(),
                |key: &'a String, child: &'a V, mut entries: BTreeMap<&'a String, T>| {
                    entries.insert(key, object_child(key, child)?);
                    Ok::<_, E>(entries)
                })?;
            Ok(Normalized::Object(("object", mapped)))
        }
        Node::Array(rows) => {
            let ghost model = array_child;
            let visit = |i: usize| -> (result: Result<T, E>)
                requires i < rows.len()
                ensures model.ensures((i, &rows@[i as int]), result)
            {
                array_child(i, &rows[i])
            };
            let values = match children(rows.len(), visit) {
                Ok(values) => {
                    assert(normalized_children(rows, array_child, values@, rows.len() as int));
                    values
                }
                Err(error) => {
                    let ghost (i, prefix) = choose|i: usize, prefix: Seq<T>| i < rows.len()
                        && visit.ensures((i,), Err(error)) && #[trigger] processed(visit, prefix, i as int);
                    assert(normalized_children(rows, array_child, prefix, i as int));
                    return Err(error);
                }
            };
            let keys = row_ids(rows)?;
            Ok(Normalized::Array(array_form(keys, values)))
        }
        Node::Scalar(value) => Ok(Normalized::Scalar(("scalar", value))),
    }
}

pub open spec fn normalized_children<'a, V, A: Fn(usize, &'a V) -> Result<T, E> + Copy, T, E>(
    rows: &'a [V], visit: A, values: Seq<T>, count: int,
) -> bool {
    values.len() == count && forall|i: usize| i < count
        ==> visit.ensures((i, &rows@[i as int]), Ok(#[trigger] values[i as int]))
}

pub fn select_node<'a, V: 'a, C, S, E, L, R, N, F>(
    node: Node<'a, C, V>, parts: &[String], depth: usize, initial: S,
    leaf: L, row_ids: R, index_name: N, child: F,
) -> (out: Result<S, E>)
    where
        C: ObjectCursor<'a, V>,
        L: FnOnce(S) -> Result<S, E>,
        R: FnOnce(&'a [V]) -> Result<Option<Vec<String>>, E>,
        N: Fn(usize) -> String,
        F: Fn(&'a V, usize, &str, String, S) -> Result<S, E>,
    requires
        depth <= parts.len(),
        leaf.requires((initial,)),
        forall|rows: &'a [V]| row_ids.requires((rows,)),
        forall|i: usize| index_name.requires((i,)),
        forall|v: &'a V, i: usize, component: &str, id: String, s: S|
            child.requires((v, i, component, id, s)),
        forall|rows: &'a [V], keys: Vec<String>| row_ids.ensures((rows,), Ok(Some(keys)))
            ==> keys.len() == rows.len(),
    ensures
        depth == parts.len() ==> leaf.ensures((initial,), out),
        depth < parts.len() && node is Scalar ==> out == Ok::<S, E>(initial),
        match node {
            Node::Array(rows) => depth < parts.len() ==>
                (out matches Err(error) && row_ids.ensures((rows,), Err::<Option<Vec<String>>, E>(error)))
                || exists|keys: Option<Vec<String>>| #[trigger] row_ids.ensures((rows,), Ok(keys)),
            _ => true,
        },
{
    let (token, next_depth) = match step(parts, depth) {
        Step::Leaf => return leaf(initial),
        Step::Child(token, next_depth) => (token, next_depth),
    };
    match node {
        Node::Object(members) => object_members(members, Some(token), initial,
            |key: &'a String, value: &'a V, state: S| {
                let component = key.as_str();
                child(value, next_depth, component, selection_identity(true, component, None), state)
            }),
        Node::Array(rows) => {
            let keys = row_ids(rows)?;
            indices(rows.len(), initial, |i: usize, state: S| -> Result<S, E>
                requires i < rows.len()
            {
                let index = index_name(i);
                let name = match &keys {
                    Some(keys) => Some(keys[i].as_str()),
                    None => None,
                };
                select_array_child(token, index.as_str(), name, &rows[i], next_depth, state, &child)
            })
        }
        Node::Scalar(_) => Ok(initial),
    }
}

/// Select by physical index and preserve the stable identity for comparison.
pub fn select_array_child<'a, V, S, E, F>(
    token: &str, index: &str, name: Option<&str>,
    value: &'a V, depth: usize, initial: S, child: &F,
) -> (out: Result<S, E>)
    where F: Fn(&'a V, usize, &str, String, S) -> Result<S, E>,
    requires forall|component: &str, id: String| child.requires((value, depth, component, id, initial)),
    ensures
        if token@ == "*"@ || token@ == index@ {
            exists|id: String| #[trigger] child.ensures((value, depth, index, id, initial), out)
                && id@ == if let Some(name) = name {name@} else {"index:"@ + index@}
        } else {
            out == Ok::<S, E>(initial)
        },
{
    if !matches_child(token, index) {
        return Ok(initial);
    }
    child(value, depth, index, selection_identity(false, index, name), initial)
}

pub open spec fn same_members<'a, V, F: Fn(&'a V, &'a V) -> bool>(
    left: Seq<(&'a String, &'a V)>, right: Seq<(&'a String, &'a V)>, equal: F,
) -> bool {
    left.len() == right.len() && forall|i: int| #![trigger left[i], right[i]]
        0 <= i < left.len() ==> left[i].0@ == right[i].0@
            && equal.ensures((left[i].1, right[i].1), true)
}

pub open spec fn different_members<'a, V, F: Fn(&'a V, &'a V) -> bool>(
    left: Seq<(&'a String, &'a V)>, right: Seq<(&'a String, &'a V)>, equal: F,
) -> bool {
    left.len() != right.len() || exists|i: int| #![trigger left[i], right[i]]
        0 <= i < left.len() && 0 <= i < right.len()
        && (left[i].0@ != right[i].0@ || equal.ensures((left[i].1, right[i].1), false))
}

fn equal_members<'a, V: 'a, C: ObjectCursor<'a, V>, F: Fn(&'a V, &'a V) -> bool>(
    left: C, right: C, equal: F,
) -> (same: bool)
    requires
        forall|a: &'a V, b: &'a V| equal.requires((a, b)),
    ensures
        same ==> same_members(left.remaining(), right.remaining(), equal),
        !same ==> different_members(left.remaining(), right.remaining(), equal),
{
    let ghost lhs = left.remaining();
    let ghost rhs = right.remaining();
    let mut lhs_cursor = left;
    let mut rhs_cursor = right;
    let ghost mut i = 0int;
    loop
        invariant
            lhs == left.remaining(), rhs == right.remaining(),
            0 <= i <= lhs.len(), 0 <= i <= rhs.len(),
            lhs_cursor.remaining() == lhs.skip(i), rhs_cursor.remaining() == rhs.skip(i),
            same_members(lhs.take(i), rhs.take(i), equal),
            forall|a: &'a V, b: &'a V| equal.requires((a, b)),
        decreases lhs.len() - i,
    {
        match (lhs_cursor.next_pair(), rhs_cursor.next_pair()) {
            (None, None) => {
                assert(lhs =~= lhs.take(i) && rhs =~= rhs.take(i));
                return true;
            }
            (Some((ak, a)), Some((bk, b))) => {
                assert(lhs[i] == (ak, a) && rhs[i] == (bk, b));
                if !<&str>::exec_eq(ak.as_str(), bk.as_str()) {
                    assert(different_members(lhs, rhs, equal));
                    return false;
                }
                if !equal(a, b) {
                    assert(different_members(lhs, rhs, equal));
                    return false;
                }
                proof {
                    assert(same_members(lhs.take(i + 1), rhs.take(i + 1), equal)) by {
                        assert forall|j: int| 0 <= j < i + 1 implies
                            (#[trigger] lhs.take(i + 1)[j]).0@ == (#[trigger] rhs.take(i + 1)[j]).0@
                            && equal.ensures((lhs.take(i + 1)[j].1, rhs.take(i + 1)[j].1), true)
                        by {
                            if j < i {
                                assert(lhs.take(i)[j] == lhs.take(i + 1)[j]);
                                assert(rhs.take(i)[j] == rhs.take(i + 1)[j]);
                            }
                        };
                    }
                    i = i + 1;
                    assert(lhs_cursor.remaining() =~= lhs.skip(i));
                    assert(rhs_cursor.remaining() =~= rhs.skip(i));
                }
            }
            _ => return false,
        }
    }
}

pub fn equal_nodes<'a, V: 'a, C, F, S>(
    left: Node<'a, C, V>, right: Node<'a, C, V>, equal_child: F, equal_scalar: S,
) -> (same: bool)
    where
        C: ObjectCursor<'a, V>,
        F: Fn(&'a V, &'a V) -> bool + Copy,
        S: FnOnce(&'a V, &'a V) -> bool,
    requires
        forall|a: &'a V, b: &'a V| equal_child.requires((a, b)) && equal_scalar.requires((a, b)),
    ensures match (left, right) {
        (Node::Object(a), Node::Object(b)) => if same {
            same_members(a.remaining(), b.remaining(), equal_child)
        } else {
            different_members(a.remaining(), b.remaining(), equal_child)
        },
        (Node::Array(a), Node::Array(b)) => if same {
            a.len() == b.len()
            && forall|i: usize| i < a.len() ==> #[trigger] equal_child.ensures((&a@[i as int], &b@[i as int]), true)
        } else {
            a.len() != b.len() || exists|i: usize| i < a.len() && i < b.len()
                && #[trigger] equal_child.ensures((&a@[i as int], &b@[i as int]), false)
        },
        (Node::Scalar(a), Node::Scalar(b)) => equal_scalar.ensures((a, b), same),
        _ => !same,
    },
{
    match (left, right) {
        (Node::Object(a), Node::Object(b)) => equal_members(a, b, equal_child),
        (Node::Array(a), Node::Array(b)) => {
            if a.len() != b.len() { return false; }
            if a.len() == 0 { return true; }
            let ghost model = equal_child;
            let compare = |i: usize| -> (result: bool)
                requires i < a.len(), i < b.len()
                ensures model.ensures((&a@[i as int], &b@[i as int]), result)
            {
                equal_child(&a[i], &b[i])
            };
            if matching_predecessors(a.len(), compare) {
                assert forall|i: usize| i < a.len() implies #[trigger] model.ensures((&a@[i as int], &b@[i as int]), true)
                    by { assert(compare.ensures((i,), true)); }
                true
            } else {
                let ghost i = choose|i: usize| i < a.len() && #[trigger] compare.ensures((i,), false);
                assert(model.ensures((&a@[i as int], &b@[i as int]), false));
                false
            }
        }
        (Node::Scalar(a), Node::Scalar(b)) => equal_scalar(a, b),
        _ => false,
    }
}

}

#[cfg(not(verus_keep_ghost))]
use crate::verified_classification::{self as policy, ObjectCursor, RowIdentity, Selection};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};

#[cfg(not(verus_keep_ghost))]
struct Members<'a>(serde_json::map::Iter<'a>);

#[cfg(not(verus_keep_ghost))]
impl<'a> ObjectCursor<'a, Value> for Members<'a> {
    fn next_pair(&mut self) -> Option<(&'a String, &'a Value)> {
        self.0.next()
    }
}

#[cfg(not(verus_keep_ghost))]
fn node(value: &Value) -> Node<'_, Members<'_>, Value> {
    match value {
        Value::Object(map) => Node::Object(Members(map.iter())),
        Value::Array(rows) => Node::Array(rows),
        scalar => Node::Scalar(scalar),
    }
}

#[cfg(not(verus_keep_ghost))]
fn child_pointer(parent: &str, key: &str) -> String {
    policy::child_pointer(parent, key).into_iter().collect()
}

#[cfg(not(verus_keep_ghost))]
fn tokens(pointer: &str) -> Result<Vec<String>, String> {
    use policy::{PointerError, decode_pointer};
    match decode_pointer(pointer) {
        Ok(parts) => Ok(parts.into_iter().map(String::from_iter).collect()),
        Err(PointerError::Prefix) => Err("E_SEMANTIC_POINTER: expected / prefix".into()),
        Err(PointerError::Escape) => {
            Err(format!("E_SEMANTIC_POINTER: invalid escape in {pointer}"))
        }
    }
}

#[cfg(not(verus_keep_ghost))]
fn row_ids(rows: &[Value], pointer: &str, workflow: bool) -> Result<Option<Vec<String>>, String> {
    row_ids_from(
        rows,
        pointer,
        workflow,
        |row, name| row.get(name).map(Value::as_str),
        |kind, value| json!([kind, value]).to_string(),
        String::from,
        |key| format!("E_SEMANTIC_IDENTITY: duplicate {key}"),
    )
}

#[cfg(not(verus_keep_ghost))]
fn normalized(value: &Value, pointer: &str, workflow: bool) -> Result<Value, String> {
    let normal = normalize_node(
        node(value),
        |key, child| normalized(child, &child_pointer(pointer, key), workflow),
        |i, child| normalized(child, &child_pointer(pointer, &i.to_string()), workflow),
        |rows| row_ids(rows, pointer, workflow),
    )?;
    serde_json::to_value(normal).map_err(|error| error.to_string())
}

#[cfg(not(verus_keep_ghost))]
type Selections = BTreeMap<Vec<String>, Selection<Value>>;

#[cfg(not(verus_keep_ghost))]
fn select(
    value: &Value,
    parts: &[String],
    depth: usize,
    pointer: &str,
    identity: &[String],
    out: Selections,
    workflow: bool,
) -> Result<Selections, String> {
    select_node(
        node(value),
        parts,
        depth,
        out,
        |mut entries| {
            let entry = Selection {
                normalized: normalized(value, pointer, workflow)?,
                pointer: pointer.to_owned(),
                value: value.clone(),
            };
            policy::record_selection(&mut entries, identity.to_vec(), entry)?;
            Ok(entries)
        },
        |rows| row_ids(rows, pointer, workflow),
        |i| i.to_string(),
        |child, next_depth, component, child_identity, entries| {
            let mut next = identity.to_vec();
            next.push(child_identity);
            select(
                child,
                parts,
                next_depth,
                &child_pointer(pointer, component),
                &next,
                entries,
                workflow,
            )
        },
    )
}

#[cfg(not(verus_keep_ghost))]
fn equal_normalized(before: &Value, after: &Value) -> bool {
    equal_nodes(node(before), node(after), equal_normalized, |a, b| a == b)
}

#[cfg(not(verus_keep_ghost))]
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
        |value, workflow| select(value, &parts, 0, "", &[], Selections::new(), workflow),
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
                |before, after| equal_normalized(&before.normalized, &after.normalized),
            )?;
            Some(json!(crate::verified_classification::semantic_change(
                pattern, on, difference
            )))
        },
    ))
}
