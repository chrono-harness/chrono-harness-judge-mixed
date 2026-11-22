use serde_json::Value;

/// Append observations only when both readers used the same Git binding.
pub(crate) fn append(registered: Option<&mut Value>, mut documents: Value) -> Result<(), String> {
    if documents.is_null() && registered.is_none() {
        return Ok(());
    }
    let extra = documents
        .as_object_mut()
        .ok_or("E_GIT_FACTS: document reader is unbound")?;
    let processes = extra
        .remove("processes")
        .ok_or("E_GIT_FACTS: missing document processes")?;
    let Value::Array(processes) = processes else {
        return Err("E_GIT_FACTS: invalid document processes".into());
    };
    let actual = registered
        .and_then(Value::as_object_mut)
        .ok_or("E_GIT_FACTS: registration reader is unbound")?;
    if actual.len() != extra.len() + 1
        || extra
            .iter()
            .any(|(key, value)| actual.get(key) != Some(value))
    {
        return Err("E_GIT_FACTS: registration and document reader bindings differ".into());
    }
    actual
        .get_mut("processes")
        .and_then(Value::as_array_mut)
        .ok_or("E_GIT_FACTS: missing registration processes")?
        .extend(processes);
    Ok(())
}
