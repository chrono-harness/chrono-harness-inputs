//! Wire format accepted by offline input transport.
use super::files as wire;
use super::files::{relative_path, valid_host_state_path};
use serde_json::{Map, Value};
use std::collections::BTreeSet;

pub const SNAPSHOT_SCHEMA: &str = "chrono-input-snapshot/v1";
pub const SNAPSHOT_SCHEMA_V2: &str = "chrono-input-snapshot/v2";
pub const SNAPSHOT_SCHEMA_V3: &str = "chrono-input-snapshot/v3";

fn fields<'a>(
    value: &'a Value,
    required: &[&str],
    optional: &[&str],
    context: &str,
) -> Result<&'a Map<String, Value>, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{context}: expected object"))?;
    for name in required {
        if !object.contains_key(*name) {
            return Err(format!("{context}: missing field {name}"));
        }
    }
    for name in object.keys() {
        if !(required.contains(&name.as_str()) || optional.contains(&name.as_str())) {
            return Err(format!("{context}: unknown field {name}"));
        }
    }
    Ok(object)
}

fn selector(value: &Value) -> Result<(), String> {
    let path = value["effective_config_path"]
        .as_str()
        .ok_or("E_INPUT_SNAPSHOT: missing effective config path")?;
    relative_path(path)?;
    let selection = fields(
        &value["selection"],
        &["schema", "path", "platform", "config_path"],
        &["registry_path"],
        "E_INPUT_SNAPSHOT: invalid selector binding",
    )?;
    if selection["schema"] != "chrono-registry-selection/v1"
        || !selection["platform"]
            .as_str()
            .is_some_and(|name| !name.is_empty() && name.trim() == name)
        || selection["path"] != value["config_path"]
        || selection["config_path"] != path
        || selection["path"] == path
    {
        return Err("E_INPUT_SNAPSHOT: invalid selector binding schema".into());
    }
    let entry = selection["path"]
        .as_str()
        .ok_or("E_INPUT_SNAPSHOT: selector path must be a string")?;
    relative_path(entry)?;
    if let Some(registry) = selection.get("registry_path") {
        relative_path(
            registry
                .as_str()
                .ok_or("E_INPUT_SNAPSHOT: selector registry path must be a string")?,
        )?;
    }
    Ok(())
}

fn file(value: &Value, absence_allowed: bool) -> Result<(), String> {
    let context = "E_INPUT_BLOB";
    if let Some(absent) = value.get("absent") {
        fields(value, &["absent"], &[], context)?;
        if absent != true {
            return Err("E_INPUT_BLOB: absent must be true".into());
        }
        if !absence_allowed {
            return Err("E_INPUT_SNAPSHOT: absence requires snapshot v2".into());
        }
        return Ok(());
    }
    match (value.get("bytes"), value.get("blob")) {
        (Some(bytes), None) => {
            fields(value, &["bytes"], &[], context)?;
            let valid = bytes.as_array().is_some_and(|bytes| {
                bytes
                    .iter()
                    .all(|n| n.as_u64().is_some_and(|n| n <= u8::MAX.into()))
            });
            if !valid {
                return Err("E_INPUT_BLOB: invalid retained byte array".into());
            }
        }
        (None, Some(blob)) => {
            fields(value, &["blob", "sha256", "length"], &[], context)?;
            if !blob
                .as_str()
                .is_some_and(|path| valid_host_state_path(path))
            {
                return Err("E_INPUT_BLOB: reference must be within host state".into());
            }
            if !value["sha256"].as_str().is_some_and(wire::is_digest) {
                return Err("E_INPUT_BLOB: invalid digest".into());
            }
            if !value["length"].is_u64() {
                return Err("E_INPUT_BLOB: invalid length".into());
            }
        }
        _ => return Err("E_INPUT_BLOB: expected exactly one bytes or blob representation".into()),
    }
    Ok(())
}

/// Admit every record before the transport attempts any file I/O.
pub fn snapshot_shape(value: &Value) -> Result<(), String> {
    fields(
        value,
        &[
            "schema",
            "commit",
            "config_path",
            "config_digest",
            "environment",
            "files",
        ],
        &["effective_config_path", "selection"],
        "E_INPUT_SNAPSHOT",
    )?;
    let schema = value["schema"].as_str();
    match schema {
        Some(SNAPSHOT_SCHEMA_V3) => selector(value)?,
        Some(SNAPSHOT_SCHEMA | SNAPSHOT_SCHEMA_V2) => {
            if value.get("selection").is_some() || value.get("effective_config_path").is_some() {
                return Err("E_INPUT_SNAPSHOT: selection binding requires snapshot v3".into());
            }
        }
        _ => return Err("E_INPUT_SNAPSHOT: unsupported snapshot schema".into()),
    }
    wire::full_oid(
        value["commit"]
            .as_str()
            .ok_or("E_INPUT_SNAPSHOT: invalid commit")?,
    )?;
    relative_path(
        value["config_path"]
            .as_str()
            .ok_or("E_INPUT_SNAPSHOT: invalid config path")?,
    )?;
    if !value["config_digest"].as_str().is_some_and(wire::is_digest) {
        return Err("E_INPUT_SNAPSHOT: invalid config digest".into());
    }
    let env = value["environment"]
        .as_object()
        .ok_or("E_INPUT_SNAPSHOT: invalid environment")?;
    if env
        .iter()
        .any(|(key, val)| key.is_empty() || !(val.is_string() || val.is_null()))
    {
        return Err("E_INPUT_SNAPSHOT: environment values must be strings or null".into());
    }
    for (id, record) in value["files"]
        .as_object()
        .ok_or("E_INPUT_SNAPSHOT: invalid files")?
    {
        if id.is_empty() {
            return Err("E_INPUT_SNAPSHOT: empty file ID".into());
        }
        file(record, schema != Some(SNAPSHOT_SCHEMA))?;
    }
    Ok(())
}

/// Compose binds captured values to the endpoint and does not materialize a process environment.
pub(crate) fn bind_environment(
    credentials: &BTreeSet<String>,
    config: &Value,
    captured: &Value,
) -> Result<(), String> {
    let env = &config["environment"];
    let values = env["values"].as_object().ok_or("environment values")?;
    if values
        .iter()
        .any(|(key, val)| key.is_empty() || key.contains(['=', '\0']) || !val.is_string())
    {
        return Err("invalid environment value".into());
    }
    let mut inherited = BTreeSet::new();
    for value in env["inherit"].as_array().ok_or("inherit missing")? {
        let key = value
            .as_str()
            .filter(|s| !s.is_empty())
            .ok_or("inherit key")?;
        if !inherited.insert(key) {
            return Err(format!("duplicate ID {key}"));
        }
    }
    let captured = captured
        .as_object()
        .ok_or("E_INPUT_SNAPSHOT: invalid environment")?;
    for key in captured.keys() {
        if !inherited.contains(key.as_str()) && !values.contains_key(key) {
            return Err(format!("unregistered retained environment variable {key}"));
        }
    }
    for key in inherited {
        if credentials.contains(key) && captured.get(key) != Some(&Value::Null) {
            return Err(
                "acquisition credentials cannot be retained as business environment inputs".into(),
            );
        }
        if !captured.contains_key(key) {
            return Err(format!("missing retained environment variable {key}"));
        }
    }
    Ok(())
}
