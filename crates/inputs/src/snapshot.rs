//! Wire format accepted by offline input transport.
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub enum FieldError<'a> { Missing(usize), Unexpected(&'a str) }

pub fn field_declared(names: &[&str], key: &str) -> (found: bool)
    ensures found == (exists|i: int| 0 <= i < names.len() && (#[trigger] names@[i])@ == key@),
{
    let mut i = 0;
    while i < names.len()
        invariant i <= names.len(), forall|j: int| 0 <= j < i ==> (#[trigger] names@[j])@ != key@,
        decreases names.len() - i,
    {
        if <&str>::exec_eq(names[i], key) { return true; }
        i += 1;
    }
    false
}

/// Unknown fields are read in the deserializer's iteration order, after all required lookups.
pub fn first_field_error<'a, P, U>(required: &[&str], present: P, unexpected: U)
    -> (error: Option<FieldError<'a>>)
    where P: Fn(&str) -> bool, U: FnOnce() -> Option<&'a str>,
    requires forall|name: &str| present.requires((name,)),
        (forall|j: int| 0 <= j < required.len()
            ==> #[trigger] present.ensures((required@[j],), true)) ==> unexpected.requires(()),
    ensures match error {
        Some(FieldError::Missing(i)) => i < required.len()
            && present.ensures((required@[i as int],), false)
            && forall|j: int| 0 <= j < i ==> #[trigger] present.ensures((required@[j],), true),
        other => (forall|j: int| 0 <= j < required.len()
            ==> #[trigger] present.ensures((required@[j],), true))
            && match other {
                Some(FieldError::Unexpected(name)) => unexpected.ensures((), Some(name)),
                None => unexpected.ensures((), None),
                _ => false,
            },
    },
{
    let mut i = 0;
    while i < required.len()
        invariant i <= required.len(), forall|name: &str| present.requires((name,)),
            forall|j: int| 0 <= j < i ==> #[trigger] present.ensures((required@[j],), true),
        decreases required.len() - i,
    {
        if !present(required[i]) { return Some(FieldError::Missing(i)); }
        i += 1;
    }
    match unexpected() {
        Some(name) => Some(FieldError::Unexpected(name)),
        None => None,
    }
}
}

#[cfg(not(verus_keep_ghost))]
use super::files as wire;
#[cfg(not(verus_keep_ghost))]
use super::files::{relative_path, valid_host_state_path};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Map, Value};
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeSet;

#[cfg(not(verus_keep_ghost))]
use super::retained_shape::{self, Representation, Version};
#[cfg(not(verus_keep_ghost))]
pub use super::retained_shape::{SNAPSHOT_SCHEMA, SNAPSHOT_SCHEMA_V2, SNAPSHOT_SCHEMA_V3};

#[cfg(not(verus_keep_ghost))]
fn fields<'a>(
    value: &'a Value,
    required: &[&str],
    optional: &[&str],
    context: &str,
) -> Result<&'a Map<String, Value>, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{context}: expected object"))?;
    let error = first_field_error(
        required,
        |name| object.contains_key(name),
        || {
            object
                .keys()
                .map(String::as_str)
                .find(|name| !field_declared(required, name) && !field_declared(optional, name))
        },
    );
    match error {
        Some(FieldError::Missing(index)) => {
            return Err(format!("{context}: missing field {}", required[index]));
        }
        Some(FieldError::Unexpected(name)) => {
            return Err(format!("{context}: unknown field {name}"));
        }
        None => {}
    }
    Ok(object)
}

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
fn file(value: &Value, version: Version) -> Result<(), String> {
    let context = "E_INPUT_BLOB";
    let representation = retained_shape::representation(
        value.get("absent").is_some(),
        value.get("bytes").is_some(),
        value.get("blob").is_some(),
    )?;
    match representation {
        Representation::Absent => {
            fields(value, &["absent"], &[], context)?;
            retained_shape::admit_absent(version, value["absent"].as_bool())?;
        }
        Representation::Bytes => {
            fields(value, &["bytes"], &[], context)?;
            if !value["bytes"]
                .as_array()
                .is_some_and(|bytes| bytes.iter().all(|n| retained_shape::is_byte(n.as_u64())))
            {
                return Err("E_INPUT_BLOB: invalid retained byte array".into());
            }
        }
        Representation::Blob => {
            fields(value, &["blob", "sha256", "length"], &[], context)?;
            retained_shape::admit_reference(
                value["blob"].as_str().is_some_and(valid_host_state_path),
                value["sha256"].as_str().is_some_and(wire::is_digest),
                value["length"].is_u64(),
            )?;
        }
    }
    Ok(())
}

/// Admit every record before the transport attempts any file I/O.
#[cfg(not(verus_keep_ghost))]
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
    let version = retained_shape::version(
        value["schema"].as_str(),
        value.get("selection").is_some(),
        value.get("effective_config_path").is_some(),
    )?;
    if matches!(version, Version::V3) {
        selector(value)?;
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
        file(record, version)?;
    }
    Ok(())
}

/// Compose binds captured values to the endpoint and does not materialize a process environment.
#[cfg(not(verus_keep_ghost))]
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
