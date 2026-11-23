use chrono_harness::CommandSpec;
use serde::{Deserialize, de::DeserializeOwned};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Deserialize)]
struct FilemapSelection {
    tests: Vec<String>,
    retired_tests: Vec<String>,
    findings: Vec<chrono_harness::wire::Finding>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CapturePlan {
    pub schema: String,
    pub effective_config: String,
    pub selection: Option<Value>,
    pub required: BTreeSet<String>,
}

/// Ask registration to interpret the same fixed documents held by capture.
pub fn capture_plan(
    config: &str,
    documents: &BTreeMap<String, Value>,
    unit: Option<&str>,
    search_path: &str,
    invoke: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<CapturePlan, String> {
    let identity = chrono_harness::facts::registry_identity(documents, config)?;
    let selected = documents
        .get(&identity.effective_path)
        .ok_or("missing effective config")?;
    let reply: CapturePlan = query(
        "chrono-judge-registration",
        "capture-plan-v1",
        &serde_json::json!({"config": config, "documents": documents, "unit": unit}),
        &selected["protocol"],
        &BTreeMap::from([("PATH".into(), search_path.into())]),
        invoke,
    )?;
    if reply.effective_config != identity.effective_path || reply.selection != identity.selection {
        return Err(
            "E_INPUT_SNAPSHOT: capture plan differs from the fixed configuration selection".into(),
        );
    }
    Ok(reply)
}

pub fn selected_tests(
    commits: &Value,
    mut registries: Value,
    protocol: &Value,
    environment: &BTreeMap<String, String>,
    mut invoke: impl FnMut(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<BTreeSet<String>, String> {
    let impact: FilemapSelection = query(
        "chrono-judge-filemap",
        "endpoint-tests",
        commits,
        protocol,
        environment,
        &mut invoke,
    )?;
    if impact
        .findings
        .iter()
        .any(|finding| finding.level == "error")
    {
        return Err(format!(
            "E_COMPOSE_SELECTION: {}",
            serde_json::to_string(&impact.findings).map_err(|error| error.to_string())?
        ));
    }
    registries["tests"] = serde_json::json!(impact.tests);
    registries["retired_tests"] = serde_json::json!(impact.retired_tests);
    let env = BTreeMap::from([(
        "PATH".into(),
        environment.get("PATH").ok_or("route query PATH")?.clone(),
    )]);
    query(
        "chrono-judge-routes",
        "global-selection",
        &registries,
        protocol,
        &env,
        invoke,
    )
}

pub(crate) fn query<T: DeserializeOwned>(
    program: &str,
    operation: &str,
    endpoints: &Value,
    protocol: &Value,
    environment: &BTreeMap<String, String>,
    invoke: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<T, String> {
    let command = CommandSpec {
        program: program.into(),
        args: vec![operation.into()],
        env: environment.clone(),
        timeout_seconds: protocol["timeout_seconds"]
            .as_u64()
            .ok_or("invalid route query timeout")?,
        output_limit_bytes: protocol["stdout_limit_bytes"]
            .as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or("invalid route query output bound")?,
    };
    let input = serde_json::to_vec(endpoints).map_err(|error| error.to_string())?;
    let (code, output, diagnostic) = invoke(&command, &input)?;
    if code != 0 {
        let message = std::str::from_utf8(&diagnostic).map_err(|error| error.to_string())?;
        let message = message.strip_suffix('\n').unwrap_or(message);
        return Err(if message.is_empty() {
            format!("{program} {operation} exited with {code}")
        } else {
            message.into()
        });
    }
    serde_json::from_slice(&output)
        .map_err(|error| format!("invalid {operation} response: {error}"))
}
