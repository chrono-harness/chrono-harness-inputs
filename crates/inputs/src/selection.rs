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

pub(crate) fn selected_tests(
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

fn query<T: DeserializeOwned>(
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
