use crate::command::CommandSpec;
use serde::{Deserialize, de::DeserializeOwned};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
struct Finding {
    code: String,
    level: String,
    message: String,
    delta_refs: Vec<String>,
    causes: Vec<String>,
}

#[derive(Deserialize)]
struct FilemapSelection {
    tests: Vec<String>,
    retired_tests: Vec<String>,
    findings: Vec<Finding>,
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
    endpoint: &Endpoint,
    unit: Option<&str>,
    search_path: &str,
    invoke: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<CapturePlan, String> {
    let documents = &endpoint.values;
    let selected = documents
        .get(&endpoint.effective_path)
        .ok_or("missing effective config")?;
    let reply: CapturePlan = query(
        "chrono-judge-registration",
        "capture-plan-v1",
        &serde_json::json!({"config": config, "documents": documents, "unit": unit}),
        &selected["protocol"],
        &BTreeMap::from([("PATH".into(), search_path.into())]),
        invoke,
    )?;
    if reply.effective_config != endpoint.effective_path || reply.selection != endpoint.selection {
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

#[derive(Deserialize)]
pub struct Endpoint {
    pub values: BTreeMap<String, Value>,
    pub effective_path: String,
    pub selection: Option<Value>,
}

/// A single Git reader fixes the host configuration for all requested endpoints.
pub(crate) fn endpoints(
    root: &std::path::Path,
    config: &str,
    base: &str,
    candidate: &str,
    capture: bool,
) -> Result<Vec<Endpoint>, String> {
    use std::io::{BufRead, BufReader, Write};
    use std::process::{Command, Stdio};
    let mut process = Command::new("chrono-harness")
        .arg("git-facts-v1")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| format!("chrono-harness git-facts-v1: {error}"))?;
    let mut stdin = process.stdin.take().expect("piped stdin");
    let mut stdout = BufReader::new(process.stdout.take().expect("piped stdout"));
    let mut exchange = |request: Value| -> Result<Value, String> {
        serde_json::to_writer(&mut stdin, &request).map_err(|error| error.to_string())?;
        stdin
            .write_all(b"\n")
            .and_then(|()| stdin.flush())
            .map_err(|error| error.to_string())?;
        let mut line = String::new();
        if stdout
            .read_line(&mut line)
            .map_err(|error| error.to_string())?
            == 0
        {
            return Err("git-facts-v1 ended before its response".into());
        }
        serde_json::from_str::<Result<Value, String>>(&line)
            .map_err(|error| format!("invalid git facts: {error}"))?
    };
    let result: Result<Vec<Endpoint>, String> = (|| {
        exchange(
            serde_json::json!({"mode":"config","config":config,"base":base,"candidate":candidate}),
        )?;
        let views = if capture {
            vec![("checked-out-snapshot", "candidate")]
        } else {
            vec![
                ("registry-snapshot", "base"),
                ("registry-snapshot", "candidate"),
            ]
        };
        views
            .into_iter()
            .map(|(op, endpoint)| {
                let result = exchange(serde_json::json!({"op":op,"endpoint":endpoint}))?;
                serde_json::from_value(result)
                    .map_err(|error| format!("invalid registry endpoint: {error}"))
            })
            .collect()
    })();
    drop(stdin);
    let status = process.wait().map_err(|error| error.to_string())?;
    let endpoints = result?;
    if !status.success() {
        return Err(format!("chrono-harness git-facts-v1: {status}"));
    }
    Ok(endpoints)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct InputProfile {
    pub credential_environment: BTreeSet<String>,
    pub has_execution_units: Option<bool>,
}
pub(crate) fn input_profile(
    root: &std::path::Path,
    config: &Value,
    inspect: bool,
) -> Result<InputProfile, String> {
    query(
        "chrono-judge-registration",
        "input-profile-v1",
        &serde_json::json!({"config":config,"inspect_execution_units":inspect}),
        &config["protocol"],
        &BTreeMap::from([(
            "PATH".into(),
            std::env::var("PATH").map_err(|e| e.to_string())?,
        )]),
        |spec, input| crate::command::run(root, spec, input),
    )
}
