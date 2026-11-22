use chrono_harness::CommandSpec;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn selected_tests(
    endpoints: &Value,
    protocol: &Value,
    path: String,
    invoke: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<BTreeSet<String>, String> {
    let command = CommandSpec {
        program: "chrono-judge-routes".into(),
        args: vec!["global-selection".into()],
        env: BTreeMap::from([("PATH".into(), path)]),
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
            format!("route selection exited with {code}")
        } else {
            message.into()
        });
    }
    serde_json::from_slice(&output).map_err(|error| format!("invalid route selection: {error}"))
}
