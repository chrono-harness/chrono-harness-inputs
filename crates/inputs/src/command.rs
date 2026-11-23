//! Run an installed tool with the host's output and time limits.
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

#[derive(Serialize)]
pub struct CommandSpec {
    pub program: String,
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Lengths {
    exit_code: i32,
    stdout_length: usize,
    stderr_length: usize,
}

pub(crate) fn run(
    root: &Path,
    spec: &CommandSpec,
    input: &[u8],
) -> Result<(i32, Vec<u8>, Vec<u8>), String> {
    let mut header = serde_json::to_vec(spec).map_err(|error| error.to_string())?;
    header.push(b'\n');
    let mut child = Command::new("chrono-harness")
        .arg("run-command-v1")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("chrono-harness run-command-v1: {error}"))?;
    let mut stdin = child.stdin.take().expect("piped stdin");
    let written = stdin
        .write_all(&header)
        .and_then(|()| stdin.write_all(input));
    drop(stdin);
    let result = child
        .wait_with_output()
        .map_err(|error| error.to_string())?;
    if !result.status.success() {
        let error = std::str::from_utf8(&result.stderr).map_err(|error| error.to_string())?;
        return Err(if error.is_empty() {
            format!("chrono-harness run-command-v1: {}", result.status)
        } else {
            error.trim_end_matches('\n').into()
        });
    }
    written.map_err(|error| error.to_string())?;
    let end = result
        .stdout
        .iter()
        .position(|b| *b == b'\n')
        .ok_or("invalid command result header")?;
    let lengths: Lengths =
        serde_json::from_slice(&result.stdout[..end]).map_err(|error| error.to_string())?;
    let bytes = &result.stdout[end + 1..];
    if lengths.stdout_length > spec.output_limit_bytes
        || lengths.stderr_length > spec.output_limit_bytes
        || lengths.stdout_length.checked_add(lengths.stderr_length) != Some(bytes.len())
    {
        return Err("invalid command result lengths".into());
    }
    let (stdout, stderr) = bytes.split_at(lengths.stdout_length);
    Ok((lengths.exit_code, stdout.into(), stderr.into()))
}
