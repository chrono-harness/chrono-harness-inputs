//! Run an installed tool with the host's output and time limits.
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::BTreeMap,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

#[cfg(not(verus_keep_ghost))]
#[derive(Serialize)]
pub struct CommandSpec {
    pub program: String,
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Lengths {
    exit_code: i32,
    stdout_length: usize,
    stderr_length: usize,
}

use vstd::prelude::*;

verus! {
pub const LF: u8 = 10;

/// The JSON header ends at the first LF. The binary payload may contain any bytes.
pub fn response_parts(bytes: &[u8]) -> (parts: Option<(&[u8], &[u8])>)
    ensures
        parts.is_none() == (forall|i: int| 0 <= i < bytes.len() ==> #[trigger] bytes@[i] != LF),
        match parts {
            Some((header, payload)) => {
                &&& header.len() < bytes.len()
                &&& bytes@[header.len() as int] == LF
                &&& forall|i: int| 0 <= i < header.len() ==> #[trigger] bytes@[i] != LF
                &&& header@ == bytes@.subrange(0, header.len() as int)
                &&& payload@ == bytes@.subrange(header.len() as int + 1, bytes.len() as int)
            },
            None => true,
        },
{
    let mut i = 0;
    while i < bytes.len()
        invariant
            0 <= i <= bytes.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] bytes@[j] != LF,
        decreases bytes.len() - i,
    {
        if bytes[i] == LF {
            let (header, rest) = bytes.split_at(i);
            let (_, payload) = rest.split_at(1);
            return Some((header, payload));
        }
        i += 1;
    }
    None
}
}

#[cfg(not(verus_keep_ghost))]
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
    let (header, bytes) = response_parts(&result.stdout).ok_or("invalid command result header")?;
    let lengths: Lengths = serde_json::from_slice(header).map_err(|error| error.to_string())?;
    let (stdout, stderr) = crate::command_frame::split(
        bytes,
        lengths.stdout_length,
        lengths.stderr_length,
        spec.output_limit_bytes,
    )
    .ok_or("invalid command result lengths")?;
    Ok((lengths.exit_code, stdout.into(), stderr.into()))
}
