#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Preserve the process status used by the caller and the diagnostics session.
pub(crate) fn output_code(result: &Result<String, String>) -> (code: u8)
    ensures code == if result.is_ok() { 0u8 } else { 2u8 },
{
    match result { Ok(_) => 0, Err(_) => 2 }
}

pub(crate) enum Completion {
    Confirmed(u8),
    WorkError(String),
    LoggerMismatch(u8),
}

/// A failed request keeps its original error. A completed request requires
/// the logger to have exited with that exact code, including after CLI errors.
pub(crate) fn completion(result: Result<u8, String>, observed: Option<i32>) -> (out: Completion)
    ensures match result {
        Err(e) => out == Completion::WorkError(e),
        Ok(wanted) => match observed {
            Some(code) if code as int == wanted as int => out == Completion::Confirmed(wanted),
            _ => out == Completion::LoggerMismatch(wanted),
        },
    },
{
    match result {
        Err(e) => Completion::WorkError(e),
        Ok(wanted) => match observed {
            Some(code) if code == wanted as i32 => Completion::Confirmed(wanted),
            _ => Completion::LoggerMismatch(wanted),
        },
    }
}
}

#[cfg(not(verus_keep_ghost))]
use serde_json::json;
#[cfg(not(verus_keep_ghost))]
use std::{
    ffi::OsString,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
};

#[cfg(not(verus_keep_ghost))]
fn work(root: &Path, args: &[OsString]) -> Result<String, String> {
    let mut decoded = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        let Some(text) = arg.to_str() else {
            let message = "arguments must be valid UTF-8.";
            let timestamp = time::OffsetDateTime::now_utc()
                .format(&time::format_description::well_known::Rfc3339)
                .map_err(|e| e.to_string())?;
            return Err(json!({
                "schema": "chrono-log/v1", "timestamp": timestamp, "level": "error",
                "producer": "chrono-inputs", "event": "cli.invalid_argument",
                "message": message, "context": {}, "fields": {"target":"chrono"},
                "error": {"schema":"chrono-error/v1","error":{
                    "type":"chrono_inputs::ArgumentError","code":"E_USAGE","message":message,
                    "context":{"argument_bytes":arg.as_encoded_bytes(),"argument_index":i,"argv_index":i+1},
                    "source":null
                }}
            }).to_string());
        };
        decoded.push(text.to_owned());
    }
    chrono_inputs::run(root, &decoded)
}
#[cfg(not(verus_keep_ghost))]
fn finish(result: Result<String, String>) -> u8 {
    let code = output_code(&result);
    match result {
        Ok(text) => print!("{text}"),
        Err(error) => eprintln!("{error}"),
    }
    code
}
#[cfg(not(verus_keep_ghost))]
fn run() -> Result<u8, String> {
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    let root = args
        .windows(2)
        .find(|item| item[0] == "--host-root")
        .map(|item| PathBuf::from(&item[1]))
        .unwrap_or_else(|| cwd.clone());
    let policy = root.join(".chrono-harness/logging.json");
    match policy.symlink_metadata() {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(finish(work(&cwd, &args))),
        Err(e) => return Err(e.to_string()),
        Ok(_) => {}
    }
    let operation = args.first().and_then(|arg| arg.to_str()).unwrap_or("cli");
    let mut child = Command::new("chrono-diagnostics")
        .arg("cli-events-v1")
        .arg(&root)
        .args(["chrono-inputs", operation])
        .arg(std::process::id().to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("chrono-diagnostics cli-events-v1: {e}"))?;
    let mut writer = child.stdin.take().expect("piped stdin");
    let mut reader = BufReader::new(child.stdout.take().expect("piped stdout"));
    let result = (|| -> Result<u8, String> {
        let mut line = String::new();
        reader.read_line(&mut line).map_err(|e| e.to_string())?;
        if serde_json::from_str::<serde_json::Value>(&line).ok() != Some(json!({"ready":true})) {
            return Err("chrono-diagnostics did not open the CLI log".into());
        }
        let result = work(&cwd, &args);
        if let Err(error) = &result {
            serde_json::to_writer(&mut writer, &json!({"diagnostic":error}))
                .map_err(|e| e.to_string())?;
            writer.write_all(b"\n").map_err(|e| e.to_string())?;
        }
        let status = finish(result);
        serde_json::to_writer(&mut writer, &json!({"exit_code":status}))
            .map_err(|e| e.to_string())?;
        writer
            .write_all(b"\n")
            .and_then(|()| writer.flush())
            .map_err(|e| e.to_string())?;
        Ok(status)
    })();
    drop(writer);
    let status = child.wait().map_err(|e| e.to_string())?;
    match completion(result, status.code()) {
        Completion::Confirmed(code) => Ok(code),
        Completion::WorkError(error) => Err(error),
        Completion::LoggerMismatch(wanted) => Err(format!(
            "chrono-diagnostics cli-events-v1 exited {status} after {wanted}"
        )),
    }
}
#[cfg(not(verus_keep_ghost))]
fn main() -> ExitCode {
    match run() {
        Ok(exit) => exit.into(),
        Err(error) => {
            eprintln!("{error}");
            2.into()
        }
    }
}
