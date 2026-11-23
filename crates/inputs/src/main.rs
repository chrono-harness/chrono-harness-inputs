use serde_json::json;
use std::{
    ffi::OsString,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
};

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
fn finish(result: Result<String, String>) -> u8 {
    match result {
        Ok(text) => {
            print!("{text}");
            0
        }
        Err(error) => {
            eprintln!("{error}");
            2
        }
    }
}
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
    let wanted = result?;
    if status.code() != Some(i32::from(wanted)) {
        return Err(format!(
            "chrono-diagnostics cli-events-v1 exited {status} after {wanted}"
        ));
    }
    Ok(wanted)
}
fn main() -> ExitCode {
    match run() {
        Ok(exit) => exit.into(),
        Err(error) => {
            eprintln!("{error}");
            2.into()
        }
    }
}
