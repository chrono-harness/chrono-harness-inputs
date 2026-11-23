use serde_json::{Value, json};
use std::{fs, process::Command};

#[test]
fn pairs_stored_inputs_with_an_empty_tool_search_path() {
    let fixture = tempfile::tempdir().unwrap();
    let root = fixture.path();
    let bytes = b"offline input\0\xff";
    let digest = chrono_harness::sha256(bytes);
    let blob = format!(".chrono-harness/state/inputs/blobs/{digest}");
    let snapshot = |endpoint: &str, oid: &str| {
        let host = root.join(endpoint);
        fs::create_dir_all(host.join(&blob).parent().unwrap()).unwrap();
        fs::write(host.join(&blob), bytes).unwrap();
        let value = json!({"schema":"chrono-input-snapshot/v2", "commit":oid, "config_path":"config.json",
            "config_digest":"2".repeat(64), "environment":{}, "files":{
                "sdk":{"blob":blob,"sha256":digest,"length":bytes.len()}, "optional":{"absent":true}}});
        fs::write(
            host.join(".chrono-harness/state/input.json"),
            value.to_string(),
        )
        .unwrap();
        value
    };
    let base = snapshot("base", &"a".repeat(40));
    let candidate = snapshot("candidate", &"b".repeat(40));
    let destination = root.join("destination");
    fs::create_dir(&destination).unwrap();
    let run = |output: &str| {
        Command::new(
            std::env::var_os("CHRONO_INPUTS_BIN")
                .expect("check.sh supplies the built inputs binary"),
        )
        .current_dir(root)
        .env_clear()
        .env("PATH", "")
        .env("HOME", root)
        .args([
            "pair",
            "--host-root",
            "destination",
            "--base-root",
            "base",
            "--candidate-root",
            "candidate",
            "--base-snapshot",
            ".chrono-harness/state/input.json",
            "--candidate-snapshot",
            ".chrono-harness/state/input.json",
            "--output",
            output,
        ])
        .output()
        .unwrap()
    };
    let pair = ".chrono-harness/state/pair.json";
    let result = run(pair);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let stored: Value = serde_json::from_slice(&fs::read(destination.join(pair)).unwrap()).unwrap();
    assert_eq!(stored, json!({"base":base,"candidate":candidate}));
    assert_eq!(fs::read(destination.join(&blob)).unwrap(), bytes);

    fs::write(root.join("candidate").join(&blob), b"changed offline bytes").unwrap();
    let rejected = ".chrono-harness/state/rejected.json";
    let result = run(rejected);
    assert_eq!(result.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&result.stderr)
            .contains("E_INPUT_BLOB: retained bytes differ from snapshot")
    );
    assert!(!destination.join(rejected).exists());
}
