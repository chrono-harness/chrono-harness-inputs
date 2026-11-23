use serde_json::{Value, json};
use std::{fs, process::Command};

#[test]
fn pairs_stored_inputs_with_an_empty_tool_search_path() {
    let fixture = tempfile::tempdir().unwrap();
    let root = fixture.path();
    let bytes = b"offline input\0\xff";
    let digest = "c168483cfd5092329b33e18921c9911d828ad34b1b94c376e0dcab35cde50d46";
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

    let mut inline = base;
    inline["files"] = json!({"a":{"bytes":[0,255]}});
    let base_path = root.join("base/.chrono-harness/state/input.json");
    fs::write(&base_path, inline.to_string()).unwrap();
    let result = run(rejected);
    assert_eq!(result.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&result.stderr)
            .contains("E_INPUT_BLOB: pair requires captured blob references")
    );

    // Admit the entire snapshot before importing even its first file.
    inline["files"]["z"] = json!({"absent":false});
    fs::write(base_path, inline.to_string()).unwrap();
    let result = run(rejected);
    assert_eq!(result.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&result.stderr).contains("E_INPUT_BLOB: absent must be true"));
    assert!(!destination.join(rejected).exists());
}

#[test]
fn snapshot_versions_reject_inconsistent_selectors_and_malformed_file_addresses() {
    let mut snapshot = json!({
        "schema":"chrono-input-snapshot/v3", "commit":"c".repeat(40),
        "config_path":"selector.json", "config_digest":"d".repeat(64),
        "effective_config_path":"host.json", "selection":{
            "schema":"chrono-registry-selection/v1", "path":"selector.json",
            "config_path":"host.json", "registry_path":"release.json", "platform":"test-platform"
        },
        "environment":{"ABSENT":null,"EMPTY":""}, "files":{"optional":{"absent":true}}
    });
    let admit = chrono_inputs::test_support::snapshot_shape;
    assert!(admit(&snapshot).is_ok());
    for (pointer, invalid) in [
        ("/schema", json!("chrono-input-snapshot/v2")),
        ("/selection/path", json!("wrong.json")),
        ("/selection/config_path", json!("other.json")),
        ("/selection/platform", json!("  ")),
        ("/selection/registry_path", json!("../bad")),
        ("/environment/ABSENT", json!(0)),
        ("/files/optional", json!({"absent":true,"bytes":[]})),
        (
            "/files/optional",
            json!({"blob":"../bad","sha256":"f".repeat(64),"length":0}),
        ),
        (
            "/files/optional",
            json!({"blob":".chrono-harness/state/file","sha256":"bad","length":0}),
        ),
        (
            "/files/optional",
            json!({"blob":".chrono-harness/state/file","sha256":"f".repeat(64),"length":-1}),
        ),
    ] {
        let mut modified = snapshot.clone();
        *modified.pointer_mut(pointer).unwrap() = invalid;
        assert!(admit(&modified).is_err(), "{pointer}");
    }
    let object = snapshot.as_object_mut().unwrap();
    object.remove("selection");
    object.remove("effective_config_path");
    snapshot["schema"] = json!("chrono-input-snapshot/v2");
    assert!(admit(&snapshot).is_ok());
    snapshot["schema"] = json!("chrono-input-snapshot/v1");
    assert_eq!(
        admit(&snapshot).unwrap_err(),
        "E_INPUT_SNAPSHOT: absence requires snapshot v2"
    );
    snapshot["files"] = json!({"inline":{"bytes":[0,255]}});
    assert!(admit(&snapshot).is_ok());
    snapshot["files"]["inline"]["bytes"] = json!([256]);
    assert_eq!(
        admit(&snapshot).unwrap_err(),
        "E_INPUT_BLOB: invalid retained byte array"
    );
}
