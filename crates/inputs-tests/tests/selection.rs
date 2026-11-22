#[path = "../../inputs/src/routes.rs"]
mod routes;
use serde_json::{Value, json};
#[test]
fn passes_fixed_registries_and_preserves_route_retirement_errors() {
    let endpoints = json!({"config":"cfg","base":{"cfg":{"old":true}},"candidate":{"cfg":{}},"tests":[],"retired_tests":["test:old"]});
    let protocol = json!({"timeout_seconds":9,"stdout_limit_bytes":8192});
    let result = routes::selected_tests(
        &endpoints,
        &protocol,
        "/installed".into(),
        |command, input| {
            assert_eq!(command.args, ["global-selection"]);
            assert_eq!(command.program, "chrono-judge-routes");
            assert_eq!(command.env["PATH"], "/installed");
            assert_eq!(
                (command.timeout_seconds, command.output_limit_bytes),
                (9, 8192)
            );
            assert_eq!(serde_json::from_slice::<Value>(input).unwrap(), endpoints);
            Ok((0, br#"["test:replacement"]"#.to_vec(), vec![]))
        },
    )
    .unwrap();
    assert_eq!(result.into_iter().collect::<Vec<_>>(), ["test:replacement"]);
    for (response, error) in [
        (
            Ok((2, vec![], b"E_REQUIRED_TEST_REMOVED: test:old\n".to_vec())),
            "E_REQUIRED_TEST_REMOVED: test:old",
        ),
        (Ok((2, vec![], vec![])), "route selection exited with 2"),
        (Err("process timeout".into()), "process timeout"),
        (Ok((0, b"{}".to_vec(), vec![])), "invalid route selection:"),
    ] {
        assert!(
            routes::selected_tests(&endpoints, &protocol, "/installed".into(), |_, _| response)
                .unwrap_err()
                .starts_with(error)
        );
    }
}
