use chrono_inputs::test_support as selection;
use serde_json::{Value, json};
use std::collections::BTreeMap;

#[test]
fn sends_fixed_commits_to_filemap_and_its_test_ids_to_routes() {
    let commits = json!({"config":"cfg","base":"old","candidate":"new"});
    let docs = json!({"config":"cfg","base":{"cfg":{"a":1}},"candidate":{"cfg":{"b":2}}});
    let protocol = json!({"timeout_seconds":9,"stdout_limit_bytes":8192});
    let env = BTreeMap::from([
        ("PATH".into(), "/installed".into()),
        ("HOST_DECLARED".into(), "value".into()),
    ]);
    let mut calls = Vec::new();
    let selected =
        selection::selected_tests(&commits, docs.clone(), &protocol, &env, |cmd, input| {
            calls.push(cmd.program.clone());
            assert_eq!((cmd.timeout_seconds, cmd.output_limit_bytes), (9, 8192));
            let req: Value = serde_json::from_slice(input).unwrap();
            match cmd.program.as_str() {
                "chrono-judge-filemap" => {
                    assert_eq!(cmd.args, ["endpoint-tests"]);
                    assert_eq!(req, commits);
                    assert_eq!(cmd.env, env);
                    Ok((
                        0,
                        br#"{"tests":["test:a"],"retired_tests":["test:old"],"findings":[]}"#
                            .to_vec(),
                        vec![],
                    ))
                }
                "chrono-judge-routes" => {
                    assert_eq!(cmd.args, ["global-selection"]);
                    assert_eq!(cmd.env.len(), 1);
                    assert_eq!(cmd.env["PATH"], "/installed");
                    let mut expected = docs.clone();
                    expected["tests"] = json!(["test:a"]);
                    expected["retired_tests"] = json!(["test:old"]);
                    assert_eq!(req, expected);
                    Ok((0, br#"["test:a","test:replacement"]"#.to_vec(), vec![]))
                }
                _ => panic!("unexpected tool {}", cmd.program),
            }
        })
        .unwrap();
    assert_eq!(calls, ["chrono-judge-filemap", "chrono-judge-routes"]);
    assert_eq!(
        selected.into_iter().collect::<Vec<_>>(),
        ["test:a", "test:replacement"]
    );
}

#[test]
fn reports_original_findings_and_transports_failures() {
    let finding = json!({"code":"E_FILEMAP","level":"error","message":"missing edge","delta_refs":["/request"],"causes":[]});
    let env = BTreeMap::from([("PATH".into(), "/fixed".into())]);
    let protocol = json!({"timeout_seconds":3,"stdout_limit_bytes":4096});
    for (response, error) in [
        (
            Ok((
                0,
                serde_json::to_vec(&json!({"tests":[],"retired_tests":[],"findings":[finding]}))
                    .unwrap(),
                vec![],
            )),
            "E_COMPOSE_SELECTION:",
        ),
        (
            Ok((2, vec![], b"E_GIT_FACTS: observation\n".to_vec())),
            "E_GIT_FACTS: observation",
        ),
        (
            Ok((
                0,
                br#"{"tests":[],"retired_tests":[],"findings":[{"level":"error"}]}"#.to_vec(),
                vec![],
            )),
            "invalid endpoint-tests response:",
        ),
        (Err("process timeout".into()), "process timeout"),
        (
            Ok((0, b"{}".to_vec(), vec![])),
            "invalid endpoint-tests response:",
        ),
    ] {
        let mut response = Some(response);
        let reason = selection::selected_tests(&json!({}), json!({}), &protocol, &env, |cmd, _| {
            assert_eq!(cmd.program, "chrono-judge-filemap");
            response.take().unwrap()
        })
        .unwrap_err();
        assert!(reason.starts_with(error), "{reason}");
        if error == "E_COMPOSE_SELECTION:" {
            let findings: Vec<Value> =
                serde_json::from_str(reason.strip_prefix("E_COMPOSE_SELECTION: ").unwrap())
                    .unwrap();
            assert_eq!(findings, [finding.clone()]);
        }
    }
    for (reply, reason) in [
        (
            Ok((2, vec![], b"E_REQUIRED_TEST_REMOVED: test:old\n".to_vec())),
            "E_REQUIRED_TEST_REMOVED: test:old",
        ),
        (
            Ok((2, vec![], vec![])),
            "chrono-judge-routes global-selection exited with 2",
        ),
        (Err("process timeout".into()), "process timeout"),
        (
            Ok((0, b"{}".to_vec(), vec![])),
            "invalid global-selection response:",
        ),
    ] {
        let mut reply = Some(reply);
        assert!(
            selection::selected_tests(&json!({}), json!({}), &protocol, &env, |cmd, _| {
                if cmd.program == "chrono-judge-filemap" {
                    Ok((
                        0,
                        br#"{"tests":[],"retired_tests":[],"findings":[]}"#.to_vec(),
                        vec![],
                    ))
                } else {
                    reply.take().unwrap()
                }
            })
            .unwrap_err()
            .starts_with(reason)
        );
    }
}

#[test]
fn capture_uses_fixed_documents_and_checks_the_returned_selection() {
    let config = "config.json";
    let policy =
        json!({"schema_version":3, "protocol":{"timeout_seconds":8,"stdout_limit_bytes":4096}});
    let documents = BTreeMap::from([(config.to_owned(), policy)]);
    let expected = json!({"config":config,"documents":documents,"unit":"example"});
    let endpoint = selection::Endpoint {
        values: documents.clone(),
        effective_path: config.into(),
        selection: None,
    };
    let valid = json!({"schema":"chrono-input-snapshot/v2","effective_config":config,"selection":null,"required":["sdk"]});
    let run = |output: Value| {
        selection::capture_plan(
            config,
            &endpoint,
            Some("example"),
            "/tools",
            |cmd, input| {
                assert_eq!(cmd.program, "chrono-judge-registration");
                assert_eq!(cmd.args, ["capture-plan-v1"]);
                assert_eq!(cmd.env, BTreeMap::from([("PATH".into(), "/tools".into())]));
                assert_eq!((cmd.timeout_seconds, cmd.output_limit_bytes), (8, 4096));
                assert_eq!(serde_json::from_slice::<Value>(input).unwrap(), expected);
                Ok((0, serde_json::to_vec(&output).unwrap(), vec![]))
            },
        )
    };
    let plan = run(valid.clone()).unwrap();
    assert_eq!(plan.schema, "chrono-input-snapshot/v2");
    assert_eq!(plan.required.into_iter().collect::<Vec<_>>(), ["sdk"]);
    for (field, other) in [
        ("effective_config", json!("other")),
        ("selection", json!({})),
    ] {
        let mut wrong = valid.clone();
        wrong[field] = other;
        assert!(
            run(wrong)
                .err()
                .unwrap()
                .contains("fixed configuration selection")
        );
    }
    let failure = selection::capture_plan(config, &endpoint, None, "/tools", |_, input| {
        assert_eq!(
            serde_json::from_slice::<Value>(input).unwrap()["unit"],
            Value::Null
        );
        Ok((2, vec![], b"E_UNIT_ASSIGNMENT: unknown\n".to_vec()))
    });
    assert_eq!(failure.err().unwrap(), "E_UNIT_ASSIGNMENT: unknown");
}
