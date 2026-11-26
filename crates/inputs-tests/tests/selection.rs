#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::policy;
#[cfg(not(verus_keep_ghost))]
use chrono_inputs as policy;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::{prelude::*, vpanic as panic};

verus! {
#[cfg(verus_keep_ghost)]
fn only_exact_error_blocks_routes(findings: &[policy::Finding], at: usize)
    requires at < findings.len(),
{
    let rejected = policy::contains_error(findings);
    proof {
        if findings[at as int].level_view() == "error"@ { assert(rejected); }
        if forall|i: int| 0 <= i < findings.len() ==>
            #[trigger] findings[i].level_view() != "error"@ { assert(!rejected); }
    }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn query_status_and_empty_diagnostics() {
    proof { reveal_strlit(""); reveal_strlit("\n"); }
    let empty: [policy::Finding; 0] = [];
    let no_findings = !policy::contains_error(&empty);
    let ok = policy::query_succeeded(0);
    let positive = policy::query_succeeded(2);
    let negative = policy::query_succeeded(-1);
    let absent = policy::has_diagnostic("");
    let newline = policy::has_diagnostic("\n");
    if !no_findings || !ok || positive || negative || absent || !newline { panic!(); }
}

}

#[cfg(not(verus_keep_ghost))]
use chrono_inputs::test_support as selection;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeMap;

#[cfg(not(verus_keep_ghost))]
#[test]
fn routes_only_after_a_complete_selection_without_errors() {
    let protocol = json!({"timeout_seconds":3, "stdout_limit_bytes":4096});
    let env = BTreeMap::from([("PATH".into(), "/fixed".into())]);
    for (levels, blocked) in [
        (vec![], false),
        (vec!["warning", "Error", "error "], false),
        (vec!["warning", "error", "notice"], true),
        (vec!["error", "error"], true),
    ] {
        let findings: Vec<_> = levels
            .iter()
            .enumerate()
            .map(|(i, level)| {
                json!({"code":format!("C{i}"), "level":level, "message":format!("message {i}"),
                   "delta_refs":["/request"], "causes":[]})
            })
            .collect();
        let mut calls = Vec::new();
        let selected =
            selection::selected_tests(&json!({}), json!({}), &protocol, &env, |command, input| {
                calls.push(command.program.clone());
                match command.program.as_str() {
                    "chrono-judge-filemap" => Ok((
                        0,
                        serde_json::to_vec(&json!({
                            "tests":["current"], "retired_tests":["retired"], "findings":findings
                        }))
                        .unwrap(),
                        vec![],
                    )),
                    "chrono-judge-routes" => {
                        let request: Value = serde_json::from_slice(input).unwrap();
                        assert_eq!(request["tests"], json!(["current"]));
                        assert_eq!(request["retired_tests"], json!(["retired"]));
                        Ok((0, br#"["selected"]"#.to_vec(), vec![]))
                    }
                    other => panic!("unexpected command {other}"),
                }
            });
        if blocked {
            let error = selected.unwrap_err();
            let actual: Vec<Value> =
                serde_json::from_str(error.strip_prefix("E_COMPOSE_SELECTION: ").unwrap()).unwrap();
            assert_eq!(actual, findings);
            assert_eq!(calls, ["chrono-judge-filemap"]);
        } else {
            assert_eq!(selected.unwrap(), ["selected".to_owned()].into());
            assert_eq!(calls, ["chrono-judge-filemap", "chrono-judge-routes"]);
        }
    }
}

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
#[test]
fn capture_uses_fixed_documents_and_checks_the_returned_selection() {
    let config = "config.json";
    let policy =
        json!({"schema_version":3, "protocol":{"timeout_seconds":8,"stdout_limit_bytes":4096}});
    let mut policy = policy;
    let image = ".chrono-harness/bin/chrono-ci";
    policy["tools"] = json!([{"id":"chrono-ci","program":image}]);
    policy["environment"] = json!({"inputs":[{"id":"ci-image","location":image,"presence":"present","sha256":"a".repeat(64)},{"id":"sdk","location":"sdk","presence":"present","sha256":"b".repeat(64)}]});
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
    let mut image_reply = valid.clone();
    image_reply["required"] = json!(["ci-image"]);
    image_reply["installed_paths"] = json!({"ci-image":"/opt/tools/chrono-ci"});
    assert!(run(image_reply.clone()).is_ok());
    for (id, location) in [
        ("ci-image", "relative"),
        ("sdk", "/opt/tools/sdk"),
        ("ghost", "/opt/tools/ghost"),
    ] {
        let mut wrong = image_reply.clone();
        wrong["required"] = json!([id]);
        wrong["installed_paths"] = json!({(id):location});
        assert!(run(wrong).is_err());
    }
    let mut multiple = image_reply.clone();
    multiple["required"] = json!(["b", "a"]);
    multiple["installed_paths"] = json!({"b": "later", "a": "first"});
    assert_eq!(
        run(multiple.clone()).err().unwrap(),
        "E_INPUT_PATH: invalid installed tool mapping for a"
    );
    multiple["selection"] = json!({});
    assert!(
        run(multiple)
            .err()
            .unwrap()
            .contains("fixed configuration selection")
    );
    image_reply["required"] = json!([]);
    assert!(run(image_reply).is_err());
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

#[cfg(not(verus_keep_ghost))]
#[test]
fn artifact_session_preserves_requests_replies_and_terminal_order() {
    use chrono_inputs::test_support::exchange;
    use std::{
        cell::{Cell, RefCell},
        io::{self, Cursor, Write},
        os::unix::process::ExitStatusExt,
        process::ExitStatus,
    };

    struct Request<'a> {
        bytes: &'a RefCell<Vec<u8>>,
        closed: &'a Cell<bool>,
        failure: Option<&'static str>,
    }
    impl Write for Request<'_> {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.failure == Some("write") || (self.failure == Some("newline") && bytes == b"\n")
            {
                return Err(io::Error::other(self.failure.unwrap()));
            }
            self.bytes.borrow_mut().extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            if self.failure == Some("flush") {
                Err(io::Error::other("flush"))
            } else {
                Ok(())
            }
        }
    }
    impl Drop for Request<'_> {
        fn drop(&mut self) {
            self.closed.set(true);
        }
    }

    let bytes = RefCell::new(Vec::new());
    let closed = Cell::new(false);
    let open = |failure| {
        Some(Request {
            bytes: &bytes,
            closed: &closed,
            failure,
        })
    };
    let message = json!({"operation":"accepts"});
    let unexpected_wait = || panic!("unexpected child wait");
    let mut input = open(None);
    let mut replies = Cursor::new(b"{\"Ok\":true}\n{\"Err\":\"producer error\"}\n!\n\n");
    assert_eq!(
        exchange(&mut input, &mut replies, &message, unexpected_wait),
        Ok(true)
    );
    assert_eq!(bytes.borrow().as_slice(), b"{\"operation\":\"accepts\"}\n");
    assert_eq!(
        exchange::<bool>(&mut input, &mut replies, &message, unexpected_wait),
        Err("producer error".into())
    );
    for _ in 0..2 {
        assert!(
            exchange::<bool>(&mut input, &mut replies, &message, unexpected_wait)
                .unwrap_err()
                .starts_with("invalid artifact response:")
        );
    }
    let eof = exchange::<bool>(&mut input, &mut replies, &message, || {
        assert!(closed.get());
        Ok(ExitStatus::from_raw(7 << 8))
    });
    assert_eq!(
        eof,
        Err("artifact producer ended before its response: exit status: 7".into())
    );
    assert_eq!(
        exchange::<bool>(&mut input, &mut replies, &message, unexpected_wait),
        Err("artifact producer has ended".into())
    );

    for failure in ["write", "newline", "flush"] {
        let mut replies = Cursor::new(b"unread");
        assert_eq!(
            exchange::<bool>(
                &mut open(Some(failure)),
                &mut replies,
                &message,
                unexpected_wait
            ),
            Err(failure.into())
        );
        assert_eq!(replies.position(), 0);
    }
    let bad_utf8 = exchange::<bool>(
        &mut open(None),
        &mut Cursor::new([0xff]),
        &message,
        unexpected_wait,
    );
    assert_eq!(
        bad_utf8.unwrap_err(),
        io::Error::new(
            io::ErrorKind::InvalidData,
            "stream did not contain valid UTF-8"
        )
        .to_string()
    );
    let wait_error = exchange::<bool>(&mut open(None), &mut Cursor::new([]), &message, || {
        Err(io::Error::other("wait failed"))
    });
    assert_eq!(wait_error, Err("wait failed".into()));
}
