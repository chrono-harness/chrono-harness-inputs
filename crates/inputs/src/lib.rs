//! Snapshot transport, not dependency discovery or a governance verdict.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
#[derive(Clone, Copy)]
pub enum InputKind { Capture, Compose, Pair }

pub enum InputAction<'a> {
    Version,
    Help,
    Command(InputCommand<'a>),
}

/// The validated command borrows its original argv; no second option inventory is built.
pub struct InputCommand<'a> {
    pub kind: InputKind,
    pub arguments: &'a [String],
}

pub struct MissingInputOption<'a> {
    pub key: &'a str,
}

pub open spec fn input_kind(text: Seq<char>) -> Option<InputKind> {
    if text == "capture"@ { Some(InputKind::Capture) }
    else if text == "compose"@ { Some(InputKind::Compose) }
    else if text == "pair"@ { Some(InputKind::Pair) }
    else { None }
}

pub open spec fn input_key_allowed(kind: InputKind, key: Seq<char>) -> bool {
    key == "--host-root"@ || key == "--output"@ || key == "--report-consumer"@ || match kind {
        InputKind::Capture => key == "--config"@ || key == "--commit"@ || key == "--unit"@,
        InputKind::Compose => key == "--config"@ || key == "--base"@ || key == "--candidate"@
            || key == "--manifest"@ || key == "--receipt"@,
        InputKind::Pair => key == "--base-snapshot"@ || key == "--candidate-snapshot"@
            || key == "--base-root"@ || key == "--candidate-root"@,
    }
}

fn allowed_input_key(kind: InputKind, key: &str) -> (allowed: bool)
    ensures allowed == input_key_allowed(kind, key@),
{
    <&str>::exec_eq(key, "--host-root") || <&str>::exec_eq(key, "--output")
        || <&str>::exec_eq(key, "--report-consumer")
        || match kind {
            InputKind::Capture => <&str>::exec_eq(key, "--config")
                || <&str>::exec_eq(key, "--commit") || <&str>::exec_eq(key, "--unit"),
            InputKind::Compose => <&str>::exec_eq(key, "--config")
                || <&str>::exec_eq(key, "--base") || <&str>::exec_eq(key, "--candidate")
                || <&str>::exec_eq(key, "--manifest") || <&str>::exec_eq(key, "--receipt"),
            InputKind::Pair => <&str>::exec_eq(key, "--base-snapshot")
                || <&str>::exec_eq(key, "--candidate-snapshot")
                || <&str>::exec_eq(key, "--base-root") || <&str>::exec_eq(key, "--candidate-root"),
        }
}

pub open spec fn input_prefix_valid(args: Seq<String>, kind: InputKind, pairs: int) -> bool {
    0 <= pairs <= (args.len() - 1) / 2 && forall|i: int| 0 <= i < pairs ==>
        input_key_allowed(kind, (#[trigger] args[1 + 2 * i])@)
        && forall|j: int| 0 <= j < i ==> (#[trigger] args[1 + 2 * j])@ != args[1 + 2 * i]@
}

pub open spec fn input_command_valid(command: InputCommand) -> bool {
    let args = command.arguments@;
    args.len() > 0 && args.len() % 2 == 1 && input_kind(args[0]@) == Some(command.kind)
        && input_prefix_valid(args, command.kind, (args.len() - 1) / 2)
}

pub open spec fn input_command_result(args: Seq<String>) -> Option<Seq<char>> {
    if args.len() == 0 { Some("E_USAGE: capture or pair required"@) }
    else if args.len() == 1 && (args[0]@ == "--version"@ || args[0]@ == "--help"@) { None }
    else { match input_kind(args[0]@) {
        None => Some("E_USAGE: unknown command"@),
        Some(kind) => if !input_prefix_valid(args, kind, (args.len() - 1) / 2) {
            Some("E_USAGE: unknown or duplicate option"@)
        } else if args.len() % 2 == 0 { Some("E_USAGE: option needs a value"@) }
        else { None },
    } }
}

/// Return the first matching complete key/value pair from the specified original prefix.
fn find_input_option(args: &[String], pairs: usize, key: &str) -> (found: Option<usize>)
    requires args.len() > 0, pairs <= (args.len() - 1) / 2,
    ensures match found {
        Some(i) => i < pairs && args@[1 + 2 * i]@ == key@
            && forall|j: int| 0 <= j < i ==> (#[trigger] args@[1 + 2 * j])@ != key@,
        None => forall|j: int| 0 <= j < pairs ==> (#[trigger] args@[1 + 2 * j])@ != key@,
    },
{
    let mut i = 0;
    while i < pairs
        invariant args.len() > 0, pairs <= (args.len() - 1) / 2, i <= pairs,
            forall|j: int| 0 <= j < i ==> (#[trigger] args@[1 + 2 * j])@ != key@,
        decreases pairs - i,
    {
        if <&str>::exec_eq(args[1 + 2 * i].as_str(), key) { return Some(i); }
        i += 1;
    }
    None
}

impl<'a> InputCommand<'a> {
    pub fn option(&self, key: &str) -> (value: Option<&'a str>)
        requires input_command_valid(*self),
        ensures match value {
            Some(value) => exists|i: int| 0 <= i < (self.arguments@.len() - 1) / 2
                && (#[trigger] self.arguments@[1 + 2 * i])@ == key@ && value@ == self.arguments@[2 + 2 * i]@,
            None => forall|i: int| 0 <= i < (self.arguments@.len() - 1) / 2
                ==> (#[trigger] self.arguments@[1 + 2 * i])@ != key@,
        },
    {
        match find_input_option(self.arguments, (self.arguments.len() - 1) / 2, key) {
            Some(i) => Some(self.arguments[2 + 2 * i].as_str()),
            None => None,
        }
    }

    pub fn required<'k>(&self, key: &'k str) -> (value: Result<&'a str, MissingInputOption<'k>>)
        requires input_command_valid(*self),
        ensures match value {
            Ok(value) => exists|i: int| 0 <= i < (self.arguments@.len() - 1) / 2
                && (#[trigger] self.arguments@[1 + 2 * i])@ == key@ && value@ == self.arguments@[2 + 2 * i]@,
            Err(error) => error.key@ == key@
                && forall|i: int| 0 <= i < (self.arguments@.len() - 1) / 2
                    ==> (#[trigger] self.arguments@[1 + 2 * i])@ != key@,
        },
    {
        match self.option(key) {
            Some(value) => Ok(value),
            None => Err(MissingInputOption { key }),
        }
    }
}

pub fn parse_input_command(args: &[String]) -> (out: Result<InputAction<'_>, String>)
    ensures match out {
        Err(error) => input_command_result(args@) == Some(error@),
        Ok(action) => input_command_result(args@).is_none() && match action {
            InputAction::Version => args@.len() == 1 && args@[0]@ == "--version"@,
            InputAction::Help => args@.len() == 1 && args@[0]@ == "--help"@,
            InputAction::Command(command) => input_command_valid(command) && command.arguments@ == args@,
        },
    },
{
    if args.len() == 0 { return Err("E_USAGE: capture or pair required".to_string()); }
    let first = args[0].as_str();
    if args.len() == 1 && <&str>::exec_eq(first, "--version") { return Ok(InputAction::Version); }
    if args.len() == 1 && <&str>::exec_eq(first, "--help") { return Ok(InputAction::Help); }
    let kind = if <&str>::exec_eq(first, "capture") { InputKind::Capture }
        else if <&str>::exec_eq(first, "compose") { InputKind::Compose }
        else if <&str>::exec_eq(first, "pair") { InputKind::Pair }
        else { return Err("E_USAGE: unknown command".to_string()); };
    let pairs = (args.len() - 1) / 2;
    let mut i = 0;
    while i < pairs
        invariant args.len() > 0, pairs == (args.len() - 1) / 2, i <= pairs,
            input_kind(args@[0]@) == Some(kind), input_prefix_valid(args@, kind, i as int),
        decreases pairs - i,
    {
        let key = args[1 + 2 * i].as_str();
        if !allowed_input_key(kind, key) || find_input_option(args, i, key).is_some() {
            assert(!input_prefix_valid(args@, kind, pairs as int));
            return Err("E_USAGE: unknown or duplicate option".to_string());
        }
        proof {
            assert forall|j: int| 0 <= j < i + 1 implies
                input_key_allowed(kind, (#[trigger] args@[1 + 2 * j])@)
                    && forall|k: int| 0 <= k < j ==> (#[trigger] args@[1 + 2 * k])@ != args@[1 + 2 * j]@ by {
                if j < i { assert(input_key_allowed(kind, args@[1 + 2 * j]@)); }
            }
        }
        i += 1;
    }
    if args.len() % 2 == 0 { return Err("E_USAGE: option needs a value".to_string()); }
    Ok(InputAction::Command(InputCommand { kind, arguments: args }))
}

/// A completed line belongs to the decoder. EOF belongs to the producer's exit report.
pub fn artifact_response_line<T>(read: Result<(usize, T), String>) -> (out: Result<Option<T>, String>)
    ensures match read {
        Err(error) => out == Err::<Option<T>, String>(error),
        Ok((count, line)) => if count == 0 { out == Ok::<Option<T>, String>(None) }
            else { out == Ok::<Option<T>, String>(Some(line)) },
    },
{
    match read {
        Err(error) => Err(error),
        Ok((0, _)) => Ok(None),
        Ok((_, line)) => Ok(Some(line)),
    }
}

/// All current capture and composition paths use the same exact blob identity.
pub fn blob_identity_matches(actual: &str, actual_length: u64,
    expected: &str, expected_length: u64) -> (matches: bool)
    ensures matches == (actual@ == expected@ && actual_length == expected_length),
{
    <&str>::exec_eq(actual, expected) && actual_length == expected_length
}
}

#[cfg(not(verus_keep_ghost))]
mod artifacts;
#[cfg(not(verus_keep_ghost))]
mod command;
#[cfg(not(verus_keep_ghost))]
use artifacts::Store;
pub mod capture_mapping;
pub mod command_frame;
pub mod composition;
pub mod retained_shape;
#[cfg(not(verus_keep_ghost))]
mod selection;
#[cfg(all(feature = "test-support", not(verus_keep_ghost)))]
pub mod test_support {
    pub use crate::artifacts::exchange;
    pub use crate::files::sha256;
    pub use crate::selection::{Endpoint, capture_plan, selected_tests};
    pub use crate::snapshot::snapshot_shape;
}
#[cfg(not(verus_keep_ghost))]
mod custody {
    //! Input callers own their exact output capability until handoff or last use.
    use super::*;

    /// Keep this value alive while using its retained paths. Serialization copies
    /// the snapshot, not its ownership; a different process needs an explicit handoff.
    pub struct Produced {
        pub(crate) value: Value,
        root: Store,
        primary: String,
    }

    impl std::ops::Deref for Produced {
        type Target = Value;
        fn deref(&self) -> &Value {
            &self.value
        }
    }
    impl std::fmt::Debug for Produced {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            std::fmt::Debug::fmt(&self.value, f)
        }
    }
    impl PartialEq for Produced {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }
    impl PartialEq<Value> for Produced {
        fn eq(&self, other: &Value) -> bool {
            &self.value == other
        }
    }
    impl PartialEq<Produced> for Value {
        fn eq(&self, other: &Produced) -> bool {
            self == &other.value
        }
    }
    impl serde::Serialize for Produced {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serde::Serialize::serialize(&self.value, serializer)
        }
    }
    impl Produced {
        pub(crate) fn new(root: &Store, primary: &str, value: Value) -> Result<Self, String> {
            Ok(Self {
                root: root.clone(),
                primary: primary.into(),
                value,
            })
        }
        pub fn handoff(&self, consumer: &str) -> Result<Value, String> {
            self.root.call(value!({"operation":"protect-consumer","producer":"full-original","path":self.primary,"consumer":consumer,"purpose":"调用方保管输入导出，直到后续使用完成或已交接，并释放此声明"}))
        }
    }

    pub(crate) fn blobs(snapshot: &Value) -> Vec<String> {
        snapshot["files"]
            .as_object()
            .into_iter()
            .flat_map(|files| files.values())
            .filter_map(|file| file["blob"].as_str().map(str::to_owned))
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect()
    }

    pub(crate) struct BoundedFile {
        file: fs::File,
        remaining: u64,
    }
    impl Write for BoundedFile {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if bytes.len() as u64 > self.remaining {
                return Err(std::io::Error::other(
                    "E_INPUT_BLOB: source exceeds declared length",
                ));
            }
            let written = self.file.write(bytes)?;
            self.remaining -= written as u64;
            Ok(written)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.file.flush()
        }
    }

    /// A registered staging allocation survives interruption under the same finite
    /// owner policy. Unadopted callers retain the ordinary RAII cleanup behavior.
    #[derive(serde::Deserialize)]
    struct Stage {
        path: PathBuf,
        managed: bool,
    }
    pub(crate) struct StagedBlob {
        pub path: PathBuf,
        managed: bool,
        owner: Store,
    }
    impl Drop for StagedBlob {
        fn drop(&mut self) {
            if !self.managed {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
    impl StagedBlob {
        pub(crate) fn copy_original(
            root: &Store,
            length: u64,
            artifacts: &Value,
            original: &str,
            transport: Option<&composition::ArtifactTransport>,
        ) -> Result<(Self, String, u64), String> {
            fs::create_dir_all(state(root, BLOB_DIRECTORY)?).map_err(|e| e.to_string())?;
            let selected:Stage=root.call(value!({"operation":"new-stage","producer":"full-original","directory":BLOB_DIRECTORY,"prefix":"input-stage","suffix":".bytes","length":length,"outcome":{"kind":"input-staging","outcome":"not-established"}}))?;
            let stage = Self {
                path: selected.path,
                managed: selected.managed,
                owner: root.clone(),
            };
            #[derive(serde::Deserialize)]
            struct Identity {
                sha256: String,
                length: u64,
            }
            let identity:Identity = root.call(value!({"operation":"copy-original","path":original,"transport":transport,"artifacts":artifacts,"target":stage.path,"length":length})).map_err(|e|format!("{e}; input staging original: {}",stage.path.display()))?;
            root.call::<()>(value!({"operation":"seal-stage","path":stage.path,"outcome":{"kind":"input-staging","sha256":identity.sha256,"length":identity.length}}))?;
            Ok((stage, identity.sha256, identity.length))
        }
        pub fn write(
            root: &Store,
            length: u64,
            write: impl FnOnce(&mut BoundedFile) -> Result<(String, u64), String>,
        ) -> Result<(Self, String, u64), String> {
            let directory = state(root, BLOB_DIRECTORY)?;
            fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
            let (path, managed) = if root.adopted() {
                let stage:Stage = root.call(value!({"operation":"new-stage","producer":"full-original","directory":BLOB_DIRECTORY,"prefix":"input-stage","suffix":".bytes","length":length,"outcome":{"kind":"input-staging","outcome":"not-established"}}))?;
                (stage.path, stage.managed)
            } else {
                let stage = tempfile::Builder::new()
                    .prefix("input-stage")
                    .suffix(".bytes")
                    .tempfile_in(directory)
                    .map_err(|e| e.to_string())?;
                let (_, path) = stage.keep().map_err(|e| e.error.to_string())?;
                (path, false)
            };
            let stage = Self {
                path,
                managed,
                owner: root.clone(),
            };
            let mut output = BoundedFile {
                file: fs::OpenOptions::new()
                    .write(true)
                    .open(&stage.path)
                    .map_err(|e| e.to_string())?,
                remaining: length,
            };
            let (digest, copied) = write(&mut output)
                .map_err(|e| format!("{e}; input staging original: {}", stage.path.display()))?;
            if copied != length || output.remaining != 0 {
                return Err(format!(
                    "E_INPUT_BLOB: source length changed; input staging original: {}",
                    stage.path.display()
                ));
            }
            output.file.sync_all().map_err(|e| e.to_string())?;
            if stage.managed {
                stage.owner.call::<()>(value!({"operation":"seal-stage","path":stage.path,"outcome":{"kind":"input-staging","sha256":digest,"length":copied}}))?;
            }
            Ok((stage, digest, copied))
        }
    }
}

#[cfg(not(verus_keep_ghost))]
mod files;
#[cfg(not(verus_keep_ghost))]
use files as wire;
#[cfg(not(verus_keep_ghost))]
use files::{copy_hashed, file_identity, json, no_symlink_parents, observe_file, sha256};
mod snapshot;
#[cfg(not(verus_keep_ghost))]
pub use composition::{Manifest as CompositionManifest, Source as CompositionSource, compose};
#[cfg(not(verus_keep_ghost))]
pub use custody::Produced;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json as value};
#[cfg(not(verus_keep_ghost))]
use snapshot::snapshot_shape;
pub use snapshot::{FieldError, field_declared, first_field_error};
#[cfg(not(verus_keep_ghost))]
pub use snapshot::{SNAPSHOT_SCHEMA, SNAPSHOT_SCHEMA_V2, SNAPSHOT_SCHEMA_V3};
#[cfg(not(verus_keep_ghost))]
use std::{
    fs,
    io::{Read, Seek, Write},
    path::{Path, PathBuf},
};
#[cfg(not(verus_keep_ghost))]
const BLOB_DIRECTORY: &str = ".chrono-harness/state/inputs/blobs";

#[cfg(not(verus_keep_ghost))]
fn state(root: &Path, path: &str) -> Result<PathBuf, String> {
    if !files::valid_host_state_path(path) {
        return Err("E_INPUT_PATH: output/reference must be within host state".into());
    }
    no_symlink_parents(root, path)
}
#[cfg(not(verus_keep_ghost))]
fn output_path(root: &Path, path: &str) -> Result<PathBuf, String> {
    let target = state(root, path)?;
    let parent = target
        .parent()
        .ok_or("E_INPUT_OUTPUT_PARENT: missing parent")?;
    if parent != root.join(".chrono-harness/state") {
        let metadata = fs::symlink_metadata(parent)
            .map_err(|e| format!("E_INPUT_OUTPUT_PARENT: {}: {e}", parent.display()))?;
        if !metadata.is_dir() {
            return Err(format!(
                "E_INPUT_OUTPUT_PARENT: {} is not a physical directory",
                parent.display()
            ));
        }
    }
    Ok(target)
}
#[cfg(not(verus_keep_ghost))]
fn publish(root: &Store, path: &str, v: &Value) -> Result<(), String> {
    let bytes = wire::canonical(v)?;
    publish_bytes(root, path, &bytes)
}
#[cfg(not(verus_keep_ghost))]
fn publish_bytes(root: &Store, path: &str, bytes: &[u8]) -> Result<(), String> {
    let target = output_path(root, path)?;
    let parent = target.parent().ok_or("snapshot parent")?;
    if parent == root.join(".chrono-harness/state") {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    if root.publish_text(
        path,
        bytes,
        value!({"kind":"input-original","sha256":sha256(bytes),"length":bytes.len()}),
    )? {
        return Ok(());
    }
    if target.exists() {
        if fs::read(&target).map_err(|e| e.to_string())? == bytes {
            return Ok(());
        }
        return Err("E_SNAPSHOT_EXISTS: retain old snapshot; choose a new output path".into());
    }
    let mut tmp = tempfile::NamedTempFile::new_in(parent).map_err(|e| e.to_string())?;
    tmp.write_all(bytes).map_err(|e| e.to_string())?;
    tmp.persist_noclobber(&target).map_err(|e| e.to_string())?;
    Ok(())
}
#[cfg(not(verus_keep_ghost))]
fn store(root: &Store, input: &Path) -> Result<Value, String> {
    let _input = input
        .strip_prefix(&**root)
        .ok()
        .and_then(|path| path.to_str())
        .map(|path| root.retain(path))
        .transpose()?;
    if !fs::metadata(input)
        .map_err(|e| format!("E_INPUT_READ: {}: {e}", input.display()))?
        .is_file()
    {
        return Err("E_INPUT_READ: not a regular file".into());
    }
    let mut file =
        fs::File::open(input).map_err(|e| format!("E_INPUT_READ: {}: {e}", input.display()))?;
    if !file.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err("E_INPUT_READ: not a regular file".into());
    }
    let length = file.metadata().map_err(|e| e.to_string())?.len();
    if root.adopted() {
        let (sha256, observed_length) =
            copy_hashed((&mut file).take(length.saturating_add(1)), std::io::sink())?;
        if observed_length != length {
            return Err("E_INPUT_BLOB: source length changed".into());
        }
        let path = format!("{BLOB_DIRECTORY}/{sha256}");
        // The blob owner already reserves before writing and verifies the
        // bounded source copy. A second managed staging original has no caller.
        if root
            .publish_file(
                &path,
                input,
                &sha256,
                length,
                value!({"kind":"input-blob","sha256":sha256,"length":length}),
            )
            .map_err(|e| format!("E_INPUT_BLOB: {e}"))?
        {
            return Ok(value!({"blob":path,"sha256":sha256,"length":length}));
        }
        file.rewind().map_err(|e| e.to_string())?;
    }
    let (stage, sha256, length) =
        custody::StagedBlob::write(root, length, |output| copy_hashed(file, output))?;
    publish_blob(root, &stage.path, sha256, length)
}
// The caller hashes all bytes written to its private temporary file before publication.
#[cfg(not(verus_keep_ghost))]
fn publish_blob(root: &Store, staged: &Path, sha256: String, length: u64) -> Result<Value, String> {
    let path = format!("{BLOB_DIRECTORY}/{sha256}");
    let target = state(root, &path)?;
    if root
        .publish_file(
            &path,
            staged,
            &sha256,
            length,
            value!({"kind":"input-blob","sha256":sha256,"length":length}),
        )
        .map_err(|e| format!("E_INPUT_BLOB: {e}"))?
    {
        return Ok(value!({"blob":path,"sha256":sha256,"length":length}));
    }
    if target.exists() {
        let observed = file_identity(&target)?;
        if !blob_identity_matches(&observed.0, observed.1, &sha256, length) {
            return Err("E_INPUT_BLOB: existing content does not match its address".into());
        }
    } else if let Err(error) = fs::hard_link(staged, &target) {
        if error.kind() != std::io::ErrorKind::AlreadyExists {
            return Err(format!("E_INPUT_BLOB: {error}"));
        }
        let observed = file_identity(&target)?;
        if !blob_identity_matches(&observed.0, observed.1, &sha256, length) {
            return Err(format!("E_INPUT_BLOB: {error}"));
        }
    }
    Ok(value!({"blob":path,"sha256":sha256,"length":length}))
}
#[cfg(not(verus_keep_ghost))]
pub fn capture(root: &Path, config: &str, commit: &str, output: &str) -> Result<Produced, String> {
    capture_selected(root, config, commit, output, &Selection::All)
}
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug)]
pub enum Selection {
    All,
    Unit { unit: String },
    Collect,
}
#[cfg(not(verus_keep_ghost))]
pub fn capture_selected(
    root: &Path,
    config: &str,
    commit: &str,
    output: &str,
    selection: &Selection,
) -> Result<Produced, String> {
    let ownership = Store::open(root)?;
    let root = &ownership;
    let unit = match selection {
        Selection::All => None,
        Selection::Unit { unit } => Some(unit.as_str()),
        Selection::Collect => return Err("E_INPUT_SCOPE: collection consumes original snapshots; it does not capture live inputs".into()),
    };
    output_path(root, output)?;
    let [endpoint]: [selection::Endpoint; 1] =
        selection::endpoints(root, config, commit, commit, true)?
            .try_into()
            .map_err(|_| "missing checked-out endpoint")?;
    let path = std::env::var("PATH").map_err(|error| error.to_string())?;
    let plan = selection::capture_plan(config, &endpoint, unit, &path, |spec, input| {
        command::run(root, spec, input)
    })?;
    let effective = endpoint
        .values
        .get(&plan.effective_config)
        .ok_or("missing capture configuration")?;
    let credentials = if effective["schema_version"] == 4 {
        selection::input_profile(root, effective, false)?.credential_environment
    } else {
        Default::default()
    };
    let mut environment = serde_json::Map::new();
    for key in effective["environment"]["inherit"]
        .as_array()
        .ok_or("invalid inherited environment")?
    {
        let key = key.as_str().ok_or("invalid inherited variable")?;
        let v = if credentials.contains(key) {
            Value::Null
        } else {
            match std::env::var(key) {
                Ok(v) => Value::String(v),
                Err(std::env::VarError::NotPresent) => Value::Null,
                Err(_) => return Err(format!("E_INPUT_ENVIRONMENT: non-UTF8 value for {key}")),
            }
        };
        environment.insert(key.into(), v);
    }
    let mut files = serde_json::Map::new();
    for input in effective["environment"]["inputs"]
        .as_array()
        .ok_or("invalid registered inputs")?
    {
        let id = input["id"].as_str().ok_or("invalid input id")?;
        if !plan.required.contains(id) {
            continue;
        }
        let location = input["location"].as_str().ok_or("invalid input location")?;
        let installed = plan.installed_paths.get(id);
        let path = installed.cloned().unwrap_or_else(|| root.join(location));
        let retained = if matches!(effective["schema_version"].as_u64(), Some(2 | 3 | 4)) {
            let identity = observe_file(&path)?;
            if installed.is_some()
                && identity.as_ref().map(|(digest, _)| digest.as_str()) != input["sha256"].as_str()
            {
                return Err(format!(
                    "E_INPUT_READ: installed tool digest or presence differs: {id}"
                ));
            }
            match identity {
                None => value!({"absent":true}),
                Some(identity) => {
                    let observed = store(root, &path)?;
                    if observed["sha256"] != identity.0 || observed["length"] != identity.1 {
                        return Err("E_INPUT_READ: input changed during capture".into());
                    }
                    observed
                }
            }
        } else {
            store(root, &path)?
        };
        files.insert(id.into(), retained);
    }
    let mut snapshot = value!({"schema":plan.schema,"commit":commit,"config_path":config,"config_digest":wire::digest(effective)?,"environment":environment,"files":files});
    if let Some(selection) = plan.selection {
        snapshot["effective_config_path"] = value!(plan.effective_config);
        snapshot["selection"] = selection;
    }
    publish(root, output, &snapshot)?;
    root.dependencies(output, &custody::blobs(&snapshot))?;
    Produced::new(root, output, snapshot)
}

/// Transport reads references only after snapshot_shape has admitted every record.
#[cfg(not(verus_keep_ghost))]
fn captured_blob<'a>(
    file: &'a Value,
    inline_error: &str,
) -> Result<Option<(&'a str, &'a str, u64)>, String> {
    if file["absent"] == true {
        return Ok(None);
    }
    let path = file["blob"].as_str().ok_or(inline_error)?;
    let digest = file["sha256"]
        .as_str()
        .ok_or("missing captured file digest")?;
    let length = file["length"]
        .as_u64()
        .ok_or("missing captured file length")?;
    Ok(Some((path, digest, length)))
}

#[cfg(not(verus_keep_ghost))]
fn transport(from: &Store, snapshot: &str, to: &Store) -> Result<Value, String> {
    from.retain(snapshot)?;
    let bytes = fs::read(state(from, snapshot)?).map_err(|e| e.to_string())?;
    let mut v = json(&bytes)?;
    snapshot_shape(&v)?;
    let files = v["files"]
        .as_object_mut()
        .ok_or("E_INPUT_SNAPSHOT: missing files")?;
    for f in files.values_mut() {
        let Some((blob, digest, length)) =
            captured_blob(f, "E_INPUT_BLOB: pair requires captured blob references")?
        else {
            continue;
        };
        from.retain(blob)?;
        let path = state(from, blob)?;
        let observed = store(to, &path)?;
        if observed["sha256"] != digest || observed["length"] != length {
            return Err("E_INPUT_BLOB: retained bytes differ from snapshot".into());
        }
        *f = observed;
    }
    Ok(v)
}
#[cfg(not(verus_keep_ghost))]
pub fn pair(
    root: &Path,
    base_root: &Path,
    base: &str,
    candidate_root: &Path,
    candidate: &str,
    output: &str,
) -> Result<Produced, String> {
    let ownership = Store::open(root)?;
    let root = &ownership;
    // Source capabilities survive both transports and the destination handoff.
    let base_root = Store::open(base_root)?;
    let candidate_root = Store::open(candidate_root)?;
    output_path(root, output)?;
    let a = transport(&base_root, base, root)?;
    let b = transport(&candidate_root, candidate, root)?;
    let v = value!({"base":a,"candidate":b});
    publish(root, output, &v)?;
    let mut blobs = custody::blobs(&v["base"]);
    blobs.extend(custody::blobs(&v["candidate"]));
    blobs.sort();
    blobs.dedup();
    root.dependencies(output, &blobs)?;
    Produced::new(root, output, v)
}
#[cfg(not(verus_keep_ghost))]
pub fn run(cwd: &Path, args: &[String]) -> Result<String, String> {
    let command = match parse_input_command(args)? {
        InputAction::Version => return Ok(format!("chrono-inputs {}\n", env!("CARGO_PKG_VERSION"))),
        InputAction::Help => return Ok("chrono-inputs capture --host-root H --config P --commit OID --output P [--unit ID] [--report-consumer ID]\nchrono-inputs pair --host-root H --base-snapshot P --candidate-snapshot P --output P [--base-root H] [--candidate-root H] [--report-consumer ID]\nchrono-inputs compose --host-root H --config P --base OID --candidate OID --manifest P --output P --receipt P [--report-consumer ID]\nAdopted input exports require --report-consumer and return chrono-input-export/v1; the caller releases the returned consumer after use.\nExplicit input transport only; snapshots are not governance verdicts.\n".into()),
        InputAction::Command(command) => command,
    };
    let required = |key: &str| {
        command
            .required(key)
            .map_err(|missing| format!("E_USAGE: missing {}", missing.key))
    };
    let root = fs::canonicalize(cwd.join(required("--host-root")?)).map_err(|e| e.to_string())?;
    let consumer = command.option("--report-consumer");
    let output = required("--output")?;
    let primary = match command.kind {
        InputKind::Compose => required("--receipt")?,
        _ => output,
    };
    let ownership = Store::open(&root)?;
    if consumer.is_none() && (ownership.accepts(output)? || ownership.accepts(primary)?) {
        return Err("E_INPUT_RETENTION: adopted input export requires --report-consumer ID".into());
    }
    if let Some(consumer) = consumer {
        if consumer.trim().is_empty() || !ownership.accepts(primary)? {
            return Err("E_INPUT_RETENTION: caller handoff requires a nonempty consumer and adopted primary output".into());
        }
    }
    drop(ownership);
    let result = match command.kind {
        InputKind::Capture => capture_selected(
            &root,
            required("--config")?,
            required("--commit")?,
            required("--output")?,
            &command
                .option("--unit")
                .map_or(Selection::All, |unit| Selection::Unit { unit: unit.into() }),
        )?,
        InputKind::Compose => compose(
            &root,
            required("--config")?,
            required("--base")?,
            required("--candidate")?,
            required("--manifest")?,
            required("--output")?,
            required("--receipt")?,
        )?,
        InputKind::Pair => {
            let location = |key: &str| -> Result<PathBuf, String> {
                match command.option(key) {
                    Some(p) => fs::canonicalize(cwd.join(p)).map_err(|e| e.to_string()),
                    None => Ok(root.clone()),
                }
            };
            pair(
                &root,
                &location("--base-root")?,
                required("--base-snapshot")?,
                &location("--candidate-root")?,
                required("--candidate-snapshot")?,
                required("--output")?,
            )?
        }
    };
    let result = if let Some(consumer) = consumer {
        let declaration = result.handoff(consumer)?;
        value!({"schema":"chrono-input-export/v1","result":result.value,"report_consumer":declaration})
    } else {
        result.value.clone()
    };
    Ok(serde_json::to_string_pretty(&result).map_err(|e| e.to_string())? + "\n")
}
