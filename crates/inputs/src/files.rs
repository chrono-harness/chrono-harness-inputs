//! On-disk file identities and relative addresses used by input snapshots.
#[cfg(not(verus_keep_ghost))]
use std::fmt::Write as _;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub(crate) fn copied_length(previous: u64, count: u64) -> (total: Option<u64>)
    ensures match total {
        Some(size) => size as int == previous as int + count as int,
        None => previous as int + count as int > u64::MAX,
    },
{
    previous.checked_add(count)
}
}

#[cfg(not(verus_keep_ghost))]
fn digest_text(digest: [u8; 32]) -> String {
    let mut text = String::with_capacity(64);
    for byte in digest {
        write!(text, "{byte:02x}").expect("writing to a String is infallible");
    }
    text
}
#[cfg(not(verus_keep_ghost))]
use serde::Serialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use sha2::{Digest, Sha256};
#[cfg(not(verus_keep_ghost))]
use std::{
    fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

#[cfg(not(verus_keep_ghost))]
pub fn sha256(bytes: &[u8]) -> String {
    digest_text(Sha256::digest(bytes).into())
}
#[cfg(not(verus_keep_ghost))]
struct SnapshotNumberView<'a>(&'a Value);

#[cfg(not(verus_keep_ghost))]
impl Serialize for SnapshotNumberView<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            // The runner computes semantic digests with ECMAScript binary64 numbers.
            Value::Number(number) => serializer.serialize_f64(
                number
                    .as_f64()
                    .ok_or_else(|| serde::ser::Error::custom("invalid JSON number"))?,
            ),
            Value::Array(values) => serializer.collect_seq(values.iter().map(SnapshotNumberView)),
            Value::Object(fields) => serializer.collect_map(
                fields
                    .iter()
                    .map(|(key, value)| (key, SnapshotNumberView(value))),
            ),
            value => value.serialize(serializer),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub fn canonical(value: &Value) -> Result<Vec<u8>, String> {
    serde_jcs::to_vec(&SnapshotNumberView(value)).map_err(|e| e.to_string())
}
#[cfg(not(verus_keep_ghost))]
pub fn digest(value: &Value) -> Result<String, String> {
    Ok(sha256(&canonical(value)?))
}
#[cfg(not(verus_keep_ghost))]
pub fn is_digest(s: &str) -> bool {
    crate::retained_shape::valid_identity(s.as_bytes(), crate::retained_shape::IdentityKind::Digest)
}
#[cfg(not(verus_keep_ghost))]
pub fn full_oid(s: &str) -> Result<(), String> {
    if crate::retained_shape::valid_identity(
        s.as_bytes(),
        crate::retained_shape::IdentityKind::Commit,
    ) {
        Ok(())
    } else {
        Err("expected full nonzero lowercase commit OID".into())
    }
}
#[cfg(not(verus_keep_ghost))]
pub fn relative_path(value: &str) -> Result<(), String> {
    if value.is_empty()
        || value.starts_with('/')
        || value == "."
        || value.starts_with("./")
        || value.contains(['\0', '\n', '\r', '\\'])
        || value.split('/').any(|part| part == "..")
    {
        return Err(format!("invalid relative path: {value:?}"));
    }
    Ok(())
}
#[cfg(not(verus_keep_ghost))]
pub fn valid_host_state_path(value: &str) -> bool {
    value
        .strip_prefix(".chrono-harness/state/")
        .is_some_and(|tail| !tail.is_empty())
        && relative_path(value).is_ok()
}
#[cfg(not(verus_keep_ghost))]
pub fn no_symlink_parents(root: &Path, relative: &str) -> Result<PathBuf, String> {
    relative_path(relative)?;
    let mut path = root.to_path_buf();
    for component in Path::new(relative).components() {
        path.push(component);
        match fs::symlink_metadata(&path) {
            Ok(m) if m.file_type().is_symlink() => {
                return Err(format!("symlink path is not allowed: {}", path.display()));
            }
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.to_string()),
        }
    }
    Ok(path)
}
#[cfg(not(verus_keep_ghost))]
pub fn copy_hashed(mut input: impl Read, mut output: impl Write) -> Result<(String, u64), String> {
    let mut hash = Sha256::new();
    let mut length = 0u64;
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = input.read(&mut buffer).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        output
            .write_all(&buffer[..count])
            .map_err(|e| e.to_string())?;
        hash.update(&buffer[..count]);
        length = copied_length(length, count as u64).ok_or("file length overflow")?;
    }
    Ok((digest_text(hash.finalize().into()), length))
}
#[cfg(not(verus_keep_ghost))]
pub fn file_identity(path: &Path) -> Result<(String, u64), String> {
    let input = fs::File::open(path).map_err(|e| e.to_string())?;
    if !input.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err(format!("not a regular input file: {}", path.display()));
    }
    copy_hashed(input, std::io::sink())
}
#[cfg(not(verus_keep_ghost))]
pub fn observe_file(path: &Path) -> Result<Option<(String, u64)>, String> {
    let mut prefix = PathBuf::new();
    for component in path.components() {
        if !matches!(
            component,
            std::path::Component::RootDir
                | std::path::Component::Prefix(_)
                | std::path::Component::Normal(_)
        ) {
            return Err(format!(
                "E_INPUT_PATH: non-normal input path: {}",
                path.display()
            ));
        }
        prefix.push(component);
        match fs::symlink_metadata(&prefix) {
            Ok(m) if m.file_type().is_symlink() => {
                return Err(format!("E_INPUT_PATH: symlink input: {}", prefix.display()));
            }
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(format!("E_INPUT_PATH: {}: {e}", prefix.display())),
        }
    }
    match fs::symlink_metadata(path) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("E_INPUT_PATH: {}: {e}", path.display())),
        Ok(_) => file_identity(path).map(Some),
    }
}

#[cfg(not(verus_keep_ghost))]
pub fn json(bytes: &[u8]) -> Result<serde_json::Value, String> {
    let value: serde_yaml_ng::Value =
        serde_json::from_slice(bytes).map_err(|error: serde_json::Error| {
            let message = error.to_string();
            if let Some((key, location)) = message
                .strip_prefix("duplicate entry with key ")
                .and_then(|tail| tail.rsplit_once(" at line "))
                .and_then(|(quoted, at)| litrs::StringLit::parse(quoted).ok().map(|key| (key, at)))
            {
                return format!("duplicate JSON member {} at line {location}", key.value());
            }
            message
        })?;
    serde_json::to_value(value).map_err(|error| error.to_string())
}

#[cfg(not(verus_keep_ghost))]
pub fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, String> {
    serde_json::from_value(json(bytes)?).map_err(|e| e.to_string())
}
