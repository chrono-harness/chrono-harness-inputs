//! On-disk file identities and relative addresses used by input snapshots.
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
pub fn canonical<T: Serialize>(v: &T) -> Result<Vec<u8>, String> {
    serde_jcs::to_vec(v).map_err(|e| e.to_string())
}
pub fn digest<T: Serialize>(v: &T) -> Result<String, String> {
    Ok(sha256(&canonical(v)?))
}
pub fn is_digest(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
pub fn full_oid(s: &str) -> Result<(), String> {
    if (s.len() == 40 || s.len() == 64)
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        && s.bytes().any(|b| b != b'0')
    {
        Ok(())
    } else {
        Err("expected full nonzero lowercase commit OID".into())
    }
}
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
pub fn valid_host_state_path(value: &str) -> bool {
    value
        .strip_prefix(".chrono-harness/state/")
        .is_some_and(|tail| !tail.is_empty())
        && relative_path(value).is_ok()
}
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
        length = length
            .checked_add(count as u64)
            .ok_or("file length overflow")?;
    }
    Ok((format!("{:x}", hash.finalize()), length))
}
pub fn file_identity(path: &Path) -> Result<(String, u64), String> {
    let input = fs::File::open(path).map_err(|e| e.to_string())?;
    if !input.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err(format!("not a regular input file: {}", path.display()));
    }
    copy_hashed(input, std::io::sink())
}
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

pub fn json(bytes: &[u8]) -> Result<serde_json::Value, String> {
    let value: serde_yaml_ng::Value =
        serde_json::from_slice(bytes).map_err(|error: serde_json::Error| {
            let message = error.to_string();
            if let Some((quoted, location)) = message
                .strip_prefix("duplicate entry with key ")
                .and_then(|tail| tail.rsplit_once(" at line "))
                && let Ok(key) = litrs::StringLit::parse(quoted)
            {
                return format!("duplicate JSON member {} at line {location}", key.value());
            }
            message
        })?;
    serde_json::to_value(value).map_err(|error| error.to_string())
}

pub fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T, String> {
    serde_json::from_value(json(bytes)?).map_err(|e| e.to_string())
}
