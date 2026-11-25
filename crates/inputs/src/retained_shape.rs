//! Admission decisions shared by offline and composition snapshot readers.
use vstd::{contrib::exec_spec::ExecSpecEq, prelude::*};

verus! {

/// The host supplies UTF-8, while lengths and the hexadecimal alphabet are byte-based.
pub enum IdentityKind { Commit, Digest }

pub open spec fn lower_hex(b: u8) -> bool {
    48 <= b <= 57 || 97 <= b <= 102
}

pub fn valid_identity(s: &[u8], kind: IdentityKind) -> (valid: bool)
    ensures valid == (
        (forall|j: int| 0 <= j < s.len() ==> lower_hex(#[trigger] s[j]))
        && match kind {
            IdentityKind::Digest => s.len() == 64,
            IdentityKind::Commit => (s.len() == 40 || s.len() == 64)
                && (exists|j: int| 0 <= j < s.len() && #[trigger] s[j] != 48),
        }
    ),
{
    let commit = match kind { IdentityKind::Commit => true, IdentityKind::Digest => false };
    if s.len() != 64 && !(commit && s.len() == 40) { return false; }
    let mut i = 0;
    let mut nonzero = false;
    while i < s.len()
        invariant i <= s.len(),
            forall|j: int| 0 <= j < i ==> lower_hex(#[trigger] s[j]),
            nonzero == (exists|j: int| 0 <= j < i && #[trigger] s[j] != 48),
        decreases s.len() - i,
    {
        let b=s[i];
        if !((48 <= b && b <= 57) || (97 <= b && b <= 102)) { return false; }
        if b != 48 { nonzero = true; }
        i += 1;
    }
    !commit || nonzero
}

pub const SNAPSHOT_SCHEMA: &'static str = "chrono-input-snapshot/v1";
pub const SNAPSHOT_SCHEMA_V2: &'static str = "chrono-input-snapshot/v2";
pub const SNAPSHOT_SCHEMA_V3: &'static str = "chrono-input-snapshot/v3";

#[derive(Clone, Copy)]
pub enum Version { V1, V2, V3 }

pub fn version(schema: Option<&str>, selection: bool, effective: bool) -> (out: Result<Version, &'static str>)
    ensures match out {
        Ok(Version::V1) => schema matches Some(s) && s@ == "chrono-input-snapshot/v1"@ && !selection && !effective,
        Ok(Version::V2) => schema matches Some(s) && s@ == "chrono-input-snapshot/v2"@ && !selection && !effective,
        Ok(Version::V3) => schema matches Some(s) && s@ == "chrono-input-snapshot/v3"@,
        Err(message) => {
            if schema matches Some(s) && (s@ == "chrono-input-snapshot/v1"@ || s@ == "chrono-input-snapshot/v2"@) {
                (selection || effective) && message@ == "E_INPUT_SNAPSHOT: selection binding requires snapshot v3"@
            } else {
                !(schema matches Some(s) && s@ == "chrono-input-snapshot/v3"@)
                    && message@ == "E_INPUT_SNAPSHOT: unsupported snapshot schema"@
            }
        }
    },
{
    proof {
        reveal_strlit("chrono-input-snapshot/v1"); reveal_strlit("chrono-input-snapshot/v2");
        reveal_strlit("chrono-input-snapshot/v3");
        assert("chrono-input-snapshot/v3"@[23] != "chrono-input-snapshot/v1"@[23]);
        assert("chrono-input-snapshot/v3"@[23] != "chrono-input-snapshot/v2"@[23]);
    }
    let Some(text) = schema else { return Err("E_INPUT_SNAPSHOT: unsupported snapshot schema"); };
    if <&str>::exec_eq(text, SNAPSHOT_SCHEMA_V3) { return Ok(Version::V3); }
    let v = if <&str>::exec_eq(text, SNAPSHOT_SCHEMA) { Version::V1 }
        else if <&str>::exec_eq(text, SNAPSHOT_SCHEMA_V2) { Version::V2 }
        else { return Err("E_INPUT_SNAPSHOT: unsupported snapshot schema"); };
    if selection || effective { return Err("E_INPUT_SNAPSHOT: selection binding requires snapshot v3"); }
    Ok(v)
}

pub enum Representation { Absent, Bytes, Blob }

pub fn representation(absent: bool, bytes: bool, blob: bool) -> (out: Result<Representation, &'static str>)
    ensures match out {
        Ok(Representation::Absent) => absent,
        Ok(Representation::Bytes) => !absent && bytes && !blob,
        Ok(Representation::Blob) => !absent && !bytes && blob,
        Err(message) => !absent && bytes == blob && message@ == "E_INPUT_BLOB: expected exactly one bytes or blob representation"@,
    },
{
    if absent { Ok(Representation::Absent) }
    else if bytes && !blob { Ok(Representation::Bytes) }
    else if blob && !bytes { Ok(Representation::Blob) }
    else { Err("E_INPUT_BLOB: expected exactly one bytes or blob representation") }
}

pub fn admit_absent(version: Version, value: Option<bool>) -> (out: Result<(), &'static str>)
    ensures match out {
        Ok(()) => value == Some(true) && !(version is V1),
        Err(message) => if value != Some(true) { message@ == "E_INPUT_BLOB: absent must be true"@ }
            else { version is V1 && message@ == "E_INPUT_SNAPSHOT: absence requires snapshot v2"@ },
    },
{
    if !matches!(value, Some(true)) { return Err("E_INPUT_BLOB: absent must be true"); }
    match version {
        Version::V1 => Err("E_INPUT_SNAPSHOT: absence requires snapshot v2"),
        _ => Ok(()),
    }
}

pub fn is_byte(value: Option<u64>) -> (accepted: bool)
    ensures accepted == (value matches Some(n) && n <= 255),
{
    match value { Some(n) => n <= 255, None => false }
}

pub fn admit_reference(path_ok: bool, digest_ok: bool, length_ok: bool) -> (out: Result<(), &'static str>)
    ensures match out {
        Ok(()) => path_ok && digest_ok && length_ok,
        Err(message) => if !path_ok { message@ == "E_INPUT_BLOB: reference must be within host state"@ }
            else if !digest_ok { message@ == "E_INPUT_BLOB: invalid digest"@ }
            else { !length_ok && message@ == "E_INPUT_BLOB: invalid length"@ },
    },
{
    if !path_ok { return Err("E_INPUT_BLOB: reference must be within host state"); }
    if !digest_ok { return Err("E_INPUT_BLOB: invalid digest"); }
    if !length_ok { return Err("E_INPUT_BLOB: invalid length"); }
    Ok(())
}
}
