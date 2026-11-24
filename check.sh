#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/inputs/Cargo.toml
product=crates/inputs/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/inputs-tests/Cargo.toml
CHRONO_INPUTS_BIN="$(cd "$CARGO_TARGET_DIR" && pwd -P)/debug/chrono-inputs" cargo test --locked --manifest-path crates/inputs-tests/Cargo.toml

coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

verifier=$(command -v "${VERUS:-verus}") || coverage_failure "verifier not found"

prove() {
  chrono-host-bootstrap run-compiler-proof "$scratch" "$1" "$verifier" "$2" ||
    coverage_failure "$1: verifier execution failed"
}

admit_proof() {
  local label=$1
  shift
  chrono-host-bootstrap collect-compiler-proof "$scratch" "$label" "$verifier" \
    0.2026.04.24.f8e1704 f8e17045c4ac17a02e566b8997070f2eecc255be "$@" ||
    coverage_failure "$label: required proof result was not admitted"
}

# Read the exact library selected by Cargo in the build of the tested executable.
metadata=$(jq -ers --arg manifest "$(pwd -P)/$product" '
  [.[] | select(.reason == "compiler-artifact" and .manifest_path == $manifest
                 and .target.kind == ["lib"]) | .filenames[] | select(endswith(".rmeta"))]
  | if length == 1 then .[0] else error("expected the product library") end
' "$scratch/build.jsonl") || coverage_failure "native library was not identified"
filename=${metadata##*/}
stem=${filename#lib}
stem=${metadata%/*}/${stem%.rmeta}
chrono-host-bootstrap check-compiler-sources native "$stem" \
  src/lib.rs src/composition.rs src/snapshot.rs || coverage_failure "native library differs from required sources"

prove verify.inputs-blobs crates/inputs/src/lib.rs
prove verify.inputs-blobs-tests crates/inputs-tests/tests/snapshots.rs

admit_proof verify.inputs-blobs crates/inputs/src/lib.rs \
  crates/inputs/src/composition.rs
admit_proof verify.inputs-blobs-tests crates/inputs-tests/tests/snapshots.rs \
  crates/inputs-tests/tests/../../inputs/src/lib.rs \
  crates/inputs-tests/tests/../../inputs/src/composition.rs
