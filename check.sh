#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ $# -eq 0 ]]; then
  /bin/sh .chrono-harness/ci/install.sh
  export PATH="$PWD/.chrono-harness/bin:$PATH"
  export CHRONO_CHECK_SOURCE=${CHRONO_CHECK_SOURCE:-local}
  exec .chrono-harness/bin/chrono-harness check
fi
if [[ $# -ne 1 || $1 != --native ]]; then
  echo 'usage: ./check.sh [--native]' >&2
  exit 2
fi

mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/inputs/Cargo.toml
product=crates/inputs/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/inputs-tests/Cargo.toml
CHRONO_INPUTS_BIN="$(cd "$CARGO_TARGET_DIR" && pwd -P)/debug/chrono-inputs" cargo test --color never --locked --manifest-path crates/inputs-tests/Cargo.toml -- --format pretty | tee "$scratch/tests.log"
for consumer in retained_snapshot_versions_and_file_forms_preserve_error_order snapshot_versions_reject_inconsistent_selectors_and_malformed_file_addresses capture_uses_fixed_documents_and_checks_the_returned_selection pairs_stored_inputs_with_an_empty_tool_search_path; do
  grep -Fxq "test $consumer ... ok" "$scratch/tests.log" || {
    echo "E_VERUS_COVERAGE: required snapshot consumer did not pass: $consumer" >&2
    exit 1
  }
done

coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
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
  src/lib.rs src/composition.rs src/snapshot.rs src/retained_shape.rs || coverage_failure "native library differs from required sources"
