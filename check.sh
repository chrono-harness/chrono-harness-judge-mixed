#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/judge-mixed/Cargo.toml
product=crates/judge-mixed/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/judge-mixed-tests/Cargo.toml
cargo test --locked --manifest-path crates/judge-mixed-tests/Cargo.toml
coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

if [[ ${1:-} == --native && $# == 1 ]]; then
  native_only=true
elif [[ $# == 0 ]]; then
  native_only=false
else
  echo 'usage: ./check.sh [--native]' >&2
  exit 2
fi

verifier=$(command -v "${VERUS:-verus}") || coverage_failure "registered verifier was not found"

prove() {
  chrono-host-bootstrap run-compiler-proof "$scratch" "$1" "$verifier" "$2" ||
    coverage_failure "$1: verifier failed"
}

admit_proof() {
  local operation=$1
  shift
  chrono-host-bootstrap collect-compiler-proof "$scratch" "$operation" "$verifier" \
    0.2026.04.24.f8e1704 f8e17045c4ac17a02e566b8997070f2eecc255be "$@" ||
    coverage_failure "$operation: required proof result was not admitted"
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
chrono-host-bootstrap check-compiler-sources native "$stem" src/verified_classification.rs src/lib.rs src/native.rs ||
  coverage_failure "native library differs from required sources"

if "$native_only"; then
  exit 0
fi

policy=crates/judge-mixed/src/verified_classification.rs
expectations=crates/judge-mixed-tests/tests/verified_classification.rs

product_operation=verify.mixed-classification
test_operation=verify.mixed-classification-tests

prove "$product_operation" "$policy"
prove "$test_operation" "$expectations"

admit_proof "$product_operation" "$policy"
admit_proof "$test_operation" "$expectations" crates/judge-mixed-tests/tests/../../judge-mixed/src/verified_classification.rs
