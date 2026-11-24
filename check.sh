#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
target_dir="${CARGO_TARGET_DIR:-$scratch/cargo}"
mkdir -p -- "$target_dir"
CARGO_TARGET_DIR=$(cd -- "$target_dir" && pwd -P)
export CARGO_TARGET_DIR
cargo fmt --check --manifest-path crates/judge-mixed/Cargo.toml
product=crates/judge-mixed/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/judge-mixed-tests/Cargo.toml
cargo test --locked --manifest-path crates/judge-mixed-tests/Cargo.toml
coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

prove() {
  local label=$1 root=$2
  local output="$scratch/$label.rlib" report="$scratch/$label.json"
  "${VERUS:-verus}" --crate-type=lib --no-cheating --no-external-by-default --num-threads 2 \
    --output-json --compile "--emit=link=$output,dep-info=$output.d" "$root" -o "$output" \
    -Zchecksum-hash-algorithm=sha256 > "$report" || { cat "$report" >&2; coverage_failure "$label: verifier failed"; }
}

admit_proof() {
  local label=$1
  shift
  chrono-host-bootstrap check-compiler-proof \
    0.2026.04.24.f8e1704 f8e17045c4ac17a02e566b8997070f2eecc255be \
    "$scratch/$label.json" "$scratch/$label.rlib" "$@" ||
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
chrono-host-bootstrap check-compiler-sources native "$stem" src/verified_classification.rs src/lib.rs src/native.rs ||
  coverage_failure "native library differs from required sources"

policy=crates/judge-mixed/src/verified_classification.rs
expectations=crates/judge-mixed-tests/tests/verified_classification.rs

product_operation=verify.mixed-classification
test_operation=verify.mixed-classification-tests

prove "$product_operation" "$policy"
prove "$test_operation" "$expectations"

admit_proof "$product_operation" "$policy"
admit_proof "$test_operation" "$expectations" crates/judge-mixed-tests/tests/../../judge-mixed/src/verified_classification.rs
