#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/judge-mixed/Cargo.toml
cargo build --locked --manifest-path crates/judge-mixed/Cargo.toml
cargo fmt --check --manifest-path crates/judge-mixed-tests/Cargo.toml
cargo test --locked --manifest-path crates/judge-mixed-tests/Cargo.toml
