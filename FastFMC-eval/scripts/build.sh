#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
CRATE=../FastFMC/FastFMC

command -v cargo >/dev/null || { echo "cargo not found (install Rust)" >&2; exit 1; }
echo "== cargo build --release ($CRATE) =="
( cd "$CRATE" && cargo build --release )

BIN="$CRATE/target/release/FastFMC"
[[ -x "$BIN" ]] || { echo "build failed: $BIN not found" >&2; exit 1; }
echo "binary -> $BIN"
"$BIN" --help >/dev/null 2>&1 || true
echo "done."
