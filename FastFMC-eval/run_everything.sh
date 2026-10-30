#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")"

RUNS="${RUNS:-10}"
SUITE="${SUITE:-all}"
OUT="${OUT:-experimental_results}"
CFG="${CFG:-config/eval.yaml}"
LIMIT="${LIMIT:-0}"
FORCE="${FORCE:-0}"
CHECK_ONLY="${CHECK_ONLY:-0}"
SKIP_CHECK="${SKIP_CHECK:-0}"

note() { printf '  %-30s %s\n' "$1" "$2"; }

check_released() {
    echo "=========== released data (experimental_results/) ==========="
    python3 scripts/analysis/reproduce_tables.py --data-dir experimental_results
    python3 scripts/analysis/statistical_tests.py --data-dir experimental_results
}

if [[ "$CHECK_ONLY" == "1" ]]; then
    check_released
    exit 0
fi

fail=0
echo "=============== preflight ==============="
for b in ../FastFMC/FastFMC/target/release/FastFMC ../FastFMC/tools/d4v2 ../FastFMC/tools/coprocessor \
         solvers/ddnnife solvers/ganak solvers/sharpSAT solvers/countAntom; do
    if [[ -x "$b" ]]; then note "$b" ok
    elif [[ "$b" == ../FastFMC/FastFMC/target/release/FastFMC ]]; then
        note "$b" "not built -> run ./scripts/build.sh"; fail=1
    else note "$b" "MISSING/not executable"; fail=1; fi
done
[[ -x solvers/c2d ]] && note solvers/c2d ok \
    || note solvers/c2d "absent -> query-ddnnf is skipped (not redistributable)"

if [[ -d ../benchmarks/all ]]; then
    note ../benchmarks/all "$(find -L ../benchmarks/all -maxdepth 1 -name '*.cnf' | wc -l | tr -d ' ') CNF models"
else
    note ../benchmarks/all "MISSING"; fail=1
fi
if [[ -d ../benchmarks/queries ]]; then
    note ../benchmarks/queries "$(find -L ../benchmarks/queries -maxdepth 1 -name '*.config' | wc -l | tr -d ' ') query files"
else
    note ../benchmarks/queries "MISSING"; fail=1
fi
command -v python3 >/dev/null && note python3 "$(python3 -V 2>&1)" || { note python3 MISSING; fail=1; }
python3 -c 'import yaml' 2>/dev/null && note pyyaml ok \
    || { note pyyaml "MISSING (pip install -r requirements.txt)"; fail=1; }
python3 -c 'import scipy' 2>/dev/null && note scipy ok \
    || note scipy "absent -> statistical_tests.py will be skipped"
note configuration "$CFG  suite=$SUITE runs=$RUNS limit=$LIMIT out=$OUT"
[[ "$fail" -eq 0 ]] || { echo "preflight FAILED" >&2; exit 2; }

extra=()
[[ "$FORCE" == "1" ]] && extra+=(--force)
[[ "$LIMIT" != "0" ]] && extra+=(--limit "$LIMIT")

echo
echo "=============== running ================"
python3 scripts/run/er_pipeline.py --config "$CFG" --suite "$SUITE" \
        --runs "$RUNS" --output "$OUT" "${extra[@]}" "$@"
rc=$?
[[ $rc -ne 0 ]] && echo "WARNING: pipeline exited with rc=$rc" >&2

if [[ "$SKIP_CHECK" != "1" ]]; then
    echo
    echo "=========== verification of the fresh run ==========="
    mkdir -p "$OUT"
    python3 scripts/analysis/reproduce_tables.py --data-dir "$OUT" > "$OUT/tables_report.txt" 2>&1 \
        && echo "  tables -> $OUT/tables_report.txt" \
        || echo "  WARNING: table report failed ($OUT/tables_report.txt)" >&2
    python3 scripts/analysis/statistical_tests.py --data-dir "$OUT" > "$OUT/statistical_tests.txt" 2>&1 \
        && echo "  tests  -> $OUT/statistical_tests.txt" \
        || echo "  WARNING: statistical tests skipped ($OUT/statistical_tests.txt)" >&2
    echo "  NOTE: a fresh campaign runs on different hardware than the published"
    echo "        one, so its absolute times are expected to differ."
    echo
    check_released
fi

exit $rc
