#!/usr/bin/env bash
#
# Replay every real path-flip query of a finished RPC matrix and prove the
# path solver still asks the same question and gets the same answer.
#
# What it proves: for every query the matrix actually solved (175 across the
# twenty rows of the 2026-08-25 baseline), running the CURRENT jar's
# ConcolicPathFlipSolver on that query's recorded worklist row and execution
# task reproduces, byte for byte, the recorded path_flip_query.smt2, the
# recorded path_flip_solver_result.json, and the recorded replay
# execution_task_plan.jsonl -- the last of which carries the SAT model's
# concrete input values, so a solver that picks a different valuation is
# caught here even when its status is unchanged.
#
# This is the cheap stand-in for `gate.sh --matrix --baseline` when the change
# is inside the expression encoder: it exercises the solver on the real
# workload in minutes instead of re-running the campaign for three hours.  It
# does not replace the matrix -- it never runs the VM, the importer, or the
# iteration loop, and the RPC matrix's queries use only Symbol/Binary/
# FieldAccess/Const/TypeCast expressions, so it says nothing about the string
# or container lowering paths that HDFS-11741 reaches.
#
# Runtime: ~3 minutes.  Needs jq, z3 and a built jar (mvn -q package).
# Honours GRAPH_CHECKER_JAVA and Z3_BIN; falls back to `java` and `z3`.
#
# Usage:
#   experiments/shrink/replay-flips.sh <matrix-root>
#
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
jar="${repo_root}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
java_bin="${GRAPH_CHECKER_JAVA:-java}"
z3_bin="${Z3_BIN:-z3}"

if [[ $# -ne 1 ]]; then
  echo "usage: $(basename "${BASH_SOURCE[0]}") <matrix-root>" >&2
  exit 2
fi
matrix_root=$1
[[ -d "${matrix_root}" ]] || { echo "no such matrix root: ${matrix_root}" >&2; exit 2; }
[[ -f "${jar}" ]] || { echo "jar not built: ${jar} (run: mvn -q package)" >&2; exit 2; }
command -v jq >/dev/null || { echo "jq is required" >&2; exit 2; }
command -v "${z3_bin}" >/dev/null || { echo "z3 not found: ${z3_bin}" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -rf "${work}"' EXIT

# A flip's sourceTaskId may name a TASK.REPLAY row minted by an earlier
# obligation wave, which no single worker's plan holds.  Compose one plan per
# scenario from every task row the run left behind, keeping the first row per
# taskId so the solver's unique-index decode still accepts it.
merged_task_plan() {
  local scenario=$1 destination=$2
  find "${scenario}" \
    \( -name 'execution_task_plan.jsonl' \
    -o -name 'session_execution_task_plan.jsonl' \
    -o -name 'import_execution_task_plan.jsonl' \) -print0 \
    | xargs -0 cat 2>/dev/null \
    | jq -c 'select(.taskId != null)' \
    | jq -s -c 'group_by(.taskId) | map(.[0]) | .[]' >"${destination}"
}

total=0
identical=0
for scenario in "${matrix_root}"/scenario-*/; do
  [[ -d "${scenario}" ]] || continue
  name=$(basename "${scenario}")
  tasks="${work}/${name}.tasks.jsonl"
  merged_task_plan "${scenario}" "${tasks}"
  [[ -s "${tasks}" ]] || continue

  while IFS= read -r recorded_result; do
    query_dir=$(dirname "${recorded_result}")
    query_key=$(basename "${query_dir}")
    worklist=$(dirname "${query_dir}")/region_path_worklist.jsonl
    [[ -s "${worklist}" ]] || continue
    total=$((total + 1))
    out="${work}/${name}/${query_key}"
    mkdir -p "${out}"

    status=0
    "${java_bin}" -cp "${jar}" \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipSolver \
      --worklist "${worklist}" \
      --task-plan "${tasks}" \
      --query-key "${query_key}" \
      --output-dir "${out}" \
      --z3 "${z3_bin}" \
      --solver-timeout-ms 120000 >/dev/null 2>"${out}/stderr.log" || status=$?
    if [[ ! -s "${out}/path_flip_solver_result.json" ]]; then
      echo "query ${query_key:0:12} DIFF solver exited ${status}: $(head -1 "${out}/stderr.log" 2>/dev/null)"
      continue
    fi
    if ! cmp -s "${query_dir}/path_flip_query.smt2" \
        "${out}/path_flip_query.smt2"; then
      first=$(diff "${query_dir}/path_flip_query.smt2" \
        "${out}/path_flip_query.smt2" | grep -m1 -E '^[<>]' || true)
      echo "query ${query_key:0:12} DIFF smt: ${first:-<query differs>}"
      continue
    fi
    if ! diff -q <(jq -S . "${query_dir}/path_flip_solver_result.json") \
        <(jq -S . "${out}/path_flip_solver_result.json") >/dev/null; then
      first=$(diff <(jq -S . "${query_dir}/path_flip_solver_result.json") \
        <(jq -S . "${out}/path_flip_solver_result.json") \
        | grep -m1 -E '^[<>]' || true)
      echo "query ${query_key:0:12} DIFF record: ${first:-<record differs>}"
      continue
    fi
    # The SAT model's chosen input values travel in the replay task, not the
    # record: comparing it is what catches a different valuation.
    if ! cmp -s "${query_dir}/execution_task_plan.jsonl" \
        "${out}/execution_task_plan.jsonl"; then
      echo "query ${query_key:0:12} DIFF replay task plan (model valuation changed)"
      continue
    fi
    identical=$((identical + 1))
  done < <(find "${scenario}" -name 'path_flip_solver_result.json' | sort)
done

echo "FLIPS ${identical}/${total} identical"
if [[ "${total}" -eq 0 || "${identical}" -ne "${total}" ]]; then
  echo "FLIPS FAIL: every recorded query must replay identically"
  exit 1
fi
