#!/usr/bin/env bash
#
# Recompose every row of a finished RPC matrix from its own real inputs and
# prove the Composer still emits the same formula.
#
# What it proves: for each of the twenty scenarios, running the CURRENT jar's
# ConcolicSmtComposer on that row's recorded reach query, merged producer
# summaries and frozen region plan reproduces the recorded candidate.smt2
# byte for byte, and reproduces the recorded composition manifest apart from
# `canonicalModel` and the two artifact path/digest members (which name the
# output file this run wrote, not the composition).  A refactor that changes
# one emitted assertion shows up here as a named differing line.
#
# What it does NOT prove: nothing about the solver, the replay, or the
# iteration loop -- only that the composition of already-recorded inputs is
# unchanged.  Use replay-flips.sh beside it, and the full matrix for the rest.
#
# Runtime: ~60 seconds.  Needs jq and a built jar (mvn -q package).
# Honours GRAPH_CHECKER_JAVA; falls back to `java` on PATH.
#
# Usage:
#   experiments/shrink/recompose-matrix.sh <matrix-root>
#
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
jar="${repo_root}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
java_bin="${GRAPH_CHECKER_JAVA:-java}"

if [[ $# -ne 1 ]]; then
  echo "usage: $(basename "${BASH_SOURCE[0]}") <matrix-root>" >&2
  exit 2
fi
matrix_root=$1
[[ -d "${matrix_root}" ]] || { echo "no such matrix root: ${matrix_root}" >&2; exit 2; }
[[ -f "${jar}" ]] || { echo "jar not built: ${jar} (run: mvn -q package)" >&2; exit 2; }
command -v jq >/dev/null || { echo "jq is required" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -rf "${work}"' EXIT

# The manifest members a re-run legitimately rewrites: the reduced evidence
# census and the two records that name where this run put its own output.
strip_manifest() {
  jq -S 'del(.canonicalModel, .composedSmtArtifact, .runtimePlanArtifact)' "$1"
}

total=0
identical=0
for row in $(seq 1 20); do
  label=$(printf '%02d' "${row}")
  scenario=$(find -L "${matrix_root}" -maxdepth 1 -type d \
    -name "scenario-${label}.*" 2>/dev/null | sort | head -1)
  if [[ -z "${scenario}" ]]; then
    echo "row ${label} MISSING no scenario directory under ${matrix_root}"
    continue
  fi
  iteration="${scenario}/iteration-0000"
  index="${iteration}/runtime_workflow_schedule_index.json"
  recorded_smt="${scenario}/final/candidate.smt2"
  recorded_manifest="${scenario}/final/candidate_composition_manifest.json"
  if [[ ! -f "${index}" || ! -f "${recorded_smt}" || ! -f "${recorded_manifest}" ]]; then
    echo "row ${label} MISSING incomplete scenario: ${scenario}"
    continue
  fi
  total=$((total + 1))

  target_task=$(jq -r '.target.taskId' "${index}")
  target_region=$(jq -r '.target.regionId' "${index}")
  target_occurrence=$(jq -r '.target.occurrenceId' "${index}")

  # Every non-target member that left a merged relation is composed, exactly
  # as campaign_compose() selects them.
  args=(--fatal-query "${iteration}/workers/${target_task}/reach_query.jsonl")
  for worker in "${iteration}"/workers/*/; do
    task=$(basename "${worker}")
    [[ "${task}" != "${target_task}" ]] || continue
    [[ -s "${worker}/merged_summary.jsonl" ]] || continue
    args+=(--summaries "${worker}/merged_summary.jsonl")
  done
  out="${work}/${label}"
  mkdir -p "${out}"
  args+=(--runtime-plan "${iteration}/concolic_region_plan.jsonl"
    --output "${out}/candidate.smt2"
    --manifest "${out}/manifest.json"
    --fatal-region "${target_region}"
    --occurrence-id "${target_occurrence}")

  status=0
  "${java_bin}" -cp "${jar}" \
    edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer \
    "${args[@]}" >/dev/null 2>"${out}/stderr.log" || status=$?
  if [[ "${status}" -ne 0 || ! -s "${out}/candidate.smt2" ]]; then
    echo "row ${label} DIFF composer exited ${status}: $(head -1 "${out}/stderr.log" 2>/dev/null)"
    continue
  fi

  if ! cmp -s "${recorded_smt}" "${out}/candidate.smt2"; then
    first=$(diff "${recorded_smt}" "${out}/candidate.smt2" \
      | grep -m1 -E '^[<>]' || true)
    echo "row ${label} DIFF ${first:-<smt differs, no line shown>}"
    continue
  fi
  if ! diff -q <(strip_manifest "${recorded_manifest}") \
      <(strip_manifest "${out}/manifest.json") >/dev/null; then
    first=$(diff <(strip_manifest "${recorded_manifest}") \
      <(strip_manifest "${out}/manifest.json") | grep -m1 -E '^[<>]' || true)
    echo "row ${label} DIFF manifest: ${first:-<manifest differs>}"
    continue
  fi
  identical=$((identical + 1))
  echo "row ${label} IDENTICAL"
done

echo "RECOMPOSE ${identical}/${total} identical"
if [[ "${total}" -ne 20 || "${identical}" -ne 20 ]]; then
  echo "RECOMPOSE FAIL: expected 20 rows, all identical"
  exit 1
fi
