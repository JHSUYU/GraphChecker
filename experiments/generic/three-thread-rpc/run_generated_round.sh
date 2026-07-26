#!/usr/bin/env bash

set -uo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
round=${1:-}
jobs=${GRAPH_CHECKER_GENERATED_JOBS:-13}
path_jobs=${CAUSYNTH_GENERATED_CONCOLIC_JOBS:-10}
generator="${fixture_dir}/generate_regression_round.sh"
runner="${fixture_dir}/run.sh"
generated_root="${graphchecker_dir}/target/generated-regression/current"

die() {
  echo "[generated-rpc-round] $*" >&2
  exit 1
}

[[ "${round}" =~ ^([1-9]|10)$ ]] || die "round must be 1..10"
[[ "${jobs}" =~ ^[1-9][0-9]*$ ]] || die "jobs must be positive"
(( jobs <= 13 )) || die "jobs must not exceed 13"
[[ "${path_jobs}" =~ ^[1-9][0-9]*$ ]] \
  || die "CAUSYNTH_GENERATED_CONCOLIC_JOBS must be positive"
command -v jq >/dev/null 2>&1 || die "jq is required"
command -v z3 >/dev/null 2>&1 || die "z3 is required"

"${generator}" "${round}" || die "round generation failed"
run_id=$(date -u +%Y%m%dT%H%M%SZ).$$
log_root="${graphchecker_dir}/target/generated-regression/logs/round-${round}/${run_id}"
mkdir -p "${log_root}" || die "cannot create log root ${log_root}"

validate_case() {
  local index=$1
  local expected=$2
  local case_root="${generated_root}/case-${index}"
  local work="${case_root}/work"
  local result="${work}/candidate/candidate_result_manifest.json"
  local composition="${work}/candidate/candidate_composition_manifest.json"
  local smt="${work}/candidate/candidate.smt2"
  local plan="${work}/runtime/concolic_region_plan.jsonl"
  local actual direct producer_count
  [[ -f "${result}" && -f "${composition}" && -f "${smt}" \
      && -f "${plan}" ]] || return 1
  actual=$(jq -er '.reachability' "${result}") || return 1
  [[ "${actual}" == "${expected}" ]] || return 1
  producer_count=$(jq -er -s '
    [.[] | .closureGoals[]
      | select(.kind == "OUTPUT_RELATION_CLOSURE"
        and .admission.state == "READY")] | length
  ' "${plan}") || return 1
  (( producer_count >= 1 && producer_count <= 2 )) || return 1
  jq -e --argjson producer_count "${producer_count}" '
    .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.gaps | type == "array" and length == 0)
    and (.resolvedEdgeBindings | length) == $producer_count
    and ([.resolvedEdgeBindings[]] | unique | length) == $producer_count
  ' "${composition}" >/dev/null || return 1
  jq -e -s --argjson producer_count "${producer_count}" '
    [.[] as $plan | $plan.closureGoals[]
      | select(.kind == "OUTPUT_RELATION_CLOSURE"
        and .admission.state == "READY")] as $goals
    | ($goals | length) == $producer_count
    and ([ $goals[].edgeBindings[]
      | select(.evidenceKind == "FIELD_ASSIGNMENT_READ_FROM_V1"
        and .writerEventSeq < .readerEventSeq
        and .receiverObjectId != 0)
      | .fromOutputCell ] | unique | length) == $producer_count
  ' "${plan}" >/dev/null || return 1
  mapfile -t closures < <(find "${work}/producer-campaign" \
    -mindepth 2 -maxdepth 2 -type f -name region_path_closure.json \
    | LC_ALL=C sort)
  [[ ${#closures[@]} -eq ${producer_count} ]] || return 1
  jq -e -s --argjson producer_count "${producer_count}" '
    length == $producer_count
    and all(.[];
      .state == "CLOSED"
      and .outputClosure.kind == "OUTPUT_CLOSURE_CONTRACT"
      and (.gaps | length) == 0)
  ' "${closures[@]}" >/dev/null || return 1
  direct=$(z3 "${smt}" | sed -n '1p') || return 1
  if [[ "${expected}" == "REACHABLE" ]]; then
    [[ "${direct}" == "sat" ]] || return 1
  else
    [[ "${direct}" == "unsat" ]] || return 1
  fi
}

debug_case() {
  local index=$1
  local case_root="${generated_root}/case-${index}/work"
  echo "[generated-rpc-round] debug root: ${case_root}" >&2
  find "${case_root}" -type f \
    \( -name '*manifest*.json' -o -name '*solver_result.json' \
       -o -name '*gaps*.json' \) -print 2>/dev/null \
    | LC_ALL=C sort | tail -40 >&2
  while IFS= read -r manifest; do
    jq -r --arg path "${manifest}" '
      select((.state? // "") == "GAPPED"
        or ((.gaps? // []) | length) > 0)
      | "\($path): state=\(.state // "n/a") gaps=\(.gaps // [])"
    ' "${manifest}" 2>/dev/null >&2 || true
  done < <(find "${case_root}" -type f -name '*.json' 2>/dev/null)
}

run_case() {
  local number=$1
  local index
  index=$(printf '%02d' "${number}")
  local config="${generated_root}/case-${index}/workflow.properties"
  local expected
  expected=$(jq -er --argjson case "${number}" '
    .cases[] | select(.case == $case) | .expected
  ' "${generated_root}/manifest.json") || return 1
  CAUSYNTH_WORKFLOW_CONFIG="${config}" \
    GRAPH_CHECKER_SKIP_BUILD=true \
    "${runner}" clean
  CAUSYNTH_WORKFLOW_CONFIG="${config}" \
    GRAPH_CHECKER_SKIP_BUILD=true \
    CAUSYNTH_CONCOLIC_JOBS="${path_jobs}" \
    "${runner}" candidate
  validate_case "${index}" "${expected}"
}

failures=0
completed=0
for ((offset = 0; offset < 13; offset += jobs)); do
  pids=()
  indexes=()
  logs=()
  upper=$((offset + jobs))
  (( upper > 13 )) && upper=13
  for ((index = offset; index < upper; index++)); do
    formatted=$(printf '%02d' "${index}")
    log="${log_root}/case-${formatted}.log"
    echo "[generated-rpc-round] starting round=${round} case=${formatted}"
    run_case "${index}" >"${log}" 2>&1 &
    pids+=("$!")
    indexes+=("${formatted}")
    logs+=("${log}")
  done
  for slot in "${!pids[@]}"; do
    formatted=${indexes[slot]}
    log=${logs[slot]}
    if wait "${pids[slot]}"; then
      expected=$(jq -r --argjson case "$((10#${formatted}))" '
        .cases[] | select(.case == $case) | .expected
      ' "${generated_root}/manifest.json")
      echo "[generated-rpc-round] case=${formatted} ${expected} passed"
    else
      status=$?
      failures=$((failures + 1))
      echo "[generated-rpc-round] case=${formatted} failed (${status}); log=${log}" >&2
      tail -n 100 "${log}" >&2
      debug_case "${formatted}"
    fi
    completed=$((completed + 1))
  done
done

echo "[generated-rpc-round] round=${round} completed=${completed} failures=${failures} logs=${log_root}"
(( failures == 0 )) || exit 1
