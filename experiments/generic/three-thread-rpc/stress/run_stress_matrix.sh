#!/usr/bin/env bash

set -uo pipefail

stress_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${stress_dir}/../../../.." && pwd -P)
pipeline="${stress_dir}/../run.sh"
manifest="${stress_dir}/manifest.tsv"
jobs=${GRAPH_CHECKER_STRESS_JOBS:-20}
maven_repo=${GRAPH_CHECKER_MAVEN_REPO:-${graphchecker_dir}/target/codex-m2/repository}

die() {
  echo "[stress-matrix] $*" >&2
  exit 1
}

[[ "${jobs}" =~ ^[1-9][0-9]*$ ]] \
  || die "GRAPH_CHECKER_STRESS_JOBS must be positive"
(( jobs <= 64 )) || die "GRAPH_CHECKER_STRESS_JOBS must not exceed 64"
[[ -f "${manifest}" ]] || die "missing manifest; run generate_round.py"
[[ -x "${pipeline}" ]] || die "pipeline is not executable"

round=$(sed -n 's/^# round=//p' "${manifest}")
[[ "${round}" =~ ^([1-9]|10)$ ]] || die "manifest has invalid round"
requested_round=${1:-"${round}"}
[[ "${requested_round}" == "${round}" ]] \
  || die "current generated round is ${round}, not ${requested_round}"

declare -a cases classes targets expected configs work_roots
while IFS=$'\t' read -r case_number class_name target_id expectation \
    _producer_a _producer_b _consumer; do
  [[ "${case_number}" =~ ^[0-9][0-9]$ ]] || continue
  cases+=("${case_number}")
  classes+=("${class_name}")
  targets+=("${target_id}")
  expected+=("${expectation}")
  configs+=("${stress_dir}/generated/case-${case_number}/workflow.properties")
  work_roots+=("${graphchecker_dir}/target/stress-r$(printf '%02d' "${round}")-c${case_number}")
done < "${manifest}"
[[ ${#cases[@]} -eq 20 ]] || die "manifest must contain 20 cases"

echo "[stress-matrix] round=${round}: building once"
(cd "${graphchecker_dir}" && \
  MAVEN_OPTS="-Dmaven.repo.local=${maven_repo} ${MAVEN_OPTS:-}" \
  mvn -q -DskipTests package) \
  || die "GraphChecker or generated fixture compilation failed"
jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
[[ -f "${jar}" ]] || die "GraphChecker jar not found"
build_hash=$(sha256sum "${jar}" | awk '{print $1}')
"${stress_dir}/validate_concrete_round.sh" \
  || die "generated workloads do not match their concrete SAT/UNSAT labels"

run_id=$(date -u +%Y%m%dT%H%M%SZ).$$
log_root="${graphchecker_dir}/target/stress-matrix-logs/round-$(printf '%02d' "${round}")-${run_id}"
mkdir -p "${log_root}" || die "cannot create ${log_root}"
raw_results="${log_root}/results.unsorted.tsv"
: >"${raw_results}"

sanitize() {
  tr '\t\r\n' '   ' | sed 's/[[:space:]][[:space:]]*/ /g'
}

failure_detail() {
  local root=$1
  local log=$2
  local row
  row=$(find "${root}" -type f -name concolic_import_diagnostics.jsonl \
      -exec jq -r 'select(.code != null)
        | "IMPORT:" + .code + ":" + (.detail // "")' {} + \
      2>/dev/null | tail -1)
  if [[ -n "${row}" ]]; then
    printf '%s' "${row}" | sanitize
    return
  fi
  row=$(find "${root}" -type f -name path_flip_solver_result.json \
      -exec jq -r 'select(.status != "SAT_MODEL_READY"
          and .status != "UNSAT")
        | "SOLVER:" + (.status // "") + ":" + (.reason // "")
        + ":" + ((.unsupported // []) | join(","))' {} + \
      2>/dev/null | tail -1)
  if [[ -n "${row}" ]]; then
    printf '%s' "${row}" | sanitize
    return
  fi
  row=$(find "${root}" -type f \
      \( -name region_path_closure.json -o -name region_path_manifest.json \) \
      -exec jq -r 'select((.gaps // []) | length > 0)
        | "WORKLIST:" + (.state // "") + ":"
        + ((.gaps // []) | map((.kind // "") + ":" + (.reason // "")
          + ":" + (.subject // "")) | join(","))' {} + \
      2>/dev/null | tail -1)
  if [[ -n "${row}" ]]; then
    printf '%s' "${row}" | sanitize
    return
  fi
  row=$(jq -r 'select((.gaps // []) | length > 0)
      | "COMPOSE:" + (.state // "") + ":"
      + ((.gaps // []) | map((.kind // "") + ":" + (.subject // ""))
        | join(","))' \
      "${root}/candidate/candidate_composition_manifest.json" \
      2>/dev/null)
  if [[ -n "${row}" ]]; then
    printf '%s' "${row}" | sanitize
    return
  fi
  grep -E '\[three-thread-rpc\].*(failed|incomplete|not |lost |timed out)' \
      "${log}" | tail -1 | sanitize
}

resolved_rpc_binding_count() {
  local root=$1
  local composition="${root}/candidate/candidate_composition_manifest.json"
  local a_plan="${root}/schedule-a/execution_task_plan.jsonl"
  local b_plan="${root}/schedule-b/execution_task_plan.jsonl"
  [[ -s "${composition}" && -s "${a_plan}" && -s "${b_plan}" ]] || {
    echo 0
    return
  }
  jq -r '.edgeBindings[]?.edgeId' "${a_plan}" "${b_plan}" \
    | sort -u \
    | jq -Rsc --slurpfile composition "${composition}" '
        split("\n") | map(select(length > 0)) as $required
        | ($composition[0].resolvedEdgeBindings // []) as $resolved
        | [$required[] as $id
            | select($resolved | index($id) != null)] | length'
}

run_case() {
  local index=$1
  local case_number=${cases[index]}
  local expectation=${expected[index]}
  local config=${configs[index]}
  local root=${work_roots[index]}
  local log="${log_root}/case-${case_number}.log"
  local process_status observed="UNKNOWN" result="FAIL" detail=""
  local resolved_rpc_bindings=0
  echo "[stress-matrix] round=${round} starting case=${case_number}"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_WORKFLOW_CONFIG="${config}" \
    GRAPH_CHECKER_SKIP_BUILD=true \
    "${pipeline}" clean && \
    CAUSYNTH_WORKFLOW_CONFIG="${config}" \
    GRAPH_CHECKER_SKIP_BUILD=true \
    "${pipeline}" full) >"${log}" 2>&1
  process_status=$?
  if [[ -s "${root}/candidate/candidate_result_manifest.json" ]]; then
    observed=$(jq -r '.reachability // "UNKNOWN"' \
      "${root}/candidate/candidate_result_manifest.json")
  fi
  resolved_rpc_bindings=$(resolved_rpc_binding_count "${root}")
  local expected_reachability=UNREACHABLE
  [[ "${expectation}" == "SAT" ]] && expected_reachability=REACHABLE
  if [[ ${process_status} -eq 0
        && "${observed}" == "${expected_reachability}"
        && "${resolved_rpc_bindings}" -eq 2 ]]; then
    result=PASS
  elif [[ ${process_status} -eq 0
          && "${resolved_rpc_bindings}" -ne 2 ]]; then
    detail="COMPOSE:EXPECTED_TWO_RPC_BINDINGS:observed=${resolved_rpc_bindings}"
  else
    detail=$(failure_detail "${root}" "${log}")
    [[ -n "${detail}" ]] || detail="PIPELINE_EXIT:${process_status}"
  fi
  [[ -n "${detail}" ]] || detail="-"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${case_number}" "${classes[index]}" "${expectation}" \
    "${observed}" "${result}" "${process_status}" "${detail}" \
    >>"${raw_results}"
}

for ((offset = 0; offset < 20; offset += jobs)); do
  pids=()
  upper=$((offset + jobs))
  (( upper > 20 )) && upper=20
  for ((index = offset; index < upper; index++)); do
    run_case "${index}" &
    pids+=("$!")
  done
  for pid in "${pids[@]}"; do
    wait "${pid}" || die "case collector crashed"
  done
done

results="${stress_dir}/history/round-$(printf '%02d' "${round}")-results.tsv"
{
  printf '# round=%s\n' "${round}"
  printf 'case\tclass\texpected\tobserved\tresult\texit\tdetail\n'
  sort -t $'\t' -k1,1 "${raw_results}"
} >"${results}"

passes=$(awk -F'\t' '$5 == "PASS" {count++} END {print count+0}' "${results}")
failures=$((20 - passes))
final_hash=$(sha256sum "${jar}" | awk '{print $1}')
[[ "${final_hash}" == "${build_hash}" ]] \
  || die "shared GraphChecker jar changed during matrix"
echo "[stress-matrix] round=${round} completed=20 passes=${passes} failures=${failures}"
echo "[stress-matrix] results=${results}"
echo "[stress-matrix] logs=${log_root}"
if [[ ${failures} -ne 0 ]]; then
  exit 1
fi
