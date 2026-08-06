#!/usr/bin/env bash

set -euo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
fixture_runner="${fixture_dir}/run.sh"
engine_runner="${graphchecker_dir}/run_engine.sh"
log_root="${graphchecker_dir}/target/three-thread-rpc-matrix-logs"

die() {
  echo "[three-thread-rpc-matrix] $*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: experiments/generic/three-thread-rpc/run_robustness_matrix.sh [MODE]

  full                         Run all 18 real workflows (default)
  all                          Run the original 13 workflows
  core                         Run baseline, cross-method, and multitype
  container-tricky             Run the five tricky container workflows
  <workflow-label>             Run one named workflow

The runner builds once, executes independent workflows in parallel, and checks
only the durable fixture contract: complete composition, at least two proven
shared-field bindings, expected reachability, and the matching Z3 sat/unsat
result. CAUSYNTH_FIXTURE_JOBS controls workflow-level parallelism.
EOF
}

configured_value() {
  local normalized=$1
  local key=$2
  local value
  value=$(sed -n "s/^${key}=//p" <<< "${normalized}")
  [[ -n "${value}" ]] || die "normalized config has no ${key}"
  printf '%s\n' "${value}"
}

resolve_executable() {
  local candidate=$1
  if [[ "${candidate}" != */* ]]; then
    candidate=$(command -v "${candidate}") \
      || die "executable not found on PATH: ${candidate}"
  elif [[ "${candidate}" != /* ]]; then
    candidate="${graphchecker_dir}/${candidate}"
  fi
  candidate=$(realpath -m -- "${candidate}")
  [[ -x "${candidate}" ]] || die "executable not found: ${candidate}"
  printf '%s\n' "${candidate}"
}

expected_reachability() {
  case "$1" in
    cross-method-fields|multitype|dependent-scalar|containers|\
    compound-target|tricky-divergent-object-fields|\
    tricky-map-key-value)
      printf 'REACHABLE\n'
      ;;
    baseline|unreachable-parity|unreachable-correlated-fields|\
    unreachable-nested-object|unreachable-inherited-alias|\
    unreachable-mutated-object|unreachable-long-fields|\
    unreachable-compound-target|tricky-nested-array-map-key|\
    tricky-array-element-frame|tricky-compound-container-guard)
      printf 'UNREACHABLE\n'
      ;;
    *) die "no expected result for workflow $1" ;;
  esac
}

config_for() {
  case "$1" in
    baseline) printf 'workflow.properties\n' ;;
    cross-method-fields) printf 'cross-method-fields/workflow.properties\n' ;;
    multitype) printf 'multitype/workflow.properties\n' ;;
    dependent-scalar) printf 'dependent-scalar/workflow.properties\n' ;;
    containers) printf 'containers/workflow.properties\n' ;;
    unreachable-parity) printf 'unreachable-parity/workflow.properties\n' ;;
    unreachable-correlated-fields)
      printf 'unreachable-correlated-fields/workflow.properties\n'
      ;;
    unreachable-nested-object)
      printf 'unreachable-nested-object/workflow.properties\n'
      ;;
    unreachable-inherited-alias)
      printf 'unreachable-inherited-alias/workflow.properties\n'
      ;;
    unreachable-mutated-object)
      printf 'unreachable-mutated-object/workflow.properties\n'
      ;;
    unreachable-long-fields)
      printf 'unreachable-long-fields/workflow.properties\n'
      ;;
    compound-target) printf 'compound-target/workflow.properties\n' ;;
    unreachable-compound-target)
      printf 'unreachable-compound-target/workflow.properties\n'
      ;;
    tricky-nested-array-map-key)
      printf 'tricky-nested-array-map-key/workflow.properties\n'
      ;;
    tricky-divergent-object-fields)
      printf 'tricky-divergent-object-fields/workflow.properties\n'
      ;;
    tricky-array-element-frame)
      printf 'tricky-array-element-frame/workflow.properties\n'
      ;;
    tricky-map-key-value)
      printf 'tricky-map-key-value/workflow.properties\n'
      ;;
    tricky-compound-container-guard)
      printf 'tricky-compound-container-guard/workflow.properties\n'
      ;;
    *) die "unknown workflow label: $1" ;;
  esac
}

validate_candidate() {
  local label=$1
  local work_root=$2
  local z3=$3
  local expected=$4
  local candidate="${work_root}/candidate"
  local composition="${candidate}/candidate_composition_manifest.json"
  local reach="${candidate}/candidate_boolean_model.json"
  local manifest="${candidate}/candidate_result_manifest.json"
  local smt="${candidate}/candidate.smt2"
  local expected_solver solver_output solver_status

  for artifact in "${composition}" "${reach}" "${manifest}" "${smt}"; do
    [[ -s "${artifact}" ]] || die "${label} artifact missing: ${artifact}"
  done

  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_COMPOSED_SMT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.gaps | type == "array" and length == 0)
    and (.resolvedEdgeBindings | type == "array" and length >= 2)
  ' "${composition}" >/dev/null \
    || die "${label} composition is incomplete: ${composition}"

  jq -e --arg expected "${expected}" '
    .schemaVersion == 3
    and .kind == "BOOLEAN_REACH_CONDITION_REPORT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and .reachCondition.reachability == $expected
    and (.gaps | type == "array" and length == 0)
    and (.valuations | type == "array" and length > 0)
    and (if $expected == "REACHABLE"
      then any(.valuations[]; .status == "sat")
      else all(.valuations[]; .status == "unsat")
      end)
  ' "${reach}" >/dev/null \
    || die "${label} reachability differs from ${expected}: ${reach}"

  jq -e --arg expected "${expected}" '
    .schemaVersion == 2
    and .kind == "CONCOLIC_CANDIDATE_RESULT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and .reachability == $expected
  ' "${manifest}" >/dev/null \
    || die "${label} result manifest differs from ${expected}: ${manifest}"

  expected_solver=$([[ "${expected}" == "REACHABLE" ]] \
    && printf sat || printf unsat)
  solver_output=$("${z3}" "${smt}") \
    || die "${label} z3 execution failed"
  [[ "${solver_output}" != *"(error"* ]] \
    || die "${label} z3 reported an SMT error"
  solver_status=$(awk 'NF {print $1; exit}' <<< "${solver_output}")
  [[ "${solver_status}" == "${expected_solver}" ]] \
    || die "${label} expected z3 ${expected_solver}, got ${solver_status}"
  echo "[three-thread-rpc-matrix] ${label}: ${expected}, z3=${solver_status}"
}

run_case() {
  local label=$1
  local config="${fixture_dir}/$(config_for "${label}")"
  local normalized analysis_dir work_root z3 expected

  [[ -f "${config}" ]] || die "${label} config not found: ${config}"
  normalized=$("${engine_runner}" --config "${config}" config) || return $?
  analysis_dir=$(configured_value "${normalized}" causynth_output_dir)
  work_root=$(dirname "${analysis_dir}")
  z3=$(resolve_executable "$(configured_value "${normalized}" z3_bin)") \
    || return $?
  expected=$(expected_reachability "${label}") || return $?

  echo "[three-thread-rpc-matrix] ${label}: clean"
  CAUSYNTH_WORKFLOW_CONFIG="${config}" "${fixture_runner}" clean \
    || return $?
  echo "[three-thread-rpc-matrix] ${label}: candidate"
  CAUSYNTH_WORKFLOW_CONFIG="${config}" \
    GRAPH_CHECKER_SKIP_BUILD=true \
    "${fixture_runner}" full || return $?
  validate_candidate "${label}" "${work_root}" "${z3}" "${expected}"
}

run_batch() {
  local label pid failed=false
  local -a batch_labels=("$@")
  local -a pids=()
  for label in "${batch_labels[@]}"; do
    (run_case "${label}") >"${log_root}/${label}.log" 2>&1 &
    pids+=("$!")
  done
  for index in "${!pids[@]}"; do
    label=${batch_labels[${index}]}
    pid=${pids[${index}]}
    if wait "${pid}"; then
      tail -n 1 "${log_root}/${label}.log"
    else
      failed=true
      echo "[three-thread-rpc-matrix] ${label}: FAILED; log=${log_root}/${label}.log" >&2
      tail -n 80 "${log_root}/${label}.log" >&2 || true
    fi
  done
  [[ "${failed}" == "false" ]]
}

run_parallel() {
  local jobs=$1
  shift
  local -a pending=("$@")
  local offset=0
  while (( offset < ${#pending[@]} )); do
    run_batch "${pending[@]:offset:jobs}" \
      || die "fixture batch failed"
    offset=$((offset + jobs))
  done
}

original=(
  baseline cross-method-fields multitype dependent-scalar containers
  unreachable-parity unreachable-correlated-fields
  unreachable-nested-object unreachable-inherited-alias
  unreachable-mutated-object unreachable-long-fields compound-target
  unreachable-compound-target
)
tricky=(
  tricky-nested-array-map-key tricky-divergent-object-fields
  tricky-array-element-frame tricky-map-key-value
  tricky-compound-container-guard
)

mode=${1:-full}
[[ $# -le 1 ]] || die "expected at most one mode"
case "${mode}" in
  help|-h|--help) usage; exit 0 ;;
  full) labels=("${original[@]}" "${tricky[@]}") ;;
  all) labels=("${original[@]}") ;;
  core) labels=(baseline cross-method-fields multitype) ;;
  container-tricky) labels=("${tricky[@]}") ;;
  *) config_for "${mode}" >/dev/null; labels=("${mode}") ;;
esac

jobs=${CAUSYNTH_FIXTURE_JOBS:-4}
[[ "${jobs}" =~ ^[1-9][0-9]*$ ]] \
  || die "CAUSYNTH_FIXTURE_JOBS must be a positive integer"
mkdir -p "${log_root}"
find "${log_root}" -mindepth 1 -maxdepth 1 -type f -name '*.log' -delete

echo "[three-thread-rpc-matrix] building once"
(cd "${graphchecker_dir}" && mvn -q -DskipTests package)
run_parallel "${jobs}" "${labels[@]}"
echo "[three-thread-rpc-matrix] validated ${#labels[@]} workflows"
