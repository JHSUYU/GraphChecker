#!/usr/bin/env bash

set -uo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
matrix="${fixture_dir}/run_robustness_matrix.sh"
jobs=${GRAPH_CHECKER_MATRIX_JOBS:-9}

die() {
  echo "[three-thread-rpc-parallel] $*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage:
  run_robustness_matrix_parallel.sh [core|all]
  run_robustness_matrix_parallel.sh PROFILE [PROFILE ...]

Builds GraphChecker exactly once, then runs independent workload directories
in bounded parallel batches. PROFILE is one of:
  baseline cross-method-fields multitype dependent-scalar containers
  unreachable-parity unreachable-correlated-fields
  unreachable-nested-object unreachable-inherited-alias

Set GRAPH_CHECKER_MATRIX_JOBS to control parallelism (default: 9).
EOF
}

valid_profile() {
  case "$1" in
    baseline|cross-method-fields|multitype|dependent-scalar|containers|unreachable-parity|unreachable-correlated-fields|unreachable-nested-object|unreachable-inherited-alias)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

config_for() {
  case "$1" in
    baseline) printf '%s/workflow.properties\n' "${fixture_dir}" ;;
    *) printf '%s/%s/workflow.properties\n' "${fixture_dir}" "$1" ;;
  esac
}

[[ "${jobs}" =~ ^[1-9][0-9]*$ ]] \
  || die "GRAPH_CHECKER_MATRIX_JOBS must be a positive integer"
(( jobs <= 9 )) || die "GRAPH_CHECKER_MATRIX_JOBS must not exceed 9"
[[ -x "${matrix}" ]] || die "matrix runner is not executable: ${matrix}"
command -v mvn >/dev/null 2>&1 || die "mvn is required"
command -v sha256sum >/dev/null 2>&1 || die "sha256sum is required"

case "${1:-all}" in
  help|-h|--help)
    usage
    exit 0
    ;;
esac

if [[ $# -eq 0 || $# -eq 1 && "${1:-}" == "all" ]]; then
  profiles=(baseline cross-method-fields multitype dependent-scalar \
    containers unreachable-parity unreachable-correlated-fields \
    unreachable-nested-object unreachable-inherited-alias)
elif [[ $# -eq 1 && "$1" == "core" ]]; then
  profiles=(baseline cross-method-fields multitype)
else
  profiles=("$@")
fi

declare -A seen=()
for profile in "${profiles[@]}"; do
  valid_profile "${profile}" || die "unknown profile: ${profile}"
  [[ -z "${seen[${profile}]:-}" ]] \
    || die "duplicate profile: ${profile}"
  seen["${profile}"]=1
done

echo "[three-thread-rpc-parallel] building GraphChecker once"
(cd "${graphchecker_dir}" && mvn -q -DskipTests package) \
  || die "GraphChecker build failed"

normalized=$("${graphchecker_dir}/run_engine.sh" \
  --config "$(config_for "${profiles[0]}")" config) \
  || die "cannot normalize workflow configuration"
graphchecker_jar=$(awk -F= '
  $1 == "graphchecker_jar" { print substr($0, index($0, "=") + 1); exit }
' <<< "${normalized}")
[[ -f "${graphchecker_jar}" ]] \
  || die "prebuilt GraphChecker jar not found: ${graphchecker_jar}"
build_hash=$(sha256sum "${graphchecker_jar}" | awk '{print $1}')

run_id=$(date -u +%Y%m%dT%H%M%SZ).$$
log_root="${graphchecker_dir}/target/robustness-matrix-logs/${run_id}"
mkdir -p "${log_root}" || die "cannot create log directory ${log_root}"

failures=0
completed=0
for ((offset = 0; offset < ${#profiles[@]}; offset += jobs)); do
  batch_pids=()
  batch_profiles=()
  batch_logs=()
  upper=$((offset + jobs))
  (( upper > ${#profiles[@]} )) && upper=${#profiles[@]}
  for ((index = offset; index < upper; index++)); do
    profile=${profiles[index]}
    log="${log_root}/${profile}.log"
    echo "[three-thread-rpc-parallel] starting ${profile}"
    GRAPH_CHECKER_SKIP_BUILD=true "${matrix}" "${profile}" \
      >"${log}" 2>&1 &
    batch_pids+=("$!")
    batch_profiles+=("${profile}")
    batch_logs+=("${log}")
  done

  for index in "${!batch_pids[@]}"; do
    profile=${batch_profiles[index]}
    log=${batch_logs[index]}
    if wait "${batch_pids[index]}"; then
      result=$(grep -F \
        "[three-thread-rpc-matrix] ${profile}:" "${log}" | tail -n 1)
      echo "[three-thread-rpc-parallel] ${result}"
    else
      status=$?
      failures=$((failures + 1))
      echo "[three-thread-rpc-parallel] ${profile} failed (${status}); log=${log}" >&2
      tail -n 80 "${log}" >&2
    fi
    completed=$((completed + 1))
  done
done

final_hash=$(sha256sum "${graphchecker_jar}" | awk '{print $1}')
[[ "${final_hash}" == "${build_hash}" ]] \
  || die "shared GraphChecker jar changed during parallel fixture execution"

echo "[three-thread-rpc-parallel] completed=${completed} failures=${failures} logs=${log_root}"
(( failures == 0 )) || exit 1
