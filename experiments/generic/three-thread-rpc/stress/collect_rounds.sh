#!/usr/bin/env bash

set -uo pipefail

stress_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
first=${1:-1}
last=${2:-5}

[[ "${first}" =~ ^([1-9]|10)$ && "${last}" =~ ^([1-9]|10)$ ]] || {
  echo "usage: $0 [first-round] [last-round]" >&2
  exit 1
}
(( first <= last )) || {
  echo "first round must not exceed last round" >&2
  exit 1
}

failed_rounds=0
for ((round = first; round <= last; round++)); do
  echo "[stress-collect] generating round=${round}"
  "${stress_dir}/generate_round.py" "${round}" || exit 1
  if ! "${stress_dir}/run_stress_matrix.sh" "${round}"; then
    echo "[stress-collect] round=${round} failed" >&2
    failed_rounds=$((failed_rounds + 1))
  fi
done

if [[ ${failed_rounds} -ne 0 ]]; then
  echo "[stress-collect] completed with failed rounds=${failed_rounds}" >&2
  exit 1
fi
echo "[stress-collect] collected rounds ${first}-${last}"
