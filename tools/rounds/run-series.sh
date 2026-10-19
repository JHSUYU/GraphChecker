#!/usr/bin/env bash
set -uo pipefail
self=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${self}/tools/lib/gc-env.sh"
usage="usage: run-series.sh <round> <cases.tsv> <branch>=<checkout>... [case...]"
round=${1:?${usage}}
table=${2:?${usage}}
[[ -f "${table}" ]] || { echo "run-series.sh: no case table ${table}" >&2; exit 2; }
shift 2
declare -A checkout=()
cases=()
for arg in "$@"; do
  if [[ "${arg}" == *=* ]]; then
    checkout[${arg%%=*}]=$(cd "${arg#*=}" && pwd -P)
  else
    cases+=("${arg}")
  fi
done
: "${CAUSYNTH_CUSTOM_JDK_HOME:?run-series.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}"
log=${GC_OUT}/series-${round}.log
mkdir -p "${GC_OUT}"
while IFS=$'\t' read -r id branch budget _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  ((${#cases[@]} == 0)) || [[ " ${cases[*]} " == *" ${id} "* ]] || continue
  [[ ! -e "${GC_OUT}/series-${round}.STOP" ]] || { echo "$(date +%F_%T) STOP" >>"${log}"; exit 0; }
  [[ -n "${checkout[${branch}]:-}" ]] || { echo "run-series.sh: ${id}: no checkout named for ${branch}" >&2; exit 2; }
  suffix=${round}-${id#*-}
  out=${GC_OUT}/accept-${suffix}
  (($(wc -l 2>/dev/null <"${out}/summary.tsv" || echo 0) < 2)) || continue
  snap=${checkout[${branch}]}
  echo "$(date +%F_%T) $(date +%s) START ${id} ${suffix} ${snap} host=$(hostname -s)" >>"${log}"
  env CASE_TIMEOUT_SECONDS="${budget}" CAUSYNTH_CAMPAIGN_WORKER_HOSTS="${LIFTS}" \
    bash "${snap}/tools/rounds/launch-run.sh" "${snap}" "${id}" "${suffix}" \
    >"${GC_OUT}/launch-${suffix}.log" 2>&1 </dev/null
  waited=0
  while (($(wc -l 2>/dev/null <"${out}/summary.tsv" || echo 0) < 2)) && ((waited < budget + 7200)); do
    sleep 30
    waited=$((waited + 30))
  done
  echo "$(date +%F_%T) $(date +%s) END ${id} ${suffix} rows=$(wc -l 2>/dev/null <"${out}/summary.tsv")" >>"${log}"
done <"${table}"
