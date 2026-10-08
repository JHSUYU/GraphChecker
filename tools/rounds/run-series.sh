#!/usr/bin/env bash
# run-series.sh <round> <cases.tsv> <branch>=<checkout>... [case...] -- a
# system's cases one at a time, each alone on the cluster (its obligations
# over every host of LIFTS, no shared pool), as series EX1 ran them
# (docs/design/PERFORMANCE.md §6): every case of the table
# (experiments/hadoop/hdfs-cases.tsv, experiments/solr/solr-cases.tsv: case,
# branch, budget, ...), or the named ones, from the built checkout of the
# branch its row names, with its budget.  Run accept-<round>-<case without its
# system's prefix> under GC_OUT.  A case whose run has its summary row is not
# run again, so a stopped series resumes by the same command.  Then:
# tools/rounds/round-verify.sh <round> and tools/rounds/series-stats.py <round>.
#
#   CAUSYNTH_CUSTOM_JDK_HOME  the concolic VM image (required)
#   PRUNE                     accept.sh's (0 keeps every artifact, 1.5-6 GB a case)
#   <GC_OUT>/series-<round>.STOP  ends the series before its next case
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
  # accept.sh re-execs under setsid: its summary row ends the case.
  waited=0
  while (($(wc -l 2>/dev/null <"${out}/summary.tsv" || echo 0) < 2)) && ((waited < budget + 7200)); do
    sleep 30
    waited=$((waited + 30))
  done
  echo "$(date +%F_%T) $(date +%s) END ${id} ${suffix} rows=$(wc -l 2>/dev/null <"${out}/summary.tsv")" >>"${log}"
done <"${table}"
