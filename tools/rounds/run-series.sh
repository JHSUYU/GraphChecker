#!/usr/bin/env bash
# run-series.sh <round> <system/hdfs checkout> <system/hdfs1 checkout> [case...]
# -- the HDFS cases one at a time, each alone on the cluster (its obligations
# over every host of LIFTS, no shared pool), as series EX1 ran them
# (docs/design/PERFORMANCE.md §6): every case of
# experiments/hadoop/hdfs-cases.tsv, or the named ones, from the built
# checkout of the branch the table names, with the table's budget.  Run
# accept-<round>-<case without "hdfs-"> under GC_OUT.  A case whose run has
# its summary row is not run again, so a stopped series resumes by the same
# command.  Then: tools/rounds/round-verify.sh <round> and
# tools/rounds/series-stats.py <round>.
#
#   CAUSYNTH_CUSTOM_JDK_HOME  the concolic VM image (required)
#   PRUNE                     accept.sh's (0 keeps every artifact, 1.5-6 GB a case)
#   <GC_OUT>/series-<round>.STOP  ends the series before its next case
set -uo pipefail
self=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${self}/tools/lib/gc-env.sh"
round=${1:?usage: run-series.sh <round> <system/hdfs checkout> <system/hdfs1 checkout> [case...]}
declare -A checkout=([system/hdfs]=$(cd "${2:?}" && pwd -P) [system/hdfs1]=$(cd "${3:?}" && pwd -P))
shift 3
: "${CAUSYNTH_CUSTOM_JDK_HOME:?run-series.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}"
log=${GC_OUT}/series-${round}.log
mkdir -p "${GC_OUT}"
while IFS=$'\t' read -r id branch budget _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  (($# == 0)) || [[ " $* " == *" ${id} "* ]] || continue
  [[ ! -e "${GC_OUT}/series-${round}.STOP" ]] || { echo "$(date +%F_%T) STOP" >>"${log}"; exit 0; }
  suffix=${round}-${id#hdfs-}
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
done <"${self}/experiments/hadoop/hdfs-cases.tsv"
