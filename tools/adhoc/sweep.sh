#!/usr/bin/env bash
# sweep.sh <snapshot> <round> <cases-file> [heads-per-host]
#
# Runs every case id of <cases-file> as one acceptance campaign of the
# snapshot (tools/rounds/launch-run.sh): its head on one of the ten lifts, at
# most <heads-per-host> heads on each (default 1), its obligations on all ten
# (CAUSYNTH_CAMPAIGN_WORKER_HOSTS), every lift's memory gated for both
# (fanout.sh, run_engine's host gate).  A sweep keeps what a verdict needs
# (PRUNE=1) and gives each case CASE_TIMEOUT_SECONDS (default 5400).  Case n
# of the file writes $GC_OUT/accept-<round>-<n>; <round>-cases.tsv maps n to
# the case id.
set -uo pipefail
snapshot=$(cd "${1:?snapshot}" && pwd -P)
round=${2:?round}
cases_file=${3:?cases file}
heads=${4:-1}
out=${GC_OUT:-/u/vnr3ne/gc-out}
lifts="lift06 lift07 lift08 lift09 lift10 lift11 lift12 lift13 lift14 lift15"
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
jobs="${out}/sweep-${round}-jobs.txt"
: > "${jobs}"
: > "${out}/sweep-${round}-cases.tsv"
for n in "${!cases[@]}"; do
  printf '%s\t%s\n' "${n}" "${cases[$n]}" >> "${out}/sweep-${round}-cases.tsv"
  printf '%s\n' "PRUNE=1 CASE_TIMEOUT_SECONDS=${CASE_TIMEOUT_SECONDS:-5400} CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${lifts}' CAUSYNTH_CONCOLIC_JOBS=${CONCOLIC_JOBS:-4} GC_OUT=${out} CAUSYNTH_CUSTOM_JDK_HOME=${out}/vm-f5/j2sdk-image bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} '${cases[$n]}' ${round}-${n}" >> "${jobs}"
done
JOB_MEMORY_MB=${HEAD_MEMORY_MB:-12000} exec bash "${here}/fanout.sh" "${jobs}" \
  "${out}/sweep-${round}-logs" "${heads}"
