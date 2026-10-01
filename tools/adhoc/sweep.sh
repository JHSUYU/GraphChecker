#!/usr/bin/env bash
# sweep.sh <snapshot> <round> <cases-file> [heads-per-host]
#
# Runs every case id of <cases-file> as one acceptance campaign of the
# snapshot (tools/rounds/launch-run.sh): its head on one of the lifts
# (LIFTS, tools/lib/gc-env.sh), at most <heads-per-host> heads on each
# (default 1), its obligations on all of them (CAUSYNTH_CAMPAIGN_WORKER_HOSTS),
# every lift's memory gated for both through one ledger (fanout.sh,
# run_engine's host gate): a head is admitted for its engine JVM's heap, the
# case's engine_memory_mb (run.sh config) or the launcher's 8192
# (tools/lib/heads.sh case_head_need_mb).  A sweep
# keeps what a verdict needs (PRUNE=1) and gives each case
# CASE_TIMEOUT_SECONDS (default 5400), on the concolic VM image VM_IMAGE,
# which a sweep must name.  Case n of the file writes
# $GC_OUT/accept-<round>-<n>; <round>-cases.tsv maps n to the case id.  A
# sweep started again resumes: fanout.sh skips every case that returned.
# STATIC_ROOT, when set, is every case's causynth_static_root: an ad-hoc
# batch case (cover.py `cases`) takes its checks' static slices from the
# build's $GC_OUT/static/<key> (slice.sh) and records once for all of them.
set -uo pipefail
snapshot=$(cd "${1:?snapshot}" && pwd -P)
round=${2:?round}
cases_file=${3:?cases file}
heads=${4:-1}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${here}/../lib/gc-env.sh"
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
out=${GC_OUT}
vm=CAUSYNTH_CUSTOM_JDK_HOME=${VM_IMAGE:?sweep.sh: name the concolic VM image as VM_IMAGE}
static=${STATIC_ROOT:+CAUSYNTH_STATIC_ROOT=${STATIC_ROOT}}

mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
jobs="${out}/sweep-${round}-jobs.txt"
: > "${jobs}"
: > "${out}/sweep-${round}-cases.tsv"
for n in "${!cases[@]}"; do
  printf '%s\t%s\n' "${n}" "${cases[$n]}" >> "${out}/sweep-${round}-cases.tsv"
  printf '%s\n' "NEED_MB=$(case_head_need_mb "${snapshot}" "${cases[$n]}") PRUNE=1 CASE_TIMEOUT_SECONDS=${CASE_TIMEOUT_SECONDS:-5400} CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' GC_OUT=${out} CAUSYNTH_HOST_LEDGER=${CAUSYNTH_HOST_LEDGER} ${vm} ${static} bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} '${cases[$n]}' ${round}-${n}" >> "${jobs}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${out}/sweep-${round}-logs" "${heads}"
