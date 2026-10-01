#!/usr/bin/env bash
# sweep.sh <snapshot> <round> <cases-file> [heads-per-host]
#
# Runs every case id of <cases-file> as one acceptance campaign of the
# snapshot (tools/rounds/launch-run.sh): its head on one of the lifts
# (LIFTS, tools/lib/gc-env.sh), at most <heads-per-host> heads on each
# (default 1), its obligations on all of them (CAUSYNTH_CAMPAIGN_WORKER_HOSTS),
# every lift's memory gated for both through one ledger (fanout.sh,
# run_engine's host gate): a head is admitted for its engine JVM's heap, the
# case's engine_memory_mb (run.sh config) or the launcher's 8192.  A sweep
# keeps what a verdict needs (PRUNE=1) and gives each case
# CASE_TIMEOUT_SECONDS (default 5400), on the concolic VM image VM_IMAGE
# (default: launch-run.sh's).  Case n of the file writes
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
out=${GC_OUT}
vm=${VM_IMAGE:+CAUSYNTH_CUSTOM_JDK_HOME=${VM_IMAGE}}
static=${STATIC_ROOT:+CAUSYNTH_STATIC_ROOT=${STATIC_ROOT}}

# The heap a case's head needs: the experiment a case id names is the
# longest "-"-prefix of it with a case.sh (accept.sh acc_experiment_of), and
# its config states engine_memory_mb, empty for the launcher's 8192.  The
# heap is no function of the workload's classpath, which a tree's test
# report states only once the workload ran, so the config reads none.
head_need_mb() {
  local id=$1 exp=$1 dir mb=""
  while :; do
    for dir in "${snapshot}"/experiments/*/"${exp}"; do
      [[ -f "${dir}/case.sh" ]] || continue
      local arg=${id#"${exp}"}
      mb=$(cd "${dir}" && CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
        "${snapshot}/experiments/lib/run.sh" "${dir}" "${arg#-}" config \
        2>/dev/null | sed -n 's/^engine_memory_mb=//p')
      break 2
    done
    [[ "${exp}" == *-* ]] || break
    exp=${exp%-*}
  done
  echo "${mb:-8192}"
}

mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
jobs="${out}/sweep-${round}-jobs.txt"
: > "${jobs}"
: > "${out}/sweep-${round}-cases.tsv"
for n in "${!cases[@]}"; do
  printf '%s\t%s\n' "${n}" "${cases[$n]}" >> "${out}/sweep-${round}-cases.tsv"
  printf '%s\n' "NEED_MB=$(head_need_mb "${cases[$n]}") PRUNE=1 CASE_TIMEOUT_SECONDS=${CASE_TIMEOUT_SECONDS:-5400} CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' CAUSYNTH_CONCOLIC_JOBS=${CONCOLIC_JOBS:-4} GC_OUT=${out} CAUSYNTH_HOST_LEDGER=${CAUSYNTH_HOST_LEDGER} ${vm} ${static} bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} '${cases[$n]}' ${round}-${n}" >> "${jobs}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${out}/sweep-${round}-logs" "${heads}"
