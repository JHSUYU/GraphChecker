#!/usr/bin/env bash
# sweep.sh <snapshot> <round> <cases-file> [heads-per-host]
#
# Runs every case id of <cases-file> (a bug check is a named case whose tree
# marks its target throw, experiments/lib/README.md) as one acceptance
# campaign of the snapshot (tools/rounds/launch-run.sh): its head on one of
# the lifts (LIFTS, tools/lib/gc-env.sh), at most <heads-per-host> heads on
# each (default 1), its obligations on all of them
# (CAUSYNTH_CAMPAIGN_WORKER_HOSTS), every lift's memory gated for both
# through one ledger (fanout.sh, run_engine's host gate).  A head is admitted for the room it reserves on
# its host (tools/lib/heads.sh case_head_reserve_mb: what its planner or
# composer starts at; every other step it runs is charged where it is
# placed).  The cases running at once share the lifts' obligation slots:
# every case's CAUSYNTH_STREAM_MAX_IN_FLIGHT is the slots of LIFTS for its
# obligation_memory_mb (run_engine.sh campaign_pool_slots: on each lift, as
# many replays as fit under the ledger's ceiling when each holds its charge,
# at most its cores; ten 30 GB lifts at 70 % hold 30 of 6000 MB), and each
# exploration keeps its share of them in flight: those slots over the
# capped explorations running at once, read again at every start
# (campaign_stream_has_slot), so ten cases take a tenth each and one left
# alone takes them all.  A sweep keeps what a verdict needs (PRUNE=1) and
# gives each case CASE_TIMEOUT_SECONDS (default 5400), on the concolic VM
# image VM_IMAGE, which a sweep must name.  Case n of the file writes
# $GC_OUT/accept-<round>-<n>; <round>-cases.tsv maps n to the case id.  A
# sweep started again resumes: fanout.sh skips every case that returned.
set -uo pipefail
snapshot=$(cd "${1:?snapshot}" && pwd -P)
round=${2:?round}
cases_file=${3:?cases file}
heads=${4:-1}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# The host ledger's helpers (campaign_pool_slots, campaign_head_need_mb), as
# fanout.sh takes them; with them, tools/lib/gc-env.sh.
# shellcheck source=../../run_engine.sh
source "${here}/../../run_engine.sh"
set +e
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
out=${GC_OUT}
vm=CAUSYNTH_CUSTOM_JDK_HOME=${VM_IMAGE:?sweep.sh: name the concolic VM image as VM_IMAGE}
mkdir -p "${out}"

mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
jobs="${out}/sweep-${round}-jobs.txt"
: > "${jobs}"
: > "${out}/sweep-${round}-cases.tsv"
for n in "${!cases[@]}"; do
  config=$(case_config "${snapshot}" "${cases[$n]}")
  obligation_mb=$(case_value obligation_memory_mb "${config}")
  [[ "${obligation_mb}" =~ ^[1-9][0-9]*$ ]] || {
    echo "sweep.sh: ${cases[$n]} states no obligation_memory_mb (its \
configuration could not be read): no case is launched" >&2
    exit 2
  }
  # shellcheck disable=SC2086 # the lifts are words
  slots=$(campaign_pool_slots "${obligation_mb}" ${LIFTS})
  printf '%s\t%s\n' "${n}" "${cases[$n]}" >> "${out}/sweep-${round}-cases.tsv"
  printf '%s\n' "NEED_MB=$(case_head_reserve_mb "${config}") PRUNE=1 CASE_TIMEOUT_SECONDS=${CASE_TIMEOUT_SECONDS:-5400} CAUSYNTH_STREAM_MAX_IN_FLIGHT=${slots} CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' GC_OUT=${out} CAUSYNTH_HOST_LEDGER=${CAUSYNTH_HOST_LEDGER} ${vm} bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} '${cases[$n]}' ${round}-${n}" >> "${jobs}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${out}/sweep-${round}-logs" "${heads}"
