#!/usr/bin/env bash
# launch-round.sh <snapshot> <round>
#
# Starts the acceptance campaigns of one round from one snapshot worktree --
# the eleven cases (nine HDFS, two Solr), or the cases CASES names (any case
# id a case directory declares) -- each detached on its
# head host, every one with its obligations spread over every host in LIFTS:
#
#   CAUSYNTH_CUSTOM_JDK_HOME=<image> tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22
#   CASES="hdfs-17960 hdfs-11741" CAUSYNTH_CUSTOM_JDK_HOME=<image> \
#     tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22b
#
# A campaign's HEAD is the shell that drives it.  Every heavy step it takes
# -- an engine JVM of any stage, the seed and CONFIRM replays, REPRODUCE's
# native runs -- goes wherever the host ledger has room, its own host first
# (run_engine.sh campaign_head_charged), and its host keeps room for its
# next planner or composer (campaign_head_reserve).  Its OBLIGATIONS run on
# every host in LIFTS, as many on a host as its memory admits, up to its
# cores (campaign_stream_admit_host).  So the head hosts are chosen here, at
# launch, from the hosts' room now -- the ledger's reading every start takes
# (campaign_host_room) -- the heaviest case first (its engine heap,
# tools/lib/heads.sh case_engine_heap_mb), each to the host with the most
# room among those that head the fewest cases: no host heads two before
# every host heads one.
# lift11 -- the owner's interactive machine -- heads nothing but is a
# worker, and a host whose memory cannot be read heads nothing either.
#
# CAUSYNTH_CUSTOM_JDK_HOME is the VM image every campaign runs; a launch
# must name it.  DRY=1 prints the heads chosen and launches nothing.
# Outputs: $GC_OUT/accept-<round>-<case without hdfs->/, launcher logs
# $GC_OUT/launch-<round>-<case without hdfs->.log.  One campaign is stopped
# with tools/rounds/stop-run.sh <round>-<case without hdfs->: a campaign is
# many process groups on every lift, so no one group id stops it.  A round's
# directories are written once: a name already used is refused.
set -euo pipefail

snapshot=${1:?usage: launch-round.sh <snapshot> <round>}
round=${2:?usage: launch-round.sh <snapshot> <round>}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# The host ledger's helpers (campaign_host_room, campaign_host_is_local), as
# tools/adhoc/fanout.sh takes them; with them, tools/lib/gc-env.sh.
# shellcheck source=../../run_engine.sh
source "${here}/../../run_engine.sh"
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
out=${GC_OUT}
vm=${CAUSYNTH_CUSTOM_JDK_HOME:?launch-round.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}
# The owner's interactive machine: a worker, never a head.
owner_host=lift11
round_cases=(hdfs-11741 hdfs-17960 hdfs-17967-pathA hdfs-17967-pathB
  hdfs-17967-pathC hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3
  hdfs-17897 solr-18413 solr-18406)
read -r -a cases <<<"${CASES:-${round_cases[*]}}"
(( ${#cases[@]} > 0 )) || { echo "CASES names no case" >&2; exit 2; }

[[ -s "${snapshot}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar" ]] \
  || { echo "no built jar in the snapshot: ${snapshot}" >&2; exit 2; }
for case_id in "${cases[@]}"; do
  suffix="${round}-${case_id#hdfs-}"
  [[ ! -e "${out}/accept-${suffix}" && ! -e "${out}/launch-${suffix}.log" ]] \
    || { echo "round ${round} already has ${case_id}: ${out}/accept-${suffix}" >&2; exit 2; }
done

heads=()
for host in ${LIFTS}; do
  [[ "${host}" != "${owner_host}" ]] || continue
  if room=$(campaign_host_room "${host}"); then
    heads+=("${host}:${room}")
  else
    echo "the memory of ${host} could not be read: it heads nothing" >&2
  fi
done
(( ${#heads[@]} > 0 )) \
  || { echo "no host of LIFTS but ${owner_host} could be read: no head" >&2; exit 2; }
mapfile -t launches < <(for case_id in "${cases[@]}"; do
    printf '%s %s\n' \
      "$(case_engine_heap_mb "$(case_config "${snapshot}" "${case_id}")")" \
      "${case_id}"
  done | heads_choose "${heads[@]}")

mkdir -p "${out}"
# A measurement run (CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT) reaches a head on
# another host only on the command line: ssh carries no environment.
stop_after=
[[ -z "${CAUSYNTH_CAMPAIGN_STOP_AFTER+x}" ]] \
  || stop_after="CAUSYNTH_CAMPAIGN_STOP_AFTER='${CAUSYNTH_CAMPAIGN_STOP_AFTER}'"
for launch in "${launches[@]}"; do
  read -r case_id head <<<"${launch}"
  if [[ -n "${DRY:-}" ]]; then
    echo "${case_id} head=${head}"
    continue
  fi
  suffix="${round}-${case_id#hdfs-}"
  command="setsid nohup env CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' \
GC_OUT=${out} CAUSYNTH_HOST_LEDGER=${CAUSYNTH_HOST_LEDGER} \
CAUSYNTH_HOST_MAX_USED_PCT=${CAUSYNTH_HOST_MAX_USED_PCT} \
CAUSYNTH_CUSTOM_JDK_HOME=${vm} ${stop_after} \
bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} ${case_id} ${suffix} \
> ${out}/launch-${suffix}.log 2>&1 < /dev/null &"
  if campaign_host_is_local "${head}"; then
    bash -c "${command}"
  else
    ssh -n -o BatchMode=yes -o ConnectTimeout=20 "${head}" "${command}"
  fi
  echo "$(date +%T) LAUNCHED ${case_id} head=${head} on ${LIFTS} -> ${out}/accept-${suffix}"
done
