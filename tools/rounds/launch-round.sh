#!/usr/bin/env bash
# launch-round.sh <snapshot> <round>
#
# Starts the eleven acceptance campaigns of one round (nine HDFS, two Solr)
# from one snapshot worktree, each
# detached on its head host, every one with its obligations spread over
# every host in LIFTS:
#
#   tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22
#   CASES="hdfs-17960 hdfs-11741" tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22b
#
# A campaign's HEAD runs its seed recording, its planner and its composer;
# the heads are spread so no host carries two heavy ones: 11741 and each Solr
# case alone on its head, two cases on each of the others.  lift11 -- the
# owner's interactive machine -- is no head, only a worker.  Its OBLIGATIONS
# run on every host in LIFTS, as many on a host as it has the case's
# obligation_memory_mb to spare beyond what every campaign's recent starts
# there will still claim, up to its cores (run_engine.sh,
# campaign_stream_admit_host): the hosts' memory makes the pool wide, and the
# same ledger keeps each host's memory safe.
#
# CASES narrows the round to some of its cases, each still on its own head.
# CAUSYNTH_CUSTOM_JDK_HOME, when set, is the VM image every campaign runs
# (launch-run.sh's default otherwise).
# Outputs: $GC_OUT/accept-<round>-<case without hdfs->/, launcher logs
# $GC_OUT/launch-<round>-<case without hdfs->.log.  One campaign is stopped
# with tools/rounds/stop-run.sh <round>-<case without hdfs->: a campaign is
# many process groups on every lift, so no one group id stops it.  A round's
# directories are written once: a name already used is refused.
set -euo pipefail

snapshot=${1:?usage: launch-round.sh <snapshot> <round>}
round=${2:?usage: launch-round.sh <snapshot> <round>}
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
out=${GC_OUT}

# head host, then the cases it heads.
placement=(
  "lift06 hdfs-11741"
  "lift07 hdfs-17960 hdfs-17967-pathC"
  "lift08 hdfs-17899-bug1 hdfs-17899-bug2"
  "lift09 hdfs-17899-bug3 hdfs-17897"
  "lift10 hdfs-17967-pathA hdfs-17967-pathB"
  "lift12 solr-18413"
  "lift13 solr-18406"
)
# Experiments run only when CASES names them.
experiments=(
  "lift14 hdfs-token-key"
  "lift15 hdfs-17897-nowire"
)
[[ -z "${CASES:-}" ]] || placement+=("${experiments[@]}")

[[ -s "${snapshot}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar" ]] \
  || { echo "no built jar in the snapshot: ${snapshot}" >&2; exit 2; }
wanted=" ${CASES:-} "
vm=${CAUSYNTH_CUSTOM_JDK_HOME:+CAUSYNTH_CUSTOM_JDK_HOME=${CAUSYNTH_CUSTOM_JDK_HOME}}

launches=()
for row in "${placement[@]}"; do
  read -r head cases <<<"${row}"
  for case_id in ${cases}; do
    [[ -z "${CASES:-}" || "${wanted}" == *" ${case_id} "* ]] || continue
    suffix="${round}-${case_id#hdfs-}"
    [[ ! -e "${out}/accept-${suffix}" && ! -e "${out}/launch-${suffix}.log" ]] \
      || { echo "round ${round} already has ${case_id}: ${out}/accept-${suffix}" >&2; exit 2; }
    launches+=("${head} ${case_id} ${suffix}")
  done
done
# A named case no row places (an ad-hoc case) takes the hosts but lift11 in
# turn; accept.sh refuses an id no case directory declares.
read -r -a heads <<<"${LIFTS/lift11 /}"
turn=0
for case_id in ${CASES:-}; do
  [[ " ${launches[*]:-} " == *" ${case_id} "* ]] && continue
  suffix="${round}-${case_id#hdfs-}"
  [[ ! -e "${out}/accept-${suffix}" && ! -e "${out}/launch-${suffix}.log" ]] \
    || { echo "round ${round} already has ${case_id}: ${out}/accept-${suffix}" >&2; exit 2; }
  launches+=("${heads[$((turn % ${#heads[@]}))]} ${case_id} ${suffix}")
  turn=$((turn + 1))
done
[[ ${#launches[@]} -gt 0 ]] || { echo "no case of the round matches CASES='${CASES:-}'" >&2; exit 2; }

mkdir -p "${out}"
for launch in "${launches[@]}"; do
  read -r head case_id suffix <<<"${launch}"
  command="setsid nohup env CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' \
GC_OUT=${out} \
CAUSYNTH_HOST_LEDGER=${CAUSYNTH_HOST_LEDGER} ${vm} \
bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} ${case_id} ${suffix} \
> ${out}/launch-${suffix}.log 2>&1 < /dev/null &"
  if [[ "${head}" == "$(hostname -s)" ]]; then
    bash -c "${command}"
  else
    ssh -n -o BatchMode=yes -o ConnectTimeout=20 "${head}" "${command}"
  fi
  echo "$(date +%T) LAUNCHED ${case_id} head=${head} on ${LIFTS} -> ${out}/accept-${suffix}"
done
