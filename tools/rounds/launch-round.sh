#!/usr/bin/env bash
# launch-round.sh <snapshot> <round> [workers-per-host]
#
# Starts the nine campaigns of one round from one snapshot worktree, each
# detached on its head host, every one with its obligations spread over all
# five lifts:
#
#   tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22
#   CASES="hdfs-17960 hdfs-11741" tools/rounds/launch-round.sh /u/vnr3ne/gc-run/p25 v22b
#
# A campaign's HEAD runs its seed recording, its planner and its composer;
# the heads are spread so no lift carries two heavy ones: 11741 (whose
# corpus is the largest by far) alone on its head, lift11 -- the owner's
# interactive machine -- the lightest pair, two block-key cases on each of
# the other three.  Its OBLIGATIONS run on every lift in LIFTS, with
# workers-per-host slots per lift (default 4), and each start waits until
# that lift has the case's obligation_memory_mb to spare beyond what every
# campaign's recent starts there will still claim (run_engine.sh,
# campaign_await_host_memory) -- the slots make the pool wide, the gate
# keeps each lift's memory safe.
#
# CASES narrows the round to some of its cases, each still on its own head.
# Outputs: $GC_OUT/accept-<round>-<case without hdfs->/, launcher logs
# $GC_OUT/launch-<round>-<case without hdfs->.log.  One campaign is stopped
# with tools/rounds/stop-run.sh <round>-<case without hdfs->: a campaign is
# many process groups on five lifts, so no one group id stops it.  A round's
# directories are written once: a name already used is refused.
set -euo pipefail

snapshot=${1:?usage: launch-round.sh <snapshot> <round> [workers-per-host]}
round=${2:?usage: launch-round.sh <snapshot> <round> [workers-per-host]}
workers=${3:-4}
out=${GC_OUT:-/u/vnr3ne/gc-out}
LIFTS="lift11 lift12 lift13 lift14 lift15"

# head host, then the cases it heads.
placement=(
  "lift11 hdfs-17960 hdfs-17967-pathC hdfs-token-key"
  "lift12 hdfs-11741"
  "lift13 hdfs-17899-bug1 hdfs-17899-bug2"
  "lift14 hdfs-17899-bug3 hdfs-17897"
  "lift15 hdfs-17967-pathA hdfs-17967-pathB"
)

[[ -s "${snapshot}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar" ]] \
  || { echo "no built jar in the snapshot: ${snapshot}" >&2; exit 2; }
[[ "${workers}" =~ ^[1-9][0-9]*$ ]] \
  || { echo "workers-per-host must be a positive integer: ${workers}" >&2; exit 2; }
wanted=" ${CASES:-} "

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
[[ ${#launches[@]} -gt 0 ]] || { echo "no case of the round matches CASES='${CASES:-}'" >&2; exit 2; }

mkdir -p "${out}"
for launch in "${launches[@]}"; do
  read -r head case_id suffix <<<"${launch}"
  command="setsid nohup env CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' \
CAUSYNTH_CONCOLIC_JOBS=${workers} GC_OUT=${out} \
bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} ${case_id} ${suffix} \
> ${out}/launch-${suffix}.log 2>&1 < /dev/null &"
  if [[ "${head}" == "$(hostname -s)" ]]; then
    bash -c "${command}"
  else
    ssh -n -o BatchMode=yes -o ConnectTimeout=20 "${head}" "${command}"
  fi
  echo "$(date +%T) LAUNCHED ${case_id} head=${head} workers=${workers}/host on ${LIFTS} -> ${out}/accept-${suffix}"
done
