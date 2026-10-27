#!/usr/bin/env bash
set -euo pipefail

snapshot=${1:?usage: launch-round.sh <snapshot> <round>}
round=${2:?usage: launch-round.sh <snapshot> <round>}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../../run_engine.sh
source "${here}/../../run_engine.sh"
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
out=${GC_OUT}
vm=${CAUSYNTH_CUSTOM_JDK_HOME:?launch-round.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}
owner_host=${GC_CONTROL_HOST}
round_cases=(hdfs-11741 hdfs-17960 hdfs-17967-pathA hdfs-17967-pathB
  hdfs-17967-pathC hdfs-17899-bug1 hdfs-17899-bug2 hdfs-17899-bug3
  hdfs-17897 hdfs-bugs-slowdisk-zero)
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
passed=
for name in CAUSYNTH_CAMPAIGN_STOP_AFTER CASE_TIMEOUT_SECONDS PRUNE; do
  [[ -z "${!name+x}" ]] || passed+="${name}=$(printf '%q' "${!name}") "
done
for launch in "${launches[@]}"; do
  read -r case_id head <<<"${launch}"
  if [[ -n "${DRY:-}" ]]; then
    echo "${case_id} head=${head}"
    continue
  fi
  suffix="${round}-${case_id#hdfs-}"
  command="setsid nohup env CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' $(gc_env_words)\
CAUSYNTH_CUSTOM_JDK_HOME=${vm} ${passed}\
bash ${snapshot}/tools/rounds/launch-run.sh ${snapshot} ${case_id} ${suffix} \
> ${out}/launch-${suffix}.log 2>&1 < /dev/null &"
  if campaign_host_is_local "${head}"; then
    bash -c "${command}"
  else
    ssh -n -o BatchMode=yes -o ConnectTimeout=20 "${head}" "${command}"
  fi
  echo "$(date +%T) LAUNCHED ${case_id} head=${head} on ${LIFTS} -> ${out}/accept-${suffix}"
done
