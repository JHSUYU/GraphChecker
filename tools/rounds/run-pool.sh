#!/usr/bin/env bash
set -uo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
usage="usage: run-pool.sh <round> <cases.tsv> <branch>=<checkout>... [case...]"
round=${1:?${usage}}
table=${2:?${usage}}
[[ -f "${table}" ]] || { echo "run-pool.sh: no case table ${table}" >&2; exit 2; }
shift 2
# shellcheck source=../../run_engine.sh
source "${here}/../../run_engine.sh"
# shellcheck source=../lib/heads.sh
source "${here}/../lib/heads.sh"
set +e
declare -A checkout=()
cases=()
for arg in "$@"; do
  if [[ "${arg}" == *=* ]]; then
    checkout[${arg%%=*}]=$(cd "${arg#*=}" && pwd -P)
  else
    cases+=("${arg}")
  fi
done
vm=${CAUSYNTH_CUSTOM_JDK_HOME:?run-pool.sh: name the concolic VM image as CAUSYNTH_CUSTOM_JDK_HOME}
read -r -a hosts <<<"${LIFTS}"
pool_gap_s=${POOL_GAP_S:-30}
pool_poll_s=${POOL_POLL_S:-30}
pool_max=${POOL_MAX:-0}
log=${GC_OUT}/series-${round}.log
load_log=${GC_OUT}/pool-${round}.tsv
mkdir -p "${GC_OUT}"

declare -A budget=() snap=() expected=() head_of=() started_at=()
order=()
while IFS=$'\t' read -r id branch seconds _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  ((${#cases[@]} == 0)) || [[ " ${cases[*]} " == *" ${id} "* ]] || continue
  [[ -n "${checkout[${branch}]:-}" ]] \
    || { echo "run-pool.sh: ${id}: no checkout named for ${branch}" >&2; exit 2; }
  budget[${id}]=${seconds}
  snap[${id}]=${checkout[${branch}]}
  expected[${id}]=${seconds}
  order+=("${id}")
done <"${table}"
if [[ -n "${POOL_EXPECTED:-}" ]]; then
  while IFS=$'\t' read -r id seconds _; do
    [[ -n "${budget[${id}]:-}" && "${seconds}" =~ ^[0-9]+$ ]] || continue
    expected[${id}]=${seconds}
  done <"${POOL_EXPECTED}"
fi
mapfile -t pending < <(for at in "${!order[@]}"; do
    printf '%s %s %s\n' "${expected[${order[at]}]}" "${at}" "${order[at]}"
  done | sort -k1,1nr -k2,2n | awk '{print $3}')

suffix_of() { printf '%s-%s\n' "${round}" "${1#*-}"; }
rows_of() { wc -l 2>/dev/null <"${GC_OUT}/accept-$(suffix_of "$1")/summary.tsv" || echo 0; }

host_load() {
  local load
  load=$(campaign_host_read "$1" cat /proc/loadavg | awk 'NF >= 3 {print int($1 * 100)}' | tail -n 1)
  printf '%s\n' "${load:-0}"
}

declare -A free_of=() room_of=()
cluster_free=0
read_cluster() {
  local host room cores load total line=""
  cluster_free=0
  for host in "${hosts[@]}"; do
    read -r room cores <<<"$(campaign_host_room "${host}")" || continue
    [[ "${room}" =~ ^-?[0-9]+$ && "${cores}" =~ ^-?[0-9]+$ ]] || continue
    total=$(campaign_host_core_limit "${host}") || continue
    load=$(host_load "${host}")
    (( total - load >= cores )) || cores=$(( total - load ))
    (( cores >= 0 )) || cores=0
    free_of[${host}]=${cores}
    room_of[${host}]=${room}
    cluster_free=$(( cluster_free + cores ))
    line+="${host}:${load}:${cores}:${room} "
  done
  printf '%s\t%s\t%s\t%s\n' "${EPOCHSECONDS}" "${#head_of[@]}" "${cluster_free}" "${line% }" >>"${load_log}"
}

cluster_cores=0
for host in "${hosts[@]}"; do
  cores=$(campaign_host_core_limit "${host}") || continue
  cluster_cores=$(( cluster_cores + cores ))
done
pool_free_cores=${POOL_FREE_CORES:-$(( cluster_cores / 10 ))}

choose_head() {
  local need=$1 host best="" n
  local -A heads=()
  for host in "${hosts[@]}"; do heads[${host}]=0; done
  for host in "${head_of[@]}"; do heads[${host}]=$(( ${heads[${host}]:-0} + 1 )); done
  for host in "${hosts[@]}"; do
    [[ -n "${free_of[${host}]:-}" ]] || continue
    (( room_of[${host}] >= need )) || continue
    n=${heads[${host}]}
    if [[ -z "${best}" ]] || (( n < heads[${best}] )) \
        || { (( n == heads[${best}] )) && campaign_host_roomier "${free_of[${host}]}" \
               "${room_of[${host}]}" "${free_of[${best}]}" "${room_of[${best}]}"; }; then
      best=${host}
    fi
  done
  printf '%s\n' "${best}"
}

passed=
for name in CAUSYNTH_CAMPAIGN_STOP_AFTER PRUNE; do
  [[ -z "${!name+x}" ]] || passed+="${name}=$(printf '%q' "${!name}") "
done
start_case() {
  local id=$1 host=$2 suffix command
  suffix=$(suffix_of "${id}")
  command="cd ${snap[${id}]} && setsid nohup env CASE_TIMEOUT_SECONDS=${budget[${id}]} \
CAUSYNTH_CAMPAIGN_WORKER_HOSTS='${LIFTS}' $(gc_env_words)CAUSYNTH_CUSTOM_JDK_HOME=${vm} ${passed}\
bash ${snap[${id}]}/tools/rounds/launch-run.sh ${snap[${id}]} ${id} ${suffix} \
> ${GC_OUT}/launch-${suffix}.log 2>&1 < /dev/null &"
  if campaign_host_is_local "${host}"; then
    bash -c "${command}"
  else
    ssh -n -o BatchMode=yes -o ConnectTimeout=20 "${host}" "${command}"
  fi
  head_of[${id}]=${host}
  started_at[${id}]=${EPOCHSECONDS}
  echo "$(date +%F_%T) ${EPOCHSECONDS} START ${id} ${suffix} ${snap[${id}]} host=${host} free=${cluster_free}" >>"${log}"
}

head_alive() {
  local id=$1 pgid
  read -r pgid 2>/dev/null <"${GC_OUT}/accept-$(suffix_of "${id}")/pgid" || return 0
  campaign_host_read "${head_of[${id}]}" "kill -0 -${pgid} 2>/dev/null && echo alive" | grep -qx alive
}

reap() {
  local id rows age why
  for id in "${!head_of[@]}"; do
    rows=$(rows_of "${id}")
    why=""
    if (( rows < 2 )); then
      age=$(( EPOCHSECONDS - started_at[${id}] ))
      if (( age > budget[${id}] + 7200 )); then
        why=" (past its budget)"
      elif (( age >= 600 )) && ! head_alive "${id}"; then
        why=" (its head is gone)"
      else
        continue
      fi
    fi
    echo "$(date +%F_%T) ${EPOCHSECONDS} END ${id} $(suffix_of "${id}") rows=${rows}${why}" >>"${log}"
    unset "head_of[${id}]"
  done
}

last_start=0
echo "$(date +%F_%T) ${EPOCHSECONDS} POOL ${#pending[@]} case(s) on ${LIFTS}: ${cluster_cores} cores, a start once ${pool_free_cores} are free, at least ${pool_gap_s} s apart" >>"${log}"
while (( ${#pending[@]} > 0 || ${#head_of[@]} > 0 )); do
  reap
  read_cluster
  if (( ${#pending[@]} > 0 )) && [[ ! -e "${GC_OUT}/series-${round}.STOP" ]] \
      && (( EPOCHSECONDS - last_start >= pool_gap_s && cluster_free >= pool_free_cores )) \
      && (( pool_max == 0 || ${#head_of[@]} < pool_max )); then
    id=${pending[0]}
    if (( $(rows_of "${id}") >= 2 )); then
      pending=("${pending[@]:1}")
      continue
    fi
    host=$(choose_head "$(case_engine_heap_mb "$(case_config "${snap[${id}]}" "${id}")")")
    if [[ -n "${host}" ]]; then
      start_case "${id}" "${host}"
      pending=("${pending[@]:1}")
      last_start=${EPOCHSECONDS}
    fi
  fi
  [[ ! -e "${GC_OUT}/series-${round}.STOP" ]] || (( ${#head_of[@]} > 0 )) || break
  sleep "${pool_poll_s}"
done
echo "$(date +%F_%T) ${EPOCHSECONDS} POOL done" >>"${log}"
