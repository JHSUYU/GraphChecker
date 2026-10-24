#!/usr/bin/env bash
set -uo pipefail
jobs_file=${1:?jobs file}
log_dir=${2:?log dir}
slots=${3:-8}
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
# shellcheck source=../../run_engine.sh
source "${checkout}/run_engine.sh"
set +e
read -r -a hosts <<<"${LIFTS}"
mkdir -p "${log_dir}"
mapfile -t commands < <(grep -v '^\s*$' "${jobs_file}")
declare -A running=() pid_host=() pid_job=() pid_charge=() started=()
for host in "${hosts[@]}"; do running[$host]=0; done
next=0
reap() {
  local pid status
  for pid in "${!pid_host[@]}"; do
    if ! kill -0 "${pid}" 2>/dev/null; then
      wait "${pid}"; status=$?
      printf '%s\n' "${status}" >"${log_dir}/${pid_job[$pid]}.exit"
      [[ -z "${pid_charge[$pid]}" ]] \
        || campaign_host_release "${pid_host[$pid]}" "${pid_charge[$pid]}"
      echo "${pid_job[$pid]} ${pid_host[$pid]} exit=${status} $(( $(date +%s) - started[$pid] ))s"
      running[${pid_host[$pid]}]=$(( running[${pid_host[$pid]}] - 1 ))
      unset "pid_host[$pid]" "pid_job[$pid]" "pid_charge[$pid]" "started[$pid]"
    fi
  done
}
hold_job=""
release_hold() {
  [[ -z "${campaign_head_hold}" ]] || rm -f -- "${campaign_head_hold}"
  campaign_head_hold=""; hold_job=""
}
trap release_hold EXIT
hold_room() {
  local need=$1 host room best="" best_room="" dir
  if [[ -n "${campaign_head_hold}" && "${hold_job}" == "${next}" ]]; then
    touch -- "${campaign_head_hold}"
    return 0
  fi
  release_hold
  for host in "${hosts[@]}"; do
    (( running[$host] < slots )) || continue
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")/heads"
    ! compgen -G "${dir}/fanout.*.hold" >/dev/null || continue
    room=$(campaign_host_room "${host}") || continue
    [[ -z "${best_room}" ]] || (( room > best_room )) || continue
    best=${host}; best_room=${room}
  done
  [[ -n "${best}" ]] || return 0
  dir="${campaign_host_gate_root}/$(campaign_host_key "${best}")/heads"
  mkdir -p "${dir}"
  campaign_head_hold="${dir}/fanout.$(hostname -s).$$.$(date +%s).hold"
  printf '%s\n' "${need}" >"${campaign_head_hold}"
  hold_job=${next}
  local first
  first=$(compgen -G "${dir}/fanout.*.hold" | LC_ALL=C sort | head -n 1)
  [[ "${first}" == "${campaign_head_hold}" ]] || release_hold
}
job_need() {
  local need=${JOB_MEMORY_MB:-4000}
  [[ ! "$1" =~ ^(NEED|ADMIT)_MB=([0-9]+)[[:space:]] ]] \
    || need=${BASH_REMATCH[2]}
  printf '%s\n' "${need}"
}
skip_returned() {
  while (( next < ${#commands[@]} )) && [[ -e "${log_dir}/${next}.exit" ]]; do
    next=$(( next + 1 ))
  done
}
skip_returned
while (( next < ${#commands[@]} )) || (( ${#pid_host[@]} > 0 )); do
  reap
  launched=0
  for host in "${hosts[@]}"; do
    while (( next < ${#commands[@]} && running[$host] < slots )); do
      command=${commands[$next]}
      need=${JOB_MEMORY_MB:-4000}
      admit=0
      if [[ "${command}" =~ ^(NEED|ADMIT)_MB=([0-9]+)[[:space:]]+(.*)$ ]]; then
        [[ "${BASH_REMATCH[1]}" == NEED ]] || admit=1
        need=${BASH_REMATCH[2]}
        command=${BASH_REMATCH[3]}
      fi
      campaign_host_try_start "${host}" "${need}" \
        "${campaign_fanout_job_cores}" || break
      charge=${campaign_host_charge_id}
      if (( admit )); then
        campaign_host_release "${host}" "${charge}"
        charge=""
      fi
      if campaign_host_is_local "${host}"; then
        (cd "${checkout}" && exec bash -c "${command}") \
          > "${log_dir}/${next}.log" 2>&1 < /dev/null &
      else
        ssh -o BatchMode=yes "${host}" "cd ${checkout} && ${command}" \
          > "${log_dir}/${next}.log" 2>&1 < /dev/null &
      fi
      pid_host[$!]=${host}; pid_job[$!]=${next}
      pid_charge[$!]=${charge}; started[$!]=$(date +%s)
      running[$host]=$(( running[$host] + 1 ))
      next=$(( next + 1 ))
      launched=1
      skip_returned
    done
  done
  if (( launched )); then
    release_hold
  elif (( next < ${#commands[@]} )); then
    hold_room "$(job_need "${commands[$next]}")"
  fi
  sleep "${campaign_host_poll_s}"
done
