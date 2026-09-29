#!/usr/bin/env bash
# fanout.sh <jobs-file> <log-dir> [slots-per-host]
#
# Runs every line of <jobs-file> -- one shell command, run from the
# GraphChecker checkout -- on the ten lifts, at most <slots-per-host> at a
# time on each (default 8).  A job starts on a host only when the host's
# MemAvailable covers JOB_MEMORY_MB (default 4000) plus RESERVE_MB (3072), so
# no lift is ever run out of memory.  Job n writes <log-dir>/<n>.log; a line
# "<n> <host> exit=<status> <seconds>s" per finished job goes to stdout.
set -uo pipefail
jobs_file=${1:?jobs file}
log_dir=${2:?log dir}
slots=${3:-8}
hosts=(${FANOUT_HOSTS:-lift06 lift07 lift08 lift09 lift10 lift11 lift12 lift13 lift14 lift15})
need=$(( ${JOB_MEMORY_MB:-4000} + ${RESERVE_MB:-3072} ))
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
mkdir -p "${log_dir}"
mapfile -t commands < <(grep -v '^\s*$' "${jobs_file}")
declare -A running pid_host pid_job started
for host in "${hosts[@]}"; do running[$host]=0; done
next=0
available_mb() {
  ssh -o BatchMode=yes -o ConnectTimeout=5 "$1" \
    "awk '/MemAvailable/ {print int(\$2/1024)}' /proc/meminfo" 2>/dev/null || echo 0
}
reap() {
  local pid status
  for pid in "${!pid_host[@]}"; do
    if ! kill -0 "${pid}" 2>/dev/null; then
      wait "${pid}"; status=$?
      echo "${pid_job[$pid]} ${pid_host[$pid]} exit=${status} $(( $(date +%s) - started[$pid] ))s"
      running[${pid_host[$pid]}]=$(( running[${pid_host[$pid]}] - 1 ))
      unset "pid_host[$pid]" "pid_job[$pid]" "started[$pid]"
    fi
  done
}
while (( next < ${#commands[@]} )) || (( ${#pid_host[@]} > 0 )); do
  reap
  launched=0
  for host in "${hosts[@]}"; do
    (( next < ${#commands[@]} )) || break
    (( running[$host] < slots )) || continue
    (( $(available_mb "${host}") >= need )) || continue
    n=${next}; next=$(( next + 1 ))
    ssh -o BatchMode=yes "${host}" "cd ${checkout} && ${commands[$n]}" \
      > "${log_dir}/${n}.log" 2>&1 < /dev/null &
    pid_host[$!]=${host}; pid_job[$!]=${n}; started[$!]=$(date +%s)
    running[$host]=$(( running[$host] + 1 )); launched=1
    # A JVM takes tens of seconds to show its memory: one start per host per pass.
  done
  (( launched )) || sleep 10
  (( launched )) && sleep 3
done
