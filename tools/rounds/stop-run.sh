#!/usr/bin/env bash
# stop-run.sh <round>-<case without hdfs-> ... -- stops acceptance runs
# everywhere they run.
#
#   tools/rounds/stop-run.sh v23-17899-bug1 v23-17967-pathC
#
# A run is not one process group: accept.sh's case runs under `timeout`, which
# takes a group of its own, and run_engine gives every replay and every
# remote worker its own group too.  So the run is named by what its processes
# share -- its output directory, $GC_OUT/accept-<suffix>: on the command line
# of everything below the harness, and as OUT in the environment of the
# harness itself (its group id is $OUT/pgid, a number that means something
# only on the head) -- and every group that has such a process, on every
# lift, is sent TERM, then KILL for whatever is still there after the grace.
set -euo pipefail

(( $# > 0 )) || { echo "usage: stop-run.sh <round>-<case> ..." >&2; exit 2; }
out=${GC_OUT:-/u/vnr3ne/gc-out}
LIFTS=${LIFTS:-"lift06 lift07 lift08 lift09 lift10 lift11 lift12 lift13 lift14 lift15"}
grace=${STOP_GRACE_S:-20}
dirs=()
for suffix in "$@"; do
  dirs+=("${out}/accept-${suffix}")
done

# signal_groups <host> <signal>: signals the run's groups on <host> and prints
# how many of its processes were there.
signal_groups() {
  ssh -o BatchMode=yes -o ConnectTimeout=20 "$1" bash -s -- "$2" "${dirs[@]}" <<'REMOTE'
signal=$1; shift
groups=(); count=0
while read -r pid group args; do
  for dir in "$@"; do
    if [[ "${args}" == *"${dir}/"* ]] \
        || { tr '\0' '\n' <"/proc/${pid}/environ"; } 2>/dev/null | grep -qx "OUT=${dir}"; then
      groups+=("${group}"); count=$((count + 1)); break
    fi
  done
done < <(ps -u "$(id -un)" -o pid=,pgid=,args= | grep -v -e "bash -s -- ")
for group in $(printf '%s\n' "${groups[@]}" | sort -u); do
  kill "-${signal}" -- "-${group}" 2>/dev/null
done
echo "${count}"
REMOTE
}

for host in ${LIFTS}; do
  echo "${host}: TERM to the groups of $(signal_groups "${host}" TERM) process(es)"
done
sleep "${grace}"
for host in ${LIFTS}; do
  echo "${host}: KILL to the groups of $(signal_groups "${host}" KILL) process(es) still there"
done
