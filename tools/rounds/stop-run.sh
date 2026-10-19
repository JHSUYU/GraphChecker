#!/usr/bin/env bash
set -euo pipefail

(( $# > 0 )) || { echo "usage: stop-run.sh <round>-<case> ..." >&2; exit 2; }
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
out=${GC_OUT}
grace=${STOP_GRACE_S:-20}
dirs=()
for suffix in "$@"; do
  dirs+=("${out}/accept-${suffix}")
done

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
