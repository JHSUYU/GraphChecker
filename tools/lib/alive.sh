#!/usr/bin/env bash
# alive.sh <path>... -- which of the paths a process of this user still names
# on some lift (LIFTS, gc-env.sh): in its command line (as "<path>/..."), as
# its working directory, or as OUT in its environment (accept.sh's harness
# names its run so).  Prints "alive <path>" once per path some lift runs, and
# "silent <host>" for a lift that did not answer, which says nothing either
# way.  Every lift is asked at once.  The scan's own shell names every path
# (without the trailing slash) and is never counted.
set -uo pipefail
# shellcheck source=gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/gc-env.sh"
scan='
for pid in $(pgrep -u "$(id -un)"); do
  [[ ${pid} == $$ ]] && continue
  args=$(tr "\0" " " <"/proc/${pid}/cmdline" 2>/dev/null)
  cwd=$(readlink "/proc/${pid}/cwd" 2>/dev/null)
  env=$(tr "\0" "\n" <"/proc/${pid}/environ" 2>/dev/null | grep -m 1 "^OUT=")
  for dir in "$@"; do
    if [[ ${args} == *"${dir}/"* || ${cwd}/ == "${dir}/"* \
        || ${env} == "OUT=${dir}" ]]; then
      echo "alive ${dir}"
    fi
  done
done
'
answers=$(mktemp -d)
trap 'rm -rf -- "${answers}"' EXIT
for host in ${LIFTS}; do
  { timeout 120 ssh -n -o BatchMode=yes -o ConnectTimeout=10 "${host}" \
      "bash -c $(printf %q "${scan}") scan $(printf '%q ' "$@")" \
      >"${answers}/${host}" 2>/dev/null \
    || echo "silent ${host}" >"${answers}/${host}"; } &
done
wait
cat "${answers}"/* | sort -u
