#!/usr/bin/env bash
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
