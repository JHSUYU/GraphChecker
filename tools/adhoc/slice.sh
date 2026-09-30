#!/usr/bin/env bash
# slice.sh <adhoc-experiment-dir> <key> <cases-file> [slots-per-host]
#
# The engine's own static slice of every check <cases-file> names, one
# "<check>.<workload>" per line (select.py `declare` prints them): SEED's
# static half (run_engine.sh `slice`, through experiments/lib/run.sh) into
# $GC_OUT/static/<key>/<check>/, then score.py, which writes score.json
# there -- what select.py `rank` reads.  The workload only states the
# module's classpath and the case's scope, so any workload that reaches the
# check does.  <key> names the build the slices belong to: a check whose
# score.json is there already is not sliced again.
#
# The jobs run on the lifts (fanout.sh), each charged the case's engine heap
# (engine_memory_mb, else the launcher's 8192) and at most <slots-per-host>
# at a time on each (default 6); job n logs to
# $GC_OUT/static/<key>/slice-logs/<n>.log.  Started again with the same
# cases-file, it resumes.
set -uo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
key=${2:?key}
cases_file=${3:?cases file}
slots=${4:-6}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
checkout=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${checkout}/tools/lib/gc-env.sh"
root=${GC_OUT}/static/${key}
mkdir -p "${root}"
mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
(( ${#cases[@]} > 0 )) || { echo "no case in ${cases_file}" >&2; exit 2; }
need=$(CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
  "${checkout}/experiments/lib/run.sh" "${experiment}" "${cases[0]}" config \
  | sed -n 's/^engine_memory_mb=//p')
jobs=${root}/slice-jobs.txt
: > "${jobs}"
for case_id in "${cases[@]}"; do
  out=${root}/${case_id%%.*}
  printf 'NEED_MB=%s [[ -s %s/score.json ]] || { CAUSYNTH_OUTPUT_DIR=%s bash experiments/lib/run.sh %s %s slice && python3 tools/adhoc/score.py %s; }\n' \
    "${need:-8192}" "${out}" "${out}" "${experiment}" "${case_id}" "${out}" \
    >> "${jobs}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${root}/slice-logs" "${slots}"
