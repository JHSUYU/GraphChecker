#!/usr/bin/env bash
# slice.sh <adhoc-experiment-dir> <cases-file> [slots-per-host]
#
# The engine's own static slice of every check <cases-file> names, one
# "<check>.<workload>" per line (select.py `declare` prints them): SEED's
# static half (run_engine.sh `slice`, through experiments/lib/run.sh) into
# $GC_OUT/static/<key>/<check>/, then score.py, which writes score.json
# there -- what select.py `rank` reads.  The workload only states the
# module's classpath and the case's scope, so any workload that reaches the
# check does.  <key> is this checkout's build key of the experiment
# (buildkey.sh: the jar, the tree's commit, the scope declarations), printed
# on stderr and kept with what it digests as <key>/key.json: a check whose
# score.json is there already belongs to the same build and is not sliced
# again, whichever run sliced it.
#
# The jobs run on the lifts (fanout.sh), each charged the case's engine heap
# (engine_memory_mb, else the launcher's 8192) and at most <slots-per-host>
# at a time on each (default 6).  One cases file is one fanout: its jobs and
# logs are $GC_OUT/static/<key>/slices-<digest of the file>/ (jobs.txt,
# logs/<n>.log), so started again with the same file it resumes, and another
# file never inherits its finished jobs; a failed job runs again.
set -uo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
cases_file=${2:?cases file}
slots=${3:-6}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
checkout=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${checkout}/tools/lib/gc-env.sh"
key=$(bash "${here}/buildkey.sh" "${experiment}") || exit 2
root=${GC_OUT}/static/${key}
mkdir -p "${root}"
bash "${here}/buildkey.sh" "${experiment}" --inputs >"${root}/key.json" || exit 2
echo "slices of build ${key}: ${root}" >&2
mapfile -t cases < <(grep -v '^\s*\(#\|$\)' "${cases_file}")
(( ${#cases[@]} > 0 )) || { echo "no case in ${cases_file}" >&2; exit 2; }
need=$(CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
  "${checkout}/experiments/lib/run.sh" "${experiment}" "${cases[0]}" config \
  | sed -n 's/^engine_memory_mb=//p')
run=${root}/slices-$(printf '%s\n' "${cases[@]}" | sha256sum | cut -c1-12)
mkdir -p "${run}"
jobs=${run}/jobs.txt
: > "${jobs}"
for case_id in "${cases[@]}"; do
  out=${root}/${case_id%%.*}
  printf 'NEED_MB=%s [[ -s %s/score.json ]] || { CAUSYNTH_OUTPUT_DIR=%s bash experiments/lib/run.sh %s %s slice && python3 tools/adhoc/score.py %s; }\n' \
    "${need:-8192}" "${out}" "${out}" "${experiment}" "${case_id}" "${out}" \
    >> "${jobs}"
done
# A job that failed (a lift ran out of memory, a slice refused) runs
# again; one that finished is kept.
for status in "${run}/logs"/*.exit; do
  [[ ! -e "${status}" || "$(cat "${status}")" == 0 ]] || rm -f -- "${status}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${run}/logs" "${slots}"
