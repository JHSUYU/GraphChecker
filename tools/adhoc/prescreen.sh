#!/usr/bin/env bash
# prescreen.sh <adhoc-experiment-dir> <jobs-file> [slots-per-host]
#
# One recording per row of <jobs-file> (cover.py's prescreen-jobs.tsv:
# "<batch><TAB><workload><TAB><bound-seconds><TAB><check> ...").  The row
# becomes a batch case B<n> of the experiment (batch.sh).  The batch's `record`
# (run_engine.sh) runs on the lifts (fanout.sh), charged the case's engine
# heap, at most <slots-per-host> (default 4) at a time on each, its workload
# bounded by the row's seconds.  <key> is this checkout's build key of the
# experiment (buildkey.sh); each check's static slice must be under
# $GC_OUT/static/<key>/<check>/ (slice.sh, the same build).  The row's
# recording is $GC_OUT/prescreen/<key>/<batch>/, whose
# runtime/record-summary.json cover.py `cases` reads: one that is there
# already is the same build's recording of the same batch and is kept.  One
# jobs file is one fanout, $GC_OUT/prescreen/<key>/runs-<digest of the
# file>/ (jobs.txt, logs/<n>.log): started again with the same file, it
# resumes, and runs a failed job again.
set -uo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
jobs_file=${2:?prescreen jobs file}
slots=${3:-4}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
checkout=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${checkout}/tools/lib/gc-env.sh"
key=$(bash "${here}/buildkey.sh" "${experiment}") || exit 2
static=${GC_OUT}/static/${key}
root=${GC_OUT}/prescreen/${key}
[[ -s "${static}/key.json" ]] || {
  echo "no static slices of build ${key}: run slice.sh first (${static})" >&2
  exit 2
}
echo "pre-screen of build ${key}: ${root}" >&2
run=${root}/runs-$(sha256sum <"${jobs_file}" | cut -c1-12)
mkdir -p "${run}"
jobs=${run}/jobs.txt
: > "${jobs}"
need=""
while IFS=$'\t' read -r dir workload bound checks; do
  [[ -n "${workload}" ]] || continue
  # shellcheck disable=SC2086 # the checks are words
  batch=$(bash "${here}/batch.sh" "${experiment}" "${workload}" ${checks})
  if [[ -z "${need}" ]]; then
    need=$(CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
      "${checkout}/experiments/lib/run.sh" "${experiment}" "${batch}" config \
      | sed -n 's/^engine_memory_mb=//p')
    need=${need:-8192}
  fi
  out=${root}/${dir}
  printf 'NEED_MB=%s [[ -s %s/runtime/record-summary.json ]] || { rm -rf -- %s && CAUSYNTH_STATIC_ROOT=%s CAUSYNTH_OUTPUT_DIR=%s CAUSYNTH_RECORD_TIMEOUT_S=%s bash experiments/lib/run.sh %s %s record; }\n' \
    "${need}" "${out}" "${out}" "${static}" "${out}" "${bound}" \
    "${experiment}" "${batch}" >>"${jobs}"
done <"${jobs_file}"
# A job that failed (a lift ran out of memory, the record command died)
# runs again; one that finished is kept.
for status in "${run}/logs"/*.exit; do
  [[ ! -e "${status}" || "$(cat "${status}")" == 0 ]] || rm -f -- "${status}"
done
exec bash "${here}/fanout.sh" "${jobs}" "${run}/logs" "${slots}"
