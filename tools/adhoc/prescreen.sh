#!/usr/bin/env bash
# prescreen.sh <adhoc-experiment-dir> <key> <jobs-file> [slots-per-host]
#
# One recording per row of <jobs-file> (cover.py's prescreen-jobs.tsv:
# "<workload><TAB><bound-seconds><TAB><check> ...").  The row becomes a batch
# of the experiment: a row "B<n><TAB><workload><TAB><check> ..." of its
# batches.tsv, and its target spec targets/B<n>.yaml, each check's target
# line named by the check (a batch already there with the same workload and
# checks is the row's).  The batch's `record` (run_engine.sh) runs on the
# lifts (fanout.sh), charged the case's engine heap, at most <slots-per-host>
# (default 4) at a time on each, its workload bounded by the row's seconds.
# Each check's static slice must be under $GC_OUT/static/<key>/<check>/
# (slice.sh, the same build); batch B<n> writes $GC_OUT/prescreen/<key>/B<n>/,
# whose runtime/record-summary.json cover.py `cases` reads.  Job n logs to
# $GC_OUT/prescreen/<key>/logs/<n>.log; started again with the same jobs file,
# it resumes.
set -uo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
key=${2:?key}
jobs_file=${3:?prescreen jobs file}
slots=${4:-4}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
checkout=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${checkout}/tools/lib/gc-env.sh"
static=${GC_OUT}/static/${key}
root=${GC_OUT}/prescreen/${key}
batches=${experiment}/batches.tsv
mkdir -p "${root}"
touch "${batches}"
jobs=${root}/jobs.txt
: > "${jobs}"
need=""
while IFS=$'\t' read -r workload bound checks; do
  [[ -n "${workload}" ]] || continue
  batch=$(awk -F'\t' -v w="${workload}" -v c="${checks}" \
    '$2 == w && $3 == c {print $1; exit}' "${batches}")
  if [[ -z "${batch}" ]]; then
    batch=B$(awk -F'\t' '{n = substr($1, 2) + 0; if (n > max) max = n}
      END {print max + 1}' "${batches}")
    printf '%s\t%s\t%s\n' "${batch}" "${workload}" "${checks}" >>"${batches}"
    for check in ${checks}; do
      awk -v c="${check}" '$1 == "exception_target:" {$2 = c; print}' \
        "${experiment}/targets/${check}.yaml"
    done >"${experiment}/targets/${batch}.yaml"
  fi
  if [[ -z "${need}" ]]; then
    need=$(CAUSYNTH_CLASSPATH_OVERRIDE=unread bash \
      "${checkout}/experiments/lib/run.sh" "${experiment}" "${batch}" config \
      | sed -n 's/^engine_memory_mb=//p')
    need=${need:-8192}
  fi
  out=${root}/${batch}
  printf 'NEED_MB=%s rm -rf -- %s && CAUSYNTH_STATIC_ROOT=%s CAUSYNTH_OUTPUT_DIR=%s CAUSYNTH_RECORD_TIMEOUT_S=%s bash experiments/lib/run.sh %s %s record\n' \
    "${need}" "${out}" "${static}" "${out}" "${bound}" \
    "${experiment}" "${batch}" >>"${jobs}"
done <"${jobs_file}"
exec bash "${here}/fanout.sh" "${jobs}" "${root}/logs" "${slots}"
