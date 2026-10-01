#!/usr/bin/env bash
# batch.sh <adhoc-experiment-dir> <workload> <check>... -- the batch case of
# these checks on this workload, printed as its id B<n>.  A batch is a row
# "B<n><TAB><workload><TAB><check> ..." of the experiment's batches.tsv and
# its target spec targets/B<n>.yaml, each check's target line
# (targets/<check>.yaml) named by the check; a row already there with the
# same workload and checks is the batch, else one is appended.  The
# pre-screen's recordings (prescreen.sh) and the campaigns of a sweep
# (cover.py `cases`) are batches.
set -euo pipefail
experiment=$(cd "${1:?adhoc experiment dir}" && pwd -P)
workload=${2:?workload}
shift 2
(( $# > 0 )) || { echo "batch.sh: no check" >&2; exit 2; }
checks="$*"
batches=${experiment}/batches.tsv
touch "${batches}"
batch=$(awk -F'\t' -v w="${workload}" -v c="${checks}" \
  '$2 == w && $3 == c {print $1; exit}' "${batches}")
if [[ -z "${batch}" ]]; then
  batch=B$(awk -F'\t' '{n = substr($1, 2) + 0; if (n > max) max = n}
    END {print max + 1}' "${batches}")
  for check in "$@"; do
    awk -v c="${check}" '$1 == "exception_target:" {$2 = c; print}' \
      "${experiment}/targets/${check}.yaml"
  done >"${experiment}/targets/${batch}.yaml"
  printf '%s\t%s\t%s\n' "${batch}" "${workload}" "${checks}" >>"${batches}"
fi
echo "${batch}"
