#!/usr/bin/env bash
# reproduce-again.sh <finished run dir> <case-id> <copy dir> -- REPRODUCE
# alone, again, over a finished campaign (PIPELINE §10b): the case's output
# directory of <finished run dir> (accept-<round>-<n>, out/<case-id>) copied
# into <copy dir> -- what REPRODUCE reads linked (the woven classes, the
# scope map, the recording's directory, the iteration), what it writes
# beside made fresh (final/ with the claim, manifest and confirmation EMIT
# published) -- then `run.sh <case> reproduce` from this checkout with the
# copy as its output directory, so the finished run is never written.
# Prints final/reproduce.json.  The case runs on the tree this checkout's
# case.sh names (a campaign made on another: OPERATIONS §5, edit it in a
# snapshot) with this checkout's jar, which must call the runtime the
# finished run's woven classes call.
set -euo pipefail
checkout=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)
# shellcheck source=../../experiments/lib/case-id.sh
source "${checkout}/experiments/lib/case-id.sh"
run=${1:?usage: reproduce-again.sh <finished run dir> <case-id> <copy dir>}
case_id=${2:?missing case id}
copy=${3:?missing copy dir}
source_dir=$(cd "${run}/out/${case_id}" && pwd -P)
[[ -s "${source_dir}/schedule/final/confirm.json" ]] \
  || { echo "no finished campaign of ${case_id} in ${run}" >&2; exit 2; }
[[ ! -e "${copy}" ]] || { echo "${copy} exists" >&2; exit 2; }
out=${copy}/out/${case_id}
mkdir -p "${out}/schedule/final"
for name in instrumented-classes static_scope_map.jsonl runtime; do
  ln -s "${source_dir}/${name}" "${out}/${name}"
done
ln -s "${source_dir}/schedule/iteration-0000" "${out}/schedule/iteration-0000"
cp "${source_dir}/schedule/stage_metrics.tsv" "${out}/schedule/"
for name in claim.json candidate_composition_manifest.json confirm.json; do
  cp "${source_dir}/schedule/final/${name}" "${out}/schedule/final/"
done
read -r dir arg <<<"$(case_dir_of "${checkout}" "${case_id}")"
[[ "${arg}" != - ]] || arg=""
CAUSYNTH_OUTPUT_DIR=${out} bash "${checkout}/experiments/lib/run.sh" \
  "${dir}" "${arg}" reproduce
