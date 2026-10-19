#!/usr/bin/env bash
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
[[ ! -d "${source_dir}/schedule/witness-confirm" ]] \
  || ln -s "${source_dir}/schedule/witness-confirm" \
    "${out}/schedule/witness-confirm"
[[ ! -d "${source_dir}/schedule/final/confirm" ]] \
  || ln -s "${source_dir}/schedule/final/confirm" \
    "${out}/schedule/final/confirm"
cp "${source_dir}/schedule/stage_metrics.tsv" "${out}/schedule/"
for name in claim.json candidate_composition_manifest.json confirm.json; do
  cp "${source_dir}/schedule/final/${name}" "${out}/schedule/final/"
done
read -r dir arg <<<"$(case_dir_of "${checkout}" "${case_id}")"
[[ "${arg}" != - ]] || arg=""
CAUSYNTH_OUTPUT_DIR=${out} bash "${checkout}/experiments/lib/run.sh" \
  "${dir}" "${arg}" reproduce
