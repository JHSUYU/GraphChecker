#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../../tools/lib/gc-env.sh
source "${graphchecker}/tools/lib/gc-env.sh"
# shellcheck source=../lib/case-id.sh
source "${graphchecker}/experiments/lib/case-id.sh"
fork=${SOLR_FORK:-https://github.com/JHSUYU/solr.git}

declare -A workloads=()
while IFS=$'\t' read -r id _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  read -r dir arg <<<"$(case_dir_of "${graphchecker}" "${id}")"
  [[ "${arg}" != - ]] || arg=""
  read -r repo seed spec < <(bash -c 'source "$1" "$2" "$3" >/dev/null && echo "${repo} ${solr_seed} ${test_class}#${test_method}"' \
    _ "${graphchecker}/experiments/lib/case-env.sh" "${dir}" "${arg}")
  key="$(basename "${repo}") ${seed}"
  [[ " ${workloads[${key}]:-} " == *" ${spec} "* ]] || workloads[${key}]+=" ${spec}"
done < <(cat "${here}"/solr-*cases.tsv)

names=("$@")
((${#names[@]} > 0)) || mapfile -t names < <(awk -F'\t' '$1 !~ /^#/ && NF {print $1}' "${here}/trees.tsv")
for name in "${names[@]}"; do
  branch=$(awk -F'\t' -v n="${name}" '$1 == n {print $2}' "${here}/trees.tsv")
  [[ -n "${branch}" ]] || { echo "${name}: not in trees.tsv" >&2; exit 2; }
  tree=${GC_TREES}/${name}
  if [[ ! -d "${tree}/.git" && ! -f "${tree}/.git" ]]; then
    mkdir -p "${GC_TREES}"
    git clone -q --branch "${branch}" --single-branch "${fork}" "${tree}"
  fi
  echo "== ${name}: ${branch} at $(git -C "${tree}" rev-parse --short HEAD), $(date +%T) on $(hostname)"
  built=0
  for key in "${!workloads[@]}"; do
    [[ "${key%% *}" == "${name}" ]] || continue
    # shellcheck disable=SC2086 # the specs are one word each
    SKIP_TREE_BUILD=${built} bash "${here}/build.sh" "${tree}" "${key#* }" ${workloads[${key}]}
    built=1
  done
  ((built)) || bash "${here}/build.sh" "${tree}" -
  echo "== ${name}: ready $(date +%T)"
done
