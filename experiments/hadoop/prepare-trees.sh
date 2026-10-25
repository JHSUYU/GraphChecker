#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../../tools/lib/gc-env.sh
source "${graphchecker}/tools/lib/gc-env.sh"
# shellcheck source=../lib/case-id.sh
source "${graphchecker}/experiments/lib/case-id.sh"
fork=${HADOOP_FORK:-https://github.com/JHSUYU/hadoop.git}

declare -A workloads=()
while IFS=$'\t' read -r id _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  read -r dir arg <<<"$(case_dir_of "${graphchecker}" "${id}")"
  [[ "${arg}" != - ]] || arg=""
  read -r repo spec < <(bash -c 'source "$1" "$2" "$3" >/dev/null && echo "${repo} ${test_class}#${test_method}"' \
    _ "${graphchecker}/experiments/lib/case-env.sh" "${dir}" "${arg}")
  workloads[$(basename "${repo}")]+=" ${spec}"
done < <(cat "${here}"/hdfs-*cases.tsv)

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
  echo "== ${name}: ${branch} at $(git -C "${tree}" rev-parse --short HEAD), Maven repository ${GC_M2}/${name}, $(date +%T) on $(hostname)"
  # shellcheck disable=SC2086 # the specs are one word each
  MAVEN_REPO_LOCAL=${GC_M2}/${name} bash "${here}/build.sh" "${tree}" ${workloads[${name}]:-}
  echo "== ${name}: ready $(date +%T)"
done
