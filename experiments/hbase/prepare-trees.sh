#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
source "${graphchecker}/tools/lib/gc-env.sh"
source "${graphchecker}/experiments/lib/case-id.sh"
fork=${HBASE_FORK:-https://github.com/JHSUYU/hbase.git}

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
  specs=()
  while IFS=$'\t' read -r id _; do
    [[ -n "${id}" && "${id}" != \#* ]] || continue
    read -r dir arg <<<"$(case_dir_of "${graphchecker}" "${id}")"
    [[ "${arg}" != - ]] || arg=""
    read -r repo spec < <(bash -c 'source "$1" "$2" "$3" >/dev/null && echo "${repo} $(hbase_spec)"' \
      _ "${graphchecker}/experiments/lib/case-env.sh" "${dir}" "${arg}")
    [[ "$(basename "${repo}")" == "${name}" ]] || continue
    [[ " ${specs[*]-} " == *" ${spec} "* ]] || specs+=("${spec}")
  done < <(cat "${here}"/hbase-*cases.tsv)
  bash "${here}/build.sh" "${tree}" "${specs[@]+"${specs[@]}"}"
  echo "== ${name}: ready $(date +%T)"
done
