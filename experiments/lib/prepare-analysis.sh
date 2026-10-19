#!/usr/bin/env bash
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?missing case directory}" "${2-}"
mkdir -p "${analysis}"
find "${analysis}" -type f -delete

copy() {
  local root=$1 path=$2 exact=$3 file found=false base
  [[ -d "${root}" ]] || {
    echo "missing compiled class root: ${root}" >&2
    return 2
  }
  base=$(basename "${path}")
  while IFS= read -r file; do
    found=true
    mkdir -p "${analysis}/$(dirname "${file}")"
    cp "${root}/${file}" "${analysis}/${file}"
  done < <(cd "${root}" && if [[ "${exact}" == true ]]; then
      find "$(dirname "${path}")" -maxdepth 1 -type f \
        \( -name "${base}.class" -o -name "${base}\$*.class" \)
    else
      find "$(dirname "${path}")" -maxdepth 1 -type f -name "${base}*.class"
    fi | sort)
  [[ "${found}" == true ]] || {
    echo "missing compiled class ($([[ "${exact}" == true ]] && echo exact \
      || echo family)): ${path}" >&2
    return 2
  }
}

(( ${#scope[@]} > 0 )) || {
  echo "${case_name}/case.sh declares no analysis scope for '${case_id}'" >&2
  exit 2
}
for entry in "${scope[@]}" "${system_scope[@]}"; do
  rootname=${entry%%:*}
  path=${entry#*:}
  exact=false
  if [[ "${rootname}" == *= ]]; then
    rootname=${rootname%=}
    exact=true
  fi
  copy "$(system_root "${rootname}")" "${path}" "${exact}"
done
