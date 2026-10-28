#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
out=${GC_OUT:-/bigtemp/vnr3ne/gc-out/hdfs-final}
order=${1:?usage: collect-results.sh <rounds, most final first, comma-separated> [cases.tsv]}
cases=${2:-${here}/../../experiments/hadoop/hdfs-cases.tsv}
IFS=, read -r -a rounds <<<"${order}"
printf 'case\trun\tclaim\tsmt\tclaim_json\n' >"${here}/index.tsv"
while IFS=$'\t' read -r id _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  for round in "${rounds[@]}"; do
    run=accept-${round}-${id#hdfs-}
    summary=${out}/${run}/summary.tsv
    [[ -f "${summary}" && $(wc -l <"${summary}") -ge 2 ]] || continue
    final=${out}/${run}/out/${id}/schedule/final
    claim=$(tail -1 "${summary}" | cut -f4)
    smt=-; json=-
    if [[ -s "${final}/candidate.smt2" ]]; then
      gzip -9 -c "${final}/candidate.smt2" >"${here}/${id}.smt2.gz"; smt=${id}.smt2.gz
    fi
    if [[ -s "${final}/claim.json" ]]; then
      cp "${final}/claim.json" "${here}/${id}.claim.json"; json=${id}.claim.json
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "${id}" "${run}" "${claim}" "${smt}" "${json}" >>"${here}/index.tsv"
    break
  done
done <"${cases}"
