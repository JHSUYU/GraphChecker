#!/usr/bin/env bash
# collect-results.sh <results dir> <cases.tsv> <rounds, most final first, comma-separated>: copies each case's final
# formula (gzip of schedule/final/candidate.smt2) and claim from its final run under GC_OUT into <results dir>, and
# names the run each came from in <results dir>/index.tsv (as results/hbase and results/hdfs).
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${here}/../lib/gc-env.sh"
dest=${1:?usage: collect-results.sh <results dir> <cases.tsv> <rounds>}
cases=${2:?usage: collect-results.sh <results dir> <cases.tsv> <rounds>}
IFS=, read -r -a rounds <<<"${3:?usage: collect-results.sh <results dir> <cases.tsv> <rounds>}"
mkdir -p "${dest}"
printf 'case\trun\tclaim\tsmt\tclaim_json\n' >"${dest}/index.tsv"
while IFS=$'\t' read -r id _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  for round in "${rounds[@]}"; do
    run=accept-${round}-${id#*-}
    summary=${GC_OUT}/${run}/summary.tsv
    [[ -f "${summary}" && $(wc -l <"${summary}") -ge 2 ]] || continue
    final=${GC_OUT}/${run}/out/${id}/schedule/final
    claim=$(tail -1 "${summary}" | cut -f4)
    smt=-; json=-
    if [[ -s "${final}/candidate.smt2" ]]; then
      gzip -9 -c "${final}/candidate.smt2" >"${dest}/${id}.smt2.gz"; smt=${id}.smt2.gz
    fi
    if [[ -s "${final}/claim.json" ]]; then
      cp "${final}/claim.json" "${dest}/${id}.claim.json"; json=${id}.claim.json
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "${id}" "${run}" "${claim}" "${smt}" "${json}" >>"${dest}/index.tsv"
    break
  done
done <"${cases}"
