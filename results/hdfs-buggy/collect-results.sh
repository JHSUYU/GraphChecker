#!/usr/bin/env bash
# collect-results.sh <cases.tsv> [round]: copy each buggy-detect case's final .smt (gzip) and claim from its run
# accept-<round>-<case> (launch-round.sh's name: hdfs-* loses its hdfs-) under GC_OUT into this directory, and
# index.tsv naming each file's run (final-stats.py reads the runs themselves).
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
out=${GC_OUT:-/bigtemp/vnr3ne/gc-out/buggy-detect}
cases=${1:?usage: collect-results.sh <cases.tsv> [round]}
round=${2:-B1}
printf 'case\trun\tclaim\tsmt\tclaim_json\n' >"${here}/index.tsv"
while IFS=$'\t' read -r id _; do
  [[ -n "${id}" && "${id}" != \#* ]] || continue
  run=accept-${round}-${id#hdfs-}
  summary=${out}/${run}/summary.tsv
  [[ -f "${summary}" && $(wc -l <"${summary}") -ge 2 ]] || { echo "${id}: no finished ${run}" >&2; continue; }
  final=${out}/${run}/out/${id}/schedule/final
  claim=$(tail -1 "${summary}" | cut -f4)
  smt=-; json=-
  if [[ -s "${final}/candidate.smt2" ]]; then
    gzip -9 -c "${final}/candidate.smt2" >"${here}/${id}.smt2.gz"; smt=${id}.smt2.gz
  fi
  if [[ -s "${final}/claim.json" ]]; then
    cp "${final}/claim.json" "${here}/${id}.claim.json"; json=${id}.claim.json
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${id}" "buggy-detect/${run}" "${claim}" "${smt}" "${json}" >>"${here}/index.tsv"
done <"${cases}"
