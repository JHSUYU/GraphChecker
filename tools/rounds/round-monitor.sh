#!/usr/bin/env bash
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
shopt -s nullglob
declare -A seen=()
out=${GC_OUT}
while :; do
  for pat in "$@"; do
    for d in ${out}/accept-$pat; do
      [[ -d "$d" ]] || continue
      c=${d##*/accept-}
      if (( $(wc -l < "$d/summary.tsv" 2>/dev/null || echo 0) >= 2 )); then
        if [[ -z "${seen[$c]:-}" ]]; then
          seen[$c]=1
          cf=$(ls $d/out/*/schedule/final/claim.json 2>/dev/null | head -1)
          m=""
          [[ -n "$cf" ]] && m=$(jq -c '.claim | {kind, polarityDecides, moved: [.movedRoots | to_entries[] | select(.value != "0") | (.key|sub("M_J_field_";"")|.[0:20])]}' "$cf" 2>/dev/null | cut -c1-200)
          echo "DONE $c: $(tail -1 $d/summary.tsv | awk -F'\t' '{print $2, $3, $4, $6, $11}') | $m"
        fi
      fi
    done
  done
  for pat in "$@"; do for f in ${out}/launch-$pat.log; do
    while IFS= read -r line; do
      k="L:$f:$line"; [[ -n "${seen[$k]:-}" ]] && continue; seen[$k]=1; echo "$line"
    done < "$f"
  done; done
  sleep 30
done
