#!/usr/bin/env bash
# round-status.sh <round>: per started case, its age, current stage and seed-replay give-ups (or its verdict when done).
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
out=${GC_OUT}; round=$1; now=$(date +%s)
while IFS=$'\t' read -r n c; do
  d=$out/accept-$round-$n; [[ -d $d ]] || continue
  s=$d/summary.tsv
  if [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )); then
    tail -1 "$s" | awk -F'\t' -v n=$n '{printf "%-3s %-24s DONE %6ss %-14s %s %s\n", n, $1, $3, $4, $11, substr($12,1,70)}'; continue
  fi
  age=$(( (now - $(stat -c %Y "$d/logs/$c.driver.log" 2>/dev/null || echo $now)) / 60 ))
  stage=$(grep -o '^\[campaign\] stage [A-Z_]*' "$d/logs/$c.log" 2>/dev/null | tail -1 | awk '{print $3}')
  r=$d/out/$c/schedule/iteration-0000/seed-result/focused/replay.log
  g=$( [[ -f $r ]] && grep -c 'did not happen' "$r")
  printf "%-3s %-24s %4sm %-10s giveups=%s\n" "$n" "$c" "$age" "${stage:-?}" "${g:--}"
done < <(round_runs "$round")
