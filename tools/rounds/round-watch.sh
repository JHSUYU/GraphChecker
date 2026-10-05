#!/usr/bin/env bash
# round-watch.sh <round>: one line per finished case (its claim and verdict) and per seed replay past 30/80 stalls.
out=${GC_OUT:-/bigtemp/vnr3ne/gc-out/hdfs-study}
round=$1
shopt -s nullglob
declare -A seen
state=$out/.watch-$round
mkdir -p "$state"
while true; do
  for f in "${out}"/accept-"${round}"-*/out/*/schedule/iteration-0000/seed-result/focused/replay.log; do
    n=$(grep -c 'did not happen' "$f" 2>/dev/null)
    c=$(sed -E 's#.*/out/([^/]+)/schedule.*#\1#' <<< "$f")
    for t in 30 80; do
      k=$(echo "$c.$t" | tr '/' '_')
      if (( ${n:-0} >= t )) && [[ ! -e "$state/stall.$k" ]]; then
        : > "$state/stall.$k"; echo "STALLS>=${t} ${c} seed replay stalls=${n}"
      fi
    done
  done
  for s in "${out}"/accept-"${round}"-*/summary.tsv; do
    d=$(dirname "$s"); k=$(basename "$d")
    [[ -e "$state/done.$k" ]] && continue
    (( $(wc -l < "$s") >= 2 )) || continue
    : > "$state/done.$k"
    tail -1 "$s" | awk -F'\t' '{printf "DONE %s %ss %s %s\n", $1, $3, $4, $11}'
  done
  sleep 60
done
