#!/usr/bin/env bash
# round-slow.sh <round> <baseline-round>: one line when a running case passes 2x (and 4x) its baseline time (or 30/60 min
# with no baseline row). Per-case state under $out/.watch-<round>, so a re-armed watcher does not repeat itself.
out=${GC_OUT:-/bigtemp/vnr3ne/gc-out/hdfs-study}
round=$1 base=$2
state=$out/.watch-$round; mkdir -p "$state"
declare -A basesec
while IFS=$'\t' read -r n c; do
  s=$out/accept-$base-$n/summary.tsv
  [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )) && basesec[$c]=$(tail -1 "$s" | cut -f3)
done < "$out/sweep-$base-cases.tsv"
while true; do
  now=$(date +%s)
  while IFS=$'\t' read -r n c; do
    d=$out/accept-$round-$n; [[ -d $d ]] || continue
    s=$d/summary.tsv; [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )) && continue
    age=$(( now - $(stat -c %Y "$d/logs/$c.driver.log" 2>/dev/null || echo $now) ))
    b=${basesec[$c]:-900}
    for m in 2 4; do
      k=$state/slow.$n.$m
      if (( age > m * b && age > 1200 )) && [[ ! -e $k ]]; then
        : > "$k"; stage=$(grep -o '^\[campaign\] stage [A-Z_]*' "$d/logs/$c.log" 2>/dev/null | tail -1 | awk '{print $3}')
        echo "SLOW x$m $c (n=$n) age=$((age/60))m base=$((b/60))m $stage"
      fi
    done
  done < "$out/sweep-$round-cases.tsv"
  sleep 120
done
