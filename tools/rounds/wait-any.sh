#!/usr/bin/env bash
# The per-round watcher the launcher pairs with.
# wait-any.sh <max-seconds> <seen-file> <round>...: exit on the first new finish/error in any given round
max=$1; seen=$2; shift 2; touch "$seen"; t=0
while (( t < max )); do
  for round in "$@"; do for d in ${GC_OUT:-/u/vnr3ne/gc-out}/accept-$round-*; do
    [ -d "$d" ] || continue; c=$round/${d##*/accept-$round-}
    if [ "$(wc -l < $d/summary.tsv 2>/dev/null || echo 0)" -ge 2 ] && ! grep -qx "done $c" "$seen"; then echo "done $c" >> "$seen"; echo "DONE $c: $(tail -1 $d/summary.tsv | cut -f2-4,11,12 | cut -c1-400)"; exit 0; fi
    if grep -q '^\[campaign:error\]' $d/logs/*.log 2>/dev/null && ! grep -qx "err $c" "$seen"; then echo "err $c" >> "$seen"; echo "ERROR $c: $(grep -A4 '^\[campaign:error\]' $d/logs/*.log | tr '\n' ' ' | cut -c1-400)"; exit 0; fi
  done; done
  sleep 30; t=$((t+30))
done
echo "TIMEOUT"
