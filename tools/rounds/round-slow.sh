#!/usr/bin/env bash
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
out=${GC_OUT}
round=$1 base=$2
state=$out/.watch-$round; mkdir -p "$state"
declare -A basesec
while IFS=$'\t' read -r n c; do
  s=$out/accept-$base-$n/summary.tsv
  [[ -f $s ]] && (( $(wc -l < "$s") >= 2 )) && basesec[$c]=$(tail -1 "$s" | cut -f3)
done < <(round_runs "$base")
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
  done < <(round_runs "$round")
  sleep 120
done
