#!/usr/bin/env bash
# shellcheck source=../lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/../lib/gc-env.sh"
out=${GC_OUT}
round=$1 base=${2:-}
declare -A basestalls
if [[ -n $base ]]; then
  while IFS=$'\t' read -r n c; do
    f=$out/accept-$base-$n/out/$c/schedule/iteration-0000/seed-result/focused/replay.log
    [[ -f $f ]] && basestalls[$c]=$(grep -c 'did not happen' "$f")
  done < <(round_runs "$base")
fi
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
    b=${basestalls[$c]:-}
    k=$(echo "$c.regress" | tr '/' '_')
    if [[ -n $b ]] && (( ${n:-0} >= 20 && ${n:-0} > 2 * b )) && [[ ! -e "$state/stall.$k" ]]; then
      : > "$state/stall.$k"; echo "STALLS-REGRESSION ${c} seed replay stalls=${n}, ${b} in ${base}"
    fi
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
