#!/usr/bin/env bash
lifts_given=${LIFTS+set}
# shellcheck source=lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/gc-env.sh"
[[ -n "${lifts_given}" ]] || LIFTS=$(printf '%s\n' ${LIFTS} | grep -vx lift11 | tr '\n' ' ')
min=${1:-6}
for h in ${LIFTS}; do
  ssh -o ConnectTimeout=4 -o BatchMode=yes "$h" \
    "awk -v h=$h '/MemTotal/ {t=\$2/1048576} /MemAvailable/ {m=\$2/1048576} END {getline l < \"/proc/loadavg\"; split(l,a,\" \"); print h, m, t, a[1]}' /proc/meminfo" 2>/dev/null
done | awk -v min="$min" -v pct="${CAUSYNTH_HOST_MAX_USED_PCT}" '$2 - min >= $3 * (100 - pct) / 100 {score = ($2 - $3 * (100 - pct) / 100) / (1 + $4); print score, $1}' \
  | sort -rn | head -1 | awk '{print $2}'
