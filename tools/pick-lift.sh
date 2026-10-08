#!/usr/bin/env bash
# pick-lift.sh [min-free-gb]: prints the host of LIFTS (tools/lib/gc-env.sh)
# with the most free memory per unit of load among those where taking
# min-free-gb (default 6) still leaves the host at most
# CAUSYNTH_HOST_MAX_USED_PCT percent full.  Prints nothing when none
# qualifies.
# shellcheck source=lib/gc-env.sh
source "$(dirname "${BASH_SOURCE[0]}")/lib/gc-env.sh"
min=${1:-6}
for h in ${LIFTS}; do
  ssh -o ConnectTimeout=4 -o BatchMode=yes "$h" \
    "awk -v h=$h '/MemTotal/ {t=\$2/1048576} /MemAvailable/ {m=\$2/1048576} END {getline l < \"/proc/loadavg\"; split(l,a,\" \"); print h, m, t, a[1]}' /proc/meminfo" 2>/dev/null
done | awk -v min="$min" -v pct="${CAUSYNTH_HOST_MAX_USED_PCT}" '$2 - min >= $3 * (100 - pct) / 100 {score = ($2 - $3 * (100 - pct) / 100) / (1 + $4); print score, $1}' \
  | sort -rn | head -1 | awk '{print $2}'
