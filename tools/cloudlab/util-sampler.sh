#!/usr/bin/env bash
# util-sampler.sh <dir> [interval_s]: on every host of LIFTS, a sampler that appends one row per interval to
# <dir>/<host>.tsv -- epoch, CPU busy % over the interval (/proc/stat), the 1-minute load, memory in use
# (MemTotal - MemAvailable, MB), MemTotal (MB), nproc -- until <dir>/STOP exists.  final-stats.py --util <dir>
# reads them over each case's window.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=../lib/gc-env.sh
source "${here}/../lib/gc-env.sh"
dir=${1:?usage: util-sampler.sh <dir> [interval_s]}
interval=${2:-15}
mkdir -p "${dir}"
rm -f -- "${dir}/STOP"
for host in ${LIFTS}; do
  ssh -o BatchMode=yes "${host}" "setsid nohup bash -c '
    out=${dir}/\$(hostname -s).tsv
    read -r _ u n s i w q sq st _ </proc/stat
    busy0=\$((u + n + s + q + sq + st)); all0=\$((busy0 + i + w))
    while [[ ! -e ${dir}/STOP ]]; do
      sleep ${interval}
      read -r _ u n s i w q sq st _ </proc/stat
      busy=\$((u + n + s + q + sq + st)); all=\$((busy + i + w))
      pct=\$(( all > all0 ? 100 * (busy - busy0) / (all - all0) : 0 ))
      busy0=\${busy}; all0=\${all}
      read -r load _ </proc/loadavg
      mem=\$(awk \"/^MemTotal:/ {t = \\\$2} /^MemAvailable:/ {a = \\\$2} END {print int((t - a) / 1024), int(t / 1024)}\" /proc/meminfo)
      printf \"%s\\t%s\\t%s\\t%s\\t%s\\t%s\\n\" \$(date +%s) \${pct} \${load} \${mem} \$(nproc) >>\${out}
    done' >/dev/null 2>&1 </dev/null &"
done
echo "sampling ${LIFTS} every ${interval}s into ${dir} (touch ${dir}/STOP to end)"
