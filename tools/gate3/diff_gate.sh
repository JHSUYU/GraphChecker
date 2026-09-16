#!/usr/bin/env bash
# diff_gate.sh <outdir> [baseline-dir]
#
# Compare one gate3 run's DIGESTS.txt against the recorded baseline and print
# one line per artifact that changed, keyed corpus/gate/artifact.  Exit 0 when
# nothing changed, 1 when something did, 2 when a file is missing.
set -euo pipefail
[[ $# -ge 1 ]] || { echo "usage: diff_gate.sh <outdir> [baseline-dir]" >&2; exit 2; }
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
NEW="$1/DIGESTS.txt"
BASE="${2:-${HERE}/baseline}/DIGESTS.txt"
[[ -f "${NEW}" ]] || { echo "no such digests: ${NEW}" >&2; exit 2; }
[[ -f "${BASE}" ]] || { echo "no such digests: ${BASE}" >&2; exit 2; }
python3 - "${BASE}" "${NEW}" <<'PY'
import sys

def load(path):
    rows = {}
    with open(path) as handle:
        for line in handle:
            parts = line.rstrip("\n").split(" ", 4)
            if len(parts) < 4:
                continue
            corpus, gate, artifact, digest = parts[:4]
            counts = parts[4] if len(parts) > 4 else ""
            rows[(corpus, gate, artifact)] = (digest, counts)
    return rows

base = load(sys.argv[1])
new = load(sys.argv[2])
changed = 0
for key in sorted(set(base) | set(new)):
    label = "/".join(key)
    if key not in new:
        print("GONE     %s  baseline had %s %s" % (label, *base[key]))
        changed += 1
        continue
    if key not in base:
        print("NEW      %s  now %s %s" % (label, *new[key]))
        changed += 1
        continue
    (bd, bc), (nd, nc) = base[key], new[key]
    if bd == nd and bc == nc:
        continue
    changed += 1
    if bd != nd and bc != nc:
        kind = "CHANGED "
    elif bd != nd:
        kind = "DIGEST  "
    else:
        kind = "COUNTS  "
    print("%s %s" % (kind, label))
    if bd != nd:
        print("           sha    %s -> %s" % (bd, nd))
    if bc != nc:
        print("           counts %s" % bc)
        print("                  %s" % nc)
print()
print("%d of %d artifact(s) differ from the baseline"
      % (changed, len(set(base) | set(new))))
sys.exit(1 if changed else 0)
PY
