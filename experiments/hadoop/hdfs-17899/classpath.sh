#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${here}/case.sh" "${1:?missing case}"
[[ -f "${report}" ]] || {
  echo "missing test report: ${report}; run build first" >&2
  exit 2
}
python3 - "${report}" <<'PY'
import os
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
value = next((p.get("value", "") for p in root.findall("./properties/property")
              if p.get("name") == "java.class.path"), "")
entries = []
for entry in value.split(os.pathsep):
    if entry and entry not in entries:
        entries.append(entry)
if not entries:
    raise SystemExit("test report has no java.class.path")
print(os.pathsep.join(entries))
PY
