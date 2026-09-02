#!/usr/bin/env bash
set -euo pipefail

report=${SOLR_TEST_REPORT:-/opt/solr/solr/build/solr-core/test/TEST-org.apache.solr.handler.TestReplicationHandler.xml}
[[ -f "${report}" ]] || {
  echo "missing Solr test report: ${report}; run build.sh first" >&2
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
    raise SystemExit("Solr report has no java.class.path")
print(os.pathsep.join(entries))
PY
