#!/usr/bin/env bash
set -euo pipefail

report=/opt/hadoop-hdfs-17897/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-org.apache.hadoop.hdfs.TestCausynthStripedChecksum.xml
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
