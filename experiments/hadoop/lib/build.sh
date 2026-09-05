#!/usr/bin/env bash
set -euo pipefail

repo=${1:?missing Hadoop checkout}
test_class=${2:?missing test class}
test_method=${3:?missing test method}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../../.." && pwd -P)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}

# Hadoop's bridge compiles against this main checkout, not an older installed
# GraphChecker API. The experiment launcher also loads its frozen jar first.
mvn -q -f "${graphchecker}/pom.xml" -DskipTests install
cd "${repo}"
common=(-q -Djavac.version=8 -DskipShade -Dskip.npm -Dskip.yarn
  -Dmaven.compiler.fork=true
  "-Dmaven.compiler.executable=${here}/javac8-filter-crc32c.sh")
./mvnw "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -am -DskipTests clean install
./mvnw "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -Dtest="${test_class##*.}#${test_method}" test

python3 - "${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-${test_class}.xml" <<'PY'
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
counts = {name: int(root.get(name, "0"))
          for name in ("tests", "errors", "failures", "skipped")}
if counts != {"tests": 1, "errors": 0, "failures": 0, "skipped": 0}:
    raise SystemExit(f"workload did not pass: {counts}")
print(f"Workload passed: {root.get('name')}")
PY
