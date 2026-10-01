#!/usr/bin/env bash
# build.sh <solr checkout> <test class> <test method> <seed> -- builds the
# tree's core module and its tests with the current GraphChecker jar, and runs
# the workload once natively, as an automatic cluster, under the case's seed.
# Its junit4 report states the classpath every workload JVM runs on.
set -euo pipefail

repo=${1:?missing Solr checkout}
test_class=${2:?missing test class}
test_method=${3:?missing test method}
seed=${4:?missing seed}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}
# Ant, wherever the host installed it: a remote command's PATH (onlift.sh)
# has it on some lifts only (lift12-15 keep it under /usr/lib/ant/bin).
ant=$(command -v ant || true)
for candidate in /usr/share/ant/bin/ant /usr/lib/ant/bin/ant; do
  [[ -n "${ant}" ]] || [[ ! -x "${candidate}" ]] || ant=${candidate}
done
[[ -n "${ant}" ]] || { echo "no ant on $(hostname)" >&2; exit 2; }

jar=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
[[ "${SKIP_GRAPHCHECKER_INSTALL:-0}" == 1 ]] \
  || (cd "${graphchecker}" && mvn -q -o -DskipTests package)
cd "${repo}/solr/core"
"${ant}" -q -Dgraphchecker.jar="${jar}" compile-test
"${ant}" -q -Dgraphchecker.jar="${jar}" test -Dtests.class="${test_class}" \
  -Dtests.method="${test_method}" -Dtests.seed="${seed}" -Dtests.jvms=1 \
  -Dtests.useSecurityManager=false -Dargs="-Dcausynth.cluster.automatic=true"

python3 - "${repo}/solr/build/solr-core/test/TEST-${test_class}.xml" <<'PY'
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
counts = {name: int(root.get(name, "0"))
          for name in ("tests", "errors", "failures", "skipped")}
if counts != {"tests": 1, "errors": 0, "failures": 0, "skipped": 0}:
    raise SystemExit(f"workload did not pass: {counts}")
print(f"Workload passed: {root.get('name')}")
PY
