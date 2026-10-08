#!/usr/bin/env bash
# build.sh <tree> <seed> [<test class>#<test method>...] -- a Solr tree built
# for GraphChecker (Ant, Java 8: solr-core and its tests, with solrj and the
# test framework, against this checkout's GraphChecker jar; run `mvn package`
# first), then the named workloads run once natively, one Ant run each, as an
# automatic cluster under the randomized-testing seed: a case's classpath is
# read off its workload's junit4 report (system.sh system_classpath), so every
# case a tree serves needs its test run there once after a build.  One line
# per workload: PASSED, FAILED (natively; its report is still its classpath)
# or MISSING (no report names it: the script fails).
#
#   SKIP_TREE_BUILD=1 only run the workloads (the tree is built)
set -euo pipefail

tree=$(cd "${1:?usage: build.sh <tree> <seed> [<class>#<method>...]}" && pwd -P)
seed=${2:?missing seed}
shift 2
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
[[ -f "${jar}" ]] || { echo "no ${jar}: run mvn package in ${graphchecker} first" >&2; exit 2; }

cd "${tree}/solr/core"
[[ "${SKIP_TREE_BUILD:-0}" == 1 ]] || "${ant}" -q -Dgraphchecker.jar="${jar}" compile-test
missing=0
for spec in "$@"; do
  class=${spec%%#*}
  method=${spec#*#}
  # A test that fails natively still writes its report.
  "${ant}" -q -Dgraphchecker.jar="${jar}" test -Dtests.class="${class}" \
    -Dtests.method="${method}" -Dtests.seed="${seed}" -Dtests.jvms=1 \
    -Dtests.useSecurityManager=false -Dargs="-Dcausynth.cluster.automatic=true" || true
  python3 - "${tree}/solr/build/solr-core/test/TEST-${class}.xml" "${spec}" <<'PY' || missing=$((missing + 1))
import os
import sys
import xml.etree.ElementTree as ET

path, spec = sys.argv[1], sys.argv[2]
method = spec.split("#", 1)[1]
if not os.path.exists(path):
    print(f"MISSING  {spec}: no {path}")
    sys.exit(1)
root = ET.parse(path).getroot()
cases = [c for c in root.iter("testcase") if c.get("name") == method]
if not cases:
    print(f"MISSING  {spec}: {path} does not name it")
    sys.exit(1)
if any(c.find(k) is not None for c in cases for k in ("failure", "error", "skipped")):
    print(f"FAILED   {spec} (natively; its report is still its classpath)")
else:
    print(f"PASSED   {spec} {cases[0].get('time')} s")
PY
done
exit $((missing > 0))
