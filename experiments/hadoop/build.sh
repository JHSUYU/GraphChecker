#!/usr/bin/env bash
set -euo pipefail

repo=${1:?missing Hadoop checkout}
test_class=${2:?missing test class}
test_method=${3:?missing test method}
# The javac the Hadoop build uses: the case's own when it declares one.
declared_javac=${4-}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}

# Hadoop's bridge compiles against this main checkout, not an older installed
# GraphChecker API. The experiment launcher also loads its frozen jar first.
# SKIP_GRAPHCHECKER_INSTALL=1 when the jar is already in this host's local
# repository: several hosts building trees at once must not all rebuild the
# one shared checkout's target/.
[[ "${SKIP_GRAPHCHECKER_INSTALL:-0}" == 1 ]] \
  || mvn -q -f "${graphchecker}/pom.xml" -DskipTests install
cd "${repo}"
maven=(mvn)
[[ ! -x ./mvnw ]] || maven=(./mvnw)
javac=${declared_javac:-${CAUSYNTH_HADOOP_JAVAC:-${here}/javac8-filter-crc32c.sh}}
common=(-q -Djavac.version=8 -DskipShade -Dskip.npm -Dskip.yarn
  -Dmaven.compiler.fork=true
  "-Dmaven.compiler.executable=${javac}")
# MAVEN_REPO_LOCAL: a local repository of this build's own, so several trees
# can build at once without two installs racing on one repository's metadata.
[[ -z "${MAVEN_REPO_LOCAL:-}" ]] \
  || common+=("-Dmaven.repo.local=${MAVEN_REPO_LOCAL}")
"${maven[@]}" "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -am -DskipTests clean install
# Surefire takes the method: a parameterized one (m[k]) runs every invocation.
"${maven[@]}" "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs \
  -Dtest="${test_class##*.}#${test_method%%\[*}" test

python3 - "${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-${test_class}.xml" <<'PY'
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
counts = {name: int(root.get(name, "0"))
          for name in ("tests", "errors", "failures", "skipped")}
if counts["tests"] < 1 or counts["errors"] or counts["failures"] or counts["skipped"]:
    raise SystemExit(f"workload did not pass: {counts}")
print(f"Workload passed: {root.get('name')}")
PY
