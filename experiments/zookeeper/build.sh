#!/usr/bin/env bash
# build.sh <zookeeper checkout> <module> <test class> <test method> <modules>
# -- builds the workload's module, the modules of the lineage scope (comma
# separated; system.sh zk_lineage_modules) and what they need with the
# current GraphChecker jar, and runs the workload once natively, as an
# automatic cluster.  Its surefire report states the classpath every workload
# JVM runs on.
#
# MAVEN_REPO_LOCAL is the tree's own Maven repository (system.sh
# zk_maven_repo): the tree's SNAPSHOT artifacts and the GraphChecker jar its
# modules depend on (provided) are installed there, never into ~/.m2.
set -euo pipefail

repo=${1:?missing ZooKeeper checkout}
module=${2:?missing module}
test_class=${3:?missing test class}
test_method=${4:?missing test method}
lineage_modules=${5:?missing lineage modules}
m2=${MAVEN_REPO_LOCAL:?missing MAVEN_REPO_LOCAL}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}

jar=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
[[ "${SKIP_GRAPHCHECKER_INSTALL:-0}" == 1 ]] \
  || (cd "${graphchecker}" && mvn -q -o -DskipTests package)
common=(-q -B "-Dmaven.repo.local=${m2}")
# The whole jar: the tree's tests run natively with the engine's runtime on
# their classpath, last (the dependency is the last of each module).
mvn "${common[@]}" install:install-file "-Dfile=${jar}" \
  -DgroupId=org.example -DartifactId=GraphChecker -Dversion=1.0-SNAPSHOT \
  -Dpackaging=jar
cd "${repo}"
common+=(-Dcheckstyle.skip -Dspotbugs.skip -Dmaven.javadoc.skip=true)
mvn "${common[@]}" -DskipTests install -pl "${module},${lineage_modules}" -am
mvn "${common[@]}" test -pl "${module}" \
  -Dtest="${test_class##*.}#${test_method}" -Dcausynth.cluster.automatic=true

python3 - "${repo}/${module}/target/surefire-reports/TEST-${test_class}.xml" <<'PY'
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
counts = {name: int(root.get(name, "0"))
          for name in ("tests", "errors", "failures", "skipped")}
if counts != {"tests": 1, "errors": 0, "failures": 0, "skipped": 0}:
    raise SystemExit(f"workload did not pass: {counts}")
automatic = {p.get("name"): p.get("value")
             for p in root.findall("./properties/property")}.get(
    "causynth.cluster.automatic")
if automatic != "true":
    raise SystemExit("workload did not run as an automatic cluster")
print(f"Workload passed: {root.get('name')}")
PY
