#!/usr/bin/env bash
set -euo pipefail

repo=${1:?missing ZooKeeper checkout}
module=${2:?missing module}
test_class=${3:?missing test class}
test_method=${4:?missing test method}
m2=${MAVEN_REPO_LOCAL:?missing MAVEN_REPO_LOCAL}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}

jar=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
[[ "${SKIP_GRAPHCHECKER_INSTALL:-0}" == 1 ]] \
  || (cd "${graphchecker}" && mvn -q -o -DskipTests package)
common=(-q -B "-Dmaven.repo.local=${m2}")
# ZK_MAVEN_PROFILES: the profiles that put the workload's module in the reactor (system.sh's zk_maven_profiles)
read -r -a profiles <<<"${ZK_MAVEN_PROFILES:-}"
mvn "${common[@]}" install:install-file "-Dfile=${jar}" \
  -DgroupId=org.example -DartifactId=GraphChecker -Dversion=1.0-SNAPSHOT \
  -Dpackaging=jar
cd "${repo}"
common+=(-Dcheckstyle.skip -Dspotbugs.skip -Dmaven.javadoc.skip=true)
((${#profiles[@]} == 0)) || common+=("-P$(IFS=,; echo "${profiles[*]}")")
[[ "${SKIP_TREE_INSTALL:-0}" == 1 ]] || mvn "${common[@]}" -DskipTests install -pl "${module}" -am
# ZK_TEST_PROPERTIES: extra -D properties a case's workload needs at JVM start (a static final read at class load)
read -r -a extra <<<"${ZK_TEST_PROPERTIES:-}"
mvn "${common[@]}" test -pl "${module}" \
  -Dtest="${test_class##*.}#${test_method%%\[*}" -Dcausynth.cluster.automatic=true "${extra[@]+"${extra[@]}"}"

python3 - "${repo}/${module}/target/surefire-reports/TEST-${test_class}.xml" <<'PY'
import sys
import xml.etree.ElementTree as ET

root = ET.parse(sys.argv[1]).getroot()
counts = {name: int(root.get(name, "0"))
          for name in ("tests", "errors", "failures", "skipped")}
if counts["tests"] < 1 or counts["errors"] or counts["failures"] or counts["skipped"]:
    raise SystemExit(f"workload did not pass: {counts}")
automatic = {p.get("name"): p.get("value")
             for p in root.findall("./properties/property")}.get(
    "causynth.cluster.automatic")
if automatic != "true":
    raise SystemExit("workload did not run as an automatic cluster")
print(f"Workload passed: {root.get('name')}")
PY
