#!/usr/bin/env bash
# build.sh <tree> [<test class>#<test method>...] -- an HDFS tree built for
# GraphChecker, then the named workloads run once natively: a case's
# classpath is read off its workload's surefire report (system.sh
# system_classpath), so every case a tree serves needs its test run there
# once after a build.
#
# GraphChecker's plain jar, from this checkout's target/ (run `mvn package`
# first), is installed into the tree's own Maven repository: the tree's
# hadoop-common, hadoop-hdfs-client and hadoop-hdfs compile against it
# (provided).  The launcher puts the run's frozen jar ahead of the tree's
# classpath, so the installed one only has to compile the tree.  Then
# hadoop-hdfs and every module it needs are built (-am), Java 8, by the
# tree's own Maven repository: no tree installs into ~/.m2, where it would
# change the jars every other tree resolves.
#
#   MAVEN_REPO_LOCAL  the tree's Maven repository
#                     (default $GC_M2/<tree's directory name>)
#   SKIP_TREE_BUILD=1 only run the workloads (the tree is built)
set -euo pipefail

tree=$(cd "${1:?usage: build.sh <tree> [<class>#<method>...]}" && pwd -P)
shift
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
# shellcheck source=../../tools/lib/gc-env.sh
source "${graphchecker}/tools/lib/gc-env.sh"
m2=${MAVEN_REPO_LOCAL:-${GC_M2}/$(basename "${tree}")}
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:${PATH}
cd "${tree}"
maven=(mvn)
[[ ! -x ./mvnw ]] || maven=(./mvnw)
common=(-Dmaven.repo.local="${m2}" -Djavac.version=8 -DskipShade -Dskip.npm
  -Dskip.yarn -Dmaven.compiler.fork=true
  "-Dmaven.compiler.executable=${here}/javac8-filter-crc32c.sh")

if [[ "${SKIP_TREE_BUILD:-0}" != 1 ]]; then
  jar=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT.jar
  [[ -f "${jar}" ]] || { echo "no ${jar}: run mvn package in ${graphchecker} first" >&2; exit 2; }
  (cd "${graphchecker}" && mvn -q install:install-file "-Dmaven.repo.local=${m2}" \
    "-Dfile=${jar}" -DpomFile=pom.xml)
  "${maven[@]}" -q "${common[@]}" -pl hadoop-hdfs-project/hadoop-hdfs -am \
    -DskipTests clean install
fi
(($# > 0)) || exit 0

# One surefire run for every workload, grouped by class: -Dtest=A#m1*+m2*,B#m3*
# (a parameterized method m[k] runs as m*, every invocation; surefire takes
# the simple class name).  A test that fails natively still writes its
# report; whether each one passed is printed below.
declare -A methods=() seen=()
for spec in "$@"; do
  class=${spec%%#*}
  method=${spec#*#}
  [[ -z "${seen[${class}#${method%%\[*}]:-}" ]] || continue
  seen[${class}#${method%%\[*}]=1
  methods[${class}]+="${methods[${class}]:++}${method%%\[*}*"
done
filter=""
for class in "${!methods[@]}"; do
  filter+="${filter:+,}${class##*.}#${methods[${class}]}"
done
mkdir -p "/localtmp/$(id -un)"
scratch=$(mktemp -d "/localtmp/$(id -un)/hdfs-workloads.XXXXXX")
trap 'rm -rf "${scratch}"' EXIT
"${maven[@]}" -q "${common[@]}" -DfailIfNoTests=false \
  -Dsurefire.failIfNoSpecifiedTests=false -Dmaven.test.failure.ignore=true \
  "-Dtest.build.dir=${scratch}" "-Dtest.build.data=${scratch}" \
  -pl hadoop-hdfs-project/hadoop-hdfs surefire:test "-Dtest=${filter}"

python3 - "${tree}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports" "$@" <<'PY'
import os
import re
import sys
import xml.etree.ElementTree as ET

# JUnit 5 names an invocation m(String)[1], or plain m when the class is the
# parameterized one: a report names a workload when the method matches with
# parameters and invocation index set aside.
def base(name):
    return re.sub(r"(\(.*?\))?(\[.*\])?$", "", name)

reports, specs = sys.argv[1], sys.argv[2:]
missing = 0
for spec in dict.fromkeys(specs):
    class_name, method = spec.split("#", 1)
    path = os.path.join(reports, f"TEST-{class_name}.xml")
    if not os.path.exists(path):
        print(f"MISSING  {spec}: no {path}")
        missing += 1
        continue
    cases = [c for c in ET.parse(path).getroot().iter("testcase")
             if base(c.get("name", "")) == base(method)]
    if not cases:
        print(f"MISSING  {spec}: {path} does not name it")
        missing += 1
    elif any(c.find(k) is not None for c in cases for k in ("failure", "error", "skipped")):
        print(f"FAILED   {spec} (natively; its report is still its classpath)")
    else:
        print(f"PASSED   {spec}")
sys.exit(1 if missing else 0)
PY
