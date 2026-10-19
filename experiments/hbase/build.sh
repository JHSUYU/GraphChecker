#!/usr/bin/env bash
set -euo pipefail

tree=$(cd "${1:?usage: build.sh <tree> [<class>#<method>[@<window>]...]}" && pwd -P)
shift
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
source "${graphchecker}/tools/lib/gc-env.sh"
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH=${JAVA_HOME}/bin:/usr/lib/maven/bin:${PATH}
repository=${HBASE_MAVEN_REPO:-${GC_M2}/$(basename "${tree}")}
jar=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT.jar
full=${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar
[[ -f "${jar}" && -f "${full}" ]] || { echo "no ${jar}: run mvn package in ${graphchecker} first" >&2; exit 2; }
common=(-B -q -Dmaven.repo.local="${repository}" -Dcheckstyle.skip -Dspotless.skip=true -Denforcer.skip=true)

module_of() {
  local source
  for source in "${tree}"/hbase-*/src/test/java/"${1//.//}".java; do
    [[ -f "${source}" ]] || continue
    source=${source#"${tree}/"}
    echo "${source%%/*}"
    return 0
  done
  echo "no test source of $1 in ${tree}" >&2
  return 2
}

modules=hbase-server
for spec in "$@"; do
  module=$(module_of "${spec%%#*}")
  [[ ",${modules}," == *",${module},"* ]] || modules+=",${module}"
done

cd "${tree}"
if [[ "${SKIP_TREE_BUILD:-0}" != 1 ]]; then
  mvn -q -Dmaven.repo.local="${repository}" install:install-file -Dfile="${jar}" \
    -DgroupId=org.example -DartifactId=GraphChecker -Dversion=1.0-SNAPSHOT -Dpackaging=jar -DgeneratePom=true
  mvn "${common[@]}" -pl "${modules}" -am -DskipTests install
fi

missing=0
for spec in "$@"; do
  class=${spec%%#*}
  method=${spec#*#}
  window=""
  if [[ "${method}" == *@* ]]; then
    window=${method#*@}
    method=${method%@*}
  fi
  module=$(module_of "${class}")
  size=$(grep -hoE '@Tag\((Small|Medium|Large)Tests\.TAG\)' "${module}/src/test/java/${class//.//}.java" \
    | head -1 | sed -E 's/@Tag\((.*)\.TAG\)/\1/')
  report=${tree}/${module}/target/surefire-reports/TEST-${class}.xml
  rm -f -- "${report}"
  mvn "${common[@]}" -pl "${module}" test -Dtest="${class##*.}#${method}" \
    -Dsurefire.firstPartGroups="org.apache.hadoop.hbase.testclassification.${size:-MediumTests}" \
    -Dsurefire.skipSecondPart=true -Dmaven.test.additionalClasspath="${full}" \
    -DargLine="-enableassertions -Xmx2200m -Djava.net.preferIPv4Stack=true -Dio.netty.eventLoopThreads=3 -Dcausynth.cluster.automatic=true${window:+ -Dcausynth.recording.window=${window}}" \
    || true
  python3 - "${report}" "${class}#${method}" <<'PY' || missing=$((missing + 1))
import os
import sys
import xml.etree.ElementTree as ET

path, spec = sys.argv[1], sys.argv[2]
method = spec.split("#", 1)[1]
if not os.path.exists(path):
    print(f"MISSING  {spec}: no {path}")
    sys.exit(1)
root = ET.parse(path).getroot()
cases = [c for c in root.iter("testcase") if c.get("name", "").split("(")[0] == method]
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
