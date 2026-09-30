#!/usr/bin/env bash
# coverage.sh <system-dir> <repo> <classpath-test> <test-class> <test-method> <out-prefix>
#
# One workload test method, run as the engine runs it (JUnitMethodRunner, the
# system's JVM properties, an automatic cluster) under the JaCoCo agent on
# plain JDK 8.  Writes <out-prefix>.lines ("class<TAB>line" of every line the
# run executed in the system's own classes) and <out-prefix>.log, prints one
# summary line, and exits with the test's own status: a workload that fails
# here fails its seed too, and fanout.sh's exit=<status> is what select.py
# reads (375 of HDFS's 2818 workloads failed here and stayed selectable while
# this script always exited 0).  <classpath-test> names a test whose report states the
# module's classpath: every test of the module runs on it.  WORKLOAD_JAVA_OPTS
# adds the case's own workload properties (an HDFS upstream test's automatic
# cluster).
set -uo pipefail
system_dir=$(cd "${1:?system dir}" && pwd -P)
repo=${2:?repo}
classpath_test=${3:?classpath test}
test_class=${4:?test class}
test_method=${5:?test method}
out=${6:?out prefix}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker=$(cd "${here}/../.." && pwd -P)
jar=${GRAPHCHECKER_JAR:-${graphchecker}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}
java=/usr/lib/jvm/java-8-openjdk-amd64/bin
m2=${HOME}/.m2/repository
agent=${m2}/org/jacoco/org.jacoco.agent/0.8.5/org.jacoco.agent-0.8.5-runtime.jar
tools="${m2}/org/jacoco/org.jacoco.core/0.8.6/org.jacoco.core-0.8.6.jar:${m2}/org/ow2/asm/asm/9.4/asm-9.4.jar:${m2}/org/ow2/asm/asm-commons/9.4/asm-commons-9.4.jar:${m2}/org/ow2/asm/asm-tree/9.4/asm-tree-9.4.jar:${m2}/org/ow2/asm/asm-analysis/9.4/asm-analysis-9.4.jar"
# shellcheck source=/dev/null
source "${system_dir}/system.sh"
system_paths
cp=$(system_classpath) || exit 2
scratch=/localtmp/${USER}
mkdir -p "${scratch}" 2>/dev/null || scratch=/tmp
work=$(mktemp -d "${scratch}/cov.XXXXXX")
trap 'rm -rf -- "${work}"' EXIT
mkdir -p "${work}/temp" "${work}/data" "${work}/tools" "$(dirname "${out}")"
system_jvm_properties "${work}/temp" "${work}/data"
read -r -a extra <<<"${WORKLOAD_JAVA_OPTS:-}"
if [[ ${system_jar_first} == true ]]; then
  classpath="${jar}:${cp}"
else
  classpath="${cp}:${jar}"
fi
( cd "${repo}" && timeout "${COVERAGE_TIMEOUT_S:-900}" "${java}/java" -ea -Xmx3g \
    -Djava.awt.headless=true -Djava.io.tmpdir="${work}/temp" \
    -Dsun.reflect.noInflation=true "${jvm_properties[@]}" "${extra[@]+"${extra[@]}"}" \
    -javaagent:"${agent}=destfile=${out}.exec,includes=${system_package}.*" \
    -cp "${classpath}" edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
    "${test_class}" "${test_method}" ) > "${out}.log" 2>&1
status=$?
roots=()
for root in "${system_roots[@]}"; do roots+=("$(system_root "${root}")"); done
"${java}/javac" -nowarn -cp "${tools}" -d "${work}/tools" "${here}/CoveredLines.java"
if [[ -s "${out}.exec" ]]; then
  "${java}/java" -cp "${tools}:${work}/tools" CoveredLines "${out}.exec" "${roots[@]}" > "${out}.lines"
else
  : > "${out}.lines"
fi
rm -f -- "${out}.exec"
# Whether the run started a node, read by select.py without the lines.
rm -f -- "${out}.node"
if grep -q "^${system_node_class}"$'\t' "${out}.lines"; then : > "${out}.node"; fi
echo "$(basename "${out}") exit=${status} lines=$(wc -l < "${out}.lines")"
exit "${status}"
