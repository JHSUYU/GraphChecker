#!/usr/bin/env bash

set -euo pipefail

experiment_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${experiment_dir}/../../.." && pwd -P)
hadoop_dir=${HADOOP_REPO:-/tmp/hdfs-17960-vulnerable}
workflow="${experiment_dir}/workflow.properties"
work_root=${HDFS17960_WORK_ROOT:-${graphchecker_dir}/experiments-output/hdfs-17960}
hdfs_pom="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/pom.xml"
java8_home=${HDFS17960_JAVA_HOME:-/usr/lib/jvm/java-8-openjdk-amd64}
test_class=org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion
test_method=testOrderedDeletionWithRestart
project_classpath="${work_root}/project-classpath.txt"

die() {
  echo "[hdfs-17960] $*" >&2
  exit 1
}

require_file() {
  [[ -f "$2" ]] || die "$1 not found: $2"
}

ensure_java8() {
  require_file "Java 8" "${java8_home}/bin/java"
  local version
  version=$("${java8_home}/bin/java" -version 2>&1 | sed -n '1p')
  [[ "${version}" == *'"1.8.'* ]] \
    || die "Java 8 is required; found ${version}"
}

build_graphchecker() {
  ensure_java8
  (
    cd "${graphchecker_dir}"
    JAVA_HOME="${java8_home}" PATH="${java8_home}/bin:${PATH}" \
      mvn -q -DskipTests package
  )
}

build_hadoop() {
  ensure_java8
  (
    cd "${hadoop_dir}"
    JAVA_HOME="${java8_home}" PATH="${java8_home}/bin:${PATH}" \
      mvn -pl :hadoop-hdfs -am -DskipTests -DskipShade \
        -Dcheckstyle.skip -Drat.skip -Dmaven.javadoc.skip=true install
  )
}

build_classpath() {
  mkdir -p "${work_root}"
  JAVA_HOME="${java8_home}" PATH="${java8_home}/bin:${PATH}" \
    mvn -q -f "${hdfs_pom}" -DincludeScope=test \
      -Dmdep.outputAbsoluteArtifactFilename=true \
      -Dmdep.outputFile="${work_root}/dependency-classpath.txt" \
      dependency:build-classpath
  {
    printf '%s:' \
      "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes" \
      "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes"
    tr -d '\r\n' <"${work_root}/dependency-classpath.txt"
    printf '\n'
  } >"${project_classpath}"
}

run_junit() {
  local classes=$1
  local log=$2
  local graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar"
  local gson_jar
  local classpath
  require_file "project classpath" "${project_classpath}"
  require_file "GraphChecker runtime jar" "${graphchecker_jar}"
  gson_jar=$(find /users/ZhenyuLi/.m2/repository/com/google/code/gson/gson/2.10.1 \
    -name 'gson-2.10.1.jar' -print -quit)
  require_file "GraphChecker Gson" "${gson_jar}"
  classpath=$(tr -d '\r\n' <"${project_classpath}")
  mkdir -p "$(dirname "${log}")" "${work_root}/test-data" \
    "${work_root}/java-tmp" "${work_root}/hadoop-logs"
  set +e
  "${java8_home}/bin/java" \
    -Dcausynth.trace.output.dir="${work_root}/runtime" \
    -Dcausynth.trace.test="${test_class}.${test_method}" \
    -Dcausynth.trace.max.events=5000000 \
    -Dcausynth.junit.ignore.timeout=true \
    -Dtest.build.data="${work_root}/test-data" \
    -Djava.io.tmpdir="${work_root}/java-tmp" \
    -Dhadoop.log.dir="${work_root}/hadoop-logs" \
    -cp "${classes}:${gson_jar}:${classpath}:${graphchecker_jar}" \
    edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
    "${test_class}" "${test_method}" >"${log}" 2>&1
  local java_status=$?
  set -e
  [[ "${java_status}" -ne 0 ]] \
    || die "workload unexpectedly completed without reaching the target"
  rg -q 'FSImageFormatPBSnapshot.*serializeSnapshotSection' "${log}" \
    || die "workload failed outside serializeSnapshotSection; see ${log}"
}

prepare() {
  build_graphchecker
  build_hadoop
  build_classpath
  run_junit \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes" \
    "${work_root}/baseline-workload.log"
  echo "[hdfs-17960] Java 8 workload reproduced the annotated target"
}

traced_workload() {
  run_junit "${work_root}/instrumented-classes" \
    "${work_root}/traced-workload.log"
}

delegate() {
  JAVA_HOME="${java8_home}" \
  PATH="${java8_home}/bin:${PATH}" \
  GRAPH_CHECKER_JAVA="${java8_home}/bin/java" \
  CAUSYNTH_HDFS_EXPERIMENT=hdfs-17960 \
  CAUSYNTH_HDFS_WORKFLOW="${workflow}" \
  HADOOP_REPO="${hadoop_dir}" \
  HDFS11741_WORK_ROOT="${work_root}" \
  HDFS11741_REGION_JOBS="${CAUSYNTH_REGION_JOBS:-2}" \
  HDFS11741_PATH_JOBS="${CAUSYNTH_PATH_JOBS:-2}" \
  CAUSYNTH_REQUIRE_COMPLETE_CANDIDATE=true \
  CAUSYNTH_REQUIRE_EXPLICIT_FAULT_TRUE=false \
  CAUSYNTH_HDFS_TEST_CLASS="${test_class}" \
  CAUSYNTH_HDFS_TEST_METHOD="${test_method}" \
    "${graphchecker_dir}/experiments/hdfs/hdfs-11741/run.sh" "$1"
}

verify_result() {
  python3 "${experiment_dir}/verify_result.py" --work-root "${work_root}"
}

case "${1:-prepare}" in
  prepare) prepare ;;
  traced-workload) traced_workload ;;
  tasks|schedule|candidates) delegate "$1" ;;
  verify) verify_result ;;
  full)
    prepare
    delegate tasks
    delegate candidates
    verify_result
    ;;
  config|validate)
    JAVA_HOME="${java8_home}" PATH="${java8_home}/bin:${PATH}" \
      GRAPH_CHECKER_JAVA="${java8_home}/bin/java" \
      CAUSYNTH_REPO="${hadoop_dir}" \
      "${graphchecker_dir}/run_engine.sh" --config "${workflow}" "$1"
    ;;
  *) die "usage: $0 [prepare|tasks|schedule|candidates|verify|full|config|validate|traced-workload]" ;;
esac
