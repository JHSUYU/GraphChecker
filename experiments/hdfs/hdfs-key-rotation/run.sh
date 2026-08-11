#!/usr/bin/env bash

set -euo pipefail

experiment_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${experiment_dir}/../../.." && pwd -P)
java17_home=${CAUSYNTH_JAVA17_HOME:-/tmp/jdk17}
java8_home=${CAUSYNTH_JAVA8_HOME:-/usr/lib/jvm/java-8-openjdk-amd64}

die() {
  echo "[hdfs-key-rotation] $*" >&2
  exit 1
}

case_config() {
  case "${case_id}" in
    hdfs-17897)
      hadoop_dir=${HADOOP_REPO:-/tmp/hdfs-17897-vulnerable}
      expected_head=156dd3b276457e49736638f1b57b05d78b558a7e
      test_class=org.apache.hadoop.hdfs.TestEncryptedTransfer
      test_method=testCausynthStripedFileChecksumRpcFailure
      ;;
    hdfs-17899-bug1)
      hadoop_dir=${HADOOP_REPO:-/tmp/hdfs-17899-vulnerable}
      expected_head=734dd8a67cd6df56b59ff75aa43de57834a0d248
      test_class=org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
      test_method=testEncryptedBalancer1
      ;;
    hdfs-17899-bug2)
      hadoop_dir=${HADOOP_REPO:-/tmp/hdfs-17899-vulnerable}
      expected_head=734dd8a67cd6df56b59ff75aa43de57834a0d248
      test_class=org.apache.hadoop.hdfs.server.sps.TestExternalStoragePolicySatisfier
      test_method=testCausynthSpsKeyRefreshRpcFailure
      ;;
    hdfs-17899-bug3)
      hadoop_dir=${HADOOP_REPO:-/tmp/hdfs-17899-vulnerable}
      expected_head=734dd8a67cd6df56b59ff75aa43de57834a0d248
      test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthDataTransferRpcFailure
      test_method=testReplicationAfterModeledKeyRefreshRpcFailure
      ;;
    *) die "unknown case: ${case_id}" ;;
  esac
  workflow="${graphchecker_dir}/experiments/hdfs/${case_id}/workflow.properties"
  work_root="${graphchecker_dir}/experiments-output/${case_id}"
  dependency_classpath="${work_root}/dependency-classpath.txt"
  project_classpath="${work_root}/project-classpath.txt"
}

configure_delegate() {
  export HADOOP_REPO="${hadoop_dir}"
  export HDFS11741_WORK_ROOT="${work_root}"
  export HDFS11741_REGION_JOBS=${CAUSYNTH_REGION_JOBS:-2}
  export HDFS11741_PATH_JOBS=${CAUSYNTH_PATH_JOBS:-2}
  export CAUSYNTH_HDFS_EXPERIMENT="${case_id}"
  export CAUSYNTH_HDFS_WORKFLOW="${workflow}"
  export CAUSYNTH_HDFS_TEST_CLASS="${test_class}"
  export CAUSYNTH_HDFS_TEST_METHOD="${test_method}"
  export CAUSYNTH_REQUIRE_EXPLICIT_FAULT_TRUE=true
}

verify_checkout() {
  [[ "$(git -C "${hadoop_dir}" rev-parse --is-inside-work-tree 2>/dev/null)" == true ]] \
    || die "Hadoop checkout not found: ${hadoop_dir}"
  [[ "$(git -C "${hadoop_dir}" rev-parse HEAD)" == "${expected_head}" ]] \
    || die "${case_id} requires Hadoop ${expected_head}"
  [[ -f "${workflow}" ]] || die "workflow not found: ${workflow}"
  rg -q 'class CausynthFault' \
    "${hadoop_dir}/hadoop-common-project/hadoop-annotations/src/main/java/edu/uva/liftlab/graphchecker/annotation/CausynthFault.java" \
    || die "Causynth fault marker is not installed"
  rg -q "CausynthExceptionTarget\(\"${case_id%%-bug*}\"\)" \
    "${hadoop_dir}/hadoop-hdfs-project" \
    || die "fatal target marker for ${case_id} is not installed"
}

build_hadoop() {
  [[ -x "${java17_home}/bin/java" ]] || die "Java 17 not found: ${java17_home}"
  mkdir -p "${work_root}"
  (
    cd "${hadoop_dir}"
    JAVA_HOME="${java17_home}" PATH="${java17_home}/bin:${PATH}" \
      mvn -q -pl hadoop-hdfs-project/hadoop-hdfs -am \
        -Djavac.version=8 -DskipTests -DskipShade -DskipITs \
        -Dspotbugs.skip -Dcheckstyle.skip -Denforcer.skip=true install
  )
  "${java17_home}/bin/javap" -verbose \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.class" \
    | rg -q 'major version: 52' \
    || die "HDFS classes are not Java 8 bytecode"
}

prepare_process_classes() {
  local source_class target_dir
  source_class="${hadoop_dir}/hadoop-common-project/hadoop-common/target/classes/org/apache/hadoop/security/token/delegation/DelegationKey.class"
  target_dir="${hadoop_dir}/target/causynth-process-classes/org/apache/hadoop/security/token/delegation"
  [[ -f "${source_class}" ]] \
    || die "DelegationKey bytecode is missing; run prepare first"
  mkdir -p "${target_dir}"
  cp "${source_class}" "${target_dir}/DelegationKey.class"
}

build_classpath() {
  local hdfs_pom="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/pom.xml"
  mkdir -p "${work_root}"
  JAVA_HOME="${java17_home}" PATH="${java17_home}/bin:${PATH}" \
    mvn -q -f "${hdfs_pom}" -DincludeScope=test \
      -Dmdep.outputAbsoluteArtifactFilename=true \
      -Dmdep.outputFile="${dependency_classpath}" \
      dependency:build-classpath
  local dependencies
  dependencies=$(tr -d '\r\n' <"${dependency_classpath}")
  [[ -n "${dependencies}" ]] || die "Maven produced an empty classpath"
  printf '%s:%s:%s\n' \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes" \
    "${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes" \
    "${dependencies}" >"${project_classpath}"
}

build_graphchecker() {
  (cd "${graphchecker_dir}" && mvn -q -DskipTests package)
}

run_java8_baseline() {
  local classpath gson_jar baseline_root
  classpath=$(tr -d '\r\n' <"${project_classpath}")
  gson_jar="/users/ZhenyuLi/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar"
  [[ -f "${gson_jar}" ]] || die "GraphChecker Gson runtime not found: ${gson_jar}"
  baseline_root="${work_root}/baseline"
  mkdir -p "${baseline_root}/test-data" "${baseline_root}/java-tmp" \
    "${baseline_root}/hadoop-logs"
  (
    cd "${graphchecker_dir}"
    "${java8_home}/bin/java" \
      -Dcausynth.junit.exit.after.run=true \
      -Dcausynth.junit.ignore.timeout=true \
      -Dcausynth.replay.block.key.serial.seed=17899 \
      -Dtest.build.data="${baseline_root}/test-data" \
      -Djava.io.tmpdir="${baseline_root}/java-tmp" \
      -Dhadoop.log.dir="${baseline_root}/hadoop-logs" \
      -cp "${gson_jar}:${classpath}:${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar" \
      edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
      "${test_class}" "${test_method}"
  )
}

delegate() {
  prepare_process_classes
  configure_delegate
  exec "${graphchecker_dir}/experiments/hdfs/hdfs-11741/run.sh" "$1"
}

do_prepare() {
  verify_checkout
  build_graphchecker
  build_hadoop
  prepare_process_classes
  build_classpath
  run_java8_baseline
  echo "[hdfs-key-rotation] Java 8 baseline passed: ${case_id} ${test_class}#${test_method}"
}

if [[ "${1:-}" == traced-workload ]]; then
  [[ $# -eq 2 ]] || die "usage: $0 traced-workload <case>"
  case_id=$2
  command=traced-workload
else
  [[ $# -eq 2 ]] || die "usage: $0 <case> <prepare|baseline|tasks|schedule|candidates|full>"
  case_id=$1
  command=$2
fi
case_config

case "${command}" in
  prepare) do_prepare ;;
  baseline) verify_checkout; run_java8_baseline ;;
  tasks|schedule|candidates) verify_checkout; delegate "${command}" ;;
  full)
    do_prepare
    configure_delegate
    "${graphchecker_dir}/experiments/hdfs/hdfs-11741/run.sh" tasks
    "${graphchecker_dir}/experiments/hdfs/hdfs-11741/run.sh" candidates
    ;;
  traced-workload) verify_checkout; delegate traced-workload ;;
  *) die "unknown command: ${command}" ;;
esac
