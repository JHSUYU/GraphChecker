#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
graphchecker_jar=${GRAPHCHECKER_JAR:-${repo_root}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar}
hadoop_home=${HADOOP_HOME_DIR:-/opt/hadoop}
jdk_home=${CAUSYNTH_JDK_HOME:-${CAUSYNTH_CUSTOM_JDK_HOME:-${repo_root}/third_party/OpenJDK-Concolic-Execution-Engine/build/linux-x86_64-normal-zero-release/images/j2sdk-image}}
output_dir=${LAUNCHER_OUTPUT:-${repo_root}/experiments-output/causynth-rpc-compare}
gson_jar=${GRAPHCHECKER_GSON_JAR:-${HOME}/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar}
read -r -a launcher_jvm_args <<< "${LAUNCHER_JVM_ARGS:-}"

[[ $# -ge 1 ]] || { echo "usage: $0 build|run [args]" >&2; exit 2; }
command=$1
shift
common=(
  --hadoop-home "${hadoop_home}"
  --output-dir "${output_dir}"
  --exception-target-id causynth-rpc-compare
)

case "${command}" in
  build)
    exec java "${launcher_jvm_args[@]}" -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.launcher.SourceTestLauncher build \
      "${common[@]}" "$@"
    ;;
  run)
    if [[ "${CAUSYNTH_ARTIFACT_MODE:-}" == "concolic" ]]; then
      export _JAVA_OPTIONS="-Xmx${CAUSYNTH_WORKLOAD_HEAP:?missing workload heap}"
    fi
    exec java "${launcher_jvm_args[@]}" -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.launcher.SourceTestLauncher run \
      "${common[@]}" \
      --test-class org.apache.hadoop.hdfs.TestCausynthRpcHeaderPropagation \
      --test-method nameNodeComparesValuesReadOnceFromTwoDataNodes \
      --jdk-home "${jdk_home}" \
      --target-classes "${hadoop_home}/hadoop-hdfs-project/hadoop-hdfs/target/classes/org/apache/hadoop/hdfs/server/namenode" \
      --conf-defaults-class org.apache.hadoop.hdfs.HdfsConfiguration \
      --graphchecker-lib "${gson_jar}" "$@"
    ;;
  *)
    echo "unknown command: ${command}" >&2
    exit 2
    ;;
esac
