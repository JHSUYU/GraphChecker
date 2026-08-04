#!/usr/bin/env bash

set -euo pipefail

experiment_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${experiment_dir}/../../.." && pwd -P)
hadoop_dir=${HADOOP_REPO:-/opt/hadoop}
hdfs_pom="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/pom.xml"
patch_file="${experiment_dir}/patches/mark-fatal-target.patch"
workflow="${experiment_dir}/workflow.properties"
work_root="${graphchecker_dir}/target/hdfs-11741"
dependency_classpath="${work_root}/dependency-classpath.txt"
project_classpath="${work_root}/project-classpath.txt"
cached_protoc="${work_root}/tools/protoc-2.5.0"
base_commit=ece33208b89a6a06c1b362d10fab31343fe5df13
key_manager_rel=hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java
key_manager_source="${hadoop_dir}/${key_manager_rel}"
protoc_sha256=8b62bcf4d564e08c5bdd5d409c5e8462b07abadba10904946f63870dc9735f45
test_class=org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
test_method=testEncryptedBalancer1
test_selector="${test_class}#${test_method}"
test_report="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports/TEST-${test_class}.xml"

die() {
  echo "[hdfs-11741] $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 \
    || die "required command not found: $1"
}

require_file() {
  local label=$1
  local path=$2
  [[ -f "${path}" ]] || die "${label} not found: ${path}"
}

require_nonempty_file() {
  local label=$1
  local path=$2
  [[ -s "${path}" ]] || die "${label} is missing or empty: ${path}"
}

require_nonempty_directory() {
  local label=$1
  local path=$2
  local first_file
  [[ -d "${path}" ]] || die "${label} directory not found: ${path}"
  first_file=$(find "${path}" -type f -print -quit)
  [[ -n "${first_file}" ]] \
    || die "${label} directory contains no files: ${path}"
}

verify_checkout() {
  [[ -d "${hadoop_dir}/.git" ]] \
    || die "Hadoop checkout not found: ${hadoop_dir}"
  local head
  git -C "${hadoop_dir}" rev-parse --verify "${base_commit}^{commit}" \
    >/dev/null 2>&1 \
    || die "pre-fix Hadoop base is unavailable: ${base_commit}"
  head=$(git -C "${hadoop_dir}" rev-parse HEAD)
  git -C "${hadoop_dir}" merge-base --is-ancestor \
    "${base_commit}" "${head}" \
    || die "Hadoop HEAD ${head} is not based on pre-fix ${base_commit}"

  # Descendants used for tracing are allowed, but the committed experiment
  # semantics must retain the pre-fix KeyManager.  This admits the local
  # Causynth RPC trace commit without hard-coding its commit id, while
  # rejecting the upstream HDFS-11741 fix and any other KeyManager rewrite.
  git -C "${hadoop_dir}" diff --quiet \
    "${base_commit}..${head}" -- "${key_manager_rel}" \
    || die "Hadoop descendant modifies ${key_manager_rel}; HDFS-11741 requires the pre-fix KeyManager"

  require_file "KeyManager source" "${key_manager_source}"
  local key_method
  key_method=$(sed -n \
    '/public DataEncryptionKey newDataEncryptionKey()/,/^  }/p' \
    "${key_manager_source}")
  [[ -n "${key_method}" ]] \
    || die "cannot attest KeyManager.newDataEncryptionKey()"
  case "${key_method}" in
    *expiryDate*|*isExpired*|*timer.now*|*Time.now*)
      die "refusing fixed KeyManager: newDataEncryptionKey() checks key expiry"
      ;;
  esac
  case "${key_method}" in
    *'if (encryptionKey == null) {'*) ;;
    *) die "KeyManager.newDataEncryptionKey() no longer has the pre-fix null-only guard" ;;
  esac
}

marker_is_applied() {
  git -C "${hadoop_dir}" apply --reverse --check "${patch_file}" \
    >/dev/null 2>&1
}

do_patch() {
  verify_checkout
  if marker_is_applied; then
    echo "[hdfs-11741] fatal-target patch is already applied"
    return
  fi
  git -C "${hadoop_dir}" apply --check "${patch_file}" \
    || die "fatal-target patch does not apply cleanly"
  git -C "${hadoop_dir}" apply "${patch_file}"
  echo "[hdfs-11741] applied fatal-target patch"
}

verify_marker() {
  marker_is_applied \
    || die "fatal-target patch is not applied; run: $0 patch"
}

ensure_java8() {
  require_command java
  local version
  version=$(java -version 2>&1 | sed -n '1p')
  case "${version}" in
    *\"1.8.*) ;;
    *) die "Hadoop baseline requires Java 8; found: ${version}" ;;
  esac
}

ensure_protoc() {
  local protoc=${HADOOP_PROTOC_PATH:-${cached_protoc}}
  if [[ ! -x "${protoc}" && -n "${HADOOP_PROTOC_PATH:-}" ]]; then
    die "HADOOP_PROTOC_PATH is not executable: ${protoc}"
  fi
  if [[ ! -x "${protoc}" ]]; then
    require_command curl
    require_command sha256sum
    mkdir -p "$(dirname "${cached_protoc}")"
    local staging
    staging=$(mktemp -d /tmp/hdfs-11741-protoc.XXXXXX)
    echo "[hdfs-11741] downloading protoc 2.5.0" >&2
    curl -fsSL \
      https://repo.maven.apache.org/maven2/com/google/protobuf/protoc/2.5.0/protoc-2.5.0-linux-x86_64.exe \
      -o "${staging}/protoc"
    echo "${protoc_sha256}  ${staging}/protoc" | sha256sum -c - \
      >/dev/null
    chmod 755 "${staging}/protoc"
    mv "${staging}/protoc" "${cached_protoc}"
    rmdir "${staging}"
    protoc=${cached_protoc}
  fi
  local version
  version=$("${protoc}" --version)
  [[ "${version}" == "libprotoc 2.5.0" ]] \
    || die "expected libprotoc 2.5.0; found: ${version}"
  printf '%s\n' "${protoc}"
}

do_build() {
  verify_checkout
  verify_marker
  ensure_java8
  require_command mvn
  local protoc
  protoc=$(ensure_protoc)
  (
    cd "${hadoop_dir}"
    HADOOP_PROTOC_PATH="${protoc}" mvn \
      -pl hadoop-common-project/hadoop-annotations,hadoop-hdfs-project/hadoop-hdfs \
      -am -DskipTests install
  )
}

do_classpath() {
  verify_checkout
  verify_marker
  require_command mvn
  [[ -f "${hdfs_pom}" ]] || die "HDFS POM not found: ${hdfs_pom}"
  local main_classes="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/classes"
  local test_classes="${hadoop_dir}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes"
  [[ -d "${main_classes}" ]] || die "main classes not built; run: $0 build"
  [[ -d "${test_classes}" ]] || die "test classes not built; run: $0 build"
  mkdir -p "${work_root}"
  mvn -q -f "${hdfs_pom}" \
    -DincludeScope=test \
    -Dmdep.outputAbsoluteArtifactFilename=true \
    -Dmdep.outputFile="${dependency_classpath}" \
    dependency:build-classpath
  local dependencies
  dependencies=$(tr -d '\r\n' < "${dependency_classpath}")
  [[ -n "${dependencies}" ]] || die "Maven produced an empty classpath"
  printf '%s:%s:%s\n' \
    "${main_classes}" "${test_classes}" "${dependencies}" \
    >"${project_classpath}"
  local entry
  local entries=0
  while IFS= read -r entry; do
    [[ -e "${entry}" ]] || die "classpath entry does not exist: ${entry}"
    entries=$((entries + 1))
  done < <(tr ':' '\n' < "${project_classpath}")
  echo "[hdfs-11741] classpath ready: ${entries} entries"
  echo "[hdfs-11741] ${project_classpath}"
}

do_baseline() {
  verify_checkout
  verify_marker
  ensure_java8
  require_command mvn
  local protoc
  protoc=$(ensure_protoc)
  (
    cd "${hadoop_dir}"
    HADOOP_PROTOC_PATH="${protoc}" mvn -f "${hdfs_pom}" \
      -Dtest="${test_selector}" test
  )
  [[ -f "${test_report}" ]] \
    || die "Surefire report not found: ${test_report}"
  require_command rg
  local suite
  suite=$(sed -n '2p' "${test_report}")
  case "${suite}" in
    *'tests="1"'*'errors="0"'*'skipped="0"'*'failures="0"'*) ;;
    *) die "unexpected Surefire result: ${suite}" ;;
  esac
  rg -Fq "<testcase name=\"${test_method}\"" "${test_report}" \
    || die "Surefire report did not contain ${test_method}"
  echo "[hdfs-11741] baseline passed: ${test_selector}"
}

do_prepare() {
  do_patch
  do_build
  do_classpath
  do_baseline
}

verify_static_artifacts() {
  local analysis="${work_root}/analysis"
  require_nonempty_file "resolved target" \
    "${analysis}/target_resolved.json"
  require_nonempty_file "candidate dataflow graph" \
    "${analysis}/candidate_dataflow_edges.jsonl"
  require_nonempty_file "region skeleton archive" \
    "${analysis}/region_skeletons.jsonl.gz"
  # Static analysis creates these finalizer destinations.  Their rows are
  # runtime-selected, so an empty file is valid until the two-pass workload.
  require_file "symbolic regions placeholder" \
    "${analysis}/symbolic_regions.jsonl"
  require_file "symbolic region edges placeholder" \
    "${analysis}/symbolic_region_edges.jsonl"
  require_nonempty_directory "instrumented classes" \
    "${work_root}/instrumented-classes"
}

verify_runtime_artifacts() {
  local runtime="${work_root}/runtime"
  local skeleton="${runtime}/skeleton-pass"
  require_nonempty_file "pass-1 selected region skeletons" \
    "${skeleton}/region_skeletons.jsonl"
  require_nonempty_file "pass-1 runtime trace" \
    "${skeleton}/runtime_trace.jsonl"
  require_nonempty_file "pass-1 streaming manifest" \
    "${skeleton}/streaming_trace_manifest.json"
  require_nonempty_file "pass-2 runtime trace" \
    "${runtime}/runtime_trace.jsonl"
  require_nonempty_file "pass-2 streaming manifest" \
    "${runtime}/streaming_trace_manifest.json"
  require_nonempty_file "runtime-refined graph" \
    "${runtime}/refined_dataflow_edges.jsonl"
  require_nonempty_file "runtime-finalized symbolic regions" \
    "${work_root}/analysis/symbolic_regions.jsonl"
  # A valid refinement may contain no cross-region edge, so the JSONL
  # contract requires the edge artifacts to exist but not to have rows.
  require_file "runtime-finalized symbolic region edges" \
    "${work_root}/analysis/symbolic_region_edges.jsonl"
  require_nonempty_file "runtime region plan" \
    "${runtime}/concolic_region_plan.jsonl"
  require_file "runtime edge validations" \
    "${runtime}/runtime_region_edge_validation.jsonl"
}

verify_task_artifacts() {
  local schedule="${work_root}/schedule"
  local tasks="${schedule}/execution_task_plan.jsonl"
  require_command jq
  require_nonempty_file "concolic execution task plan" "${tasks}"
  require_file "branch query plan" "${schedule}/branch_queries.jsonl"
  jq -e -s '
    length > 0 and
    any(.[]; .admission.state == "EXECUTABLE") and
    all(.[];
      (.taskId | type == "string" and length > 0) and
      (.goalId | type == "string" and length > 0) and
      (.regionId | type == "string" and length > 0) and
      (.regionInstanceId | type == "string" and length > 0) and
      (.goalKind == "TARGET_REACH_CLOSURE" or
        .goalKind == "OUTPUT_RELATION_CLOSURE") and
      (.inputActions | type == "array") and
      (.branches | type == "array") and
      (.admission.state == "EXECUTABLE" or
        .admission.state == "BLOCKED") and
      .loopBound.schemaVersion == 1 and
      .loopBound.kind == "CFG_BACKEDGE" and
      .loopBound.scope == "ALL_EXECUTION_SCOPE_LOOPS" and
      (.loopBound.maxBackedgeTraversals | type == "number" and . >= 1) and
      .loopBound.onLimit == "CUT_PATH")
  ' "${tasks}" >/dev/null \
    || die "execution task plan failed identity/admission/loopBound validation: ${tasks}"
  if [[ -s "${schedule}/branch_queries.jsonl" ]]; then
    jq -e -s 'all(.[]; type == "object")' \
      "${schedule}/branch_queries.jsonl" >/dev/null \
      || die "branch query plan is not valid JSONL: ${schedule}/branch_queries.jsonl"
  fi
}

do_engine_config() {
  local command=$1
  [[ -s "${project_classpath}" ]] \
    || die "project classpath not found; run: $0 classpath"
  local classpath
  classpath=$(tr -d '\r\n' < "${project_classpath}")
  (
    cd "${graphchecker_dir}"
    CAUSYNTH_REPO="${hadoop_dir}" \
      CAUSYNTH_CLASSPATH="${classpath}" \
      ./run_engine.sh --config "${workflow}" "${command}"
  )
}

do_tasks() {
  verify_checkout
  verify_marker
  echo "[hdfs-11741] stage 1/3: static analysis"
  do_engine_config analyze
  verify_static_artifacts
  echo "[hdfs-11741] stage 2/3: two-pass runtime refinement"
  do_engine_config workload
  verify_runtime_artifacts
  echo "[hdfs-11741] stage 3/3: schedule concolic tasks"
  do_engine_config schedule
  verify_task_artifacts
  echo "[hdfs-11741] task preparation complete: ${work_root}/schedule/execution_task_plan.jsonl"
  echo "[hdfs-11741] stopped before concolic execution"
}

do_full_auto() {
  do_prepare
  do_engine_config build
  do_tasks
}

do_traced_workload() {
  [[ -s "${project_classpath}" ]] \
    || die "project classpath not found; run: $0 classpath"
  local instrumented="${graphchecker_dir}/target/hdfs-11741/instrumented-classes"
  local graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT.jar"
  local trace_dir="${graphchecker_dir}/target/hdfs-11741/runtime"
  local hadoop_log_dir="${graphchecker_dir}/target/hdfs-11741/hadoop-logs"
  [[ -d "${instrumented}" ]] \
    || die "instrumented classes not found; run analyze first"
  [[ -f "${graphchecker_jar}" ]] \
    || die "GraphChecker jar not found: ${graphchecker_jar}"
  local maven_repository
  maven_repository=$(mvn -q help:evaluate \
    -Dexpression=settings.localRepository -DforceStdout 2>/dev/null)
  local gson_jar="${maven_repository}/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar"
  [[ -f "${gson_jar}" ]] || die "GraphChecker Gson jar not found: ${gson_jar}"
  mkdir -p "${trace_dir}" "${hadoop_log_dir}"
  local classpath
  classpath=$(tr -d '\r\n' < "${project_classpath}")
  java \
    -Dcausynth.trace.output.dir="${trace_dir}" \
    -Dcausynth.trace.test="${test_class}.${test_method}" \
    -Dcausynth.trace.max.events=2000000 \
    -Dhadoop.log.dir="${hadoop_log_dir}" \
    -cp "${instrumented}:${gson_jar}:${classpath}:${graphchecker_jar}" \
    edu.uva.liftlab.graphchecker.runtime.JUnitMethodRunner \
    "${test_class}" "${test_method}"
}

case "${1:-prepare}" in
  patch) [[ $# -eq 1 ]] || die "patch takes no arguments"; do_patch ;;
  build) [[ $# -eq 1 ]] || die "build takes no arguments"; do_build ;;
  classpath) [[ $# -eq 1 ]] || die "classpath takes no arguments"; do_classpath ;;
  baseline) [[ $# -eq 1 ]] || die "baseline takes no arguments"; do_baseline ;;
  prepare) [[ $# -le 1 ]] || die "prepare takes no arguments"; do_prepare ;;
  config) [[ $# -eq 1 ]] || die "config takes no arguments"; do_engine_config config ;;
  validate) [[ $# -eq 1 ]] || die "validate takes no arguments"; do_engine_config validate ;;
  analyze) [[ $# -eq 1 ]] || die "analyze takes no arguments"; do_engine_config analyze ;;
  workload) [[ $# -eq 1 ]] || die "workload takes no arguments"; do_engine_config workload ;;
  tasks) [[ $# -eq 1 ]] || die "tasks takes no arguments"; do_tasks ;;
  full-auto) [[ $# -eq 1 ]] || die "full-auto takes no arguments"; do_full_auto ;;
  traced-workload)
    [[ $# -eq 1 ]] || die "traced-workload takes no arguments"
    do_traced_workload
    ;;
  *)
    die "usage: $0 [patch|build|classpath|baseline|prepare|config|validate|analyze|workload|tasks|full-auto|traced-workload]"
    ;;
esac
