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

verify_checkout() {
  [[ -d "${hadoop_dir}/.git" ]] \
    || die "Hadoop checkout not found: ${hadoop_dir}"
  local head
  head=$(git -C "${hadoop_dir}" rev-parse HEAD)
  [[ "${head}" == "${base_commit}" ]] \
    || die "Hadoop HEAD is ${head}; expected ${base_commit}"
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

do_traced_workload() {
  die "traced workload is not wired yet; the current step provides baseline only"
}

case "${1:-prepare}" in
  patch) [[ $# -eq 1 ]] || die "patch takes no arguments"; do_patch ;;
  build) [[ $# -eq 1 ]] || die "build takes no arguments"; do_build ;;
  classpath) [[ $# -eq 1 ]] || die "classpath takes no arguments"; do_classpath ;;
  baseline) [[ $# -eq 1 ]] || die "baseline takes no arguments"; do_baseline ;;
  prepare) [[ $# -le 1 ]] || die "prepare takes no arguments"; do_prepare ;;
  config) [[ $# -eq 1 ]] || die "config takes no arguments"; do_engine_config config ;;
  validate) [[ $# -eq 1 ]] || die "validate takes no arguments"; do_engine_config validate ;;
  analyze)
    [[ $# -eq 1 ]] || die "analyze takes no arguments"
    CAUSYNTH_INSTRUMENT_TRACE=true do_engine_config analyze
    ;;
  traced-workload)
    [[ $# -eq 1 ]] || die "traced-workload takes no arguments"
    do_traced_workload
    ;;
  *)
    die "usage: $0 [patch|build|classpath|baseline|prepare|config|validate|analyze]"
    ;;
esac
