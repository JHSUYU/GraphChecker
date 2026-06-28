#!/bin/bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
gc_dir=$(realpath "${script_dir}/../..")
conf="${script_dir}/conf/hdfs.properties"
gc_jar="${gc_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

if [[ ! -f "${conf}" ]]; then
    echo "[ERROR] Config not found: ${conf}"
    exit 1
fi
source "${conf}"

usage() {
    echo "Usage: ./run_hdfs.sh <command> [options]"
    echo ""
    echo "Commands:"
    echo "  build                         Build GraphChecker jar"
    echo "  build-hadoop                  Build required Hadoop modules"
    echo "  compile                       Compile HDFS and snapshot original classes"
    echo "  process                       Run the empty Soot transformer"
    echo "  test [TestClass[#method]]     Run HDFS unit tests"
    echo "  run [TestClass[#method]]      process + test"
    echo "  restore                       Recompile HDFS to restore original classes"
}

timing() {
    local label=$1
    shift
    local start=$SECONDS
    "$@"
    echo "[Profiler] ${label} took $((SECONDS - start))s"
}

do_build() {
    mvn -f "${gc_dir}/pom.xml" clean package -DskipTests
}

do_build_hadoop() {
    local hadoop_root
    hadoop_root=$(realpath "${hdfs_dir}/../..")
    mvn -f "${hadoop_root}/pom.xml" install -DskipTests -Pdist \
        -pl hadoop-common-project/hadoop-common,\
hadoop-common-project/hadoop-kms,\
hadoop-hdfs-project/hadoop-hdfs-client,\
hadoop-hdfs-project/hadoop-hdfs \
        -am
}

do_compile() {
    mvn -f "${hdfs_dir}/pom.xml" compile test-compile -DskipTests
    rm -rf "${system_classes_path}"
    mkdir -p "${system_classes_path}"
    rsync -a "${hdfs_dir}/target/classes/" "${system_classes_path}/"
}

do_process() {
    if [[ ! -f "${gc_jar}" ]]; then
        echo "[ERROR] GraphChecker jar not found: ${gc_jar}"
        echo "Run './run_hdfs.sh build' first."
        exit 1
    fi
    if [[ ! -d "${system_classes_path}" ]]; then
        echo "[ERROR] Original classes snapshot not found: ${system_classes_path}"
        echo "Run './run_hdfs.sh compile' first."
        exit 1
    fi

    rm -rf "${instrumented_classes_path}"
    mkdir -p "${instrumented_classes_path}"

    java -cp "${gc_jar}:${java_class_path}" \
        edu.uva.liftlab.graphchecker.GraphCheckerMain \
        -i "${system_classes_path}" \
        -x "${java_class_path}" \
        -C "${conf}" \
        -o "${instrumented_classes_path}"

    find "${hdfs_dir}/target/classes" -name "*.class" -delete
    cp -r "${instrumented_classes_path}/." "${hdfs_dir}/target/classes/"
}

do_test() {
    local test_name="${1:-}"
    local test_arg=""
    if [[ -n "${test_name}" ]]; then
        test_arg="-Dtest=${test_name}"
    fi

    cd "${hdfs_dir}"
    mvn surefire:test \
        ${test_arg} \
        -DfailIfNoTests=false \
        -Dhadoop.log.dir="${hdfs_dir}/target/test-logs"
}

do_restore() {
    mvn -f "${hdfs_dir}/pom.xml" compile -DskipTests
}

cmd="${1:-help}"
shift || true

case "${cmd}" in
    build)
        timing "build" do_build
        ;;
    build-hadoop)
        timing "build-hadoop" do_build_hadoop
        ;;
    compile)
        timing "compile" do_compile
        ;;
    process|instrument)
        timing "process" do_process
        ;;
    test)
        timing "test" do_test "${1:-}"
        ;;
    run)
        timing "process" do_process
        timing "test" do_test "${1:-}"
        ;;
    restore)
        timing "restore" do_restore
        ;;
    help|--help|-h)
        usage
        ;;
    *)
        echo "[ERROR] Unknown command: ${cmd}"
        usage
        exit 1
        ;;
esac
