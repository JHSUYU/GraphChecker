#!/bin/bash
# GraphChecker — HDFS workflow script
#
# Usage:
#   ./run_hdfs.sh build
#   ./run_hdfs.sh compile
#   ./run_hdfs.sh instrument
#   ./run_hdfs.sh test [TestClass[#method]]
#   ./run_hdfs.sh run  [TestClass[#method]]
#   ./run_hdfs.sh restore

set -euo pipefail

# ── Resolve directories ───────────────────────────────────────────────────────
script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
gc_dir=$(realpath "${script_dir}/../..")
conf="${script_dir}/conf/hdfs.properties"
gc_jar="${gc_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

# ── Load config (gives us hdfs_dir, system_dir_path, system_classes_path,
#                         instrumented_classes_path, java_class_path)
if [[ ! -f "${conf}" ]]; then
    echo "[ERROR] Config not found: ${conf}"
    exit 1
fi
source "${conf}"

# ── Banner ────────────────────────────────────────────────────────────────────
echo ""
echo "  ╔══════════════════════════════════════════╗"
echo "  ║   GraphChecker — HDFS Workflow Script    ║"
echo "  ╚══════════════════════════════════════════╝"
echo ""
echo "  gc_dir:                   ${gc_dir}"
echo "  hdfs_dir:                 ${hdfs_dir}"
echo "  original_classes (input): ${system_dir_path}"
echo "  instrumented classes:     ${instrumented_classes_path}"
echo ""

# ── Usage ─────────────────────────────────────────────────────────────────────
usage() {
    echo "Usage: ./run_hdfs.sh <command> [options]"
    echo ""
    echo "  Commands:"
    echo "    build                         Build GraphChecker jar"
    echo "    build-hadoop                  Build required Hadoop modules (generates classpath JARs)"
    echo "    compile                       Compile HDFS main + test sources"
    echo "    instrument                    Instrument HDFS classes in-place"
    echo "    test [TestClass[#method]]     Run HDFS unit tests (no recompile)"
    echo "    run  [TestClass[#method]]     instrument + test in sequence"
    echo "    restore                       Recompile HDFS to restore original classes"
    echo ""
    echo "  Examples:"
    echo "    ./run_hdfs.sh instrument"
    echo "    ./run_hdfs.sh test org.apache.hadoop.hdfs.TestDFSClientRetries"
    echo "    ./run_hdfs.sh test org.apache.hadoop.hdfs.TestDFSClientRetries#testGetFileChecksum"
    echo "    ./run_hdfs.sh run  org.apache.hadoop.hdfs.TestDFSClientRetries"
    echo "    ./run_hdfs.sh restore"
}

# ── timing helper ─────────────────────────────────────────────────────────────
timing() {
    local label=$1; shift
    local start=$SECONDS
    "$@"
    echo "[Profiler] ${label} took $((SECONDS - start))s"
}

# ── Commands ──────────────────────────────────────────────────────────────────

do_build() {
    echo "==> Building GraphChecker..."
    mvn -f "${gc_dir}/pom.xml" clean package -DskipTests
    echo "==> Built: ${gc_jar}"
}

do_build_hadoop() {
    local hadoop_root
    hadoop_root=$(realpath "${hdfs_dir}/../..")
    echo "==> Building required Hadoop modules (DskipTests)..."
    echo "    Hadoop root: ${hadoop_root}"
    # Build only the modules referenced in java_class_path, in dependency order.
    # -am also builds any upstream modules they depend on.
    mvn -f "${hadoop_root}/pom.xml" install -DskipTests -Pdist \
        -pl hadoop-common-project/hadoop-common,\
hadoop-common-project/hadoop-kms,\
hadoop-hdfs-project/hadoop-hdfs-client,\
hadoop-hdfs-project/hadoop-hdfs \
        -am
    echo "==> Hadoop modules built."
}

do_compile() {
    echo "==> Compiling HDFS (main + test sources)..."
    mvn -f "${hdfs_dir}/pom.xml" \
        compile test-compile \
        -DskipTests

    echo "==> Snapshotting original classes → ${system_classes_path}"
    rm -rf "${system_classes_path}"
    mkdir -p "${system_classes_path}"
    rsync -a "${hdfs_dir}/target/classes/" "${system_classes_path}/"
    echo "==> Snapshot done."
}

do_instrument() {
    if [[ ! -f "${gc_jar}" ]]; then
        echo "[ERROR] GraphChecker jar not found: ${gc_jar}"
        echo "        Run './run_hdfs.sh build' first."
        exit 1
    fi
    if [[ ! -d "${system_classes_path}" ]]; then
        echo "[ERROR] Original classes snapshot not found: ${system_classes_path}"
        echo "        Run './run_hdfs.sh compile' first."
        exit 1
    fi

    rm -rf "${instrumented_classes_path}"
    mkdir -p "${instrumented_classes_path}"

    echo "==> Instrumenting HDFS classes..."
    echo "    input:  ${system_classes_path}"
    echo "    output: ${instrumented_classes_path}"

    java -cp "${gc_jar}:${java_class_path}" \
        edu.uva.liftlab.graphchecker.GraphCheckerMain \
        -i "${system_classes_path}" \
        -x "${java_class_path}" \
        -C "${conf}" \
        -o "${instrumented_classes_path}"

    echo "==> Deploying instrumented classes → ${hdfs_dir}/target/classes"
    find "${hdfs_dir}/target/classes" -name "*.class" -delete
    cp -r "${instrumented_classes_path}/." "${hdfs_dir}/target/classes/"
    echo "==> Instrumentation done."
}

do_test() {
    local test_name="${1:-}"
    local test_arg=""
    if [[ -n "${test_name}" ]]; then
        test_arg="-Dtest=${test_name}"
        echo "==> Running test: ${test_name}"
    else
        echo "==> Running all HDFS unit tests"
    fi

    # surefire:test runs the Surefire plugin directly, skipping compile phases
    # so the instrumented classes in hdfs_dir/target/classes/ are used as-is
    cd "${hdfs_dir}"
    mvn surefire:test \
        ${test_arg} \
        -DfailIfNoTests=false \
        -Dhadoop.log.dir="${hdfs_dir}/target/test-logs"
}

do_restore() {
    echo "==> Restoring original HDFS classes by recompiling..."
    mvn -f "${hdfs_dir}/pom.xml" \
        compile \
        -DskipTests
    echo "==> Restore done."
}

# ── Dispatch ──────────────────────────────────────────────────────────────────
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
    instrument)
        timing "instrument" do_instrument
        ;;
    test)
        timing "test" do_test "${1:-}"
        ;;
    run)
        timing "instrument" do_instrument
        timing "test"       do_test "${1:-}"
        ;;
    restore)
        timing "restore" do_restore
        ;;
    help|--help|-h)
        usage
        ;;
    *)
        echo "[ERROR] Unknown command: ${cmd}"
        echo ""
        usage
        exit 1
        ;;
esac