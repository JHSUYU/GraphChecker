#!/usr/bin/env bash
#
# One traced workload pass of the HDFS-11741 experiment.
#
# run_engine.sh's region/workload stages run the configured workload command
# once per pass and then aggregate whatever landed in the trace directory.
# This script is that command: it is the two-line bridge between the stage
# chain's environment and source-first-launcher.sh's flags, and it contains no
# stage ordering of its own.
#
# The pass runs on a stock JVM. A tracing pass executes rewritten bytecode and
# records method envelopes, branches, calls and field accesses; none of that
# needs symbolic execution, and the concolic image would only make the pass
# slower. The concolic image is for the replay stage, which is not this one.
#
# Environment:
#   HDFS11741_OUTPUT       launcher output root
#   CAUSYNTH_INSTRUMENTED_CLASSES_DIR rewritten classes for this pass
#   CAUSYNTH_TRACE_OUTPUT_DIR         this generation's streaming trace root
#   HDFS11741_TRACE_JDK    JVM that executes the pass
#   HDFS11741_MAX_EVENTS   streaming trace event cap; the recorder marks the
#                          trace INCOMPLETE past it and the aggregator then
#                          refuses it, so this is a fail-closed budget rather
#                          than a silent truncation
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)

# The launcher's output root holds the small per-run records and the
# MiniDFSCluster scratch tree, and stays on local disk: a DataNode takes a file
# lock on its storage directory and NFS is the wrong place for that. The trace
# directory and the analysis artifacts are the multi-gigabyte half and live on
# the project volume, because the root filesystem has under 2 GB free.
output=${HDFS11741_OUTPUT:-${repo_root}/experiments-output/hdfs-11741-session}
instrumented=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?run_engine did not name the rewritten classes for this pass}
trace_dir=${CAUSYNTH_TRACE_OUTPUT_DIR:?run_engine did not name the trace root for this generation}
trace_jdk=${HDFS11741_TRACE_JDK:-/usr/lib/jvm/java-8-openjdk-amd64}
max_events=${HDFS11741_MAX_EVENTS:-100000000}

# The stage chain passes the protocol endpoint declarations in the
# environment. The launcher forwards every causynth.* system property set on
# itself to the workload, so naming it as a property here is what carries it
# into the JVM that actually records the exchanges, rather than leaving the
# workload to depend on environment inheritance through three processes.
stub_arg=""
if [[ -n "${CAUSYNTH_PROTOCOL_STUBS:-}" ]]; then
  stub_arg="-Dcausynth.protocol.stubs=${CAUSYNTH_PROTOCOL_STUBS}"
fi

LAUNCHER_OUTPUT="${output}" \
CAUSYNTH_JDK_HOME="${trace_jdk}" \
CAUSYNTH_ARTIFACT_MODE=discovery \
LAUNCHER_JVM_ARGS="-Dcausynth.trace.max.events=${max_events} ${stub_arg} ${HDFS11741_EXTRA_JVM_ARGS:-}" \
  exec "${repo_root}/experiments/hdfs/hdfs-11741/source-first-launcher.sh" run \
    --instrumented "${instrumented}" \
    --trace-dir "${trace_dir}" \
    "$@"
