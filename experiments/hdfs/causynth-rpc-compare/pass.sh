#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
output=${RPC_COMPARE_OUTPUT:-${repo_root}/experiments-output/causynth-rpc-compare}
instrumented=${CAUSYNTH_INSTRUMENTED_CLASSES_DIR:?missing instrumented classes}
trace_dir=${CAUSYNTH_TRACE_OUTPUT_DIR:?missing trace directory}
trace_jdk=${RPC_COMPARE_TRACE_JDK:-/usr/lib/jvm/java-8-openjdk-amd64}
stub_arg=""
if [[ -n "${CAUSYNTH_PROTOCOL_STUBS:-}" ]]; then
  stub_arg="-Dcausynth.protocol.stubs=${CAUSYNTH_PROTOCOL_STUBS}"
fi

LAUNCHER_OUTPUT="${output}" \
CAUSYNTH_JDK_HOME="${trace_jdk}" \
CAUSYNTH_ARTIFACT_MODE=discovery \
LAUNCHER_JVM_ARGS="-Dcausynth.trace.max.events=5000000 ${stub_arg}" \
  exec "${repo_root}/experiments/hdfs/causynth-rpc-compare/source-first-launcher.sh" \
    run --instrumented "${instrumented}" --trace-dir "${trace_dir}" "$@"
