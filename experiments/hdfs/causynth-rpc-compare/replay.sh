#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
role=${CAUSYNTH_CONCOLIC_ROLE:?missing concolic role}
plan=${CAUSYNTH_CONCOLIC_TASK_PLAN:?missing task plan}
ids=${CAUSYNTH_CONCOLIC_TASK_ID:?missing task ids}
results=${CAUSYNTH_CONCOLIC_RESULTS:?missing result path}
classes=${CAUSYNTH_CONCOLIC_CLASSES:?missing concolic classes}
worker=${CAUSYNTH_CONCOLIC_WORKER_DIR:?missing worker directory}
max_tasks=${CAUSYNTH_CONCOLIC_MAX_TASKS:?missing task bound}
output=${RPC_COMPARE_OUTPUT:-${worker}/launcher}
build_output=${RPC_COMPARE_BUILD_OUTPUT:-${repo_root}/experiments-output/causynth-rpc-compare}

mkdir -p "${output}" "$(dirname -- "${results}")"
if [[ ! -f "${output}/hadoop-test-classpath.txt" ]]; then
  [[ -f "${build_output}/hadoop-test-classpath.txt" ]]
  ln -sf "${build_output}/hadoop-test-classpath.txt" \
    "${output}/hadoop-test-classpath.txt"
fi

properties=(
  "-Dcausynth.concolic.task.plan=${plan}"
  "-Dcausynth.concolic.task.id=${ids}"
  "-Dcausynth.concolic.results=${results}"
  "-Dcausynth.concolic.diagnostics=false"
  "-Dcausynth.concolic.campaign.max.tasks=${max_tasks}"
)
if [[ -n "${CAUSYNTH_PROTOCOL_STUBS:-}" ]]; then
  properties+=("-Dcausynth.protocol.stubs=${CAUSYNTH_PROTOCOL_STUBS}")
fi
if [[ "${role}" == "worker" ]]; then
  properties+=("-Dcausynth.concolic.halt.after.selected.result=true")
fi

LAUNCHER_OUTPUT="${output}" \
CAUSYNTH_ARTIFACT_MODE=concolic \
CAUSYNTH_WORKLOAD_HEAP=4g \
LAUNCHER_JVM_ARGS="${properties[*]}" \
  exec "${repo_root}/experiments/hdfs/causynth-rpc-compare/source-first-launcher.sh" \
    run --instrumented "${classes}" "$@"
