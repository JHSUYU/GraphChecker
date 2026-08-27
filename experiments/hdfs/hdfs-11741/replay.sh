#!/usr/bin/env bash
#
# One concolic replay of the HDFS-11741 experiment.
#
# run_engine.sh's campaign owns the stage order and names this script as the
# workload adapter; the script is the bridge between the campaign's replay
# environment and source-first-launcher.sh's flags, and it contains no stage
# ordering of its own. pass.sh is the same bridge for a tracing pass; the two
# are separate because the passes are not interchangeable -- a tracing pass
# runs rewritten bytecode on a stock JIT JVM, and a replay runs the narrow
# concolic envelope of selected tasks on the Zero image.
#
# Environment supplied by the campaign:
#   CAUSYNTH_CONCOLIC_ROLE       session | worker
#   CAUSYNTH_CONCOLIC_TASK_PLAN  the immutable execution task plan
#   CAUSYNTH_CONCOLIC_TASK_ID    selected task ids (session: every member)
#   CAUSYNTH_CONCOLIC_RESULTS    where this replay writes its raw results
#   CAUSYNTH_CONCOLIC_CLASSES    the union-instrumented class tree
#   CAUSYNTH_CONCOLIC_WORKER_DIR this replay's isolated directory
#   CAUSYNTH_CONCOLIC_MAX_TASKS  frozen scheduler/replay task bound
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)

role=${CAUSYNTH_CONCOLIC_ROLE:-}
plan=${CAUSYNTH_CONCOLIC_TASK_PLAN:-}
ids=${CAUSYNTH_CONCOLIC_TASK_ID:-}
results=${CAUSYNTH_CONCOLIC_RESULTS:-}
classes=${CAUSYNTH_CONCOLIC_CLASSES:-}
worker=${CAUSYNTH_CONCOLIC_WORKER_DIR:-}
max_tasks=${CAUSYNTH_CONCOLIC_MAX_TASKS:-}

for required in role plan ids results classes worker max_tasks; do
  [[ -n "${!required}" ]] || {
    echo "replay adapter requires CAUSYNTH_CONCOLIC_${required^^}" >&2
    exit 2
  }
done
[[ -f "${plan}" ]] || { echo "no execution task plan: ${plan}" >&2; exit 2; }
[[ -d "${classes}" ]] || { echo "no concolic tree: ${classes}" >&2; exit 2; }

# Each replay owns its own launcher output root and MiniDFSCluster scratch
# tree. A DataNode takes a file lock on its storage directory, so two workers
# sharing one root would not be two fresh clusters at all.
output=${HDFS11741_OUTPUT:-${worker}/launcher}
# The Zero image's own default MaxHeapSize is 256 MB, which does not hold a
# MiniDFSCluster plus a symbolic session; the resulting OutOfMemoryError is
# caught while the VM serialises its summary, the run still exits 0, and the
# evidence is simply absent. Stating the heap is what keeps that silent
# failure out of the campaign.
heap=${CAUSYNTH_WORKLOAD_HEAP:-8g}

mkdir -p "${output}" "$(dirname -- "${results}")"

# The launcher reads the test-scope classpath the Hadoop build wrote, from its
# own output directory. This replay gets a private output directory so that
# each fresh cluster owns its storage lock, which means the build product is
# not already there -- so it is linked in rather than rebuilt, and a missing
# one is named here instead of surfacing as TEST_CLASSPATH_MISSING from inside
# the launcher.
build_output=${HDFS11741_BUILD_OUTPUT:-\
${repo_root}/experiments-output/hdfs-11741-session}
classpath_file=hadoop-test-classpath.txt
if [[ ! -f "${output}/${classpath_file}" ]]; then
  [[ -f "${build_output}/${classpath_file}" ]] || {
    echo "no ${classpath_file} in ${build_output}; run the launcher's build" \
      "command before a campaign" >&2
    exit 2
  }
  ln -sf "${build_output}/${classpath_file}" "${output}/${classpath_file}"
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
  # A worker replays one obligation. Stopping as soon as its selected result
  # is published keeps the wave's wall clock at one obligation rather than at
  # one full workload, and the campaign reads the published row, not the exit.
  properties+=("-Dcausynth.concolic.halt.after.selected.result=true")
fi

launch() {
  LAUNCHER_OUTPUT="${output}" \
  CAUSYNTH_ARTIFACT_MODE=concolic \
  CAUSYNTH_WORKLOAD_HEAP="${heap}" \
  LAUNCHER_JVM_ARGS="${properties[*]} ${HDFS11741_EXTRA_JVM_ARGS:-}" \
    "${repo_root}/experiments/hdfs/hdfs-11741/source-first-launcher.sh" \
      run --instrumented "${classes}" "$@"
}

exec_status=0
launch "$@" || exec_status=$?
exit ${exec_status}
