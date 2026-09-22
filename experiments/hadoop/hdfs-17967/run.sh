#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
case_id=${1:?usage: run.sh pathA|pathB|pathC build|config|validate|campaign}
command=${2:?missing command}
shift 2
source "${here}/case.sh" "${case_id}"
if [[ "${command}" == build ]]; then
  exec "${here}/build.sh" "${case_id}" "$@"
fi

export CAUSYNTH_REPO=${repo}
export CAUSYNTH_MODULE_DIR=${module}
export CAUSYNTH_CLASSES_DIR=${analysis}
export CAUSYNTH_TEST_CLASSES_DIR=${module}/target/test-classes
export CAUSYNTH_CLASSPATH
CAUSYNTH_CLASSPATH=$("${here}/classpath.sh" "${case_id}")
export CAUSYNTH_OUTPUT_DIR=${CAUSYNTH_OUTPUT_DIR:-/tmp/graphchecker-hdfs-17967-${case_id}}
export CAUSYNTH_CACHE_DIR=${CAUSYNTH_CACHE_DIR:-/tmp/graphchecker-hdfs-17967-${case_id}-cache}
export CAUSYNTH_ANALYSIS_SCOPE=hdfs-17967-${case_id}
export CAUSYNTH_LOOP_BOUNDS=${loop_bounds}
export CAUSYNTH_WORKLOAD_WORK_DIR=${repo}
export CAUSYNTH_WORKLOAD_COMMAND="${here}/execute.sh ${case_id}"
export CAUSYNTH_TRACE_TEST=${test_name}
export CAUSYNTH_TARGET_OCCURRENCE=${target_occurrence}
# Path C is a different annotated site, so a different target id.
export CAUSYNTH_TARGET_SPEC=${target_spec}
export CAUSYNTH_CAMPAIGN_SETUP_COMMAND="${here}/prepare-analysis.sh ${case_id}"
export CAUSYNTH_CONCOLIC_REPLAY_COMMAND="${here}/execute.sh ${case_id}"
exec "${here}/../../../run_engine.sh" --config "${here}/workflow.properties" \
  "${command}" "$@"
