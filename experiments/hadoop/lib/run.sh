#!/usr/bin/env bash
# run.sh <case-dir> <case-id> build|config|validate|campaign [args...]
#
# The one launcher: the case's declarations become the campaign's
# environment, and run_engine.sh runs the case's workflow.properties.
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?usage: run.sh <case-dir> <case-id> <command>}" "${2-}"
command=${3:?missing command}
shift 3
if [[ "${command}" == build ]]; then
  exec bash "${lib}/build.sh" "${repo}" "${test_class}" "${test_method}" \
    "${hadoop_javac}"
fi

export CAUSYNTH_REPO=${repo}
export CAUSYNTH_MODULE_DIR=${module}
export CAUSYNTH_CLASSES_DIR=${analysis}
export CAUSYNTH_TEST_CLASSES_DIR=${module}/target/test-classes
export CAUSYNTH_CLASSPATH
CAUSYNTH_CLASSPATH=$(bash "${lib}/classpath.sh" "${case_dir}" "${case_id}")
export CAUSYNTH_OUTPUT_DIR=${CAUSYNTH_OUTPUT_DIR:-/tmp/graphchecker-${tag}}
export CAUSYNTH_CACHE_DIR=${CAUSYNTH_CACHE_DIR:-/tmp/graphchecker-${tag}-cache}
export CAUSYNTH_LOOP_BOUNDS=${loop_bounds}
export CAUSYNTH_TARGET_SPEC=${target_spec}
export CAUSYNTH_WORKLOAD_WORK_DIR=${repo}
export CAUSYNTH_TRACE_TEST=${test_name}
export CAUSYNTH_TARGET_OCCURRENCE=${target_occurrence}
export CAUSYNTH_WORKLOAD_COMMAND="${lib}/execute.sh ${case_dir} ${case_id}"
export CAUSYNTH_CONCOLIC_REPLAY_COMMAND="${lib}/execute.sh ${case_dir} ${case_id}"
export CAUSYNTH_CAMPAIGN_SETUP_COMMAND="${lib}/prepare-analysis.sh ${case_dir} ${case_id}"
export GRAPH_CHECKER_JAVA=${GRAPH_CHECKER_JAVA:-${lib}/java.sh}
exec "${lib}/../../../run_engine.sh" --config "${case_dir}/workflow.properties" \
  "${command}" "$@"
