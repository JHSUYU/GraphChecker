#!/usr/bin/env bash
# run.sh <case-dir> <case-id> build|config|validate|slice|record|campaign [args...]
#
# The one launcher: the case's declarations become the campaign's
# environment, and run_engine.sh runs the case's workflow.properties.
set -euo pipefail
lib=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${lib}/case-env.sh" "${1:?usage: run.sh <case-dir> <case-id> <command>}" "${2-}"
command=${3:?missing command}
shift 3
if [[ "${command}" == build ]]; then
  system_build
  exit
fi

export CAUSYNTH_REPO=${repo}
export CAUSYNTH_MODULE_DIR=${module}
export CAUSYNTH_CLASSES_DIR=${analysis}
export CAUSYNTH_LINEAGE_ROOTS=${lineage_roots}
# A system's own doors (experiments/<system>/doors.jsonl), which replace the
# engine catalog's of their transport and direction (SYMBOL-SCOPE §4.2).
export CAUSYNTH_SYSTEM_DOORS=
[[ ! -f "${system_dir}/doors.jsonl" ]] \
  || CAUSYNTH_SYSTEM_DOORS=${system_dir}/doors.jsonl
export CAUSYNTH_TEST_CLASSES_DIR=${test_classes}
export CAUSYNTH_CLASSPATH
# A reader of a recorded run (tools/regress/offline-ab.sh `config`) states the
# classpath that run froze: the tree's surefire report may be gone since.
# A campaign never sets it -- execute.sh reads the report either way.
CAUSYNTH_CLASSPATH=${CAUSYNTH_CLASSPATH_OVERRIDE:-$(bash "${lib}/classpath.sh" \
  "${case_dir}" "${case_id}")}
export CAUSYNTH_OUTPUT_DIR=${output_dir}
# A case directory without a target.yaml runs on the throw its tree marks with
# the case's id (tools/lib/annotated.py): the spec is derived from the tree,
# never kept by hand, and stays with the run's output.
if [[ ! -f ${target_spec} ]]; then
  mkdir -p "${CAUSYNTH_OUTPUT_DIR}"
  target_spec=${CAUSYNTH_OUTPUT_DIR}/declared-target.yaml
  python3 "${lib}/../../tools/lib/annotated.py" "${system_dir}" "${repo}" \
    "${tag}" >"${target_spec}.partial"
  mv -- "${target_spec}.partial" "${target_spec}"
fi
export CAUSYNTH_LOOP_BOUNDS=${loop_bounds}
export CAUSYNTH_TARGET_SPEC=${target_spec}
export CAUSYNTH_WORKLOAD_WORK_DIR=${repo}
export CAUSYNTH_TRACE_TEST=${test_name}
export CAUSYNTH_TARGET_OCCURRENCE=${target_occurrence}
export CAUSYNTH_WORKLOAD_COMMAND="${lib}/execute.sh ${case_dir} ${case_id}"
export CAUSYNTH_CONCOLIC_REPLAY_COMMAND="${lib}/execute.sh ${case_dir} ${case_id}"
export CAUSYNTH_CAMPAIGN_SETUP_COMMAND="${lib}/prepare-analysis.sh ${case_dir} ${case_id}"
export GRAPH_CHECKER_JAVA=${GRAPH_CHECKER_JAVA:-${lib}/java.sh}
exec "${lib}/../../run_engine.sh" --config "${case_dir}/workflow.properties" \
  "${command}" "$@"
