#!/usr/bin/env bash

set -euo pipefail

graphchecker_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
default_graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

config_file=""
config_dir="${graphchecker_dir}"

usage() {
  cat <<'EOF'
Usage:
  ./run_engine.sh --config FILE campaign
  ./run_engine.sh --config FILE catalog
  ./run_engine.sh --config FILE config|validate
  ./run_engine.sh help

Commands:
  campaign    Run the complete campaign for one configuration: validate, seed,
              then immutable iterations of plan/instrument/replay/import/
              explore/classify until composition and Z3
  catalog     Run through the first immutable PLAN only and stop after writing
              symbolic_root_mechanism_cards.json for external classification
  config      Print the normalized workflow configuration
  validate    Validate required workflow configuration fields
  help        Print this help message

Environment variables matching normalized workflow keys may override values
loaded from FILE.
EOF
}

die() {
  echo "Error: $*" >&2
  exit 1
}

trim() {
  local value=$1
  value="${value#"${value%%[![:space:]]*}"}"
  value="${value%"${value##*[![:space:]]}"}"
  printf '%s' "${value}"
}

known_config_key() {
  case "$1" in
    workflow_path_base|graphchecker_jar|java_bin|graphchecker_work_dir|project_repo|project_module_dir|project_classes_dir|project_test_classes_dir|project_classpath|analysis_classes_dir|causynth_output_dir|causynth_cache_dir|causynth_target_spec|causynth_analysis_scope|causynth_process_dirs|causynth_communication_mappings|causynth_loop_bounds|causynth_symbolic_inputs|causynth_symbolic_root_proposal|custom_jdk_home|z3_bin|workload_work_dir|workload_command|trace_test|candidate_graph|refined_graph|runtime_region_plan|schedule_output_dir|schedule_max_jobs|solver_timeout_ms|reach_max_inputs|reach_max_valuations|campaign_setup_command|concolic_replay_command|concolic_worker_count|campaign_max_iterations|producer_max_paths_per_region|producer_max_flips_per_path|producer_max_path_tasks)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

reset_config() {
  workflow_path_base=""
  graphchecker_jar=""
  java_bin=""
  graphchecker_work_dir=""
  project_repo=""
  project_module_dir=""
  project_classes_dir=""
  project_test_classes_dir=""
  project_classpath=""
  analysis_classes_dir=""
  causynth_output_dir=""
  causynth_cache_dir=""
  causynth_target_spec=""
  causynth_analysis_scope=""
  causynth_process_dirs=""
  causynth_communication_mappings=""
  causynth_loop_bounds=""
  causynth_symbolic_inputs=""
  causynth_symbolic_root_proposal=""
  custom_jdk_home=""
  z3_bin=""
  workload_work_dir=""
  workload_command=""
  trace_test=""
  candidate_graph=""
  refined_graph=""
  runtime_region_plan=""
  schedule_output_dir=""
  # Internal campaign paths. They are derived from the immutable iteration and
  # are not workflow/CLI override points.
  schedule_summaries=""
  schedule_max_jobs=""
  solver_timeout_ms=""
  reach_max_inputs=""
  reach_max_valuations=""
  campaign_setup_command=""
  concolic_replay_command=""
  concolic_worker_count=""
  campaign_max_iterations=""
  producer_max_paths_per_region=""
  producer_max_flips_per_path=""
  producer_max_path_tasks=""
}

# Workflow configs deliberately use a small key=value grammar. Unknown
# keys remain available to GraphChecker through -C but are not evaluated by the
# shell. This keeps a target config from changing PATH, HOME, IFS, or shell
# control variables.
load_config_file() {
  local path=$1
  local raw key value
  while IFS= read -r raw || [[ -n "${raw}" ]]; do
    raw=$(trim "${raw}")
    [[ -z "${raw}" || "${raw}" == \#* ]] && continue
    [[ "${raw}" == *=* ]] || continue
    key=$(trim "${raw%%=*}")
    value=$(trim "${raw#*=}")
    known_config_key "${key}" || continue
    if [[ ${#value} -ge 2 ]]; then
      if [[ "${value:0:1}" == '"' && "${value: -1}" == '"' ]] \
          || [[ "${value:0:1}" == "'" && "${value: -1}" == "'" ]]; then
        value=${value:1:${#value}-2}
      fi
    fi
    printf -v "${key}" '%s' "${value}"
  done < "${path}"
}

apply_env_override() {
  local target=$1
  local source=$2
  if [[ -n "${!source+x}" ]]; then
    printf -v "${target}" '%s' "${!source}"
  fi
}

apply_environment_overrides() {
  apply_env_override workflow_path_base GRAPH_CHECKER_PATH_BASE
  apply_env_override graphchecker_jar GRAPH_CHECKER_JAR
  apply_env_override java_bin GRAPH_CHECKER_JAVA
  apply_env_override graphchecker_work_dir GRAPH_CHECKER_WORK_DIR
  apply_env_override project_repo CAUSYNTH_REPO
  apply_env_override project_module_dir CAUSYNTH_MODULE_DIR
  apply_env_override project_classes_dir CAUSYNTH_CLASSES_DIR
  apply_env_override project_test_classes_dir CAUSYNTH_TEST_CLASSES_DIR
  apply_env_override project_classpath CAUSYNTH_CLASSPATH
  apply_env_override analysis_classes_dir CAUSYNTH_INSTRUMENTED_CLASSES_DIR
  apply_env_override causynth_output_dir CAUSYNTH_OUTPUT_DIR
  apply_env_override causynth_cache_dir CAUSYNTH_CACHE_DIR
  apply_env_override causynth_target_spec CAUSYNTH_TARGET_SPEC
  apply_env_override causynth_analysis_scope CAUSYNTH_ANALYSIS_SCOPE
  apply_env_override causynth_process_dirs CAUSYNTH_PROCESS_DIRS
  apply_env_override causynth_communication_mappings CAUSYNTH_COMMUNICATION_MAPPINGS
  apply_env_override causynth_loop_bounds CAUSYNTH_LOOP_BOUNDS
  apply_env_override causynth_symbolic_inputs CAUSYNTH_SYMBOLIC_INPUTS
  apply_env_override causynth_symbolic_root_proposal \
    CAUSYNTH_SYMBOLIC_ROOT_PROPOSAL
  apply_env_override custom_jdk_home CAUSYNTH_CUSTOM_JDK_HOME
  apply_env_override z3_bin CAUSYNTH_Z3
  apply_env_override workload_work_dir CAUSYNTH_WORKLOAD_WORK_DIR
  apply_env_override workload_command CAUSYNTH_WORKLOAD_COMMAND
  apply_env_override trace_test CAUSYNTH_TRACE_TEST
  apply_env_override candidate_graph CAUSYNTH_CANDIDATE_GRAPH
  apply_env_override refined_graph CAUSYNTH_REFINED_GRAPH
  apply_env_override runtime_region_plan CAUSYNTH_REGION_PLAN
  apply_env_override schedule_output_dir CAUSYNTH_SCHEDULE_OUTPUT_DIR
  apply_env_override schedule_max_jobs CAUSYNTH_SCHEDULE_MAX_JOBS
  apply_env_override solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS
  apply_env_override reach_max_inputs CAUSYNTH_REACH_MAX_INPUTS
  apply_env_override reach_max_valuations CAUSYNTH_REACH_MAX_VALUATIONS
  apply_env_override campaign_setup_command CAUSYNTH_CAMPAIGN_SETUP_COMMAND
  apply_env_override concolic_replay_command CAUSYNTH_CONCOLIC_REPLAY_COMMAND
  apply_env_override concolic_worker_count CAUSYNTH_CONCOLIC_JOBS
  apply_env_override campaign_max_iterations CAUSYNTH_CAMPAIGN_MAX_ITERATIONS
  apply_env_override producer_max_paths_per_region \
    CAUSYNTH_PRODUCER_MAX_PATHS_PER_REGION
  apply_env_override producer_max_flips_per_path \
    CAUSYNTH_PRODUCER_MAX_FLIPS_PER_PATH
  apply_env_override producer_max_path_tasks CAUSYNTH_PRODUCER_MAX_PATH_TASKS
}

canonical_path() {
  realpath -m -- "$1"
}

resolve_path() {
  local raw=$1
  local fallback_base=${2:-${workflow_path_base}}
  local candidate
  [[ -n "${raw}" ]] || return 0
  case "${raw}" in
    /*) candidate=${raw} ;;
    @config/*) candidate="${config_dir}/${raw#@config/}" ;;
    @project/*|@graphchecker/*)
      candidate="${graphchecker_dir}/${raw#*/}"
      ;;
    @repo/*)
      [[ -n "${project_repo}" ]] || die "@repo path used before project_repo is resolved: ${raw}"
      candidate="${project_repo}/${raw#@repo/}"
      ;;
    *)
      case "${fallback_base}" in
        config) candidate="${config_dir}/${raw}" ;;
        project|graphchecker) candidate="${graphchecker_dir}/${raw}" ;;
        repo)
          [[ -n "${project_repo}" ]] || die "workflow_path_base=repo requires project_repo"
          candidate="${project_repo}/${raw}"
          ;;
        *) die "workflow_path_base must be config, project, graphchecker, or repo" ;;
      esac
      ;;
  esac
  canonical_path "${candidate}"
}

resolve_executable() {
  local raw=$1
  [[ -n "${raw}" ]] || return 0
  case "${raw}" in
    */*|@*) resolve_path "${raw}" ;;
    *) printf '%s\n' "${raw}" ;;
  esac
}

resolve_path_list() {
  local raw=$1
  local result=""
  local entry resolved
  local -a entries
  IFS=':' read -r -a entries <<< "${raw}"
  for entry in "${entries[@]}"; do
    [[ -n "${entry}" ]] || continue
    resolved=$(resolve_path "${entry}")
    if [[ -z "${result}" ]]; then
      result=${resolved}
    else
      result="${result}:${resolved}"
    fi
  done
  printf '%s\n' "${result}"
}

initialize_config() {
  local requested=${1:-}
  reset_config
  if [[ -n "${requested}" ]]; then
    [[ -f "${requested}" ]] || die "config file not found: ${requested}"
    config_dir=$(cd "$(dirname "${requested}")" && pwd -P)
    config_file="${config_dir}/$(basename "${requested}")"
    load_config_file "${config_file}"
  else
    config_dir=${graphchecker_dir}
    config_file=""
  fi
  apply_environment_overrides

  workflow_path_base=${workflow_path_base:-project}
  graphchecker_jar=${graphchecker_jar:-${default_graphchecker_jar}}
  java_bin=${java_bin:-java}
  graphchecker_work_dir=${graphchecker_work_dir:-@project/.}

  project_repo=${project_repo:-@project/.}
  project_repo=$(resolve_path "${project_repo}" "${workflow_path_base}")
  project_module_dir=${project_module_dir:-${project_repo}}
  project_classes_dir=${project_classes_dir:-@repo/target/classes}
  project_test_classes_dir=${project_test_classes_dir:-@repo/target/test-classes}
  project_classpath=${project_classpath:-}
  causynth_output_dir=${causynth_output_dir:-@project/target/causynth-workflow}
  causynth_cache_dir=${causynth_cache_dir:-@project/.causynth-cache}
  causynth_target_spec=${causynth_target_spec:-@config/target.yaml}
  analysis_classes_dir=${analysis_classes_dir:-${causynth_output_dir}/instrumented-classes}
  custom_jdk_home=${custom_jdk_home:-}
  z3_bin=${z3_bin:-z3}
  workload_work_dir=${workload_work_dir:-${project_module_dir}}
  concolic_worker_count=${concolic_worker_count:-8}
  # Scheduler, solver and topology bounds have no engine defaults.
  # The production workload states them in its frozen configuration.

  graphchecker_jar=$(resolve_path "${graphchecker_jar}")
  graphchecker_work_dir=$(resolve_path "${graphchecker_work_dir}")
  project_module_dir=$(resolve_path "${project_module_dir}" repo)
  project_classes_dir=$(resolve_path "${project_classes_dir}" repo)
  project_test_classes_dir=$(resolve_path "${project_test_classes_dir}" repo)
  causynth_output_dir=$(resolve_path "${causynth_output_dir}")
  causynth_cache_dir=$(resolve_path "${causynth_cache_dir}")
  causynth_target_spec=$(resolve_path "${causynth_target_spec}")
  analysis_classes_dir=$(resolve_path "${analysis_classes_dir}")
  custom_jdk_home=$(resolve_path "${custom_jdk_home}")
  workload_work_dir=$(resolve_path "${workload_work_dir}" repo)
  java_bin=$(resolve_executable "${java_bin}")
  z3_bin=$(resolve_executable "${z3_bin}")

  if [[ -z "${project_classpath}" ]]; then
    project_classpath="${project_classes_dir}:${project_test_classes_dir}"
  else
    project_classpath=$(resolve_path_list "${project_classpath}")
  fi
  if [[ -n "${causynth_process_dirs}" ]]; then
    causynth_process_dirs=$(resolve_path_list "${causynth_process_dirs}")
  fi
  if [[ -n "${causynth_communication_mappings}" ]]; then
    causynth_communication_mappings=$(resolve_path "${causynth_communication_mappings}")
  fi
  if [[ -n "${causynth_loop_bounds}" ]]; then
    causynth_loop_bounds=$(resolve_path "${causynth_loop_bounds}")
  fi
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    causynth_symbolic_inputs=$(resolve_path "${causynth_symbolic_inputs}")
  fi
  if [[ -n "${causynth_symbolic_root_proposal:-}" ]]; then
    causynth_symbolic_root_proposal=$(resolve_path \
      "${causynth_symbolic_root_proposal}")
  fi
  candidate_graph=${candidate_graph:-${causynth_output_dir}/candidate_dataflow_edges.jsonl.gz}
  runtime_region_plan=${runtime_region_plan:-${causynth_output_dir}/runtime/concolic_region_plan.jsonl}
  refined_graph=${refined_graph:-$(dirname "${runtime_region_plan}")/refined_dataflow_edges.jsonl.gz}
  schedule_output_dir=${schedule_output_dir:-${causynth_output_dir}/schedule}
  candidate_graph=$(resolve_path "${candidate_graph}")
  refined_graph=$(resolve_path "${refined_graph}")
  runtime_region_plan=$(resolve_path "${runtime_region_plan}")
  schedule_output_dir=$(resolve_path "${schedule_output_dir}")
}

require_file() {
  [[ -f "$2" ]] || die "$1 not found: $2"
}

require_directory() {
  [[ -d "$2" ]] || die "$1 directory not found: $2"
}

ensure_output_directory() {
  mkdir -p "$1"
}

run_in_directory() {
  local directory=$1
  shift
  require_directory "working" "${directory}"
  (cd "${directory}" && "$@")
}

run_java_main() {
  local main_class=$1
  shift
  require_file "GraphChecker jar" "${graphchecker_jar}"
  local runtime_classpath="${graphchecker_jar}"
  if [[ "${main_class}" == \
      edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder ]]; then
    # Boundary-scalar validation resolves configured client interfaces to the
    # concrete callees recorded in the trace.  Keep that hierarchy available
    # to this offline aggregation process just as it was to the recorder.
    runtime_classpath="${runtime_classpath}:${project_classpath}"
  fi
  run_in_directory "${graphchecker_work_dir}" "${java_bin}" \
    -cp "${runtime_classpath}" "${main_class}" "$@"
}

print_normalized_config() {
  local key
  for key in campaign_setup_command concolic_replay_command concolic_worker_count campaign_max_iterations producer_max_paths_per_region producer_max_flips_per_path producer_max_path_tasks config_file workflow_path_base graphchecker_jar java_bin graphchecker_work_dir project_repo project_module_dir project_classes_dir project_test_classes_dir project_classpath analysis_classes_dir causynth_output_dir causynth_cache_dir causynth_target_spec causynth_process_dirs causynth_communication_mappings causynth_loop_bounds causynth_symbolic_inputs causynth_symbolic_root_proposal custom_jdk_home z3_bin workload_work_dir workload_command trace_test candidate_graph refined_graph runtime_region_plan schedule_output_dir schedule_max_jobs solver_timeout_ms reach_max_inputs reach_max_valuations; do
    printf '%s=%s\n' "${key}" "${!key}"
  done
}

validate_config() {
  local key
  local missing=0
  for key in project_repo project_module_dir project_classes_dir project_classpath causynth_output_dir causynth_cache_dir causynth_target_spec custom_jdk_home z3_bin workload_command trace_test causynth_loop_bounds; do
    if [[ -z "${!key}" ]]; then
      echo "Missing workflow config value: ${key}" >&2
      missing=1
    fi
  done
  [[ ${missing} -eq 0 ]] || return 1
  # README section "Loops": no retained condition-controlled loop may inherit
  # the core default, so the per-loop K_L declarations belong to the workload's
  # frozen configuration. The key is required rather than optional because an
  # absent key and a campaign whose declarations never arrived are the same
  # run: every retained loop silently models an 8-body prefix and nothing in
  # the published artifacts says so. A workload that retains no condition loop
  # still names a file -- one holding no rows -- because "none" is a statement
  # and an absent key is only silence.
  require_file "loop body bound declarations" "${causynth_loop_bounds}"
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
  fi
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
  fi
  if [[ -n "${causynth_symbolic_root_proposal:-}" ]]; then
    require_file "symbolic root proposal" \
      "${causynth_symbolic_root_proposal}"
  fi
  case "${solver_timeout_ms}" in
    ''|*[!0-9]*) die "solver_timeout_ms must be a positive integer" ;;
    0) die "solver_timeout_ms must be greater than zero" ;;
  esac
  case "${schedule_max_jobs}" in
    ''|*[!0-9]*) die "schedule_max_jobs must be a positive integer" ;;
    0) die "schedule_max_jobs must be greater than zero" ;;
  esac
  case "${reach_max_inputs}" in
    ''|*[!0-9]*) die "reach_max_inputs must be a positive integer" ;;
    0) die "reach_max_inputs must be greater than zero" ;;
  esac
  case "${reach_max_valuations}" in
    ''|*[!0-9]*) die "reach_max_valuations must be a positive integer" ;;
    0) die "reach_max_valuations must be greater than zero" ;;
  esac
  case "${concolic_worker_count}" in
    ''|*[!0-9]*) die "concolic_worker_count must be a positive integer" ;;
    0) die "concolic_worker_count must be greater than zero" ;;
  esac
  case "${campaign_max_iterations}" in
    ''|*[!0-9]*) die "campaign_max_iterations must be a positive integer" ;;
    0) die "campaign_max_iterations must be greater than zero" ;;
  esac
  local bound
  for bound in "${producer_max_paths_per_region}" \
      "${producer_max_flips_per_path}" "${producer_max_path_tasks}"; do
    [[ -z "${bound}" ]] && continue
    case "${bound}" in
      *[!0-9]*|0) die "producer path bounds must be positive integers: ${bound}" ;;
    esac
  done
  echo "Workflow configuration is valid."
}

do_analyze() {
  require_file "target specification" "${causynth_target_spec}"
  local input_flag
  local concolic_plan=${CAUSYNTH_CONCOLIC_TASK_PLAN:-}
  local concolic_task_ids=${CAUSYNTH_CONCOLIC_TASK_ID:-}
  local concolic_selected=false

  # A task plan plus selected ids is the complete authority for a narrow
  # concolic instrumentation pass. Partial task selection is refused before
  # Soot starts.
  if [[ -n "${concolic_plan}" || -n "${concolic_task_ids}" ]]; then
    [[ -n "${concolic_plan}" && -n "${concolic_task_ids}" ]] \
      || die "concolic instrumentation requires both CAUSYNTH_CONCOLIC_TASK_PLAN and CAUSYNTH_CONCOLIC_TASK_ID"
    require_file "concolic execution task plan" "${concolic_plan}"
    concolic_selected=true
  fi
  if [[ -d "${project_classes_dir}" ]]; then
    input_flag=-i
  elif [[ -f "${project_classes_dir}" ]]; then
    input_flag=-j
  else
    die "project classes input not found: ${project_classes_dir}"
  fi
  ensure_output_directory "${analysis_classes_dir}"
  local -a system_properties
  system_properties=(
    "-Dcausynth.output.dir=${causynth_output_dir}"
    "-Dcausynth.target.spec=${causynth_target_spec}"
  )
  if [[ -n "${trace_test}" ]]; then
    system_properties+=("-Dcausynth.trace.test=${trace_test}")
  fi
  if [[ -n "${causynth_analysis_scope}" ]]; then
    system_properties+=("-Dcausynth.analysis.scope=${causynth_analysis_scope}")
  fi
  if [[ -n "${causynth_process_dirs}" ]]; then
    system_properties+=("-Dcausynth.process.dirs=${causynth_process_dirs}")
  fi
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
    system_properties+=(
      "-Dcausynth.communication.mappings=${causynth_communication_mappings}"
    )
  fi
  # README section 5's per-loop K_L, declared by the campaign that owns the
  # workload. The declarations are read by the static pass that retains the
  # loops, so they are named here rather than inherited from whatever
  # environment happened to reach the JVM: a campaign whose declarations
  # silently failed to arrive would model an 8-body prefix and report nothing
  # about it. The requirement is unconditional, like the target specification
  # above it -- an unset key used to skip the check entirely, which is exactly
  # the run this comment claimed to refuse. A configured file that does not
  # exist is a die, not a fallback.
  require_file "loop body bound declarations" "${causynth_loop_bounds}"
  system_properties+=(
    "-Dcausynth.loop.bounds=${causynth_loop_bounds}"
  )
  if [[ -n "${CAUSYNTH_TRACE_MODE:-}" ]]; then
    system_properties+=(
      "-Dcausynth.trace.mode=${CAUSYNTH_TRACE_MODE}"
    )
  fi
  if [[ -n "${CAUSYNTH_REGION_SKELETONS:-}" ]]; then
    system_properties+=(
      "-Dcausynth.region.skeletons=${CAUSYNTH_REGION_SKELETONS}"
    )
  fi
  if [[ "${concolic_selected}" == true ]]; then
    system_properties+=(
      "-Dcausynth.instrument.concolic=true"
      "-Dcausynth.concolic.task.plan=${concolic_plan}"
      "-Dcausynth.concolic.task.id=${concolic_task_ids}"
    )
  fi
  require_file "GraphChecker jar" "${graphchecker_jar}"
  run_in_directory "${graphchecker_work_dir}" "${java_bin}" \
    "${system_properties[@]}" \
    -cp "${graphchecker_jar}:${project_classpath}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    "${input_flag}" "${project_classes_dir}" \
    -x "${project_classpath}" \
    -C "${config_file}" \
    -o "${analysis_classes_dir}" "$@"
}

do_schedule() {
  local region_plan="${runtime_region_plan}"
  require_file "runtime region plan" "${region_plan}"
  ensure_output_directory "${schedule_output_dir}"
  local -a args
  args=(
    --region-plan "${region_plan}"
    --output-dir "${schedule_output_dir}"
  )
  require_file "runtime-refined graph" "${refined_graph}"
  args+=(--refined-graph "${refined_graph}")
  # The cap on how many candidates become replay jobs is stated, never
  # inherited. Left unstated the scheduler falls back to one job, which keeps
  # the first candidate of the plan and drops the rest; a schedule of one task
  # is not an empty schedule, so the stage exits 0 and the truncation is
  # invisible until a downstream stage refuses an artifact nobody wrote. An
  # empty or non-numeric value would reach the parser as a bare flag and be
  # read back as that same one, so it dies here instead.
  case "${schedule_max_jobs}" in
    ''|*[!0-9]*)
      die "schedule_max_jobs must be a positive integer: '${schedule_max_jobs}'" ;;
    0) die "schedule_max_jobs must be greater than zero" ;;
  esac
  args+=(--max-jobs "${schedule_max_jobs}")
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
    args+=(--symbolic-inputs "${causynth_symbolic_inputs}")
  fi
  if [[ -n "${causynth_symbolic_root_proposal:-}" ]]; then
    require_file "symbolic root proposal" \
      "${causynth_symbolic_root_proposal}"
    args+=(--symbolic-root-proposal \
      "${causynth_symbolic_root_proposal}")
  fi
  if [[ -n "${schedule_summaries}" ]]; then
    require_file "scheduler summaries" "${schedule_summaries}"
    args+=(--summaries "${schedule_summaries}")
  fi
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler \
    "${args[@]}" "$@"
}

do_import() {
  local iteration_id=${1:-} key status=0 restore_errexit=0
  [[ -n "${iteration_id//[[:space:]]/}" ]] \
    || die "import iteration id is required"
  shift
  require_file "raw concolic results" "${raw_concolic_results}"
  require_file "import activation plan" "${import_task_plan}"
  require_file "runtime region plan" "${runtime_region_plan}"
  ensure_output_directory "$(dirname "${imported_summaries}")"
  key=$(campaign_import_cache_key "${iteration_id}")
  campaign_cached_import_status=0
  if campaign_restore_import_cache "${key}"; then
    campaign_log "cache hit IMPORT key=${key}"
    return "${campaign_cached_import_status}"
  fi
  campaign_log "cache miss IMPORT key=${key}"
  [[ $- == *e* ]] && restore_errexit=1
  set +e
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter \
    --results "${raw_concolic_results}" \
    --task-plan "${import_task_plan}" \
    --runtime-plan "${runtime_region_plan}" \
    --output "${imported_summaries}" \
    --diagnostics "${import_diagnostics}" \
    ${import_topology_delta:+--topology-delta "${import_topology_delta}"} \
    --iteration-id "${iteration_id}" "$@"
  status=$?
  [[ "${restore_errexit}" -eq 0 ]] || set -e
  campaign_store_import_cache "${key}" "${status}"
  return "${status}"
}

append_path_list_arguments() {
  local option=$1
  local values=$2
  local entry
  local -a entries
  IFS=':' read -r -a entries <<< "${values}"
  for entry in "${entries[@]}"; do
    [[ -n "${entry}" ]] || continue
    require_file "${option#--}" "${entry}"
    PATH_LIST_ARGUMENTS+=("${option}" "${entry}")
  done
}

do_compose() {
  # The reach query path is handed over whether or not it exists: whether the
  # target published one is the Composer's acceptance decision, and it names
  # the absence as its own refusal row.
  ensure_output_directory "$(dirname "${composed_smt}")"
  PATH_LIST_ARGUMENTS=()
  # Each named summary must exist -- that is the immutable-path check the shell
  # owns. Whether the named set states a closed path set is the Composer's
  # acceptance gate, so an empty set is composed and refused there rather than
  # stopped here.
  append_path_list_arguments --summaries "${compose_summary_inputs}"
  local -a selection
  selection=()
  [[ -z "${fatal_region}" ]] || selection+=(--fatal-region "${fatal_region}")
  [[ -z "${fatal_occurrence_id}" ]] \
    || selection+=(--occurrence-id "${fatal_occurrence_id}")
  require_file "runtime region plan" "${runtime_region_plan}"
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer \
    --fatal-query "${fatal_queries}" \
    "${PATH_LIST_ARGUMENTS[@]}" \
    --runtime-plan "${runtime_region_plan}" \
    --output "${composed_smt}" \
    --manifest "${composition_manifest}" \
    "${selection[@]}" "$@"
}

do_reach() {
  require_file "composed SMT" "${composed_smt}"
  require_file "composition manifest" "${composition_manifest}"
  require_file "runtime region plan" "${runtime_region_plan}"
  ensure_output_directory "$(dirname "${reach_report}")"
  run_java_main edu.uva.liftlab.graphchecker.concolic.BooleanReachConditionExtractor \
    --smt "${composed_smt}" \
    --manifest "${composition_manifest}" \
    --runtime-plan "${runtime_region_plan}" \
    --output "${reach_report}" \
    --z3 "${z3_bin}" \
    --timeout-ms "${solver_timeout_ms}" \
    --max-inputs "${reach_max_inputs}" \
    --max-valuations "${reach_max_valuations}" "$@"
}

run_configured_workload() {
  local -a workload_env
  local trace_dir
  trace_dir=$(dirname "${runtime_region_plan}")
  workload_env=(
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    "CAUSYNTH_INSTRUMENTED_CLASSES_DIR=${analysis_classes_dir}"
    "CAUSYNTH_TRACE_OUTPUT_DIR=${trace_dir}"
  )
  (cd "${workload_work_dir}" && \
    env "${workload_env[@]}" bash -lc "${workload_command}")
}

do_regions() {
  [[ -n "${workload_command}" ]] || die "workload_command is empty"
  require_directory "workload working" "${workload_work_dir}"
  local trace_dir
  trace_dir=$(dirname "${runtime_region_plan}")
  local skeleton_pass="${trace_dir}/skeleton-pass"
  local candidate_skeletons="${causynth_output_dir}/region_skeletons.jsonl.gz"
  local selected_skeletons="${skeleton_pass}/region_skeletons.jsonl"
  require_file "candidate region skeletons" "${candidate_skeletons}"
  ensure_output_directory "${trace_dir}"
  ensure_output_directory "${skeleton_pass}"

  # Pass 1: method activation envelopes only.
  run_configured_workload
  run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" \
    --region-skeletons "${candidate_skeletons}" \
    --region-skeleton-only true \
    --output-dir "${skeleton_pass}" \
    --test "${trace_test}"
  require_file "runtime-selected region skeletons" "${selected_skeletons}"

  # Preserve pass-1 evidence and leave the configured trace directory clean
  # for the state pass.
  mv "${trace_dir}/runtime_trace.jsonl" \
    "${skeleton_pass}/runtime_trace.jsonl"
  mv "${trace_dir}/streaming_trace_manifest.json" \
    "${skeleton_pass}/streaming_trace_manifest.json"
}

do_workload() {
  do_regions
  local trace_dir
  trace_dir=$(dirname "${runtime_region_plan}")
  local selected_skeletons="${trace_dir}/skeleton-pass/region_skeletons.jsonl"

  # Pass 2: re-instrument only selected region methods, then collect rich
  # calls, branches, arguments and every direct declared-field access. Keep
  # the lite classes intact so a failed or repeated workload starts from the
  # same pass-1 instrumentation instead of accidentally tracing REGION_STATE.
  local skeleton_class_backup
  skeleton_class_backup=$(mktemp -d /tmp/graphchecker-skeleton-classes.XXXXXX)
  cp -a "${analysis_classes_dir}/." "${skeleton_class_backup}/"
  (
    restore_skeleton_classes() {
      cp -a "${skeleton_class_backup}/." "${analysis_classes_dir}/"
      rm -rf -- "${skeleton_class_backup}"
    }
    trap restore_skeleton_classes EXIT
    CAUSYNTH_TRACE_MODE=region-state \
      CAUSYNTH_REGION_SKELETONS="${selected_skeletons}" \
      do_analyze
    run_configured_workload
    run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
      --trace-dir "${trace_dir}" \
      --candidate-graph "${candidate_graph}" \
      --region-skeletons "${selected_skeletons}" \
      --refined-graph "${refined_graph}" \
      --test "${trace_test}"
  )
}

# ---------------------------------------------------------------------------
# Production campaign
#
# `campaign` is the one external entry point for a whole run. It validates the
# configuration, freezes the generation's provenance, records the stock-JVM
# seed, and then drives immutable iterations of plan -> union instrumentation
# -> one fresh same-JVM causal campaign -> strict import -> bounded parallel
# worker obligations -> classification, until the topology stops changing and
# the composition can be solved.
#
# It is an orchestrator, not a second semantic engine. Every artifact it
# publishes was written by a production owner; the shell only validates
# immutable paths, digests and task-set membership, launches stages, and sorts
# and names what they wrote. It never infers a relation, rewrites a schema,
# correlates a message, builds an expression, or emits an SMT term -- and it
# never re-decides an admission a semantic owner already made. A task the
# shell finds skipped or incomplete is named as a terminal gap and travels to
# the classifier and the Composer, which are the layers that know whether it
# sits inside the frozen selected target closure.
#
# Two directory rules hold everywhere below: an iteration or worker directory
# is written once and never rewritten, and every consumer is handed the exact
# path it must read. `latest` is a diagnostic symlink and is never read back.
# ---------------------------------------------------------------------------

campaign_root=""
campaign_final=""
campaign_stage_metrics=""
campaign_provenance=""
campaign_delta_rows=0
campaign_delta_divergences=0
# This iteration's task-set membership, decoded once by PLAN from the frozen
# schedule index (README "Minimal cross-stage contract": one owner per check).
# IMPORT, EXPLORE, the iteration manifest and COMPOSE read these rows; they do
# not re-decode the index, because re-deriving the same membership at five
# stages is five chances to disagree about one frozen file that is written
# once and never rewritten.
campaign_member_rows=""

campaign_log() {
  printf '[campaign] %s\n' "$*"
}

campaign_fail() {
  local stage=$1 component=$2 artifact=$3
  shift 3
  {
    echo "[campaign:error]"
    echo "  stage=${stage}"
    echo "  component=${component}"
    echo "  artifact=${artifact}"
    echo "  reason=$*"
  } >&2
  exit 1
}

# The failure this tree has paid for more than once: a stage exits 0 after
# writing nothing, and the next stage reports a different, later problem. Every
# required output is checked for content and the check names the path.
require_nonempty() {
  [[ -s "$2" ]] || die "$1 is missing or empty: $2"
}

# Existence is not evidence that this pass produced it; a previous pass's
# leftover satisfies it just as well. The marker is stamped when the stage
# starts, so an artifact older than the marker was not written by it.
require_fresh() {
  require_nonempty "$1" "$2"
  [[ "$2" -nt "$3" ]] || die "$1 predates the stage that had to write it: $2"
}

campaign_digest() {
  [[ -f "$1" ]] || die "cannot digest a missing artifact: $1"
  sha256sum -- "$1" | awk '{print $1}'
}

# The proposal is a PLAN-only input.  Keep the complete config digest in
# frozen provenance, but remove exactly that one property from the reusable
# static-analysis/trace seed identity.
campaign_seed_config_digest() {
  local path=$1
  [[ -f "${path}" ]] || die "cannot digest a missing seed config: ${path}"
  {
    printf '%s\n' CAMPAIGN_SEED_CONFIG_V1
    awk '
      {
        key = $0
        sub(/^[[:space:]]*/, "", key)
        if (key ~ /^causynth_symbolic_root_proposal[[:space:]]*=/) next
        print $0
      }
    ' "${path}"
  } | sha256sum | awk '{print $1}'
}

# A final-stage JSON artifact is never optional.  Validate it before giving its
# value to another jq invocation: command/process substitution otherwise hides
# the producer's parse failure behind the consumer's successful exit status.
campaign_require_json() {
  local label=$1 path=$2
  [[ -s "${path}" ]] || {
    echo "${label} is missing or empty: ${path}" >&2
    return 1
  }
  jq -e -s 'length == 1 and (.[0] | type) == "object"' \
    "${path}" >/dev/null
}

# Prints the solver's materializable configured-source witness without
# exposing internal SMT term names as the user-facing identity.  sourceKey is
# the tracing authority that distinguishes nodes/threads/epochs; sourceId and
# sourcePhaseId distinguish several declared fields or phases on that source.
campaign_print_symbolic_variable_models() {
  local report=$1 model_count
  campaign_require_json "Z3 symbolic variable report" "${report}" \
    || return 1
  jq -e '
    (.symbolicVariableModels | type) == "array"
    and all(.symbolicVariableModels[];
      .schemaVersion == 1
      and .kind == "SYMBOLIC_VARIABLE_MODEL"
      and (.valuationOrdinal | type) == "number"
      and (.variables | type) == "array"
      and all(.variables[];
        (.sourceKey | type) == "string" and (.sourceKey | length) > 0
        and (.sourceId | type) == "string" and (.sourceId | length) > 0
        and (.sourcePhaseId | type) == "string"
        and (.fieldSignature | type) == "string"
        and has("value")))
  ' "${report}" >/dev/null || return 1
  model_count=$(jq -r '.symbolicVariableModels | length' "${report}")
  if [[ "${model_count}" -eq 0 ]]; then
    campaign_log "symbolic variables: no satisfying model"
    return 0
  fi
  while IFS=$'\t' read -r valuation source_key source_id phase field value nullness; do
    campaign_log "symbolic valuation=${valuation} source=${source_key} variable=${source_id} phase=${phase} field=${field} value=${value}${nullness:+ nullness=${nullness}}"
  done < <(jq -r '
    .symbolicVariableModels[] as $model
    | $model.variables[]
    | [$model.valuationOrdinal, .sourceKey, .sourceId, .sourcePhaseId,
       .fieldSignature, (.value | tostring),
       (.nullnessValue // "" | tostring)]
    | @tsv
  ' "${report}")
}

# An empty JSONL stream is a valid empty collection, but a missing file or one
# malformed row is not.  The caller captures and checks this function before
# constructing a downstream artifact.
campaign_jsonl_array() {
  local label=$1 path=$2
  [[ -f "${path}" ]] || {
    echo "${label} is missing: ${path}" >&2
    return 1
  }
  jq -e -c -s '
    if all(.[]; type == "object") then .
    else error("JSONL artifact contains a non-object row") end
  ' "${path}"
}

campaign_optional_digest() {
  [[ -f "$1" ]] || return 0
  campaign_digest "$1"
}

# A whole tree as one value: sorted paths, each file's content, one hash over
# that listing. A single file digests as itself, an absent path as "absent".
campaign_tree_digest() {
  [[ -e "$1" ]] || { printf 'absent'; return 0; }
  if [[ -f "$1" ]]; then
    campaign_digest "$1"
    return 0
  fi
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z \
    | xargs -0 -r sha256sum) | sha256sum | awk '{print $1}'
}

# Content-addressed importer cache.  Import is a pure decode of four frozen
# inputs: the tool, raw replay rows, the exact task plan, and the runtime plan.
# A cache hit copies only artifacts whose manifest and content digests match;
# a corrupt entry is refused instead of being treated as a miss.
campaign_import_cache_key() {
  local iteration_id=$1
  local jar_sha raw_sha task_sha plan_sha
  jar_sha=$(campaign_digest "${graphchecker_jar}")
  raw_sha=$(campaign_digest "${raw_concolic_results}")
  task_sha=$(campaign_digest "${import_task_plan}")
  plan_sha=$(campaign_digest "${runtime_region_plan}")
  printf '%s\0' "CONCOLIC_IMPORT_CACHE_V1" "${iteration_id}" \
    "${jar_sha}" "${raw_sha}" "${task_sha}" "${plan_sha}" \
    | sha256sum | awk '{print $1}'
}

campaign_restore_import_cache() {
  local key=$1 entry manifest expected actual name
  entry="${causynth_cache_dir}/import/${key}"
  manifest="${entry}/manifest.json"
  [[ -e "${entry}" ]] || return 1
  campaign_require_json "import cache manifest" "${manifest}" \
    || campaign_fail CACHE ConcolicSummaryImporter "${entry}" \
      "the content-addressed import cache entry is incomplete"
  jq -e --arg key "${key}" '
    . as $entry
    | .schemaVersion == 1
    and .kind == "CONCOLIC_IMPORT_CACHE_ENTRY"
    and .key == $key
    and (.exitStatus | type) == "number"
    and (.artifacts | type) == "object"
    and all(["summaries", "diagnostics", "topologyDelta"][];
      . as $name
      | ($entry.artifacts[$name].sha256 | type) == "string"
        and ($entry.artifacts[$name].sha256 | length) == 64)
  ' "${manifest}" >/dev/null \
    || campaign_fail CACHE ConcolicSummaryImporter "${manifest}" \
      "the import cache manifest has an unsupported schema"
  for name in summaries diagnostics topologyDelta; do
    [[ -f "${entry}/${name}.jsonl" ]] \
      || campaign_fail CACHE ConcolicSummaryImporter "${entry}/${name}.jsonl" \
        "the import cache artifact is missing"
    expected=$(jq -r --arg name "${name}" \
      '.artifacts[$name].sha256' "${manifest}")
    actual=$(campaign_digest "${entry}/${name}.jsonl")
    [[ "${actual}" == "${expected}" ]] \
      || campaign_fail CACHE ConcolicSummaryImporter "${entry}/${name}.jsonl" \
        "the import cache artifact digest does not match its manifest"
  done
  mkdir -p "$(dirname "${imported_summaries}")" \
    "$(dirname "${import_diagnostics}")" \
    "$(dirname "${import_topology_delta}")"
  cp -- "${entry}/summaries.jsonl" "${imported_summaries}"
  cp -- "${entry}/diagnostics.jsonl" "${import_diagnostics}"
  cp -- "${entry}/topologyDelta.jsonl" "${import_topology_delta}"
  campaign_cached_import_status=$(jq -r '.exitStatus' "${manifest}")
  return 0
}

campaign_store_import_cache() {
  local key=$1 status=$2 base entry lock temporary name path sha
  [[ -f "${imported_summaries}" && -f "${import_diagnostics}"
      && -f "${import_topology_delta}" ]] || return 0
  base="${causynth_cache_dir}/import"
  entry="${base}/${key}"
  lock="${base}/.${key}.lock"
  mkdir -p "${base}"
  temporary=$(mktemp -d "${base}/.${key}.XXXXXX")
  cp -- "${imported_summaries}" "${temporary}/summaries.jsonl"
  cp -- "${import_diagnostics}" "${temporary}/diagnostics.jsonl"
  cp -- "${import_topology_delta}" "${temporary}/topologyDelta.jsonl"
  local -a artifact_args=()
  for name in summaries diagnostics topologyDelta; do
    path="${temporary}/${name}.jsonl"
    sha=$(campaign_digest "${path}")
    artifact_args+=(--arg "${name}Sha" "${sha}")
  done
  jq -n --arg key "${key}" --argjson status "${status}" \
    "${artifact_args[@]}" '
    {schemaVersion: 1, kind: "CONCOLIC_IMPORT_CACHE_ENTRY",
     key: $key, exitStatus: $status,
     artifacts: {
       summaries: {sha256: $summariesSha},
       diagnostics: {sha256: $diagnosticsSha},
       topologyDelta: {sha256: $topologyDeltaSha}}}
  ' >"${temporary}/manifest.json"
  if mkdir "${lock}" 2>/dev/null; then
    if [[ ! -e "${entry}" ]]; then
      mv -- "${temporary}" "${entry}"
      temporary=""
    fi
    rmdir -- "${lock}"
  fi
  [[ -z "${temporary}" ]] || rm -r -- "${temporary}"
}

# The static discovery and both trace-index passes are one seed boundary.  We
# cache their published artifacts, not RuntimeRegionPlanner's private in-memory
# index, so cache reuse adds no second semantic schema.
campaign_seed_artifact_rows() {
  printf '%s\t%s\n' \
    candidateGraph "${candidate_graph}" \
    runtimePlan "${runtime_region_plan}" \
    refinedGraph "${refined_graph}" \
    targetResolved "${causynth_output_dir}/target_resolved.json" \
    regionSkeletons "${causynth_output_dir}/region_skeletons.jsonl.gz" \
    communicationCallSites \
      "${causynth_output_dir}/communication_call_sites.jsonl.gz" \
    retainedLoops "${causynth_output_dir}/retained_loops.jsonl.gz" \
    communicationGaps \
      "${causynth_output_dir}/communication_gaps.jsonl.gz" \
    selectedSkeletons \
      "$(dirname "${runtime_region_plan}")/skeleton-pass/region_skeletons.jsonl"
}

campaign_seed_cache_key() {
  local identity config_seed_sha
  config_seed_sha=$(campaign_seed_config_digest "${config_file}")
  # symbolicRootProposal is intentionally absent: it is a PLAN input and must
  # reuse the exact static analysis, workload trace, runtime plan and refined
  # graph that produced its mechanism catalog.
  identity=$(jq -S -c \
    --arg analysisScope "${causynth_analysis_scope}" \
    --arg processDirs "${causynth_process_dirs}" \
    --arg workloadWorkDir "${workload_work_dir}" \
    --arg workloadCommand "${workload_command}" \
    --arg traceTest "${trace_test}" \
    --arg configSeedSha "${config_seed_sha}" '
    {schemaVersion: 2, kind: "CAMPAIGN_SEED_CACHE_KEY",
     inputs: {
       jar: .jar.sha256,
       config: $configSeedSha,
       targetSpec: .targetSpec.sha256,
       communicationMappings: .communicationMappings.sha256,
       loopBounds: .loopBounds.sha256,
       symbolicInputs: .symbolicInputs.sha256,
       productionClasses: .productionClasses.sha256,
       workloadTestClasses: .workload.testClasses.sha256,
       workloadClasspath: .workload.classpathSha256,
       workloadSource: .source.workload},
     seedConfiguration: {
       analysisScope: $analysisScope,
       processDirs: $processDirs,
       workloadWorkDir: $workloadWorkDir,
       workloadCommand: $workloadCommand,
       traceTest: $traceTest}}
  ' <<<"${campaign_provenance}")
  printf '%s' "${identity}" | sha256sum | awk '{print $1}'
}

campaign_restore_seed_cache() {
  local key=$1 entry manifest name destination expected actual count=0
  entry="${causynth_cache_dir}/seed/${key}"
  manifest="${entry}/manifest.json"
  [[ -e "${entry}" ]] || return 1
  campaign_require_json "seed cache manifest" "${manifest}" \
    || campaign_fail CACHE CAMPAIGN "${entry}" \
      "the content-addressed seed cache entry is incomplete"
  jq -e --arg key "${key}" '
    .schemaVersion == 1
    and .kind == "CAMPAIGN_SEED_CACHE_ENTRY"
    and .key == $key
    and (.artifacts | type) == "object"
  ' "${manifest}" >/dev/null \
    || campaign_fail CACHE CAMPAIGN "${manifest}" \
      "the seed cache manifest has an unsupported schema"
  while IFS=$'\t' read -r name destination; do
    count=$((count + 1))
    [[ -f "${entry}/${name}" ]] \
      || campaign_fail CACHE CAMPAIGN "${entry}/${name}" \
        "the seed cache artifact is missing"
    expected=$(jq -r --arg name "${name}" \
      '.artifacts[$name].sha256 // ""' "${manifest}")
    [[ ${#expected} -eq 64 ]] \
      || campaign_fail CACHE CAMPAIGN "${manifest}" \
        "the seed cache manifest omits ${name}"
    actual=$(campaign_digest "${entry}/${name}")
    [[ "${actual}" == "${expected}" ]] \
      || campaign_fail CACHE CAMPAIGN "${entry}/${name}" \
        "the seed cache artifact digest does not match its manifest"
    mkdir -p "$(dirname "${destination}")"
    cp -- "${entry}/${name}" "${destination}"
  done < <(campaign_seed_artifact_rows)
  [[ "${count}" -eq 9 ]] || campaign_fail CACHE CAMPAIGN "${manifest}" \
    "the seed cache artifact set is incomplete"
}

campaign_store_seed_cache() {
  local key=$1 base entry lock temporary rows name source sha
  base="${causynth_cache_dir}/seed"
  entry="${base}/${key}"
  lock="${base}/.${key}.lock"
  mkdir -p "${base}"
  temporary=$(mktemp -d "${base}/.${key}.XXXXXX")
  rows="${temporary}/artifacts.jsonl"
  : >"${rows}"
  while IFS=$'\t' read -r name source; do
    require_nonempty "seed cache source ${name}" "${source}"
    cp -- "${source}" "${temporary}/${name}"
    sha=$(campaign_digest "${temporary}/${name}")
    jq -n -c --arg name "${name}" --arg sha "${sha}" \
      '{name: $name, sha256: $sha}' >>"${rows}"
  done < <(campaign_seed_artifact_rows)
  jq -n --arg key "${key}" --slurpfile rows "${rows}" '
    {schemaVersion: 1, kind: "CAMPAIGN_SEED_CACHE_ENTRY", key: $key,
     artifacts: ($rows | map({key: .name,
                              value: {sha256: .sha256}}) | from_entries)}
  ' >"${temporary}/manifest.json"
  rm -- "${rows}"
  if mkdir "${lock}" 2>/dev/null; then
    if [[ ! -e "${entry}" ]]; then
      mv -- "${temporary}" "${entry}"
      temporary=""
    fi
    rmdir -- "${lock}"
  fi
  [[ -z "${temporary}" ]] || rm -r -- "${temporary}"
}

# A checkout's exact state. The commit alone is not its identity: these
# checkouts carry uncommitted driver and tracing changes, so the porcelain
# listing and the content of every file it names are hashed with it.
campaign_checkout_state() {
  local repo=$1 entry head branch porcelain worktree
  if ! git -C "${repo}" rev-parse HEAD >/dev/null 2>&1; then
    jq -n --arg path "${repo}" \
      '{path: $path, head: "", branch: "", worktreeDigest: ""}'
    return 0
  fi
  if ! head=$(git -C "${repo}" rev-parse HEAD); then return 1; fi
  if ! branch=$(git -C "${repo}" rev-parse --abbrev-ref HEAD); then
    return 1
  fi
  if ! porcelain=$(git -C "${repo}" status --porcelain); then return 1; fi
  if ! worktree=$( { printf '%s\n' "${porcelain}"
      printf '%s\n' "${porcelain}" | awk '{print $NF}' \
        | while IFS= read -r entry; do
            [[ -e "${repo}/${entry}" ]] || continue
            find "${repo}/${entry}" -type f -print0 | LC_ALL=C sort -z \
              | xargs -0 -r sha256sum
          done; } | sha256sum | awk '{print $1}'); then
    return 1
  fi
  jq -n --arg path "${repo}" \
    --arg head "${head}" --arg branch "${branch}" \
    --arg worktree "${worktree}" \
    '{path: $path, head: $head, branch: $branch, worktreeDigest: $worktree}'
}

# A stage is a plain command, never the condition of an `if`: a stage wrapped
# in a condition suppresses errexit for everything it calls, which is how a
# failed `mvn package` once left a stale fat jar in place while the run
# continued against binaries that were not the tree's.
campaign_stage() {
  local name=$1
  shift
  local started ended
  started=$(date +%s%N)
  campaign_log "stage ${name}"
  "$@"
  ended=$(date +%s%N)
  printf '%s\t%s\n' "${name}" "$(( (ended - started) / 1000000 ))" \
    >>"${campaign_stage_metrics}"
}

# One depth-safe JSON helper. jq refuses a document that nests past its fixed
# parser depth, and a replay result carries one expression tree per recorded
# read; a read bound to another region's writer exceeds that limit. The modes
# only list, select, combine and sort rows a production owner already wrote --
# none of them decides whether a row is admissible.
campaign_json() {
  python3 - "$@" <<'CAMPAIGN_JSON'
import json, os, sys

mode = sys.argv[1]
args = sys.argv[2:]

DELTA_KINDS = ("NEW_LOCAL_CASE", "NEW_EFFECT", "NEW_OCCURRENCE",
               "NEW_CAUSAL_BINDING", "TOPOLOGY_DIVERGENCE", "COVERAGE_GAP")


def rows(path):
    out = []
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out


def dump(row):
    return json.dumps(row, separators=(",", ":"))


if mode == "result-tasks":
    for row in rows(args[0]):
        if row.get("event") == "CONCOLIC_REGION_RESULT":
            print(row.get("taskId", ""))

elif mode == "select-summary":
    # Membership, not admission: whatever the importer wrote for this task.
    # Whether a task ended with a usable summary is the importer's finding and
    # travels as its own diagnostic/delta row, not as a shell verdict here.
    for row in rows(args[0]):
        if row.get("taskId") == args[1]:
            print(dump(row))

elif mode == "combine":
    identity, output = args[0], args[1]
    order, table = [], {}

    def comparable(row):
        if identity != "summaryId":
            return row
        trimmed = dict(row)
        trimmed.pop("taskId", None)
        return trimmed

    for path in args[2:]:
        for row in rows(path):
            key = row.get(identity) if isinstance(row, dict) else None
            if not isinstance(key, str) or not key:
                sys.exit("missing JSONL identity " + identity + " in " + path)
            if key in table:
                if comparable(table[key]) != comparable(row):
                    sys.exit("conflicting duplicate " + identity + ":" + key)
                continue
            order.append(key)
            table[key] = row
    with open(output + ".tmp", "w") as handle:
        for key in order:
            handle.write(dump(table[key]) + "\n")
    os.replace(output + ".tmp", output)

elif mode == "delta":
    # The importer owns classification; this only keeps the rows it declared in
    # the delta vocabulary and sorts them in the stable order README states.
    # Importer rows already carry the immutable iteration. Shell-owned gap
    # rows have none and receive this call's explicit identity; a blank or
    # different declared identity is a provenance error, never repaired here.
    iteration, output = args[0], args[1]
    if not iteration.strip():
        sys.exit("topology delta iteration id is required")
    collected = []
    for path in args[2:]:
        if not os.path.exists(path):
            continue
        for row in rows(path):
            kind = (row.get("deltaKind") or row.get("kind")
                    or row.get("code") or "")
            if kind not in DELTA_KINDS:
                continue
            row = dict(row)
            row["deltaKind"] = kind
            row.setdefault("kind", "TOPOLOGY_DELTA")
            declared = row.get("iterationId")
            if declared is None:
                row["iterationId"] = iteration
            elif not isinstance(declared, str) or declared != iteration:
                sys.exit("topology delta iteration mismatch in " + path)
            collected.append(row)
    collected.sort(key=lambda row: tuple(
        str(row.get(field, "")) for field in
        ("iterationId", "taskId", "sourceKey", "occurrenceId", "caseDigest",
         "deltaKind")))
    with open(output, "w") as handle:
        for row in collected:
            handle.write(dump(row) + "\n")
    divergences = sum(1 for row in collected
                      if row["deltaKind"] == "TOPOLOGY_DIVERGENCE")
    print("%d %d" % (len(collected), divergences))

else:
    sys.exit("unknown campaign_json mode " + mode)
CAMPAIGN_JSON
}

# A stage condition the shell observed but does not own: a task with no result,
# an obligation that did not finish, an artifact a semantic owner never
# published. It is written once in the delta vocabulary so CLASSIFY collects it
# and the Composer decides whether it blocks the selected target closure. The
# shell never ends the iteration on one of these.
campaign_record_gap() {
  local iteration_dir=$1 code=$2 subject=$3 detail=$4
  local dir="${iteration_dir}/campaign-gaps"
  mkdir -p "${dir}"
  jq -n -c --arg code "${code}" --arg subject "${subject}" \
    --arg detail "${detail}" \
    '{deltaKind: "COVERAGE_GAP", source: "CAMPAIGN", code: $code,
      taskId: $subject, subject: $subject, reason: $detail}' \
    >>"${dir}/topology_delta.jsonl"
  campaign_log "gap ${code} subject=${subject}: ${detail}"
}

# The scheduler index is the only campaign membership authority.  Decode the
# complete schema in one checked jq operation.  The six fields are emitted as
# TSV only after their types, non-blank identities, and task-set disjointness
# have been proved.  A target-local-only workflow may legitimately have no
# producer, so the target row is the sole required member.
campaign_decode_index_members() {
  local index=$1
  [[ -s "${index}" ]] || {
    echo "runtime workflow schedule index is missing or empty: ${index}" >&2
    return 1
  }
  jq -e -r -s '
    def scalar_id:
      type == "string"
      and test("^[^\\t\\r\\n]*[^\\t\\r\\n[:space:]][^\\t\\r\\n]*$");
    def member:
      type == "object"
      and (.campaignId | scalar_id)
      and (.regionId | scalar_id)
      and (.occurrenceId | scalar_id)
      and (.goalId | scalar_id)
      and (.taskId | scalar_id);
    if length != 1 then
      error("schedule index must contain exactly one JSON document")
    else .[0] end
    | if (.schemaVersion == 1
        and .kind == "RUNTIME_TARGET_FIRST_SCHEDULE_INDEX"
        and .selectionAuthority
          == "RANKED_EXACT_RUNTIME_READ_FROM_CLOSURE_V1"
        and (.target | member)
        and (.producers | type == "array")
        and all(.producers[]; member)
        and (([.target.taskId] + [.producers[].taskId]) as $ids
          | ($ids | length) == ($ids | unique | length)))
    then
      ((.target + {role: "TARGET"}),
       (.producers[] + {role: "PRODUCER"}))
      | [.role, .campaignId, .regionId, .occurrenceId, .goalId, .taskId]
      | @tsv
    else error("invalid runtime target-first schedule index") end
  ' "${index}"
}

campaign_path_closures_json() {
  local workers=$1 path_list path
  [[ -d "${workers}" ]] || {
    echo "campaign workers directory is missing: ${workers}" >&2
    return 1
  }
  if ! path_list=$(find "${workers}" -type f -name path_closure.json -print \
      | LC_ALL=C sort); then
    return 1
  fi
  [[ -n "${path_list}" ]] || { printf '[]\n'; return 0; }
  while IFS= read -r path; do
    [[ -n "${path}" ]] || continue
    jq -e -c -s '
      if length == 1
          and .[0].schemaVersion == 1
          and .[0].kind == "REGION_PATH_WORKLIST"
          and (.[0].coverageGaps | type == "array")
      then .[0]
      else error("path closure must contain exactly one JSON document") end
    ' "${path}" || return 1
  done <<<"${path_list}" | jq -e -c -s .
}

# Publish one checked snapshot of the immutable worker closures.  Validation
# and EMIT then consume the same bytes; a later process-substitution failure
# cannot silently turn a prefix of the worker tree into the reported set.
# campaign_path_closures_json is the one place a closure row is checked; the
# snapshot is written from its checked output and is not re-checked here.
campaign_materialize_path_closures() {
  local workers=$1 output=$2 pending
  pending="${output}.tmp"
  [[ ! -e "${output}" ]] || {
    echo "path-closure snapshot already exists: ${output}" >&2
    return 1
  }
  if ! campaign_path_closures_json "${workers}" >"${pending}"; then
    return 1
  fi
  mv -- "${pending}" "${output}"
}

campaign_iteration_manifests_json() {
  local root=$1 path_list path
  if ! path_list=$(find "${root}" -mindepth 2 -maxdepth 2 \
      -name iteration_manifest.json -print | LC_ALL=C sort); then
    return 1
  fi
  [[ -n "${path_list}" ]] || {
    echo "campaign published no iteration manifest under ${root}" >&2
    return 1
  }
  while IFS= read -r path; do
    [[ -n "${path}" ]] || continue
    jq -e -c -s '
      if length != 1 then
        error("iteration manifest must contain exactly one JSON document")
      else .[0] end
      | if (.schemaVersion == 1
          and .kind == "CAMPAIGN_ITERATION_MANIFEST"
          and (.iterationId | type == "string" and length > 0)
          and (.members | type == "array" and length > 0)
          and all(.members[];
            ((.role == "TARGET") or (.role == "PRODUCER"))
            and (.taskId | type == "string" and length > 0)
            and (.obligationDigests | type == "array"))
          and (([.members[].taskId] | length)
            == ([.members[].taskId] | unique | length))
          and ([.members[] | select(.role == "TARGET")] | length == 1))
      then {iterationId, parentIterationId, externalWorkerCount,
            topologyDelta, taskIds: [.members[].taskId],
            obligations: [.members[]
              | {taskId, digests: .obligationDigests}]}
      else error("invalid campaign iteration manifest") end
    ' "${path}" || return 1
  done <<<"${path_list}" | jq -e -c -s '
    if length > 0
        and (([.[].iterationId] | length)
          == ([.[].iterationId] | unique | length))
    then . else error("duplicate or absent campaign iteration manifest") end
  '
}

campaign_decode_worklist_keys() {
  local worklist=$1 limit=$2
  [[ -f "${worklist}" ]] || {
    echo "path-flip worklist is missing: ${worklist}" >&2
    return 1
  }
  [[ "${limit}" =~ ^[1-9][0-9]*$ ]] || {
    echo "path-flip worker limit is invalid: ${limit}" >&2
    return 1
  }
  jq -e -r -s --argjson limit "${limit}" '
    if all(.[]; type == "object"
        and (.queryKey | type == "string" and length > 0))
        and (([.[].queryKey] | length)
          == ([.[].queryKey] | unique | length))
    then sort_by(.queryKey) | .[0:$limit][] | .queryKey
    else error("malformed or duplicate path-flip worklist row") end
  ' "${worklist}"
}

campaign_wait_workers() {
  local pid status=0
  for pid in "$@"; do
    wait "${pid}" || status=1
  done
  return "${status}"
}

campaign_validate() {
  validate_config >/dev/null
  [[ -n "${concolic_replay_command}" ]] || die \
    "campaign requires concolic_replay_command: the workload adapter that replays one immutable task plan under the concolic VM"
  require_command_available jq
  require_command_available python3
  require_command_available sha256sum
  campaign_log "workers=${concolic_worker_count} maxIterations=${campaign_max_iterations} maxJobs=${schedule_max_jobs}"
}

require_command_available() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

campaign_run_adapter() {
  local label=$1
  local command=$2
  shift 2
  local -a adapter_env
  adapter_env=(
    "CAUSYNTH_WORKFLOW_CONFIG=${config_file}"
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    # Every adapter loads the same frozen artifact as analysis and scheduling.
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "$@"
  )
  campaign_log "${label} adapter: ${command}"
  (cd "${workload_work_dir}" && env "${adapter_env[@]}" bash -lc "${command}")
}

campaign_setup() {
  campaign_run_adapter setup "${campaign_setup_command}"
}

# Copy the executable tool into this run before even the setup adapter loads
# it. A recorded hash alone is not a freeze: a concurrent `mvn package` can
# replace the live target jar after the JVM has started, making later lazy
# class loads observe a different archive. The before/copy/after digests turn
# such a race into a named FREEZE_TOOL failure; every later stage uses the
# private, read-only copy.
campaign_freeze_graphchecker_jar() {
  local source_jar="${graphchecker_jar}"
  local frozen_dir="${campaign_root}/frozen-inputs"
  local frozen_jar="${frozen_dir}/GraphChecker.jar"
  local before_sha after_sha frozen_sha
  [[ -f "${source_jar}" ]] || campaign_fail FREEZE_TOOL CAMPAIGN \
    "${source_jar}" "the source GraphChecker jar is missing"
  [[ -d "${frozen_dir}" ]] || campaign_fail FREEZE_TOOL CAMPAIGN \
    "${frozen_dir}" "the campaign did not reserve its private input directory"
  [[ ! -e "${frozen_jar}" ]] || campaign_fail FREEZE_TOOL CAMPAIGN \
    "${frozen_jar}" "the private GraphChecker jar already exists"
  before_sha=$(campaign_digest "${source_jar}") || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${source_jar}" "pre-copy digest failed"
  cp -p -- "${source_jar}" "${frozen_jar}" || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${source_jar}" "private jar copy failed"
  after_sha=$(campaign_digest "${source_jar}") || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${source_jar}" "post-copy digest failed"
  frozen_sha=$(campaign_digest "${frozen_jar}") || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${frozen_jar}" "private jar digest failed"
  [[ "${before_sha}" == "${after_sha}"
      && "${before_sha}" == "${frozen_sha}" ]] || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${source_jar}" \
    "the GraphChecker jar changed while it was being frozen"
  chmod a-w "${frozen_jar}" || campaign_fail FREEZE_TOOL CAMPAIGN \
    "${frozen_jar}" "failed to make the private jar read-only"
  graphchecker_jar="${frozen_jar}"
}

# The one frozen generation, and the campaign's only provenance authority.
# Everything the run manifest has to bind is digested here, before any stage
# can write: jar, VM, config, target, adapter, per-loop bounds, the production
# classes the analysis rewrites, the runtime workload-test class/classpath, and
# both source checkouts. Nothing re-derives a second stamp from an artifact
# afterwards -- two provenance authorities disagree exactly when it matters.
campaign_freeze() {
  require_file "GraphChecker jar" "${graphchecker_jar}"
  local vm="${custom_jdk_home}/bin/java"
  local rt_jar="${custom_jdk_home}/jre/lib/rt.jar"
  local libjava="${custom_jdk_home}/jre/lib/amd64/libjava.so"
  local libjvm="${custom_jdk_home}/jre/lib/amd64/server/libjvm.so"
  local jar_sha vm_sha rt_jar_sha libjava_sha libjvm_sha config_sha
  local spec_sha mappings_sha bounds_sha symbolic_inputs_sha root_proposal_sha
  local classes_sha test_classes_sha classpath_sha tool_source workload_source
  [[ -x "${vm}" ]] || die "the concolic VM is not built: ${vm}"
  require_file "concolic rt.jar" "${rt_jar}"
  require_file "concolic libjava" "${libjava}"
  require_file "concolic libjvm" "${libjvm}"
  [[ -d "${project_classes_dir}" ]] || campaign_fail FREEZE CAMPAIGN \
    "${project_classes_dir}" "production classes directory is absent"
  [[ -d "${project_test_classes_dir}" ]] || campaign_fail FREEZE CAMPAIGN \
    "${project_test_classes_dir}" "test classes directory is absent"
  if ! jar_sha=$(campaign_digest "${graphchecker_jar}"); then
    campaign_fail FREEZE CAMPAIGN "${graphchecker_jar}" "digest failed"
  fi
  if ! vm_sha=$(campaign_digest "${vm}"); then
    campaign_fail FREEZE CAMPAIGN "${vm}" "digest failed"
  fi
  if ! rt_jar_sha=$(campaign_digest "${rt_jar}"); then
    campaign_fail FREEZE CAMPAIGN "${rt_jar}" "digest failed"
  fi
  if ! libjava_sha=$(campaign_digest "${libjava}"); then
    campaign_fail FREEZE CAMPAIGN "${libjava}" "digest failed"
  fi
  if ! libjvm_sha=$(campaign_digest "${libjvm}"); then
    campaign_fail FREEZE CAMPAIGN "${libjvm}" "digest failed"
  fi
  if ! config_sha=$(campaign_digest "${config_file}"); then
    campaign_fail FREEZE CAMPAIGN "${config_file}" "digest failed"
  fi
  if ! spec_sha=$(campaign_optional_digest "${causynth_target_spec}"); then
    campaign_fail FREEZE CAMPAIGN "${causynth_target_spec}" "digest failed"
  fi
  if ! mappings_sha=$(campaign_optional_digest "${causynth_communication_mappings}"); then
    campaign_fail FREEZE CAMPAIGN "${causynth_communication_mappings}" "digest failed"
  fi
  # Not campaign_optional_digest: that returns an empty digest for a file
  # that is not there, and an empty loopBounds.sha256 in the frozen manifest
  # is the one thing an accepted candidate must never be allowed to carry --
  # it records "the bounds were whatever" as though it were provenance.
  if ! bounds_sha=$(campaign_digest "${causynth_loop_bounds}"); then
    campaign_fail FREEZE CAMPAIGN "${causynth_loop_bounds}" "digest failed"
  fi
  if ! symbolic_inputs_sha=$(campaign_optional_digest \
      "${causynth_symbolic_inputs}"); then
    campaign_fail FREEZE CAMPAIGN "${causynth_symbolic_inputs}" \
      "digest failed"
  fi
  if ! root_proposal_sha=$(campaign_optional_digest \
      "${causynth_symbolic_root_proposal:-}"); then
    campaign_fail FREEZE CAMPAIGN "${causynth_symbolic_root_proposal:-}" \
      "digest failed"
  fi
  if ! classes_sha=$(campaign_tree_digest "${project_classes_dir}"); then
    campaign_fail FREEZE CAMPAIGN "${project_classes_dir}" \
      "tree digest failed"
  fi
  if ! test_classes_sha=$(campaign_tree_digest \
      "${project_test_classes_dir}"); then
    campaign_fail FREEZE CAMPAIGN "${project_test_classes_dir}" \
      "tree digest failed"
  fi
  if ! classpath_sha=$(printf '%s' "${project_classpath}" | sha256sum \
      | awk '{print $1}'); then
    campaign_fail FREEZE CAMPAIGN "project_classpath" "digest failed"
  fi
  if ! tool_source=$(campaign_checkout_state "${graphchecker_dir}"); then
    campaign_fail FREEZE CAMPAIGN "${graphchecker_dir}" \
      "failed to capture GraphChecker checkout state"
  fi
  if ! workload_source=$(campaign_checkout_state "${project_repo}"); then
    campaign_fail FREEZE CAMPAIGN "${project_repo}" \
      "failed to capture workload checkout state"
  fi
  if ! campaign_provenance=$(jq -n \
    --arg jar "${graphchecker_jar}" \
    --arg jarSha "${jar_sha}" \
    --arg vm "${vm}" --arg vmSha "${vm_sha}" \
    --arg rtJar "${rt_jar}" \
    --arg rtJarSha "${rt_jar_sha}" \
    --arg libjava "${libjava}" \
    --arg libjavaSha "${libjava_sha}" \
    --arg libjvm "${libjvm}" \
    --arg libjvmSha "${libjvm_sha}" \
    --arg config "${config_file}" \
    --arg configSha "${config_sha}" \
    --arg spec "${causynth_target_spec}" \
    --arg specSha "${spec_sha}" \
    --arg mappings "${causynth_communication_mappings}" \
    --arg mappingsSha "${mappings_sha}" \
    --arg bounds "${causynth_loop_bounds}" \
    --arg boundsSha "${bounds_sha}" \
    --arg symbolicInputs "${causynth_symbolic_inputs}" \
    --arg symbolicInputsSha "${symbolic_inputs_sha}" \
    --arg symbolicRootProposal "${causynth_symbolic_root_proposal:-}" \
    --arg symbolicRootProposalSha "${root_proposal_sha}" \
    --arg classes "${project_classes_dir}" \
    --arg classesSha "${classes_sha}" \
    --arg testClass "${trace_test}" \
    --arg testClasses "${project_test_classes_dir}" \
    --arg testClassesSha "${test_classes_sha}" \
    --arg classpath "${project_classpath}" \
    --arg classpathSha "${classpath_sha}" \
    --argjson toolSource "${tool_source}" \
    --argjson workloadSource "${workload_source}" \
    '{jar: {path: $jar, sha256: $jarSha},
      vm: {path: $vm, sha256: $vmSha,
           rtJar: {path: $rtJar, sha256: $rtJarSha},
           libjava: {path: $libjava, sha256: $libjavaSha},
           libjvm: {path: $libjvm, sha256: $libjvmSha}},
      config: {path: $config, sha256: $configSha},
      targetSpec: {path: $spec, sha256: $specSha},
      communicationMappings: {path: $mappings, sha256: $mappingsSha},
      loopBounds: {path: $bounds, sha256: $boundsSha},
      symbolicInputs: {path: $symbolicInputs,
                       sha256: $symbolicInputsSha},
      symbolicRootProposal: {path: $symbolicRootProposal,
                             sha256: $symbolicRootProposalSha},
      productionClasses: {path: $classes, sha256: $classesSha},
      workload: {testClass: $testClass,
                 testClasses: {path: $testClasses, sha256: $testClassesSha},
                 classpath: $classpath, classpathSha256: $classpathSha},
      source: {graphchecker: $toolSource, workload: $workloadSource}}'); then
    campaign_fail FREEZE CAMPAIGN "${campaign_root}" \
      "failed to construct immutable campaign provenance"
  fi
}

# GATE-1: acceptance requires *current* frozen provenance, not provenance that
# was current when the run started. A campaign is hours long, and every frozen
# input except the tool jar lives outside the immutable root, so nothing stops
# a rebuild, an editor, or a second agent from moving one underneath a running
# generation. EMIT therefore re-reads what FREEZE stamped and refuses to
# publish a candidate whose inputs no longer hash to the manifest that claims
# to bind them.
#
# Scope is the FREEZE stage's inputs and only those: jar, VM and its three
# libraries, config, target spec, communication mappings, per-loop bounds, symbolic
# input selection, optional symbolic-root proposal, the production/test class
# trees, and the workload classpath
# string. The SEED additions (static catalog, region plan, refined graph) are
# this campaign's own outputs rather than its inputs, and the INSTRUMENT stage
# legitimately rewrites the analysis root they sit in; re-hashing them here
# would report the run's own work as drift. The two checkout states are left
# alone for the same reason -- campaign_checkout_state hashes every file git
# reports as dirty or untracked, and a workload writes cluster scratch beneath
# its working directory while it runs.
campaign_verify_frozen_inputs() {
  local failure_stage=${1:-EMIT}
  local failure_component=${2:-CAMPAIGN}
  local failure_target=${3:-${campaign_final}}
  local rows kind label path expected actual classpath_sha
  if ! rows=$(jq -r '
      [{kind: "file", label: "jar", entry: .jar},
       {kind: "file", label: "vm", entry: .vm},
       {kind: "file", label: "vm.rtJar", entry: .vm.rtJar},
       {kind: "file", label: "vm.libjava", entry: .vm.libjava},
       {kind: "file", label: "vm.libjvm", entry: .vm.libjvm},
       {kind: "file", label: "config", entry: .config},
       {kind: "file", label: "targetSpec", entry: .targetSpec},
       {kind: "file", label: "communicationMappings", entry: .communicationMappings},
       {kind: "file", label: "loopBounds", entry: .loopBounds},
       {kind: "file", label: "symbolicInputs", entry: .symbolicInputs},
       {kind: "file", label: "symbolicRootProposal",
        entry: .symbolicRootProposal},
       {kind: "tree", label: "productionClasses", entry: .productionClasses},
       {kind: "tree", label: "workload.testClasses",
        entry: .workload.testClasses}]
      | .[]
      | select(.entry != null)
      | [.kind, .label,
         (if (.entry.path // "") == "" then "-" else .entry.path end),
         (if (.entry.sha256 // "") == "" then "-" else .entry.sha256 end)]
      | @tsv' <<<"${campaign_provenance}"); then
    campaign_fail "${failure_stage}" "${failure_component}" "${failure_target}" \
      "the frozen campaign provenance could not be read back"
  fi
  while IFS=$'\t' read -r kind label path expected; do
    [[ -n "${label}" ]] || continue
    # An input this workload never configured is frozen as an unnamed entry.
    # It stays unnamed; a digest without a path is a provenance row nobody can
    # re-derive, so it is refused rather than skipped.
    if [[ "${path}" == "-" ]]; then
      [[ "${expected}" == "-" ]] || campaign_fail "${failure_stage}" \
        "${failure_component}" "${label}" \
        "the frozen provenance digests an input it names no path for"
      continue
    fi
    case "${kind}" in
      file)
        [[ -f "${path}" ]] || campaign_fail "${failure_stage}" \
          "${failure_component}" "${path}" \
          "frozen input ${label} no longer exists"
        if ! actual=$(campaign_digest "${path}"); then
          campaign_fail "${failure_stage}" "${failure_component}" "${path}" \
            "frozen input ${label} could not be re-digested"
        fi
        ;;
      tree)
        if ! actual=$(campaign_tree_digest "${path}"); then
          campaign_fail "${failure_stage}" "${failure_component}" "${path}" \
            "frozen input ${label} could not be re-digested"
        fi
        ;;
      *) campaign_fail "${failure_stage}" "${failure_component}" "${label}" \
          "unknown frozen provenance entry kind: ${kind}" ;;
    esac
    [[ "${actual}" == "${expected}" ]] || campaign_fail "${failure_stage}" \
      "${failure_component}" "${path}" \
      "frozen input ${label} changed after it was frozen: manifest sha256=${expected} current sha256=${actual}"
  done <<<"${rows}"

  # The classpath is a string rather than a file, so its frozen digest is over
  # the string the stages were actually handed. It cannot drift on disk, but it
  # can drift in this process: a stage that rewrote it would leave every replay
  # reading a classpath the manifest does not describe.
  if ! classpath_sha=$(printf '%s' "${project_classpath}" | sha256sum \
      | awk '{print $1}'); then
    campaign_fail "${failure_stage}" "${failure_component}" \
      "project_classpath" "digest failed"
  fi
  [[ "${classpath_sha}" == \
      "$(jq -r '.workload.classpathSha256 // ""' <<<"${campaign_provenance}")" ]] \
    || campaign_fail "${failure_stage}" "${failure_component}" \
      "project_classpath" \
      "the workload classpath changed after it was frozen"
}

# The stock-JVM seed: the static pass, then the two traced passes the workload
# stage owns. Its outputs are the campaign's static catalog and target closure.
campaign_seed() {
  local marker="${campaign_root}/.seed-started"
  local catalog_sha plan_sha refined_sha seed_manifest seed_cache_key
  local seed_cache_status
  : >"${marker}"
  seed_cache_key=$(campaign_seed_cache_key)
  if campaign_restore_seed_cache "${seed_cache_key}"; then
    seed_cache_status=HIT
    campaign_log "cache hit SEED key=${seed_cache_key}"
  else
    seed_cache_status=MISS
    campaign_log "cache miss SEED key=${seed_cache_key}"
    do_analyze
    do_workload
    campaign_store_seed_cache "${seed_cache_key}"
  fi
  require_fresh "static candidate data-flow graph" "${candidate_graph}" \
    "${marker}"
  require_fresh "runtime region plan" "${runtime_region_plan}" "${marker}"
  require_fresh "runtime-refined data-flow graph" "${refined_graph}" \
    "${marker}"
  # Snapshot both seed skeleton views inside this immutable campaign.  The
  # configured analysis and runtime roots are already generation-local; the
  # snapshot keeps the exact static/runtime pair beside the final provenance.
  local skeleton_snapshot="${campaign_root}/seed-skeletons"
  mkdir -p "${skeleton_snapshot}"
  local skeleton
  for skeleton in "${causynth_output_dir}/region_skeletons.jsonl.gz" \
      "$(dirname "${runtime_region_plan}")/skeleton-pass/region_skeletons.jsonl"; do
    [[ -f "${skeleton}" ]] && cp -p "${skeleton}" "${skeleton_snapshot}/" || true
  done
  if ! catalog_sha=$(campaign_digest "${candidate_graph}"); then
    campaign_fail SEED CAMPAIGN "${candidate_graph}" "digest failed"
  fi
  if ! plan_sha=$(campaign_digest "${runtime_region_plan}"); then
    campaign_fail SEED CAMPAIGN "${runtime_region_plan}" "digest failed"
  fi
  if ! refined_sha=$(campaign_digest "${refined_graph}"); then
    campaign_fail SEED CAMPAIGN "${refined_graph}" "digest failed"
  fi
  if ! campaign_provenance=$(jq -n \
    --argjson frozen "${campaign_provenance}" \
    --arg catalog "${candidate_graph}" \
    --arg catalogSha "${catalog_sha}" \
    --arg plan "${runtime_region_plan}" \
    --arg planSha "${plan_sha}" \
    --arg refined "${refined_graph}" \
    --arg refinedSha "${refined_sha}" \
    '$frozen + {staticCatalog: {path: $catalog, sha256: $catalogSha},
                regionPlan: {path: $plan, sha256: $planSha},
                refinedGraph: {path: $refined, sha256: $refinedSha}}'); then
    campaign_fail SEED CAMPAIGN "${campaign_root}" \
      "failed to extend immutable seed provenance"
  fi

  # Persist the seed boundary immediately.  A later replay can be interrupted
  # before an iteration manifest exists; keeping this exact pre-iteration
  # identity beside the three seed products makes the expensive static/trace
  # stage cacheable without treating timestamps or a matching JAR as proof.
  seed_manifest="${campaign_root}/seed-manifest.json"
  if ! jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg analysisScope "${causynth_analysis_scope}" \
    --arg processDirs "${causynth_process_dirs}" \
    --arg workloadWorkDir "${workload_work_dir}" \
    --arg workloadCommand "${workload_command}" \
    --arg traceTest "${trace_test}" \
    --arg cacheKey "${seed_cache_key}" \
    --arg cacheStatus "${seed_cache_status}" \
    '{schemaVersion: 1,
      kind: "CAMPAIGN_SEED_MANIFEST",
      provenance: $provenance,
      cache: {schemaVersion: 1, authority: "CONTENT_DIGEST_V1",
              key: $cacheKey, status: $cacheStatus},
      seedConfiguration: {
        analysisScope: $analysisScope,
        processDirs: $processDirs,
        workloadWorkDir: $workloadWorkDir,
        workloadCommand: $workloadCommand,
        traceTest: $traceTest
      }}' >"${seed_manifest}"; then
    campaign_fail SEED CAMPAIGN "${seed_manifest}" \
      "failed to persist the immutable seed manifest"
  fi
  require_nonempty "campaign seed manifest" "${seed_manifest}"
}

# Schedule pass one: the immutable target-first plan for this iteration, its
# digest-committed index, and one singleton subplan per indexed member.
campaign_plan() {
  local iteration_dir=$1 carry=$2
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local root_cards="${iteration_dir}/symbolic_root_mechanism_cards.json"
  local frozen="${iteration_dir}/concolic_region_plan.jsonl"
  local role campaign_id region occurrence goal task worker
  local plan_hash plan_size region_hash region_size cards_hash cards_size
  local proposal_hash

  require_nonempty "runtime region plan" "${runtime_region_plan}"
  require_nonempty "runtime-refined data-flow graph" "${refined_graph}"
  cp -f "${runtime_region_plan}" "${frozen}"
  schedule_output_dir="${iteration_dir}"
  schedule_summaries="${carry}"
  do_schedule
  # Every later consumer reads this iteration's frozen copy, never the mutable
  # discovery output.
  runtime_region_plan="${frozen}"
  require_nonempty "campaign task plan" "${plan}"
  require_nonempty "runtime workflow schedule index" "${index}"
  require_nonempty "symbolic root mechanism cards" "${root_cards}"

  plan_hash=$(campaign_digest "${plan}")
  plan_size=$(stat -c '%s' "${plan}")
  region_hash=$(campaign_digest "${frozen}")
  region_size=$(stat -c '%s' "${frozen}")
  cards_hash=$(campaign_digest "${root_cards}")
  cards_size=$(stat -c '%s' "${root_cards}")
  if ! proposal_hash=$(campaign_optional_digest \
      "${causynth_symbolic_root_proposal:-}"); then
    campaign_fail PLAN ConcolicScheduler \
      "${causynth_symbolic_root_proposal:-<none>}" \
      "failed to digest the symbolic root proposal"
  fi
  # Immutable paths, digests and task-set membership -- the whole of what the
  # shell owns here. The index must commit exactly the plan bytes this
  # iteration froze, and its members must be exactly that plan's tasks. What a
  # task selects, and by which authority, is the scheduler's own invariant.
  jq -e --arg plan_hash "${plan_hash}" --arg region_hash "${region_hash}" \
    --arg cards_hash "${cards_hash}" --arg proposal_hash "${proposal_hash}" \
    --argjson plan_size "${plan_size}" --argjson region_size "${region_size}" \
    --argjson cards_size "${cards_size}" \
    --slurpfile tasks "${plan}" '
      ([.target.taskId] + [.producers[].taskId]
        | map(select(. != null))) as $selected
      | .executionTaskPlan.sha256 == $plan_hash
        and .executionTaskPlan.sizeBytes == $plan_size
        and .regionPlan.sha256 == $region_hash
        and .regionPlan.sizeBytes == $region_size
        and .symbolicRootMechanismCatalog.sha256 == $cards_hash
        and .symbolicRootMechanismCatalog.sizeBytes == $cards_size
        and (if $proposal_hash == ""
             then .symbolicRootProposal == null
             else .symbolicRootProposal.sha256 == $proposal_hash end)
        and (.target | type == "object")
        and (.producers | type == "array")
        and ($selected | length) > 0
        and ($selected | unique | sort) == ([$tasks[].taskId] | unique | sort)
        and ([$tasks[].taskId] | unique | length) == ($tasks | length)
    ' "${index}" >/dev/null \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the target-first schedule index does not commit the canonical task plan"

  # The one task-set membership decode of this iteration. Every later stage
  # reads these rows; the index is frozen beside them and is never re-decoded.
  if ! campaign_member_rows=$(campaign_decode_index_members "${index}"); then
    campaign_fail PLAN ConcolicScheduler "${index}" \
      "the target-first schedule index has an invalid membership schema"
  fi
  [[ -n "${campaign_member_rows}" ]] || campaign_fail PLAN ConcolicScheduler \
    "${index}" "the target-first schedule index names no target member"
  # No per-task re-check of the split below: the digest/membership assertion
  # above already proved that the indexed task ids are exactly the plan's task
  # ids and that no task id repeats in the plan, so each split holds exactly
  # one row by construction.
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    worker="${iteration_dir}/workers/${task}"
    mkdir -p "${worker}"
    jq -c --arg task "${task}" 'select(.taskId == $task)' "${plan}" \
      >"${worker}/execution_task_plan.jsonl"
    campaign_log "member ${role} task=${task} occurrence=${occurrence}"
  done <<<"${campaign_member_rows}"
  campaign_log "planned tasks: $(jq -s 'length' "${plan}") by goal $(jq -r -s '
    group_by(.goalKind) | map("\(.[0].goalKind)=\(length)") | join(" ")' \
    "${plan}")"
}

campaign_task_ids() {
  jq -r -s 'map(.taskId) | join(",")' "$1"
}

# One union instrumentation pass over the whole iteration plan, into that
# iteration's own read-only class tree.
campaign_instrument() {
  local iteration_dir=$1
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local classes="${iteration_dir}/instrumented-classes"
  local ids
  ids=$(campaign_task_ids "${plan}")
  [[ -n "${ids}" ]] || die "the campaign plan published no task id: ${plan}"
  analysis_classes_dir="${classes}"
  export CAUSYNTH_CONCOLIC_TASK_PLAN="${plan}"
  export CAUSYNTH_CONCOLIC_TASK_ID="${ids}"
  do_analyze
  unset CAUSYNTH_CONCOLIC_TASK_PLAN CAUSYNTH_CONCOLIC_TASK_ID
  [[ -n "$(find "${classes}" -name '*.class' -print -quit 2>/dev/null)" ]] \
    || die "union instrumentation wrote no class file: ${classes}"
}

# One fresh workload instance, through the configured adapter. The adapter owns
# how the workload starts; the campaign owns which immutable plan it replays
# and where its evidence lands.
#
# The concolic pass rewrites only the methods this plan selected, so the union
# tree holds those owners and nothing else. The replay classpath is therefore
# that tree in front of the project's own classes: a replay given the tree
# alone loads no workload class it did not rewrite.
campaign_replay() {
  local role=$1 plan=$2 ids=$3 classes=$4 results=$5 worker=$6
  local status=0
  require_nonempty "concolic execution task plan" "${plan}"
  [[ ! -e "${results}" ]] || die \
    "replay output already exists; worker directories are written once: ${results}"
  mkdir -p "${worker}" "$(dirname "${results}")"
  set +e
  campaign_run_adapter "replay(${role})" "${concolic_replay_command}" \
    "CAUSYNTH_CONCOLIC_ROLE=${role}" \
    "CAUSYNTH_CONCOLIC_TASK_PLAN=${plan}" \
    "CAUSYNTH_CONCOLIC_TASK_ID=${ids}" \
    "CAUSYNTH_CONCOLIC_RESULTS=${results}" \
    "CAUSYNTH_CONCOLIC_CLASSES=${classes}" \
    "CAUSYNTH_CONCOLIC_CLASSPATH=${classes}:${project_classpath}" \
    "CAUSYNTH_CONCOLIC_WORKER_DIR=${worker}" \
    "CAUSYNTH_CONCOLIC_MAX_TASKS=${schedule_max_jobs}" \
    "CAUSYNTH_TRACE_TEST=${trace_test}" >"${worker}/replay.log" 2>&1
  status=$?
  set -e
  # A workload whose target branch throws exits nonzero by design, so the gate
  # is the evidence it published and not its exit code. An empty result is
  # always a failure, and it is reported with the path that is empty.
  [[ -s "${results}" ]] || campaign_fail REPLAY WORKLOAD "${results}" \
    "the concolic replay published no result (exit ${status}); see ${worker}/replay.log"
  campaign_log "replay role=${role} exit=${status} result=${results}"
}

campaign_session_replay() {
  local iteration_dir=$1
  local seed="${iteration_dir}/seed-result"
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local results="${seed}/concolic_region_results.jsonl"
  local ids published selected member worker member_results status=0
  local -a pids=()
  ids=$(campaign_task_ids "${plan}")
  mkdir -p "${seed}/tasks"
  : >"${results}"
  for selected in ${ids//,/ }; do
    member="${iteration_dir}/workers/${selected}/execution_task_plan.jsonl"
    worker="${seed}/tasks/${selected}"
    member_results="${worker}/concolic_region_results.jsonl"
    (
      set -euo pipefail
      campaign_replay worker "${member}" "${selected}" \
        "${iteration_dir}/instrumented-classes" "${member_results}" "${worker}"
    ) &
    pids+=("$!")
    if [[ ${#pids[@]} -eq ${concolic_worker_count} ]]; then
      campaign_wait_workers "${pids[@]}" || status=1
      pids=()
    fi
  done
  if [[ ${#pids[@]} -gt 0 ]]; then
    campaign_wait_workers "${pids[@]}" || status=1
  fi
  [[ "${status}" -eq 0 ]] || campaign_fail REPLAY WORKLOAD "${seed}/tasks" \
    "one or more parallel seed replays failed"
  for selected in ${ids//,/ }; do
    member_results="${seed}/tasks/${selected}/concolic_region_results.jsonl"
    cat -- "${member_results}" >>"${results}"
  done
  require_nonempty "session replay results" "${results}"
  # A planned task the replay never reached is a terminal condition, not a
  # campaign failure: it is named here and classified by the importer, which
  # is the layer that knows whether the occurrence was skipped, cut short, or
  # simply not activated on this schedule.
  published=$(campaign_json result-tasks "${results}" | LC_ALL=C sort -u)
  for selected in ${ids//,/ }; do
    grep -qxF "${selected}" <<<"${published}" || campaign_record_gap \
      "${iteration_dir}" REPLAY_TASK_WITHOUT_RESULT "${selected}" \
      "the session replay published no result row for this planned task"
  done
}

campaign_import_session() {
  local iteration_dir=$1 iteration_id=$2
  local seed="${iteration_dir}/seed-result"
  local summaries="${iteration_dir}/concolic_region_summaries.jsonl"
  local role campaign_id region occurrence goal task
  local status=0
  raw_concolic_results="${seed}/concolic_region_results.jsonl"
  import_task_plan="${iteration_dir}/execution_task_plan.jsonl"
  imported_summaries="${summaries}"
  import_diagnostics="${seed}/import_diagnostics.jsonl"
  import_topology_delta="${seed}/topology_delta.jsonl"
  set +e
  do_import "${iteration_id}"
  status=$?
  set -e
  if [[ "${status}" -ne 0 ]]; then
    [[ ! -s "${import_diagnostics}" ]] \
      || jq -c . "${import_diagnostics}" >&2 || true
    campaign_fail IMPORT ConcolicSummaryImporter "${import_diagnostics}" \
      "the campaign raw results could not be strictly imported"
  fi
  require_nonempty "imported region summaries" "${summaries}"
  # Fan the importer's own rows out to the member directories the workers use.
  # A member the importer wrote nothing for keeps an empty file and a named
  # gap; it is not admitted here and it does not stop the iteration.
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    campaign_json select-summary "${summaries}" "${task}" \
      >"${iteration_dir}/workers/${task}/concolic_region_summaries.jsonl"
    [[ -s "${iteration_dir}/workers/${task}/concolic_region_summaries.jsonl" ]] \
      || campaign_record_gap "${iteration_dir}" IMPORT_WITHOUT_SUMMARY \
        "${task}" "the importer published no summary for this member task"
  done <<<"${campaign_member_rows}"
  campaign_log "imported summaries: $(wc -l <"${summaries}")"
}

# Schedule pass two. The first pass has no summaries and cannot build the
# target's solver query; this pass hands the scheduler this iteration's own
# imported summaries and lets it publish that query. The shell no longer picks
# the target member out of the index and re-runs the scheduler restricted to
# it, and it does not re-decide what a solver-ready query is: the frozen index
# already names the target and TargetReachPathQueryBuilder already refuses a
# seed that is not exactly one ready target query.
#
# It writes into its own directory because the scheduler always publishes a
# task plan and an index beside its queries, and this iteration's frozen plan
# is not rewritable.
campaign_seed_query() {
  local iteration_dir=$1
  local query_dir="${iteration_dir}/seed-query"
  mkdir -p "${query_dir}"
  schedule_output_dir="${query_dir}"
  schedule_summaries="${iteration_dir}/concolic_region_summaries.jsonl"
  # Reuse the same canonical target-first closure used by PLAN.  The old
  # unconstrained schedule rebuilt unrelated candidates until max-jobs and
  # could truncate the selected target before its imported summary emitted
  # the one branch query this pass exists to publish.
  do_schedule
  [[ -s "${query_dir}/branch_queries.jsonl" ]] || campaign_record_gap \
    "${iteration_dir}" TARGET_QUERY_ABSENT "${iteration_dir}" \
    "the scheduler published no branch query from the imported summaries"
}

campaign_report_worklist() {
  local planner_dir=$1
  echo "[campaign] path planner artifacts: ${planner_dir}" >&2
  jq -r '
    "  state=\(.state)",
    (.gaps[]?
      | "  blocking-gap kind=\(.kind) reason=\(.reason) site=\(.siteId) occurrence=\(.occurrence) path=\(.pathKey)"),
    (.deferredObservations[]?
      | "  deferred kind=\(.kind) reason=\(.reason) site=\(.siteId) occurrence=\(.occurrence) path=\(.pathKey)")
  ' "${planner_dir}/region_path_manifest.json" >&2 || true
}

campaign_report_wave() {
  local wave_dir=$1
  local worker
  echo "[campaign] failed obligation wave: ${wave_dir}" >&2
  while IFS= read -r worker; do
    [[ ! -s "${worker}/exploration_record.jsonl" ]] || continue
    echo "  failed obligation: ${worker}" >&2
    if [[ -s "${worker}/path_flip_solver_result.json" ]]; then
      jq -r '"    solver-status=\(.status // "missing") reason=\(.reason // "")"' \
        "${worker}/path_flip_solver_result.json" >&2 || true
    fi
    [[ ! -s "${worker}/stderr.log" ]] \
      || { echo "    stderr tail:" >&2; tail -n 20 "${worker}/stderr.log" >&2; }
  done < <(find "${wave_dir}" -mindepth 1 -maxdepth 1 -type d \
    | LC_ALL=C sort)
}

# One obligation: solve the flip, replay it in its own fresh workload instance,
# strictly import the result, and admit it only against its own planned task.
campaign_worker_task() {
  local query_key=$1 worklist=$2 tasks=$3 classes=$4 worker=$5 iteration_id=$6
  local outcome replay_task reason status=0
  local raw="${worker}/concolic_region_results.jsonl"
  local imported="${worker}/concolic_region_summaries.jsonl"
  set +e
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipSolver \
    --worklist "${worklist}" \
    --task-plan "${tasks}" \
    --query-key "${query_key}" \
    --output-dir "${worker}" \
    --z3 "${z3_bin}" \
    --solver-timeout-ms "${solver_timeout_ms}"
  status=$?
  set -e
  require_nonempty "path solver result" \
    "${worker}/path_flip_solver_result.json"
  [[ "${status}" -eq 0 ]] || die "the path solver failed with exit ${status}"
  outcome=$(jq -er '.status' "${worker}/path_flip_solver_result.json")
  # The solver owns what a finished flip is. ConcolicPathFlipSolver exits 0
  # for UNSAT, UNSUPPORTED and MATERIALIZATION_GAP alike, calling all three
  # "recorded terminal exploration outcomes, not process failures", and the
  # planner records them by queryKey so the flip is not proposed again.
  # Killing the worker on two of them made the shell overrule the semantic
  # owner: one unmaterializable flip out of twenty-one failed the whole
  # obligation wave, and the producer relation it was exploring was
  # discarded rather than published with its gap named.
  case "${outcome}" in
    UNSAT|UNSUPPORTED|MATERIALIZATION_GAP)
      jq -c '{schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD", queryKey,
              regionId, sourcePathKey, sourceSummaryId, status, solverInputHash}' \
        "${worker}/path_flip_solver_result.json" \
        >"${worker}/exploration_record.jsonl"
      return 0
      ;;
  esac
  [[ "${outcome}" == "SAT_MODEL_READY" ]] \
    || die "the path flip is not solver-backed: ${outcome}"
  replay_task=$(jq -er -s '
    if length == 1 then .[0].taskId else error("expected one replay task") end
  ' "${worker}/execution_task_plan.jsonl")

  campaign_replay worker "${worker}/execution_task_plan.jsonl" \
    "${replay_task}" "${classes}" "${raw}" "${worker}"
  raw_concolic_results="${raw}"
  import_task_plan="${worker}/execution_task_plan.jsonl"
  imported_summaries="${imported}"
  import_diagnostics="${worker}/import_diagnostics.jsonl"
  import_topology_delta="${worker}/topology_delta.jsonl"
  set +e
  do_import "${iteration_id}"
  status=$?
  set -e
  if [[ "${status}" -ne 0 && ! -s "${import_diagnostics}" ]]; then
    die "the importer failed without a semantic diagnostic for ${query_key} (exit ${status})"
  fi
  if [[ ! -s "${imported}" ]]; then
    [[ -f "${import_diagnostics}" ]] || die \
      "the importer published no diagnostics for ${query_key}; expected ${import_diagnostics}"
    reason=$(jq -r -s '
      map([(.code // ""), (.detail // "")]
          | map(select(length > 0)) | join(": "))
      | map(select(length > 0)) | unique | join(" | ")
    ' "${import_diagnostics}")
    jq -n -c --arg key "${query_key}" --arg task "${replay_task}" \
      --arg reason "${reason}" \
      '{schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD", queryKey: $key,
        taskId: $task, status: "REPLAY_NOT_ADMITTED", reason: $reason}' \
      >"${worker}/exploration_record.jsonl"
    require_nonempty "path exploration record" \
      "${worker}/exploration_record.jsonl"
    campaign_log "flip ${query_key}: replay admitted no case; recorded REPLAY_NOT_ADMITTED"
    return 0
  fi
  # The record states that this obligation was solved, replayed and imported,
  # and which planned task it belongs to. Whether the imported case is
  # admissible is the importer's decision and is already in its artifacts.
  jq -c -s --arg key "${query_key}" '
    {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD", queryKey: $key,
     regionId: .[0].regionId, taskId: .[0].taskId,
     occurrenceId: .[0].occurrenceId, goalId: .[0].goalId,
     status: (if .[0].goalKind == "OUTPUT_RELATION_CLOSURE"
              then "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
              else "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY" end)}
    ' "${worker}/execution_task_plan.jsonl" \
    >"${worker}/exploration_record.jsonl"
  require_nonempty "path exploration record" \
    "${worker}/exploration_record.jsonl"
}

campaign_publish_wave() {
  local planner_dir=$1 summaries=$2 tasks=$3 records=$4
  local worker worker_list
  local -a summary_inputs task_inputs record_inputs
  summary_inputs=("${summaries}")
  task_inputs=("${tasks}")
  record_inputs=("${records}")
  if ! worker_list=$(find "${planner_dir}" -mindepth 1 -maxdepth 1 \
      -type d -print | LC_ALL=C sort); then
    campaign_fail EXPLORE CAMPAIGN "${planner_dir}" \
      "failed to enumerate completed obligation workers"
  fi
  [[ -n "${worker_list}" ]] || campaign_fail EXPLORE CAMPAIGN \
    "${planner_dir}" "a published obligation wave contains no worker"
  while IFS= read -r worker; do
    require_nonempty "path exploration record" \
      "${worker}/exploration_record.jsonl"
    record_inputs+=("${worker}/exploration_record.jsonl")
    [[ -s "${worker}/execution_task_plan.jsonl" ]] || continue
    require_nonempty "worker raw result" \
      "${worker}/concolic_region_results.jsonl"
    # A replay can validly remove the producer effect it was exploring.  The
    # importer then publishes a diagnostic/delta but no relation summary, and
    # campaign_worker_task records REPLAY_NOT_ADMITTED.  That terminal query
    # belongs in the exploration record set, not in the relation-summary set.
    [[ -s "${worker}/concolic_region_summaries.jsonl" ]] || continue
    task_inputs+=("${worker}/execution_task_plan.jsonl")
    summary_inputs+=("${worker}/concolic_region_summaries.jsonl")
  done <<<"${worker_list}"
  campaign_json combine summaryId "${summaries}" "${summary_inputs[@]}"
  campaign_json combine taskId "${tasks}" "${task_inputs[@]}"
  campaign_json combine queryKey "${records}" "${record_inputs[@]}"
}

# The inner loop for one member: while target-relevant obligations remain in
# this topology, derive immutable subplans from the canonical plan, run them in
# parallel fresh workload instances, import strictly, and merge.
campaign_explore_member() {
  local iteration_dir=$1 iteration_id=$2 role=$3 region=$4
  local occurrence=$5 goal=$6 task=$7
  local member="${iteration_dir}/workers/${task}"
  local classes="${iteration_dir}/instrumented-classes"
  local summaries="${member}/observed_path_summaries.jsonl"
  local tasks="${member}/observed_execution_tasks.jsonl"
  local records="${member}/path_exploration_records.jsonl"
  local planner_dir worker_dir wave=0 status=0 key pid key_rows
  local -a bound_args=() keys=() pids=()

  campaign_json combine summaryId "${summaries}" \
    "${member}/concolic_region_summaries.jsonl"
  campaign_json combine taskId "${tasks}" \
    "${member}/execution_task_plan.jsonl"
  : >"${records}"
  [[ -z "${producer_max_paths_per_region}" ]] \
    || bound_args+=(--max-paths-per-region "${producer_max_paths_per_region}")
  [[ -z "${producer_max_flips_per_path}" ]] \
    || bound_args+=(--max-flips-per-path "${producer_max_flips_per_path}")
  [[ -z "${producer_max_path_tasks}" ]] \
    || bound_args+=(--max-tasks "${producer_max_path_tasks}")

  while true; do
    planner_dir=$(printf '%s/obligations-%04d' "${member}" "${wave}")
    [[ ! -e "${planner_dir}" ]] || die \
      "obligation wave directory already exists: ${planner_dir}"
    mkdir -p "${planner_dir}"
    set +e
    run_java_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
      --summaries "${summaries}" \
      --task-plan "${tasks}" \
      --records "${records}" \
      --output-dir "${planner_dir}" \
      --region-id "${region}" \
      --goal-id "${goal}" \
      "${bound_args[@]}"
    status=$?
    set -e
    require_nonempty "${role} path worklist manifest" \
      "${planner_dir}/region_path_manifest.json"
    if [[ "${status}" -eq 2 ]]; then
      campaign_report_worklist "${planner_dir}"
      campaign_fail EXPLORE RegionPathWorklist \
        "${planner_dir}/region_path_manifest.json" \
        "the ${role} path worklist is not executable"
    fi
    [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE ConcolicPathFlipPlanner \
      "${planner_dir}/region_path_manifest.json" \
      "the ${role} path planner failed with exit ${status}"
    if jq -e '.state == "CLOSED"' \
        "${planner_dir}/region_path_manifest.json" >/dev/null; then
      cp -f "${planner_dir}/region_path_manifest.json" \
        "${member}/path_closure.json"
      cp -f "${planner_dir}/merged_region_summaries.jsonl" \
        "${member}/merged_summary.jsonl"
      break
    fi
    if ! jq -e '.state == "PENDING"' \
        "${planner_dir}/region_path_manifest.json" >/dev/null; then
      campaign_fail EXPLORE RegionPathWorklist \
        "${planner_dir}/region_path_manifest.json" \
        "the ${role} path planner published no pending or closed state"
    fi
    if ! key_rows=$(campaign_decode_worklist_keys \
        "${planner_dir}/region_path_worklist.jsonl" \
        "${concolic_worker_count}"); then
      campaign_fail EXPLORE RegionPathWorklist \
        "${planner_dir}/region_path_worklist.jsonl" \
        "the pending path worklist is missing or malformed"
    fi
    keys=()
    [[ -z "${key_rows}" ]] || mapfile -t keys <<<"${key_rows}"
    if [[ ${#keys[@]} -eq 0 ]]; then
      campaign_fail EXPLORE RegionPathWorklist \
        "${planner_dir}/region_path_worklist.jsonl" \
        "a pending ${role} worklist named no deterministic obligation"
    fi
    campaign_log "${role} wave ${wave}: ${#keys[@]} obligation(s), workers=${concolic_worker_count}"
    pids=()
    for key in "${keys[@]}"; do
      worker_dir="${planner_dir}/${key}"
      mkdir -p "${worker_dir}"
      (
        set -euo pipefail
        campaign_worker_task "${key}" \
          "${planner_dir}/region_path_worklist.jsonl" "${tasks}" \
          "${classes}" "${worker_dir}" "${iteration_id}"
      ) >"${worker_dir}/stdout.log" 2>"${worker_dir}/stderr.log" &
      pids+=("$!")
    done
    status=0
    campaign_wait_workers "${pids[@]}" || status=1
    if [[ "${status}" -ne 0 ]]; then
      campaign_report_wave "${planner_dir}"
      campaign_fail EXPLORE CAMPAIGN "${planner_dir}" \
        "the ${role} obligation wave ${wave} did not finish"
    fi
    campaign_publish_wave "${planner_dir}" "${summaries}" "${tasks}" \
      "${records}"
    wave=$((wave + 1))
  done
  [[ -s "${member}/merged_summary.jsonl" || "${role}" == "TARGET" ]] \
    || campaign_fail EXPLORE RegionPathWorklist "${member}" \
      "the ${role} member left no closed relation behind"
  campaign_log "${role} exploration stopped after ${wave} wave(s)"
}

# The builder requires exactly one solver-ready target seed and publishes the
# exact observed target paths it can justify.
campaign_target_reach_query() {
  local iteration_dir=$1 task=$2
  local member="${iteration_dir}/workers/${task}"
  local resolved="${causynth_output_dir}/target_resolved.json"
  local exception="" status=0
  [[ ! -s "${resolved}" ]] \
    || exception=$(jq -r '.exception // ""' "${resolved}")
  if [[ -z "${exception}" ]]; then
    campaign_fail EXPLORE TargetReachPathQueryBuilder "${resolved}" \
      "no target attestation names the selected exception"
  fi
  set +e
  run_java_main \
    edu.uva.liftlab.graphchecker.concolic.TargetReachPathQueryBuilder \
    --summaries "${member}/observed_path_summaries.jsonl" \
    --path-manifest "${member}/path_closure.json" \
    --seed-query "${iteration_dir}/seed-query/branch_queries.jsonl" \
    --output "${member}/reach_query.jsonl" >/dev/null
  status=$?
  set -e
  if [[ "${status}" -ne 0 || ! -s "${member}/reach_query.jsonl" ]]; then
    campaign_fail EXPLORE TargetReachPathQueryBuilder "${member}" \
      "TargetReachPathQueryBuilder published no exact reach query (exit ${status})"
  fi
  campaign_log "target reach paths: $(jq -r '.paths | length' \
    "${member}/reach_query.jsonl")"
}

campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local role campaign_id region occurrence goal task target_task=""
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    if [[ ! -s "${iteration_dir}/workers/${task}/concolic_region_summaries.jsonl" ]]; then
      campaign_fail EXPLORE ConcolicSummaryImporter \
        "${iteration_dir}/workers/${task}" \
        "this member has no imported summary to explore from"
    fi
    campaign_explore_member "${iteration_dir}" "${iteration_id}" \
      "${role}" "${region}" "${occurrence}" "${goal}" "${task}"
    if [[ "${role}" == "TARGET" ]]; then
      target_task=${task}
    fi
  done <<<"${campaign_member_rows}"
  [[ -z "${target_task}" ]] \
    || campaign_target_reach_query "${iteration_dir}" "${target_task}"
}

# Classification is the importer's; this collects the rows it wrote, sorts them
# deterministically, and publishes them as this iteration's delta. An iteration
# whose importer declared nothing has an empty delta, which is a topology that
# did not change, not evidence that nothing happened.
campaign_classify() {
  local iteration_dir=$1 iteration=$2
  local diagnostics="${iteration_dir}/import_diagnostics.jsonl"
  local published="${iteration_dir}/topology_delta.jsonl"
  local counts source_list delta_list
  local -a sources=()
  local -a deltas=()
  if ! source_list=$(find "${iteration_dir}" -type f \
      -name 'import_diagnostics.jsonl' -not -path "${diagnostics}" \
      | LC_ALL=C sort); then
    campaign_fail CLASSIFY CAMPAIGN "${iteration_dir}" \
      "failed to enumerate importer diagnostics"
  fi
  [[ -z "${source_list}" ]] || mapfile -t sources <<<"${source_list}"
  : >"${diagnostics}"
  [[ ${#sources[@]} -eq 0 ]] || cat "${sources[@]}" >>"${diagnostics}"
  # The delta rows are the importer's, read from the artifacts it wrote.  The
  # diagnostics are collected too, because a refusal names its own gap there.
  if ! delta_list=$(find "${iteration_dir}" -type f \
      -name 'topology_delta.jsonl' -not -path "${published}" \
      | LC_ALL=C sort); then
    campaign_fail CLASSIFY CAMPAIGN "${iteration_dir}" \
      "failed to enumerate topology deltas"
  fi
  [[ -z "${delta_list}" ]] || mapfile -t deltas <<<"${delta_list}"
  if ! counts=$(campaign_json delta "${iteration}" "${published}" \
      "${deltas[@]}" "${diagnostics}"); then
    campaign_fail CLASSIFY CAMPAIGN "${published}" \
      "failed to validate or aggregate topology deltas"
  fi
  campaign_delta_rows=${counts%% *}
  campaign_delta_divergences=${counts##* }
  campaign_log "topology delta rows=${campaign_delta_rows} divergences=${campaign_delta_divergences}"
}

campaign_publish_iteration_manifest() {
  local iteration_dir=$1 iteration=$2 parent=$3
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local members="${iteration_dir}/.members.jsonl"
  local role campaign_id region occurrence goal task worker
  local obligations plan_sha index_sha summaries_sha
  : >"${members}"
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    worker="${iteration_dir}/workers/${task}"
    if ! obligations=$(find "${worker}" -mindepth 2 -maxdepth 2 \
        -type d -path '*/obligations-*/*' -printf '%f\n' \
        | LC_ALL=C sort \
        | jq -R -s 'split("\n") | map(select(length > 0))'); then
      campaign_fail EMIT CAMPAIGN "${worker}" \
        "failed to enumerate path obligation digests"
    fi
    jq -n --arg role "${role}" --arg campaign "${campaign_id}" \
      --arg region "${region}" --arg occurrence "${occurrence}" \
      --arg goal "${goal}" --arg task "${task}" --arg dir "${worker}" \
      --argjson obligations "${obligations}" \
      '{role: $role, campaignId: $campaign, regionId: $region,
        occurrenceId: $occurrence, goalId: $goal, taskId: $task,
        workerDir: $dir, obligationDigests: $obligations}' \
      >>"${members}"
  done <<<"${campaign_member_rows}"
  if ! plan_sha=$(campaign_digest \
      "${iteration_dir}/execution_task_plan.jsonl"); then
    campaign_fail EMIT CAMPAIGN \
      "${iteration_dir}/execution_task_plan.jsonl" \
      "failed to digest the frozen execution task plan"
  fi
  if ! index_sha=$(campaign_digest "${index}"); then
    campaign_fail EMIT CAMPAIGN "${index}" \
      "failed to digest the frozen schedule index"
  fi
  if ! summaries_sha=$(campaign_digest \
      "${iteration_dir}/concolic_region_summaries.jsonl"); then
    campaign_fail EMIT CAMPAIGN \
      "${iteration_dir}/concolic_region_summaries.jsonl" \
      "failed to digest the imported summaries"
  fi
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg iteration "${iteration}" \
    --arg parent "${parent}" \
    --arg plan "${iteration_dir}/execution_task_plan.jsonl" \
    --arg planSha "${plan_sha}" \
    --arg index "${index}" --arg indexSha "${index_sha}" \
    --arg summaries "${iteration_dir}/concolic_region_summaries.jsonl" \
    --arg summariesSha "${summaries_sha}" \
    --arg classes "${iteration_dir}/instrumented-classes" \
    --argjson workers "${concolic_worker_count}" \
    --argjson deltaRows "${campaign_delta_rows}" \
    --argjson divergences "${campaign_delta_divergences}" \
    --slurpfile members "${members}" '
    {schemaVersion: 1,
     kind: "CAMPAIGN_ITERATION_MANIFEST",
     iterationId: $iteration,
     parentIterationId: $parent,
     provenance: $provenance,
     executionTaskPlan: {path: $plan, sha256: $planSha},
     scheduleIndex: {path: $index, sha256: $indexSha},
     importedSummaries: {path: $summaries, sha256: $summariesSha},
     instrumentedClasses: $classes,
     externalWorkerCount: $workers,
     topologyDelta: {rows: $deltaRows, divergences: $divergences},
     members: $members}
  ' >"${iteration_dir}/iteration_manifest.json"
  rm -f "${members}"
  require_nonempty "iteration manifest" \
    "${iteration_dir}/iteration_manifest.json"
  ln -sfn "$(basename "${iteration_dir}")" "${campaign_root}/latest"
}

# The composition consumes one closed relation for every selected producer.
campaign_compose() {
  local iteration_dir=$1
  local role campaign_id region occurrence goal task
  local target_task="" target_region="" target_occurrence=""
  local status=0
  local -a merged=()
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    if [[ "${role}" == "TARGET" ]]; then
      target_task=${task}
      target_region=${region}
      target_occurrence=${occurrence}
      continue
    fi
    [[ -s "${iteration_dir}/workers/${task}/merged_summary.jsonl" ]] \
      || campaign_fail COMPOSE RegionPathWorklist \
        "${iteration_dir}/workers/${task}" \
        "selected producer has no closed relation"
    merged+=("${iteration_dir}/workers/${task}/merged_summary.jsonl")
  done <<<"${campaign_member_rows}"
  [[ -n "${target_task}" ]] || campaign_fail COMPOSE ConcolicScheduler \
    "${iteration_dir}/runtime_workflow_schedule_index.json" \
    "the frozen schedule index names no target member"
  [[ ! -e "${campaign_final}" ]] || die \
    "the final directory already exists: ${campaign_final}"
  mkdir -p "${campaign_final}"
  fatal_queries="${iteration_dir}/workers/${target_task}/reach_query.jsonl"
  require_nonempty "target reach query" "${fatal_queries}"
  compose_summary_inputs=$(IFS=:; printf '%s' "${merged[*]}")
  composed_smt="${campaign_final}/candidate.smt2"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  fatal_region="${target_region}"
  fatal_occurrence_id="${target_occurrence}"
  set +e
  do_compose >/dev/null
  status=$?
  set -e
  [[ "${status}" -eq 0 ]] || campaign_fail COMPOSE ConcolicSmtComposer \
    "${composition_manifest}" \
    "the Composer failed with exit ${status} on inputs it was given"
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${composition_manifest}"
}

# The solver stage refuses a composition it may not conclude from and exits 2
# on a gapped one. Both are outcomes the campaign publishes rather than hides.
campaign_solve() {
  local status=0
  reach_report="${campaign_final}/z3-result.json"
  set +e
  do_reach >/dev/null
  status=$?
  set -e
  require_nonempty "Z3 result" "${reach_report}"
  [[ "${status}" -eq 0 || "${status}" -eq 2 ]] \
    || die "the solver stage failed with exit ${status}: ${reach_report}"
  campaign_log "z3 state=$(jq -r '.state' "${reach_report}") reachability=$(jq -r '.reachCondition.reachability' "${reach_report}")"
  campaign_print_symbolic_variable_models "${reach_report}" \
    || die "the solver result has no valid symbolic variable model: ${reach_report}"
}

campaign_artifact_digests() {
  local name path bytes sha row
  local -a required=(candidate.smt2 candidate_composition_manifest.json
    z3-result.json path-closures.json gaps.json result.json)
  local -a names=()
  local -a rows=()
  for name in "${required[@]}"; do
    path="${campaign_final}/${name}"
    [[ -s "${path}" ]] || {
      echo "required final artifact is missing or empty: ${path}" >&2
      return 1
    }
    names+=("${name}")
  done
  for name in "${names[@]}"; do
    path="${campaign_final}/${name}"
    if ! bytes=$(wc -c <"${path}"); then return 1; fi
    if ! sha=$(campaign_digest "${path}"); then return 1; fi
    if ! row=$(jq -n -c --arg name "${name}" --arg path "${path}" \
        --argjson bytes "${bytes}" --arg sha256 "${sha}" \
        '{name: $name, path: $path, bytes: $bytes, sha256: $sha256}'); then
      return 1
    fi
    rows+=("${row}")
  done
  printf '%s\n' "${rows[@]}" | jq -c -s .
}

# Aggregate the already-validated owner reports without copying their contents
# into exec argv.  Real compositions and topology deltas routinely exceed both
# Linux's per-argument limit and ARG_MAX, so every JSON input is a file.
campaign_write_coverage_gaps() {
  local composition=$1 reach=$2 diagnostics=$3 delta=$4
  local path_closures=$5 output=$6
  jq -n \
    --slurpfile composedDocuments "${composition}" \
    --slurpfile reachDocuments "${reach}" \
    --slurpfile diagnostics "${diagnostics}" \
    --slurpfile delta "${delta}" \
    --slurpfile pathClosureDocuments "${path_closures}" '
    $composedDocuments[0] as $composed |
    $reachDocuments[0] as $reach |
    $pathClosureDocuments[0] as $pathClosures |
    ([$composed.finalStatusRefusals[]?
         | {stage: "COMPOSE", source: "COMPOSER",
            code: .code, subject: .subject, detail: .detail}]
       + [$reach.gaps[]?
           | {stage: "SOLVE", source: "SOLVER", code: ., subject: "",
              detail: ""}]
       + [$pathClosures[]? as $closure
           | $closure.coverageGaps[]?
           | {stage: "EXPLORE", source: "PATH_WORKLIST",
              code: (.kind // ""),
              subject: (.queryKey // .regionId
                        // .evidenceIdentity.taskId // ""),
              detail: ([(.reason // ""), (.detail // "")]
                       | map(select(. != "")) | join(": "))}]
       | unique_by([.stage, .source, .code, .subject, .detail])) as $gaps |
    ([$composed.canonicalModel.gaps[]?
           | {stage: "MODEL", source: (.source // "COMPOSER"),
              code: (.code // ""), subject: (.subject // ""),
              detail: (.detail // "")}]
       + [$diagnostics[]?
           | {stage: "IMPORT", source: "IMPORTER", code: (.code // ""),
              subject: (.taskId // ""), detail: (.detail // "")}]
       + [$delta[]? | select(.deltaKind == "COVERAGE_GAP"
             or .deltaKind == "TOPOLOGY_DIVERGENCE")
           | {stage: "CLASSIFY", source: (.source // "IMPORTER"),
              code: (.code // .deltaKind), subject: (.taskId // ""),
              detail: (.reason // .gap // "")}]
       | unique_by([.stage, .source, .code, .subject, .detail]))
       as $telemetry |
    {schemaVersion: 1,
     kind: "CAMPAIGN_COVERAGE_GAPS",
     gaps: $gaps,
     telemetryGaps: $telemetry}
    | .gapCount = (.gaps | length)
    | .telemetryCount = (.telemetryGaps | length)
    | .byStage = (.gaps | group_by(.stage)
        | map({key: .[0].stage, value: length}) | from_entries)
    | .telemetryByStage = (.telemetryGaps | group_by(.stage)
        | map({key: .[0].stage, value: length}) | from_entries)
  ' >"${output}"
}

# The named outputs. Nothing here recomputes a verdict: every field is copied
# from the stage that decided it, and the claim is read off those states.
campaign_emit() {
  local iteration_dir=$1
  local replay_rows replay_bytes gapCount raw_result_list
  local path_closures_artifact="${campaign_final}/path-closures.json"
  local artifacts_json stages_json iterations_json
  local -a raw_results=()
  # Before anything is published: the generation this run was frozen on must
  # still be the generation on disk.
  campaign_verify_frozen_inputs
  if ! raw_result_list=$(find "${iteration_dir}" -type f \
      -name 'concolic_region_results.jsonl' -print | LC_ALL=C sort); then
    campaign_fail EMIT CAMPAIGN "${iteration_dir}" \
      "failed to enumerate raw replay results"
  fi
  [[ -z "${raw_result_list}" ]] || mapfile -t raw_results \
    <<<"${raw_result_list}"
  [[ ${#raw_results[@]} -gt 0 ]] || die \
    "the iteration published no raw replay result: ${iteration_dir}"

  # One readable document each, because the reads below are jq invocations
  # that would otherwise hide a producer's parse failure behind their own
  # successful exit. What schemaVersion and kind those documents declare is
  # the Composer's and the extractor's own contract, published by the layer
  # that writes them; the shell does not restate it.
  campaign_require_json "candidate composition manifest" \
    "${composition_manifest}" || campaign_fail EMIT ConcolicSmtComposer \
      "${composition_manifest}" "required composition JSON is malformed"
  campaign_require_json "Z3 reachability result" "${reach_report}" \
    || campaign_fail EMIT BooleanReachConditionExtractor "${reach_report}" \
      "required reachability JSON is malformed"
  if ! campaign_jsonl_array "import diagnostics" \
      "${iteration_dir}/import_diagnostics.jsonl" >/dev/null; then
    campaign_fail EMIT ConcolicSummaryImporter \
      "${iteration_dir}/import_diagnostics.jsonl" \
      "required diagnostics JSONL is missing or malformed"
  fi
  if ! campaign_jsonl_array "topology delta" \
      "${iteration_dir}/topology_delta.jsonl" >/dev/null; then
    campaign_fail EMIT ConcolicSummaryImporter \
      "${iteration_dir}/topology_delta.jsonl" \
      "required topology-delta JSONL is missing or malformed"
  fi
  if ! campaign_materialize_path_closures \
      "${iteration_dir}/workers" "${path_closures_artifact}"; then
    campaign_fail EMIT RegionPathWorklist "${iteration_dir}/workers" \
      "a path-closure JSON is malformed or could not be enumerated"
  fi

  # A selected path closure must be complete; its coverage gaps are blockers.
  campaign_write_coverage_gaps \
    "${composition_manifest}" \
    "${reach_report}" \
    "${iteration_dir}/import_diagnostics.jsonl" \
    "${iteration_dir}/topology_delta.jsonl" \
    "${path_closures_artifact}" \
    "${campaign_final}/gaps.json"
  require_nonempty "campaign gaps" "${campaign_final}/gaps.json"
  campaign_require_json "campaign gaps" "${campaign_final}/gaps.json" \
    || campaign_fail EMIT CAMPAIGN "${campaign_final}/gaps.json" \
      "the generated gaps JSON is malformed"

  # The claim is copied from the Composer and solver decisions.
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --slurpfile composedDocuments "${composition_manifest}" \
    --slurpfile reachDocuments "${reach_report}" \
    --slurpfile gapDocuments "${campaign_final}/gaps.json" '
    $composedDocuments[0] as $c | $reachDocuments[0] as $r |
    $gapDocuments[0] as $gaps |
    ($r.reachCondition.reachability // "UNKNOWN") as $reachability |
    ($r.unsatClosureComplete // false) as $unsatClosureComplete |
    ($gaps.gapCount) as $gapCount |
    ($gaps.telemetryCount) as $telemetryCount |
    (($c.finalStatusRefusals // []) | length) as $blockers |
    ($c.finalStatus == "FINAL_READY") as $accepted |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     provenance: $provenance,
     claim: (
       if $accepted and $reachability == "REACHABLE" then "SAT_CANDIDATE"
       elif $accepted and $reachability == "UNREACHABLE"
            and $unsatClosureComplete then "UNSAT_CLOSED"
       else "INCONCLUSIVE_PARTIAL" end),
     claimReason: (
       if ($c.finalStatus != "FINAL_READY") then
         ("the Composer published finalStatus=" + ($c.finalStatus // "none")
           + " with " + ($blockers | tostring) + " selected blocker(s): "
           + (([$c.finalStatusRefusals[]? | .code] | unique | join(","))))
       elif $reachability == "REACHABLE" then
         "a valuation satisfies the target predicate inside the recorded model"
       elif $reachability == "UNREACHABLE" and $unsatClosureComplete then
         "no valuation satisfies the target predicate and the selected model is closed"
       elif $reachability == "UNREACHABLE" then
         "the solver reported no valuation but did not publish closed selected-path authority"
       else "the solver stage reached no exact reachability decision" end),
     reachability: $reachability,
     solverState: ($r.state // ""),
     finalStatus: ($c.finalStatus // ""),
     finalStatusRefusals: $blockers,
     freeSymbolCount: (($c.freeSymbols // []) | length),
     evidence: {
       exactBindings: ($c.canonicalModel.counts.exactBindings // 0),
       guardedBindings: ($c.canonicalModel.counts.guardedBindings // 0),
       unknownArmBindings: ($c.canonicalModel.counts.unknownArmBindings // 0),
       candidateBindings: ($c.canonicalModel.counts.candidateBindings // 0),
       unsatClosureComplete: $unsatClosureComplete,
       fieldVersions: ($c.canonicalModel.counts.fieldVersions // 0),
       fieldReads: ($c.canonicalModel.counts.fieldReads // 0)},
     gapCount: $gapCount,
     telemetryCount: $telemetryCount,
     valuations: ($r.valuations // [])}
  ' >"${campaign_final}/result.json"
  require_nonempty "campaign result" "${campaign_final}/result.json"

  replay_rows=$(wc -l "${raw_results[@]}" | tail -n 1 | awk '{print $1}')
  replay_bytes=$(stat -c '%s' "${raw_results[@]}" | awk '{n += $1} END {print n + 0}')
  if ! artifacts_json=$(campaign_artifact_digests); then
    campaign_fail EMIT CAMPAIGN "${campaign_final}" \
      "failed to validate final artifact digests"
  fi
  if ! stages_json=$(jq -e -R -s 'split("\n")
      | map(select(length > 0) | split("\t"))
      | if all(.[]; length == 2 and (.[1] | test("^[0-9]+$")))
        then map({stage: .[0], wallMillis: (.[1] | tonumber)})
        else error("invalid campaign stage metric") end' \
      "${campaign_stage_metrics}"); then
    campaign_fail EMIT CAMPAIGN "${campaign_stage_metrics}" \
      "campaign stage metrics are malformed"
  fi
  if ! iterations_json=$(campaign_iteration_manifests_json \
      "${campaign_root}"); then
    campaign_fail EMIT CAMPAIGN "${campaign_root}" \
      "iteration manifests are absent or malformed"
  fi
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg root "${campaign_root}" \
    --arg final "${campaign_final}" \
    --argjson artifacts "${artifacts_json}" \
    --argjson replayRows "${replay_rows}" \
    --argjson replayBytes "${replay_bytes}" \
    --argjson stages "${stages_json}" \
    --argjson iterations "${iterations_json}" '
    {schemaVersion: 1,
     kind: "CAMPAIGN_RUN_MANIFEST",
     campaignRoot: $root,
     outputDir: $final,
     provenance: $provenance,
     iterations: $iterations,
     artifacts: $artifacts,
     metrics: {stageWallMillis: $stages,
               totalStageWallMillis: ([$stages[] | .wallMillis] | add // 0),
               replayResultRows: $replayRows,
               replayResultBytes: $replayBytes}}
  ' >"${campaign_final}/run-manifest.json"
  require_nonempty "campaign run manifest" \
    "${campaign_final}/run-manifest.json"

  gapCount=$(jq -r '.gapCount' "${campaign_final}/gaps.json")
  campaign_log "artifacts in ${campaign_final}"
  jq -r '"  claim=\(.claim) reachability=\(.reachability) gaps=\(.gapCount) telemetry=\(.telemetryCount) finalStatus=\(.finalStatus)"' \
    "${campaign_final}/result.json"
  # A published artifact set is not an accepted candidate. A run that reached
  # no witness and no closed refutation exits nonzero with its own named
  # reason, because a top-level zero exit is not completion.
  case "$(jq -r '.claim' "${campaign_final}/result.json")" in
    SAT_CANDIDATE|UNSAT_CLOSED) ;;
    *)
      jq -r '"[campaign] no accepted candidate: claim=\(.claim) reason=\(.claimReason)"' \
        "${campaign_final}/result.json" >&2
      exit 2
      ;;
  esac
  # The claim belongs to the Composer and the solver; the gap count belongs to
  # every owner that published one, and README "Completion criteria" requires
  # both -- an accepted witness and no unresolved gap. The two stay apart on
  # purpose: the gap rows never re-score the claim, so result.json still
  # reports exactly what the semantic owners decided. But a claim reached with
  # named gaps still open is not a run anybody may stop on, so the gate refuses
  # it here, under its own exit code and its own reason. This is the exit half
  # of the acceptance check README states against result.json; without it a
  # campaign exits 0 on a run that README's own documented jq refuses.
  [[ "${gapCount}" -eq 0 ]] || {
    jq -r '"[campaign] candidate withheld: claim=\(.claim), but the run named "
      + (.gapCount | tostring) + " unresolved gap(s)"' \
      "${campaign_final}/result.json" >&2
    echo "  named gaps: ${campaign_final}/gaps.json" >&2
    exit 3
  }
}

# A declared bound was reached with obligations still open. Publish the named
# gap and stop: an unsolved campaign never becomes an accepted candidate.
campaign_publish_bound_gap() {
  local iterations=$1
  mkdir -p "${campaign_final}"
  jq -n --argjson iterations "${iterations}" \
    --argjson provenance "${campaign_provenance}" \
    '{schemaVersion: 1,
      kind: "CAMPAIGN_COVERAGE_GAPS",
      gapCount: 1,
      byStage: {CLASSIFY: 1},
      provenance: $provenance,
      gaps: [{stage: "CLASSIFY", source: "CAMPAIGN",
              code: "ITERATION_BOUND_REACHED",
              subject: ("campaign_max_iterations=" + ($iterations | tostring)),
              detail: "the topology still diverged at the declared iteration bound; no candidate was composed"}]}' \
    >"${campaign_final}/gaps.json"
  die "the campaign reached campaign_max_iterations=${iterations} with a diverging topology; named gap in ${campaign_final}/gaps.json"
}

do_campaign() {
  local iteration=0 iteration_id="" parent="" carry="" iteration_dir
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  # Refused before any work rather than after the seed: a campaign root that
  # already holds an iteration belongs to another run, and its directories are
  # written once.
  [[ ! -e "${campaign_root}/iteration-0000" && ! -e "${campaign_final}" ]] \
    || die "this campaign root already holds a published run: ${campaign_root}"
  ensure_output_directory "${campaign_root}"
  # Reserve this run before either process can truncate its stage metrics.
  # mkdir is the one atomic claim on a campaign root; every later artifact is
  # immutable beneath the directory owned by the winner.
  mkdir -- "${campaign_root}/frozen-inputs" || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${campaign_root}" \
    "the campaign root is already reserved by another run"
  : >"${campaign_stage_metrics}"

  campaign_stage VALIDATE campaign_validate
  campaign_stage FREEZE_TOOL campaign_freeze_graphchecker_jar
  if [[ -n "${campaign_setup_command}" ]]; then
    campaign_stage SETUP campaign_setup
  fi
  campaign_stage FREEZE campaign_freeze
  campaign_stage SEED campaign_seed

  while [[ "${iteration}" -lt "${campaign_max_iterations}" ]]; do
    iteration_id=$(printf 'iteration-%04d' "${iteration}")
    iteration_dir="${campaign_root}/${iteration_id}"
    [[ ! -e "${iteration_dir}" ]] || die \
      "iteration directory already exists; a campaign never rewrites one: ${iteration_dir}"
    mkdir -p "${iteration_dir}"
    # Every iteration decodes its own membership in PLAN; nothing carries over
    # from the previous one, so a stage can never read a stale member set.
    campaign_member_rows=""
    campaign_stage "PLAN[${iteration}]" campaign_plan "${iteration_dir}" \
      "${carry}"
    campaign_stage "INSTRUMENT[${iteration}]" campaign_instrument \
      "${iteration_dir}"
    campaign_stage "REPLAY[${iteration}]" campaign_session_replay \
      "${iteration_dir}"
    campaign_stage "IMPORT[${iteration}]" campaign_import_session \
      "${iteration_dir}" "${iteration_id}"
    campaign_stage "SEED_QUERY[${iteration}]" campaign_seed_query \
      "${iteration_dir}"
    campaign_stage "EXPLORE[${iteration}]" campaign_explore \
      "${iteration_dir}" "${iteration_id}"
    campaign_stage "CLASSIFY[${iteration}]" campaign_classify \
      "${iteration_dir}" "${iteration_id}"
    campaign_publish_iteration_manifest "${iteration_dir}" "${iteration_id}" \
      "${parent}"
    if [[ "${campaign_delta_divergences}" -gt 0 ]]; then
      # One iteration never adds tasks to its running campaign: a divergence
      # closes this iteration and rebuilds the target frontier in the next one.
      campaign_log "iteration ${iteration} diverged; rebuilding the target frontier"
      carry="${iteration_dir}/concolic_region_summaries.jsonl"
      parent="${iteration_id}"
      iteration=$((iteration + 1))
      continue
    fi
    campaign_stage COMPOSE campaign_compose "${iteration_dir}"
    campaign_stage SOLVE campaign_solve
    campaign_stage EMIT campaign_emit "${iteration_dir}"
    return 0
  done
  campaign_publish_bound_gap "${campaign_max_iterations}"
}

# Produces the semantic compression boundary before any concolic replay.  A
# later campaign uses a different fresh output root and the same content cache.
do_catalog() {
  local iteration_dir
  [[ -z "${causynth_symbolic_root_proposal:-}" ]] \
    || die "catalog must run without a symbolic root proposal"
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  [[ ! -e "${campaign_root}/iteration-0000" \
      && ! -e "${campaign_final}" ]] \
    || die "this catalog root already holds a published run: ${campaign_root}"
  ensure_output_directory "${campaign_root}"
  mkdir -- "${campaign_root}/frozen-inputs" || campaign_fail \
    FREEZE_TOOL CATALOG "${campaign_root}" \
    "the catalog root is already reserved by another run"
  : >"${campaign_stage_metrics}"

  campaign_stage VALIDATE campaign_validate
  campaign_stage FREEZE_TOOL campaign_freeze_graphchecker_jar
  if [[ -n "${campaign_setup_command}" ]]; then
    campaign_stage SETUP campaign_setup
  fi
  campaign_stage FREEZE campaign_freeze
  campaign_stage SEED campaign_seed
  iteration_dir="${campaign_root}/iteration-0000"
  mkdir -p "${iteration_dir}"
  campaign_member_rows=""
  campaign_stage "PLAN[0]" campaign_plan "${iteration_dir}" ""
  campaign_verify_frozen_inputs CATALOG CATALOG "${campaign_root}"
  campaign_log "symbolic-root catalog ready: ${iteration_dir}/symbolic_root_mechanism_cards.json"
}

# Shell-level contract tests source the helpers without dispatching a workflow.
# Production execution still reaches the argument parser below.
if [[ "${BASH_SOURCE[0]}" != "$0" ]]; then
  return 0
fi

while [[ $# -gt 0 ]]; do
  case "$1" in
    --config)
      [[ $# -ge 2 ]] || die "--config requires a file"
      config_file=$2
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *) break ;;
  esac
done

command_name=${1:-help}
[[ $# -eq 0 ]] || shift

case "${command_name}" in
  help)
    usage
    ;;
  campaign|catalog|config|validate)
    [[ -n "${config_file}" ]] || die "${command_name} requires --config FILE"
    initialize_config "${config_file}"
    case "${command_name}" in
      campaign)
        [[ $# -eq 0 ]] || die "campaign takes no extra arguments"
        do_campaign
        ;;
      catalog)
        [[ $# -eq 0 ]] || die "catalog takes no extra arguments"
        do_catalog
        ;;
      config) print_normalized_config ;;
      validate) validate_config ;;
    esac
    ;;
  *)
    die "unknown command '${command_name}' (run './run_engine.sh help')"
    ;;
esac
