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
  ./run_engine.sh --config FILE config|validate
  ./run_engine.sh help

Commands:
  campaign    Run the complete campaign for one configuration: validate, seed,
              then immutable iterations of plan/instrument/replay/import/
              explore/classify until composition and Z3
  config      Print the normalized workflow configuration
  validate    Validate required workflow configuration fields
  help        Print this help message

The campaign is the only production execution path. Environment variables
matching normalized workflow keys may override values loaded from FILE.
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
    workflow_path_base|graphchecker_jar|java_bin|graphchecker_work_dir|project_repo|project_module_dir|project_classes_dir|project_test_classes_dir|project_classpath|analysis_classes_dir|causynth_output_dir|causynth_target_spec|causynth_analysis_scope|causynth_process_dirs|causynth_protocol_stubs|causynth_loop_bounds|causynth_symbolic_inputs|custom_jdk_home|z3_bin|workload_work_dir|workload_command|trace_test|candidate_graph|refined_graph|runtime_region_plan|schedule_output_dir|schedule_max_jobs|solver_timeout_ms|reach_max_inputs|reach_max_valuations|campaign_setup_command|concolic_replay_command|concolic_worker_count|campaign_max_iterations|producer_max_paths_per_region|producer_max_flips_per_path|producer_max_path_tasks)
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
  causynth_target_spec=""
  causynth_analysis_scope=""
  causynth_process_dirs=""
  causynth_protocol_stubs=""
  causynth_loop_bounds=""
  causynth_symbolic_inputs=""
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
  raw_concolic_results=""
  import_task_plan=""
  imported_summaries=""
  import_diagnostics=""
  import_topology_delta=""
  import_iteration_id=""
  merged_summaries=""
  fatal_queries=""
  compose_summary_inputs=""
  composed_smt=""
  composition_manifest=""
  reach_report=""
  fatal_region=""
  fatal_occurrence_id=""
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
  apply_env_override causynth_target_spec CAUSYNTH_TARGET_SPEC
  apply_env_override causynth_analysis_scope CAUSYNTH_ANALYSIS_SCOPE
  apply_env_override causynth_process_dirs CAUSYNTH_PROCESS_DIRS
  apply_env_override causynth_protocol_stubs CAUSYNTH_PROTOCOL_STUBS
  apply_env_override causynth_loop_bounds CAUSYNTH_LOOP_BOUNDS
  apply_env_override causynth_symbolic_inputs CAUSYNTH_SYMBOLIC_INPUTS
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
  local path=$1
  if command -v realpath >/dev/null 2>&1; then
    realpath -m -- "${path}"
  else
    # The repository's existing scripts require realpath. Keep a conservative
    # fallback for environments that only provide pwd.
    case "${path}" in
      /*) printf '%s\n' "${path}" ;;
      *) printf '%s/%s\n' "$(pwd -P)" "${path}" ;;
    esac
  fi
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
  causynth_target_spec=${causynth_target_spec:-@config/target.yaml}
  analysis_classes_dir=${analysis_classes_dir:-${causynth_output_dir}/instrumented-classes}
  custom_jdk_home=${custom_jdk_home:-}
  z3_bin=${z3_bin:-z3}
  workload_work_dir=${workload_work_dir:-${project_module_dir}}
  # Scheduler, solver, replay-wave and topology bounds have no engine defaults.
  # The one production workload states all of them in its frozen configuration.

  graphchecker_jar=$(resolve_path "${graphchecker_jar}")
  graphchecker_work_dir=$(resolve_path "${graphchecker_work_dir}")
  project_module_dir=$(resolve_path "${project_module_dir}" repo)
  project_classes_dir=$(resolve_path "${project_classes_dir}" repo)
  project_test_classes_dir=$(resolve_path "${project_test_classes_dir}" repo)
  causynth_output_dir=$(resolve_path "${causynth_output_dir}")
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
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    causynth_protocol_stubs=$(resolve_path "${causynth_protocol_stubs}")
  fi
  if [[ -n "${causynth_loop_bounds}" ]]; then
    causynth_loop_bounds=$(resolve_path "${causynth_loop_bounds}")
  fi
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    causynth_symbolic_inputs=$(resolve_path "${causynth_symbolic_inputs}")
  fi
  candidate_graph=${candidate_graph:-${causynth_output_dir}/candidate_dataflow_edges.jsonl.gz}
  runtime_region_plan=${runtime_region_plan:-${causynth_output_dir}/runtime/concolic_region_plan.jsonl}
  refined_graph=${refined_graph:-$(dirname "${runtime_region_plan}")/refined_dataflow_edges.jsonl.gz}
  schedule_output_dir=${schedule_output_dir:-${causynth_output_dir}/schedule}
  raw_concolic_results=${raw_concolic_results:-${schedule_output_dir}/concolic_region_results.jsonl}
  import_task_plan=${import_task_plan:-${schedule_output_dir}/execution_task_plan.jsonl}
  imported_summaries=${imported_summaries:-${schedule_output_dir}/concolic_region_summaries.jsonl}
  import_diagnostics=${import_diagnostics:-${schedule_output_dir}/concolic_import_diagnostics.jsonl}
  merged_summaries=${merged_summaries:-${schedule_output_dir}/merged_region_summaries.jsonl}
  fatal_queries=${fatal_queries:-${schedule_output_dir}/branch_queries.jsonl}
  compose_summary_inputs=${compose_summary_inputs:-${merged_summaries}}
  composed_smt=${composed_smt:-${schedule_output_dir}/composed_fatal.smt2}
  composition_manifest=${composition_manifest:-${schedule_output_dir}/composed_smt_manifest.json}
  reach_report=${reach_report:-${schedule_output_dir}/boolean_reach_condition.json}

  candidate_graph=$(resolve_path "${candidate_graph}")
  refined_graph=$(resolve_path "${refined_graph}")
  runtime_region_plan=$(resolve_path "${runtime_region_plan}")
  schedule_output_dir=$(resolve_path "${schedule_output_dir}")
  raw_concolic_results=$(resolve_path "${raw_concolic_results}")
  import_task_plan=$(resolve_path "${import_task_plan}")
  imported_summaries=$(resolve_path "${imported_summaries}")
  import_diagnostics=$(resolve_path "${import_diagnostics}")
  merged_summaries=$(resolve_path "${merged_summaries}")
  fatal_queries=$(resolve_path "${fatal_queries}")
  compose_summary_inputs=$(resolve_path_list "${compose_summary_inputs}")
  composed_smt=$(resolve_path "${composed_smt}")
  composition_manifest=$(resolve_path "${composition_manifest}")
  reach_report=$(resolve_path "${reach_report}")
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
  # The configured protocol mappings describe the transport, so every stage
  # that reasons about a cross-process value needs them, not only the static
  # pass that first resolved their stub methods.
  local -a properties=()
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    properties+=("-Dcausynth.protocol.stubs=${causynth_protocol_stubs}")
  fi
  local runtime_classpath="${graphchecker_jar}"
  if [[ "${main_class}" == \
      edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder ]]; then
    # Boundary-scalar validation resolves configured client interfaces to the
    # concrete callees recorded in the trace.  Keep that hierarchy available
    # to this offline aggregation process just as it was to the recorder.
    runtime_classpath="${runtime_classpath}:${project_classpath}"
  fi
  run_in_directory "${graphchecker_work_dir}" "${java_bin}" \
    "${properties[@]}" \
    -cp "${runtime_classpath}" "${main_class}" "$@"
}

print_normalized_config() {
  local key
  for key in campaign_setup_command concolic_replay_command concolic_worker_count campaign_max_iterations producer_max_paths_per_region producer_max_flips_per_path producer_max_path_tasks config_file workflow_path_base graphchecker_jar java_bin graphchecker_work_dir project_repo project_module_dir project_classes_dir project_test_classes_dir project_classpath analysis_classes_dir causynth_output_dir causynth_target_spec causynth_process_dirs causynth_protocol_stubs causynth_loop_bounds causynth_symbolic_inputs custom_jdk_home z3_bin workload_work_dir workload_command trace_test candidate_graph refined_graph runtime_region_plan schedule_output_dir schedule_max_jobs solver_timeout_ms reach_max_inputs reach_max_valuations; do
    printf '%s=%s\n' "${key}" "${!key}"
  done
}

validate_config() {
  local key
  local missing=0
  for key in project_repo project_module_dir project_classes_dir project_classpath causynth_output_dir causynth_target_spec custom_jdk_home z3_bin workload_command trace_test; do
    if [[ -z "${!key}" ]]; then
      echo "Missing workflow config value: ${key}" >&2
      missing=1
    fi
  done
  [[ ${missing} -eq 0 ]] || return 1
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    require_file "protocol stub mapping" "${causynth_protocol_stubs}"
  fi
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
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
  # Soot starts; there is no second compatibility flag that can override it.
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
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    require_file "protocol stub mapping" "${causynth_protocol_stubs}"
    system_properties+=(
      "-Dcausynth.protocol.stubs=${causynth_protocol_stubs}"
    )
  fi
  # README section 5's per-loop K_L, declared by the campaign that owns the
  # workload. The declarations are read by the static pass that retains the
  # loops, so they are named here rather than inherited from whatever
  # environment happened to reach the JVM: a campaign whose declarations
  # silently failed to arrive would model an 8-body prefix and report nothing
  # about it. A configured file that does not exist is a die, not a fallback.
  if [[ -n "${causynth_loop_bounds}" ]]; then
    require_file "loop body bound declarations" "${causynth_loop_bounds}"
    system_properties+=(
      "-Dcausynth.loop.bounds=${causynth_loop_bounds}"
    )
  fi
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
  # Where the concolic pass states what it rewrote: unique methods and hook
  # sites, counted from the rewritten bodies. It is a static count and is
  # deliberately separate from any trace event count -- a trace sequence
  # number says how many times instrumented code ran, not how much code was
  # instrumented, and reading one as the other is what made a replay that
  # never left waitActive() look like a symbolic-execution cost.
  if [[ -n "${CAUSYNTH_CONCOLIC_ENVELOPE_REPORT:-}" ]]; then
    system_properties+=(
      "-Dcausynth.concolic.envelope.report=${CAUSYNTH_CONCOLIC_ENVELOPE_REPORT}"
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
  if [[ -n "${schedule_summaries}" ]]; then
    require_file "scheduler summaries" "${schedule_summaries}"
    args+=(--summaries "${schedule_summaries}")
  fi
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler \
    "${args[@]}" "$@"
}

do_import() {
  require_file "raw concolic results" "${raw_concolic_results}"
  require_file "import activation plan" "${import_task_plan}"
  require_file "runtime region plan" "${runtime_region_plan}"
  ensure_output_directory "$(dirname "${imported_summaries}")"
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter \
    --results "${raw_concolic_results}" \
    --task-plan "${import_task_plan}" \
    --runtime-plan "${runtime_region_plan}" \
    --output "${imported_summaries}" \
    --diagnostics "${import_diagnostics}" \
    ${import_topology_delta:+--topology-delta "${import_topology_delta}"} \
    ${import_iteration_id:+--iteration-id "${import_iteration_id}"} "$@"
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
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    "CAUSYNTH_INSTRUMENTED_CLASSES_DIR=${analysis_classes_dir}"
    "CAUSYNTH_TRACE_OUTPUT_DIR=${trace_dir}"
  )
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    workload_env+=("CAUSYNTH_PROTOCOL_STUBS=${causynth_protocol_stubs}")
  fi
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
# pairs an RPC, builds a container expression, or emits an SMT term -- and it
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

# A stage artifact this run may legitimately not have. Printing null says the
# artifact is absent in the shape its reader already handles, and it never lets
# a leftover from an earlier command stand in for one this campaign never wrote.
campaign_optional_json() {
  [[ -n "$1" && -s "$1" ]] && jq -c . "$1" 2>/dev/null || echo null
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
  find "$1" -type f -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum \
    | sha256sum | awk '{print $1}'
}

# A checkout's exact state. The commit alone is not its identity: these
# checkouts carry uncommitted driver and tracing changes, so the porcelain
# listing and the content of every file it names are hashed with it.
campaign_checkout_state() {
  local repo=$1 entry
  if ! git -C "${repo}" rev-parse HEAD >/dev/null 2>&1; then
    jq -n --arg path "${repo}" \
      '{path: $path, head: "", branch: "", worktreeDigest: ""}'
    return 0
  fi
  jq -n --arg path "${repo}" \
    --arg head "$(git -C "${repo}" rev-parse HEAD)" \
    --arg branch "$(git -C "${repo}" rev-parse --abbrev-ref HEAD)" \
    --arg worktree "$( { git -C "${repo}" status --porcelain
        git -C "${repo}" status --porcelain | awk '{print $NF}' \
          | while IFS= read -r entry; do
              [[ -e "${repo}/${entry}" ]] || continue
              find "${repo}/${entry}" -type f -print0 | LC_ALL=C sort -z \
                | xargs -0 -r sha256sum
            done; } | sha256sum | awk '{print $1}')" \
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
    # the delta vocabulary, stamps the iteration they belong to, and sorts them
    # in the stable order README states. Completion order is never semantic.
    iteration, output = args[0], args[1]
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
            row.setdefault("iterationId", iteration)
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

# The scheduler index is the only campaign membership authority. It is decoded
# on demand and never copied into a second identity table that could drift.
campaign_index_members() {
  require_nonempty "runtime workflow schedule index" "$1"
  jq -r '
    ((.target + {role: "TARGET"}), (.producers[] + {role: "PRODUCER"}))
    | [.role, .campaignId, .regionId, .occurrenceId, .goalId, .taskId]
    | @tsv' "$1"
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
    "$@"
  )
  if [[ -n "${causynth_protocol_stubs}" ]]; then
    adapter_env+=("CAUSYNTH_PROTOCOL_STUBS=${causynth_protocol_stubs}")
  fi
  campaign_log "${label} adapter: ${command}"
  (cd "${workload_work_dir}" && env "${adapter_env[@]}" bash -lc "${command}")
}

campaign_setup() {
  campaign_run_adapter setup "${campaign_setup_command}"
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
  [[ -x "${vm}" ]] || die "the concolic VM is not built: ${vm}"
  require_file "concolic rt.jar" "${rt_jar}"
  require_file "concolic libjava" "${libjava}"
  require_file "concolic libjvm" "${libjvm}"
  campaign_provenance=$(jq -n \
    --arg jar "${graphchecker_jar}" \
    --arg jarSha "$(campaign_digest "${graphchecker_jar}")" \
    --arg vm "${vm}" --arg vmSha "$(campaign_digest "${vm}")" \
    --arg rtJar "${rt_jar}" \
    --arg rtJarSha "$(campaign_digest "${rt_jar}")" \
    --arg libjava "${libjava}" \
    --arg libjavaSha "$(campaign_digest "${libjava}")" \
    --arg libjvm "${libjvm}" \
    --arg libjvmSha "$(campaign_digest "${libjvm}")" \
    --arg config "${config_file}" \
    --arg configSha "$(campaign_digest "${config_file}")" \
    --arg spec "${causynth_target_spec}" \
    --arg specSha "$(campaign_optional_digest "${causynth_target_spec}")" \
    --arg stubs "${causynth_protocol_stubs}" \
    --arg stubsSha "$(campaign_optional_digest "${causynth_protocol_stubs}")" \
    --arg bounds "${causynth_loop_bounds}" \
    --arg boundsSha "$(campaign_optional_digest "${causynth_loop_bounds}")" \
    --arg symbolicInputs "${causynth_symbolic_inputs}" \
    --arg symbolicInputsSha "$(campaign_optional_digest \
      "${causynth_symbolic_inputs}")" \
    --arg classes "${project_classes_dir}" \
    --arg classesSha "$(campaign_tree_digest "${project_classes_dir}")" \
    --arg testClass "${trace_test}" \
    --arg testClasses "${project_test_classes_dir}" \
    --arg testClassesSha "$(campaign_tree_digest \
      "${project_test_classes_dir}")" \
    --arg classpath "${project_classpath}" \
    --arg classpathSha "$(printf '%s' "${project_classpath}" | sha256sum \
      | awk '{print $1}')" \
    --argjson toolSource "$(campaign_checkout_state "${graphchecker_dir}")" \
    --argjson workloadSource "$(campaign_checkout_state "${project_repo}")" \
    '{jar: {path: $jar, sha256: $jarSha},
      vm: {path: $vm, sha256: $vmSha,
           rtJar: {path: $rtJar, sha256: $rtJarSha},
           libjava: {path: $libjava, sha256: $libjavaSha},
           libjvm: {path: $libjvm, sha256: $libjvmSha}},
      config: {path: $config, sha256: $configSha},
      targetSpec: {path: $spec, sha256: $specSha},
      protocolStubs: {path: $stubs, sha256: $stubsSha},
      loopBounds: {path: $bounds, sha256: $boundsSha},
      symbolicInputs: {path: $symbolicInputs,
                       sha256: $symbolicInputsSha},
      productionClasses: {path: $classes, sha256: $classesSha},
      workload: {testClass: $testClass,
                 testClasses: {path: $testClasses, sha256: $testClassesSha},
                 classpath: $classpath, classpathSha256: $classpathSha},
      source: {graphchecker: $toolSource, workload: $workloadSource}}')
}

# The stock-JVM seed: the static pass, then the two traced passes the workload
# stage owns. Its outputs are the campaign's static catalog and target closure.
campaign_seed() {
  local marker="${campaign_root}/.seed-started"
  : >"${marker}"
  do_analyze
  require_fresh "static candidate data-flow graph" "${candidate_graph}" \
    "${marker}"
  do_workload
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
  campaign_provenance=$(jq -n --argjson frozen "${campaign_provenance}" \
    --arg catalog "${candidate_graph}" \
    --arg catalogSha "$(campaign_digest "${candidate_graph}")" \
    --arg plan "${runtime_region_plan}" \
    --arg planSha "$(campaign_digest "${runtime_region_plan}")" \
    --arg refined "${refined_graph}" \
    --arg refinedSha "$(campaign_digest "${refined_graph}")" \
    '$frozen + {staticCatalog: {path: $catalog, sha256: $catalogSha},
                regionPlan: {path: $plan, sha256: $planSha},
                refinedGraph: {path: $refined, sha256: $refinedSha}}')
}

# Schedule pass one: the immutable target-first plan for this iteration, its
# digest-committed index, and one singleton subplan per indexed member.
campaign_plan() {
  local iteration_dir=$1 carry=$2
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local frozen="${iteration_dir}/concolic_region_plan.jsonl"
  local role campaign_id region occurrence goal task worker
  local plan_hash plan_size region_hash region_size

  require_nonempty "runtime region plan" "${runtime_region_plan}"
  require_nonempty "runtime-refined data-flow graph" "${refined_graph}"
  cp -f "${runtime_region_plan}" "${frozen}"
  schedule_output_dir="${iteration_dir}"
  schedule_summaries="${carry}"
  do_schedule --target-first
  # Every later consumer reads this iteration's frozen copy, never the mutable
  # discovery output.
  runtime_region_plan="${frozen}"
  require_nonempty "campaign task plan" "${plan}"
  require_nonempty "runtime workflow schedule index" "${index}"

  plan_hash=$(campaign_digest "${plan}")
  plan_size=$(stat -c '%s' "${plan}")
  region_hash=$(campaign_digest "${frozen}")
  region_size=$(stat -c '%s' "${frozen}")
  # Immutable paths, digests and task-set membership -- the whole of what the
  # shell owns here. The index must commit exactly the plan bytes this
  # iteration froze, and its members must be exactly that plan's tasks. What a
  # task selects, and by which authority, is the scheduler's own invariant.
  jq -e --arg plan_hash "${plan_hash}" --arg region_hash "${region_hash}" \
    --argjson plan_size "${plan_size}" --argjson region_size "${region_size}" \
    --slurpfile tasks "${plan}" '
      ([.target.taskId] + [.producers[].taskId]
        | map(select(. != null))) as $selected
      | .executionTaskPlan.sha256 == $plan_hash
        and .executionTaskPlan.sizeBytes == $plan_size
        and .regionPlan.sha256 == $region_hash
        and .regionPlan.sizeBytes == $region_size
        and (.target | type == "object")
        and (.producers | type == "array")
        and ($selected | length) > 0
        and ($selected | unique | sort) == ([$tasks[].taskId] | unique | sort)
        and ([$tasks[].taskId] | unique | length) == ($tasks | length)
    ' "${index}" >/dev/null \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the target-first schedule index does not commit the canonical task plan"

  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    worker="${iteration_dir}/workers/${task}"
    mkdir -p "${worker}"
    jq -c --arg task "${task}" 'select(.taskId == $task)' "${plan}" \
      >"${worker}/execution_task_plan.jsonl"
    jq -e -s --arg task "${task}" '
        length == 1 and .[0].taskId == $task
      ' "${worker}/execution_task_plan.jsonl" >/dev/null \
      || campaign_fail PLAN ConcolicScheduler "${plan}" \
        "indexed campaign task ${task} is absent from the canonical task plan"
    campaign_log "member ${role} task=${task} occurrence=${occurrence}"
  done < <(campaign_index_members "${index}")
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
  local ids published selected
  ids=$(campaign_task_ids "${plan}")
  campaign_replay session "${plan}" "${ids}" \
    "${iteration_dir}/instrumented-classes" "${results}" "${seed}"
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
  local iteration_dir=$1
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
  do_import
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
  done < <(campaign_index_members \
    "${iteration_dir}/runtime_workflow_schedule_index.json")
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
  do_schedule --target-first
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
  local query_key=$1 worklist=$2 tasks=$3 session_source_plan=$4
  local member_task=$5 classes=$6 worker=$7
  local outcome replay_task reason status=0
  local raw="${worker}/concolic_region_results.jsonl"
  local member_raw="${worker}/member_concolic_region_results.jsonl"
  local session_plan="${worker}/session_execution_task_plan.jsonl"
  local session_raw="${worker}/session_concolic_region_results.jsonl"
  local import_plan="${worker}/import_execution_task_plan.jsonl"
  local imported="${worker}/concolic_region_summaries.jsonl"
  local member_imported="${worker}/member_concolic_region_summaries.jsonl"
  local member_diagnostics="${worker}/member_import_diagnostics.jsonl"
  local member_delta="${worker}/member_topology_delta.jsonl"
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

  # A distributed path flip changes one selected member, not the causal
  # closure that supplies its live RPC/state inputs. Replay the canonical
  # selected session with exactly that member replaced by the derived task;
  # a singleton worker plan cannot carry a producer's VM handoff into its
  # consumer. After the replay member itself is admitted below, retain every
  # consumer row whose VM handoff names that exact replay task. Those rows are
  # the runtime certificate that the alternate producer case actually crossed
  # the RPC cut; keeping only the member would make its alternate output cases
  # impossible to select during final composition.
  jq -c --arg member "${member_task}" \
    --slurpfile replay "${worker}/execution_task_plan.jsonl" '
      if .taskId == $member then $replay[0] else . end
    ' "${session_source_plan}" >"${session_plan}"
  jq -e -s --arg member "${member_task}" --arg replay "${replay_task}" \
    --argjson expected "$(jq -s 'length' "${session_source_plan}")" '
      length == $expected
      and ([.[].taskId] | unique | length) == length
      and (map(select(.taskId == $member)) | length) == 0
      and (map(select(.taskId == $replay)) | length) == 1
    ' "${session_plan}" >/dev/null \
    || die "the path worker did not replace exactly one canonical member: ${member_task}"
  campaign_replay worker "${session_plan}" \
    "$(campaign_task_ids "${session_plan}")" "${classes}" \
    "${session_raw}" "${worker}"
  jq -c --arg task "${replay_task}" 'select(.taskId == $task)' \
    "${session_raw}" >"${member_raw}"
  require_nonempty "path worker member result" "${member_raw}"

  # First admit the replay member in isolation. A producer can export before
  # its occurrence is later rejected by replay-prefix/anchor validation. A
  # consumer may already have attached that transient handle, so importing the
  # whole session in one pass could publish a consumer case whose producer case
  # was refused. The small first pass is the commit gate for all companions.
  raw_concolic_results="${member_raw}"
  import_task_plan="${worker}/execution_task_plan.jsonl"
  imported_summaries="${member_imported}"
  import_diagnostics="${member_diagnostics}"
  import_topology_delta="${member_delta}"
  set +e
  do_import
  status=$?
  set -e
  if [[ "${status}" -ne 0 && ! -s "${import_diagnostics}" ]]; then
    die "the importer failed without a semantic diagnostic for ${query_key} (exit ${status})"
  fi
  # Whether a replayed obligation yielded an admissible case is the importer's
  # decision, and it publishes that decision whichever way it goes. So the
  # test here is "did the semantic owner get to speak", not "is the summary
  # non-empty": an importer that ran and admitted nothing has answered, and
  # its diagnostics say why. Treating that answer as a missing file killed the
  # worker, failed the whole obligation wave, and discarded the producer
  # relation the wave was exploring - throwing away a flip the solver had
  # already solved because the next stage had no way to say "the replay
  # yielded nothing". Only an importer that published no artifact at all has
  # not spoken, and that is the infrastructure failure, named as itself.
  if [[ ! -s "${member_imported}" ]]; then
    [[ -f "${import_diagnostics}" ]] || die \
      "the importer published no diagnostics for ${query_key}; expected ${import_diagnostics}"
    cp "${member_raw}" "${raw}"
    cp "${member_diagnostics}" "${worker}/import_diagnostics.jsonl"
    cp "${member_delta}" "${worker}/topology_delta.jsonl"
    : >"${imported}"
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

  # The replay member is durable. Import it together with exactly those live
  # consumers that attest a schema-v3 handoff from this replay task. Matching
  # by taskId is safe here because the handle header obtained that id from the
  # active producer occurrence; port/value identity remains VM-owned.
  jq -c --arg task "${replay_task}" '
    select(.taskId == $task
      or any(.vmHandoffEvents[]?;
        .producerTaskId == $task))
  ' "${session_raw}" >"${raw}"
  require_nonempty "path worker result and handoff companions" "${raw}"
  jq -c --slurpfile rows "${raw}" '
    ([ $rows[].taskId ] | unique) as $selected
    | select(.taskId as $id | $selected | index($id))
  ' "${session_plan}" >"${import_plan}"
  jq -e -s --slurpfile rows "${raw}" '
    ([ $rows[].taskId ] | unique | sort) as $observed
    | ([ .[].taskId ] | unique | sort) == $observed
  ' "${import_plan}" >/dev/null \
    || die "the companion import plan does not exactly cover its result rows"

  raw_concolic_results="${raw}"
  import_task_plan="${import_plan}"
  imported_summaries="${imported}"
  import_diagnostics="${worker}/import_diagnostics.jsonl"
  import_topology_delta="${worker}/topology_delta.jsonl"
  set +e
  do_import
  status=$?
  set -e
  if [[ "${status}" -ne 0 && ! -s "${import_diagnostics}" ]]; then
    die "the companion importer failed without a semantic diagnostic for ${query_key} (exit ${status})"
  fi
  jq -e -s --arg task "${replay_task}" '
    map(select(.taskId == $task)) | length == 1
  ' "${imported}" >/dev/null \
    || die "the committed replay member disappeared during companion import: ${replay_task}"
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
  local worker
  local -a summary_inputs task_inputs record_inputs
  summary_inputs=("${summaries}")
  task_inputs=("${tasks}")
  record_inputs=("${records}")
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
  done < <(find "${planner_dir}" -mindepth 1 -maxdepth 1 -type d \
    | LC_ALL=C sort)
  campaign_json combine summaryId "${summaries}" "${summary_inputs[@]}"
  campaign_json combine taskId "${tasks}" "${task_inputs[@]}"
  campaign_json combine queryKey "${records}" "${record_inputs[@]}"
}

# The inner loop for one member: while target-relevant obligations remain in
# this topology, derive immutable subplans from the canonical plan, run them in
# parallel fresh workload instances, import strictly, and merge.
campaign_explore_member() {
  local iteration_dir=$1 role=$2 region=$3 occurrence=$4 goal=$5 task=$6
  local member="${iteration_dir}/workers/${task}"
  local classes="${iteration_dir}/instrumented-classes"
  local summaries="${member}/observed_path_summaries.jsonl"
  local tasks="${member}/observed_execution_tasks.jsonl"
  local records="${member}/path_exploration_records.jsonl"
  local planner_dir worker_dir wave=0 status=0 key pid
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
    # A planner that crashed is an infrastructure failure and stays fatal. A
    # worklist it declared unexecutable is a semantic outcome: it is named as
    # this member's terminal gap and the classifier and Composer decide what it
    # costs, because the shell cannot tell a blocked selected obligation from a
    # blocked unselected one.
    if [[ "${status}" -eq 2 ]]; then
      campaign_report_worklist "${planner_dir}"
      campaign_record_gap "${iteration_dir}" WORKLIST_NOT_EXECUTABLE "${task}" \
        "the ${role} path worklist is not executable"
      break
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
      campaign_record_gap "${iteration_dir}" WORKLIST_STATE_UNRESOLVED \
        "${task}" "the ${role} path planner published no pending or closed state"
      break
    fi
    mapfile -t keys < <(jq -r -s \
      --argjson limit "${concolic_worker_count}" '
        sort_by(.queryKey) | .[0:$limit][] | .queryKey
      ' "${planner_dir}/region_path_worklist.jsonl")
    if [[ ${#keys[@]} -eq 0 ]]; then
      campaign_record_gap "${iteration_dir}" WORKLIST_WITHOUT_OBLIGATION \
        "${task}" "a pending ${role} worklist named no deterministic obligation"
      break
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
          "${iteration_dir}/execution_task_plan.jsonl" "${task}" \
          "${classes}" "${worker_dir}"
      ) >"${worker_dir}/stdout.log" 2>"${worker_dir}/stderr.log" &
      pids+=("$!")
    done
    status=0
    for pid in "${pids[@]}"; do
      wait "${pid}" || status=1
    done
    if [[ "${status}" -ne 0 ]]; then
      # An obligation that did not finish is one unexplored case, not a reason
      # to end the campaign before anything can classify it.
      campaign_report_wave "${planner_dir}"
      campaign_record_gap "${iteration_dir}" OBLIGATION_WAVE_INCOMPLETE \
        "${task}" "the ${role} obligation wave ${wave} did not finish"
      break
    fi
    campaign_publish_wave "${planner_dir}" "${summaries}" "${tasks}" \
      "${records}"
    wave=$((wave + 1))
  done
  # A wave that ends without closing has not improved the relation; it has
  # not invalidated it either.  The planner already merged the seed-only
  # relation, so carry that rather than discarding a complete relation because
  # exploration added nothing: best-effort merging produces what it has and
  # names what it lost, and pathCoverageState=SEED_ONLY is what the acceptance
  # gate reads to refuse a partial path set.
  if [[ ! -s "${member}/merged_summary.jsonl" \
        && -s "${planner_dir}/merged_region_summaries.jsonl" ]]; then
    cp -f "${planner_dir}/merged_region_summaries.jsonl" \
      "${member}/merged_summary.jsonl"
    campaign_record_gap "${iteration_dir}" MERGED_RELATION_SEED_ONLY "${task}" \
      "the ${role} member merged its seed relation without a closed worklist"
  fi
  [[ -s "${member}/merged_summary.jsonl" || "${role}" == "TARGET" ]] \
    || campaign_record_gap "${iteration_dir}" MERGED_RELATION_ABSENT "${task}" \
      "the ${role} member left no merged relation behind"
  campaign_log "${role} exploration stopped after ${wave} wave(s)"
}

# The builder owns what a closed reach query is, and refuses a seed that is
# not exactly one solver-ready target query. Its refusal is the finding: the
# shell records it and lets the Composer decide whether the selected closure
# can still be composed without it.
campaign_target_reach_query() {
  local iteration_dir=$1 task=$2
  local member="${iteration_dir}/workers/${task}"
  local resolved="${causynth_output_dir}/target_resolved.json"
  local exception="" status=0
  [[ ! -s "${resolved}" ]] \
    || exception=$(jq -r '.exception // ""' "${resolved}")
  if [[ -z "${exception}" ]]; then
    campaign_record_gap "${iteration_dir}" TARGET_ATTESTATION_ABSENT "${task}" \
      "no target attestation names the selected exception: ${resolved}"
    return 0
  fi
  set +e
  run_java_main \
    edu.uva.liftlab.graphchecker.concolic.TargetReachPathQueryBuilder \
    --summaries "${member}/observed_path_summaries.jsonl" \
    --path-manifest "${member}/path_closure.json" \
    --seed-query "${iteration_dir}/seed-query/branch_queries.jsonl" \
    --exception-type "${exception}" \
    --output "${member}/reach_query.jsonl" >/dev/null
  status=$?
  set -e
  if [[ "${status}" -ne 0 || ! -s "${member}/reach_query.jsonl" ]]; then
    campaign_record_gap "${iteration_dir}" TARGET_REACH_QUERY_REFUSED \
      "${task}" \
      "TargetReachPathQueryBuilder published no closed reach query (exit ${status})"
    return 0
  fi
  campaign_log "target reach paths: $(jq -r '.paths | length' \
    "${member}/reach_query.jsonl")"
}

campaign_explore() {
  local iteration_dir=$1
  local role campaign_id region occurrence goal task target_task=""
  local target_summaries=""
  local -a target_summary_inputs=()
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    if [[ ! -s "${iteration_dir}/workers/${task}/concolic_region_summaries.jsonl" ]]; then
      campaign_record_gap "${iteration_dir}" MEMBER_NOT_EXPLORED "${task}" \
        "this member has no imported summary to explore from"
      continue
    fi
    campaign_explore_member "${iteration_dir}" "${role}" "${region}" \
      "${occurrence}" "${goal}" "${task}"
    if [[ "${role}" == "TARGET" ]]; then
      target_task=${task}
    fi
  done < <(campaign_index_members \
    "${iteration_dir}/runtime_workflow_schedule_index.json")

  # A producer replay can carry its expression through RPC and make the
  # already-selected target occurrence take the required outcome.  Those
  # target companion rows are imported only after the producer member itself
  # is admitted, and therefore do not exist when the target member is explored
  # first.  Build the reach query after every member has finished, merging the
  # accepted companion summaries into the target's observed path set.  The
  # query builder filters by the exact target region/goal/occurrence; producer
  # rows in these files cannot become target paths.
  if [[ -n "${target_task}" ]]; then
    target_summaries="${iteration_dir}/workers/${target_task}/observed_path_summaries.jsonl"
    target_summary_inputs=("${target_summaries}")
    while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
      [[ "${role}" == "TARGET" ]] && continue
      [[ -s "${iteration_dir}/workers/${task}/observed_path_summaries.jsonl" ]] \
        || continue
      target_summary_inputs+=(
        "${iteration_dir}/workers/${task}/observed_path_summaries.jsonl")
    done < <(campaign_index_members \
      "${iteration_dir}/runtime_workflow_schedule_index.json")
    campaign_json combine summaryId "${target_summaries}" \
      "${target_summary_inputs[@]}"
    campaign_target_reach_query "${iteration_dir}" "${target_task}"
  fi
}

# Classification is the importer's; this collects the rows it wrote, sorts them
# deterministically, and publishes them as this iteration's delta. An iteration
# whose importer declared nothing has an empty delta, which is a topology that
# did not change, not evidence that nothing happened.
campaign_classify() {
  local iteration_dir=$1 iteration=$2
  local diagnostics="${iteration_dir}/import_diagnostics.jsonl"
  local published="${iteration_dir}/topology_delta.jsonl"
  local counts
  local -a sources=()
  local -a deltas=()
  mapfile -t sources < <(find "${iteration_dir}" -type f \
    -name 'import_diagnostics.jsonl' -not -path "${diagnostics}" \
    | LC_ALL=C sort)
  : >"${diagnostics}"
  [[ ${#sources[@]} -eq 0 ]] || cat "${sources[@]}" >>"${diagnostics}"
  # The delta rows are the importer's, read from the artifacts it wrote.  The
  # diagnostics are collected too, because a refusal names its own gap there.
  mapfile -t deltas < <(find "${iteration_dir}" -type f \
    -name 'topology_delta.jsonl' -not -path "${published}" \
    | LC_ALL=C sort)
  counts=$(campaign_json delta "${iteration}" "${published}" \
    "${deltas[@]}" "${diagnostics}")
  campaign_delta_rows=${counts%% *}
  campaign_delta_divergences=${counts##* }
  campaign_log "topology delta rows=${campaign_delta_rows} divergences=${campaign_delta_divergences}"
}

campaign_publish_iteration_manifest() {
  local iteration_dir=$1 iteration=$2 parent=$3
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local members="${iteration_dir}/.members.jsonl"
  local role campaign_id region occurrence goal task worker
  : >"${members}"
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    worker="${iteration_dir}/workers/${task}"
    jq -n --arg role "${role}" --arg campaign "${campaign_id}" \
      --arg region "${region}" --arg occurrence "${occurrence}" \
      --arg goal "${goal}" --arg task "${task}" --arg dir "${worker}" \
      --argjson obligations "$(find "${worker}" -mindepth 2 -maxdepth 2 \
        -type d -path '*/obligations-*/*' -printf '%f\n' 2>/dev/null \
        | LC_ALL=C sort | jq -R -s 'split("\n") | map(select(length > 0))')" \
      '{role: $role, campaignId: $campaign, regionId: $region,
        occurrenceId: $occurrence, goalId: $goal, taskId: $task,
        workerDir: $dir, obligationDigests: $obligations}' \
      >>"${members}"
  done < <(campaign_index_members "${index}")
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg iteration "$(printf 'iteration-%04d' "${iteration}")" \
    --arg parent "${parent}" \
    --arg plan "${iteration_dir}/execution_task_plan.jsonl" \
    --arg planSha "$(campaign_digest \
      "${iteration_dir}/execution_task_plan.jsonl")" \
    --arg index "${index}" --arg indexSha "$(campaign_digest "${index}")" \
    --arg summaries "${iteration_dir}/concolic_region_summaries.jsonl" \
    --arg summariesSha "$(campaign_digest \
      "${iteration_dir}/concolic_region_summaries.jsonl")" \
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

# The composition consumes the target's reach query and the members' merged
# relations. A task that failed closed leaves one of them behind, and the layer
# that owns why already named it -- the shell does not adjudicate that a second
# time. Both inputs are handed over as named, missing or not, and the Composer
# publishes the composition it could make together with the refusal that says
# what it could not.
#
# The infrastructure failures stay failures and are named as themselves: a
# frozen index with no target member is a broken plan, and a Composer that threw
# is a Composer failure. Neither is a task that failed closed.
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
    # A member that left no merged relation was already named as this
    # iteration's gap where it happened; it is not composed and it is not a
    # second refusal here.
    [[ -s "${iteration_dir}/workers/${task}/merged_summary.jsonl" ]] || continue
    merged+=("${iteration_dir}/workers/${task}/merged_summary.jsonl")
  done < <(campaign_index_members \
    "${iteration_dir}/runtime_workflow_schedule_index.json")
  [[ -n "${target_task}" ]] || campaign_fail COMPOSE ConcolicScheduler \
    "${iteration_dir}/runtime_workflow_schedule_index.json" \
    "the frozen schedule index names no target member"
  [[ ! -e "${campaign_final}" ]] || die \
    "the final directory already exists: ${campaign_final}"
  mkdir -p "${campaign_final}"
  # A member set that left no merged relation is still composed, and so is a
  # target that published no reach query: both are closures the Composer
  # refuses by name, not missing inputs the shell decides on.
  fatal_queries="${iteration_dir}/workers/${target_task}/reach_query.jsonl"
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
}

# The causal projection is a diagnostic drawing of a composition the Composer
# already accepted or refused. It never gates the SMT: a projection that could
# not be drawn says something about the projection.
campaign_graph() {
  local status=0
  mkdir -p "${campaign_final}/graph"
  set +e
  run_java_main edu.uva.liftlab.graphchecker.concolic.CausalGraphWriter \
    "${composition_manifest}" "${campaign_final}/graph" "${reach_report}"
  status=$?
  set -e
  [[ "${status}" -eq 0 ]] \
    || campaign_log "the causal projection was not drawn (exit ${status}); it is diagnostic"
}

campaign_artifact_digests() {
  local name path
  local -a rows=()
  for name in candidate.smt2 candidate_composition_manifest.json \
      z3-result.json gaps.json graph/causal_model.json; do
    path="${campaign_final}/${name}"
    [[ -f "${path}" ]] || continue
    rows+=("$(jq -n --arg name "${name}" --arg path "${path}" \
      --argjson bytes "$(wc -c <"${path}")" \
      --arg sha256 "$(campaign_digest "${path}")" \
      '{name: $name, path: $path, bytes: $bytes, sha256: $sha256}')")
  done
  printf '%s\n' "${rows[@]}" | jq -c -s .
}

# The named outputs. Nothing here recomputes a verdict: every field is copied
# from the stage that decided it, and the claim is read off those states.
campaign_emit() {
  local iteration_dir=$1
  local replay_rows replay_bytes gapCount
  local -a raw_results=()
  mapfile -t raw_results < <(find "${iteration_dir}" -type f \
    -name 'concolic_region_results.jsonl' | LC_ALL=C sort)
  [[ ${#raw_results[@]} -gt 0 ]] || die \
    "the iteration published no raw replay result: ${iteration_dir}"

  # Only the owners speak here: the Composer's selected blockers and model
  # gaps, the solver's, the importer's, and the classifier's delta rows.
  # Unselected VM and catalog telemetry is diagnostic and lives in the raw
  # results; the causal projection is diagnostic and is not a gap source.
  jq -n \
    --slurpfile composed <(campaign_optional_json "${composition_manifest}") \
    --slurpfile reach <(campaign_optional_json "${reach_report}") \
    --slurpfile diagnostics <(jq -c -s . \
      "${iteration_dir}/import_diagnostics.jsonl" 2>/dev/null || echo '[]') \
    --slurpfile delta <(jq -c -s . \
      "${iteration_dir}/topology_delta.jsonl" 2>/dev/null || echo '[]') '
    {schemaVersion: 1,
     kind: "CAMPAIGN_COVERAGE_GAPS",
     gaps: (
       [$composed[0].finalStatusRefusals[]?
         | {stage: "COMPOSE", source: "COMPOSER",
            code: .code, subject: .subject, detail: .detail}]
       + [$composed[0].canonicalModel.gaps[]?
           | {stage: "MODEL", source: (.source // "COMPOSER"),
              code: (.code // ""), subject: (.subject // ""),
              detail: (.detail // "")}]
       + [$reach[0].gaps[]?
           | {stage: "SOLVE", source: "SOLVER", code: ., subject: "",
              detail: ""}]
       + [$diagnostics[0][]?
           | {stage: "IMPORT", source: "IMPORTER", code: (.code // ""),
              subject: (.taskId // ""), detail: (.detail // "")}]
       + [$delta[0][]? | select(.deltaKind == "COVERAGE_GAP"
             or .deltaKind == "TOPOLOGY_DIVERGENCE")
           | {stage: "CLASSIFY", source: (.source // "IMPORTER"),
              code: (.code // .deltaKind), subject: (.taskId // ""),
              detail: (.reason // .gap // "")}])}
    | .gapCount = (.gaps | length)
    | .byStage = (.gaps | group_by(.stage)
        | map({key: .[0].stage, value: length}) | from_entries)
  ' >"${campaign_final}/gaps.json"
  require_nonempty "campaign gaps" "${campaign_final}/gaps.json"

  # The claim is copied, never reconstructed. The Composer publishes the sole
  # FINAL_READY decision and its selected blockers; the solver publishes the
  # reachability it parsed. Reachability on its own is not a candidate; the
  # Composer's own members are not re-scored here into a second verdict, and
  # nothing rebuilds a retired trust state to stand in for the decision. The
  # Importer/classifier coverage rows remain telemetry for the next
  # best-effort replay; they do not re-score the Composer's selected chain.
  jq -n \
    --slurpfile composed <(campaign_optional_json "${composition_manifest}") \
    --slurpfile reach <(campaign_optional_json "${reach_report}") \
    --slurpfile gaps "${campaign_final}/gaps.json" '
    $composed[0] as $c | $reach[0] as $r |
    ($r.reachCondition.reachability // "UNKNOWN") as $reachability |
    ($gaps[0].gapCount) as $gapCount |
    (($c.finalStatusRefusals // []) | length) as $blockers |
    ($c.finalStatus == "FINAL_READY") as $accepted |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     claim: (
       if $accepted and $reachability == "REACHABLE" then "SAT_CANDIDATE"
       elif $accepted and $reachability == "UNREACHABLE" then "UNSAT_CLOSED"
       else "INCONCLUSIVE_PARTIAL" end),
     claimReason: (
       if ($c.finalStatus != "FINAL_READY") then
         ("the Composer published finalStatus=" + ($c.finalStatus // "none")
           + " with " + ($blockers | tostring) + " selected blocker(s): "
           + (([$c.finalStatusRefusals[]? | .code] | unique | join(","))))
       elif $reachability == "REACHABLE" then
         "a valuation satisfies the target predicate inside the recorded model"
       elif $reachability == "UNREACHABLE" then
         "no valuation satisfies the target predicate and the selected model is closed"
       else "the solver stage reached no exact reachability decision" end),
     reachability: $reachability,
     solverState: ($r.state // ""),
     finalStatus: ($c.finalStatus // ""),
     finalStatusRefusals: $blockers,
     evidence: {
       exactBindings: ($c.canonicalModel.counts.exactBindings // 0),
       guardedBindings: ($c.canonicalModel.counts.guardedBindings // 0),
       unknownArmBindings: ($c.canonicalModel.counts.unknownArmBindings // 0),
       candidateBindings: ($c.canonicalModel.counts.candidateBindings // 0),
       fieldVersions: ($c.canonicalModel.counts.fieldVersions // 0),
       fieldReads: ($c.canonicalModel.counts.fieldReads // 0)},
     gapCount: $gapCount,
     valuations: ($r.valuations // [])}
  ' >"${campaign_final}/result.json"
  require_nonempty "campaign result" "${campaign_final}/result.json"

  replay_rows=$(wc -l "${raw_results[@]}" | tail -n 1 | awk '{print $1}')
  replay_bytes=$(stat -c '%s' "${raw_results[@]}" | awk '{n += $1} END {print n + 0}')
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg root "${campaign_root}" \
    --arg final "${campaign_final}" \
    --argjson artifacts "$(campaign_artifact_digests)" \
    --argjson replayRows "${replay_rows}" \
    --argjson replayBytes "${replay_bytes}" \
    --argjson stages "$(jq -R -s 'split("\n")
      | map(select(length > 0) | split("\t"))
      | map({stage: .[0], wallMillis: (.[1] | tonumber)})' \
      "${campaign_stage_metrics}")" \
    --slurpfile iterations <(find "${campaign_root}" -mindepth 2 -maxdepth 2 \
      -name 'iteration_manifest.json' | LC_ALL=C sort \
      | xargs -r jq -c '{iterationId, parentIterationId,
          externalWorkerCount, topologyDelta,
          taskIds: [.members[].taskId],
          obligations: [.members[] | {taskId,
            digests: .obligationDigests}]}' | jq -c -s .) '
    {schemaVersion: 1,
     kind: "CAMPAIGN_RUN_MANIFEST",
     campaignRoot: $root,
     outputDir: $final,
     provenance: $provenance,
     iterations: $iterations[0],
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
  jq -r '"  claim=\(.claim) reachability=\(.reachability) gaps=\(.gapCount) finalStatus=\(.finalStatus)"' \
    "${campaign_final}/result.json"
  [[ "${gapCount}" -eq 0 ]] \
    || campaign_log "the run named ${gapCount} gap(s); see ${campaign_final}/gaps.json"
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
  local iteration=0 parent="" carry="" iteration_dir
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  # Refused before any work rather than after the seed: a campaign root that
  # already holds an iteration belongs to another run, and its directories are
  # written once.
  [[ ! -e "${campaign_root}/iteration-0000" && ! -e "${campaign_final}" ]] \
    || die "this campaign root already holds a published run: ${campaign_root}"
  ensure_output_directory "${campaign_root}"
  : >"${campaign_stage_metrics}"

  campaign_stage VALIDATE campaign_validate
  if [[ -n "${campaign_setup_command}" ]]; then
    campaign_stage SETUP campaign_setup
  fi
  campaign_stage FREEZE campaign_freeze
  campaign_stage SEED campaign_seed

  while [[ "${iteration}" -lt "${campaign_max_iterations}" ]]; do
    iteration_dir=$(printf '%s/iteration-%04d' "${campaign_root}" \
      "${iteration}")
    [[ ! -e "${iteration_dir}" ]] || die \
      "iteration directory already exists; a campaign never rewrites one: ${iteration_dir}"
    mkdir -p "${iteration_dir}"
    campaign_stage "PLAN[${iteration}]" campaign_plan "${iteration_dir}" \
      "${carry}"
    campaign_stage "INSTRUMENT[${iteration}]" campaign_instrument \
      "${iteration_dir}"
    campaign_stage "REPLAY[${iteration}]" campaign_session_replay \
      "${iteration_dir}"
    campaign_stage "IMPORT[${iteration}]" campaign_import_session \
      "${iteration_dir}"
    campaign_stage "SEED_QUERY[${iteration}]" campaign_seed_query \
      "${iteration_dir}"
    campaign_stage "EXPLORE[${iteration}]" campaign_explore "${iteration_dir}"
    campaign_stage "CLASSIFY[${iteration}]" campaign_classify \
      "${iteration_dir}" "${iteration}"
    campaign_publish_iteration_manifest "${iteration_dir}" "${iteration}" \
      "${parent}"
    if [[ "${campaign_delta_divergences}" -gt 0 ]]; then
      # One iteration never adds tasks to its running campaign: a divergence
      # closes this iteration and rebuilds the target frontier in the next one.
      campaign_log "iteration ${iteration} diverged; rebuilding the target frontier"
      carry="${iteration_dir}/concolic_region_summaries.jsonl"
      parent=$(basename "${iteration_dir}")
      iteration=$((iteration + 1))
      continue
    fi
    campaign_stage COMPOSE campaign_compose "${iteration_dir}"
    campaign_stage SOLVE campaign_solve
    campaign_stage GRAPH campaign_graph
    campaign_stage EMIT campaign_emit "${iteration_dir}"
    return 0
  done
  campaign_publish_bound_gap "${campaign_max_iterations}"
}

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
  campaign|config|validate)
    [[ -n "${config_file}" ]] || die "${command_name} requires --config FILE"
    initialize_config "${config_file}"
    case "${command_name}" in
      campaign)
        [[ $# -eq 0 ]] || die "campaign takes no extra arguments"
        do_campaign
        ;;
      config) print_normalized_config ;;
      validate) validate_config ;;
    esac
    ;;
  *)
    die "unknown command '${command_name}' (run './run_engine.sh help')"
    ;;
esac
