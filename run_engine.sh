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

# CONFIG-1: one declaration per workflow key, in the order `config` prints
# them.  A row is `key  environment-override  flags  default`, where `-` is an
# absent field and the flags are the three things a key can be: `k` a known
# workflow key a config file may set, `r` reset at the start of every run, `p`
# printed by `config`.  Four lists used to state this separately, so a new key
# could be loadable but never reset, or overridable but never printed.
workflow_config_keys=(
  "campaign_setup_command CAUSYNTH_CAMPAIGN_SETUP_COMMAND krp -"
  "concolic_replay_command CAUSYNTH_CONCOLIC_REPLAY_COMMAND krp -"
  "concolic_worker_count CAUSYNTH_CONCOLIC_JOBS krp -"
  "campaign_max_iterations CAUSYNTH_CAMPAIGN_MAX_ITERATIONS krp -"
  "region_path_max_paths_per_region CAUSYNTH_REGION_PATH_MAX_PATHS_PER_REGION krp -"
  "region_path_max_flips_per_path CAUSYNTH_REGION_PATH_MAX_FLIPS_PER_PATH krp -"
  "region_path_max_tasks CAUSYNTH_REGION_PATH_MAX_TASKS krp -"
  "region_path_max_waves CAUSYNTH_REGION_PATH_MAX_WAVES krp 12"
  "config_file - p -"
  "workflow_path_base GRAPH_CHECKER_PATH_BASE krp -"
  "graphchecker_jar GRAPH_CHECKER_JAR krp -"
  "java_bin GRAPH_CHECKER_JAVA krp -"
  "graphchecker_work_dir GRAPH_CHECKER_WORK_DIR krp -"
  "project_repo CAUSYNTH_REPO krp -"
  "project_module_dir CAUSYNTH_MODULE_DIR krp -"
  "project_classes_dir CAUSYNTH_CLASSES_DIR krp -"
  "project_test_classes_dir CAUSYNTH_TEST_CLASSES_DIR krp -"
  "project_classpath CAUSYNTH_CLASSPATH krp -"
  "analysis_classes_dir CAUSYNTH_INSTRUMENTED_CLASSES_DIR krp -"
  "causynth_output_dir CAUSYNTH_OUTPUT_DIR krp -"
  "causynth_cache_dir CAUSYNTH_CACHE_DIR krp -"
  "causynth_target_spec CAUSYNTH_TARGET_SPEC krp -"
  "causynth_analysis_scope CAUSYNTH_ANALYSIS_SCOPE kr -"
  "causynth_process_dirs CAUSYNTH_PROCESS_DIRS krp -"
  "causynth_communication_mappings CAUSYNTH_COMMUNICATION_MAPPINGS krp -"
  "causynth_loop_bounds CAUSYNTH_LOOP_BOUNDS krp -"
  "causynth_symbolic_inputs CAUSYNTH_SYMBOLIC_INPUTS krp -"
  "custom_jdk_home CAUSYNTH_CUSTOM_JDK_HOME krp -"
  "z3_bin CAUSYNTH_Z3 krp -"
  "workload_work_dir CAUSYNTH_WORKLOAD_WORK_DIR krp -"
  "workload_command CAUSYNTH_WORKLOAD_COMMAND krp -"
  "trace_test CAUSYNTH_TRACE_TEST krp -"
  "candidate_graph CAUSYNTH_CANDIDATE_GRAPH krp -"
  "refined_graph CAUSYNTH_REFINED_GRAPH krp -"
  "runtime_region_plan CAUSYNTH_REGION_PLAN krp -"
  "schedule_output_dir CAUSYNTH_SCHEDULE_OUTPUT_DIR krp -"
  # Internal campaign state, derived from the immutable iteration: neither a
  # workflow key nor a CLI override point.
  "schedule_summaries - r -"
  "schedule_closure_mode - r candidate"
  "schedule_max_jobs CAUSYNTH_SCHEDULE_MAX_JOBS krp -"
  "solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS krp -"
  "reach_max_inputs CAUSYNTH_REACH_MAX_INPUTS krp -"
  "reach_max_valuations CAUSYNTH_REACH_MAX_VALUATIONS krp -"
  # How far a witness may move a wall clock from the value that read
  # returned.  Cross-node skew is a failure mechanism the checker explores,
  # so this bounds it rather than pinning a clock to its recording.
  "clock_skew_ms CAUSYNTH_CLOCK_SKEW_MS krp 300000"
)

# Reads one row of workflow_config_keys into config_key/config_env/
# config_flags/config_default, with `-` decoded as the empty string.
read_config_key_row() {
  read -r config_key config_env config_flags config_default <<<"$1"
  [[ "${config_env}" != "-" ]] || config_env=""
  [[ "${config_default}" != "-" ]] || config_default=""
}

known_config_key() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    if [[ "${config_key}" == "$1" && "${config_flags}" == *k* ]]; then
      return 0
    fi
  done
  return 1
}

reset_config() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    if [[ "${config_flags}" == *r* ]]; then
      printf -v "${config_key}" '%s' "${config_default}"
    fi
  done
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
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    if [[ -n "${config_env}" ]]; then
      apply_env_override "${config_key}" "${config_env}"
    fi
  done
}

# Runs one command whose non-zero exit is an outcome the caller reads rather
# than a failure, leaving that exit in the caller's `status`.  errexit is put
# back the way it was, so a caller that is itself inside such a block stays
# inside it.
run_capturing_status() {
  local errexit_was_set=0
  [[ $- == *e* ]] && errexit_was_set=1
  set +e
  "$@"
  status=$?
  [[ "${errexit_was_set}" -eq 0 ]] || set -e
}

canonical_path() {
  realpath -m -- "$1"
}

resolve_path() {
  local raw=$1
  local path_base=${2:-${workflow_path_base}}
  local candidate
  [[ -n "${raw}" ]] || return 0
  case "${raw}" in
    /*) candidate=${raw} ;;
    @config/*) candidate="${config_dir}/${raw#@config/}" ;;
    @project/*)
      candidate="${graphchecker_dir}/${raw#*/}"
      ;;
    @repo/*)
      [[ -n "${project_repo}" ]] || die "@repo path used before project_repo is resolved: ${raw}"
      candidate="${project_repo}/${raw#@repo/}"
      ;;
    *)
      case "${path_base}" in
        config) candidate="${config_dir}/${raw}" ;;
        project) candidate="${graphchecker_dir}/${raw}" ;;
        repo)
          [[ -n "${project_repo}" ]] || die "workflow_path_base=repo requires project_repo"
          candidate="${project_repo}/${raw}"
          ;;
        *) die "workflow_path_base must be config, project, or repo" ;;
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
  local requested=$1
  reset_config
  [[ -f "${requested}" ]] || die "config file not found: ${requested}"
  config_dir=$(cd "$(dirname "${requested}")" && pwd -P)
  config_file="${config_dir}/$(basename "${requested}")"
  load_config_file "${config_file}"
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
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    if [[ "${config_flags}" == *p* ]]; then
      printf '%s=%s\n' "${config_key}" "${!config_key}"
    fi
  done
}

# One workflow key whose value is a count: stated, numeric and above zero.
require_positive_integer() {
  local key=$1
  case "${!key}" in
    ''|*[!0-9]*) die "${key} must be a positive integer" ;;
    0) die "${key} must be greater than zero" ;;
  esac
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
  # The bounds a campaign may not inherit. Left unstated, each would reach its
  # stage as a bare flag and be read back as some default the artifacts never
  # name -- a truncated schedule, an unbounded solve -- so a run without them
  # does not start.
  local key
  for key in solver_timeout_ms schedule_max_jobs reach_max_inputs \
      reach_max_valuations concolic_worker_count campaign_max_iterations \
      region_path_max_waves; do
    require_positive_integer "${key}"
  done
  # A zero skew is meaningful -- it pins every clock to its recording -- so
  # this one is validated as non-negative rather than positive.
  [[ "${clock_skew_ms}" =~ ^[0-9]+$ ]] \
    || die "clock_skew_ms must be a non-negative integer: ${clock_skew_ms}"
  local bound
  for bound in "${region_path_max_paths_per_region}" \
      "${region_path_max_flips_per_path}" "${region_path_max_tasks}"; do
    [[ -z "${bound}" ]] && continue
    case "${bound}" in
      *[!0-9]*|0) die "region path bounds must be positive integers: ${bound}" ;;
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
      # The instrumentation pass bounds the campaign it is about to rewrite
      # by the same number the scheduler bounded it by.  Left unstated it
      # falls back to its own default, so a raised schedule_max_jobs planned
      # a campaign this stage then refused.
      "-Dcausynth.concolic.campaign.max.tasks=${schedule_max_jobs}"
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
    -o "${analysis_classes_dir}"
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
  # validate_config refuses an unstated cap: left to the scheduler's own
  # fallback of one job it would keep the first candidate of the plan and drop
  # the rest, and a schedule of one task is not an empty schedule, so the
  # stage would exit 0 with the truncation invisible.
  args+=(--max-jobs "${schedule_max_jobs}")
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
    args+=(--symbolic-inputs "${causynth_symbolic_inputs}")
  fi
  if [[ -n "${schedule_summaries}" ]]; then
    require_file "scheduler summaries" "${schedule_summaries}"
    args+=(--summaries "${schedule_summaries}")
  fi
  args+=(--closure-mode "${schedule_closure_mode}")
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler \
    "${args[@]}"
}

do_import() {
  local iteration_id=${1:-} key status=0
  [[ -n "${iteration_id//[[:space:]]/}" ]] \
    || die "import iteration id is required"
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
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter \
    --results "${raw_concolic_results}" \
    --task-plan "${import_task_plan}" \
    --runtime-plan "${runtime_region_plan}" \
    --output "${imported_summaries}" \
    --diagnostics "${import_diagnostics}" \
    --topology-delta "${import_topology_delta}" \
    --iteration-id "${iteration_id}"
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
    --clock-skew-ms "${clock_skew_ms}" \
    --mappings "${causynth_communication_mappings}" \
    "${selection[@]}"
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
    --workers "${concolic_worker_count}" \
    --max-inputs "${reach_max_inputs}" \
    --max-valuations "${reach_max_valuations}" \
    --mappings "${causynth_communication_mappings}"
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
# path it must read.
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

# The claim belongs to ClaimPolicy, so a reach report without one is a report
# this stage may not publish a result from: falling back to a shell verdict
# here is exactly the second gate this change removed.
campaign_require_claim() {
  local path=$1
  jq -e '(.campaignClaim | type) == "object"
    and ((.campaignClaim.claim // "")
      | IN("SAT_CANDIDATE", "UNSAT_CLOSED", "INCONCLUSIVE_PARTIAL"))
    and (.campaignClaim.blockers | type) == "array"
    and (.campaignClaim.claimReason | type) == "string"
    and (.campaignClaim.whyNotAccepted | type) == "string"' \
    "${path}" >/dev/null \
    || campaign_fail EMIT ClaimPolicy "${path}" \
      "the reach report published no ClaimPolicy decision"
}

# Prints every explicit symbolic root without exposing internal SMT terms.
# Configured source fields and planned manual symbolizations share this model
# contract; a missing propagation source is reported as a gap, never minted as
# another input here.
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
        (.inputKind == "CONFIGURED_SOURCE_FIELD"
         and ([.sourceKey, .sourceId, .sourcePhaseId, .fieldSignature]
              | all(type == "string" and length > 0))
         or .inputKind == "REGION_SYMBOLIC_INPUT"
         and ([.occurrenceId, .portId, .sourceIdentity,
               .sourceIdentityAuthority]
              | all(type == "string" and length > 0)))
        and has("value")))
  ' "${report}" >/dev/null || return 1
  model_count=$(jq -r '.symbolicVariableModels | length' "${report}")
  if [[ "${model_count}" -eq 0 ]]; then
    campaign_log "symbolic variables: no satisfying model"
    return 0
  fi
  while IFS=$'\t' read -r valuation kind source variable phase field value nullness; do
    campaign_log "symbolic valuation=${valuation} kind=${kind} source=${source} variable=${variable} phase=${phase} field=${field} value=${value}${nullness:+ nullness=${nullness}}"
  done < <(jq -r '
    .symbolicVariableModels[] as $model
    | $model.variables[]
    | [$model.valuationOrdinal, .inputKind,
       (.sourceKey // .occurrenceId), (.sourceId // .portId),
       (.sourcePhaseId // ""),
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

# FREEZE-1: the one place that knows how each kind of frozen input is
# digested.  FREEZE stamps the twelve inputs of a generation and GATE-1
# re-derives them hours later; a second spelling of "how a tree is hashed" is
# a second answer to "did this input change".
campaign_kind_digest() {
  case "$1" in
    file) campaign_digest "$2" ;;
    optional) campaign_optional_digest "$2" ;;
    tree) campaign_tree_digest "$2" ;;
    # A classpath is a string the stages were handed, not a file on disk.
    string) printf '%s' "$2" | sha256sum | awk '{print $1}' ;;
    *) return 2 ;;
  esac
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
  config_seed_sha=$(campaign_digest "${config_file}")
  identity=$(jq -S -c \
    --arg analysisScope "${causynth_analysis_scope}" \
    --arg processDirs "${causynth_process_dirs}" \
    --arg workloadWorkDir "${workload_work_dir}" \
    --arg workloadCommand "${workload_command}" \
    --arg traceTest "${trace_test}" \
    --arg configSeedSha "${config_seed_sha}" '
    {schemaVersion: 3, kind: "CAMPAIGN_SEED_CACHE_KEY",
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
       graphCheckerSource: .source.graphchecker,
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

# One JSONL helper for byte-preserving membership selection, deduplication and
# topology-delta ordering. It moves rows that production owners already wrote
# and never decides whether a row is admissible.
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


if mode == "select-summary":
    # Membership, not admission: whatever the importer wrote for this task.
    # Whether a task ended with a usable summary is the importer's finding and
    # travels as its own diagnostic/delta row, not as a shell verdict here.
    for row in rows(args[0]):
        if row.get("taskId") == args[1]:
            print(dump(row))

elif mode == "select-tasks":
    # Post-seed membership is computed by the scheduler from exact VM
    # propagation evidence.  Keep only rows owned by that active task plan;
    # this is a byte-preserving membership projection, not readmission.
    selected = {row.get("taskId") for row in rows(args[1])
                if isinstance(row.get("taskId"), str)
                and row.get("taskId")}
    if not selected:
        sys.exit("active task plan names no task")
    for row in rows(args[0]):
        if row.get("taskId") in selected:
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
# have been proved. The target and all causal predecessors are peers in one
# linked region-path bundle.
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
    # ConcolicScheduler owns the index schema, its constants and its task
    # identities. What is checked here is what this shell then does with the
    # rows: it emits them as TSV and it dispatches on the one TARGET.
    | if ((.members | type == "array" and length > 0)
        and all(.members[];
          member and ((.role == "TARGET") or (.role == "DEPENDENCY")))
        and ([.members[] | select(.role == "TARGET")] | length == 1))
    then
      .members[]
      | [.role, .campaignId, .regionId, .occurrenceId, .goalId, .taskId]
      | @tsv
    else error("invalid runtime region-path schedule index") end
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
            ((.role == "TARGET") or (.role == "DEPENDENCY"))
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
  local worklist=$1
  [[ -f "${worklist}" ]] || {
    echo "path-flip worklist is missing: ${worklist}" >&2
    return 1
  }
  jq -e -r -s '
    if all(.[]; type == "object"
        and (.queryKey | type == "string" and length > 0))
        and (([.[].queryKey] | length)
          == ([.[].queryKey] | unique | length))
    then sort_by(.queryKey)[] | .queryKey
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
# Stamps one frozen input into the named variable, failing the campaign when
# its digest cannot be taken.  The fourth argument names the input in that
# failure when the input is not a path.
campaign_freeze_digest() {
  local name=$1 kind=$2 input=$3 subject=${4:-$3} value
  if ! value=$(campaign_kind_digest "${kind}" "${input}"); then
    campaign_fail FREEZE CAMPAIGN "${subject}" "digest failed"
  fi
  printf -v "${name}" '%s' "${value}"
}

campaign_freeze() {
  require_file "GraphChecker jar" "${graphchecker_jar}"
  local vm="${custom_jdk_home}/bin/java"
  local rt_jar="${custom_jdk_home}/jre/lib/rt.jar"
  local libjava="${custom_jdk_home}/jre/lib/amd64/libjava.so"
  local libjvm="${custom_jdk_home}/jre/lib/amd64/server/libjvm.so"
  local jar_sha vm_sha rt_jar_sha libjava_sha libjvm_sha config_sha
  local spec_sha mappings_sha bounds_sha symbolic_inputs_sha
  local classes_sha test_classes_sha classpath_sha tool_source workload_source
  [[ -x "${vm}" ]] || die "the concolic VM is not built: ${vm}"
  require_file "concolic rt.jar" "${rt_jar}"
  require_file "concolic libjava" "${libjava}"
  require_file "concolic libjvm" "${libjvm}"
  [[ -d "${project_classes_dir}" ]] || campaign_fail FREEZE CAMPAIGN \
    "${project_classes_dir}" "production classes directory is absent"
  [[ -d "${project_test_classes_dir}" ]] || campaign_fail FREEZE CAMPAIGN \
    "${project_test_classes_dir}" "test classes directory is absent"
  # The twelve inputs, each named once with the digest its kind takes.
  # loopBounds is `file` rather than `optional` on purpose: an optional digest
  # is empty for a file that is not there, and an empty loopBounds.sha256 in
  # the frozen manifest is the one thing an accepted candidate must never
  # carry -- it records "the bounds were whatever" as though it were
  # provenance.
  campaign_freeze_digest jar_sha file "${graphchecker_jar}"
  campaign_freeze_digest vm_sha file "${vm}"
  campaign_freeze_digest rt_jar_sha file "${rt_jar}"
  campaign_freeze_digest libjava_sha file "${libjava}"
  campaign_freeze_digest libjvm_sha file "${libjvm}"
  campaign_freeze_digest config_sha file "${config_file}"
  campaign_freeze_digest spec_sha optional "${causynth_target_spec}"
  campaign_freeze_digest mappings_sha optional \
    "${causynth_communication_mappings}"
  campaign_freeze_digest bounds_sha file "${causynth_loop_bounds}"
  campaign_freeze_digest symbolic_inputs_sha optional \
    "${causynth_symbolic_inputs}"
  campaign_freeze_digest classes_sha tree "${project_classes_dir}"
  campaign_freeze_digest test_classes_sha tree "${project_test_classes_dir}"
  campaign_freeze_digest classpath_sha string "${project_classpath}" \
    project_classpath
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
# libraries, config, target spec, communication mappings, per-loop bounds,
# symbolic input selection, the production/test class trees, and the workload
# classpath
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
        ;;
      tree) ;;
      *) campaign_fail "${failure_stage}" "${failure_component}" "${label}" \
          "unknown frozen provenance entry kind: ${kind}" ;;
    esac
    if ! actual=$(campaign_kind_digest "${kind}" "${path}"); then
      campaign_fail "${failure_stage}" "${failure_component}" "${path}" \
        "frozen input ${label} could not be re-digested"
    fi
    [[ "${actual}" == "${expected}" ]] || campaign_fail "${failure_stage}" \
      "${failure_component}" "${path}" \
      "frozen input ${label} changed after it was frozen: manifest sha256=${expected} current sha256=${actual}"
  done <<<"${rows}"

  # The classpath is a string rather than a file, so its frozen digest is over
  # the string the stages were actually handed. It cannot drift on disk, but it
  # can drift in this process: a stage that rewrote it would leave every replay
  # reading a classpath the manifest does not describe.
  if ! classpath_sha=$(campaign_kind_digest string "${project_classpath}"); then
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

# Schedule the immutable causal candidate closure used for union
# instrumentation, then derive the smaller value closure activated by the
# first linked replay. Producer and consumer regions in that replay still
# share one workload JVM so VM expressions cross their real RPC/field
# boundaries.
campaign_plan() {
  local iteration_dir=$1 carry=$2
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local seed_dir="${iteration_dir}/seed-replay"
  local seed_plan="${seed_dir}/execution_task_plan.jsonl"
  local seed_index="${seed_dir}/runtime_workflow_schedule_index.json"
  local frozen="${iteration_dir}/concolic_region_plan.jsonl"
  local role campaign_id region occurrence goal task worker
  local plan_hash plan_size region_hash region_size

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

  plan_hash=$(campaign_digest "${plan}")
  plan_size=$(stat -c '%s' "${plan}")
  region_hash=$(campaign_digest "${frozen}")
  region_size=$(stat -c '%s' "${frozen}")
  # Immutable paths and digests -- the whole of what the shell owns here. The
  # index must commit exactly the plan bytes this iteration froze. Which tasks
  # it names, what each selects, and by which authority, are the scheduler's
  # own invariants and are not restated against the same file.
  jq -e --arg plan_hash "${plan_hash}" --arg region_hash "${region_hash}" \
    --argjson plan_size "${plan_size}" --argjson region_size "${region_size}" '
      .executionTaskPlan.sha256 == $plan_hash
        and .executionTaskPlan.sizeBytes == $plan_size
        and .regionPlan.sha256 == $region_hash
        and .regionPlan.sizeBytes == $region_size
        and (.target | type == "object")
        and (.members | type == "array" and length > 0)
    ' "${index}" >/dev/null \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index does not commit the frozen task plan"

  mkdir -p "${seed_dir}"
  schedule_output_dir="${seed_dir}"
  schedule_closure_mode=seed-replay
  do_schedule
  schedule_closure_mode=candidate
  require_nonempty "seed replay task plan" "${seed_plan}"
  require_nonempty "seed replay workflow index" "${seed_index}"
  # Seed activation may narrow candidate membership, but task identity must
  # stay byte-for-byte compatible with the union-instrumented candidate plan.
  jq -e --slurpfile candidate "${index}" --slurpfile candidateTasks "${plan}" \
    --slurpfile seedTasks "${seed_plan}" '
      . as $seed
      | $candidate[0] as $all
      | [$candidateTasks[].taskId] as $allTasks
      | [$seedTasks[].taskId] as $activeTasks
      | $seed.target.taskId == $all.target.taskId
        and all($seed.members[];
          .taskId as $task | ($allTasks | index($task)) != null)
        and (($activeTasks | unique | sort)
             == ([$seed.members[].taskId] | unique | sort))
    ' "${seed_index}" >/dev/null || campaign_fail \
      PLAN ConcolicScheduler "${seed_index}" \
      "the seed value closure is not a stable subset of instrumentation candidates"

  # The one task-set membership decode of this iteration. Every later stage
  # reads these rows; the index is frozen beside them and is never re-decoded.
  if ! campaign_member_rows=$(campaign_decode_index_members "${index}"); then
    campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index has an invalid membership schema"
  fi
  [[ -n "${campaign_member_rows}" ]] || campaign_fail PLAN ConcolicScheduler \
    "${index}" "the region-path schedule index names no target member"
  # Member directories own path-closure artifacts, while every member points
  # at the same immutable linked replay plan.  Link it rather than copy it:
  # a copy per member restated one plan once per member, which is most of
  # what a campaign writes (measured: 49 members x 10.2 MB = 498 MB of the
  # 545 MB of task plans in one recorded iteration).  Every writer here
  # publishes through a temporary file and an atomic rename, so a later
  # rewrite replaces a member's entry instead of editing the shared one.
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    worker="${iteration_dir}/workers/${task}"
    mkdir -p "${worker}"
    ln -f "${plan}" "${worker}/execution_task_plan.jsonl"
    campaign_log "member ${role} task=${task} occurrence=${occurrence}"
  done <<<"${campaign_member_rows}"
  campaign_log "planned tasks: $(jq -s 'length' "${plan}") by goal $(jq -r -s '
    group_by(.goalKind) | map("\(.[0].goalKind)=\(length)") | join(" ")' \
    "${plan}")"
  campaign_log "seed replay tasks: $(jq -s 'length' "${seed_plan}")"
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
  local status=0 replay_group plan_digest replay_group_seed
  require_nonempty "concolic execution task plan" "${plan}"
  [[ ! -e "${results}" ]] || die \
    "replay output already exists; worker directories are written once: ${results}"
  mkdir -p "${worker}" "$(dirname "${results}")"
  # Every task in one workload JVM shares one propagation ledger. Replayed
  # bundles already name that group in their tasks; the initial linked plan
  # does not, so give the whole invocation one identity here.
  if ! replay_group=$(jq -e -r -s '
      ([.[] | (.linkedReplayGroupId // "")]) as $all
      | ($all | map(select(length > 0)) | unique) as $named
      | if ($named | length) == 0 then ""
        elif ($named | length) == 1
             and ($all | all(length > 0)) then $named[0]
        else error("linked replay plan has mixed or conflicting group ids")
        end
    ' "${plan}"); then
    die "linked replay plan has mixed or conflicting group ids: ${plan}"
  fi
  if [[ -z "${replay_group}" ]]; then
    # The group names one propagation ledger, so it is seeded from what the
    # ledger is over: the plan these tasks came from and the task ids this
    # invocation replays. The worker directory used to be in the seed and is
    # not: it is a per-iteration filesystem path, so the same plan and the
    # same task ids were given a different group id in every iteration and in
    # every campaign root, which no reader could join across two runs.
    plan_digest=$(campaign_digest "${plan}") \
      || die "failed to digest linked replay plan: ${plan}"
    replay_group_seed=$(printf '%s\0' "${plan_digest}" "${ids}" \
      | sha256sum | awk '{print $1}')
    replay_group="REPLAY.GROUP.${replay_group_seed}"
  fi
  run_capturing_status \
    campaign_run_adapter "replay(${role})" "${concolic_replay_command}" \
    "CAUSYNTH_CONCOLIC_ROLE=${role}" \
    "CAUSYNTH_CONCOLIC_TASK_PLAN=${plan}" \
    "CAUSYNTH_CONCOLIC_TASK_ID=${ids}" \
    "CAUSYNTH_CONCOLIC_RESULTS=${results}" \
    "CAUSYNTH_CONCOLIC_CLASSES=${classes}" \
    "CAUSYNTH_CONCOLIC_WORKER_DIR=${worker}" \
    "CAUSYNTH_CONCOLIC_REPLAY_GROUP_ID=${replay_group}" \
    "CAUSYNTH_CONCOLIC_MAX_TASKS=${schedule_max_jobs}" \
    "CAUSYNTH_TRACE_TEST=${trace_test}" >"${worker}/replay.log" 2>&1
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
  local plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  local results="${seed}/concolic_region_results.jsonl"
  local ids worker status=0
  ids=$(campaign_task_ids "${plan}")
  worker="${seed}/linked-bundle"
  campaign_replay worker "${plan}" "${ids}" \
    "${iteration_dir}/instrumented-classes" "${results}" "${worker}"
  require_nonempty "session replay results" "${results}"
}

campaign_import_session() {
  local iteration_dir=$1 iteration_id=$2
  local seed="${iteration_dir}/seed-result"
  local summaries="${iteration_dir}/concolic_region_summaries.jsonl"
  local role campaign_id region occurrence goal task
  local status=0
  raw_concolic_results="${seed}/concolic_region_results.jsonl"
  import_task_plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  imported_summaries="${summaries}"
  import_diagnostics="${seed}/import_diagnostics.jsonl"
  import_topology_delta="${seed}/topology_delta.jsonl"
  run_capturing_status do_import "${iteration_id}"
  if [[ "${status}" -ne 0 ]]; then
    [[ ! -s "${import_diagnostics}" ]] \
      || jq -c . "${import_diagnostics}" >&2 || true
    campaign_fail IMPORT ConcolicSummaryImporter "${import_diagnostics}" \
      "the campaign raw results could not be strictly imported"
  fi
  require_nonempty "imported region summaries" "${summaries}"
  # Fan the importer's own rows out to the candidate directories.  Candidate
  # occurrences may be dormant on this replay; exact VM evidence selects the
  # active observed closure in SEED_QUERY before any worklist is built.
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    campaign_json select-summary "${summaries}" "${task}" \
      >"${iteration_dir}/workers/${task}/concolic_region_summaries.jsonl"
  done <<<"${campaign_member_rows}"
  campaign_log "imported summaries: $(wc -l <"${summaries}")"
}

# Schedule pass three. The candidate pass feeds union instrumentation; the
# value-frontier pass feeds the linked seed replay. This pass hands the
# scheduler that replay's imported summaries, so VM propagation anchors and
# GuardedRead candidates select the observed ancestry that owns path worklists
# and the target query.
#
# It writes into its own directory because the scheduler always publishes a
# task plan and an index beside its queries, and this iteration's frozen plan
# is not rewritable.
campaign_seed_query() {
  local iteration_dir=$1
  local query_dir="${iteration_dir}/seed-query"
  local active_index="${query_dir}/runtime_workflow_schedule_index.json"
  local seed_index="${iteration_dir}/seed-replay/runtime_workflow_schedule_index.json"
  mkdir -p "${query_dir}"
  schedule_output_dir="${query_dir}"
  schedule_summaries="${iteration_dir}/concolic_region_summaries.jsonl"
  schedule_closure_mode=active-observed
  do_schedule
  schedule_closure_mode=candidate
  require_nonempty "active observed workflow index" "${active_index}"
  require_nonempty "active observed task plan" \
    "${query_dir}/execution_task_plan.jsonl"
  # Active membership can only narrow this iteration's seed candidates.  A VM
  # edge to a previously unknown occurrence remains a topology divergence and
  # is replanned in the next epoch; it is never spliced into this frozen one.
  jq -e --slurpfile seed "${seed_index}" '
    . as $active
    | $seed[0] as $seedIndex
    | [$seedIndex.members[].taskId] as $seedTasks
    | $active.target.taskId == $seedIndex.target.taskId
      and all($active.members[];
        .taskId as $task | ($seedTasks | index($task)) != null)
  ' "${active_index}" >/dev/null || campaign_fail \
    SEED_QUERY ConcolicScheduler "${active_index}" \
    "the active observed closure is not a subset of the seed candidates"
  if ! campaign_member_rows=$(campaign_decode_index_members \
      "${active_index}"); then
    campaign_fail SEED_QUERY ConcolicScheduler "${active_index}" \
      "the active observed closure index is invalid"
  fi
  campaign_log "active observed tasks: $(jq -r '.members | length' \
    "${active_index}")"
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

# One terminal exploration record: the solver's own result for this query,
# stamped with the query it answers, the tasks it linked and why this is the
# end of it.  Three call sites used to spell the same object literal.
campaign_record_exploration() {
  local worker=$1 key=$2 tasks=$3 record_status=$4 reason=$5
  jq -c --arg key "${key}" --arg tasks "${tasks}" \
    --arg status "${record_status}" --arg reason "${reason}" \
    '. + {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD", queryKey: $key,
      linkedTaskIds: ($tasks | split(",")), status: $status, reason: $reason}' \
    "${worker}/path_flip_solver_result.json" \
    >"${worker}/exploration_record.jsonl"
  require_nonempty "path exploration record" \
    "${worker}/exploration_record.jsonl"
}

# One obligation: solve the flip, replay it in its own fresh workload instance,
# strictly import the result, and admit it only against its own planned task.
# The terminal record for an obligation that was solved, replayed and
# imported: which planned task it belongs to, stamped with the query it
# answers.  Whether the imported case is admissible is the importer's
# decision and is already in its artifacts.  An empty PRIMARY selection is
# refused rather than published as a record of nulls.
campaign_publish_primary_record() {
  local task_plan=$1 key=$2 out=$3
  jq -e -c -s --arg key "${key}" '
    map(select(.linkedReplayRole == "PRIMARY")) | .[0]
    | select(. != null)
    | {schemaVersion: 1, kind: "PATH_EXPLORATION_RECORD", queryKey: $key,
     regionId, taskId, occurrenceId, goalId,
     familySnapshotDigest, topologyEpoch,
     status: "VALIDATED_FRESH_REGION_PATH_FLIP_REPLAY"}
    ' "${task_plan}" >"${out}"
}

campaign_worker_task() {
  local query_key=$1 worklist=$2 tasks=$3 classes=$4 worker=$5 iteration_id=$6
  local outcome replay_tasks primary_replay_task reason status=0
  local raw="${worker}/concolic_region_results.jsonl"
  local imported="${worker}/concolic_region_summaries.jsonl"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipSolver \
    --worklist "${worklist}" \
    --task-plan "${tasks}" \
    --query-key "${query_key}" \
    --output-dir "${worker}" \
    --z3 "${z3_bin}" \
    --solver-timeout-ms "${solver_timeout_ms}"
  require_nonempty "path solver result" \
    "${worker}/path_flip_solver_result.json"
  [[ "${status}" -eq 0 ]] || die "the path solver failed with exit ${status}"
  outcome=$(jq -er '.status' "${worker}/path_flip_solver_result.json")
  # The solver owns what a finished flip is. ConcolicPathFlipSolver exits 0
  # for UNSAT, UNSUPPORTED, MATERIALIZATION_GAP and SOLVER_TIMEOUT alike,
  # calling all four "recorded terminal exploration outcomes, not process
  # failures", and the planner records them by queryKey so the flip is not
  # proposed again.  Killing the worker on any of them would make the shell
  # overrule the semantic owner and discard the remaining local path cases
  # in the wave.  A solver that crashed or rejected the query still exits
  # non-zero above and remains fatal.
  case "${outcome}" in
    UNSAT|UNSUPPORTED|MATERIALIZATION_GAP|SOLVER_TIMEOUT)
      jq -c '. + {schemaVersion: 1,
                    kind: "PATH_EXPLORATION_RECORD"}' \
        "${worker}/path_flip_solver_result.json" \
        >"${worker}/exploration_record.jsonl"
      return 0
      ;;
  esac
  [[ "${outcome}" == "SAT_MODEL_READY" ]] \
    || die "the path flip is not solver-backed: ${outcome}"
  replay_tasks=$(campaign_task_ids "${worker}/execution_task_plan.jsonl")
  [[ -n "${replay_tasks}" ]] \
    || die "the linked path solver emitted an empty replay bundle"

  campaign_replay worker "${worker}/execution_task_plan.jsonl" \
    "${replay_tasks}" "${classes}" "${raw}" "${worker}"
  raw_concolic_results="${raw}"
  import_task_plan="${worker}/execution_task_plan.jsonl"
  imported_summaries="${imported}"
  import_diagnostics="${worker}/import_diagnostics.jsonl"
  import_topology_delta="${worker}/topology_delta.jsonl"
  run_capturing_status do_import "${iteration_id}"
  if [[ "${status}" -ne 0 && ! -s "${import_diagnostics}" ]]; then
    die "the importer failed without a semantic diagnostic for ${query_key} (exit ${status})"
  fi
  if [[ -s "${worker}/topology_delta.jsonl" ]] \
      && jq -e 'select(.deltaKind == "TOPOLOGY_DIVERGENCE")' \
        "${worker}/topology_delta.jsonl" >/dev/null; then
    [[ ! -s "${imported}" ]] || mv "${imported}" \
      "${worker}/quarantined_concolic_region_summaries.jsonl"
    : >"${imported}"
    campaign_record_exploration "${worker}" "${query_key}" \
      "${replay_tasks}" BUNDLE_TOPOLOGY_DIVERGENCE \
      "linked replay left the frozen topology epoch"
    : >"${worker}/../../../../.linked-topology-divergence"
    return 0
  fi
  if [[ ! -s "${imported}" ]]; then
    [[ -f "${import_diagnostics}" ]] || die \
      "the importer published no diagnostics for ${query_key}; expected ${import_diagnostics}"
    reason=$(jq -r -s '
      map([(.code // ""), (.detail // "")]
          | map(select(length > 0)) | join(": "))
      | map(select(length > 0)) | unique | join(" | ")
    ' "${import_diagnostics}")
    campaign_record_exploration "${worker}" "${query_key}" \
      "${replay_tasks}" REPLAY_NOT_ADMITTED "${reason}"
    campaign_log "flip ${query_key}: replay admitted no case; recorded REPLAY_NOT_ADMITTED"
    return 0
  fi
  # LinkedReplayBundle refuses a bundle without exactly one primary, and the
  # replay plan carries that bundle's roles, so this reads the primary rather
  # than counting the primaries again.
  primary_replay_task=$(jq -e -r -s '
    map(select(.linkedReplayRole == "PRIMARY")) | .[0].taskId
    ' "${worker}/execution_task_plan.jsonl") \
    || die "the linked replay plan for ${query_key} names no PRIMARY task"
  if ! jq -e -s --arg task "${primary_replay_task}" \
      'any(.[]; .taskId == $task)' "${imported}" >/dev/null; then
    campaign_record_exploration "${worker}" "${query_key}" \
      "${replay_tasks}" REPLAY_NOT_ADMITTED \
      "linked replay admitted companion cases but no primary flip case"
    campaign_log "flip ${query_key}: primary case was not admitted"
    return 0
  fi
  campaign_publish_primary_record "${worker}/execution_task_plan.jsonl" \
    "${query_key}" "${worker}/exploration_record.jsonl" \
    || die "the linked replay plan for ${query_key} names no PRIMARY task to record"
  require_nonempty "path exploration record" \
    "${worker}/exploration_record.jsonl"
}

campaign_publish_wave() {
  local planner_dir=$1 summaries=$2 tasks=$3 records=$4
  local worker worker_list record_status
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
    if ! record_status=$(jq -e -r -s '
        if length == 1 and (.[0].status | type) == "string"
        then .[0].status
        else error("one terminal exploration status is required") end
      ' "${worker}/exploration_record.jsonl"); then
      campaign_fail EXPLORE CAMPAIGN \
        "${worker}/exploration_record.jsonl" \
        "the obligation published no unique terminal status"
    fi
    case "${record_status}" in
      UNSAT|UNSUPPORTED|MATERIALIZATION_GAP|SOLVER_TIMEOUT|REPLAY_NOT_ADMITTED|BUNDLE_TOPOLOGY_DIVERGENCE)
        # Companion summaries from a linked replay whose primary prefix did
        # not match are not a causal observation. Publishing them used to
        # leave propagated boundary values without the primary producer case.
        # Solver-terminal and topology-terminal outcomes likewise contribute
        # only their exploration record; they did not admit a new path case.
        continue
        ;;
      VALIDATED_FRESH_REGION_PATH_FLIP_REPLAY)
        ;;
      *)
        campaign_fail EXPLORE CAMPAIGN \
          "${worker}/exploration_record.jsonl" \
          "the obligation published an unexpected terminal status ${record_status}"
        ;;
    esac
    [[ -s "${worker}/execution_task_plan.jsonl" ]] || continue
    require_nonempty "worker raw result" \
      "${worker}/concolic_region_results.jsonl"
    # A replay can validly remove the causal effect it was exploring.  The
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

# Region-path obligations are coordinated in closure-wide waves below.

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
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.concolic.TargetReachPathQueryBuilder \
    --summaries "${member}/observed_path_summaries.jsonl" \
    --path-manifest "${member}/path_closure.json" \
    --seed-query "${iteration_dir}/seed-query/branch_queries.jsonl" \
    --output "${member}/reach_query.jsonl" >/dev/null
  if [[ "${status}" -ne 0 || ! -s "${member}/reach_query.jsonl" ]]; then
    campaign_fail EXPLORE TargetReachPathQueryBuilder "${member}" \
      "TargetReachPathQueryBuilder published no exact reach query (exit ${status})"
  fi
  campaign_log "target reach paths: $(jq -r '.paths | length' \
    "${member}/reach_query.jsonl")"
}

# EXPLORE-1: the closure loop stops on its own fixed point, and failing that
# on a budget.  A wave that proposes the very same obligations as the wave
# before it, and whose recorded verdicts have not changed either, has learned
# nothing; continuing would re-solve and re-replay the same set forever.  Both
# stops are coverage telemetry, never a campaign failure: an unexplored
# sibling path blocks a closed UNSAT conclusion and says nothing about a SAT
# candidate, so the gap is written onto the still-pending worklists and the
# campaign goes on to publish what it did establish.
campaign_explore_stop() {
  local kind=$1 reason=$2
  shift 2
  local planner_dir member pending_manifest
  for planner_dir in "$@"; do
    member=$(dirname "${planner_dir}")
    pending_manifest="${planner_dir}/region_path_manifest.json"
    [[ -s "${pending_manifest}" ]] || continue
    jq -c --arg kind "${kind}" --arg reason "${reason}" \
      '.coverageGaps = ((.coverageGaps // []) + [{kind: $kind,
         reason: $reason, regionId: .regionId,
         occurrenceId: (.occurrenceId // "")}])' \
      "${pending_manifest}" >"${pending_manifest}.stopped" \
      || campaign_fail EXPLORE RegionPathWorklist "${pending_manifest}" \
        "failed to record the closure stop on a pending worklist"
    mv "${pending_manifest}.stopped" "${pending_manifest}"
    cp -f "${pending_manifest}" "${member}/path_closure.json"
  done
  campaign_log "closure exploration stopped: ${kind}: ${reason}"
}

campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local role campaign_id region occurrence goal task member planner_dir
  local worklist key_rows key worker_dir target_task="" wave_dir roster
  local status=0 wave=0 pending=0 job planner_index
  local wave_signature="" previous_signature="" stop_kind="" stop_reason=""
  local summaries="${iteration_dir}/linked_observed_path_summaries.jsonl"
  local tasks="${iteration_dir}/linked_observed_execution_tasks.jsonl"
  local active_plan="${iteration_dir}/seed-query/execution_task_plan.jsonl"
  local active_seed="${iteration_dir}/active_seed_summaries.jsonl"
  local records="${iteration_dir}/linked_path_exploration_records.jsonl"
  local classes="${iteration_dir}/instrumented-classes"
  local seed_delta="${iteration_dir}/seed-result/topology_delta.jsonl"
  local -a bound_args=() jobs=() pids=() planner_dirs=()
  local -a planner_all_dirs=()
  local -a planner_roles=() planner_tasks=()

  campaign_json select-tasks \
    "${iteration_dir}/concolic_region_summaries.jsonl" "${active_plan}" \
    >"${active_seed}"
  campaign_json combine summaryId "${summaries}" "${active_seed}"
  campaign_json combine taskId "${tasks}" "${active_plan}"
  : >"${records}"
  if [[ -s "${seed_delta}" ]] \
      && jq -e 'select(.deltaKind == "TOPOLOGY_DIVERGENCE")' \
        "${seed_delta}" >/dev/null; then
    campaign_log "seed replay left ${iteration_id}; deferring all flips to the next topology epoch"
    return 0
  fi
  [[ -z "${region_path_max_paths_per_region}" ]] \
    || bound_args+=(--max-paths-per-region "${region_path_max_paths_per_region}")
  [[ -z "${region_path_max_flips_per_path}" ]] \
    || bound_args+=(--max-flips-per-path "${region_path_max_flips_per_path}")
  [[ -z "${region_path_max_tasks}" ]] \
    || bound_args+=(--max-tasks "${region_path_max_tasks}")

  # Every planner in a wave reads the same immutable family snapshot. All
  # returned linked bundles are merged only after the wave settles; the next
  # wave therefore sees every new upstream arm before declaring a downstream
  # local path closed.
  while true; do
    jobs=()
    planner_dirs=()
    planner_all_dirs=()
    planner_roles=()
    planner_tasks=()
    pids=()
    pending=0
    wave_dir=$(printf '%s/obligations-%04d' "${iteration_dir}" "${wave}")
    [[ ! -e "${wave_dir}" ]] || die \
      "obligation wave directory already exists: ${wave_dir}"
    mkdir -p "${wave_dir}"
    roster="${wave_dir}/members.tsv"
    : >"${roster}"
    while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
      member="${iteration_dir}/workers/${task}"
      if [[ "${role}" == "TARGET" ]]; then
        target_task=${task}
      fi
      planner_dir=$(printf '%s/obligations-%04d' "${member}" "${wave}")
      [[ ! -e "${planner_dir}" ]] || die \
        "obligation wave directory already exists: ${planner_dir}"
      mkdir -p "${planner_dir}"
      planner_roles+=("${role}")
      planner_tasks+=("${task}")
      planner_all_dirs+=("${planner_dir}")
      printf '%s\t%s\t%s\n' "${region}" "${goal}" "${planner_dir}" \
        >>"${roster}"
    done <<<"${campaign_member_rows}"
    # Every member of the wave is planned against the same summaries, the same
    # task plan and therefore the same symbolic propagation closure.  One JVM
    # computes that closure once and writes each member's own manifest and
    # worklist into the member's own directory.
    status=0
    run_java_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
      --summaries "${summaries}" \
      --task-plan "${tasks}" \
      --records "${records}" \
      --members "${roster}" \
      --topology-epoch "${iteration_id}" \
      "${bound_args[@]}" \
      >"${wave_dir}/stdout.log" 2>"${wave_dir}/stderr.log" || status=$?
    # Exit 2 names a member whose worklist is not executable; which member it
    # is, is read below from that member's own manifest state.
    if [[ "${status}" -ne 0 && "${status}" -ne 2 ]]; then
      campaign_fail EXPLORE ConcolicPathFlipPlanner \
        "${wave_dir}/stderr.log" \
        "the wave path planner failed with exit ${status}"
    fi

    # Collect in the schedule index's original order. Completion order therefore
    # cannot change manifest publication or the obligation launch order.
    for ((planner_index = 0;
          planner_index < ${#planner_all_dirs[@]}; planner_index++)); do
      role="${planner_roles[planner_index]}"
      task="${planner_tasks[planner_index]}"
      planner_dir="${planner_all_dirs[planner_index]}"
      member="${iteration_dir}/workers/${task}"
      require_nonempty "${role} path worklist manifest" \
        "${planner_dir}/region_path_manifest.json"
      if jq -e '.state == "CLOSED"' \
          "${planner_dir}/region_path_manifest.json" >/dev/null; then
        cp -f "${planner_dir}/region_path_manifest.json" \
          "${member}/path_closure.json"
        continue
      fi
      if ! jq -e '.state == "PENDING"' \
          "${planner_dir}/region_path_manifest.json" >/dev/null; then
        campaign_report_worklist "${planner_dir}"
        campaign_fail EXPLORE RegionPathWorklist \
          "${planner_dir}/region_path_manifest.json" \
          "the ${role} path worklist is not executable"
      fi
      worklist="${planner_dir}/region_path_worklist.jsonl"
      if ! key_rows=$(campaign_decode_worklist_keys "${worklist}"); then
        campaign_fail EXPLORE RegionPathWorklist "${worklist}" \
          "the pending path worklist is missing or malformed"
      fi
      [[ -n "${key_rows}" ]] || campaign_fail EXPLORE RegionPathWorklist \
        "${worklist}" "a pending ${role} worklist named no obligation"
      planner_dirs+=("${planner_dir}")
      while IFS= read -r key; do
        [[ -n "${key}" ]] || continue
        worker_dir="${planner_dir}/${key}"
        jobs+=("${worklist}"$'\t'"${key}"$'\t'"${worker_dir}")
        pending=$((pending + 1))
      done <<<"${key_rows}"
    done

    [[ "${pending}" -gt 0 ]] || break

    # The obligations this wave would solve, plus the verdicts every earlier
    # wave recorded.  Obligation identity is stable across waves
    # (RegionPathWorklist#emitTask), so an unchanged signature means an
    # unchanged frontier over unchanged evidence: a fixed point the
    # `pending -gt 0` test alone cannot see.
    wave_signature=$({
        printf '%s\n' "${jobs[@]}" | cut -f2 | LC_ALL=C sort
        printf -- '--\n'
        jq -r '.status // ""' "${records}" | LC_ALL=C sort | uniq -c
      } | sha256sum | cut -d' ' -f1) \
      || campaign_fail EXPLORE CAMPAIGN "${records}" \
        "failed to summarise closure wave ${wave}"
    stop_kind=""
    if [[ "${wave}" -ge "${region_path_max_waves}" ]]; then
      stop_kind=REGION_PATH_WAVE_BUDGET_REACHED
      stop_reason="the closure loop reached its configured budget of \
${region_path_max_waves} wave(s) with ${pending} obligation(s) still open"
    elif [[ "${wave_signature}" == "${previous_signature}" ]]; then
      stop_kind=REGION_PATH_CLOSURE_NO_PROGRESS
      stop_reason="closure wave ${wave} proposes the same ${pending} \
obligation(s) as the wave before it with no new verdict"
    fi
    if [[ -n "${stop_kind}" ]]; then
      campaign_explore_stop "${stop_kind}" "${stop_reason}" \
        "${planner_dirs[@]}"
      break
    fi
    previous_signature=${wave_signature}
    campaign_log "closure wave ${wave}: ${pending} linked obligation(s), workers=${concolic_worker_count}"
    pids=()
    status=0
    for job in "${jobs[@]}"; do
      IFS=$'\t' read -r worklist key worker_dir <<<"${job}"
      mkdir -p "${worker_dir}"
      (
        set -euo pipefail
        campaign_worker_task "${key}" "${worklist}" "${tasks}" \
          "${classes}" "${worker_dir}" "${iteration_id}"
      ) >"${worker_dir}/stdout.log" 2>"${worker_dir}/stderr.log" &
      pids+=("$!")
      if [[ ${#pids[@]} -eq ${concolic_worker_count} ]]; then
        campaign_wait_workers "${pids[@]}" || status=1
        pids=()
      fi
    done
    if [[ ${#pids[@]} -gt 0 ]]; then
      campaign_wait_workers "${pids[@]}" || status=1
    fi
    if [[ "${status}" -ne 0 ]]; then
      for planner_dir in "${planner_dirs[@]}"; do
        campaign_report_wave "${planner_dir}"
      done
      campaign_fail EXPLORE CAMPAIGN "${iteration_dir}/workers" \
        "closure obligation wave ${wave} did not finish"
    fi
    # One diverging linked bundle invalidates this frozen epoch. Keep every
    # wave result private; CLASSIFY consumes the worker delta and the next
    # iteration replans instead of mixing sibling results into the old corpus.
    [[ ! -e "${iteration_dir}/.linked-topology-divergence" ]] || return 0
    for planner_dir in "${planner_dirs[@]}"; do
      campaign_publish_wave "${planner_dir}" "${summaries}" "${tasks}" \
        "${records}"
    done
    wave=$((wave + 1))
  done

  # A worklist can stop because its configured exploration bound was reached.
  # Its state is then CLOSED, but its coverageState remains PARTIAL. Preserve
  # that distinction in every summary so the final selected path family cannot
  # be accepted before its bounded exploration is complete.
  campaign_path_closures_json "${iteration_dir}/workers" \
    >"${summaries}.path-closures" \
    || campaign_fail EXPLORE RegionPathWorklist \
      "${iteration_dir}/workers" \
      "failed to read the closure-wide worklist reports"
  jq -c --slurpfile closures "${summaries}.path-closures" '
    . as $summary
    | ([$closures[0][]
        | select(.regionId == $summary.regionId
            and .occurrenceId == $summary.plannedOccurrenceId
            and .sourceKey == $summary.sourceKey)]) as $matches
    | . + {pathSetClosed:
        (($matches | length) == 1
         and $matches[0].state == "CLOSED"
         and $matches[0].coverageState == "CLOSED"
         and (($matches[0].coverageGaps // []) | length) == 0)}
  ' "${summaries}" >"${summaries}.closed" \
    || campaign_fail EXPLORE RegionPathWorklist "${summaries}" \
      "failed to publish the closure-wide fixed-point corpus"
  rm -f "${summaries}.path-closures"
  mv "${summaries}.closed" "${summaries}"

  # Final consumers all read the identical closure-wide fixed point, so link
  # it rather than copy it.  One copy per member is the largest thing a
  # campaign writes: measured on recorded runs, l1/out5 held 25 copies of one
  # 130.7 MB corpus (3266.9 MB) and 25 of one 24.6 MB task set (615.6 MB).
  # Both files are published above by an atomic rename and nothing rewrites a
  # member's entry in place, so the link cannot carry an edit between members.
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    member="${iteration_dir}/workers/${task}"
    ln -f "${summaries}" "${member}/observed_path_summaries.jsonl"
    ln -f "${tasks}" "${member}/observed_execution_tasks.jsonl"
  done <<<"${campaign_member_rows}"
  campaign_target_reach_query "${iteration_dir}" "${target_task}"
  campaign_log "closure exploration stopped after ${wave} global wave(s)"
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
  local index="${iteration_dir}/seed-query/runtime_workflow_schedule_index.json"
  local plan="${iteration_dir}/seed-query/execution_task_plan.jsonl"
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
  if ! plan_sha=$(campaign_digest "${plan}"); then
    campaign_fail EMIT CAMPAIGN "${plan}" \
      "failed to digest the active observed execution task plan"
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
    --arg plan "${plan}" \
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
}

# Composition consumes the closure-wide local cases. Consumer anchors inside
# those path conditions already carry the propagated values into the formula.
campaign_compose() {
  local iteration_dir=$1
  local role campaign_id region occurrence goal task
  local target_task="" target_region="" target_occurrence=""
  local status=0 observed
  local -a observed_inputs=()
  while IFS=$'\t' read -r role campaign_id region occurrence goal task; do
    require_nonempty "linked member observed summaries" \
      "${iteration_dir}/workers/${task}/observed_path_summaries.jsonl"
    observed_inputs+=(
      "${iteration_dir}/workers/${task}/observed_path_summaries.jsonl")
    if [[ "${role}" == "TARGET" ]]; then
      target_task=${task}
      target_region=${region}
      target_occurrence=${occurrence}
    fi
  done <<<"${campaign_member_rows}"
  [[ ! -e "${campaign_final}" ]] || die \
    "the final directory already exists: ${campaign_final}"
  mkdir -p "${campaign_final}"
  fatal_queries="${iteration_dir}/workers/${target_task}/reach_query.jsonl"
  require_nonempty "target reach query" "${fatal_queries}"
  observed="${iteration_dir}/closure_observed_summaries.jsonl"
  campaign_json combine summaryId "${observed}" "${observed_inputs[@]}"
  require_nonempty "closure-wide observed summaries" "${observed}"
  compose_summary_inputs="${observed}"
  composed_smt="${campaign_final}/candidate.smt2"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  fatal_region="${target_region}"
  fatal_occurrence_id="${target_occurrence}"
  run_capturing_status do_compose >/dev/null
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
  run_capturing_status do_reach >/dev/null
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
       | unique_by([.stage, .source, .code, .subject, .detail])) as $gaps |
    ([$composed.gaps[]?
           | {stage: "COMPOSE", source: "COMPOSER",
              code: (.reason // .kind // ""),
              subject: (.subject // ""), detail: (.detail // "")}]
       + [if ($composed.pathSetComplete // false)
            then empty else
            {stage: "COMPOSE", source: "COVERAGE",
             code: "SELECTED_PATH_SET_INCOMPLETE", subject: "",
             detail: "required only for a closed UNSAT conclusion"} end]
       + [$composed.boundedLoopComposition.gaps[]?
           | {stage: "COMPOSE", source: "BOUNDED_LOOP",
              code: (.reason // .kind // ""),
              subject: (.subject // ""), detail: (.detail // "")}]
       + [$composed.symbolicPropagationGaps[]?
           | {stage: "COMPOSE", source: "SYMBOLIC_PROPAGATION",
              code: (.reason // .kind // ""),
              subject: (.subject // ""), detail: (.detail // "")}]
       + [$composed.faultControlGaps[]?
           | {stage: "COMPOSE", source: "FAULT_CONTROL",
              code: (.reason // .kind // ""),
              subject: (.subject // ""), detail: (.detail // "")}]
       + [$pathClosures[]? as $closure
           | $closure.coverageGaps[]?
           | {stage: "EXPLORE", source: "PATH_WORKLIST",
              code: (.kind // ""),
              subject: (.queryKey // .regionId
                        // .evidenceIdentity.taskId // ""),
              detail: ([(.reason // ""), (.detail // "")]
                       | map(select(. != "")) | join(": "))}]
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

  # Formula/solver gaps block a candidate. Exploration, loop-bound and
  # propagation-merge coverage stay as telemetry: they are needed to justify
  # a closed UNSAT result, while one connected SAT witness is already valid.
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

  # The claim is the ClaimPolicy decision the solver stage published with its
  # own report.  Nothing here recomputes it: this stage copies the claim, its
  # reason, and every named blocker, so one Java policy decides acceptance and
  # the shell only publishes what it decided.
  campaign_require_claim "${reach_report}"
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --slurpfile composedDocuments "${composition_manifest}" \
    --slurpfile reachDocuments "${reach_report}" \
    --slurpfile gapDocuments "${campaign_final}/gaps.json" '
    $composedDocuments[0] as $c | $reachDocuments[0] as $r |
    $gapDocuments[0] as $gaps |
    ($r.campaignClaim) as $decided |
    ($r.reachCondition.reachability // "UNKNOWN") as $reachability |
    ($r.reachCondition.degeneracyCheck // "UNDECIDED") as $degeneracy |
    ($r.unsatClosureComplete // false) as $unsatClosureComplete |
    ($gaps.gapCount) as $gapCount |
    ($gaps.telemetryCount) as $telemetryCount |
    (($c.finalStatusRefusals // []) | length) as $blockers |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     provenance: $provenance,
     claim: $decided.claim,
     claimReason: $decided.claimReason,
     blockers: $decided.blockers,
     blockerCount: ($decided.blockers | length),
     whyNotAccepted: $decided.whyNotAccepted,
     reachability: $reachability,
     degeneracyCheck: $degeneracy,
     solverState: ($r.state // ""),
     finalStatus: ($c.finalStatus // ""),
     finalStatusRefusals: $blockers,
     evidence: {
       symbolicPropagationComplete:
         ($c.symbolicPropagationComplete // false),
       # Copied from the policy, which counts the consumer boundary families
       # the Composer publishes. Reading the retired symbolicPropagation
       # array here reported zero families on every real manifest.
       consumerBoundaryFamilies:
         ($decided.rootSpace.consumerBoundaryFamilies // 0),
       consumerBoundaryArms:
         ($decided.rootSpace.consumerBoundaryArms // 0),
       declaredWireFlows:
         ($decided.rootSpace.declaredWireFlows // 0),
       wireFlows: ($decided.rootSpace.wireFlows // []),
       guardedReadModelComplete:
         ($c.guardedReadModelComplete // false),
       guardedReads:
         (($c.guardedReadModel.reads // []) | length),
       guardedReadCandidates:
         ([$c.guardedReadModel.reads[]? | ((.arms // []) | length)]
          | add // 0),
       unsatClosureComplete: $unsatClosureComplete,
       casePathConditionFamilies:
         (($c.casePathConditionDependencies // []) | length)},
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
  jq -r '"  claim=\(.claim) reachability=\(.reachability) blockers=\(.blockerCount) gaps=\(.gapCount) telemetry=\(.telemetryCount) finalStatus=\(.finalStatus)"' \
    "${campaign_final}/result.json"
  # One view of why a run was not accepted, with a line per named blocker.
  # finalStatus stays printed above as the stage-local state it is; this is
  # the acceptance answer.
  jq -r 'select((.whyNotAccepted // "") != "") | .whyNotAccepted' \
    "${campaign_final}/result.json"
  # A published artifact set is not an accepted candidate. A run that reached
  # no witness and no closed refutation exits nonzero with its own named
  # reason, because a top-level zero exit is not completion.
  case "$(jq -r '.claim' "${campaign_final}/result.json")" in
    SAT_CANDIDATE|UNSAT_CLOSED) ;;
    *)
      jq -r '"[campaign] no accepted candidate: claim=\(.claim) reason=\(.claimReason)"' \
        "${campaign_final}/result.json" >&2
      jq -r 'select((.whyNotAccepted // "") != "") | .whyNotAccepted' \
        "${campaign_final}/result.json" >&2
      exit 2
      ;;
  esac
  # Formula and solver gaps remain hard failures. Coverage gaps are telemetry
  # above and only keep an UNSAT result from becoming UNSAT_CLOSED.
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
