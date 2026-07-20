#!/usr/bin/env bash

set -euo pipefail

graphchecker_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
default_graphchecker_jar="${graphchecker_dir}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"

config_file=""
config_dir="${graphchecker_dir}"
dry_run=${GRAPH_CHECKER_DRY_RUN:-false}
debug_graphs=${GRAPH_CHECKER_DEBUG:-false}
debug_max_items=${GRAPH_CHECKER_DEBUG_MAX_ITEMS:-40}
debug_max_bytes=${GRAPH_CHECKER_DEBUG_MAX_BYTES:-1048576}

usage() {
  cat <<'EOF'
Usage:
  ./run_engine.sh [--config FILE] [--dry-run] [--debug] <command> [args...]
  ./run_engine.sh process <legacy-conf>

Config-driven commands:
  build       Build GraphChecker with the configured Maven/POM/work directory
  analyze     Run GraphCheckerMain over the configured target classes
  schedule    Create concolic jobs and the instance-scoped merge plan
  import      Strictly import raw concolic runtime results
  merge       Merge imported output paths into guarded region relations
  compose     Compose the fatal query and upstream summaries into SMT-LIB
  solve       Run generated SMT relationship obligations through Z3
  reach       Project the composed bug path onto finite Boolean root inputs
  workload    Run the configured target workload command
  debug-stage Print an already-produced analyze/workload/schedule/merge/compose artifact
  config      Print the normalized workflow configuration
  validate    Validate required workflow configuration fields

Compatibility commands:
  process <conf>    Run the original config-based Soot transformer
  transform <conf>  Alias for process
  help              Print this help message

Extra arguments after a workflow command are forwarded to its Maven or Java
entry point. Environment variables documented in experiments/generic/README.md
override values loaded from FILE.

--debug prints deterministic, bounded workflow artifacts to stderr after
analyze, workload, schedule, merge, and compose. GRAPH_CHECKER_DEBUG=true is
the environment equivalent; *_MAX_ITEMS and *_MAX_BYTES adjust its caps.
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
    workflow_path_base|graphchecker_jar|graphchecker_pom|java_bin|maven_bin|graphchecker_work_dir|build_maven_args|project_repo|causynth_repo|project_module_dir|causynth_module_dir|project_classes_dir|system_classes_path|project_test_classes_dir|project_classpath|java_class_path|analysis_classes_dir|instrumented_classes_dir|causynth_output_dir|causynth_target_spec|causynth_analysis_scope|causynth_process_dirs|custom_jdk_home|concolic_jdk_home|z3_bin|rpc_mapping_file|workload_work_dir|workload_command|static_regions|static_graph|runtime_activation_plan|runtime_region_instances|runtime_edge_validations|schedule_output_dir|schedule_summaries|schedule_path_records|schedule_region_id|schedule_activation_id|schedule_target_site|raw_concolic_results|import_activation_plan|imported_summaries|import_diagnostics|summary_cache_dir|merge_summary_inputs|path_manifest|merged_summaries|merge_manifest|fatal_queries|compose_summary_inputs|symbolic_merge_plan|composed_smt|composition_manifest|relationship_candidates|proof_report|reach_report|fatal_region|fatal_activation_id|solver_timeout_ms|reach_max_inputs|reach_max_valuations)
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
  graphchecker_pom=""
  java_bin=""
  maven_bin=""
  graphchecker_work_dir=""
  build_maven_args=""
  project_repo=""
  causynth_repo=""
  project_module_dir=""
  causynth_module_dir=""
  project_classes_dir=""
  system_classes_path=""
  project_test_classes_dir=""
  project_classpath=""
  java_class_path=""
  analysis_classes_dir=""
  instrumented_classes_dir=""
  causynth_output_dir=""
  causynth_target_spec=""
  causynth_analysis_scope=""
  causynth_process_dirs=""
  custom_jdk_home=""
  concolic_jdk_home=""
  z3_bin=""
  rpc_mapping_file=""
  workload_work_dir=""
  workload_command=""
  static_regions=""
  static_graph=""
  runtime_activation_plan=""
  runtime_region_instances=""
  runtime_edge_validations=""
  schedule_output_dir=""
  schedule_summaries=""
  schedule_path_records=""
  schedule_region_id=""
  schedule_activation_id=""
  schedule_target_site=""
  raw_concolic_results=""
  import_activation_plan=""
  imported_summaries=""
  import_diagnostics=""
  summary_cache_dir=""
  merge_summary_inputs=""
  path_manifest=""
  merged_summaries=""
  merge_manifest=""
  fatal_queries=""
  compose_summary_inputs=""
  symbolic_merge_plan=""
  composed_smt=""
  composition_manifest=""
  relationship_candidates=""
  proof_report=""
  reach_report=""
  fatal_region=""
  fatal_activation_id=""
  solver_timeout_ms=""
  reach_max_inputs=""
  reach_max_valuations=""
}

# Generic workflow configs deliberately use a small key=value grammar. Unknown
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
  apply_env_override graphchecker_pom GRAPH_CHECKER_POM
  apply_env_override java_bin GRAPH_CHECKER_JAVA
  apply_env_override maven_bin GRAPH_CHECKER_MAVEN
  apply_env_override graphchecker_work_dir GRAPH_CHECKER_WORK_DIR
  apply_env_override build_maven_args GRAPH_CHECKER_BUILD_ARGS
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
  apply_env_override custom_jdk_home CAUSYNTH_CUSTOM_JDK_HOME
  apply_env_override z3_bin CAUSYNTH_Z3
  apply_env_override rpc_mapping_file CAUSYNTH_RPC_MAPPING_FILE
  apply_env_override workload_work_dir CAUSYNTH_WORKLOAD_WORK_DIR
  apply_env_override workload_command CAUSYNTH_WORKLOAD_COMMAND
  apply_env_override static_regions CAUSYNTH_STATIC_REGIONS
  apply_env_override static_graph CAUSYNTH_STATIC_GRAPH
  apply_env_override runtime_activation_plan CAUSYNTH_ACTIVATION_PLAN
  apply_env_override runtime_region_instances CAUSYNTH_RUNTIME_REGION_INSTANCES
  apply_env_override runtime_edge_validations CAUSYNTH_EDGE_VALIDATIONS
  apply_env_override schedule_output_dir CAUSYNTH_SCHEDULE_OUTPUT_DIR
  apply_env_override schedule_summaries CAUSYNTH_SCHEDULE_SUMMARIES
  apply_env_override schedule_path_records CAUSYNTH_SCHEDULE_PATH_RECORDS
  apply_env_override schedule_region_id CAUSYNTH_SCHEDULE_REGION_ID
  apply_env_override schedule_activation_id CAUSYNTH_SCHEDULE_ACTIVATION_ID
  apply_env_override schedule_target_site CAUSYNTH_SCHEDULE_TARGET_SITE
  apply_env_override raw_concolic_results CAUSYNTH_RAW_RESULTS
  apply_env_override import_activation_plan CAUSYNTH_IMPORT_ACTIVATION_PLAN
  apply_env_override imported_summaries CAUSYNTH_IMPORTED_SUMMARIES
  apply_env_override import_diagnostics CAUSYNTH_IMPORT_DIAGNOSTICS
  apply_env_override summary_cache_dir CAUSYNTH_SUMMARY_CACHE_DIR
  apply_env_override merge_summary_inputs CAUSYNTH_MERGE_SUMMARIES
  apply_env_override path_manifest CAUSYNTH_PATH_MANIFEST
  apply_env_override merged_summaries CAUSYNTH_MERGED_SUMMARIES
  apply_env_override merge_manifest CAUSYNTH_MERGE_MANIFEST
  apply_env_override fatal_queries CAUSYNTH_FATAL_QUERIES
  apply_env_override compose_summary_inputs CAUSYNTH_COMPOSE_SUMMARIES
  apply_env_override symbolic_merge_plan CAUSYNTH_MERGE_PLAN
  apply_env_override composed_smt CAUSYNTH_COMPOSED_SMT
  apply_env_override composition_manifest CAUSYNTH_COMPOSITION_MANIFEST
  apply_env_override relationship_candidates CAUSYNTH_RELATIONSHIP_CANDIDATES
  apply_env_override proof_report CAUSYNTH_PROOF_REPORT
  apply_env_override reach_report CAUSYNTH_REACH_REPORT
  apply_env_override fatal_region CAUSYNTH_FATAL_REGION
  apply_env_override fatal_activation_id CAUSYNTH_FATAL_ACTIVATION_ID
  apply_env_override solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS
  apply_env_override reach_max_inputs CAUSYNTH_REACH_MAX_INPUTS
  apply_env_override reach_max_valuations CAUSYNTH_REACH_MAX_VALUATIONS
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
  graphchecker_pom=${graphchecker_pom:-@project/pom.xml}
  java_bin=${java_bin:-java}
  maven_bin=${maven_bin:-mvn}
  graphchecker_work_dir=${graphchecker_work_dir:-@project/.}
  build_maven_args=${build_maven_args:-clean package -DskipTests}

  project_repo=${project_repo:-${causynth_repo:-@project/.}}
  project_repo=$(resolve_path "${project_repo}" "${workflow_path_base}")
  project_module_dir=${project_module_dir:-${causynth_module_dir:-${project_repo}}}
  project_classes_dir=${project_classes_dir:-${system_classes_path:-@repo/target/classes}}
  project_test_classes_dir=${project_test_classes_dir:-@repo/target/test-classes}
  project_classpath=${project_classpath:-${java_class_path:-}}
  causynth_output_dir=${causynth_output_dir:-@project/target/causynth-workflow}
  causynth_target_spec=${causynth_target_spec:-@config/target.yaml}
  analysis_classes_dir=${analysis_classes_dir:-${instrumented_classes_dir:-${causynth_output_dir}/instrumented-classes}}
  custom_jdk_home=${custom_jdk_home:-${concolic_jdk_home:-}}
  z3_bin=${z3_bin:-z3}
  workload_work_dir=${workload_work_dir:-${project_module_dir}}
  solver_timeout_ms=${solver_timeout_ms:-20000}
  reach_max_inputs=${reach_max_inputs:-12}
  reach_max_valuations=${reach_max_valuations:-4096}

  graphchecker_jar=$(resolve_path "${graphchecker_jar}")
  graphchecker_pom=$(resolve_path "${graphchecker_pom}")
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
  maven_bin=$(resolve_executable "${maven_bin}")
  z3_bin=$(resolve_executable "${z3_bin}")

  if [[ -z "${project_classpath}" ]]; then
    project_classpath="${project_classes_dir}:${project_test_classes_dir}"
  else
    project_classpath=$(resolve_path_list "${project_classpath}")
  fi
  if [[ -n "${causynth_process_dirs}" ]]; then
    causynth_process_dirs=$(resolve_path_list "${causynth_process_dirs}")
  fi
  if [[ -n "${rpc_mapping_file}" ]]; then
    rpc_mapping_file=$(resolve_path "${rpc_mapping_file}")
  fi

  static_regions=${static_regions:-${causynth_output_dir}/symbolic_regions.jsonl}
  static_graph=${static_graph:-${causynth_output_dir}/static_dataflow_edges.jsonl}
  runtime_activation_plan=${runtime_activation_plan:-${causynth_output_dir}/runtime/concolic_activation_plan.jsonl}
  runtime_region_instances=${runtime_region_instances:-${causynth_output_dir}/runtime/runtime_region_instances.jsonl}
  runtime_edge_validations=${runtime_edge_validations:-${causynth_output_dir}/runtime/runtime_region_edge_validation.jsonl}
  schedule_output_dir=${schedule_output_dir:-${causynth_output_dir}/schedule}
  raw_concolic_results=${raw_concolic_results:-${schedule_output_dir}/concolic_region_results.jsonl}
  import_activation_plan=${import_activation_plan:-${schedule_output_dir}/scheduled_activation_plan.jsonl}
  imported_summaries=${imported_summaries:-${schedule_output_dir}/concolic_region_summaries.jsonl}
  import_diagnostics=${import_diagnostics:-${schedule_output_dir}/concolic_import_diagnostics.jsonl}
  summary_cache_dir=${summary_cache_dir:-${schedule_output_dir}/concolic-summary-cache}
  merge_summary_inputs=${merge_summary_inputs:-${imported_summaries}}
  path_manifest=${path_manifest:-${schedule_output_dir}/region_path_manifest.json}
  merged_summaries=${merged_summaries:-${schedule_output_dir}/merged_region_summaries.jsonl}
  merge_manifest=${merge_manifest:-${schedule_output_dir}/region_relation_merge_manifest.json}
  fatal_queries=${fatal_queries:-${schedule_output_dir}/branch_queries.jsonl}
  compose_summary_inputs=${compose_summary_inputs:-${merged_summaries}}
  symbolic_merge_plan=${symbolic_merge_plan:-${schedule_output_dir}/symbolic_merge_plan.json}
  composed_smt=${composed_smt:-${schedule_output_dir}/composed_fatal.smt2}
  composition_manifest=${composition_manifest:-${schedule_output_dir}/composed_smt_manifest.json}
  relationship_candidates=${relationship_candidates:-${schedule_output_dir}/symbolic_relationship_candidates.json}
  proof_report=${proof_report:-${schedule_output_dir}/symbolic_relationship_proofs.json}
  reach_report=${reach_report:-${schedule_output_dir}/boolean_reach_condition.json}

  static_regions=$(resolve_path "${static_regions}")
  static_graph=$(resolve_path "${static_graph}")
  runtime_activation_plan=$(resolve_path "${runtime_activation_plan}")
  runtime_region_instances=$(resolve_path "${runtime_region_instances}")
  runtime_edge_validations=$(resolve_path "${runtime_edge_validations}")
  schedule_output_dir=$(resolve_path "${schedule_output_dir}")
  raw_concolic_results=$(resolve_path "${raw_concolic_results}")
  import_activation_plan=$(resolve_path "${import_activation_plan}")
  imported_summaries=$(resolve_path "${imported_summaries}")
  import_diagnostics=$(resolve_path "${import_diagnostics}")
  summary_cache_dir=$(resolve_path "${summary_cache_dir}")
  merge_summary_inputs=$(resolve_path_list "${merge_summary_inputs}")
  path_manifest=$(resolve_path "${path_manifest}")
  merged_summaries=$(resolve_path "${merged_summaries}")
  merge_manifest=$(resolve_path "${merge_manifest}")
  fatal_queries=$(resolve_path "${fatal_queries}")
  compose_summary_inputs=$(resolve_path_list "${compose_summary_inputs}")
  symbolic_merge_plan=$(resolve_path "${symbolic_merge_plan}")
  composed_smt=$(resolve_path "${composed_smt}")
  composition_manifest=$(resolve_path "${composition_manifest}")
  relationship_candidates=$(resolve_path "${relationship_candidates}")
  proof_report=$(resolve_path "${proof_report}")
  reach_report=$(resolve_path "${reach_report}")
  if [[ -n "${schedule_summaries}" ]]; then
    schedule_summaries=$(resolve_path "${schedule_summaries}")
  fi
  if [[ -n "${schedule_path_records}" ]]; then
    schedule_path_records=$(resolve_path "${schedule_path_records}")
  fi
}

require_config() {
  [[ -n "${config_file}" ]] || die "$1 requires --config FILE"
}

require_file() {
  [[ -f "$2" ]] || die "$1 not found: $2"
}

require_directory() {
  [[ -d "$2" ]] || die "$1 directory not found: $2"
}

ensure_output_directory() {
  if [[ "${dry_run}" != true ]]; then
    mkdir -p "$1"
  fi
}

print_command() {
  local arg
  printf '[dry-run]'
  for arg in "$@"; do
    printf ' %q' "${arg}"
  done
  printf '\n'
}

run_in_directory() {
  local directory=$1
  shift
  require_directory "working" "${directory}"
  if [[ "${dry_run}" == true ]]; then
    print_command env "WORK_DIR=${directory}" "$@"
  else
    (cd "${directory}" && "$@")
  fi
}

run_java_main() {
  local main_class=$1
  shift
  require_file "GraphChecker jar" "${graphchecker_jar}"
  run_in_directory "${graphchecker_work_dir}" "${java_bin}" \
    -cp "${graphchecker_jar}" "${main_class}" "$@"
}

print_normalized_config() {
  local key
  for key in config_file workflow_path_base graphchecker_jar graphchecker_pom java_bin maven_bin graphchecker_work_dir project_repo project_module_dir project_classes_dir project_test_classes_dir project_classpath analysis_classes_dir causynth_output_dir causynth_target_spec causynth_process_dirs custom_jdk_home z3_bin rpc_mapping_file workload_work_dir workload_command static_regions static_graph runtime_activation_plan runtime_region_instances runtime_edge_validations schedule_output_dir raw_concolic_results import_activation_plan imported_summaries path_manifest merged_summaries fatal_queries symbolic_merge_plan composed_smt composition_manifest relationship_candidates proof_report reach_report solver_timeout_ms reach_max_inputs reach_max_valuations; do
    printf '%s=%s\n' "${key}" "${!key}"
  done
}

validate_config() {
  local key
  local missing=0
  for key in project_repo project_module_dir project_classes_dir project_classpath causynth_output_dir causynth_target_spec custom_jdk_home z3_bin workload_command; do
    if [[ -z "${!key}" ]]; then
      echo "Missing workflow config value: ${key}" >&2
      missing=1
    fi
  done
  [[ ${missing} -eq 0 ]] || return 1
  case "${solver_timeout_ms}" in
    ''|*[!0-9]*) die "solver_timeout_ms must be a positive integer" ;;
    0) die "solver_timeout_ms must be greater than zero" ;;
  esac
  case "${reach_max_inputs}" in
    ''|*[!0-9]*) die "reach_max_inputs must be a positive integer" ;;
    0) die "reach_max_inputs must be greater than zero" ;;
  esac
  case "${reach_max_valuations}" in
    ''|*[!0-9]*) die "reach_max_valuations must be a positive integer" ;;
    0) die "reach_max_valuations must be greater than zero" ;;
  esac
  echo "Workflow configuration is valid."
}

do_build() {
  local -a configured_args
  local -a command_args
  read -r -a configured_args <<< "${build_maven_args}"
  command_args=("${configured_args[@]}" "$@")
  require_file "GraphChecker POM" "${graphchecker_pom}"
  run_in_directory "${graphchecker_work_dir}" "${maven_bin}" \
    -f "${graphchecker_pom}" "${command_args[@]}"
}

do_analyze() {
  require_file "target specification" "${causynth_target_spec}"
  require_directory "project repository" "${project_repo}"
  require_directory "project module" "${project_module_dir}"
  local input_flag
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
    "-Dcausynth.repo=${project_repo}"
    "-Dcausynth.module.dir=${project_module_dir}"
    "-Dcausynth.output.dir=${causynth_output_dir}"
    "-Dcausynth.target.spec=${causynth_target_spec}"
  )
  if [[ -n "${causynth_analysis_scope}" ]]; then
    system_properties+=("-Dcausynth.analysis.scope=${causynth_analysis_scope}")
  fi
  if [[ -n "${causynth_process_dirs}" ]]; then
    system_properties+=("-Dcausynth.process.dirs=${causynth_process_dirs}")
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
  require_file "symbolic regions" "${static_regions}"
  require_file "runtime activation plan" "${runtime_activation_plan}"
  require_file "runtime edge validations" "${runtime_edge_validations}"
  ensure_output_directory "${schedule_output_dir}"
  local -a args
  args=(
    --regions "${static_regions}"
    --activation-plan "${runtime_activation_plan}"
    --edge-validations "${runtime_edge_validations}"
    --output-dir "${schedule_output_dir}"
  )
  if [[ -f "${static_graph}" ]]; then
    args+=(--static-graph "${static_graph}")
  fi
  if [[ -f "${runtime_region_instances}" ]]; then
    args+=(--runtime-region-instances "${runtime_region_instances}")
  fi
  if [[ -n "${schedule_summaries}" ]]; then
    require_file "scheduler summaries" "${schedule_summaries}"
    args+=(--summaries "${schedule_summaries}")
  fi
  if [[ -n "${schedule_path_records}" ]]; then
    require_file "scheduler path records" "${schedule_path_records}"
    args+=(--path-records "${schedule_path_records}")
  fi
  [[ -z "${schedule_region_id}" ]] || args+=(--region-id "${schedule_region_id}")
  [[ -z "${schedule_activation_id}" ]] || args+=(--activation-id "${schedule_activation_id}")
  [[ -z "${schedule_target_site}" ]] || args+=(--target-site "${schedule_target_site}")
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler \
    "${args[@]}" "$@"
}

do_import() {
  require_file "raw concolic results" "${raw_concolic_results}"
  require_file "import activation plan" "${import_activation_plan}"
  require_file "symbolic regions" "${static_regions}"
  ensure_output_directory "$(dirname "${imported_summaries}")"
  ensure_output_directory "${summary_cache_dir}"
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter \
    --results "${raw_concolic_results}" \
    --activation-plan "${import_activation_plan}" \
    --regions "${static_regions}" \
    --output "${imported_summaries}" \
    --diagnostics "${import_diagnostics}" \
    --cache-dir "${summary_cache_dir}" "$@"
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

do_merge() {
  require_file "region path manifest" "${path_manifest}"
  ensure_output_directory "$(dirname "${merged_summaries}")"
  PATH_LIST_ARGUMENTS=()
  append_path_list_arguments --summaries "${merge_summary_inputs}"
  [[ ${#PATH_LIST_ARGUMENTS[@]} -gt 0 ]] || die "merge_summary_inputs is empty"
  run_java_main edu.uva.liftlab.graphchecker.concolic.RegionSummaryMerger \
    "${PATH_LIST_ARGUMENTS[@]}" \
    --path-manifest "${path_manifest}" \
    --output "${merged_summaries}" \
    --manifest "${merge_manifest}" "$@"
}

do_compose() {
  require_file "fatal branch queries" "${fatal_queries}"
  require_file "symbolic regions" "${static_regions}"
  require_file "symbolic merge plan" "${symbolic_merge_plan}"
  ensure_output_directory "$(dirname "${composed_smt}")"
  PATH_LIST_ARGUMENTS=()
  append_path_list_arguments --summaries "${compose_summary_inputs}"
  [[ ${#PATH_LIST_ARGUMENTS[@]} -gt 0 ]] || die "compose_summary_inputs is empty"
  local -a selection
  selection=()
  [[ -z "${fatal_region}" ]] || selection+=(--fatal-region "${fatal_region}")
  [[ -z "${fatal_activation_id}" ]] || selection+=(--activation-id "${fatal_activation_id}")
  run_java_main edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer \
    --fatal-query "${fatal_queries}" \
    "${PATH_LIST_ARGUMENTS[@]}" \
    --regions "${static_regions}" \
    --merge-plan "${symbolic_merge_plan}" \
    --output "${composed_smt}" \
    --manifest "${composition_manifest}" \
    --relationships "${relationship_candidates}" \
    "${selection[@]}" "$@"
}

do_solve() {
  require_file "composed SMT" "${composed_smt}"
  require_file "relationship candidates" "${relationship_candidates}"
  ensure_output_directory "$(dirname "${proof_report}")"
  run_java_main edu.uva.liftlab.graphchecker.concolic.SymbolicRelationshipVerifier \
    --smt "${composed_smt}" \
    --candidates "${relationship_candidates}" \
    --output "${proof_report}" \
    --z3 "${z3_bin}" \
    --timeout-ms "${solver_timeout_ms}" "$@"
}

do_reach() {
  require_file "composed SMT" "${composed_smt}"
  require_file "composition manifest" "${composition_manifest}"
  require_file "symbolic regions" "${static_regions}"
  require_file "relationship candidates" "${relationship_candidates}"
  ensure_output_directory "$(dirname "${reach_report}")"
  run_java_main edu.uva.liftlab.graphchecker.concolic.BooleanReachConditionExtractor \
    --smt "${composed_smt}" \
    --manifest "${composition_manifest}" \
    --regions "${static_regions}" \
    --relationships "${relationship_candidates}" \
    --output "${reach_report}" \
    --z3 "${z3_bin}" \
    --timeout-ms "${solver_timeout_ms}" \
    --max-inputs "${reach_max_inputs}" \
    --max-valuations "${reach_max_valuations}" "$@"
}

do_workload() {
  [[ -n "${workload_command}" ]] || die "workload_command is empty"
  require_directory "workload working" "${workload_work_dir}"
  if [[ "${dry_run}" == true ]]; then
    print_command env \
      "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}" \
      "CAUSYNTH_RPC_MAPPING_FILE=${rpc_mapping_file}" \
      bash -lc "${workload_command}"
  else
    (cd "${workload_work_dir}" && \
      CAUSYNTH_CUSTOM_JDK_HOME="${custom_jdk_home}" \
      CAUSYNTH_RPC_MAPPING_FILE="${rpc_mapping_file}" \
      bash -lc "${workload_command}")
  fi
}

debug_log() {
  printf '[graphchecker-debug] %s\n' "$*" >&2
}

debug_is_enabled() {
  case "${debug_graphs}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    *) return 1 ;;
  esac
}

debug_prepare_limits() {
  case "${debug_max_items}" in
    ''|*[!0-9]*|0) debug_max_items=40 ;;
  esac
  case "${debug_max_bytes}" in
    ''|*[!0-9]*|0) debug_max_bytes=1048576 ;;
  esac
  debug_max_items=$((10#${debug_max_items}))
  debug_max_bytes=$((10#${debug_max_bytes}))
  if (( debug_max_items > 500 )); then debug_max_items=500; fi
  if (( debug_max_bytes > 16777216 )); then debug_max_bytes=16777216; fi
}

debug_file_bytes() {
  local count
  count=$(LC_ALL=C wc -c < "$1")
  printf '%s' "${count//[[:space:]]/}"
}

# JSON artifacts are projected before printing so runtime ids, trace payloads,
# and other large incidental fields do not hide the graph structure.
debug_json_projection() {
  local label=$1
  local path=$2
  local filter=$3
  local bytes rendered
  if [[ ! -r "${path}" ]]; then
    debug_log "artifact=${label} path=${path} status=missing"
    return 0
  fi
  bytes=$(debug_file_bytes "${path}")
  if (( bytes > debug_max_bytes )); then
    debug_log "artifact=${label} path=${path} bytes=${bytes} status=skipped reason=byte-cap cap=${debug_max_bytes}"
    return 0
  fi
  if ! command -v jq >/dev/null 2>&1; then
    debug_log "artifact=${label} path=${path} status=skipped reason=jq-unavailable"
    return 0
  fi
  if ! rendered=$(jq -cS --argjson max "${debug_max_items}" \
      "${filter}" "${path}" 2>/dev/null); then
    debug_log "artifact=${label} path=${path} bytes=${bytes} status=invalid-json"
    return 0
  fi
  debug_log "artifact=${label} path=${path} bytes=${bytes} status=shown"
  [[ -z "${rendered}" ]] || printf '%s\n' "${rendered}" >&2
}

debug_jsonl_projection() {
  local label=$1
  local path=$2
  local filter=$3
  local bytes total shown truncated=false rendered
  if [[ ! -r "${path}" ]]; then
    debug_log "artifact=${label} path=${path} status=missing"
    return 0
  fi
  bytes=$(debug_file_bytes "${path}")
  if (( bytes > debug_max_bytes )); then
    debug_log "artifact=${label} path=${path} bytes=${bytes} status=skipped reason=byte-cap cap=${debug_max_bytes}"
    return 0
  fi
  if ! command -v jq >/dev/null 2>&1; then
    debug_log "artifact=${label} path=${path} status=skipped reason=jq-unavailable"
    return 0
  fi
  total=$(LC_ALL=C awk 'NF { count++ } END { print count + 0 }' "${path}")
  shown=${total}
  if (( shown > debug_max_items )); then
    shown=${debug_max_items}
    truncated=true
  fi
  if ! rendered=$(jq -cS --argjson max "${debug_max_items}" \
      "${filter}" "${path}" 2>/dev/null \
      | LC_ALL=C sort | sed -n "1,${debug_max_items}p"); then
    debug_log "artifact=${label} path=${path} bytes=${bytes} status=invalid-json"
    return 0
  fi
  debug_log "artifact=${label} path=${path} bytes=${bytes} total=${total} shown=${shown} truncated=${truncated}"
  [[ -z "${rendered}" ]] || printf '%s\n' "${rendered}" >&2
}

debug_static_artifacts() {
  local region_edges="$(dirname "${static_regions}")/symbolic_region_edges.jsonl"
  debug_jsonl_projection static_graph "${static_graph}" '
    select(type == "object")
    | {id, kind, transferKind, fromCell, toCell, method, siteId}'
  debug_jsonl_projection symbolic_regions "${static_regions}" '
    select(type == "object")
    | {regionId, anchorMethod, rootMethod, precision, truncated,
       inputCount: ((.symbolicInputs // []) | length),
       inputs: ((.symbolicInputs // []) | sort_by(tojson) | .[:$max]),
       outputCount: ((.outputs // []) | length),
       outputs: ((.outputs // []) | sort_by(tojson) | .[:$max])}'
  debug_jsonl_projection symbolic_region_edges "${region_edges}" '
    select(type == "object")
    | {edgeId, kind, relation, candidateRelation, fromRegion, fromPort,
       toRegion, toPort, requiresOrder, runtimeStatus}'
}

debug_runtime_graph() {
  local label=$1
  local path=$2
  debug_json_projection "${label}" "${path}" '
    def stable_cell:
      if type == "string" then gsub("@methodObject:[0-9-]+"; "@methodObject") else "" end;
    def stable_node:
      {process: (.process // ""),
       threadRole: (.threadRole // .threadName // ""),
       method: (.method // ""), cell: ((.cell // "") | stable_cell)};
    (.nodes // []) as $raw_nodes
    | ($raw_nodes | map({key: (.id | tostring), value: (. | stable_node)})
       | from_entries) as $by_id
    | ($raw_nodes | map(stable_node)
       | sort_by([.process, .threadRole, .method, .cell])) as $nodes
    | ([((.edges // [])[]) as $edge
        | {kind: ($edge.kind // ""),
           staticEdgeId: ($edge.staticEdgeId // ""),
           staticEdgeIds: ($edge.staticEdgeIds // ""),
           from: ($by_id[($edge.from | tostring)] // {cell: ($edge.from // "")}),
           to: ($by_id[($edge.to | tostring)] // {cell: ($edge.to // "")}),
           method: ($edge.method // ""),
           occurrences: ($edge.occurrences // 0),
           mergedInstances: ($edge.mergedInstances // 0)}]
       | sort_by([.kind, .staticEdgeId, (.from | tojson), (.to | tojson)])) as $edges
    | {summary: ((.summary // {})
         | {test, traceEventCount, fieldEventCount, executionEventCount,
            staticEdgeCount, instantiatedNodeCount, instantiatedEdgeCount,
            roleMergedNodeCount, roleMergedEdgeCount, truncated, roleTruncated}),
       nodes: {total: ($nodes | length),
               shown: ([($nodes[:$max])[]] | length),
               truncated: (($nodes | length) > $max), items: $nodes[:$max]},
       edges: {total: ($edges | length),
               shown: ([($edges[:$max])[]] | length),
               truncated: (($edges | length) > $max), items: $edges[:$max]}}'
}

debug_runtime_artifacts() {
  local runtime_dir
  runtime_dir=$(dirname "${runtime_activation_plan}")
  debug_runtime_graph runtime_instantiated_graph \
    "${runtime_dir}/unit_test_instantiated_graph.json"
  debug_runtime_graph runtime_role_merged_graph \
    "${runtime_dir}/unit_test_role_merged_graph.json"
}

debug_schedule_artifacts() {
  debug_json_projection symbolic_merge_plan "${symbolic_merge_plan}" '
    def relation:
      {edgeId, kind, transportKind, fromRegion, toRegion, fromEndpoint,
       toEndpoint, runtimeStatus,
       runtimeBindingCount: ((.runtimeBindings // []) | length),
       requiresOrder, requiresObjectIdentity, confirmedReadFromPairCount};
    (.equalityClasses // []) as $classes
    | (.equalityRelations // []) as $equalities
    | (.versionedStateMerges // []) as $states
    | (.alternativeWriterGroups // []) as $groups
    | {counts: {equalityClasses: ($classes | length),
                equalityRelations: ($equalities | length),
                versionedStateMerges: ($states | length),
                alternativeWriterGroups: ($groups | length)},
       equalityClasses: ($classes
         | map({canonicalSymbol, members: ((.members // []) | sort)})
         | sort_by([(.members | join("\u0000")), .canonicalSymbol]) | .[:$max]),
       equalityRelations: ($equalities | map(relation)
         | sort_by([.fromEndpoint, .toEndpoint, .edgeId]) | .[:$max]),
       versionedStateMerges: ($states | map(relation)
         | sort_by([.fromEndpoint, .toEndpoint, .edgeId]) | .[:$max]),
       alternativeWriterGroups: ($groups | map(. as $group
         | {groupId: $group.groupId, kind: $group.kind,
            downstreamEndpoint: $group.downstreamEndpoint,
            selectionSemantics: $group.selectionSemantics,
            alternativeCount: (($group.alternatives // []) | length),
            alternatives: (($group.alternatives // [])
              | map(. as $alternative
                | ($alternative | relation)
                  + {guardSymbol: ($alternative.guardSymbol // "")})
              | sort_by([.fromEndpoint, .toEndpoint, .edgeId]) | .[:$max])})
         | sort_by([.downstreamEndpoint, .groupId]) | .[:$max])}'
}

debug_merge_artifacts() {
  debug_jsonl_projection guarded_merge "${merged_summaries}" '
    def capped_object:
      if type == "object" then to_entries | sort_by(.key) | .[:$max] | from_entries
      else {} end;
    select(type == "object")
    | (.regionRelation // {}) as $relation
    | {regionId,
       requestedOutput: ((.requestedOutput // {}) | {portId, cell, kind}),
       relation: {kind: ($relation.kind // ""),
         complete: ($relation.complete // false),
         caseCount: ($relation.caseCount // (($relation.cases // []) | length)),
         shownCaseCount: ([($relation.cases // [])[:$max][]] | length),
         cases: (($relation.cases // [])
           | map(. as $case
             | {caseId: ($case.caseId // ""), pathKey: ($case.pathKey // ""),
                symbolScope: ($case.symbolScope // ""),
                guard: (($case.guard // {})
                  | {kind: (.kind // ""),
                     conditionCount: ((.conditions // []) | length),
                     conditions: ((.conditions // [])[:$max])}),
                outputExpressionCount: (($case.outputExpressions // {}) | length),
                outputExpressions: (($case.outputExpressions // {}) | capped_object),
                heapEffectCount: (($case.heapEffects // []) | length),
                heapEffects: (($case.heapEffects // [])[:$max]),
                relationallyComplete: ($case.relationallyComplete // false),
                normalExit: ($case.normalExit // false),
                exceptionType: ($case.exceptionType // "")})
           | sort_by([.caseId, .pathKey]) | .[:$max])}}'
}

debug_compose_artifacts() {
  debug_json_projection composition_manifest "${composition_manifest}" '
    {schemaVersion, kind, complete, status, fatalRegion, fatalActivationId,
     fatalConditionCount, summaryCount, guardedCaseCount,
     symbolicEqualityCount, versionedStateMergeCount}'
  local path=${composed_smt}
  local bytes lines truncated=false rendered
  if [[ ! -r "${path}" ]]; then
    debug_log "artifact=final_smt path=${path} status=missing"
    return 0
  fi
  bytes=$(debug_file_bytes "${path}")
  lines=$(LC_ALL=C awk 'END { print NR + 0 }' "${path}")
  if (( bytes > debug_max_bytes || lines > debug_max_items )); then
    truncated=true
  fi
  rendered=$(LC_ALL=C awk -v max_lines="${debug_max_items}" \
      -v max_bytes="${debug_max_bytes}" '
    BEGIN { used = 0 }
    NR > max_lines { exit }
    {
      line = $0 "\n"
      remaining = max_bytes - used
      if (remaining <= 0) exit
      if (length(line) > remaining) {
        printf "%s", substr(line, 1, remaining)
        exit
      }
      printf "%s", line
      used += length(line)
    }' "${path}")
  debug_log "artifact=final_smt path=${path} bytes=${bytes} lines=${lines} truncated=${truncated} lineCap=${debug_max_items} byteCap=${debug_max_bytes}"
  [[ -z "${rendered}" ]] || printf '%s\n' "${rendered}" >&2
}

debug_workflow_stage() {
  local stage=$1
  debug_is_enabled || return 0
  if [[ "${dry_run}" == true ]]; then
    debug_log "stage=${stage} status=skipped reason=dry-run"
    return 0
  fi
  debug_prepare_limits
  debug_log "stage=${stage} status=begin maxItems=${debug_max_items} maxBytes=${debug_max_bytes}"
  case "${stage}" in
    analyze) debug_static_artifacts ;;
    workload) debug_runtime_artifacts ;;
    schedule) debug_schedule_artifacts ;;
    merge) debug_merge_artifacts ;;
    compose) debug_compose_artifacts ;;
  esac
  debug_log "stage=${stage} status=end"
}

debug_after_stage() {
  debug_workflow_stage "$1" \
    || debug_log "stage=$1 status=formatter-error (workflow result preserved)"
}

# Keep the original process/transform contract intact for the HDFS adapter.
# New workflows should use `--config FILE analyze` so all paths are normalized.
legacy_process() {
  local requested=${1:-}
  [[ -n "${requested}" ]] || die "process requires a config file argument"
  [[ -f "${requested}" ]] || die "config file not found: ${requested}"
  local legacy_config_dir
  legacy_config_dir=$(cd "$(dirname "${requested}")" && pwd -P)
  local legacy_config="${legacy_config_dir}/$(basename "${requested}")"
  # shellcheck disable=SC1090
  source "${legacy_config}"
  local legacy_jar=${GRAPH_CHECKER_JAR:-${graphchecker_jar:-${default_graphchecker_jar}}}
  local legacy_java=${GRAPH_CHECKER_JAVA:-${java_bin:-java}}
  local legacy_work=${GRAPH_CHECKER_WORK_DIR:-${graphchecker_work_dir:-${graphchecker_dir}}}
  [[ "${legacy_jar}" == /* ]] || legacy_jar="${legacy_config_dir}/${legacy_jar}"
  if [[ "${legacy_java}" == */* && "${legacy_java}" != /* ]]; then
    legacy_java="${legacy_config_dir}/${legacy_java}"
  fi
  [[ "${legacy_work}" == /* ]] || legacy_work="${legacy_config_dir}/${legacy_work}"
  require_file "GraphChecker jar" "${legacy_jar}"
  require_directory "system classes" "${system_classes_path}"
  require_directory "working" "${legacy_work}"
  run_in_directory "${legacy_work}" "${legacy_java}" \
    -cp "${legacy_jar}:${java_class_path}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${system_classes_path}" \
    -x "${java_class_path}" \
    -C "${legacy_config}" \
    -o "${system_classes_path}"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --config)
      [[ $# -ge 2 ]] || die "--config requires a file"
      config_file=$2
      shift 2
      ;;
    --dry-run)
      dry_run=true
      shift
      ;;
    --debug)
      debug_graphs=true
      shift
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
  process|transform)
    if [[ -n "${config_file}" ]]; then
      initialize_config "${config_file}"
      require_config analyze
      do_analyze "$@"
      debug_after_stage analyze
    else
      legacy_process "${1:-}"
    fi
    ;;
  build)
    initialize_config "${config_file}"
    do_build "$@"
    ;;
  analyze|schedule|import|merge|compose|solve|reach|workload|config|validate)
    [[ -n "${config_file}" ]] || die "${command_name} requires --config FILE"
    initialize_config "${config_file}"
    case "${command_name}" in
      analyze) do_analyze "$@"; debug_after_stage analyze ;;
      schedule) do_schedule "$@"; debug_after_stage schedule ;;
      import) do_import "$@" ;;
      merge) do_merge "$@"; debug_after_stage merge ;;
      compose) do_compose "$@"; debug_after_stage compose ;;
      solve) do_solve "$@" ;;
      reach) do_reach "$@" ;;
      workload) do_workload "$@"; debug_after_stage workload ;;
      config) print_normalized_config ;;
      validate) validate_config ;;
    esac
    ;;
  debug-stage)
    [[ -n "${config_file}" ]] || die "debug-stage requires --config FILE"
    [[ $# -eq 1 ]] || die "debug-stage requires exactly one stage"
    case "$1" in
      analyze|workload|schedule|merge|compose) ;;
      *) die "unsupported debug stage '$1'" ;;
    esac
    initialize_config "${config_file}"
    debug_graphs=true
    debug_after_stage "$1"
    ;;
  *)
    die "unknown command '${command_name}' (run './run_engine.sh help')"
    ;;
esac
