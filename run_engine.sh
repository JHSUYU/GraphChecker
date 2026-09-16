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
  # The stage a measurement run stops after, once its measurement is
  # complete.  `IMPORT` returns successfully right after the IMPORT stage of
  # the current epoch: the seed session and its per-kind row census are what a
  # runtime change is gated on, and running EXPLORE..EMIT to reach them costs
  # hours and answers a different question.  Empty -- the default -- runs the
  # whole campaign, so an unconfigured workload is unaffected.  Only these two
  # values exist; validate_config refuses any other, because a misspelling
  # would silently run the full campaign and look like a measurement run that
  # never stopped.
  "campaign_stop_after CAUSYNTH_CAMPAIGN_STOP_AFTER krp -"
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
  "causynth_process_dirs CAUSYNTH_PROCESS_DIRS krp -"
  "causynth_communication_mappings CAUSYNTH_COMMUNICATION_MAPPINGS krp -"
  "causynth_loop_bounds CAUSYNTH_LOOP_BOUNDS krp -"
  # The backedge ceiling a retained loop the case did not narrow runs under.
  # It used to be a constant in LoopBoundPolicy, applied silently to 54 of
  # hdfs-17960's retained loops, which README LOOP-1 forbids a retained
  # condition loop doing.  The case states it; every inherited application is
  # still published as the catalog's DIAGNOSTIC gap row (INHERITED_K_L_<n>).
  # No default here: a campaign that states none is refused by name.
  "causynth_loop_default_bound CAUSYNTH_LOOP_DEFAULT_BOUND krp -"
  "causynth_symbolic_inputs CAUSYNTH_SYMBOLIC_INPUTS krp -"
  # CLOSURE-V2 SS4: the epoch's static scope map (write sites, export
  # sites, guard sets).  Two stages read it and both must read the SAME
  # file: the workload JVM installs the guard sites it names, and EXPLORE
  # flips at them.  Defaults beside the other discovery artifacts.
  "causynth_static_scope_map CAUSYNTH_STATIC_SCOPE_MAP krp -"
  # The epoch's selected region skeletons.  Two weaves read it and both must
  # read the SAME file: the recording opens an execution-index region at
  # every root it names, and the concolic weave opens one at every root the
  # campaign did not select, so the frame stack a replay stands on is the
  # frame stack the recording stood on.  Written by the skeleton pass,
  # beside the other discovery artifacts.
  "causynth_region_skeletons CAUSYNTH_REGION_SKELETONS krp -"
  # What the case says its declared roots may be, beside what the recording
  # read: one row per source id, with declaredDomainMin/Max absolute or
  # written +k / -k from the recorded value.  A root with no row stays pinned
  # to its recording, which is what a case that claims nothing about it says.
  "causynth_root_domains CAUSYNTH_ROOT_DOMAINS krp -"
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
  "schedule_closure_mode - r candidate"
  # Regions a previous epoch's TOPOLOGY_DIVERGENCE said the retained set must
  # grow to include.  Internal campaign state: it is derived from the epoch
  # that diverged, never configured.
  "schedule_retain_regions - r -"
  "schedule_max_jobs CAUSYNTH_SCHEDULE_MAX_JOBS krp -"
  # Per solver run, in milliseconds.  The composer runs z3 once per
  # valuation while it composes, so this is the budget of one of those runs.
  "solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS krp -"
  # How many root valuations the composer enumerates around the recorded one.
  # The composer runs z3 per valuation while it composes, so this bounds the
  # solving a campaign does, not a separate stage's budget.
  "compose_max_valuations CAUSYNTH_COMPOSE_MAX_VALUATIONS krp 16"
  # The occurrence of the annotated site this campaign is about, as the case
  # declares it: an occurrence address.  A campaign is target-directed -- the
  # case knows which instance can fail -- and the declaration is what says
  # so; it is the anchor COMPOSE composes and the claim DECIDE publishes.
  "declared_target_occurrence CAUSYNTH_TARGET_OCCURRENCE krp -"
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

# Workflow configs deliberately use a small key=value grammar, and only the
# keys workflow_config_keys carries.  A key outside it is refused by name, so
# a target config can neither change PATH, HOME, IFS or a shell control
# variable nor ship a setting nothing reads.
load_config_file() {
  local path=$1
  local raw key value
  while IFS= read -r raw || [[ -n "${raw}" ]]; do
    raw=$(trim "${raw}")
    [[ -z "${raw}" || "${raw}" == \#* ]] && continue
    [[ "${raw}" == *=* ]] || continue
    key=$(trim "${raw%%=*}")
    value=$(trim "${raw#*=}")
    # A key this table does not carry is a refusal, not a comment.  It used to
    # be skipped, so a misspelling -- or a key a stage deletion retired --
    # stayed in a shipped config and read as a setting that did nothing:
    # `reach_max_inputs`, `reach_max_valuations` and `causynth_analysis_scope`
    # all shipped that way in all four case configs.
    known_config_key "${key}" \
      || die "unknown workflow config key in ${path}: ${key}"
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
  if [[ -n "${causynth_root_domains}" ]]; then
    causynth_root_domains=$(resolve_path "${causynth_root_domains}")
  fi
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    causynth_symbolic_inputs=$(resolve_path "${causynth_symbolic_inputs}")
  fi
  causynth_static_scope_map=${causynth_static_scope_map:-${causynth_output_dir}/static_scope_map.jsonl}
  causynth_static_scope_map=$(resolve_path "${causynth_static_scope_map}")
  causynth_region_skeletons=${causynth_region_skeletons:-${causynth_output_dir}/runtime/skeleton-pass/region_skeletons.jsonl}
  causynth_region_skeletons=$(resolve_path "${causynth_region_skeletons}")
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
    "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
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
  for key in project_repo project_module_dir project_classes_dir project_classpath causynth_output_dir causynth_cache_dir causynth_target_spec custom_jdk_home z3_bin workload_command trace_test causynth_loop_bounds causynth_loop_default_bound; do
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
  if [[ -n "${causynth_root_domains}" ]]; then
    require_file "declared root domains" "${causynth_root_domains}"
  fi
  # The bounds a campaign may not inherit. Left unstated, each would reach its
  # stage as a bare flag and be read back as some default the artifacts never
  # name -- a truncated schedule, an unbounded solve -- so a run without them
  # does not start.
  local key
  for key in solver_timeout_ms schedule_max_jobs \
      concolic_worker_count campaign_max_iterations \
      region_path_max_waves compose_max_valuations \
      campaign_max_epochs causynth_loop_default_bound; do
    require_positive_integer "${key}"
  done
  # The one stage a campaign may be asked to stop after.  Refused here rather
  # than in do_campaign so that `validate` and PREFLIGHT both name it before
  # any work starts: a value this table does not carry would otherwise match
  # nothing, run the whole campaign, and be read back as a measurement run
  # that never stopped.
  case "${campaign_stop_after}" in
    ''|IMPORT) ;;
    *) die "campaign_stop_after must be empty or IMPORT: \
${campaign_stop_after}" ;;
  esac
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
  if [[ -n "${causynth_process_dirs}" ]]; then
    system_properties+=("-Dcausynth.process.dirs=${causynth_process_dirs}")
  fi
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
    system_properties+=(
      "-Dcausynth.communication.mappings=${causynth_communication_mappings}"
    )
  fi
  # Roots are manual, so the case's declaration is an input to P1 and not
  # only to PLAN: the static slice holds every declared method, the skeleton
  # weave roots a region at it, and both passes weave it. Named on the same
  # condition do_schedule passes --symbolic-inputs, so the two stages cannot
  # be planned against different declarations.
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
    system_properties+=(
      "-Dcausynth.symbolic.inputs=${causynth_symbolic_inputs}"
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
    "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}"
  )
  if [[ -n "${CAUSYNTH_TRACE_MODE:-}" ]]; then
    system_properties+=(
      "-Dcausynth.trace.mode=${CAUSYNTH_TRACE_MODE}"
    )
  fi
  # One key, every weave.  The region-state pass and the concolic pass both
  # open their regions from this file; a pass that read a different one (or
  # none) would stand on a different frame stack and address a different
  # occurrence for the same event.  The environment may still name it for a
  # one-off run, and the key is the default.
  system_properties+=(
    "-Dcausynth.region.skeletons=${CAUSYNTH_REGION_SKELETONS:-${causynth_region_skeletons}}"
  )
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
    -o "${analysis_classes_dir}"
}

# The occurrence of the annotated site the case declares.  It is a config
# key rather than a member of the target spec because the spec accepts one
# entry and three cases share one file: hdfs-17899's per-bug selection lives
# in case.sh, which exports it, and a single-case experiment states it in its
# own workflow.properties.
campaign_declared_target_occurrence() {
  printf '%s\n' "${declared_target_occurrence}"
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
  # PLAN reads the STATIC candidate graph, for one thing: the exact-copy
  # relation a declaration is renamed over, which Soot proved and stamped on
  # those rows.  It used to read the runtime-refined graph; the other three
  # things it took from there are static facts of the candidate graph or of
  # the static scope map, and are read from the map now.
  require_file "candidate data-flow graph" "${candidate_graph}"
  args+=(--candidate-graph "${candidate_graph}")
  # The one guard authority's publication: the scheduler reads the fatal arm
  # of the declared target branch off the TARGET_SITE row rather than
  # re-deriving a polarity from the graph.
  require_file "static scope map" "${causynth_static_scope_map}"
  args+=(--static-scope-map "${causynth_static_scope_map}")
  # validate_config refuses an unstated cap: left to the scheduler's own
  # fallback of one job it would keep the first candidate of the plan and drop
  # the rest, and a schedule of one task is not an empty schedule, so the
  # stage would exit 0 with the truncation invisible.
  args+=(--max-jobs "${schedule_max_jobs}")
  if [[ -n "${causynth_symbolic_inputs}" ]]; then
    require_file "symbolic input selection" "${causynth_symbolic_inputs}"
    args+=(--symbolic-inputs "${causynth_symbolic_inputs}")
  fi
  args+=(--closure-mode "${schedule_closure_mode}")
  # The regions a previous epoch's divergence said this plan must name, so
  # that INSTRUMENT -- which instruments the regions the plan names --
  # instruments them before this epoch replays.
  [[ -z "${schedule_retain_regions}" ]] \
    || args+=(--retain-regions "${schedule_retain_regions}")
  [[ -z "${declared_target_occurrence}" ]] \
    || args+=(--target-occurrence "${declared_target_occurrence}")
  run_java_main edu.uva.liftlab.graphchecker.plan.ConcolicScheduler \
    "${args[@]}"
}

do_compose() {
  ensure_output_directory "$(dirname "${composed_smt}")"
  local -a selection=()
  local declared
  declared=$(campaign_declared_target_occurrence)
  [[ -z "${declared}" ]] || selection+=(--anchor "${declared}")
  [[ -z "${causynth_root_domains}" ]] \
    || selection+=(--root-domains "${causynth_root_domains}")
  run_java_main edu.uva.liftlab.graphchecker.compose.ComposeMain \
    --sessions "${compose_sessions_dir}" \
    --output "${composed_smt}" \
    --manifest "${composition_manifest}" \
    --solver-timeout-ms "${solver_timeout_ms}" \
    --max-valuations "${compose_max_valuations}" \
    --z3 "${z3_bin}" \
    "${selection[@]}"
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
  # The gaps pass 1 stated; the state pass files them with its own, so an
  # absent artifact is a plan with a silently short gap list.
  require_file "pass-1 recording gaps" "${skeleton_pass}/recording_gaps.jsonl"

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
    require_file "static scope map" "${causynth_static_scope_map}"
    run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
      --trace-dir "${trace_dir}" \
      --candidate-graph "${candidate_graph}" \
      --region-skeletons "${selected_skeletons}" \
      --static-scope-map "${causynth_static_scope_map}" \
      --refined-graph "${refined_graph}" \
      --recording-gaps "${trace_dir}/skeleton-pass/recording_gaps.jsonl" \
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
# This iteration's task-set membership, decoded once by PLAN from the frozen
# schedule index (README "Minimal cross-stage contract": one owner per check).
# IMPORT, EXPLORE, the iteration manifest and COMPOSE read these rows; they do
# not re-decode the index, because re-deriving the same membership at five
# stages is five chances to disagree about one frozen file that is written
# once and never rewritten.
campaign_member_rows=""
# One row per observed occurrence of the annotated target: what COMPOSE
# composed for it, what SOLVE concluded from that, and what DECIDE elected.
# COMPOSE writes the rows, SOLVE rewrites them with its own artifact, DECIDE
# turns them into the published ledger and EMIT copies that ledger into the
# result.

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

# A count a campaign DECIDES on, read back from an artifact.
#
# `[[ "${n}" -eq 0 ]]` is true for an empty string: bash evaluates the word as
# an arithmetic expression and an empty one is zero.  So every gate of the
# shape "no blocking gaps, carry on" passed whenever the count could not be
# read at all -- a jq that printed nothing because the key was absent, a
# summary file the stage wrote no JSON into, a jq that failed -- and the gate
# that exists to stop the campaign let it through with the artifact it was
# reading unreadable.  A count is a decision: an unreadable one is a refusal
# naming the artifact, never a zero.
#
# `-eq` is also happy with `1+1`, `x` and `9 -o 1` (bash arithmetic evaluates
# the word and an unset name is 0), so the test is the spelling of a count and
# not just "non-empty".
# It CHECKS rather than returns the value: campaign_fail ends the run with
# `exit`, and a helper that answered through a command substitution would end
# only that substitution, leaving the caller with the empty string this rule
# exists to refuse.
campaign_count() {
  local stage=$1 component=$2 artifact=$3 label=$4 value=$5
  case "${value}" in
    ''|*[!0-9]*)
      campaign_fail "${stage}" "${component}" "${artifact}" \
        "${label} is not a count: '${value}'" ;;
  esac
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

# The claim belongs to ClaimPolicy, so a manifest whose solver block carries
# none is a manifest this stage may not publish a result from: falling back to
# a shell verdict here is exactly the second gate this change removed.
campaign_require_claim() {
  local path=$1
  jq -e '.solver as $r
    | ($r.campaignClaim | type) == "object"
    and (($r.campaignClaim.claim // "")
      | IN("SAT_CANDIDATE", "UNSAT_CLOSED", "INCONCLUSIVE_PARTIAL"))
    and ($r.campaignClaim.blockers | type) == "array"
    and ($r.campaignClaim.blockerCount | type) == "number"
    and ($r.campaignClaim.claimReason | type) == "string"
    and ($r.campaignClaim.whyNotAccepted | type) == "string"
    and (($r.campaignClaim.findingKind // "")
      | IN("MARKER_FLIPPED", "CLOCK_SKEW", "MESSAGE_PAIRING_FLIPPED",
           "STATE_PAIRING_FLIPPED", "RECORDED_FAILURE_EXPLAINED",
           "NO_SUPPORTED_WITNESS"))
    and ($r.campaignClaim.polarityDecides | type) == "boolean"' \
    "${path}" >/dev/null \
    || campaign_fail EMIT ClaimPolicy "${path}" \
      "the composition manifest published no ClaimPolicy decision"
}

# Prints every explicit symbolic root without exposing internal SMT terms.
# Configured source fields and planned manual symbolizations share this model
# contract; a missing propagation source is reported as a gap, never minted as
# another input here.
campaign_print_symbolic_variable_models() {
  local report=$1 model_count
  campaign_require_json "composition manifest" "${report}" \
    || return 1
  jq -e '.solver as $r
    | ($r.symbolicVariableModels | type) == "array"
    and all($r.symbolicVariableModels[];
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
  model_count=$(jq -r '.solver.symbolicVariableModels | length' "${report}")
  campaign_count SOLVE SymbolicModels "${report}" \
    "the solver's model count" "${model_count}"
  if [[ "${model_count}" -eq 0 ]]; then
    campaign_log "symbolic variables: no satisfying model"
    return 0
  fi
  while IFS=$'\t' read -r valuation kind source variable phase field value nullness; do
    campaign_log "symbolic valuation=${valuation} kind=${kind} source=${source} variable=${variable} phase=${phase} field=${field} value=${value}${nullness:+ nullness=${nullness}}"
  done < <(jq -r '
    .solver.symbolicVariableModels[] as $model
    | $model.variables[]
    | [$model.valuationOrdinal, .inputKind,
       (.sourceKey // .occurrenceId), (.sourceId // .portId),
       (.sourcePhaseId // ""),
       .fieldSignature, (.value | tostring),
       (.nullnessValue // "" | tostring)]
    | @tsv
  ' "${report}")
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

# The static discovery and both trace-index passes are one seed boundary.  We
# cache their published artifacts, not RuntimeRegionPlanner's private in-memory
# index, so cache reuse adds no second semantic schema.
campaign_seed_artifact_rows() {
  # Every published artifact of the seed boundary, and only published ones:
  # target_resolved.json, communication_call_sites.jsonl.gz and
  # retained_loops.jsonl.gz are gone because nothing read their content, and
  # the static scope map is here because a cache HIT skips do_analyze -- so
  # without it PLAN and EXPLORE were handed a file that did not exist, which
  # StaticScopeMap.read answers as "this epoch published no map".
  printf '%s\t%s\n' \
    candidateGraph "${candidate_graph}" \
    runtimePlan "${runtime_region_plan}" \
    refinedGraph "${refined_graph}" \
    regionSkeletons "${causynth_output_dir}/region_skeletons.jsonl.gz" \
    staticScopeMap "${causynth_static_scope_map}" \
    communicationGaps \
      "${causynth_output_dir}/communication_gaps.jsonl.gz" \
    selectedSkeletons \
      "$(dirname "${runtime_region_plan}")/skeleton-pass/region_skeletons.jsonl"
}

campaign_seed_cache_key() {
  local identity config_seed_sha
  config_seed_sha=$(campaign_digest "${config_file}")
  identity=$(jq -S -c \
    --arg processDirs "${causynth_process_dirs}" \
    --arg workloadWorkDir "${workload_work_dir}" \
    --arg workloadCommand "${workload_command}" \
    --arg traceTest "${trace_test}" \
    --arg configSeedSha "${config_seed_sha}" '
    # The jar digest is NOT an input: a fat jar is not reproducible (its
    # entries carry build timestamps), so keying on it made every rebuild a
    # cache miss even when nothing about the tool had changed.  What the jar
    # is built FROM is in the key as graphCheckerSource -- the checkout head,
    # the branch, and a digest of every file `git status --porcelain` names,
    # tracked or not -- so the tool is identified exactly and stably.
    {schemaVersion: 5, kind: "CAMPAIGN_SEED_CACHE_KEY",
     inputs: {
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
    || campaign_fail SEED CAMPAIGN "${entry}" \
      "the content-addressed seed cache entry is incomplete"
  jq -e --arg key "${key}" '
    .schemaVersion == 1
    and .kind == "CAMPAIGN_SEED_CACHE_ENTRY"
    and .key == $key
    and (.artifacts | type) == "object"
  ' "${manifest}" >/dev/null \
    || campaign_fail SEED CAMPAIGN "${manifest}" \
      "the seed cache manifest has an unsupported schema"
  while IFS=$'\t' read -r name destination; do
    count=$((count + 1))
    [[ -f "${entry}/${name}" ]] \
      || campaign_fail SEED CAMPAIGN "${entry}/${name}" \
        "the seed cache artifact is missing"
    expected=$(jq -r --arg name "${name}" \
      '.artifacts[$name].sha256 // ""' "${manifest}")
    [[ ${#expected} -eq 64 ]] \
      || campaign_fail SEED CAMPAIGN "${manifest}" \
        "the seed cache manifest omits ${name}"
    actual=$(campaign_digest "${entry}/${name}")
    [[ "${actual}" == "${expected}" ]] \
      || campaign_fail SEED CAMPAIGN "${entry}/${name}" \
        "the seed cache artifact digest does not match its manifest"
    mkdir -p "$(dirname "${destination}")"
    cp -- "${entry}/${name}" "${destination}"
  done < <(campaign_seed_artifact_rows)
  [[ "${count}" -eq 9 ]] || campaign_fail SEED CAMPAIGN "${manifest}" \
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

# The scheduler index is the only campaign membership authority.  Decode the
# complete schema in one checked jq operation.  The seven fields are emitted
# as TSV only after their types, non-blank identities, and task-set
# disjointness have been proved. The target and all causal predecessors are
# peers in one linked region-path bundle, and the seventh field says which of
# those peers carry a goal that captures target reach.
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
      and (.taskId | scalar_id)
      and (.targetReachGoal | type == "boolean");
    if length != 1 then
      error("schedule index must contain exactly one JSON document")
    else .[0] end
    # ConcolicScheduler owns the index schema, its constants and its task
    # identities. What is checked here is what this shell then does with the
    # rows: it emits them as TSV, it dispatches on the one TARGET, and it
    # composes one query per member whose goal captures target reach. The
    # elected TARGET is one of those members by construction; an index that
    # says otherwise is an index this shell cannot dispatch on.
    | if ((.members | type == "array" and length > 0)
        and all(.members[];
          member and ((.role == "TARGET") or (.role == "DEPENDENCY")))
        and ([.members[] | select(.role == "TARGET")] | length == 1)
        and all(.members[]; select(.role == "TARGET") | .targetReachGoal))
    then
      # targetReachGoal is VALIDATED above -- the elected TARGET must have
      # it -- and not emitted: no consumer of these rows reads it, and the
      # column leaked into the global scope through two `read -r` lists that
      # never declared it.
      .members[]
      | [.role, .campaignId, .regionId, .occurrenceId, .goalId, .taskId]
      | @tsv
    else error("invalid runtime region-path schedule index") end
  ' "${index}"
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
            taskIds: [.members[].taskId],
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

campaign_wait_workers() {
  local pid status=0
  for pid in "$@"; do
    wait "${pid}" || status=1
  done
  return "${status}"
}

campaign_preflight() {
  validate_config >/dev/null
  [[ -n "${concolic_replay_command}" ]] || die \
    "campaign requires concolic_replay_command: the workload adapter that replays one immutable task plan under the concolic VM"
  require_command_available jq
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
  local iteration_dir=$1 retain=${2:-}
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local seed_dir="${iteration_dir}/seed-replay"
  local seed_plan="${seed_dir}/execution_task_plan.jsonl"
  local seed_index="${seed_dir}/runtime_workflow_schedule_index.json"
  local frozen="${iteration_dir}/concolic_region_plan.jsonl"
  local role campaign_id region occurrence goal task worker
  local region_hash region_size

  require_nonempty "runtime region plan" "${runtime_region_plan}"
  require_nonempty "runtime-refined data-flow graph" "${refined_graph}"
  cp -f "${runtime_region_plan}" "${frozen}"
  schedule_output_dir="${iteration_dir}"
  schedule_retain_regions="${retain}"
  do_schedule
  # Every later consumer reads this iteration's frozen copy, never the mutable
  # discovery output.
  runtime_region_plan="${frozen}"
  require_nonempty "campaign task plan" "${plan}"
  require_nonempty "runtime workflow schedule index" "${index}"

  region_hash=$(campaign_digest "${frozen}")
  region_size=$(stat -c '%s' "${frozen}")
  # The copy above is the only fact about this index the shell owns: the
  # scheduler read the discovery output, and every later stage reads the
  # frozen copy, so the two must be the same bytes. The index's own
  # executionTaskPlan identity is written and re-verified against the file by
  # ConcolicScheduler in the process that wrote both, and the target and
  # member schema is decoded once below; neither is restated here.
  jq -e --arg region_hash "${region_hash}" \
    --argjson region_size "${region_size}" '
      .regionPlan.sha256 == $region_hash
        and .regionPlan.sizeBytes == $region_size
    ' "${index}" >/dev/null \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index does not commit the frozen region plan"

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
  [[ -n "${ids}" ]] || campaign_fail INSTRUMENT CAMPAIGN "${plan}" \
    "the campaign plan published no task id"
  analysis_classes_dir="${classes}"
  export CAUSYNTH_CONCOLIC_TASK_PLAN="${plan}"
  export CAUSYNTH_CONCOLIC_TASK_ID="${ids}"
  do_analyze
  unset CAUSYNTH_CONCOLIC_TASK_PLAN CAUSYNTH_CONCOLIC_TASK_ID
  [[ -n "$(find "${classes}" -name '*.class' -print -quit 2>/dev/null)" ]] \
    || campaign_fail INSTRUMENT CAMPAIGN "${classes}" \
      "union instrumentation wrote no class file"
  campaign_verify_woven_classes "${iteration_dir}"
}

# The JVM verifier is the authority on whether woven bytecode is executable,
# and INSTRUMENT is the stage that asks it.  Asked for the first time inside a
# replay instead, its answer arrives as a VerifyError hours into the campaign
# at a method the campaign never mentions: 9d2761c17's seed replay died on
# woven FSNamesystem.allowSnapshot @142 "Local index 2 is invalid" before any
# region ran, and REPLAY reported a failed workload method.  The class loader
# is the replay's own layout -- execute.sh composes ${classes}:${jar}:${cp} --
# so a class that links here links there.
campaign_verify_woven_classes() {
  local iteration_dir=$1
  local classes="${iteration_dir}/instrumented-classes"
  local report="${iteration_dir}/woven_class_verification.log"
  local status=0
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.causynth.VerifyWovenClasses \
    "${classes}" "${project_classpath}" >"${report}"
  [[ "${status}" -eq 0 ]] || campaign_fail INSTRUMENT VerifyWovenClasses \
    "${report}" "$(grep -m 1 -E \
      '^(UNVERIFIABLE|VERIFY_WOVEN_CLASSES_REFUSED)' "${report}" \
      || echo 'the verifier gate failed without naming a class')"
  campaign_log "$(head -n 1 "${report}")"
}

# One fresh workload instance, through the configured adapter. The adapter owns
# how the workload starts; the campaign owns which immutable plan it replays
# and where its evidence lands.
#
# The concolic pass rewrites only the methods this plan selected, so the union
# tree holds those owners and nothing else. The replay classpath is therefore
# that tree in front of the project's own classes: a replay given the tree
# alone loads no workload class it did not rewrite.
# $7 says what an all-skipped result means to this caller. A seed replay is
# the iteration's only source of observed cases, so "required" (the default)
# makes REPLAY fail closed on one. A flip worker may legitimately replay a
# model the workload never realized, and campaign_obligation_worker already records
# that as REPLAY_NOT_ADMITTED, so it passes "tolerated" and keeps that
# recorded outcome instead of ending the campaign.
campaign_replay() {
  local role=$1 plan=$2 ids=$3 classes=$4 results=$5 worker=$6
  local region_results=${7:-required}
  local status=0
  # Where this replay writes its per-kind rows.  A focused replay is a
  # session: every row it publishes is keyed by it, and every later stage
  # reads the session rather than a folded result.
  local sessions="${campaign_sessions_dir:-$(dirname "${results}")/sessions}"
  mkdir -p "${sessions}"
  require_nonempty "concolic execution task plan" "${plan}"
  [[ ! -e "${worker}/replay.log" ]] || die \
    "replay output already exists; worker directories are written once: ${worker}"
  mkdir -p "${worker}" "$(dirname "${results}")"
  # Every task in one workload JVM shares one propagation ledger, and the plan
  # names it: ConcolicScheduler stamps the seed replay's tasks and
  # PathReplayTaskFactory stamps every focused flip replay's, both as
  # REPLAY.GROUP.<sha256>. One authority mints it, so nothing is derived or
  # cross-checked here.
  run_capturing_status \
    campaign_run_adapter "replay(${role})" "${concolic_replay_command}" \
    "CAUSYNTH_CONCOLIC_ROLE=${role}" \
    "CAUSYNTH_CONCOLIC_TASK_PLAN=${plan}" \
    "CAUSYNTH_CONCOLIC_TASK_ID=${ids}" \
    "CAUSYNTH_CONCOLIC_RESULTS=${results}" \
    "CAUSYNTH_CONCOLIC_SESSIONS=${sessions}" \
    "CAUSYNTH_CONCOLIC_CLASSES=${classes}" \
    "CAUSYNTH_CONCOLIC_WORKER_DIR=${worker}" \
    "CAUSYNTH_CONCOLIC_MAX_TASKS=${schedule_max_jobs}" \
    "CAUSYNTH_TRACE_TEST=${trace_test}" \
    "CAUSYNTH_TRACE_MODE=replay-context" \
    "CAUSYNTH_STATIC_SCOPE_MAP=${causynth_static_scope_map}" \
    >"${worker}/replay.log" 2>&1
  # A workload whose target branch throws exits nonzero by design, so the gate
  # is the evidence it published and not its exit code.  That evidence is the
  # session: one JSONL file per row kind (CONTRACT-SPEC SS2), and a session
  # with no activation row replayed nothing whatever the exit code said.
  if [[ "${region_results}" == required ]]; then
    local live
    live=$(find "${sessions}" -mindepth 2 -maxdepth 2 \
      -name activations.jsonl -size +0c -print -quit 2>/dev/null) || live=""
    [[ -n "${live}" ]] || campaign_fail REPLAY WORKLOAD "${sessions}" \
      "the concolic replay published no activation row (exit ${status}); the workload terminated before its selected regions ran and its exception is in ${worker}/replay.log"
    # Some region ran, but not the failure target.  EXPLORE still plans the
    # TARGET member the kept slice names, and refuses it as
    # NO_OBSERVED_PATH_SEED -- stages and one JVM wave away from the workload
    # exception that caused it.  Name the unreached target here instead,
    # beside the log that holds that exception.  The target row states it:
    # reachedAnchor says whether this session reached the anchor at all.
    local declared_target reached=""
    local -a target_rows=()
    # The annotated target's method, off the TARGET_SITE row of the static
    # scope map: the map already states that site, and target_resolved.json
    # restated it for this one reader.
    declared_target=$(jq -r -s '
      [.[] | select(.role == "TARGET_SITE") | .siteId
             | sub("#u[0-9]+$"; "")] | first // ""' \
      "${causynth_static_scope_map}") \
      || campaign_fail REPLAY WORKLOAD "${sessions}" \
        "the declared target could not be read for target coverage"
    while IFS= read -r -d '' target_file; do
      target_rows+=("${target_file}")
    done < <(find "${sessions}" -mindepth 2 -maxdepth 2 -name targets.jsonl \
      -print0)
    if [[ -n "${declared_target}" && ${#target_rows[@]} -gt 0 ]]; then
      reached=$(jq -r -n --arg target "${declared_target}" '
        [inputs
          | select(.reachedAnchor == true)
          | select(.anchorSiteId | startswith($target + "#"))
          | .anchorSiteId] | first // ""' "${target_rows[@]}") \
        || campaign_fail REPLAY WORKLOAD "${sessions}" \
          "the target rows could not be read for target coverage"
    fi
    [[ -n "${declared_target}" && -n "${reached}" ]] || campaign_fail REPLAY \
      WORKLOAD "${sessions}" \
      "the concolic replay reached no TARGET_REACH occurrence (exit ${status}); no session published a target row that reached ${declared_target:-the declared target}; the workload's terminating exception is in ${worker}/replay.log"
  fi
  campaign_log "replay role=${role} exit=${status} sessions=${sessions}"
}


campaign_session_replay() {
  local iteration_dir=$1
  local seed="${iteration_dir}/seed-result"
  local plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  # CAUSYNTH_CONCOLIC_RESULTS names this replay, it is not a file any more:
  # RowRuntime derives the session id from the directory holding it, and the
  # rows themselves go to ${iteration_dir}/sessions/<sessionId>/.
  local results="${seed}/concolic_region_results.jsonl"
  local ids
  ids=$(campaign_task_ids "${plan}")
  # The seed replay is a focused replay like any other: one occurrence is
  # symbolic, everything else runs concretely, recording its exports and
  # minting v_H at every declared port.  It writes its rows per kind into its
  # own session directory (CONTRACT-SPEC SS2), which is what IMPORT reads.
  campaign_sessions_dir="${iteration_dir}/sessions"
  mkdir -p "${campaign_sessions_dir}"
  campaign_replay worker "${plan}" "${ids}" \
    "${iteration_dir}/instrumented-classes" "${results}" "${seed}/focused"
}


# IMPORT: the replay's per-kind session files, checked and counted.
#
# A replay session writes one JSONL file per row kind under
# <iteration>/sessions/<sessionId>/ (CONTRACT-SPEC SS2).  There is nothing to
# fold here any more: a reader of exports never parses attaches, the kinds are
# joined by Endpoint and Interaction id rather than by the activation envelope
# they used to share, and no stage has to re-parse a whole result to read one
# of them.  This stage checks that each session published every kind its
# readers open, and publishes the census.
campaign_import_session() {
  local iteration_dir=$1 iteration_id=$2
  local sessions="${iteration_dir}/sessions"
  local census="${iteration_dir}/session_census.jsonl"
  local session name kind path rows missing="" count=0
  require_directory "replay sessions" "${sessions}"
  : >"${census}"
  for session in "${sessions}"/*/; do
    [[ -d "${session}" ]] || continue
    name=$(basename "${session}")
    count=$((count + 1))
    for kind in activations decisions exports attaches writes reads roots \
        targets gaps; do
      path="${session}${kind}.jsonl"
      if [[ ! -e "${path}" ]]; then
        missing="${missing} ${name}/${kind}.jsonl"
        continue
      fi
      rows=$(wc -l <"${path}")
      jq -n -c --arg session "${name}" --arg kind "${kind}" \
        --arg epoch "${iteration_id}" --argjson rows "${rows}" \
        '{schemaVersion: 1, kind: "SESSION_CENSUS", topologyEpoch: $epoch,
          sessionId: $session, rowKind: $kind, rows: $rows}' >>"${census}"
    done
    [[ -s "${session}expressions.json" ]] \
      || missing="${missing} ${name}/expressions.json"
  done
  [[ "${count}" -gt 0 ]] || campaign_fail IMPORT SessionDir "${sessions}" \
    "the replay published no session directory"
  [[ -z "${missing}" ]] || campaign_fail IMPORT SessionDir "${sessions}" \
    "a replay session published no file for:${missing}"
  require_nonempty "replay session census" "${census}"
  campaign_log "sessions: ${count}, rows: $(jq -r -s '[.[].rows] | add // 0' \
    "${census}")"
  campaign_import_gate "${iteration_dir}" "${iteration_id}"
}

# The row contract, checked once, where every row passes through.
#
# A defect in a row is not one stage's problem.  17960 lost two campaigns to
# rows that EXPLORE and COMPOSE each read as valid -- a decision whose
# `outcome` was the complement of its term's truth value, and a focused
# session that published rows with an empty expression table -- and each stage
# that met one reported something later and elsewhere.  contract.
# RowInvariants states the contract's own sentences, and the gate runs them
# here: a BLOCKING violation stops the campaign at IMPORT, naming the row, and
# a DIAGNOSTIC one is recorded and the campaign goes on.
#
# Append-only, into the campaign's own gap file: a gap row a later stage
# overwrites was never evidence.
campaign_import_gate() {
  local iteration_dir=$1 iteration_id=$2
  # A wave runs the same gate over its own session set: the gate is given
  # the sessions to read and the file to summarise into, and appends to the
  # one campaign gap file either way.
  local sessions=${3:-${iteration_dir}/sessions}
  local summary=${4:-${iteration_dir}/import_gate.json}
  local gaps="${iteration_dir}/campaign_gaps.jsonl"
  local blocking violations first
  run_java_main edu.uva.liftlab.graphchecker.contract.ImportGateMain \
    --sessions "${sessions}" \
    --out "${gaps}" \
    --topology-epoch "${iteration_id}" >"${summary}"
  require_nonempty "import gate summary" "${summary}"
  violations=$(jq -r '.violations' "${summary}")
  campaign_count IMPORT ImportGate "${summary}" \
    "the import gate's violation count" "${violations}"
  blocking=$(jq -r '.blocking' "${summary}")
  campaign_count IMPORT ImportGate "${summary}" \
    "the import gate's blocking count" "${blocking}"
  first=$(jq -r '.firstBlockingSubject // ""' "${summary}")
  campaign_log "import gate: ${violations} row invariant violation(s), \
${blocking} blocking"
  [[ "${blocking}" -eq 0 ]] || campaign_fail IMPORT ImportGate "${gaps}" \
    "${blocking} row invariants violated: ${first}"
}

# The same gate, over one wave's own replays.
#
# It used to run once, on the seed session alone, so every FOCUSED session a
# wave published entered EXPLORE and COMPOSE unchecked: an invariant-8
# violation there (a root mint whose recordedValue is empty) was read as a
# valid row by both stages and reported, if at all, later and elsewhere.  A
# wave is where a focused session is produced, so it is where the contract is
# checked -- a BLOCKING violation fails the campaign at that wave, by name.
#
# ImportGateMain reads the session set of an ITERATION directory
# ({@code <iteration>/sessions}) and invariant 10 needs that directory's
# obligation workers, so the wave is given a directory of exactly that shape:
# the EPOCH's whole session roster, and itself as the one wave of workers.
# Nothing is copied and nothing under sessions/ is written.
#
# The whole roster, not the wave's own new sessions: invariant 1 is a
# SET-level rule -- exactly one session of the set states role SEED -- and a
# set built from the wave alone never holds the seed, so every wave of every
# case refused "0 of N sessions state role SEED".  The wave's own sessions
# decide only WHETHER this gate runs, not what it reads.
campaign_import_wave_gate() {
  local iteration_dir=$1 iteration_id=$2 wave_dir=$3 sessions=$4
  local before="${wave_dir}/sessions-before.txt"
  local gate="${wave_dir}/import-gate"
  local name count=0
  require_file "wave session roster" "${before}"
  rm -rf -- "${gate}"
  mkdir -p "${gate}/sessions"
  ln -s "${wave_dir}" "${gate}/obligations-0000"
  while IFS= read -r name; do
    [[ -n "${name}" && -d "${sessions}/${name}" ]] || continue
    count=$((count + 1))
  done < <(campaign_wave_sessions "${sessions}" "${before}")
  if [[ "${count}" -eq 0 ]]; then
    # Every obligation of the wave failed to replay, which its own result
    # rows already say; there is no row here to check.
    campaign_log "import gate: $(basename "${wave_dir}") published no session"
    return 0
  fi
  campaign_log "import gate: $(basename "${wave_dir}") published \
${count} session(s)"
  while IFS= read -r name; do
    [[ -n "${name}" && -d "${sessions}/${name}" ]] || continue
    ln -s "${sessions}/${name}" "${gate}/sessions/${name}"
  done < <(campaign_session_roster "${sessions}")
  campaign_import_gate "${iteration_dir}" "${iteration_id}" \
    "${gate}/sessions" "${wave_dir}/import_gate.json"
}

# The session names under ${1} that are not in the roster file ${2}.
campaign_wave_sessions() {
  local sessions=$1 before=$2
  LC_ALL=C comm -13 "${before}" <(campaign_session_roster "${sessions}")
}

# Every session directory name under ${1}, sorted.
campaign_session_roster() {
  local sessions=$1 entry
  for entry in "${sessions}"/*/; do
    [[ -d "${entry}" ]] || continue
    basename "${entry}"
  done | LC_ALL=C sort
}


# One obligation: solve it, replay it focused, record its verdict.
#
# The obligation names ONE focused occurrence, the decision it flips, the root
# assignments to apply at the mints and the answers to apply at the attaches
# (CONTRACT-SPEC SS3).  The replay writes its rows into its own session
# directory, which is the only thing COMPOSE reads; this function's output is
# the one ObligationResult row that says which verdict it reached.
#
# A single obligation that could not be solved or replayed is that
# obligation's own result row, never the wave's death: on laneVM11 one planner
# exception discarded ten finished replays and every verdict they carried.
campaign_obligation_worker() {
  local obligation_id=$1 obligations=$2 classes=$3 worker=$4 sessions=$5
  local seed_plan=$6
  local outcome replay_tasks status=0
  local -a domain_args=()
  # The same declaration EXPLORE and COMPOSE read: an answer is only as free
  # as the root domains behind the arm that produces it.
  [[ -z "${causynth_root_domains}" ]] \
    || domain_args+=(--root-domains "${causynth_root_domains}")
  # Two files, one shape each.  execution_task_plan.jsonl is the PLAN, whose
  # rows the workload session opener decodes (ConcolicTaskPlan.load ->
  # plan.ExecutionTask.decode), so a focused replay gets the SEED's plan
  # here, hard-linked exactly as campaign_plan links it for seed workers.  The
  # obligation's own focus row is focused_task.jsonl, written by the solver;
  # it used to be written under the plan's name, and every obligation replay
  # died on "execution task requires sourceKey" before it started.
  local plan="${worker}/execution_task_plan.jsonl"
  local focus="${worker}/focused_task.jsonl"
  local results="${worker}/concolic_region_results.jsonl"
  local result_row="${worker}/obligation_result.jsonl"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ObligationSolverMain \
    --obligations "${obligations}" \
    --obligation-id "${obligation_id}" \
    --sessions "${sessions}" \
    --output-dir "${worker}" \
    --z3 "${z3_bin}" \
    --solver-timeout-ms "${solver_timeout_ms}" \
    "${domain_args[@]}"
  if [[ "${status}" -ne 0 ]]; then
    campaign_log "obligation solver failed on ${obligation_id} \
(exit ${status}): $(grep -v -E '^[[:space:]]+at ' "${worker}/stderr.log" \
      2>/dev/null | tail -n 1)"
    jq -n -c --arg id "${obligation_id}" --arg detail "$(grep -v -E \
        '^[[:space:]]+at ' "${worker}/stderr.log" 2>/dev/null | tail -n 1)" \
      '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
        verdict: "NOT_ADMITTED", sessionId: "", detail: $detail}' \
      >"${result_row}"
    return 0
  fi
  require_nonempty "obligation solver result" "${result_row}"
  require_nonempty "obligation query" "${worker}/obligation_query.smt2"
  outcome=$(jq -er '.verdict' "${result_row}")
  # The solver owns what a finished obligation is.  UNSAT and NOT_ADMITTED
  # are recorded terminal verdicts, not process failures, and the next wave
  # reads them so the obligation is not proposed again.
  case "${outcome}" in
    UNSAT|NOT_ADMITTED) return 0 ;;
  esac
  [[ "${outcome}" == "SAT_MODEL_READY" ]] \
    || die "the obligation verdict is not solver-backed: ${outcome}"
  require_nonempty "obligation focus row" "${focus}"
  ln -f "${seed_plan}" "${plan}"
  replay_tasks=$(campaign_task_ids "${plan}")
  [[ -n "${replay_tasks}" ]] \
    || die "the seed plan names no task to replay: ${plan}"
  campaign_sessions_dir="${sessions}" \
    campaign_replay worker "${plan}" "${replay_tasks}" "${classes}" \
      "${results}" "${worker}" tolerated
  # THE REPLAY OWNS THE VERDICT.  RowRuntime.closeSession rewrites this
  # file with the rows FocusedReplay.results built -- the same rows it
  # publishes into the session, which is the evidence -- so there is
  # nothing to stamp here and never was: `. + {verdict: "ADMITTED"}` said
  # ADMITTED of every replay that merely finished, and on hdfs-11741
  # campaign #3 six of eleven obligations were aggregated ADMITTED while
  # their own sessions said NOT_ADMITTED.  What is checked instead is that
  # the replay DID state one: a row still carrying the solver's
  # SAT_MODEL_READY means the replay published no verdict for it, which is
  # neither an admission nor a refusal.
  outcome=$(jq -r '.verdict // ""' "${result_row}")
  case "${outcome}" in
    ADMITTED|NOT_ADMITTED|UNSAT) ;;
    *) campaign_fail EXPLORE ObligationSolverMain "${result_row}" \
        "the replay of ${obligation_id} published no verdict for it \
(the row still states \"${outcome}\")" ;;
  esac
}

# Region-path obligations are coordinated in closure-wide waves below.


# EXPLORE: waves of focused obligations until the frontier stops moving.
#
# One JVM plans the wave -- explore.ExploreMain reads every session this
# epoch has produced and writes the obligations the frontier is owed -- and
# one worker per obligation executes it.  A task is ONE focused occurrence
# (or one state-connected factor); everything else in that replay runs
# concretely, so there is no member roster to plan against and no per-member
# worklist to reconcile: the sessions are the shared state, and a wave reads
# every session the waves before it wrote.
#
# Both stops are coverage telemetry, never a campaign failure.  A wave that
# proposes the same obligations as the wave before it, with the same verdicts
# behind them, has learned nothing; continuing would re-solve the same set for
# ever.  An unexplored sibling path blocks a closed UNSAT and says nothing
# about a SAT candidate, so the stop is written as a gap row and the campaign
# goes on to publish what it did establish.
campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local sessions="${iteration_dir}/sessions"
  local results="${iteration_dir}/obligation_results.jsonl"
  local classes="${iteration_dir}/instrumented-classes"
  local wave=0 pending=0 status=0 obligation_id worker_dir wave_dir job
  local wave_signature="" previous_signature="" stop_kind="" stop_reason=""
  local obligations
  local -a bound_args=() domain_args=() anchor_args=() jobs=() pids=()
  local declared
  declared=$(campaign_declared_target_occurrence)
  [[ -z "${declared}" ]] || anchor_args+=(--target-occurrence "${declared}")

  : >"${results}"
  [[ -z "${region_path_max_paths_per_region}" ]] \
    || bound_args+=(--max-paths-per-region "${region_path_max_paths_per_region}")
  [[ -z "${region_path_max_flips_per_path}" ]] \
    || bound_args+=(--max-flips-per-path "${region_path_max_flips_per_path}")
  [[ -z "${region_path_max_tasks}" ]] \
    || bound_args+=(--max-tasks "${region_path_max_tasks}")
  # The same declaration COMPOSE reads.  An obligation's handoff answers are
  # constrained by their interaction's family, and a family arm is only as
  # constraining as the roots inside it: without the case's declared domain
  # every arm pins its answer to what the recording delivered, and no
  # rotation the case assumes could ever be explored.
  [[ -z "${causynth_root_domains}" ]] \
    || domain_args+=(--root-domains "${causynth_root_domains}")

  while true; do
    wave_dir=$(printf '%s/obligations-%04d' "${iteration_dir}" "${wave}")
    [[ ! -e "${wave_dir}" ]] || die \
      "obligation wave directory already exists: ${wave_dir}"
    mkdir -p "${wave_dir}"
    obligations="${wave_dir}/obligations.jsonl"
    status=0
    run_java_main edu.uva.liftlab.graphchecker.explore.ExploreMain \
      --sessions "${sessions}" \
      --results "${results}" \
      --static-scope-map "${causynth_static_scope_map}" \
      --topology-epoch "${iteration_id}" \
      --wave "${wave}" \
      --output-dir "${wave_dir}" \
      "${anchor_args[@]}" \
      "${domain_args[@]}" \
      "${bound_args[@]}" \
      >"${wave_dir}/stdout.log" 2>"${wave_dir}/stderr.log" || status=$?
    if [[ "${status}" -ne 0 ]]; then
      campaign_fail EXPLORE ExploreMain "${wave_dir}/stderr.log" \
        "the wave planner failed with exit ${status}"
    fi
    # An empty obligations file is the frontier closing, which is how the
    # loop is meant to end: the planner has nothing left to ask for.  This
    # used to be require_nonempty, so the planner had to write a blank-id
    # marker row to survive its own success.
    [[ -s "${obligations}" ]] || break

    jobs=()
    pending=0
    while IFS= read -r obligation_id; do
      [[ -n "${obligation_id}" ]] || continue
      jobs+=("${obligation_id}")
      pending=$((pending + 1))
    done < <(jq -r '.obligationId' "${obligations}")
    [[ "${pending}" -gt 0 ]] || break

    # Obligation identity is stable across waves, so an unchanged signature
    # over the ids AND the verdicts recorded so far is a fixed point the
    # "pending > 0" test alone cannot see.
    wave_signature=$({
        printf '%s\n' "${jobs[@]}" | LC_ALL=C sort
        printf -- '--\n'
        jq -r '.verdict // ""' "${results}" | LC_ALL=C sort | uniq -c
      } | sha256sum | cut -d' ' -f1) \
      || campaign_fail EXPLORE CAMPAIGN "${results}" \
        "failed to summarise obligation wave ${wave}"
    stop_kind=""
    if [[ "${wave}" -ge "${region_path_max_waves}" ]]; then
      stop_kind=REGION_PATH_WAVE_BUDGET_REACHED
      stop_reason="the exploration loop reached its configured budget of \
${region_path_max_waves} wave(s) with ${pending} obligation(s) still open"
    elif [[ "${wave_signature}" == "${previous_signature}" ]]; then
      stop_kind=REGION_PATH_CLOSURE_NO_PROGRESS
      stop_reason="wave ${wave} proposes the same ${pending} obligation(s) \
as the wave before it with no new verdict"
    fi
    if [[ -n "${stop_kind}" ]]; then
      jq -n -c --arg kind "${stop_kind}" --arg detail "${stop_reason}" \
        --arg epoch "${iteration_id}" \
        '{schemaVersion: 1, sessionId: "",
          kind: "ADMISSION_GAP", cls: "DIAGNOSTIC",
          subject: $kind, detail: $detail, topologyEpoch: $epoch}' \
        >>"${iteration_dir}/campaign_gaps.jsonl"
      campaign_log "exploration stopped: ${stop_kind}: ${stop_reason}"
      break
    fi
    previous_signature=${wave_signature}
    campaign_log "wave ${wave}: ${pending} obligation(s), \
workers=${concolic_worker_count}"
    # Which sessions existed before this wave's replays landed, so the row
    # contract below is checked over the wave's own and no other.
    campaign_session_roster "${sessions}" >"${wave_dir}/sessions-before.txt"
    pids=()
    status=0
    for job in "${jobs[@]}"; do
      worker_dir="${wave_dir}/${job}"
      mkdir -p "${worker_dir}"
      (
        set -euo pipefail
        campaign_obligation_worker "${job}" "${obligations}" "${classes}" \
          "${worker_dir}" "${sessions}" \
          "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
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
    [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE CAMPAIGN "${wave_dir}" \
      "obligation wave ${wave} did not finish"
    # Every verdict this wave reached, appended once the wave settled, so the
    # next wave sees a complete frontier rather than a partial one.
    find "${wave_dir}" -mindepth 2 -maxdepth 2 -name obligation_result.jsonl \
      -print0 | LC_ALL=C sort -z | xargs -0 -r cat >>"${results}"
    # The row contract, over the sessions this wave published, before the
    # next wave's planner reads one of their rows.
    campaign_import_wave_gate "${iteration_dir}" "${iteration_id}" \
      "${wave_dir}" "${sessions}"
    wave=$((wave + 1))
  done
  campaign_log "exploration stopped after ${wave} wave(s), \
$(wc -l <"${results}") obligation verdict(s)"
}


# Gap rows this iteration's stages wrote outside a session live in one file,
# ${iteration_dir}/campaign_gaps.jsonl, appended by whoever raises them and
# read once by EMIT.  There is no collector any more and nothing truncates it.
#
# There was one, and it discarded every row it was supposed to gather: its
# find excluded the only path that could match its own -name, so the merge
# list was always empty and the function's whole effect was a truncation of
# the very file it was named for.  It ran one line after EXPLORE -- deleting
# the wave-budget and no-progress GAP_ROWs campaign_explore had just appended
# -- and again at the end of campaign_publish_pending_refinement, deleting
# that function's own TOPOLOGY_DIVERGENCE row.  EMIT then read an empty file
# into gaps.json, so both kinds were silently absent from every gap report.
#
# Session gap rows stay where the replay wrote them: EMIT reads them straight
# out of the session directories, because a GapRow states its own class and
# nothing between the runtime and the report is in a position to change it.
campaign_publish_iteration_manifest() {
  local iteration_dir=$1 iteration=$2 parent=$3
  local index="${iteration_dir}/seed-replay/runtime_workflow_schedule_index.json"
  local plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  local members="${iteration_dir}/.members.jsonl"
  local role campaign_id region occurrence goal task worker
  local obligations plan_sha index_sha census_sha obligations_sha
  local census="${iteration_dir}/session_census.jsonl"
  local obligation_results="${iteration_dir}/obligation_results.jsonl"
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
  # What this epoch imported and explored, digested from the two artifacts
  # its own stages wrote before this point.  It used to digest
  # concolic_region_summaries.jsonl, which no stage has written since the
  # stage reduction: campaign_digest dies on a missing file, so the
  # campaign_fail below fired on every run that reached PLAN.  The manifest is
  # published after EXPLORE and before COMPOSE, so the composition manifest
  # and result.json do not exist yet and cannot be what it commits to; the
  # census IMPORT required and the verdicts EXPLORE appended do.
  if ! census_sha=$(campaign_digest "${census}"); then
    campaign_fail EMIT CAMPAIGN "${census}" \
      "failed to digest the replay session census"
  fi
  if ! obligations_sha=$(campaign_digest "${obligation_results}"); then
    campaign_fail EMIT CAMPAIGN "${obligation_results}" \
      "failed to digest the obligation verdicts"
  fi
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg iteration "${iteration}" \
    --arg parent "${parent}" \
    --arg plan "${plan}" \
    --arg planSha "${plan_sha}" \
    --arg index "${index}" --arg indexSha "${index_sha}" \
    --arg census "${census}" --arg censusSha "${census_sha}" \
    --arg obligations "${obligation_results}" \
    --arg obligationsSha "${obligations_sha}" \
    --arg classes "${iteration_dir}/instrumented-classes" \
    --argjson workers "${concolic_worker_count}" \
    --slurpfile members "${members}" '
    {schemaVersion: 1,
     kind: "CAMPAIGN_ITERATION_MANIFEST",
     iterationId: $iteration,
     parentIterationId: $parent,
     provenance: $provenance,
     executionTaskPlan: {path: $plan, sha256: $planSha},
     scheduleIndex: {path: $index, sha256: $indexSha},
     sessionCensus: {path: $census, sha256: $censusSha},
     obligationResults: {path: $obligations, sha256: $obligationsSha},
     instrumentedClasses: $classes,
     externalWorkerCount: $workers,
     members: $members}
  ' >"${iteration_dir}/iteration_manifest.json"
  rm -f "${members}"
  require_nonempty "iteration manifest" \
    "${iteration_dir}/iteration_manifest.json"
}


# COMPOSE: one anchor, one formula.
#
# The anchor is the occurrence the case declares.  Which execution of the
# annotated site a campaign answers about is the case's to state, so there is
# no fan-out over observed occurrences here and nothing to elect afterwards:
# the composer reads every session this epoch produced, factorizes the paths
# that reach the declared anchor, and writes one candidate.smt2 beside one
# manifest.
campaign_compose() {
  local iteration_dir=$1
  local started ended millis status=0
  [[ ! -e "${campaign_final}" ]] || die \
    "the final directory already exists: ${campaign_final}"
  mkdir -p "${campaign_final}"
  compose_sessions_dir="${iteration_dir}/sessions"
  require_directory "replay sessions" "${compose_sessions_dir}"
  composed_smt="${campaign_final}/candidate.smt2"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  started=$(date +%s%N)
  run_capturing_status do_compose >"${campaign_final}/compose.log" 2>&1
  ended=$(date +%s%N)
  millis=$(( (ended - started) / 1000000 ))
  [[ "${status}" -eq 0 ]] || campaign_fail COMPOSE ComposeMain \
    "${campaign_final}/compose.log" \
    "the composer failed with exit ${status} on inputs it was given"
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${composition_manifest}"
  printf '%s\t%s\n' "COMPOSE[anchor]" "${millis}" \
    >>"${campaign_stage_metrics}"
  campaign_log "composed $(jq -r '.anchor // ""' "${composition_manifest}") \
in ${millis}ms status=$(jq -r '.finalStatus // ""' "${composition_manifest}")"
}



# SOLVE: z3's verdict on the anchor's formula, as the composer recorded it.
#
# ComposeMain runs z3 per valuation while it composes -- it has the root
# domains, the selectors and the formula in hand -- and writes the state,
# the reachability, the valuations and the claim into the manifest under
# `solver`.  A second solver process would re-derive what that one already
# decided from artifacts it wrote, so this stage reads the manifest and
# checks that the verdict is there.  The stage stays its own stage: it is
# where a reader looks for the solver's answer, and where its wall time is
# recorded.
campaign_solve() {
  local report="${composition_manifest}"
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${report}"
  campaign_require_json "candidate composition manifest" "${report}" \
    || campaign_fail SOLVE ComposeMain "${report}" \
      "the composition manifest is malformed"
  jq -e '(.solver | type) == "object" and ((.solver.state // "") != "")' \
    "${report}" >/dev/null \
    || campaign_fail SOLVE ComposeMain "${report}" \
      "the composition published no solver verdict for its anchor"
  campaign_log "z3 state=$(jq -r '.solver.state' "${report}") \
reachability=$(jq -r '.solver.reachability // "UNKNOWN"' "${report}") \
valuations=$(jq -r '(.solver.valuations // []) | length' "${report}")"
}


# DECIDE: the claim the composition reached, checked and printed.
#
# There is one anchor and therefore one claim.  Ranking observed occurrences
# into a campaign verdict is gone with the election: which execution of the
# annotated site the campaign is about is the case's declaration, and the
# claim about it is whatever its own formula decided.
campaign_decide() {
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${composition_manifest}"
  campaign_print_symbolic_variable_models "${composition_manifest}" \
    || campaign_fail DECIDE ComposeMain "${composition_manifest}" \
      "the solver result has no valid symbolic variable model"
  jq -r '"  anchor=\(.anchor // "") finalStatus=\(.finalStatus // "")"
    + " claim=\(.solver.campaignClaim.claim // "")"
    + " blockers=\(.solver.campaignClaim.blockerCount // 0)"' \
    "${composition_manifest}"
}

campaign_artifact_digests() {
  local name path bytes sha row
  local -a required=(candidate.smt2 candidate_composition_manifest.json
    gaps.json result.json)
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

# The static catalog's own gaps, as a JSON array.  A campaign that restored
# its seed from cache still has this artifact, because it is one of the
# cached ones.
campaign_static_gaps_json() {
  local gzipped="${causynth_output_dir}/communication_gaps.jsonl.gz"
  if [[ ! -s "${gzipped}" ]]; then
    echo '[]'
    return 0
  fi
  gzip -d -c -- "${gzipped}" | jq -c -s '.' || return 1
}

# The planning gaps the runtime plan artifact carries in its catalog row.
campaign_plan_gaps_json() {
  if [[ ! -s "${runtime_region_plan}" ]]; then
    echo '[]'
    return 0
  fi
  head -n 1 -- "${runtime_region_plan}" | jq -c '.gaps // []' || return 1
}

# One generated JSON document, as a file jq can read.
#
# A command-line argument is capped at 128 KiB on Linux -- MAX_ARG_STRLEN,
# 32 pages, a per-argument limit that no ARG_MAX headroom relaxes -- and the
# documents below are proportional to the corpus.  lane11741j died at EMIT
# with "Argument list too long" on a generated document of 134,436 bytes
# reaching DECIDE with SAT_CANDIDATE and 0 blockers: a whole campaign's
# verdict lost to an argv limit.  Every generated document is written to a
# file and slurped; none is passed with --argjson.
campaign_json_file() {
  local destination=$1 content=$2
  printf '%s\n' "${content}" >"${destination}" || return 1
  printf '%s' "${destination}"
}

# Every gap this campaign raised, in one document, each row classed by the row
# itself.
#
# A GapRow states its own kind and class (CONTRACT-SPEC SS2): the stage that
# raised it knows what it could not do, and no later stage is in a position to
# overrule that.  So this is a partition, not a classification -- the 190
# lines of jq that used to decide a row's class against the replay slice, the
# composed ports and the flip wave are gone with the questions they asked, and
# so is the second registry that classed PLAN rows by code.  A row that states
# no class is BLOCKING.
#
# This function and the `accepted` conjunction it feeds are the ONE reader of
# a gap's class in the campaign: every other stage states classes and reads
# none but its own.  classReason says which of the two rules answered, and it
# used to answer "no stated class: blocking by default" for every row that
# stated BLOCKING -- all three OCCURRENCE_ADDRESS_SHARED rows of the reviewed
# hdfs-17960 run, whose producer had stated the class the reader then
# disowned.
campaign_write_gaps() {
  local composition=$1 iteration_dir=$2 output=$3
  local scratch status=0
  scratch=$(mktemp -d "${TMPDIR:-/tmp}/graphchecker-gapargs.XXXXXX") \
    || return 1
  campaign_json_file "${scratch}/static-gaps.json" \
    "$(campaign_static_gaps_json)" >/dev/null \
    || { rm -rf -- "${scratch}"; return 1; }
  campaign_json_file "${scratch}/plan-gaps.json" \
    "$(campaign_plan_gaps_json)" >/dev/null \
    || { rm -rf -- "${scratch}"; return 1; }
  # Every session's own gap rows, plus the campaign's.
  find "${iteration_dir}" -type f -name 'gaps.jsonl' -print0 \
    | LC_ALL=C sort -z | xargs -0 -r cat >"${scratch}/session-gaps.jsonl"
  [[ ! -s "${iteration_dir}/campaign_gaps.jsonl" ]] \
    || cat "${iteration_dir}/campaign_gaps.jsonl" \
      >>"${scratch}/session-gaps.jsonl"
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --slurpfile composedDocuments "${composition}" \
    --slurpfile staticGapDocuments "${scratch}/static-gaps.json" \
    --slurpfile planGapDocuments "${scratch}/plan-gaps.json" \
    --rawfile sessionGaps "${scratch}/session-gaps.jsonl" '
    ($staticGapDocuments[0] // []) as $staticGaps |
    ($planGapDocuments[0] // []) as $planGaps |
    $composedDocuments[0] as $composed |
    # A row that states its own class is taken at its word.
    (($sessionGaps | split("\n") | map(select(length > 0) | fromjson))
      | map({stage: "REPLAY", source: (.sessionId // "RUNTIME"),
             code: (.kind // "ADMISSION_GAP"),
             subject: (.subject // ""), detail: (.detail // ""),
             class: (if (.cls // "BLOCKING") == "DIAGNOSTIC"
                     then "DIAGNOSTIC" else "BLOCKING" end),
             classReason: "the row states its own class"}))
      as $sessionRows |
    # The composer names its refusals; each is blocking by construction.  Its
    # own gap rows state their class like any other GapRow, and a row that
    # states none is blocking, which is what an unregistered code means.
    (($composed.finalStatusRefusals // [])
      | map({stage: "COMPOSE", source: "ComposeMain",
             code: (.kind // "COMPOSITION_GAP"),
             subject: (.subject // ""), detail: (.detail // ""),
             class: "BLOCKING",
             classReason: "a composition refusal withholds its own claim"}))
      as $refusalRows |
    ((($composed.gaps // []) + ($composed.claim.gaps // []))
      | map({stage: "COMPOSE", source: "ComposeMain",
             code: (.kind // .reason // ""),
             subject: (.subject // ""), detail: (.detail // ""),
             class: (if (.cls // "BLOCKING") == "DIAGNOSTIC"
                     then "DIAGNOSTIC" else "BLOCKING" end),
             classReason: (if (.cls // "") == ""
                           then "no stated class: blocking by default"
                           else "the row states its own class"
                           end)}))
      as $composerGapRows |
    ($refusalRows + $composerGapRows) as $composeRows |
    # The static catalog and the runtime plan state kind and class on their
    # own rows, like every other producer; a row that states none is blocking.
    (($staticGaps + $planGaps)
      | map({stage: "PLAN", source: (.source // "CATALOG"),
             code: (.kind // ""),
             subject: (.subject // .siteId // ""), detail: (.detail // ""),
             class: (if (.cls // "BLOCKING") == "DIAGNOSTIC"
                     then "DIAGNOSTIC" else "BLOCKING" end),
             classReason: (if (.cls // "") == ""
                           then "no stated class: blocking by default"
                           else "the row states its own class"
                           end)}))
      as $declaredRows |
    (($sessionRows + $composeRows + $declaredRows)
      | unique_by([.stage, .source, .code, .subject, .detail])) as $rows |
    {schemaVersion: 2,
     kind: "CAMPAIGN_COVERAGE_GAPS",
     provenance: $provenance,
     gaps: [$rows[] | select(.class == "BLOCKING")],
     telemetryGaps: [$rows[] | select(.class == "DIAGNOSTIC")]}
    | .gapCount = (.gaps | length)
    | .telemetryCount = (.telemetryGaps | length)
    | .byStage = (.gaps | group_by(.stage)
        | map({key: .[0].stage, value: length}) | from_entries)
    | .byCode = (.gaps | group_by(.code)
        | map({key: .[0].code, value: length}) | from_entries)
  ' >"${output}" || status=$?
  rm -rf -- "${scratch}"
  return "${status}"
}

# The named outputs. Nothing here recomputes a verdict: every field is copied
# from the stage that decided it, and the claim is read off those states.
campaign_emit() {
  local iteration_dir=$1
  local session_rows session_bytes gapCount
  local artifacts_json stages_json iterations_json
  # Before anything is published: the generation this run was frozen on must
  # still be the generation on disk.
  campaign_verify_frozen_inputs

  # One readable document each, because the reads below are jq invocations
  # that would otherwise hide a producer's parse failure behind their own
  # successful exit. What schemaVersion and kind those documents declare is
  # the Composer's and the extractor's own contract, published by the layer
  # that writes them; the shell does not restate it.
  campaign_require_json "candidate composition manifest" \
    "${composition_manifest}" || campaign_fail EMIT ComposeMain \
      "${composition_manifest}" "required composition JSON is malformed"
  require_nonempty "replay session census" \
    "${iteration_dir}/session_census.jsonl"

  # Every gap row states its own kind and class, wherever it was raised, and
  # a row that states no class is blocking: a gap added to some stage
  # withholds the claim until its producer states why it cannot break a chain.
  campaign_write_gaps \
    "${composition_manifest}" \
    "${iteration_dir}" \
    "${campaign_final}/gaps.json"
  require_nonempty "campaign gaps" "${campaign_final}/gaps.json"
  campaign_require_json "campaign gaps" "${campaign_final}/gaps.json" \
    || campaign_fail EMIT CAMPAIGN "${campaign_final}/gaps.json" \
      "the generated gaps JSON is malformed"

  # The claim is the ClaimPolicy decision the solver stage published with its
  # own report.  Nothing here recomputes it: this stage copies the claim, its
  # reason, and every named blocker, so one Java policy decides acceptance and
  # the shell only publishes what it decided.
  campaign_require_claim "${composition_manifest}"
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --slurpfile composedDocuments "${composition_manifest}" \
    --slurpfile gapDocuments "${campaign_final}/gaps.json" '
    $composedDocuments[0] as $c | ($c.solver // {}) as $r |
    $gapDocuments[0] as $gaps |
    ($r.campaignClaim) as $decided |
    ($r.reachability // "UNKNOWN") as $reachability |
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
     # ClaimPolicy counts its own blockers; re-counting the array here let
     # the published count drift from the policy that decided the claim.
     blockerCount: $decided.blockerCount,
     whyNotAccepted: $decided.whyNotAccepted,
     # WHICH mechanism the formula supports, beside WHETHER the run is
     # accepted.  Two questions, and a reader of result.json alone could
     # answer only the second: the ClaimKind, the valuation that carried it
     # and the roots it moved stayed in the composition manifest, so the
     # acceptance harness had to re-derive the mechanism from a probe of its
     # own.  polarityDecides travels with them because it is the condition
     # the claim rests on -- ClaimPolicy refuses MARKER_FLIPPED and
     # CLOCK_SKEW outright without it -- not a note beside the claim.
     findingKind: $decided.findingKind,
     polarityDecides: $decided.polarityDecides,
     valuationOrdinal: $decided.valuationOrdinal,
     movedRoots: $decided.movedRoots,
     reachability: $reachability,
     solverState: ($r.state // ""),
     finalStatus: ($c.finalStatus // ""),
     finalStatusRefusals: $blockers,
     evidence: {
       symbolicPropagationComplete:
         ($c.symbolicPropagationComplete // false),
       unsatClosureComplete: $unsatClosureComplete},
     gapCount: $gapCount,
     telemetryCount: $telemetryCount,
     # The claim is what ClaimPolicy decided; acceptance is that claim
     # together with the named gaps, because the stages the policy cannot
     # see -- IMPORT, EXPLORE and the static plan -- raise their own blocking
     # gaps.  This is the conjunction the exit code below already tests,
     # published so a reader of result.json alone does not have to infer it
     # from two numbers.
     accepted: (($decided.claim == "SAT_CANDIDATE"
                 or $decided.claim == "UNSAT_CLOSED")
                and $gapCount == 0),
     blockingGapCodes: ($gaps.byCode // {}),
     # What each satisfying witness named, and whether the policy read it as a
     # finding or as freedom nobody accounted for. A reader asking "why is this
     # sat" gets the mechanism narrative here rather than having to rebuild it
     # from the model.
     witnessFindings: ($decided.witnessFindings // []),
     reportedFindings: ($decided.rootSpace.reportedFindings // []),
     # The whole policy decision, not a selection from it.  A consumer asking
     # which valuation the acceptance rests on, or what shape that witness
     # has, reads it here rather than opening the composition manifest to
     # find the claim this file was written from.
     rootSpace: ($decided.rootSpace // {}),
     # Which execution of the annotated target this claim is about: the one
     # the case declares and the composer anchored on.  A campaign answers
     # about one anchor, so there is no ledger of runners-up to publish.
     targetOccurrence: ($c.anchor // ""),
     valuations: ($r.valuations // [])}
  ' >"${campaign_final}/result.json"
  require_nonempty "campaign result" "${campaign_final}/result.json"

  # The replay's own provenance, off the census IMPORT published and the
  # session files it counted.  There is no folded result to measure.
  session_rows=$(jq -r -s '[.[].rows] | add // 0' \
    "${iteration_dir}/session_census.jsonl") || campaign_fail EMIT CAMPAIGN \
    "${iteration_dir}/session_census.jsonl" "the session census is malformed"
  session_bytes=$(find "${iteration_dir}/sessions" -type f \
    \( -name '*.jsonl' -o -name 'expressions.json' \) -printf '%s\n' \
    | awk '{n += $1} END {print n + 0}')
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
  # Same rule as campaign_write_gaps: these three grow with the
  # corpus -- one iteration manifest is already 72 KB on hdfs-11741, and the
  # campaign concatenates one per epoch -- so they travel as files.  The
  # provenance and the two counts are bounded and stay arguments.
  local manifest_scratch manifest_status=0
  manifest_scratch=$(mktemp -d \
    "${TMPDIR:-/tmp}/graphchecker-manifestargs.XXXXXX") || campaign_fail \
      EMIT CAMPAIGN "${campaign_final}" "no scratch for the run manifest"
  campaign_json_file "${manifest_scratch}/artifacts.json" \
    "${artifacts_json}" >/dev/null
  campaign_json_file "${manifest_scratch}/stages.json" \
    "${stages_json}" >/dev/null
  campaign_json_file "${manifest_scratch}/iterations.json" \
    "${iterations_json}" >/dev/null
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --arg root "${campaign_root}" \
    --arg final "${campaign_final}" \
    --slurpfile artifactDocuments "${manifest_scratch}/artifacts.json" \
    --argjson sessionRows "${session_rows}" \
    --argjson sessionBytes "${session_bytes}" \
    --slurpfile stageDocuments "${manifest_scratch}/stages.json" \
    --slurpfile iterationDocuments "${manifest_scratch}/iterations.json" '
    ($artifactDocuments[0] // []) as $artifacts |
    ($stageDocuments[0] // []) as $stages |
    ($iterationDocuments[0] // []) as $iterations |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RUN_MANIFEST",
     campaignRoot: $root,
     outputDir: $final,
     provenance: $provenance,
     iterations: $iterations,
     artifacts: $artifacts,
     metrics: {stageWallMillis: $stages,
               totalStageWallMillis: ([$stages[] | .wallMillis] | add // 0),
               sessionRows: $sessionRows,
               sessionBytes: $sessionBytes}}
  ' >"${campaign_final}/run-manifest.json" || manifest_status=$?
  rm -rf -- "${manifest_scratch}"
  [[ "${manifest_status}" -eq 0 ]] || campaign_fail EMIT CAMPAIGN \
    "${campaign_final}" "the run manifest could not be composed"
  require_nonempty "campaign run manifest" \
    "${campaign_final}/run-manifest.json"

  # Published here, not after the stage: the claim gates below leave this
  # shell with exit 2 or exit 3, so the epoch loop's own call to this helper
  # was unreachable on exactly the runs whose verdict a reader most needs --
  # lane17897h withheld on six gaps, and ${campaign_root}/final never
  # existed, so the harness read claim=MISSING for a run that had composed,
  # solved and decided.  Every completed epoch publishes, whatever the
  # claim.  The loop's call stays and is idempotent.
  campaign_publish_epoch_final "${iteration_dir}"

  gapCount=$(jq -r '.gapCount' "${campaign_final}/gaps.json")
  campaign_count EMIT GapLedger "${campaign_final}/gaps.json" \
    "the published blocking gap count" "${gapCount}"
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
  # Every blocking gap is a hard failure, whichever stage raised it.  The
  # telemetry array holds only the rows their own producer classed as unable
  # to change a chain, and each of those carries its reason there.
  [[ "${gapCount}" -eq 0 ]] || {
    jq -r '"[campaign] candidate withheld: claim=\(.claim), but the run named "
      + (.gapCount | tostring) + " BLOCKING gap(s); "
      + (.telemetryCount | tostring) + " diagnostic row(s) withhold nothing"' \
      "${campaign_final}/result.json" >&2
    echo "  named gaps: ${campaign_final}/gaps.json" >&2
    exit 3
  }
}

# A refinement this run owes and did not take, as a row the gap report classes
# like any other.  Stating it is the whole point: the divergent sessions are
# held for an epoch the campaign has not planned, so a reader of this run's
# verdict has to be able to see that it covers epoch e only.
campaign_publish_pending_refinement() {
  local iteration_dir=$1 iteration_id=$2 rows=$3
  jq -n -c --arg epoch "${iteration_id}" --argjson rows "${rows}" \
    '{schemaVersion: 1, sessionId: "",
      kind: "TOPOLOGY_DIVERGENCE", cls: "DIAGNOSTIC",
      subject: $epoch,
      detail: ("\($rows) topology divergence row(s) hold sessions for the "
               + "epoch after \($epoch), which this run did not plan")}' \
    >>"${iteration_dir}/campaign_gaps.jsonl" || true
}



# How many rows this iteration's replays published about a topology their plan
# had not addressed: a consumer endpoint paired with a producer endpoint the
# epoch catalog does not carry (INTERACTION-ID R-I3), or a path that reached a
# region the workload never retained (section 8 case 2).  Zero means the
# topology is closed.
# The same rule as campaign_count, at the one count this file computes rather
# than reads: `|| printf '0'` said "no divergences" for a jq that failed, which
# is the answer that ends the epoch loop.
campaign_topology_divergences() {
  local iteration_dir=$1 counted
  counted=$(campaign_divergence_rows "${iteration_dir}" | jq -r -s 'length')
  campaign_count EXPLORE TopologyDivergence "${iteration_dir}" \
    "the iteration's topology divergence count" "${counted}"
  printf '%s' "${counted}"
}

# Every TOPOLOGY_DIVERGENCE row of this iteration, from the sessions.
campaign_divergence_rows() {
  local sessions="$1/sessions"
  [[ -d "${sessions}" ]] || return 0
  find "${sessions}" -type f -name 'gaps.jsonl' -print0 \
    | LC_ALL=C sort -z | xargs -0 -r cat \
    | jq -c 'select(.kind == "TOPOLOGY_DIVERGENCE")' 2>/dev/null || true
}

# The regions a divergence says the retained set must grow to include.
#
# INTERACTION-ID section 8 distinguishes two causes, and the epoch loop has to
# act differently on them.  A path that reached a region the workload never
# retained -- lightweight entry hooks ran there, so it published activations
# and no decisions -- names that region here, and the next epoch must
# INSTRUMENT it before it replays or it will diverge identically.  Every other
# divergence is a pairing or a context the catalog did not carry: a new epoch
# over the same retained set.
campaign_retained_growth() {
  campaign_divergence_rows "$1" \
    | jq -r 'select((.detail // "")
               | test("retained set must grow: "))
             | (.detail | sub(".*retained set must grow: *"; "")
                        | split(" ") | .[0])' 2>/dev/null \
    | LC_ALL=C sort -u | paste -sd, - 2>/dev/null || true
}

# The session whose own trace is the recording of the next epoch, as the
# runtime named it on the divergent row.  Empty when this epoch's topology
# closed.  The harness never re-derives which replay diverged: one stage
# decides it and states it on the row.
campaign_seeding_replay() {
  local iteration_dir=$1
  local sessions="${iteration_dir}/sessions"
  [[ -d "${sessions}" ]] || { printf ''; return 0; }
  find "${sessions}" -type f -name 'gaps.jsonl' -print0 \
    | LC_ALL=C sort -z | xargs -0 -r cat \
    | jq -r -s 'first(.[] | select(.seedsNextEpoch == true)
        | .sessionId // empty) // empty' 2>/dev/null || printf ''
}


# The campaign publishes the LAST epoch at ${campaign_root}/final, so every
# reader keeps reading one path while each epoch keeps its own artifacts under
# its iteration directory.  A copy rather than a symlink: the published
# directory is what a later stage and the harness's own validation read, and a
# dangling link into an iteration directory is a worse failure than a copy.
campaign_publish_epoch_final() {
  local iteration_dir=$1
  local epoch_final="${iteration_dir}/final"
  local published="${campaign_root}/final"
  [[ -d "${epoch_final}" ]] || return 0
  rm -rf -- "${published}"
  mkdir -p "${published}"
  cp -a "${epoch_final}/." "${published}/"
}

# A campaign refines its topology at most this many times.  Three epochs is
# the owner's bound: the recording, one refinement, and one more in case the
# refinement itself found a new binding.  Beyond it the pending-refinement row
# stands and the campaign publishes what it has.
campaign_max_epochs=3

do_campaign() {
  local iteration=0 iteration_id="" parent="" retain="" previous_retain=""
  local iteration_dir
  local divergences=0 seeding_replay="" seeding_results=""
  campaign_root="${schedule_output_dir}"
  # Set per iteration inside the loop: each epoch composes into its own
  # final/, and the last one is published at ${campaign_root}/final.
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

  campaign_stage PREFLIGHT campaign_preflight
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
      "${retain}"
    campaign_stage "INSTRUMENT[${iteration}]" campaign_instrument \
      "${iteration_dir}"
    campaign_stage "REPLAY[${iteration}]" campaign_session_replay \
      "${iteration_dir}"
    campaign_stage "IMPORT[${iteration}]" campaign_import_session \
      "${iteration_dir}" "${iteration_id}"
    # A measurement run stops where its measurement is complete: the seed
    # session and its census, which IMPORT has just published for this epoch.
    # Declared, defaulted empty and validated in the workflow-key table, so
    # this reads a resolved key like every other bound rather than an
    # environment variable of its own.
    if [[ "${campaign_stop_after}" == "IMPORT" ]]; then
      campaign_log "stopping after IMPORT[${iteration}]: \
campaign_stop_after=IMPORT"
      return 0
    fi
    campaign_stage "EXPLORE[${iteration}]" campaign_explore \
      "${iteration_dir}" "${iteration_id}"
    campaign_publish_iteration_manifest "${iteration_dir}" "${iteration_id}" \
      "${parent}"
    # A flip that changed the topology found a new one.  The iteration loop
    # is how a campaign takes it into account: the replay's exact evidence
    # stays, and the next epoch is planned with the handoffs and occurrences
    # it ran -- the unplanned handoff already composes as its own family
    # with the one pair that replay delivered, and its decisions become that
    # epoch's obligations.  With nothing new found, the topology is closed
    # and this iteration is the one the campaign publishes from.
    # This epoch composes its own compatible paths whatever it learned.
    # Deferring COMPOSE until the topology closed was wrong twice over: a
    # campaign that found a divergence published no verdict about the paths
    # it *could* read, and when the next epoch's PLAN could not run -- it
    # looks for scheduler summaries under the previous iteration, which the
    # iteration-0000 layout does not publish -- the whole case exited 1 with
    # claim=MISSING.  An epoch's evidence is its own; a refinement that is
    # owed is a row that says so.
    divergences=$(campaign_topology_divergences "${iteration_dir}")
    # INTERACTION-ID section 8: two causes, two epochs.  A path that reached a
    # region the workload never retained needs that region INSTRUMENTED before
    # the next epoch replays, or the next epoch diverges identically; every
    # other divergence is a pairing or a context the catalog did not carry,
    # and the next epoch plans the same retained set again.
    retain=$(campaign_retained_growth "${iteration_dir}")
    if [[ "${divergences}" -gt 0 ]]; then
      if [[ -n "${retain}" ]]; then
        campaign_log "topology divergences: ${divergences}; the retained set \
must grow by ${retain}, so epoch $((iteration + 1)) instruments them before \
it replays"
      fi
      campaign_log "topology divergences: ${divergences}; epoch \
${iteration_id} composes its own paths and the refinement is pending"
      campaign_publish_pending_refinement "${iteration_dir}" \
        "${iteration_id}" "${divergences}"
    fi
    # Every epoch composes, solves, decides and emits its own evidence, into
    # its own final/.  Path merging never crosses epochs -- a path row carries
    # its topologyEpoch and the anchor key includes it -- so these are two
    # answers about two causal graphs, not one answer averaged over both.
    campaign_final="${iteration_dir}/final"
    campaign_stage "COMPOSE[${iteration}]" campaign_compose "${iteration_dir}"
    campaign_stage "SOLVE[${iteration}]" campaign_solve
    campaign_stage "DECIDE[${iteration}]" campaign_decide
    campaign_stage "EMIT[${iteration}]" campaign_emit "${iteration_dir}"
    campaign_publish_epoch_final "${iteration_dir}"

    # The seam the whole re-seeding turns on: epoch e+1 is planned from the
    # DIVERGENT REPLAY'S OWN trace, not from the original recording.  Getting
    # this input wrong would re-plan the old topology and loop; the seeding
    # replay is named on the row by the one stage that saw both.
    seeding_replay=$(campaign_seeding_replay "${iteration_dir}")
    if [[ -z "${seeding_replay}" ]]; then
      campaign_log "topology closed at ${iteration_id}"
      return 0
    fi
    if [[ "${retain}" == "${previous_retain}" ]]; then
      # The same retained set twice is the guard EPOCH2 named, now stated on
      # the quantity the next epoch actually varies: PLAN re-plans an epoch
      # through --retain-regions, so an epoch whose retained set did not grow
      # would instrument, replay and diverge identically, for ever.
      campaign_log "epoch e+1 would plan the same retained set as this epoch \
(${retain:-none}); the topology is not refining, publishing ${iteration_id}"
      return 0
    fi
    if [[ $((iteration + 1)) -ge "${campaign_max_epochs}" ]]; then
      campaign_log "topology divergence at ${iteration_id} seeds no further \
epoch: the campaign's bound of ${campaign_max_epochs} epoch(s) is reached"
      return 0
    fi
    campaign_log "topology divergence: epoch $((iteration + 1)) is seeded \
from replay ${seeding_replay}, retaining ${retain}"
    previous_retain="${retain}"
    parent="${iteration_id}"
    iteration=$((iteration + 1))
  done
  # The loop leaves only by one of the returns above or by exhausting
  # campaign_max_iterations, and an exhausted bound is not a verdict.  It used
  # to publish a CAMPAIGN_COVERAGE_GAPS document naming the deleted CLASSIFY
  # stage, over the top of the gaps.json EMIT had already written for the last
  # epoch it completed.  Nothing overwrites a published epoch now: the bound is
  # named and the run stops.
  die "the campaign reached campaign_max_iterations=${campaign_max_iterations} \
with a diverging topology; the last epoch it completed is published under \
${campaign_root}"
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
