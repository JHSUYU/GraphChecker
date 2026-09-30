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
  ./run_engine.sh --config FILE slice
  ./run_engine.sh --config FILE record
  ./run_engine.sh --config FILE config|validate
  ./run_engine.sh --config FILE --run-obligation \
      --graphchecker-jar JAR --graphchecker-jar-sha256 SHA -- \
      ID OBLIGATIONS CLASSES WORKER SESSIONS SEED_PLAN
  ./run_engine.sh help

Commands:
  campaign    Run the complete campaign for one configuration: validate, seed,
              then one iteration of plan/instrument/replay/import/explore
              (waves of obligations, growing the woven region set inside
              the wave) and compose/solve/decide/confirm/reproduce/emit.
              With causynth_static_root (an ad-hoc batch): one recording
              for every target of the spec, each target's slice as the
              build made it, then one such iteration per target
              (targets/<name>/)
  slice       Run SEED's static half alone: the setup adapter, then the
              seed analysis with the scope grown until nothing is added,
              into causynth_output_dir.  No workload runs and nothing is
              frozen (tools/adhoc/slice.sh scores what it writes)
  record      Pre-screen one workload for every target of the spec: one
              recording woven for all of them, each aggregated on its own
              static slice (causynth_static_root/<name>, frozen into
              targets/<name>/), and runtime/record-summary.json
              (tools/adhoc/prescreen.sh)
  config      Print the normalized workflow configuration
  validate    Validate required workflow configuration fields
  help        Print this help message

  --run-obligation
              Execute ONE obligation of a wave that some campaign planned,
              and nothing else.  This is what `campaign_worker_hosts` runs
              over ssh on a peer; the campaign generates the invocation into
              the obligation's own worker directory, so it is not a command
              to be typed.  The six positional arguments are exactly what
              campaign_obligation_worker takes.

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
# printed by `config`.  One table, so a key cannot be loadable but never
# reset, or overridable but never printed.
workflow_config_keys=(
  "campaign_setup_command CAUSYNTH_CAMPAIGN_SETUP_COMMAND krp -"
  "concolic_replay_command CAUSYNTH_CONCOLIC_REPLAY_COMMAND krp -"
  "concolic_worker_count CAUSYNTH_CONCOLIC_JOBS krp -"
  # The machines a wave's obligations may run on: a space-separated host
  # list.  Within a wave the obligations are independent -- each runs its own
  # solver and its own replay JVM, writes into its own worker directory and
  # publishes a session under an id it mints itself -- so the only thing a
  # second machine needs is the shared home every path in this configuration
  # already names.  Each host gets ${concolic_worker_count} slots, so the
  # pool is hosts x workers wide; the wave barrier (collect, gate, plan the
  # next wave) stays on the head.
  #
  # EMPTY -- the default -- runs every worker locally, no ssh anywhere.  A
  # host spelled `localhost` or as this machine's own hostname runs locally
  # too.
  "campaign_worker_hosts CAUSYNTH_CAMPAIGN_WORKER_HOSTS krp -"
  # The memory, in MB, one obligation takes on the host that runs it: its
  # solver JVM (which loads the session corpus) and its replay JVM together.
  # A slot starts an obligation only on a host with that much available
  # beyond what the obligations started there in the last ramp window will
  # still claim (campaign_await_host_memory), whichever campaign started
  # them -- the hosts are shared, and so is this accounting.  No default: the
  # need is the case's, measured, and a campaign that states none is refused.
  "obligation_memory_mb CAUSYNTH_OBLIGATION_MEMORY_MB krp -"
  # The heap, in MB, of the head's own engine JVMs -- analysis, planner,
  # import gate, composer, decision -- each of which holds the whole corpus.
  # Empty: the launcher's default.  A case whose corpus outgrows it states
  # its own (hdfs-11741: 202 sessions by wave 4 ran the planner out of 8 GB);
  # an obligation's solver keeps the default, since obligation_memory_mb
  # already accounts for it.
  "engine_memory_mb GRAPH_CHECKER_ENGINE_MEMORY_MB krp -"
  # The stage a measurement run stops after, once its measurement is
  # complete.  `IMPORT` returns successfully right after the IMPORT stage:
  # the seed session and its per-kind row census are what a runtime change
  # is gated on, and running EXPLORE..EMIT to reach them costs hours and
  # answers a different question.  Empty -- the default -- runs the whole
  # campaign.  Only these two values exist; validate_config refuses any
  # other, because a misspelling would silently run the full campaign and
  # look like a measurement run that never stopped.
  "campaign_stop_after CAUSYNTH_CAMPAIGN_STOP_AFTER krp -"
  "region_path_max_paths_per_region CAUSYNTH_REGION_PATH_MAX_PATHS_PER_REGION krp -"
  "region_path_max_flips_per_path CAUSYNTH_REGION_PATH_MAX_FLIPS_PER_PATH krp -"
  "region_path_max_tasks CAUSYNTH_REGION_PATH_MAX_TASKS krp -"
  "region_path_max_world_depth CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH krp -"
  "region_path_max_waves CAUSYNTH_REGION_PATH_MAX_WAVES krp 12"
  # 'true': the case asks about its declared occurrence only, and exploring
  # stops at the first admitted replay that observed the fatal there
  # (ExploreMain --stop-at-fatal).  Empty -- the default -- explores to the
  # fixed point.
  "region_path_stop_at_fatal CAUSYNTH_REGION_PATH_STOP_AT_FATAL krp -"
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
  "causynth_output_dir CAUSYNTH_OUTPUT_DIR krp -"
  "causynth_target_spec CAUSYNTH_TARGET_SPEC krp -"
  "causynth_communication_mappings CAUSYNTH_COMMUNICATION_MAPPINGS krp -"
  "causynth_loop_bounds CAUSYNTH_LOOP_BOUNDS krp -"
  # The backedge ceiling a retained loop the case did not narrow runs under.
  # The case states it (PIPELINE §0); every inherited application is
  # published as the catalog's DIAGNOSTIC gap row (INHERITED_K_L_<n>).
  # No default here: a campaign that states none is refused by name.
  "causynth_loop_default_bound CAUSYNTH_LOOP_DEFAULT_BOUND krp -"
  "causynth_lineage_roots CAUSYNTH_LINEAGE_ROOTS krp -"
  # How many classes of the lineage roots SEED may add to the case's scope
  # where the slice stops at it (plan.ScopeGrowth, SYMBOL-SCOPE §2.4),
  # nearest the throw first; 0 keeps the declared scope as it is.
  "causynth_scope_growth_budget CAUSYNTH_SCOPE_GROWTH_BUDGET krp 24"
  # The directory holding each target's static slice, <root>/<target
  # name>/, as `slice` wrote it (tools/adhoc/slice.sh): what `record` (a
  # pre-screen) and a batch campaign (an ad-hoc sweep's case) weave and
  # aggregate each target on, instead of a static pass of their own.
  "causynth_static_root CAUSYNTH_STATIC_ROOT krp -"
  # The wall clock a recording's workload may take after SEED's own: the
  # pre-screen's, and each native reproduction run's (REPRODUCE).
  "record_timeout_s CAUSYNTH_RECORD_TIMEOUT_S krp 300"
  # How many times REPRODUCE runs a confirmed witness natively.
  "reproduce_runs CAUSYNTH_REPRODUCE_RUNS krp 10"
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
  # The discovery artifacts, derived from causynth_output_dir in
  # initialize_config and printed by `config`: neither a workflow key nor an
  # override point, so every stage of a run -- and every peer of a wave --
  # reads the same file.  The static scope map is read by the workload JVM
  # (guard sites) and by PLAN and EXPLORE (flip sites); the region skeletons
  # by both weaves, so a replay stands on the recording's frame stack.
  "candidate_graph - rp -"
  "runtime_region_plan - rp -"
  "causynth_static_scope_map - rp -"
  "causynth_region_skeletons - rp -"
  "analysis_classes_dir - rp -"
  "schedule_output_dir - rp -"
  "schedule_max_jobs CAUSYNTH_SCHEDULE_MAX_JOBS krp -"
  # Per solver run, in milliseconds.  The composer runs z3 once per
  # valuation while it composes, so this is the budget of one of those runs.
  "solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS krp -"
  # The wall clock ONE focused replay may take, in seconds.  Without it a
  # replay JVM that deadlocks never returns, campaign_wait_workers holds its
  # wave open until an outer timeout kills the campaign, and every verdict
  # the wave already reached is lost.  A replay that exceeds this is that
  # obligation's own NOT_ADMITTED row, not the wave's death.  Defaulted
  # rather than required: an absent bound is exactly the unbounded wait this
  # exists to end.
  "replay_timeout_s CAUSYNTH_REPLAY_TIMEOUT_S krp 2400"
  # The wall clock the SEED replay may take, as a multiple of how long the
  # recording's workload ran (SEED times it), and never less than one
  # focused replay's replay_timeout_s.  Unbounded, a seed replay that
  # stopped progressing held its case to the case budget and died unnamed
  # (11 of h4's 111 cases, 7 of q5's 154, at 5400 s); a replay past this
  # fails the campaign at REPLAY naming it.  The seed replays the 09-29
  # sweeps finished took up to 38x their recording, one of 78 took 63x.
  "seed_replay_time_factor CAUSYNTH_SEED_REPLAY_TIME_FACTOR krp 40"
  # How many root valuations the composer enumerates around the recorded one.
  # The composer runs z3 per valuation while it composes, so this bounds the
  # solving a campaign does, not a separate stage's budget.
  "compose_max_valuations CAUSYNTH_COMPOSE_MAX_VALUATIONS krp 16"
  # The occurrence of the declared target site this campaign is about, as the case
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
    # A key this table does not carry is a refusal, not a comment: skipped, a
    # misspelling -- or a retired key -- would stay in a shipped config and
    # read as a setting that did nothing.
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
  causynth_target_spec=${causynth_target_spec:-@config/target.yaml}
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
  causynth_target_spec=$(resolve_path "${causynth_target_spec}")
  custom_jdk_home=$(resolve_path "${custom_jdk_home}")
  workload_work_dir=$(resolve_path "${workload_work_dir}" repo)
  java_bin=$(resolve_executable "${java_bin}")
  z3_bin=$(resolve_executable "${z3_bin}")

  if [[ -z "${project_classpath}" ]]; then
    project_classpath="${project_classes_dir}:${project_test_classes_dir}"
  else
    project_classpath=$(resolve_path_list "${project_classpath}")
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
  if [[ -n "${causynth_static_root}" ]]; then
    causynth_static_root=$(resolve_path "${causynth_static_root}")
  fi
  derive_output_paths
}

# The discovery artifacts, one layout under causynth_output_dir: the
# configured one, or a batch target's own (campaign_batch_target).
derive_output_paths() {
  candidate_graph="${causynth_output_dir}/candidate_dataflow_edges.jsonl.gz"
  causynth_static_scope_map="${causynth_output_dir}/static_scope_map.jsonl"
  runtime_region_plan="${causynth_output_dir}/runtime/concolic_region_plan.jsonl"
  causynth_region_skeletons="${causynth_output_dir}/region_skeletons.jsonl.gz"
  analysis_classes_dir="${causynth_output_dir}/instrumented-classes"
  schedule_output_dir="${causynth_output_dir}/schedule"
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

# The engine JVM, with the heap the case states (engine_memory_mb, else the
# launcher's 8 GB) -- on a campaign's head charged to its host for as long as
# a JVM takes to reach its size (campaign_head_charged).
engine_java() {
  campaign_head_charged "${engine_memory_mb:-8192}" 120 \
    env "$(config_env_assignment engine_memory_mb)" "${java_bin}" "$@"
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
  run_in_directory "${graphchecker_work_dir}" engine_java \
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
  for key in project_repo project_module_dir project_classes_dir project_classpath causynth_output_dir causynth_target_spec custom_jdk_home z3_bin workload_command trace_test causynth_loop_bounds causynth_loop_default_bound; do
    if [[ -z "${!key}" ]]; then
      echo "Missing workflow config value: ${key}" >&2
      missing=1
    fi
  done
  [[ ${missing} -eq 0 ]] || return 1
  # PIPELINE §0: no retained condition-controlled loop may inherit
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
  if [[ -n "${causynth_root_domains}" ]]; then
    require_file "declared root domains" "${causynth_root_domains}"
  fi
  # The bounds a campaign may not inherit. Left unstated, each would reach its
  # stage as a bare flag and be read back as some default the artifacts never
  # name -- a truncated schedule, an unbounded solve -- so a run without them
  # does not start.
  local key
  for key in solver_timeout_ms replay_timeout_s seed_replay_time_factor \
      schedule_max_jobs concolic_worker_count region_path_max_waves \
      compose_max_valuations causynth_loop_default_bound \
      obligation_memory_mb record_timeout_s reproduce_runs; do
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
  case "${region_path_stop_at_fatal}" in
    ''|true) ;;
    *) die "region_path_stop_at_fatal must be empty or true: \
${region_path_stop_at_fatal}" ;;
  esac
  [[ "${causynth_scope_growth_budget}" =~ ^[0-9]+$ ]] \
    || die "causynth_scope_growth_budget must be a non-negative integer: \
${causynth_scope_growth_budget}"
  # Every host in the worker list ends up inside an `ssh <host> ...` command,
  # so the spelling is checked before any work starts rather than discovered
  # by a shell on the far side.  Letters, digits, dot, dash and underscore is
  # a hostname; anything else -- a space is already a separator, and a quote,
  # a semicolon or a `$` would be somebody putting a command where a machine
  # belongs -- is refused by name.
  local worker_host
  for worker_host in ${campaign_worker_hosts}; do
    case "${worker_host}" in
      *[!A-Za-z0-9._-]*|-*|'')
        die "campaign_worker_hosts must be a space-separated list of host \
names: '${worker_host}'" ;;
    esac
  done
  [[ -z "${engine_memory_mb}" || "${engine_memory_mb}" =~ ^[1-9][0-9]*$ ]] \
    || die "engine_memory_mb must be empty or a positive integer: \
${engine_memory_mb}"
  local bound
  for bound in "${region_path_max_paths_per_region}" \
      "${region_path_max_flips_per_path}" "${region_path_max_tasks}"; do
    [[ -z "${bound}" ]] && continue
    case "${bound}" in
      *[!0-9]*|0) die "region path bounds must be positive integers: ${bound}" ;;
    esac
  done
  # A world depth of 0 is a bound too: the seed alone is cut from.
  case "${region_path_max_world_depth}" in
    ''|[0-9]|[0-9][0-9]) ;;
    *) die "region_path_max_world_depth must be a small non-negative \
integer: ${region_path_max_world_depth}" ;;
  esac
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
  # The scope SEED grew is the application scope of every pass after it.
  if [[ -s "$(campaign_grown_scope)/${scope_growth_manifest}" ]]; then
    system_properties+=("-Dcausynth.process.dirs=$(campaign_grown_scope)")
  fi
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
    system_properties+=(
      "-Dcausynth.communication.mappings=${causynth_communication_mappings}"
    )
  fi
  # The per-loop K_L (PIPELINE §2), declared by the campaign that owns the
  # workload. The declarations are read by the static pass that retains the
  # loops, so they are named here rather than inherited from whatever
  # environment happened to reach the JVM: a campaign whose declarations
  # silently failed to arrive would model an 8-body prefix and report nothing
  # about it. The requirement is unconditional, like the target specification
  # above it. A configured file that does not exist is a die, not a fallback.
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
  # One file, every weave: the CANDIDATE skeletons.  The recording and the
  # concolic pass both open their regions at its roots, whichever of them the
  # run turns out to exercise; a pass that read a different one would stand
  # on a different frame stack and address a different occurrence for the
  # same event.
  system_properties+=(
    "-Dcausynth.region.skeletons=${causynth_region_skeletons}"
  )
  # The lineage scope (plan.LineageScan), on the two weave runs and never on
  # discovery: every class of the application that starts, hands off or
  # runs work gets the lineage hooks, whatever the case analyses.
  if [[ -n "${causynth_lineage_roots}" ]] && [[ "${concolic_selected}" == true \
      || "${CAUSYNTH_TRACE_MODE:-}" == region-state ]]; then
    local lineage
    lineage=$(campaign_lineage_classes) \
      || die "the lineage scan failed over ${causynth_lineage_roots}"
    system_properties+=("-Dcausynth.lineage.dirs=${lineage}")
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
  run_in_directory "${graphchecker_work_dir}" engine_java \
    "${system_properties[@]}" \
    -cp "${graphchecker_jar}:${project_classpath}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    "${input_flag}" "${project_classes_dir}" \
    -x "${project_classpath}" \
    -o "${analysis_classes_dir}"
}

# The lineage scope's classes, scanned once per output directory from the
# application's own class roots (causynth_lineage_roots, colon-separated),
# leaving out what the analysis scope already holds.  Prints the directory.
campaign_lineage_classes() {
  local out="${causynth_output_dir}/lineage-classes"
  local -a roots=()
  if [[ ! -d "${out}" ]]; then
    IFS=: read -r -a roots <<<"${causynth_lineage_roots}"
    rm -rf -- "${out}.partial"
    mkdir -p "${out}.partial"
    run_java_main edu.uva.liftlab.graphchecker.plan.LineageScan \
      "${out}.partial" "${project_classes_dir}:$(campaign_grown_scope)" \
      "${roots[@]}" >&2 || return 1
    mv -- "${out}.partial" "${out}"
  fi
  printf '%s\n' "${out}"
}

# The classes SEED added to the case's scope, and why (plan.ScopeGrowth).
scope_growth_manifest=GROWN
campaign_grown_scope() {
  printf '%s\n' "${causynth_output_dir}/scope-classes"
}

# The static pass, with the scope grown where the slice stops at it until
# nothing is added or the budget is spent (SYMBOL-SCOPE §2.4).
campaign_analyze_grown_scope() {
  local grown changes summary
  grown=$(campaign_grown_scope)
  local -a roots=()
  rm -rf -- "${grown}"
  mkdir -p "${grown}"
  IFS=: read -r -a roots <<<"${causynth_lineage_roots}"
  while :; do
    do_analyze
    (( causynth_scope_growth_budget > 0 && ${#roots[@]} > 0 )) || return 0
    read -r changes summary < <(run_java_main \
      edu.uva.liftlab.graphchecker.plan.ScopeGrowth "${grown}" \
      "${causynth_output_dir}/scope_frontier.jsonl" \
      "${causynth_scope_growth_budget}" "${project_classes_dir}" \
      "${roots[@]}") \
      && [[ "${changes}" =~ ^[0-9]+$ ]] \
      || campaign_fail SEED ScopeGrowth "${grown}" "scope growth failed"
    campaign_log "scope growth: ${summary}"
    [[ "${changes}" != 0 ]] || return 0
  done
}

# slice: SEED's static half alone -- the case's scope copied in by the setup
# adapter, then campaign_analyze_grown_scope -- writing what SEED's does into
# causynth_output_dir: candidate_dataflow_edges.jsonl.gz,
# static_scope_map.jsonl, region_skeletons.jsonl.gz, scope_frontier.jsonl
# and scope-classes/.  No workload runs and nothing is frozen: an ad-hoc
# selection reads it (tools/adhoc/slice.sh, score.py).  The discovery pass's
# woven classes go: the recording weaves its own (do_workload).
do_slice() {
  validate_config >/dev/null
  [[ -z "${campaign_setup_command}" ]] || campaign_setup
  campaign_analyze_grown_scope
  rm -rf -- "${analysis_classes_dir}"
}

# The occurrence of the declared target site the case declares.  It is a config
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
  # those rows.
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
    --static-scope-map "${causynth_static_scope_map}" \
    --output "${composed_smt}" \
    --manifest "${composition_manifest}" \
    --solver-timeout-ms "${solver_timeout_ms}" \
    --max-valuations "${compose_max_valuations}" \
    --z3 "${z3_bin}" \
    "${selection[@]}"
}

# run_configured_workload <trace-dir> [seconds] [plant]: the workload in the
# recording weave (analysis_classes_dir, as SEED's static pass wove it), its
# trace into <trace-dir>, under a wall-clock bound of <seconds> when one is
# given (run_under_wall_clock_bound), with a native reproduction's plant
# (runtime.RecordingPlant) when one is named.
run_configured_workload() {
  local trace_dir=$1
  local -a workload_env bound=()
  workload_env=(
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    "CAUSYNTH_INSTRUMENTED_CLASSES_DIR=${analysis_classes_dir}"
    "CAUSYNTH_TRACE_OUTPUT_DIR=${trace_dir}"
    "CAUSYNTH_PLANT=${3:-}"
  )
  [[ -z "${2:-}" ]] || bound=(run_under_wall_clock_bound "$2")
  (cd "${workload_work_dir}" && "${bound[@]+"${bound[@]}"}" \
    env "${workload_env[@]}" bash -lc "${workload_command}")
}

do_workload() {
  [[ -n "${workload_command}" ]] || die "workload_command is empty"
  require_directory "workload working" "${workload_work_dir}"
  local trace_dir
  trace_dir=$(dirname "${runtime_region_plan}")
  require_file "candidate region skeletons" "${causynth_region_skeletons}"
  ensure_output_directory "${trace_dir}"
  # ONE recording: rich calls, branches, arguments and every declared-field
  # access over every candidate region, whose roots open the execution
  # index exactly where the replay's weave opens it (the same candidate
  # file).  Which regions the run exercised is read off this trace by the
  # aggregation below, which writes them to ${trace_dir}/region_skeletons.jsonl.
  CAUSYNTH_TRACE_MODE=region-state do_analyze
  local status=0 started=${SECONDS}
  run_configured_workload "${trace_dir}" || status=$?
  campaign_recorded_workload_s=$(( SECONDS - started ))
  (( status == 0 )) || campaign_fail SEED WORKLOAD "${trace_dir}" \
    "the recorded workload exited ${status}: the test failed, or its run" \
    "never opened a recording window (its output is above)"
  require_file "static scope map" "${causynth_static_scope_map}"
  campaign_target_slice="${candidate_graph},${causynth_static_scope_map},\
${causynth_region_skeletons}"
  run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" --test "${trace_test}" \
    --target "$(campaign_target_names | head -n 1)=${campaign_target_slice},\
${trace_dir}"
}

# The names of the targets the case's target spec declares, one per line.
campaign_target_names() {
  awk '$1 == "exception_target:" {print $2}' "${causynth_target_spec}"
}

# record: the pre-screen of one workload for every target of the case's
# spec (tools/adhoc/prescreen.sh), its workload bounded by record_timeout_s
# (campaign_record_batch).
do_record() {
  validate_config >/dev/null
  [[ -n "${causynth_static_root}" ]] \
    || die "record requires causynth_static_root"
  [[ -z "${campaign_setup_command}" ]] || campaign_setup
  campaign_record_batch "${record_timeout_s}"
}

# campaign_record_batch [seconds]: one recording for every target of the
# spec, each on its own static slice -- a pre-screen's `record`, a batch
# campaign's SEED.  Each target's slice (${causynth_static_root}/<name>/, as
# `slice` wrote it, tools/adhoc/slice.sh) is frozen into targets/<name>/:
# its candidate graph, scope map, frontier and communication gaps, and its
# line of the spec as target.yaml; a target without one is refused before
# any work.  ONE recording is woven for all of them (campaign_union_static)
# and its workload runs under <seconds> when given; then each target is
# aggregated on its own slice and on its view of the merged skeletons
# (campaign_region_view) into targets/<name>/runtime/.
# runtime/record-summary.json states the workload's exit, its seconds,
# whether the bound ended it, and each target's outcome
# (runtime.CausynthTraceRecorder: ACTIVATED, or the refusal).
campaign_record_batch() {
  local bound=${1:-}
  local trace_dir="${causynth_output_dir}/runtime" name static target
  local exit_status wall timed_out=false status started
  local -a names targets=()
  mapfile -t names < <(campaign_target_names)
  (( ${#names[@]} > 0 )) \
    || die "the target spec names no target: ${causynth_target_spec}"
  for name in "${names[@]}"; do
    require_file "static slice of ${name}" \
      "${causynth_static_root}/${name}/static_scope_map.jsonl"
  done
  for name in "${names[@]}"; do
    static="${causynth_static_root}/${name}"
    target="${causynth_output_dir}/targets/${name}"
    mkdir -p "${target}/runtime"
    cp -- "${static}/candidate_dataflow_edges.jsonl.gz" \
      "${static}/static_scope_map.jsonl" "${static}/scope_frontier.jsonl" \
      "${static}/communication_gaps.jsonl.gz" "${target}/"
    awk -v name="${name}" '$1 == "exception_target:" && $2 == name' \
      "${causynth_target_spec}" >"${target}/target.yaml"
    targets+=(--target "${name}=${target}/candidate_dataflow_edges.jsonl.gz,\
${target}/static_scope_map.jsonl,${target}/view_region_skeletons.jsonl.gz,\
${target}/runtime")
  done
  campaign_union_static "${names[@]}"
  for name in "${names[@]}"; do
    campaign_region_view "${causynth_static_root}/${name}" \
      >"${causynth_output_dir}/targets/${name}/view_region_skeletons.jsonl.gz"
  done
  CAUSYNTH_TRACE_MODE=region-state do_analyze
  ensure_output_directory "${trace_dir}"
  started=${SECONDS}
  run_capturing_status run_configured_workload "${trace_dir}" "${bound}"
  exit_status=${status}
  wall=$(( SECONDS - started ))
  campaign_recorded_workload_s=${wall}
  case "${exit_status}" in
    "${campaign_adapter_timeout_status}"|"${campaign_adapter_killed_status}")
      [[ -z "${bound}" ]] || timed_out=true ;;
  esac
  # A target the recording does not serve is its own outcome: the
  # aggregation's status says only whether any was served.
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" --test "${trace_test}" "${targets[@]}" \
    --summary "${trace_dir}/targets.json"
  jq -n --argjson exit "${exit_status}" --argjson wall "${wall}" \
    --argjson timedOut "${timed_out}" \
    --slurpfile outcomes "${trace_dir}/targets.json" \
    '{exit: $exit, wallSeconds: $wall, timedOut: $timedOut,
      targets: $outcomes[0].targets}' >"${trace_dir}/record-summary.json"
  rm -f -- "${trace_dir}/targets.json"
}

# campaign_region_view <static-slice>: the batch's merged skeletons as that
# slice's target labels them, gzipped on stdout -- what it is aggregated on.
# Its regions are every target's: the recording opened all of them, and a
# region of this target entered inside another target's is folded into that
# occurrence, where the aggregation finds it only if it knows the enclosing
# region (a check whose exception context BlockSender.<init> folds into
# another check's DataXceiver.readBlock was lost as NOT_IN_WINDOW).  Its
# labels are this target's: a region at a root this target plans keeps its
# own selection, and another's exception context is state to this target,
# so that no other target's failure context is taken for its own.
campaign_region_view() {
  zcat -- "${causynth_region_skeletons}" | jq -c --slurpfile own \
    <(zcat -- "$1/region_skeletons.jsonl.gz" | jq -s \
      "${campaign_region_key} map({(region_key): .selection}) | add // {}") \
    "${campaign_region_key}"'
    .selection = ($own[0][region_key]
      // (if .selection | startswith("EXCEPTION") then "STATE_CONTEXT"
          else .selection end))' | gzip -c
}

# What one region of a batch is: its root, the one region a weave opens
# there (a skeleton row naming no root is its id), as a jq function.
campaign_region_key='def region_key:
  if (.rootMethod // "") == "" then .regionId else .rootMethod end;'


# A batch's one recording weave (do_record): the case's skeleton file is
# every target's region skeletons merged by root -- the weave opens ONE
# region at a root, the first the file names there (a region's id is its
# authority and root, and two targets may root one method under two
# authorities) -- the first row's words kept and their lists united; its
# grown scope is every target's grown classes, the GROWN manifest one row
# per class.
campaign_union_static() {
  local name static grown
  grown=$(campaign_grown_scope)
  rm -rf -- "${grown}"
  mkdir -p "${grown}"
  local -a skeletons=()
  for name in "$@"; do
    static="${causynth_static_root}/${name}"
    skeletons+=("${static}/region_skeletons.jsonl.gz")
    [[ -d "${static}/scope-classes" ]] || continue
    cp -R -- "${static}/scope-classes/." "${grown}/"
    [[ ! -s "${static}/scope-classes/${scope_growth_manifest}" ]] \
      || cat "${static}/scope-classes/${scope_growth_manifest}" \
        >>"${grown}/${scope_growth_manifest}.all"
  done
  rm -f -- "${grown}/${scope_growth_manifest}"
  if [[ -s "${grown}/${scope_growth_manifest}.all" ]]; then
    awk -F'\t' '!seen[$1]++' "${grown}/${scope_growth_manifest}.all" \
      >"${grown}/${scope_growth_manifest}"
  fi
  rm -f -- "${grown}/${scope_growth_manifest}.all"
  zcat -- "${skeletons[@]}" | jq -c -s "${campaign_region_key}"'
    def unite($a; $b): reduce $b[] as $x ($a;
      if any(.[]; . == $x) then . else . + [$x] end);
    reduce .[] as $row ({}; .[$row | region_key] |=
      (if . == null then $row else
        reduce ($row | to_entries[] | select(.value | type == "array")) as $e
          (.; .[$e.key] = unite(.[$e.key] // []; $e.value)) end))
    | .[]' | gzip -c >"${causynth_region_skeletons}"
}

# ---------------------------------------------------------------------------
# Production campaign
#
# `campaign` is the one external entry point for a whole run. It validates the
# configuration, freezes the generation's provenance, records the stock-JVM
# seed, and then drives one iteration: plan -> union instrumentation -> one
# fresh same-JVM seed replay -> strict import -> waves of bounded parallel
# worker obligations, each wave growing the woven region set by what its
# replays exposed -> composition, solving, the claim and its publication.
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
# How long the recording's workload ran, in seconds (do_workload): the seed
# replay's bound is seed_replay_time_factor times it.
campaign_recorded_workload_s=""
# The campaign's target's static slice as the recording was aggregated on
# it, "<candidate-graph>,<scope-map>,<region-skeletons>" (SEED): REPRODUCE
# aggregates its runs on the same.
campaign_target_slice=""
# This iteration's task-set membership, decoded once by PLAN from the frozen
# schedule index (PIPELINE §3), one owner per check.
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

# A count a campaign DECIDES on, read back from an artifact.
#
# `[[ "${n}" -eq 0 ]]` is true for an empty string: bash evaluates the word as
# an arithmetic expression and an empty one is zero.  So a gate of the shape
# "no blocking gaps, carry on" would pass whenever the count could not be read
# at all -- an absent key, a summary with no JSON, a jq that failed.  A count
# is a decision: an unreadable one is a refusal naming the artifact, never a
# zero.
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

# A stage can exit 0 after writing nothing, and the next stage then reports a
# different, later problem. Every required output is checked for content and
# the check names the path.
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
# none is a manifest this stage may not publish a result from: a shell verdict
# here would be a second gate.
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

# Prints what the solver answered for each valuation the composer enumerated:
# its status and the assignment it was asked about, off the manifest's own
# valuation rows.
campaign_print_valuations() {
  local report=$1 count
  campaign_require_json "composition manifest" "${report}" \
    || return 1
  jq -e '.solver.valuations as $v
    | ($v | type) == "array"
    and all($v[];
      (.ordinal | type) == "number"
      and (.status | type) == "string"
      and (.assignment | type) == "object")
  ' "${report}" >/dev/null || return 1
  count=$(jq -r '.solver.valuations | length' "${report}")
  campaign_count SOLVE Valuations "${report}" \
    "the solver's valuation count" "${count}"
  while IFS=$'\t' read -r ordinal status assignment; do
    campaign_log "valuation=${ordinal} ${status}: ${assignment}"
  done < <(jq -r '
    .solver.valuations[]
    | [.ordinal, .status,
       (.assignment | to_entries | map("\(.key)=\(.value)") | join(" "))]
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
  # Read-only: campaigns start together on one snapshot, and a status that
  # refreshes the index takes index.lock from the others (v84 hdfs-17967
  # pathC: "failed to capture GraphChecker checkout state").
  if ! porcelain=$(git -C "${repo}" --no-optional-locks status --porcelain)
  then
    return 1
  fi
  if ! worktree=$( { printf '%s\n' "${porcelain}"
      printf '%s\n' "${porcelain}" | awk '{print $NF}' \
        | while IFS= read -r entry; do
            # A CLEAN TREE STATES NO ENTRY, and an empty one is not the
            # repository root.  `printf '%s\n' ""` emits one empty line, awk
            # prints an empty field for it, and `${repo}/` then exists -- so
            # without this skip a clean checkout would hash the WHOLE tree,
            # vendored sources and agent worktrees included.
            [[ -n "${entry}" ]] || continue
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
# in a condition suppresses errexit for everything it calls, so a failed
# `mvn package` inside it would leave a stale fat jar in place and the run
# would continue against binaries that are not the tree's.
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
      # it -- and not emitted: no consumer of these rows reads it.
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
      then {iterationId, externalWorkerCount,
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
  campaign_log "workers=${concolic_worker_count} maxJobs=${schedule_max_jobs} \
maxWaves=${region_path_max_waves} stopAtFatal=${region_path_stop_at_fatal:-false}"
  campaign_log "obligation pool: $(campaign_worker_slot_hosts | wc -l) slot(s) \
across host(s) ${campaign_worker_hosts:-$(hostname) (local only)}"
  campaign_log "replay scratch: \
${campaign_local_scratch_root:-<shared home, as before>}"
  # Every peer is reached once before the seed replay, not for the first time
  # somewhere inside wave 0 with a hundred obligations already planned.
  local worker_host
  for worker_host in ${campaign_worker_hosts}; do
    campaign_host_is_local "${worker_host}" && continue
    campaign_ssh "${campaign_ssh_options[@]}" -o ConnectTimeout=20 -- \
      "${worker_host}" \
      "test -x $(printf '%q' "${graphchecker_dir}/run_engine.sh")" \
      || die "campaign_worker_hosts names ${worker_host}, which this host \
cannot reach over ssh in batch mode, or which cannot see \
${graphchecker_dir}/run_engine.sh on the shared home"
  done
}

require_command_available() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

# How long this adapter run may take, in seconds, or empty for unbounded.
#
# One variable, read in one place (campaign_run_adapter), set by the two
# callers that have a bound to impose, around a replay:
# campaign_obligation_worker (replay_timeout_s) and campaign_session_replay
# (seed_replay_time_factor).  SETUP leaves it empty.
campaign_adapter_timeout_s=""
# The rule that bound came from, as its caller spells it: what a replay
# killed on the bound says it exceeded.
campaign_adapter_timeout_rule=""

# What an adapter that outlived its bound exits with.  124 is `timeout`'s own
# code for "the command timed out"; 137 is the command killed by SIGKILL,
# which is what --kill-after sends to anything that ignored the TERM.
campaign_adapter_timeout_status=124
campaign_adapter_killed_status=137

# How long a bounded adapter is given to die of SIGTERM before SIGKILL.
campaign_adapter_kill_grace_s=30

# One command under a wall-clock bound, in its own process group.
#
# `timeout` is not given --foreground, so it puts itself and the command in a
# NEW process group and signals that whole group on expiry: the adapter's
# login shell, the workload's launcher and the replay JVM it forked all
# receive it, which is the point -- a hung replay is a JVM several processes
# below the worker, and signalling only the shell would leave it running.
# Verified on coreutils 8.32: a grandchild of the bounded command is gone
# when it returns 124.
run_under_wall_clock_bound() {
  local seconds=$1
  shift
  timeout --kill-after="${campaign_adapter_kill_grace_s}s" "${seconds}s" "$@"
}

# ---------------------------------------------------------------------------
# REPLAY SCRATCH ON LOCAL DISK
#
# A focused replay stands up a MiniDFSCluster, and the cluster's name
# directories, edit logs and block files go wherever `test.build.data` and
# `java.io.tmpdir` point.  In the worker directory, on the shared home, every
# concurrent replay would be one more fsync-heavy little filesystem on one
# NFS mount.
#
# None of those bytes is READ or PUBLISHED by anything downstream.  The
# evidence a replay produces is its session under ${sessions}/<sessionId>/,
# its ${worker}/obligation_result.jsonl, its region results and its
# replay.log -- every one of them written straight to the shared home and
# none of them under temp/ or data/.  So only genuinely temporary bytes move;
# everything a later stage opens stays exactly where it was.
#
# The root is per USER and per RUN, because two campaigns may share a
# cluster, and the per-obligation leaf below makes it per OBLIGATION as well.
# Stated by the environment when the operator states one -- and an explicitly
# EMPTY CAUSYNTH_LOCAL_SCRATCH turns the whole thing off, which is why this
# tests for the variable being SET rather than for it being non-empty.
campaign_local_scratch_root=""

campaign_init_local_scratch_root() {
  local run_key
  if [[ -n "${CAUSYNTH_LOCAL_SCRATCH+x}" ]]; then
    campaign_local_scratch_root=${CAUSYNTH_LOCAL_SCRATCH}
    return 0
  fi
  # The campaign root is this run's unique name -- `mkdir frozen-inputs` is
  # the atomic claim on it -- so its digest is a run id no second campaign on
  # this cluster can collide with.
  run_key=$(printf '%s' "${campaign_root}" | sha256sum | cut -c1-16)
  campaign_local_scratch_root="/localtmp/$(id -un)/graphchecker/${run_key}"
}

# ---------------------------------------------------------------------------
# DISPATCHING ONE OBLIGATION TO ANOTHER MACHINE
#
# Every path this configuration names is absolute and on the shared home, so
# there is nothing to copy: the peer opens the same jar, the same woven
# classes, the same obligations file and the same sessions directory the head
# does.  What the peer must NOT do is work any of that out for itself.
# ---------------------------------------------------------------------------

# BatchMode: a peer that wants a password is a failure, not a prompt nothing
# will ever answer.  ServerAlive*: a connection that has silently died is
# noticed in ~90s rather than held open by the kernel for hours.  -n: stdin
# from /dev/null, so forty background ssh clients do not fight over the
# campaign's own stdin.
campaign_ssh_options=(
  -o BatchMode=yes
  -o ServerAliveInterval=30
  -o ServerAliveCountMax=3
  -n
)

# THE ssh of a campaign: one connection, retried while sshd REFUSES it.
#
# A round opens hundreds of connections at once and sshd's MaxStartups
# closes some during key exchange ("kex_exchange_identification: Connection
# closed by remote host").  A refused connection ran nothing on the far side,
# so it is retried with a jittered pause, for campaign_ssh_patience_s; a
# connection that was made and then failed -- or a command that failed -- is
# ssh's answer and is returned as it is, never re-run.  Every call site that
# runs one command over ssh goes through here.
campaign_ssh_refused='kex_exchange_identification|^ssh: connect to host|Connection closed by [0-9a-f.:]+ port|banner exchange'
campaign_ssh() {
  local started=${SECONDS} err rc
  err=$(mktemp "${TMPDIR:-/tmp}/graphchecker-ssh.XXXXXX") || return 255
  while true; do
    ssh "$@" 2>"${err}"
    rc=$?
    if (( rc == 255 )) && grep -qE "${campaign_ssh_refused}" "${err}" \
        && (( SECONDS - started < campaign_ssh_patience_s )); then
      sleep $((campaign_host_poll_s + RANDOM % campaign_host_poll_s))
      continue
    fi
    cat "${err}" >&2
    rm -f -- "${err}"
    return "${rc}"
  done
}

# How long the remote side has to poll for the connection that started it.
campaign_remote_watchdog_interval_s=5

# The margin over the declared budgets that the remote worker's own outer
# wall clock allows.
#
# The bound the OBLIGATION answers to is still `replay_timeout_s`, applied by
# campaign_obligation_worker around the replay exactly as it is locally; this
# outer one is a backstop against a remote side that is wedged somewhere
# else (a hung ssh channel, an NFS mount that stopped answering) and it is
# therefore the sum of the two budgets a worker is allowed to spend -- its
# solver run and its replay -- plus this margin for JVM start-up and the
# shared home.  It is not a policy about obligations; an obligation that
# reaches it has hit something no declared budget describes, and the wave
# fails naming the host.
campaign_remote_bound_margin_s=300

campaign_remote_worker_bound_s() {
  printf '%s\n' "$(( replay_timeout_s + (solver_timeout_ms + 999) / 1000 \
    + campaign_remote_bound_margin_s ))"
}

# How long the head waits for a finished remote worker's files to become
# visible to it.
#
# The peer wrote and CLOSED obligation_result.jsonl before its ssh exited,
# and the head opens it afterwards, so close-to-open consistency says the
# head sees the final contents -- of a file it can find.  Finding it is the
# part close-to-open does not settle: the head CREATED the worker directory,
# so it holds a cached listing of it and a cached negative lookup for the
# name the peer has since created, and it keeps both until its attribute
# cache for that directory expires.  Linux's NFS client caps that at
# `acdirmax`, 60 seconds by default, so the wait below is bounded at twice
# that rather than assumed away.
campaign_remote_visibility_wait_s=120

# Every workflow key's CURRENT value, under the environment override that
# sets it.
#
# This is what makes the peer's configuration the HEAD's configuration
# instead of a second derivation of it.  Two things would otherwise differ.
# FREEZE_TOOL rebinds `graphchecker_jar` to the campaign's private read-only
# copy, so a peer that resolved the key itself would load whatever is in
# target/ right now -- on this cluster the shared home means that is a
# DIFFERENT BUILD the moment anybody runs `mvn package`, and the run
# manifest's provenance would be a lie about half the wave.  And the
# workflow file itself lives on that same shared home and can be edited
# mid-run; forwarding the values means an edit cannot reach a worker,
# because every key it could change arrives already decided.
# One workflow key as its environment assignment, spelled by the table.
config_env_assignment() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    [[ "${config_key}" == "$1" ]] || continue
    printf '%s=%s\n' "${config_env}" "${!config_key-}"
    return 0
  done
  die "no workflow key $1"
}

campaign_remote_env_assignments() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    [[ -n "${config_env}" && "${config_flags}" == *k* ]] || continue
    printf '%s=%s\n' "${config_env}" "${!config_key}"
  done
}

# The script one peer runs for one obligation.
#
# Written into the worker directory on the shared home rather than squeezed
# through the ssh command line, which keeps the command line trivial (so the
# peer's login shell -- whatever it is -- has nothing to parse) and leaves
# the exact invocation beside the logs it produced.
#
# KILL SAFETY.  A remote JVM must not outlive the campaign, and sshd does not
# arrange that: with no pty, a remote command whose ssh client dies is simply
# reparented and keeps running, every process below it included.  Two things
# are therefore built in here.
#
#   1. The payload runs under `timeout`, which (not being given --foreground)
#      calls setpgid(0,0), so its own pid IS the new process group's id and
#      one `kill -<pgid>` reaches the replay JVM below it.
#   2. A watchdog polls this shell's parent.  That parent is the sshd session
#      process; when the connection drops, sshd goes and this shell is
#      reparented within about a second.  A parent that is no longer the one
#      we started with means the head is gone, and the watchdog kills the
#      payload's whole process group: TERM, then KILL after the same grace the
#      local bound uses.
#
# Comparing against the STARTING parent rather than against 1 on purpose: a
# user-level subreaper would adopt the orphan and pid 1 would never arrive.
campaign_write_remote_worker_script() {
  local script=$1 obligation_id=$2 obligations=$3 classes=$4 worker=$5
  local sessions=$6 seed_plan=$7
  local jar_sha assignment
  jar_sha=$(campaign_digest "${graphchecker_jar}")
  {
    printf '%s\n' '#!/usr/bin/env bash'
    printf '%s\n' \
      '# Generated by run_engine.sh for ONE obligation on ONE host.' \
      '# Read the campaign_write_remote_worker_script comment for why each' \
      '# line is here.  Regenerated per obligation; never edited by hand.' \
      'set -uo pipefail' \
      '' \
      'wrapper_pid=$$' \
      'wrapper_parent=$(awk "{print \$4}" "/proc/${wrapper_pid}/stat" \' \
      '  2>/dev/null || echo 1)' \
      ''
    printf 'timeout --kill-after=%ss %ss \\\n' \
      "${campaign_adapter_kill_grace_s}" "$(campaign_remote_worker_bound_s)"
    printf '  env \\\n'
    printf '    PATH=%q \\\n' "${PATH}"
    printf '    HOME=%q \\\n' "${HOME}"
    printf '    CAUSYNTH_LOCAL_SCRATCH=%q \\\n' "${campaign_local_scratch_root}"
    while IFS= read -r assignment; do
      printf '    %q \\\n' "${assignment}"
    done < <(campaign_remote_env_assignments)
    printf '  %q --config %q --run-obligation \\\n' \
      "${graphchecker_dir}/run_engine.sh" "${config_file}"
    printf '    --graphchecker-jar %q \\\n' "${graphchecker_jar}"
    printf '    --graphchecker-jar-sha256 %q \\\n' "${jar_sha}"
    printf '    -- %q %q %q %q %q %q \\\n' \
      "${obligation_id}" "${obligations}" "${classes}" "${worker}" \
      "${sessions}" "${seed_plan}"
    printf '  >%q 2>%q &\n' "${worker}/stdout.log" "${worker}/stderr.log"
    printf '%s\n' \
      'payload=$!' \
      '' \
      '(' \
      '  while kill -0 "${payload}" 2>/dev/null; do' \
      '    now=$(awk "{print \$4}" "/proc/${wrapper_pid}/stat" \' \
      '      2>/dev/null || echo 1)' \
      '    if [[ "${now}" != "${wrapper_parent}" ]]; then' \
      '      echo "remote worker: the campaign that started this is gone" \' \
      '        "(parent ${wrapper_parent} -> ${now}); killing process" \' \
      '        "group ${payload}" >&2'
    printf '%s\n' \
      '      kill -TERM -"${payload}" 2>/dev/null' \
      "      sleep ${campaign_adapter_kill_grace_s}" \
      '      kill -KILL -"${payload}" 2>/dev/null' \
      '      exit 0' \
      '    fi' \
      "    sleep ${campaign_remote_watchdog_interval_s}" \
      '  done' \
      ') &' \
      'watchdog=$!' \
      '' \
      'wait "${payload}"' \
      'status=$?' \
      'kill "${watchdog}" 2>/dev/null' \
      'exit "${status}"'
  } >"${script}"
}

# One obligation on one peer, and its files back.
campaign_dispatch_remote_obligation() {
  local host=$1 obligation_id=$2 obligations=$3 classes=$4 worker=$5
  local sessions=$6 seed_plan=$7
  local script="${worker}/remote-worker.sh"
  local status=0
  campaign_write_remote_worker_script "${script}" "${obligation_id}" \
    "${obligations}" "${classes}" "${worker}" "${sessions}" "${seed_plan}"
  # The payload writes stdout.log and stderr.log itself, on the shared home,
  # so the worker's own logs read the same whichever machine ran it.  What
  # lands here is ssh's OWN diagnostics -- a refused connection, a host key,
  # a peer that has no /bin/bash -- which would otherwise be the one part of
  # a failed remote obligation that nothing recorded.
  run_capturing_status campaign_ssh "${campaign_ssh_options[@]}" -- \
    "${host}" "exec /bin/bash $(printf '%q' "${script}")" \
    >"${worker}/ssh.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    campaign_log "obligation ${obligation_id} on ${host}: the remote worker \
exited ${status}; ssh's own output is in ${worker}/ssh.log"
    return "${status}"
  fi
  campaign_await_remote_result "${worker}" "${host}" "${obligation_id}" \
    "${sessions}"
}

# The peer's evidence, visible HERE.
#
# Bounded, never assumed: see campaign_remote_visibility_wait_s.  The
# directory is re-listed on each turn because it is the directory's cached
# listing, not the file's contents, that a fresh lookup has to get past.
campaign_await_remote_result() {
  local worker=$1 host=$2 obligation_id=$3 sessions=$4
  local result="${worker}/obligation_result.jsonl"
  local waited=0 session_id=""
  while [[ ! -s "${result}" ]]; do
    if [[ "${waited}" -ge "${campaign_remote_visibility_wait_s}" ]]; then
      campaign_log "obligation ${obligation_id} on ${host}: its worker \
returned successfully but ${result} is still not visible here after \
${waited}s; the shared home did not deliver what the peer wrote"
      return 1
    fi
    ls "${worker}" >/dev/null 2>&1 || true
    sleep 1
    waited=$((waited + 1))
  done
  session_id=$(jq -r '.sessionId // ""' "${result}" 2>/dev/null) || session_id=""
  # A terminal verdict the solver reached publishes no session, and says so
  # by naming none; only a session that was NAMED has to be here.
  [[ -n "${session_id}" ]] || return 0
  while [[ ! -d "${sessions}/${session_id}" ]]; do
    if [[ "${waited}" -ge "${campaign_remote_visibility_wait_s}" ]]; then
      campaign_log "obligation ${obligation_id} on ${host}: its result names \
session ${session_id} but ${sessions}/${session_id} is still not visible \
here after ${waited}s"
      return 1
    fi
    ls "${sessions}" >/dev/null 2>&1 || true
    sleep 1
    waited=$((waited + 1))
  done
  return 0
}

# Anything of THIS RUN still alive on a peer, ended.
#
# The primary guarantee is the watchdog inside each remote worker: a head
# that is killed -- `kill -TERM -<pgid>`, a crash, a severed network --
# reparents every remote wrapper within seconds and each one kills its own
# process group.  This is the second line, for the failure paths that are
# still in a position to do something: the campaign has decided to stop, and
# rather than trust the peers to notice, it says so.
#
# The pattern is the campaign root, which every process of this run carries
# on its command line (the wrapper script's path, the --run-obligation
# arguments, the `env` that fronts the adapter, and the replay JVM's own
# -Dcausynth.concolic.task.plan) and no other run does.  It is fed on STDIN
# rather than given as an argument, so the remote shell's own command line
# does not contain the pattern and pkill cannot match the process doing the
# matching.
campaign_reap_remote_workers() {
  local host reaped=0
  [[ -n "${campaign_worker_hosts}" ]] || return 0
  [[ -n "${campaign_root}" ]] || return 0
  for host in ${campaign_worker_hosts}; do
    campaign_host_is_local "${host}" && continue
    # Not campaign_ssh_options: that list carries -n, and this one speaks to
    # the far side through stdin.
    ssh -o BatchMode=yes -o ConnectTimeout=20 -- "${host}" 'bash -s' \
      >/dev/null 2>&1 <<EOF || true
pattern=$(printf '%q' "${campaign_root}")
pkill -TERM -u "\$(id -u)" -f "\${pattern}" 2>/dev/null || true
sleep ${campaign_adapter_kill_grace_s}
pkill -KILL -u "\$(id -u)" -f "\${pattern}" 2>/dev/null || true
EOF
    reaped=$((reaped + 1))
  done
  [[ "${reaped}" -eq 0 ]] || campaign_log "reaped this run's remote workers \
on ${reaped} host(s) matching ${campaign_root}"
}

campaign_run_adapter() {
  local label=$1
  local command=$2
  shift 2
  local -a adapter_env
  adapter_env=(
    # What one replay may use, which its JVM sizes its heap by; a peer's
    # replay gets it with the rest (campaign_remote_env_assignments).
    "$(config_env_assignment obligation_memory_mb)"
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    # Every adapter loads the same frozen artifact as analysis and scheduling.
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "$@"
  )
  # The bound, as a command prefix: an empty one is the unbounded call, with
  # no `timeout` in the picture at all.
  local -a bound=()
  if [[ -n "${campaign_adapter_timeout_s}" ]]; then
    bound=(run_under_wall_clock_bound "${campaign_adapter_timeout_s}")
    campaign_log "${label} adapter bound: ${campaign_adapter_timeout_s}s"
  fi
  campaign_log "${label} adapter: ${command}"
  (cd "${workload_work_dir}" \
    && "${bound[@]+"${bound[@]}"}" env "${adapter_env[@]}" \
      bash -lc "${command}")
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
  local spec_sha mappings_sha bounds_sha
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
# the production/test class trees, and the workload
# classpath string. The SEED additions (static catalog, region plan) are
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

# The stock-JVM seed: the static pass, then the one recording the workload
# stage owns. Its outputs are the campaign's static catalog and region plan.
campaign_seed() {
  local marker="${campaign_root}/.seed-started"
  : >"${marker}"
  campaign_analyze_grown_scope
  do_workload
  require_fresh "static candidate data-flow graph" "${candidate_graph}" \
    "${marker}"
  require_fresh "runtime region plan" "${runtime_region_plan}" "${marker}"
  campaign_seed_provenance
}

# The seed's static catalog and runtime region plan, digested into the
# campaign's provenance, and both seed skeleton views snapshot inside the
# campaign.  The configured analysis and runtime roots are already
# generation-local; the snapshot keeps the exact static/runtime pair beside
# the final provenance.
campaign_seed_provenance() {
  local catalog_sha plan_sha
  local skeleton_snapshot="${campaign_root}/seed-skeletons"
  mkdir -p "${skeleton_snapshot}"
  local skeleton
  for skeleton in "${causynth_region_skeletons}" \
      "$(dirname "${runtime_region_plan}")/region_skeletons.jsonl"; do
    [[ -f "${skeleton}" ]] && cp -p "${skeleton}" "${skeleton_snapshot}/" || true
  done
  if ! catalog_sha=$(campaign_digest "${candidate_graph}"); then
    campaign_fail SEED CAMPAIGN "${candidate_graph}" "digest failed"
  fi
  if ! plan_sha=$(campaign_digest "${runtime_region_plan}"); then
    campaign_fail SEED CAMPAIGN "${runtime_region_plan}" "digest failed"
  fi
  if ! campaign_provenance=$(jq -n \
    --argjson frozen "${campaign_provenance}" \
    --arg catalog "${candidate_graph}" \
    --arg catalogSha "${catalog_sha}" \
    --arg plan "${runtime_region_plan}" \
    --arg planSha "${plan_sha}" \
    '$frozen + {staticCatalog: {path: $catalog, sha256: $catalogSha},
                regionPlan: {path: $plan, sha256: $planSha}}'); then
    campaign_fail SEED CAMPAIGN "${campaign_root}" \
      "failed to extend immutable seed provenance"
  fi
}

# Schedule the immutable causal candidate closure used for union
# instrumentation, then derive the smaller value closure activated by the
# first linked replay. Producer and consumer regions in that replay still
# share one workload JVM so VM expressions cross their real RPC/field
# boundaries.
campaign_plan() {
  local iteration_dir=$1
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local seed_dir="${iteration_dir}/seed-replay"
  local seed_plan="${seed_dir}/execution_task_plan.jsonl"
  local frozen="${iteration_dir}/concolic_region_plan.jsonl"
  local role campaign_id region occurrence goal task worker
  local region_hash region_size

  require_nonempty "runtime region plan" "${runtime_region_plan}"
  cp -f "${runtime_region_plan}" "${frozen}"
  # The recording's schedule is frozen with the plan it was recorded beside:
  # the seed replay of this iteration is held to it (campaign_session_replay).
  local recorded_schedule
  recorded_schedule="$(dirname "${runtime_region_plan}")/schedule.jsonl"
  if [[ -s "${recorded_schedule}" ]]; then
    cp -f "${recorded_schedule}" "${iteration_dir}/recorded_schedule.jsonl"
  fi
  schedule_output_dir="${iteration_dir}"
  do_schedule
  campaign_plan_read "${iteration_dir}"
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

  # The seed replay runs the same plan: one file, linked, so a GROW append
  # reaches every reader through the one inode.
  mkdir -p "${seed_dir}"
  ln -f "${plan}" "${seed_plan}"

  # Member directories own path-closure artifacts, while every member points
  # at the same immutable linked replay plan.  Link it rather than copy it:
  # a copy per member would restate one plan once per member, most of what
  # a campaign writes.  Every writer here
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
}

# What an iteration's PLAN states that its later stages read, taken into the
# campaign's globals once per process that runs them (a batch target's
# campaign reads its PLAN again): the declared "first" occurrence resolved
# against the recording (RuntimeWorkflowDiscovery.FIRST), the frozen region
# plan, and the one task-set membership decode -- the index is frozen beside
# its rows and every later stage reads the rows.
campaign_plan_read() {
  local iteration_dir=$1
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  if [[ "${declared_target_occurrence}" == first ]]; then
    declared_target_occurrence=$(jq -r '.target.occurrenceId // ""' "${index}")
    [[ -n "${declared_target_occurrence}" ]] \
      || campaign_fail PLAN ConcolicScheduler "${index}" \
        "the schedule index names no target for the declared first occurrence"
    campaign_log "declared target first = ${declared_target_occurrence}"
  fi
  # Every later consumer reads this iteration's frozen copy, never the mutable
  # discovery output.
  runtime_region_plan="${iteration_dir}/concolic_region_plan.jsonl"
  if ! campaign_member_rows=$(campaign_decode_index_members "${index}"); then
    campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index has an invalid membership schema"
  fi
  [[ -n "${campaign_member_rows}" ]] || campaign_fail PLAN ConcolicScheduler \
    "${index}" "the region-path schedule index names no target member"
}

campaign_task_ids() {
  jq -r -s 'map(.taskId) | join(",")' "$1"
}

# One union instrumentation pass over the whole iteration plan, into the
# iteration's own class tree.  The tree is the weave of the plan as it
# stands: GROW appends task rows and runs this again, so the tree is cleared
# first, and it is only ever rewritten while every wave is settled and no
# replay reads it.
campaign_instrument() {
  local iteration_dir=$1
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local classes="${iteration_dir}/instrumented-classes"
  local ids
  ids=$(campaign_task_ids "${plan}")
  [[ -n "${ids}" ]] || campaign_fail INSTRUMENT CAMPAIGN "${plan}" \
    "the campaign plan published no task id"
  rm -rf -- "${classes}"
  # This weave's output; the recording weave stays analysis_classes_dir
  # (REPRODUCE runs it again).
  local analysis_classes_dir="${classes}"
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
# at a method the campaign never mentions, and REPLAY reports a failed
# workload method.  The class loader
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

# Why the last bounded campaign_replay was killed, or empty: its wall-clock
# bound, or a SIGKILL that came before the bound (the kernel's memory killer,
# an operator) -- hdfs-17960 v65-v67 read a 30-second 16 GB death as "exceeded
# replay_timeout_s=2400".  Read by the caller that set the bound; every other
# caller leaves the bound empty and this empty.
campaign_replay_killed=""

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
  local status=0 started=${SECONDS}
  campaign_replay_killed=""
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
    "CAUSYNTH_SCHEDULE_PREFIX=${campaign_schedule_prefix:-}" \
    "CAUSYNTH_STATIC_SCOPE_MAP=${causynth_static_scope_map}" \
    "CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root:+\
${campaign_local_scratch_root}/$(basename "${worker}")}" \
    >"${worker}/replay.log" 2>&1
  # The one exit code that is NOT the workload's own: this replay outlived
  # the wall clock its caller gave it and the process group was killed.  Said
  # here, as a fact of the run, and answered by the caller that set the bound
  # -- campaign_replay is not the place that owns what an unfinished
  # obligation means.
  if [[ -n "${campaign_adapter_timeout_s}" ]] \
      && { [[ "${status}" -eq "${campaign_adapter_timeout_status}" ]] \
        || [[ "${status}" -eq "${campaign_adapter_killed_status}" ]]; }; then
    local lived=$(( SECONDS - started ))
    if [[ "${status}" -eq "${campaign_adapter_timeout_status}" ]] \
        || (( lived >= campaign_adapter_timeout_s )); then
      campaign_replay_killed="exceeded ${campaign_adapter_timeout_rule}"
    else
      campaign_replay_killed="was killed (exit ${status}) after ${lived}s, \
inside its ${campaign_adapter_timeout_s}s bound: by its memory \
reservation (the replay log says so), the kernel's memory killer or an \
operator"
    fi
    campaign_log "replay role=${role} ${campaign_replay_killed} \
(exit ${status}); its session states no verdict: ${sessions}"
    # A caller whose replay is the iteration's only source of observed cases
    # cannot absorb a truncated one, and a killed JVM may well have published
    # rows before it died -- enough for the evidence gate below to pass on a
    # recording that stopped halfway.  Fail closed for those; the caller that
    # says `tolerated` owns the outcome and reads it back.
    if [[ "${region_results}" == required ]]; then
      campaign_fail REPLAY WORKLOAD "${sessions}" \
        "the concolic replay ${campaign_replay_killed}; what it published is \
a truncated run and its log is in ${worker}/replay.log"
    fi
    return 0
  fi
  # A workload whose target branch throws exits nonzero by design, so the gate
  # is the evidence it published and not its exit code.  That evidence is the
  # session: one JSONL file per row kind (CONTRACT-SPEC §2.1), and a session
  # with no activation row replayed nothing whatever the exit code said.
  if [[ "${region_results}" == required ]]; then
    local live
    live=$(find "${sessions}" -mindepth 2 -maxdepth 2 \
      -name activations.jsonl -size +0c -print -quit 2>/dev/null) || live=""
    [[ -n "${live}" ]] || campaign_fail REPLAY WORKLOAD "${sessions}" \
      "the concolic replay published no activation row (exit ${status}); the workload terminated before its selected regions ran and its exception is in ${worker}/replay.log"
    # Some region ran, but not the failure target's occurrence.  EXPLORE
    # still plans the TARGET member the kept slice names, and refuses it as
    # NO_OBSERVED_PATH_SEED -- stages and one JVM wave away from the workload
    # exception that caused it.  Name the missing target here instead, beside
    # the log that holds that exception.  A target occurrence publishes its
    # target row whether its path reached the throw or left before it (the
    # scope map's chain); reachedAnchor says which, and exploration flips the
    # decision it left by.
    local reached
    reached=$(campaign_target_reached "${sessions}" \
      "${causynth_static_scope_map}") \
      || campaign_fail REPLAY WORKLOAD "${sessions}" \
        "the target rows could not be read for target coverage"
    [[ -n "${reached}" ]] || campaign_fail REPLAY WORKLOAD "${sessions}" \
      "the concolic replay ran no TARGET_REACH occurrence (exit ${status}); no session published a target row of a TARGET_SITE of ${causynth_static_scope_map}; the workload's terminating exception is in ${worker}/replay.log"
  fi
  campaign_log "replay role=${role} exit=${status} sessions=${sessions}"
}


# The first target row a replay's sessions published at a TARGET_SITE of
# <scope-map> (its method's; a batch group's map names every target's), or
# "" when none did.
campaign_target_reached() {
  local sessions=$1 map=$2
  local -a rows=()
  mapfile -d '' rows < <(find "${sessions}" -mindepth 2 -maxdepth 2 \
    -name targets.jsonl -print0)
  (( ${#rows[@]} > 0 )) || return 0
  jq -r -n --slurpfile map "${map}" '
    [$map[] | select(.role == "TARGET_SITE") | .siteId
     | sub("#u[0-9]+$"; "")] as $methods
    | [inputs | .anchorSiteId
       | select(. as $site | any($methods[] + "#"; . as $method
           | $site | startswith($method)))]
    | first // ""' "${rows[@]}"
}

campaign_session_replay() {
  local iteration_dir=$1
  local seed="${iteration_dir}/seed-result"
  local plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  # CAUSYNTH_CONCOLIC_RESULTS names this replay, it is not a file:
  # RowRuntime derives the session id from the directory holding it, and the
  # rows themselves go to ${iteration_dir}/sessions/<sessionId>/.
  local results="${seed}/concolic_region_results.jsonl"
  local ids
  ids=$(campaign_task_ids "${plan}")
  # The seed replay is a focused replay like any other: one occurrence is
  # symbolic, everything else runs concretely, recording its exports and
  # minting v_H at every declared port.  It writes its rows per kind into its
  # own session directory (CONTRACT-SPEC §2.1), which is what IMPORT reads.
  campaign_sessions_dir="${iteration_dir}/sessions"
  mkdir -p "${campaign_sessions_dir}"
  # The seed replay is held to the RECORDING's schedule: the plan it runs
  # was built from that execution, so its occurrences are the recording's
  # in the recording's order.  A focused replay's prefix is its own task's,
  # beside its focus row (runtime.ScheduleLog#PREFIX_FILE).
  local recorded_schedule="${iteration_dir}/recorded_schedule.jsonl"
  [[ -s "${recorded_schedule}" ]] || recorded_schedule=""
  # Under a wall clock derived from the recording (seed_replay_time_factor):
  # the seed is the iteration's only source of observed cases, so a replay
  # past it is a campaign failure at REPLAY, named, not a recorded verdict.
  local bound=$(( seed_replay_time_factor * campaign_recorded_workload_s ))
  (( bound >= replay_timeout_s )) || bound=${replay_timeout_s}
  campaign_schedule_prefix="${recorded_schedule}" \
    campaign_adapter_timeout_s="${bound}" \
    campaign_adapter_timeout_rule="${bound}s, seed_replay_time_factor=\
${seed_replay_time_factor} x the recording's ${campaign_recorded_workload_s}s \
workload and at least replay_timeout_s=${replay_timeout_s}" \
    campaign_head_charged "${obligation_memory_mb}" 300 \
    campaign_replay worker "${plan}" "${ids}" \
    "${iteration_dir}/instrumented-classes" "${results}" "${seed}/focused"
}


# IMPORT: the replay's per-kind session files, checked and counted.
#
# A replay session writes one JSONL file per row kind under
# <iteration>/sessions/<sessionId>/ (CONTRACT-SPEC §2.1).  There is nothing to
# fold here: a reader of exports never parses attaches, the kinds are joined
# by Endpoint and Interaction id, and no stage has to re-parse a whole result
# to read one of them.  This stage checks that each session published every
# kind its readers open, and publishes the census.
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
    # schedule is censused with the rows and read by IMPORT, but no row
    # invariant is stated over it (contract.SessionDir#SCHEDULE).
    for kind in activations decisions exports attaches writes reads roots \
        targets gaps schedule; do
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
    [[ -s "${session}expressions.jsonl" ]] \
      || missing="${missing} ${name}/expressions.jsonl"
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
# A defect in a row is not one stage's problem: a row EXPLORE and COMPOSE
# each read as valid can still break the contract, and each stage that meets
# one reports something later and elsewhere.  contract.RowInvariants states
# the contract's own sentences, and the gate runs them
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
# A wave is where a focused session is produced, so it is where the contract
# is checked -- a BLOCKING violation fails the campaign at that wave, by name.
#
# ImportGateMain reads the session set of an ITERATION directory
# ({@code <iteration>/sessions}) and invariant 10 needs that directory's
# obligation workers, so the wave is given a directory of exactly that shape:
# the ITERATION's whole session roster, and EVERY wave of workers it has,
# each under its own name.  Nothing is copied and nothing under sessions/ is
# written.
#
# Every wave, not just this one: a focus row is what says a FOCUSED session
# ran in a world, and invariant 6 asks that of each session in the set.
# Linking this wave alone would leave every EARLIER wave's focused session
# reading as "no focus row this iteration".
#
# The whole roster, not the wave's own new sessions: invariant 1 is a
# SET-level rule -- exactly one session of the set states role SEED -- and a
# set built from the wave alone never holds the seed.  The wave's own
# sessions decide only WHETHER this gate runs, not what it reads.
#
# The gate directory sits OUTSIDE the waves it links, at
# ${iteration_dir}/import-gates/<wave>.  Built inside the wave it would hold
# a link to its own ancestor, and a walker that recurses would loop; the
# wave keeps its own summary (import_gate.json) and nothing else.
campaign_import_wave_gate() {
  local iteration_dir=$1 iteration_id=$2 wave_dir=$3 sessions=$4
  local before="${wave_dir}/sessions-before.txt"
  local gate="${iteration_dir}/import-gates/$(basename "${wave_dir}")"
  local name count=0
  require_file "wave session roster" "${before}"
  rm -rf -- "${gate}"
  mkdir -p "${gate}/sessions"
  local wave
  for wave in "${iteration_dir}"/obligations-*; do
    [[ -d "${wave}" ]] || continue
    ln -s "${wave}" "${gate}/$(basename "${wave}")"
  done
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


# The sessions that name one obligation, out of the corpus and under the
# worker that owned them.
#
# Two callers.  A replay killed on its bound has opened its session --
# SessionPublisher writes manifest.json at the OPEN -- and will never close
# it, so its rows state no verdict for the obligation the manifest names;
# Composer.settled reads exactly that pair as UNSTATED_VALUE/BLOCKING, and
# one hung JVM would withhold the whole candidate.  A replay that exposed a
# region ran without that region's hooks, and the re-run's session is the
# one the corpus keeps.  Either way the directory is MOVED under the worker,
# never deleted: it is the evidence of why the obligation's verdict is what
# it is, and the campaign keeps what it saw.
#
# Found by the manifest, which is the same lookup settled() does -- read the
# document and match one element of obligationIds exactly -- and never by
# diffing the session directory, because eight workers write into that one
# directory at once and every session but this obligation's belongs to
# somebody else.  A manifest that cannot be read is somebody else's, half
# written: skipped, not guessed at.
campaign_withdraw_sessions() {
  local obligation_id=$1 sessions=$2 quarantine=$3 why=$4
  local manifest session_dir session_id withdrawn=0
  # SessionDir.MANIFEST, one directory down: <sessions>/<sessionId>/.
  for manifest in "${sessions}"/*/manifest.json; do
    [[ -f "${manifest}" ]] || continue
    # `any(...; . == $id)` is an exact element match: an obligation id that
    # is a prefix of another's does not answer for it.
    jq -e --arg id "${obligation_id}" \
      'any((.obligationIds // [])[]; . == $id)' "${manifest}" \
      >/dev/null 2>&1 || continue
    session_dir=$(dirname "${manifest}")
    session_id=$(basename "${session_dir}")
    mkdir -p "${quarantine}"
    if mv -- "${session_dir}" "${quarantine}/${session_id}"; then
      withdrawn=$((withdrawn + 1))
      campaign_log "obligation ${obligation_id}: withdrew session \
${session_id} from ${sessions} to ${quarantine}/${session_id}: ${why}"
    else
      # Not the wave's death, and not silent either: the session stays where
      # COMPOSE will read it, and this line says what it is.
      campaign_log "obligation ${obligation_id}: could not withdraw session \
${session_id} from ${sessions}: ${why}; COMPOSE will read it"
    fi
  done
  if [[ "${withdrawn}" -eq 0 ]]; then
    campaign_log "obligation ${obligation_id}: no session under ${sessions} \
names it; nothing withdrawn"
  fi
}


# One obligation: solve it, replay it focused, record its verdict.
#
# The obligation names ONE focused occurrence, the decision it flips, the root
# assignments to apply at the mints and the answers to apply at the attaches
# (CONTRACT-SPEC §3).  The replay writes its rows into its own session
# directory, which is the only thing COMPOSE reads; this function's output is
# the one ObligationResult row that says which verdict it reached.
#
# A single obligation that could not be solved or replayed is that
# obligation's own result row, never the wave's death.
campaign_obligation_worker() {
  local obligation_id=$1 obligations=$2 classes=$3 worker=$4 sessions=$5
  local seed_plan=$6
  local outcome status=0
  # Its slot charged the host obligation_memory_mb: a local slot is a
  # subshell of the head, and its JVMs are not the head's.
  local campaign_head_charging=0
  local -a domain_args=()
  # The same declaration EXPLORE and COMPOSE read: an answer is only as free
  # as the root domains behind the arm that produces it.
  [[ -z "${causynth_root_domains}" ]] \
    || domain_args+=(--root-domains "${causynth_root_domains}")
  local result_row="${worker}/obligation_result.jsonl"
  # obligation_memory_mb budgets this JVM: it keeps the launcher's heap.
  engine_memory_mb="" run_capturing_status run_java_main \
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
  campaign_obligation_replay "${obligation_id}" "${classes}" "${worker}" \
    "${sessions}" "${seed_plan}"
}

# The replay half of an obligation: the solver's model, run focused, and the
# verdict the replay states for it.  The worker calls it once the solver has
# answered SAT_MODEL_READY; GROW calls it again for an obligation whose
# replay exposed a region, in the same worker directory, under the grown
# class tree.
#
# Two files, one shape each.  execution_task_plan.jsonl is the PLAN, whose
# rows the workload session opener decodes (ConcolicTaskPlan.load ->
# plan.ExecutionTask.decode): a focused replay runs the SEED's plan, hard
# linked here so a row GROW appends to the seed plan is in every worker's.
# The obligation's own focus row is focused_task.jsonl, written by the
# solver and read unchanged by a re-run.
campaign_obligation_replay() {
  local obligation_id=$1 classes=$2 worker=$3 sessions=$4 seed_plan=$5
  # Charged as a whole by whoever runs it: a slot, GROW, or CONFIRM.
  local campaign_head_charging=0
  local plan="${worker}/execution_task_plan.jsonl"
  local focus="${worker}/focused_task.jsonl"
  local results="${worker}/concolic_region_results.jsonl"
  local result_row="${worker}/obligation_result.jsonl"
  local outcome replay_tasks
  require_nonempty "obligation focus row" "${focus}"
  ln -f "${seed_plan}" "${plan}"
  replay_tasks=$(campaign_task_ids "${plan}")
  [[ -n "${replay_tasks}" ]] \
    || die "the seed plan names no task to replay: ${plan}"
  # Under a wall clock, because a replay JVM that never returns is not a slow
  # obligation but a stopped wave: campaign_wait_workers would wait on this
  # worker forever.  On expiry the whole process group goes (the JVM is a
  # grandchild of this worker) and this obligation records the same terminal
  # NOT_ADMITTED row a failed solver records -- one obligation's answer, not
  # the wave's death.
  campaign_sessions_dir="${sessions}" \
    campaign_adapter_timeout_s="${replay_timeout_s}" \
    campaign_adapter_timeout_rule="replay_timeout_s=${replay_timeout_s}" \
    campaign_replay worker "${plan}" "${replay_tasks}" "${classes}" \
      "${results}" "${worker}" tolerated
  if [[ -n "${campaign_replay_killed}" ]]; then
    campaign_log "obligation ${obligation_id}: \
replay ${campaign_replay_killed}"
    campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
      "${worker}/timed-out-sessions" "its manifest names this obligation \
and its rows state no verdict, which no later stage may read as a corpus \
session"
    jq -n -c --arg id "${obligation_id}" \
      --arg detail "replay ${campaign_replay_killed}" \
      '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
        verdict: "NOT_ADMITTED", sessionId: "", detail: $detail}' \
      >"${result_row}"
    return 0
  fi
  # THE REPLAY OWNS THE VERDICT.  RowRuntime.closeSession rewrites this file
  # with the rows FocusedReplay.results built -- the same rows it publishes
  # into the session, which is the evidence -- so nothing is stamped here.
  # What is checked is that the replay DID state one: a row still carrying
  # the solver's SAT_MODEL_READY means the replay published no verdict for
  # it, which is neither an admission nor a refusal.
  outcome=$(jq -r '.verdict // ""' "${result_row}")
  case "${outcome}" in
    ADMITTED|NOT_ADMITTED|UNSAT) ;;
    *) campaign_fail EXPLORE ObligationSolverMain "${result_row}" \
        "the replay of ${obligation_id} published no verdict for it \
(the row still states \"${outcome}\")" ;;
  esac
}


# ---------------------------------------------------------------------------
# THE WAVE'S WORK POOL
#
# Within a wave the obligations are independent: each runs its own solver,
# then its own replay JVM, writes into its own ${wave_dir}/${obligationId}/
# worker directory, and publishes a session under an id it mints itself.
# Nothing is merged until COMPOSE, so the only coordination a wave needs is
# "who takes the next one" and "has everybody finished".
#
# A POOL, not a batch barrier (which lets one slow obligation idle every
# other slot of its batch): one long-lived runner per slot, each pulling the
# next unclaimed obligation the moment its previous one returns.  A slot that
# frees takes the next obligation immediately; no slot waits on another.
#
# The claim is a `mkdir` on a per-index directory, which is the one atomic
# "exactly one of us gets this" primitive available to a set of plain
# background shells with no shared memory (and the one that also holds over
# NFS, which matters when the slots are on five machines).  Each slot's
# cursor only ever moves forward, so the whole wave costs at most
# slots x obligations mkdir attempts and no slot ever rescans behind itself.
# ---------------------------------------------------------------------------

# One slot's cursor into the wave's job list, and the index it last claimed.
# Every slot runs in its own background subshell, so these are private to it
# even though they are spelled as globals -- the same arrangement
# campaign_replay_killed already uses to answer its one caller.
campaign_claim_cursor=0
campaign_claimed_index=""

# Claims the next unclaimed obligation index for this slot, or returns 1 when
# the wave has none left.  The claim is the directory: `mkdir` fails with
# EEXIST for every slot but the one that created it, and that slot owns the
# index.
campaign_claim_next_obligation() {
  local queue_dir=$1 count=$2
  local index
  campaign_claimed_index=""
  while [[ "${campaign_claim_cursor}" -lt "${count}" ]]; do
    index=${campaign_claim_cursor}
    campaign_claim_cursor=$((index + 1))
    if mkdir "${queue_dir}/$(printf '%06d' "${index}")" 2>/dev/null; then
      campaign_claimed_index=${index}
      return 0
    fi
  done
  return 1
}

# Which host runs each slot, one per line.
#
# `campaign_worker_hosts` empty is one host, ${concolic_worker_count} slots,
# every worker local and no ssh anywhere.  A stated list gives
# ${concolic_worker_count} slots PER HOST, so the pool is as wide as hosts x
# workers.
#
# The hosts are interleaved rather than blocked, so the wave's opening fill
# -- which is every slot claiming at once -- lands round-robin across the
# hosts instead of loading the first host to capacity before the second sees
# any work.  The list starts at host [offset] (mod its length): a wave
# rotates it, so a one-obligation wave is not always the first host's.
campaign_worker_slot_hosts() {
  local offset=${1:-0}
  local -a hosts=()
  local slot index
  read -r -a hosts <<<"${campaign_worker_hosts}"
  [[ ${#hosts[@]} -gt 0 ]] || hosts=(localhost)
  for ((slot = 0; slot < concolic_worker_count; slot++)); do
    for ((index = 0; index < ${#hosts[@]}; index++)); do
      printf '%s\n' "${hosts[$(( (offset + index) % ${#hosts[@]} ))]}"
    done
  done
}

# This machine's own names, resolved once.  A host the operator spelled
# `localhost`, or spelled as this machine's own hostname, runs in a plain
# background subshell with no ssh in the picture at all.
campaign_local_host_names=""

campaign_host_is_local() {
  local host=$1
  if [[ -z "${campaign_local_host_names}" ]]; then
    campaign_local_host_names=" localhost $(hostname 2>/dev/null) \
$(hostname -s 2>/dev/null) "
  fi
  [[ -z "${host}" || "${campaign_local_host_names}" == *" ${host} "* ]]
}

# ---------------------------------------------------------------------------
# MEMORY PER HOST
#
# Every lift has 30 GB and every campaign's pool spans every lift, so what
# decides whether one more JVM fits on a host is the host, not the campaign.
# So every start asks the HOST first -- an obligation's slot, a campaign
# head's engine JVMs and replays, a fanout job (tools/adhoc/fanout.sh) --
# through a ledger all of them share, on a filesystem every lift mounts
# (tools/lib/gc-env.sh, CAUSYNTH_HOST_LEDGER), one directory per host:
#
#   ${campaign_host_gate_root}/<host>/lock       an mkdir lock, held for the
#                                                 few lines that read and
#                                                 append the ledger
#   ${campaign_host_gate_root}/<host>/starts     "<epoch> <mb> <ramp_s> <id>"
#                                                 per start still ramping
#   ${campaign_host_gate_root}/<host>/available  "<epoch> <mb>": MemAvailable,
#                                                 read at most every poll
#   ${campaign_host_gate_root}/<host>/total      "<mb>": MemTotal, read once
#
# A start of <mb> may go when MemAvailable, less what every start still in
# its ramp will grow into, leaves <mb> plus the host's reserve: the share of
# MemTotal above CAUSYNTH_HOST_MAX_USED_PCT (tools/lib/gc-env.sh), so no
# start leaves a host more than that full.  A JVM takes
# tens of seconds to reach its size and MemAvailable says nothing about
# memory a JVM has not touched yet, so a start is charged in full for its own
# ramp; after it, what it holds is in MemAvailable.  A start whose command
# returned inside its ramp is released (campaign_host_release), so a head's
# JVMs, one after another, are never charged twice.  A start that does not
# fit WAITS -- an obligation is the wave's and is never skipped -- and says
# so once.
# ---------------------------------------------------------------------------

# shellcheck source=tools/lib/gc-env.sh
source "${graphchecker_dir}/tools/lib/gc-env.sh"
campaign_host_gate_root=${CAUSYNTH_HOST_LEDGER}
# How long an obligation's start is charged in full: the time a solver JVM
# takes to load its corpus (about half a minute to 5 GB RSS).
campaign_host_ramp_s=60
# Whether this shell is a campaign's head, whose engine JVMs and replays are
# charged to its own host (do_campaign); an obligation's work is inside the
# obligation's charge.
campaign_head_charging=0
# The most of a host's memory a start may leave in use, in percent: what
# stays free is the page cache the JVMs read their jars and corpora through,
# the owner's own sessions, and the room JVMs past their ramp still grow into.
campaign_host_max_used_pct=${CAUSYNTH_HOST_MAX_USED_PCT}
[[ "${campaign_host_max_used_pct}" =~ ^[0-9]+$ ]] \
  && (( campaign_host_max_used_pct > 0 && campaign_host_max_used_pct <= 100 )) \
  || die "CAUSYNTH_HOST_MAX_USED_PCT must be a percentage in 1..100: \
${campaign_host_max_used_pct}"
# How often a waiting slot asks again, and how old a MemAvailable reading
# may be before it is read again.
campaign_host_poll_s=5
# How long a host may stay unreachable over ssh -- its memory unreadable, a
# worker's connection refused before it started -- before the obligation
# fails by name.  sshd refuses connections under a round's burst of them.
campaign_ssh_patience_s=300
# A lock older than this was left by a campaign that died holding it.
campaign_host_lock_stale_s=30

# The ledger's name for a host: this machine's short name for a local one,
# so a campaign on lift11 and one addressing lift11 over ssh share one entry.
campaign_host_key() {
  if campaign_host_is_local "$1"; then
    hostname -s
  else
    printf '%s\n' "$1"
  fi
}

# MemAvailable of one host, in MB.  Local: /proc/meminfo.  Remote: the same
# file over the same batch-mode ssh every remote obligation uses.
campaign_host_available_mb() {
  local host=$1
  local read_it="awk '/^MemAvailable:/ {print int(\$2 / 1024)}' /proc/meminfo"
  if campaign_host_is_local "${host}"; then
    bash -c "${read_it}"
  else
    campaign_ssh "${campaign_ssh_options[@]}" -o ConnectTimeout=20 -- \
      "${host}" "${read_it}"
  fi
}

# MemTotal of one host, in MB, read like campaign_host_available_mb.
campaign_host_total_mb() {
  local host=$1
  local read_it="awk '/^MemTotal:/ {print int(\$2 / 1024)}' /proc/meminfo"
  if campaign_host_is_local "${host}"; then
    bash -c "${read_it}"
  else
    campaign_ssh "${campaign_ssh_options[@]}" -o ConnectTimeout=20 -- \
      "${host}" "${read_it}"
  fi
}

# The host's MemTotal, from the ledger once it has been read: it never moves.
campaign_host_memory_total() {
  local host=$1 dir=$2 mb fresh
  if read -r mb 2>/dev/null <"${dir}/total" && [[ "${mb}" =~ ^[0-9]+$ ]]; then
    printf '%s\n' "${mb}"
    return 0
  fi
  mb=$(campaign_host_total_mb "${host}" | grep -E '^[0-9]+$' | tail -n 1) \
    || return 1
  [[ "${mb}" =~ ^[0-9]+$ ]] || return 1
  fresh=$(mktemp "${dir}/total.XXXXXX") || return 1
  printf '%s\n' "${mb}" >"${fresh}"
  mv -f -- "${fresh}" "${dir}/total"
  printf '%s\n' "${mb}"
}

# The host's MemAvailable, from the ledger when it is fresh enough.
campaign_host_memory_reading() {
  local host=$1 dir=$2 now=$3 at mb fresh
  if read -r at mb 2>/dev/null <"${dir}/available" \
      && [[ "${at}" =~ ^[0-9]+$ && "${mb}" =~ ^[0-9]+$ ]] \
      && (( now - at < campaign_host_poll_s )); then
    printf '%s\n' "${mb}"
    return 0
  fi
  mb=$(campaign_host_available_mb "${host}" | grep -E '^[0-9]+$' | tail -n 1) \
    || return 1
  [[ "${mb}" =~ ^[0-9]+$ ]] || return 1
  # A name of its own: the campaign's slots are subshells sharing $$, and
  # every campaign on every lift writes this ledger.
  fresh=$(mktemp "${dir}/available.XXXXXX") || return 1
  printf '%s %s\n' "${now}" "${mb}" >"${fresh}"
  mv -f -- "${fresh}" "${dir}/available"
  printf '%s\n' "${mb}"
}

# Takes the ledger's lock of one host directory: 0, or 3 while another start
# holds it (a lock older than campaign_host_lock_stale_s is broken).
campaign_host_lock() {
  local dir=$1 now=$2 lock_at
  mkdir "${dir}/lock" 2>/dev/null && return 0
  lock_at=$(stat -c %Y "${dir}/lock" 2>/dev/null || echo "${now}")
  if (( now - lock_at >= campaign_host_lock_stale_s )); then
    rmdir "${dir}/lock" 2>/dev/null || true
  fi
  return 3
}

# campaign_host_try_start <host> [need_mb] [ramp_s]: one try.  0 when the
# start may go now and is charged to the host, its row named in
# campaign_host_charge_id; 1 when it does not fit yet (why, in
# campaign_host_wait_reason); 2 when the host's memory cannot be read; 3 when
# another start holds the ledger's lock for the instant it takes to charge
# one.  An obligation's need and ramp are the defaults.
campaign_host_wait_reason=""
campaign_host_charge_id=""
campaign_host_try_start() {
  local host=$1 need=${2:-${obligation_memory_mb}}
  local ramp=${3:-${campaign_host_ramp_s}} key dir now available total
  local reserve charged=0 at mb row_ramp id kept=""
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  reserve=$(( total * (100 - campaign_host_max_used_pct) / 100 ))
  campaign_host_lock "${dir}" "${now}" || return 3
  if [[ -f "${dir}/starts" ]]; then
    while read -r at mb row_ramp id; do
      [[ "${at}" =~ ^[0-9]+$ && "${mb}" =~ ^[0-9]+$ \
        && "${row_ramp}" =~ ^[0-9]+$ ]] || continue
      (( now - at < row_ramp )) || continue
      charged=$((charged + mb))
      kept+="${at} ${mb} ${row_ramp} ${id}"$'\n'
    done <"${dir}/starts"
  fi
  if (( available - charged < need + reserve )); then
    printf '%s' "${kept}" >"${dir}/starts"
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${available} MB available and \
${charged} MB charged to starts still in their ramp; one needs ${need} MB \
and ${reserve} MB stay free (at most ${campaign_host_max_used_pct}% of \
${total} MB in use)"
    return 1
  fi
  campaign_host_charge_id="$(hostname -s).${BASHPID}.${now}.${RANDOM}"
  printf '%s%s %s %s %s\n' "${kept}" "${now}" "${need}" "${ramp}" \
    "${campaign_host_charge_id}" >"${dir}/starts"
  rmdir "${dir}/lock"
  return 0
}

# Drops one start's row: what it ran has returned, and whatever it held is
# back in MemAvailable.
campaign_host_release() {
  local host=$1 id=$2 dir kept
  dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
  until campaign_host_lock "${dir}" "$(date +%s)"; do
    sleep 0.$(( (RANDOM % 9) + 1 ))
  done
  if [[ -f "${dir}/starts" ]]; then
    kept=$(awk -v id="${id}" '$4 != id' "${dir}/starts")
    [[ -z "${kept}" ]] || kept+=$'\n'
    printf '%s' "${kept}" >"${dir}/starts"
  fi
  rmdir "${dir}/lock"
}

# campaign_head_charged <need_mb> <ramp_s> <command...>: a campaign head's
# own heavy start -- an engine JVM, the seed or the CONFIRM replay -- waits
# for room on the head's host, is charged there, and is released when it
# returns.  Outside a head it runs the command alone.  The command runs as a
# plain command, so errexit means inside it what it meant before: a failure
# that ends the shell leaves the charge to lapse with its ramp.
campaign_head_charged() {
  local need=$1 ramp=$2 id status
  shift 2
  if [[ "${campaign_head_charging}" != 1 ]]; then
    "$@"
    return
  fi
  # Its words go to stderr: the command's stdout is often its artifact
  # (ImportGateMain's summary JSON).
  campaign_await_host_memory localhost "" 0 "${need}" "${ramp}" >&2 || return
  id=${campaign_host_charge_id}
  "$@"
  status=$?
  campaign_host_release localhost "${id}"
  return "${status}"
}

# campaign_await_host_memory <host> [queue] [count] [need_mb] [ramp_s]:
# blocks until one start fits on the host, then charges it there: 0.  A slot
# waits BEFORE it claims, so a host without room holds no obligation while
# another host could run it (a10: one claim sat 30 min on a lift whose
# planner held 15 GB while eight lifts had 26 GB free).  1 once every
# obligation of the wave's queue is claimed -- nothing is left to wait for;
# without a queue (a GROW re-run, a head's own start) never.  2 when the
# host's memory cannot be read, the waiter's named failure.
campaign_await_host_memory() {
  local host=$1 queue_dir=${2:-} count=${3:-0} need=${4:-} ramp=${5:-}
  local said=false status=0 unread_since=""
  while true; do
    [[ -z "${queue_dir}" ]] \
      || (( $(find "${queue_dir}" -mindepth 1 -maxdepth 1 -type d | wc -l) \
        < count )) || return 1
    run_capturing_status campaign_host_try_start "${host}" "${need}" "${ramp}"
    case "${status}" in
      0) return 0 ;;
      2)
        # Unreadable is not "no room": sshd refuses some connections while a
        # round opens hundreds.  Waited out, stated, within the patience.
        [[ -n "${unread_since}" ]] || unread_since=${SECONDS}
        if (( SECONDS - unread_since >= campaign_ssh_patience_s )); then
          campaign_log "the memory of host ${host} could not be read for \
${campaign_ssh_patience_s}s"
          return 2
        fi
        campaign_host_wait_reason="the memory of ${host} could not be read"
        ;;
      3)
        # Another start is being charged: a moment, not a poll interval --
        # a wave's opening fill is every slot at once.
        sleep 0.$(( (RANDOM % 9) + 1 ))
        continue ;;
      *) unread_since="" ;;
    esac
    if [[ "${said}" == false ]]; then
      campaign_log "waiting for memory on ${host}: \
${campaign_host_wait_reason}"
      said=true
    fi
    sleep "${campaign_host_poll_s}"
  done
}

# One obligation, on the host its slot belongs to.  The local branch is a
# subshell under `set -euo pipefail`, its stdout and stderr in the worker
# directory.
campaign_run_obligation_on_host() {
  local host=$1 obligation_id=$2 obligations=$3 classes=$4 worker=$5
  local sessions=$6 seed_plan=$7
  if campaign_host_is_local "${host}"; then
    (
      set -euo pipefail
      campaign_obligation_worker "${obligation_id}" "${obligations}" \
        "${classes}" "${worker}" "${sessions}" "${seed_plan}"
    ) >"${worker}/stdout.log" 2>"${worker}/stderr.log"
  else
    campaign_dispatch_remote_obligation "${host}" "${obligation_id}" \
      "${obligations}" "${classes}" "${worker}" "${sessions}" "${seed_plan}"
  fi
}

# One slot: room on its host, then a claim, then the run, until the wave is
# empty.  A start charged just before the last claim went elsewhere is a
# ramp window of over-count, never a lost obligation.
#
# A failed obligation does not stop the slot: the remaining obligations of
# the wave still run, and the WAVE fails at the end.  The slot carries the
# failure out in its own exit status, which campaign_wait_workers reads.
campaign_wave_slot() {
  local host=$1 queue_dir=$2 count=$3 jobs_file=$4 wave_dir=$5
  local obligations=$6 classes=$7 sessions=$8 seed_plan=$9
  local status=0 gate job worker_dir
  campaign_claim_cursor=0
  while true; do
    gate=0
    campaign_await_host_memory "${host}" "${queue_dir}" "${count}" \
      || gate=$?
    (( gate != 1 )) || break
    (( gate == 0 )) || { status=1; break; }
    campaign_claim_next_obligation "${queue_dir}" "${count}" || break
    job=$(sed -n "$((campaign_claimed_index + 1))p" "${jobs_file}")
    [[ -n "${job}" ]] || continue
    worker_dir="${wave_dir}/${job}"
    printf '%s\n' "${host}" >"${worker_dir}/host.txt"
    if campaign_run_obligation_on_host "${host}" "${job}" \
          "${obligations}" "${classes}" "${worker_dir}" "${sessions}" \
          "${seed_plan}"; then
      campaign_log "obligation ${job}: host=${host} verdict=$(jq -r \
        '.verdict // "?"' "${worker_dir}/obligation_result.jsonl" \
        2>/dev/null || echo '?')"
    else
      status=1
      campaign_log "obligation ${job}: host=${host} DID NOT FINISH"
    fi
  done
  return "${status}"
}

# The whole wave, through the pool.
#
# Results are collected by the caller once the wave has SETTLED -- this
# returns only when every slot has returned -- so the frontier the next wave
# plans against is a complete one.
campaign_dispatch_wave() {
  local wave_dir=$1 obligations=$2 classes=$3 sessions=$4 seed_plan=$5
  shift 5
  local -a jobs=("$@")
  local -a pids=() slot_hosts=()
  local queue_dir="${wave_dir}/work-queue"
  local jobs_file="${wave_dir}/work-queue.txt"
  local host slot count=${#jobs[@]} status=0
  mkdir -p "${queue_dir}"
  printf '%s\n' "${jobs[@]}" >"${jobs_file}"
  # The wave's directory, which names its campaign and its wave, picks the
  # first host.
  while IFS= read -r host; do
    slot_hosts+=("${host}")
  done < <(campaign_worker_slot_hosts \
    "$(printf '%s' "${wave_dir}" | cksum | cut -d ' ' -f 1)")
  # A pool wider than the wave starts only the slots that can claim work; the
  # rest would claim nothing and return immediately anyway, and starting them
  # would put ${hosts} x ${workers} ssh connections on the wire for a wave of
  # three.
  for ((slot = 0; slot < ${#slot_hosts[@]} && slot < count; slot++)); do
    campaign_wave_slot "${slot_hosts[${slot}]}" "${queue_dir}" "${count}" \
      "${jobs_file}" "${wave_dir}" "${obligations}" "${classes}" \
      "${sessions}" "${seed_plan}" &
    pids+=("$!")
  done
  campaign_wait_workers "${pids[@]}" || status=1
  return "${status}"
}

# Where each of this wave's obligations ran, in one line.
campaign_log_wave_hosts() {
  local wave_dir=$1 wave=$2
  local distribution
  distribution=$(cat "${wave_dir}"/*/host.txt 2>/dev/null | LC_ALL=C sort \
    | uniq -c | awk '{printf "%s=%s ", $2, $1}') || distribution=""
  campaign_log "wave ${wave} ran on: ${distribution:-(nothing recorded)}"
}


# EXPLORE: waves of focused obligations until the frontier stops moving.
#
# One JVM plans the wave -- explore.ExploreMain reads every session this
# iteration has produced and writes the obligations the frontier is owed
# (obligations.jsonl) and the regions those sessions reached without their
# hooks (growth.jsonl) -- and one worker per obligation executes it.  A task
# is ONE focused occurrence (or one state-connected factor); everything else
# in that replay runs concretely, so there is no member roster to plan
# against: the sessions are the shared state, and a wave reads every session
# the waves before it wrote.  Once a wave's replays have settled, GROW takes
# up what they exposed (PIPELINE §7.8) before the next planner runs.
#
# The fixed point is both files empty: nothing left to ask for and nothing
# left to weave.  Both forced stops are coverage telemetry, never a campaign
# failure: a wave that proposes the same obligations, verdicts and exposures
# as the wave before it has learned nothing, and the wave bound is the
# budget the case stated.  An unexplored sibling path blocks a closed UNSAT
# and says nothing about a SAT candidate, so the stop is a gap row and the
# campaign goes on to publish what it did establish.
campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local sessions="${iteration_dir}/sessions"
  local results="${iteration_dir}/obligation_results.jsonl"
  local classes="${iteration_dir}/instrumented-classes"
  local seed_plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  local wave=0 pending=0 exposed=0 status=0 obligation_id wave_dir job
  local wave_signature="" previous_signature="" stop_kind="" stop_reason=""
  local obligations growth exposures
  local -a bound_args=() domain_args=() anchor_args=() jobs=()
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
  [[ -z "${region_path_max_world_depth}" ]] \
    || bound_args+=(--max-world-depth "${region_path_max_world_depth}")
  [[ -z "${region_path_stop_at_fatal}" ]] || bound_args+=(--stop-at-fatal)
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
    growth="${wave_dir}/growth.jsonl"
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
    # The planner states both files every wave; an empty obligations file is
    # the frontier closing, and a growth file with no EXPOSED_REGION row is
    # a closed region set.
    require_file "wave growth rows" "${growth}"
    exposures=$(campaign_exposures "${growth}")
    exposed=$(printf '%s' "${exposures}" | grep -c '' || true)
    jobs=()
    pending=0
    if [[ -s "${obligations}" ]]; then
      while IFS= read -r obligation_id; do
        [[ -n "${obligation_id}" ]] || continue
        jobs+=("${obligation_id}")
        pending=$((pending + 1))
      done < <(jq -r '.obligationId' "${obligations}")
    fi
    if [[ "${pending}" -eq 0 && "${exposed}" -eq 0 ]]; then
      campaign_log "wave ${wave}: no obligation open and no region exposed"
      break
    fi

    # Obligation identity is stable across waves, so an unchanged signature
    # over the ids, the verdicts recorded so far AND the exposures is a fixed
    # point the counts alone cannot see.
    wave_signature=$({
        printf '%s\n' "${jobs[@]}" | LC_ALL=C sort
        printf -- '--\n'
        jq -r '.verdict // ""' "${results}" | LC_ALL=C sort | uniq -c
        printf -- '--\n'
        printf '%s\n' "${exposures}"
      } | sha256sum | cut -d' ' -f1) \
      || campaign_fail EXPLORE CAMPAIGN "${results}" \
        "failed to summarise obligation wave ${wave}"
    stop_kind=""
    if [[ "${wave}" -ge "${region_path_max_waves}" ]]; then
      stop_kind=REGION_PATH_WAVE_BUDGET_REACHED
      stop_reason="the exploration loop reached its configured budget of \
region_path_max_waves=${region_path_max_waves} with ${pending} obligation(s) \
still open and ${exposed} region exposure(s) not yet woven"
    elif [[ "${wave_signature}" == "${previous_signature}" ]]; then
      stop_kind=REGION_PATH_CLOSURE_NO_PROGRESS
      stop_reason="wave ${wave} proposes the same ${pending} obligation(s) \
and ${exposed} exposure(s) as the wave before it with no new verdict"
    fi
    if [[ -n "${stop_kind}" ]]; then
      jq -n -c --arg kind "${stop_kind}" --arg detail "${stop_reason}" \
        --arg epoch "${iteration_id}" \
        '{schemaVersion: 1, sessionId: "", stage: "EXPLORE",
          kind: "ADMISSION_GAP", cls: "DIAGNOSTIC",
          subject: $kind, detail: $detail, topologyEpoch: $epoch}' \
        >>"${iteration_dir}/campaign_gaps.jsonl"
      campaign_log "exploration stopped: ${stop_kind}: ${stop_reason}"
      break
    fi
    previous_signature=${wave_signature}
    # Which sessions existed before this wave's replays and re-runs landed,
    # so the row contract below is checked over the wave's own and no other.
    campaign_session_roster "${sessions}" >"${wave_dir}/sessions-before.txt"
    if [[ "${pending}" -gt 0 ]]; then
      campaign_log "wave ${wave}: ${pending} obligation(s), \
slots=$(campaign_worker_slot_hosts | wc -l) \
(workers=${concolic_worker_count} per host, \
hosts=${campaign_worker_hosts:-local})"
      for job in "${jobs[@]}"; do
        mkdir -p "${wave_dir}/${job}"
      done
      status=0
      campaign_dispatch_wave "${wave_dir}" "${obligations}" "${classes}" \
        "${sessions}" "${seed_plan}" "${jobs[@]}" || status=1
      campaign_log_wave_hosts "${wave_dir}" "${wave}"
      if [[ "${status}" -ne 0 ]]; then
        # Whatever is still alive on a peer is this run's to end, before the
        # campaign exits and takes the head's own process group with it.
        campaign_reap_remote_workers
        campaign_fail EXPLORE CAMPAIGN "${wave_dir}" \
          "obligation wave ${wave} did not finish"
      fi
      # Every verdict this wave reached, appended once the wave settled, so
      # the next wave sees a complete frontier rather than a partial one.
      find "${wave_dir}" -mindepth 2 -maxdepth 2 \
        -name obligation_result.jsonl -print0 \
        | LC_ALL=C sort -z | xargs -0 -r cat >>"${results}"
    fi
    if [[ "${exposed}" -gt 0 ]]; then
      campaign_grow "${iteration_dir}" "${wave_dir}" "${classes}" \
        "${sessions}" "${seed_plan}" "${results}"
    fi
    # The row contract, over every session this wave added to the corpus --
    # its replays' and GROW's re-runs' -- before the next planner reads one
    # of their rows.
    campaign_import_wave_gate "${iteration_dir}" "${iteration_id}" \
      "${wave_dir}" "${sessions}"
    wave=$((wave + 1))
  done
  campaign_log "exploration stopped after ${wave} wave(s), \
$(wc -l <"${results}") obligation verdict(s)"
}

# The EXPOSED_REGION rows of a wave's growth.jsonl, one `obligation region
# session` line each, sorted.
campaign_exposures() {
  jq -r 'select(.kind == "EXPOSED_REGION")
         | [.obligationId, .regionId, .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

# GROW (PIPELINE §7.8): a region a replay reached without its hooks is
# planned, woven in, and the replay that exposed it is run again under the
# same world, so the next wave's closure sees the region's decisions and
# exports.
#
# ExploreMain names the exposures on the wave it planned.  Inside that wave,
# once its replays have settled and before the next planner reads the
# corpus: ExposedRegionPlanMain synthesises the task rows the exposures need
# (admissionBasis EXPOSED_BY); the rows are appended to BOTH plans --
# INSTRUMENT weaves the regions the iteration plan names, and a focused
# replay runs the seed plan; every worker's plan is a hard link of one of
# the two, so the rows reach every worker -- the iteration's class tree is
# woven again, and each exposing obligation's replay is re-run in its own
# worker directory.  The re-runs are the head's, one after another: a
# growth step re-runs a few replays, and a pool for them would be a second
# pool.
campaign_grow() {
  local iteration_dir=$1 wave_dir=$2 classes=$3 sessions=$4 seed_plan=$5
  local results=$6
  local growth="${wave_dir}/growth.jsonl"
  local rows="${wave_dir}/exposed_region_plan.jsonl"
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local status=0 obligation_id session
  # An exposure names the obligation whose replay is re-run.  One that names
  # none was exposed by the seed replay, and the seed is not re-run: the
  # recording reached that region too, so it is PLAN's to name, not GROW's.
  [[ -z "$(campaign_exposures "${growth}" | awk -F'\t' '$1 == ""')" ]] \
    || campaign_fail EXPLORE ExploreMain "${growth}" \
      "an EXPOSED_REGION row names no obligation; only a focused replay's \
exposure can be grown into"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain \
    --iteration "${iteration_dir}" \
    --static-scope-map "${causynth_static_scope_map}" \
    --growth "${growth}" \
    --output "${rows}" \
    >"${wave_dir}/grow-stdout.log" 2>"${wave_dir}/grow-stderr.log"
  [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE ExposedRegionPlanMain \
    "${wave_dir}/grow-stderr.log" \
    "the exposed-region planner failed with exit ${status}"
  require_nonempty "exposed region plan rows" "${rows}"
  cat "${rows}" >>"${plan}"
  campaign_log "$(basename "${wave_dir}"): grown by \
$(jq -r -s 'map(.regionId) | unique | join(",")' "${rows}") \
($(wc -l <"${rows}") task row(s)); weaving the grown plan"
  campaign_instrument "${iteration_dir}"
  # The exposing replays re-run side by side: each withdraws its own session
  # into its own worker, and the head's memory gate spaces their starts.
  # Their verdicts join the ledger, one file, once all have settled.
  local -a pids=() reruns=()
  while IFS=$'\t' read -r obligation_id session; do
    campaign_rerun_exposing_obligation "${iteration_dir}" "${wave_dir}" \
      "${obligation_id}" "${session}" "${classes}" "${sessions}" \
      "${seed_plan}" &
    pids+=("$!")
    reruns+=("${obligation_id}")
  done < <(campaign_exposures "${growth}" | cut -f1,3 | LC_ALL=C sort -u)
  campaign_wait_workers "${pids[@]}" || campaign_fail EXPLORE CAMPAIGN \
    "${wave_dir}" "a re-run of an exposing obligation did not finish"
  for obligation_id in "${reruns[@]}"; do
    campaign_record_rerun "${iteration_dir}" "${obligation_id}" "${results}"
  done
}

# One exposing obligation's focused replay, again, under the grown class
# tree.
#
# The worker directory is the obligation's own, from whichever wave proposed
# it: the focus row and the solver's model are there, and the re-run reads
# them unchanged.  What the exposing replay wrote -- its log, its verdict row
# and its session -- moves under the worker as before-<wave>/, kept as the
# evidence of why the region was grown and out of the corpus, where COMPOSE
# would otherwise read a session that ran without the region's hooks.  Its
# verdict joins obligation_results once every re-run of the wave has settled
# (campaign_record_rerun).
campaign_rerun_exposing_obligation() {
  local iteration_dir=$1 wave_dir=$2 obligation_id=$3 session=$4 classes=$5
  local sessions=$6 seed_plan=$7
  local worker aside file
  worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
    "${obligation_id}") || exit 1
  aside="${worker}/before-$(basename "${wave_dir}")"
  mkdir "${aside}" || campaign_fail EXPLORE CAMPAIGN "${aside}" \
    "obligation ${obligation_id} was already re-run for this wave"
  campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
    "${aside}/sessions" "it exposed a region that is woven now, and the \
re-run's session stands in its place"
  [[ ! -e "${sessions}/${session}" ]] || campaign_fail EXPLORE CAMPAIGN \
    "${sessions}/${session}" "the exposing session ${session} does not name \
obligation ${obligation_id}, so it was not withdrawn from the corpus"
  for file in replay.log concolic_region_results.jsonl \
      obligation_result.jsonl stdout.log stderr.log; do
    [[ ! -e "${worker}/${file}" ]] || mv -- "${worker}/${file}" "${aside}/"
  done
  printf 'localhost\n' >"${worker}/host.txt"
  campaign_await_host_memory localhost \
    || campaign_fail EXPLORE CAMPAIGN "${worker}" \
      "the re-run of ${obligation_id} found no readable memory on the head"
  (
    set -euo pipefail
    campaign_obligation_replay "${obligation_id}" "${classes}" "${worker}" \
      "${sessions}" "${seed_plan}"
  ) >"${worker}/stdout.log" 2>"${worker}/stderr.log" \
    || campaign_fail EXPLORE CAMPAIGN "${worker}" \
      "the re-run of ${obligation_id} did not finish"
}

# The one worker directory of an obligation, with its focus row.
campaign_obligation_worker_dir() {
  local iteration_dir=$1 obligation_id=$2 worker
  worker=$(find "${iteration_dir}" -mindepth 2 -maxdepth 2 -type d \
    -path "*/obligations-*/${obligation_id}" | LC_ALL=C sort)
  [[ -n "${worker}" && "${worker}" != *$'\n'* \
      && -s "${worker}/focused_task.jsonl" ]] \
    || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}" \
      "the exposing obligation ${obligation_id} has no one worker with a \
focus row: ${worker:-none}"
  printf '%s\n' "${worker}"
}

# A re-run's verdict replaces the obligation's row in the ledger.
campaign_record_rerun() {
  local iteration_dir=$1 obligation_id=$2 results=$3 worker
  worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
    "${obligation_id}") || exit 1
  jq -c --arg id "${obligation_id}" 'select(.obligationId != $id)' \
    "${results}" >"${results}.tmp"
  cat "${worker}/obligation_result.jsonl" >>"${results}.tmp"
  mv -- "${results}.tmp" "${results}"
  campaign_log "obligation ${obligation_id}: re-run under the grown tree, \
verdict=$(jq -r '.verdict // "?"' "${worker}/obligation_result.jsonl")"
}


# Gap rows this iteration's stages wrote outside a session live in one file,
# ${iteration_dir}/campaign_gaps.jsonl, appended by whoever raises them and
# read once by EMIT.  Nothing collects or truncates it.
#
# Session gap rows stay where the replay wrote them: EMIT reads them straight
# out of the session directories, because a GapRow states its own class and
# nothing between the runtime and the report is in a position to change it.

campaign_publish_iteration_manifest() {
  local iteration_dir=$1 iteration=$2
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local plan="${iteration_dir}/execution_task_plan.jsonl"
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
  # What this iteration imported and explored, digested from the two
  # artifacts its own stages wrote before this point: the manifest is
  # published after EXPLORE and before COMPOSE, so the census IMPORT required
  # and the verdicts EXPLORE appended are what it commits to.
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
# declared target site a campaign answers about is the case's to state, so
# there is no fan-out over observed occurrences here and nothing to elect
# afterwards: the composer reads every session this iteration produced,
# factorizes the paths that reach the declared anchor, and writes one
# candidate.smt2 beside one manifest.
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
# There is one anchor and therefore one claim, and no ranking of observed
# occurrences: which execution of the declared target site the campaign is about
# is the case's declaration, and the claim about it is whatever its own
# formula decided.
campaign_decide() {
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${composition_manifest}"
  campaign_print_valuations "${composition_manifest}" \
    || campaign_fail DECIDE ComposeMain "${composition_manifest}" \
      "the solver result states no valid valuation rows"
  jq -r '"  anchor=\(.anchor // "") finalStatus=\(.finalStatus // "")"
    + " claim=\(.solver.campaignClaim.claim // "")"
    + " blockers=\(.solver.campaignClaim.blockerCount // 0)"' \
    "${composition_manifest}"
}

# CONFIRM: a SAT claim, checked by one replay (PIPELINE §10).
#
# SAT says the model satisfies the formula; CONFIRM says the program agrees:
# one run takes every edge the model chose, with the moved roots at the
# model's values, and observes the fatal at the anchor.  When the selected
# session is that run -- every chosen arm its own delivery -- ConfirmMain
# says so (realized.json) and nothing is replayed.  Otherwise
# ConfirmMain writes what an obligation replay is handed -- a focus row that
# plants the model's roots and flips nothing, the selected session's
# schedule UNHELD (every event is the rest; only a WAKE still waits for
# what it followed), and the edges the model chose -- and the
# replay runs through campaign_obligation_replay exactly as an obligation
# does, into its own sessions directory under final/confirm.  The verdict is
# read off the session it published (ConfirmMain --sessions): ADMITTED (the
# roots were planted and the anchor was reached), a published gap file with
# no CONFIRM_MISMATCH, and a target row AT THE CLAIM'S ANCHOR occurrence that
# reached it and observed the fatal -- an occurrence id only the Java address
# computes, so the decision is Java's.  The recorded order is not what the
# claim says, so it is not held (a divergence stays a diagnostic gap of the
# session); the model's order is, by the ORDER rows of
# expected_edges.jsonl (runtime.Confirmation), and an ORDER the run cannot
# hold is a CONFIRM_MISMATCH (PIPELINE §10).  Every other
# outcome -- a refused task, a replay that published no verdict -- is
# "unconfirmed, because ...": EMIT downgrades the claim,
# the campaign does not fail.  Only a SAT_CANDIDATE is confirmed; any other
# claim has nothing to confirm and the stage says so.
campaign_confirm() {
  local iteration_dir=$1
  local claim confirm_dir="${campaign_final}/confirm"
  local worker sessions status=0 reason
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  if [[ "${claim}" != SAT_CANDIDATE ]]; then
    campaign_log "claim=${claim}: nothing to confirm"
    return 0
  fi
  [[ ! -e "${confirm_dir}" ]] \
    || die "the confirmation directory already exists: ${confirm_dir}"
  worker="${confirm_dir}/worker"
  sessions="${confirm_dir}/sessions"
  mkdir -p "${worker}" "${sessions}"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${iteration_dir}" \
    --claim "${campaign_final}/claim.json" \
    --manifest "${composition_manifest}" \
    --output "${worker}" >"${confirm_dir}/confirm.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    reason=$(grep -m 1 'CONFIRM refused:' "${confirm_dir}/confirm.log" \
      || grep -v -E '^[[:space:]]+at ' "${confirm_dir}/confirm.log" \
        | tail -n 1)
    campaign_confirm_verdict false \
      "${reason:-ConfirmMain exited ${status}}" "" \
      >"${campaign_final}/confirm.json"
  elif [[ -s "${worker}/realized.json" ]]; then
    # The selected session already took every edge the model chose, with
    # the moved roots at the model's values, and observed the fatal: that
    # run is the confirmation, and a replay of its world would test only
    # whether a race the order does not hold goes the same way twice.
    jq -c '.' "${worker}/realized.json" >"${campaign_final}/confirm.json"
  else
    # The replay, exactly as an obligation's.  A campaign_fail inside it
    # ends a wave; here, in a subshell, it ends the confirmation as "no
    # verdict", which is one more way of not agreeing with the model.
    ( campaign_head_charged "${obligation_memory_mb}" 300 \
        campaign_obligation_replay CONFIRM \
        "${iteration_dir}/instrumented-classes" "${worker}" "${sessions}" \
        "${iteration_dir}/seed-replay/execution_task_plan.jsonl" ) \
      >>"${confirm_dir}/confirm.log" 2>&1 || status=$?
    if [[ "${status}" -ne 0 ]]; then
      campaign_confirm_verdict false "the confirmation replay published no \
verdict (exit ${status}); its log is ${confirm_dir}/confirm.log" "" \
        >"${campaign_final}/confirm.json"
    else
      run_capturing_status run_java_main \
        edu.uva.liftlab.graphchecker.explore.ConfirmMain \
        --claim "${campaign_final}/claim.json" --output "${worker}" \
        --sessions "${sessions}" >"${campaign_final}/confirm.json" \
        2>>"${confirm_dir}/confirm.log"
      [[ "${status}" -eq 0 ]] || campaign_confirm_verdict false "the \
confirmation decision exited ${status}; its log is \
${confirm_dir}/confirm.log" "" >"${campaign_final}/confirm.json"
    fi
  fi
  require_nonempty "confirmation" "${campaign_final}/confirm.json"
  jq -r '"  confirmed=\(.confirmed) session=\(.sessionId) \(.reason)"' \
    "${campaign_final}/confirm.json"
}

# REPRODUCE (ADHOC-INFRA WP5.D): a confirmed witness run again natively --
# the recording weave on the stock JDK, planting only the fault markers the
# confirmation's world plants (explore.ConfirmMain --plant, the code that
# wrote CONFIRM's world; runtime.RecordingPlant) -- reproduce_runs times,
# each under record_timeout_s and charged as a replay, and each aggregated
# for the target as the pre-screen aggregates.  final/reproduce.json states
# how many runs there were, how many planted a marker, how many took the
# target's fatal arm and how many at the claim's own anchor occurrence.  A
# native run holds no schedule, so the planted occurrence may not recur: the
# rate ranks a finding (tools/adhoc/findings.py) and never refutes it, and
# nothing here moves the claim or CONFIRM's decision.  A world a native run
# cannot plant (a clock, an attach's answer, any root but a marker) is a
# reproduce.json with no run and the reason.  Only a confirmed SAT_CANDIDATE
# is reproduced.
campaign_reproduce() {
  local iteration_dir=$1
  local dir="${campaign_final}/reproduce" run trace name status=0
  if [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      != SAT_CANDIDATE || "$(jq -r '.confirmed' \
      "${campaign_final}/confirm.json")" != true ]]; then
    campaign_log "nothing confirmed to reproduce"
    return 0
  fi
  [[ ! -e "${dir}" ]] \
    || die "the reproduction directory already exists: ${dir}"
  mkdir -p "${dir}"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${iteration_dir}" --claim "${campaign_final}/claim.json" \
    --plant "${dir}/plant.jsonl" >"${dir}/plant.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    jq -n --arg reason "$(sed -n 's/^CONFIRM refused: //p' \
        "${dir}/plant.log" | head -n 1)" \
      '{schemaVersion: 1, kind: "REPRODUCTION", runs: 0, planted: 0,
        fatal: 0, atAnchor: 0,
        reason: ("no native run: " + $reason)}' \
      >"${campaign_final}/reproduce.json"
    campaign_log "reproduce: $(jq -r .reason "${campaign_final}/reproduce.json")"
    return 0
  fi
  name=$(campaign_target_names | head -n 1)
  for (( run = 1; run <= reproduce_runs; run++ )); do
    trace="${dir}/run-${run}"
    # The run's own outcome is its summary: a planted fault may well fail
    # the test.
    campaign_head_charged "${obligation_memory_mb}" 300 \
      run_configured_workload "${trace}" "${record_timeout_s}" \
      "${dir}/plant.jsonl" >"${trace}.log" 2>&1 || true
    run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
      --trace-dir "${trace}" --test "${trace_test}" \
      --target "${name}=${campaign_target_slice},${trace}/${name}" \
      --summary "${trace}/summary.json" >>"${trace}.log" 2>&1 || true
  done
  find "${dir}" -mindepth 2 -maxdepth 2 -name summary.json -print0 \
    | xargs -0 -r cat \
    | jq -s --argjson runs "${reproduce_runs}" --arg name "${name}" \
      --arg anchor "$(jq -r '.anchor' "${campaign_final}/claim.json")" '
      {schemaVersion: 1, kind: "REPRODUCTION", runs: $runs,
       planted: map(select(.plantsApplied > 0)) | length,
       fatal: map(select((.targets[$name].fatalOccurrences // [])
                         | length > 0)) | length,
       atAnchor: map(select((.targets[$name].fatalOccurrences // [])
                            | index($anchor) != null)) | length,
       reason: ""}' >"${campaign_final}/reproduce.json"
  jq -r '"  reproduced at the anchor in \(.atAnchor) of \(.runs) native run(s) (\(.planted) planted, \(.fatal) fatal)"' \
    "${campaign_final}/reproduce.json"
}

# The one shape of final/confirm.json.
campaign_confirm_verdict() {
  local confirmed=$1 reason=$2 session_id=$3
  jq -n --argjson confirmed "${confirmed}" --arg reason "${reason}" \
    --arg sessionId "${session_id}" \
    '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: $confirmed,
      reason: $reason, sessionId: $sessionId}'
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

# The static catalog's own gaps, as a JSON array.
campaign_static_gaps_json() {
  local gzipped="${causynth_output_dir}/communication_gaps.jsonl.gz"
  require_nonempty "static communication gaps" "${gzipped}"
  gzip -d -c -- "${gzipped}" | jq -c -s '.' || return 1
}

# The planning gaps the runtime plan artifact carries in its catalog row.
campaign_plan_gaps_json() {
  require_nonempty "runtime region plan" "${runtime_region_plan}"
  head -n 1 -- "${runtime_region_plan}" | jq -c '.gaps // []' || return 1
}

# One generated JSON document, as a file jq can read.
#
# A command-line argument is capped at 128 KiB on Linux -- MAX_ARG_STRLEN,
# 32 pages, a per-argument limit that no ARG_MAX headroom relaxes -- and the
# documents below are proportional to the corpus, so passing one as an
# argument can fail EMIT with "Argument list too long".  Every generated
# document is written to a file and slurped; none is passed with --argjson.
campaign_json_file() {
  local destination=$1 content=$2
  printf '%s\n' "${content}" >"${destination}" || return 1
  printf '%s' "${destination}"
}

# Every gap this campaign raised, in one document, each row classed by the row
# itself.
#
# A GapRow states its own kind and class (CONTRACT-SPEC §2.5): the stage that
# raised it knows what it could not do, and no later stage is in a position to
# overrule that.  So this is a partition, not a classification.  A row that
# states no class is BLOCKING.
#
# This function and the `accepted` conjunction it feeds are the ONE reader of
# a gap's class in the campaign: every other stage states classes and reads
# none but its own.  classReason says which of the two rules answered.
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
  # Every session's own gap rows, plus the campaign's, each labelled with the
  # stage that raised it: a replay session's rows are REPLAY, an obligation
  # worker's or a wave's are EXPLORE, and a campaign row states its own stage
  # (IMPORT's gate is the one writer that states none).
  local gapfile gapstage
  : >"${scratch}/session-gaps.jsonl"
  while IFS= read -r -d '' gapfile; do
    case "${gapfile}" in
      */sessions/*/gaps.jsonl) gapstage=REPLAY ;;
      */obligations-*/gaps.jsonl) gapstage=EXPLORE ;;
      *) rm -rf -- "${scratch}"
         campaign_fail EMIT campaign_write_gaps "${gapfile}" \
           "a gaps.jsonl at a path no stage of this campaign writes" ;;
    esac
    jq -c --arg stage "${gapstage}" '. + {stage: (.stage // $stage)}' \
      "${gapfile}" >>"${scratch}/session-gaps.jsonl"
  done < <(find "${iteration_dir}" -type f -name 'gaps.jsonl' -print0 \
    | LC_ALL=C sort -z)
  [[ ! -s "${iteration_dir}/campaign_gaps.jsonl" ]] \
    || jq -c '. + {stage: (.stage // "IMPORT")}' \
      "${iteration_dir}/campaign_gaps.jsonl" \
      >>"${scratch}/session-gaps.jsonl"
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --slurpfile composedDocuments "${composition}" \
    --slurpfile staticGapDocuments "${scratch}/static-gaps.json" \
    --slurpfile planGapDocuments "${scratch}/plan-gaps.json" \
    --slurpfile sessionGaps "${scratch}/session-gaps.jsonl" '
    ($staticGapDocuments[0] // []) as $staticGaps |
    ($planGapDocuments[0] // []) as $planGaps |
    $composedDocuments[0] as $composed |
    # A row that states its own class is taken at its word.
    # Slurped as rows, never one string: 2.5 GB of rows (v69) was past the
    # longest string jq reads, and the split met a row cut in half.
    ($sessionGaps
      | map({stage: (.stage // "REPLAY"),
             source: (if (.sessionId // "") == "" then "RUNTIME"
                      else .sessionId end),
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
  # CONFIRM's answer (PIPELINE §10).  A SAT claim is a claim about the model;
  # whether the program agreed is final/confirm.json, required for every
  # SAT_CANDIDATE, and an unconfirmed one is published as SAT_UNCONFIRMED
  # with the first mismatch named.  Any other claim was never confirmed
  # and carries null.
  local confirmation=null
  if [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      == SAT_CANDIDATE ]]; then
    require_nonempty "confirmation" "${campaign_final}/confirm.json"
    campaign_require_json "confirmation" "${campaign_final}/confirm.json" \
      || campaign_fail EMIT CONFIRM "${campaign_final}/confirm.json" \
        "the confirmation is malformed"
    jq -e '(.confirmed | type) == "boolean" and (.reason | type) == "string"' \
      "${campaign_final}/confirm.json" >/dev/null \
      || campaign_fail EMIT CONFIRM "${campaign_final}/confirm.json" \
        "the confirmation states no boolean confirmed and string reason"
    confirmation=$(cat "${campaign_final}/confirm.json")
  fi
  # REPRODUCE's answer for a confirmed candidate, beside the confirmation it
  # never changes; null for every other claim.
  local reproduction=null
  if [[ "$(jq -r '.confirmed' <<<"${confirmation}")" == true ]]; then
    require_nonempty "reproduction" "${campaign_final}/reproduce.json"
    campaign_require_json "reproduction" "${campaign_final}/reproduce.json" \
      || campaign_fail EMIT REPRODUCE "${campaign_final}/reproduce.json" \
        "the reproduction is malformed"
    reproduction=$(cat "${campaign_final}/reproduce.json")
  fi
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --argjson confirmation "${confirmation}" \
    --argjson reproduction "${reproduction}" \
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
    (if $decided.claim == "SAT_CANDIDATE"
        and ($confirmation.confirmed != true)
     then "SAT_UNCONFIRMED" else $decided.claim end) as $claim |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     provenance: $provenance,
     claim: $claim,
     claimReason: (if $claim == "SAT_UNCONFIRMED"
       then "the confirmation replay did not agree with the model: "
            + $confirmation.reason
       else $decided.claimReason end),
     blockers: $decided.blockers,
     # ClaimPolicy counts its own blockers; re-counting the array here let
     # the published count drift from the policy that decided the claim.
     blockerCount: $decided.blockerCount,
     whyNotAccepted: (if $claim == "SAT_UNCONFIRMED"
       then "SAT_UNCONFIRMED: " + $confirmation.reason
       else $decided.whyNotAccepted end),
     # The confirmation itself, so a reader of result.json sees which
     # session answered and why, not only that the claim was downgraded.
     confirmation: $confirmation,
     # How often the confirmed world reproduced natively (REPRODUCE).
     reproduction: $reproduction,
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
     accepted: (($claim == "SAT_CANDIDATE" or $claim == "UNSAT_CLOSED")
                and $gapCount == 0),
     blockingGapCodes: ($gaps.byCode // {}),
     # What each satisfying witness named, and whether the policy read it as a
     # finding or as freedom nobody accounted for. A reader asking "why is this
     # sat" gets the mechanism narrative here rather than having to rebuild it
     # from the model.
     witnessFindings: ($decided.witnessFindings // []),
     # Which execution of the declared target this claim is about: the one
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
    -name '*.jsonl' -printf '%s\n' \
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
  # Same rule as campaign_write_gaps: these three grow with the corpus, so
  # they travel as files.  The provenance and the two counts are bounded and
  # stay arguments.
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

# SEED of a batch campaign: one recording for every target of the spec, each
# on its own slice (campaign_record_batch, the workload unbounded as SEED's
# is); a workload that exits nonzero fails SEED as it does alone.  Each
# target's directory then holds what a campaign of its own reads beside its
# slice: the batch's region skeletons, grown scope, lineage and recording
# weave, and the recorded schedule, linked, so every weave and replay of
# every target stands on the recording's frames.
campaign_batch_seed() {
  local name target
  campaign_record_batch
  jq -e '.exit == 0' "${causynth_output_dir}/runtime/record-summary.json" \
    >/dev/null || campaign_fail SEED WORKLOAD "${causynth_output_dir}/runtime" \
    "the recorded workload exited $(jq -r .exit \
      "${causynth_output_dir}/runtime/record-summary.json"): the test failed, \
or its run never opened a recording window (its output is above)"
  while IFS= read -r name; do
    target="${causynth_output_dir}/targets/${name}"
    ln -s ../../region_skeletons.jsonl.gz "${target}/region_skeletons.jsonl.gz"
    ln -s ../../scope-classes "${target}/scope-classes"
    ln -s ../../lineage-classes "${target}/lineage-classes"
    ln -s ../../instrumented-classes "${target}/instrumented-classes"
    ln -s ../../../runtime/schedule.jsonl "${target}/runtime/schedule.jsonl"
    campaign_log "target ${name}: $(jq -r --arg name "${name}" \
      '.targets[$name] | .state + " " + .detail' \
      "${causynth_output_dir}/runtime/record-summary.json")"
  done < <(campaign_target_names)
}

# A batch campaign (causynth_static_root: an ad-hoc sweep's case).  SEED
# records once for every target (campaign_batch_seed); each target the
# recording activated is planned on its own slice (campaign_batch_plan); the
# plans are grouped so that each group's union is one plan one replay runs
# (plan.PlanUnion) -- the targets' plans stand on one recording, so the
# tasks they share are one task -- and each group is woven, seed-replayed
# and imported once (campaign_batch_group), all groups at once; then every
# target its group's seed replay reached runs its own campaign from EXPLORE
# on (campaign_batch_target), all at once.  Each target logs to
# targets/<name>/campaign.log.  The batch fails when SEED does, when the
# recording activated no target, or when a target that was planned ends
# before EMIT (its PLAN, its group's seed, or its own stages); each target's
# claim is its own targets/<name>/schedule/final/result.json.
campaign_batch() {
  local summary="${causynth_output_dir}/runtime/record-summary.json"
  local groups="${campaign_root}/groups"
  local name group index status failed=0
  local -a names=() planned=() members=() served=() pids=()
  campaign_stage SEED campaign_batch_seed
  mapfile -t names < <(jq -r '.targets | to_entries[]
    | select(.value.state == "ACTIVATED") | .key' "${summary}")
  (( ${#names[@]} > 0 )) || campaign_fail SEED CausynthTraceRecorder \
    "${summary}" "the recording activated no target of the batch"
  for name in "${names[@]}"; do
    if ( campaign_batch_plan "${name}" ) \
        >>"${causynth_output_dir}/targets/${name}/campaign.log" 2>&1; then
      planned+=("${name}")
    else
      campaign_log "target ${name}: $(campaign_batch_verdict \
        "${causynth_output_dir}/targets/${name}")"
      failed=$((failed + 1))
    fi
  done
  (( ${#planned[@]} > 0 )) || campaign_fail PLAN CAMPAIGN \
    "${causynth_output_dir}/targets" "no target of the batch was planned"
  campaign_stage UNION campaign_batch_union "${groups}" "${planned[@]}"
  mapfile -t members < <(jq -r '.[] | .targets | join(" ")' \
    "${groups}/groups.json")
  for group in "${!members[@]}"; do
    # shellcheck disable=SC2086 # the members are words
    ( campaign_batch_group "${groups}/group-${group}" ${members[$group]} ) \
      >"${groups}/group-${group}.log" 2>&1 &
    pids[group]=$!
  done
  for group in "${!members[@]}"; do
    if wait "${pids[$group]}"; then
      mapfile -t -O "${#served[@]}" served <"${groups}/group-${group}/served"
      failed=$((failed + $(wc -w <<<"${members[$group]}") \
        - $(wc -l <"${groups}/group-${group}/served")))
    else
      campaign_log "group ${group} (${members[$group]}) ended before \
EXPLORE: $(campaign_batch_verdict "${groups}/group-${group}" \
        "${groups}/group-${group}.log")"
      failed=$((failed + $(wc -w <<<"${members[$group]}")))
    fi
  done
  pids=()
  if [[ "${campaign_stop_after}" == "IMPORT" ]]; then
    campaign_log "stopping after IMPORT: campaign_stop_after=IMPORT"
    return 0
  fi
  for index in "${!served[@]}"; do
    name=${served[$index]%%$'\t'*}
    ( campaign_batch_target "${name}" "${served[$index]#*$'\t'}" ) \
      >>"${causynth_output_dir}/targets/${name}/campaign.log" 2>&1 &
    pids[index]=$!
  done
  for index in "${!served[@]}"; do
    name=${served[$index]%%$'\t'*}
    status=0
    wait "${pids[$index]}" || status=$?
    campaign_log "target ${name}: exit ${status}, $(\
      campaign_batch_verdict "${causynth_output_dir}/targets/${name}")"
    # EMIT's own exits: 2, no accepted claim; 3, BLOCKING gaps.
    case "${status}" in
      0|2|3) ;;
      *) failed=$((failed + 1)) ;;
    esac
  done
  (( failed == 0 )) || campaign_fail EMIT CAMPAIGN \
    "${causynth_output_dir}/targets" "${failed} of ${#names[@]} target \
campaign(s) ended before EMIT; each names its stage in its campaign.log"
}

# One target's PLAN, in its own campaign root (campaign_batch_enter).
campaign_batch_plan() {
  campaign_batch_enter "$1"
  local iteration_dir="${campaign_root}/iteration-0000"
  mkdir -p "${iteration_dir}"
  campaign_member_rows=""
  campaign_stage PLAN campaign_plan "${iteration_dir}"
}

# The planned targets' groups (plan.PlanUnion): <dir>/groups.json and each
# group's union plan, <dir>/group-<n>/execution_task_plan.jsonl.
campaign_batch_union() {
  local dir=$1 name
  shift
  local -a plans=()
  for name in "$@"; do
    plans+=(--plan "${name}=${causynth_output_dir}/targets/${name}/schedule/\
iteration-0000/execution_task_plan.jsonl")
  done
  run_java_main edu.uva.liftlab.graphchecker.plan.PlanUnion \
    "${plans[@]}" --output-dir "${dir}" >/dev/null
  campaign_log "groups: $(jq -r -c 'map(.targets)' "${dir}/groups.json")"
}

# One group's seed: its union plan woven once (INSTRUMENT), replayed once on
# the recording's schedule (REPLAY) under the union of its targets' scope
# maps -- what the replay's guarded stores are, and its target coverage: any
# target -- and imported once (IMPORT), in <dir>, which a campaign reads as
# its iteration.  Each target the replay reached is written to <dir>/served
# as "<name><TAB><dir>"; one it did not reach is named and not run.
campaign_batch_group() {
  local dir=$1 name reached
  shift
  local targets="${causynth_output_dir}/targets"
  mkdir -p "${dir}/seed-replay"
  ln -f "${dir}/execution_task_plan.jsonl" \
    "${dir}/seed-replay/execution_task_plan.jsonl"
  cp -f "${causynth_output_dir}/runtime/schedule.jsonl" \
    "${dir}/recorded_schedule.jsonl"
  for name in "$@"; do
    cat "${targets}/${name}/static_scope_map.jsonl"
  done | awk '!seen[$0]++' >"${dir}/static_scope_map.jsonl"
  causynth_static_scope_map="${dir}/static_scope_map.jsonl"
  campaign_stage INSTRUMENT campaign_instrument "${dir}"
  campaign_stage REPLAY campaign_session_replay "${dir}"
  campaign_stage IMPORT campaign_import_session "${dir}" iteration-0000
  : >"${dir}/served"
  for name in "$@"; do
    reached=$(campaign_target_reached "${dir}/sessions" \
      "${targets}/${name}/static_scope_map.jsonl")
    if [[ -n "${reached}" ]]; then
      printf '%s\t%s\n' "${name}" "${dir}" >>"${dir}/served"
    else
      # Its campaign's own failure, in its own log, as a solo REPLAY's.
      ( campaign_fail REPLAY WORKLOAD "${dir}/sessions" "the group's seed \
replay published no target row of ${name}; the workload's terminating \
exception is in ${dir}/seed-result/focused/replay.log" ) \
        2>>"${targets}/${name}/campaign.log" || true
      campaign_log "target ${name}: the group's seed replay published no \
target row of it"
    fi
  done
}

# One target's verdict line: its claim, else the failure its log names
# (<dir>/campaign.log, or the log given).
campaign_batch_verdict() {
  local result="$1/schedule/final/result.json" log=${2:-$1/campaign.log}
  if [[ -s "${result}" ]]; then
    jq -r '"\(.claim) \(.findingKind // "")"' "${result}"
  else
    grep -A4 '^\[campaign:error\]' "${log}" \
      | sed -n 's/^ *\(stage\|reason\)=//p' | tail -n 2 | paste -sd ' ' -
  fi
}

# One target of a batch campaign as its own campaign, in targets/<name>/:
# its causynth_output_dir (so every stage -- and every peer of its waves,
# which derive their paths from it -- reads its slice and its region plan
# there), its spec that one target's line, its region plan aggregated on its
# view of the merged skeletons (campaign_target_slice), and its campaign
# root targets/<name>/schedule/.  In a subshell of its own.
campaign_batch_enter() {
  local name=$1
  causynth_output_dir="${causynth_output_dir}/targets/${name}"
  derive_output_paths
  causynth_target_spec="${causynth_output_dir}/target.yaml"
  campaign_target_slice="${candidate_graph},${causynth_static_scope_map},\
${causynth_output_dir}/view_region_skeletons.jsonl.gz"
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  mkdir -p "${campaign_root}"
  touch "${campaign_stage_metrics}"
  campaign_init_local_scratch_root
}

# A planned target's campaign from EXPLORE on, over its group's seed <group>
# (campaign_batch_group): its iteration takes the group's union plan (a copy:
# GROW appends to it), its woven classes and seed session (hard links: GROW
# re-weaves its own), and its census and import gate; its own PLAN is read
# again (campaign_plan_read).
campaign_batch_target() {
  local name=$1 group=$2
  campaign_batch_enter "${name}"
  local iteration_dir="${campaign_root}/iteration-0000" worker
  campaign_seed_provenance
  campaign_plan_read "${iteration_dir}"
  cp -f -- "${group}/execution_task_plan.jsonl" \
    "${iteration_dir}/execution_task_plan.jsonl.union"
  mv -f -- "${iteration_dir}/execution_task_plan.jsonl.union" \
    "${iteration_dir}/execution_task_plan.jsonl"
  ln -f "${iteration_dir}/execution_task_plan.jsonl" \
    "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  for worker in "${iteration_dir}"/workers/*/; do
    ln -f "${iteration_dir}/execution_task_plan.jsonl" \
      "${worker}execution_task_plan.jsonl"
  done
  cp -al -- "${group}/instrumented-classes" "${group}/sessions" \
    "${iteration_dir}/"
  cp -- "${group}/session_census.jsonl" "${group}/import_gate.json" \
    "${group}/woven_class_verification.log" "${iteration_dir}/"
  # The gate writes its gap rows only when a row states one.
  [[ ! -e "${group}/campaign_gaps.jsonl" ]] \
    || cp -- "${group}/campaign_gaps.jsonl" "${iteration_dir}/"
  campaign_log "target ${name}: campaign root ${campaign_root}, seed of \
${group}"
  campaign_iteration_explore "${iteration_dir}" iteration-0000
}

# ONE obligation of somebody else's wave, on this machine.
#
# The peer loads the same configuration file the campaign loaded, from the
# same shared home, and every path in it resolves identically -- but two
# values are NOT in that file and must arrive already decided, or this worker
# silently does different work from the local workers of the same wave.
#
#   graphchecker_jar, because FREEZE_TOOL rebinds it to the campaign's
#     private read-only copy.  Re-derived here it would be whatever is in
#     target/ at this instant, and on a shared home that is a different build
#     the moment anybody runs `mvn package`.  Taken as GIVEN, and then
#     CHECKED: the digest the campaign
#     froze is the digest of the file about to be loaded, or this worker
#     refuses before it starts.
#
#   the workflow key values, forwarded by campaign_remote_env_assignments as
#     environment overrides.  They win over the file, so an edit to the file
#     while the wave is in flight cannot reach a worker.
do_run_obligation() {
  local jar="" jar_sha="" actual_sha
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --graphchecker-jar)
        [[ $# -ge 2 ]] || die "--graphchecker-jar requires a path"
        jar=$2
        shift 2
        ;;
      --graphchecker-jar-sha256)
        [[ $# -ge 2 ]] || die "--graphchecker-jar-sha256 requires a digest"
        jar_sha=$2
        shift 2
        ;;
      --)
        shift
        break
        ;;
      *) break ;;
    esac
  done
  [[ -n "${jar}" ]] || die "--run-obligation requires --graphchecker-jar: \
the campaign's frozen jar is not derivable from the configuration"
  [[ -n "${jar_sha}" ]] || die "--run-obligation requires \
--graphchecker-jar-sha256"
  [[ $# -eq 6 ]] || die "--run-obligation takes six positional arguments \
(id obligations classes worker sessions seed-plan), got $#"
  graphchecker_jar=${jar}
  require_file "GraphChecker jar" "${graphchecker_jar}"
  actual_sha=$(campaign_digest "${graphchecker_jar}")
  [[ "${actual_sha}" == "${jar_sha}" ]] || die "the GraphChecker jar this \
worker was handed is not the one the campaign froze: ${graphchecker_jar} is \
${actual_sha}, the campaign says ${jar_sha}"
  # The same gate the head's PREFLIGHT ran, so a peer that resolved a
  # nonsense configuration says so here rather than inside a replay JVM.
  validate_config >/dev/null
  require_command_available jq
  require_command_available sha256sum
  # Set from the CAUSYNTH_LOCAL_SCRATCH the campaign forwarded, so this
  # worker's replay scratch lands on THIS machine's local disk under the same
  # per-run root every other worker of the run uses.
  campaign_init_local_scratch_root
  campaign_log "obligation $1 on $(hostname): jar ${graphchecker_jar} \
(${actual_sha}), scratch ${campaign_local_scratch_root:-<shared home>}"
  campaign_obligation_worker "$@"
}

# One campaign, one iteration.  What a replay learns past the recording's
# topology is taken up inside EXPLORE's wave loop (GROW), so there is nothing
# for a second iteration to re-plan.
do_campaign() {
  local iteration_id=iteration-0000
  local iteration_dir
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  iteration_dir="${campaign_root}/${iteration_id}"
  # Refused before any work rather than after the seed: a campaign root that
  # already holds an iteration belongs to another run, and its directories are
  # written once.
  [[ ! -e "${iteration_dir}" && ! -e "${campaign_final}" ]] \
    || die "this campaign root already holds a published run: ${campaign_root}"
  ensure_output_directory "${campaign_root}"
  # Reserve this run before either process can truncate its stage metrics.
  # mkdir is the one atomic claim on a campaign root; every later artifact is
  # immutable beneath the directory owned by the winner.
  mkdir -- "${campaign_root}/frozen-inputs" || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${campaign_root}" \
    "the campaign root is already reserved by another run"
  : >"${campaign_stage_metrics}"
  # Named now that the campaign root is claimed, because the root is what
  # makes it this run's and no other run's.
  campaign_init_local_scratch_root
  # This shell is the head: its engine JVMs and its replays are charged to
  # its host (campaign_head_charged).
  campaign_head_charging=1

  campaign_stage PREFLIGHT campaign_preflight
  campaign_stage FREEZE_TOOL campaign_freeze_graphchecker_jar
  if [[ -n "${campaign_setup_command}" ]]; then
    campaign_stage SETUP campaign_setup
  fi
  campaign_stage FREEZE campaign_freeze
  # A campaign over a build's slices -- an ad-hoc sweep's batch case --
  # records once for all its targets and runs each on its own.
  if [[ -n "${causynth_static_root}" ]]; then
    campaign_batch
    return
  fi
  campaign_stage SEED campaign_seed
  campaign_iteration
}

# The campaign's one iteration once SEED has run: PLAN .. EMIT in
# ${campaign_root}/iteration-0000.
campaign_iteration() {
  local iteration_id=iteration-0000
  local iteration_dir="${campaign_root}/${iteration_id}"
  mkdir -p "${iteration_dir}"
  campaign_member_rows=""
  campaign_stage PLAN campaign_plan "${iteration_dir}"
  campaign_stage INSTRUMENT campaign_instrument "${iteration_dir}"
  campaign_stage REPLAY campaign_session_replay "${iteration_dir}"
  campaign_stage IMPORT campaign_import_session "${iteration_dir}" \
    "${iteration_id}"
  # A measurement run stops where its measurement is complete: the seed
  # session and its census, which IMPORT has just published.
  if [[ "${campaign_stop_after}" == "IMPORT" ]]; then
    campaign_log "stopping after IMPORT: campaign_stop_after=IMPORT"
    return 0
  fi
  campaign_iteration_explore "${iteration_dir}" "${iteration_id}"
}

# The iteration from EXPLORE on, once its seed session is imported.
campaign_iteration_explore() {
  local iteration_dir=$1 iteration_id=$2
  campaign_stage EXPLORE campaign_explore "${iteration_dir}" "${iteration_id}"
  campaign_publish_iteration_manifest "${iteration_dir}" "${iteration_id}"
  campaign_stage COMPOSE campaign_compose "${iteration_dir}"
  campaign_stage SOLVE campaign_solve
  campaign_stage DECIDE campaign_decide
  campaign_stage CONFIRM campaign_confirm "${iteration_dir}"
  campaign_stage REPRODUCE campaign_reproduce "${iteration_dir}"
  campaign_stage EMIT campaign_emit "${iteration_dir}"
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
  campaign|slice|record|config|validate|--run-obligation)
    [[ -n "${config_file}" ]] || die "${command_name} requires --config FILE"
    initialize_config "${config_file}"
    case "${command_name}" in
      campaign|slice|record)
        [[ $# -eq 0 ]] || die "${command_name} takes no extra arguments"
        "do_${command_name}"
        ;;
      config) print_normalized_config ;;
      validate) validate_config ;;
      --run-obligation) do_run_obligation "$@" ;;
    esac
    ;;
  *)
    die "unknown command '${command_name}' (run './run_engine.sh help')"
    ;;
esac
