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
              (a streaming pool of obligations, growing the woven region
              set as replays expose it) and
              compose/solve/decide/confirm/reproduce/emit.
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
              Execute ONE obligation that some campaign planned,
              and nothing else.  This is what `campaign_worker_hosts` runs
              over ssh on a peer; the campaign generates the invocation into
              the obligation's own worker directory, so it is not a command
              to be typed.  The six positional arguments are exactly what
              campaign_obligation_worker takes.
  --run-placed
              Execute ONE step of a campaign head on a peer with room
              (campaign_run_placed) -- an engine JVM, the seed or CONFIRM
              replay, a GROW re-run, a native run of REPRODUCE: a working
              directory, the head's exported CAUSYNTH_/GRAPH_CHECKER_
              assignments, `--`, then the command or run_engine.sh function
              with its arguments.

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
  # The machines a campaign's obligations may run on: a space-separated host
  # list.  The obligations are independent -- each runs its own solver and
  # its own replay JVM, writes into its own worker directory and stages a
  # session under an id it mints itself -- so the only thing a second
  # machine needs is the shared home every path in this configuration
  # already names.  How many run on one host is that host's memory and cores
  # (campaign_stream_admit_host); landing, gating and planning stay on the
  # head.
  #
  # EMPTY -- the default -- runs every worker locally, no ssh anywhere.  A
  # host spelled `localhost` or as this machine's own hostname runs locally
  # too.
  "campaign_worker_hosts CAUSYNTH_CAMPAIGN_WORKER_HOSTS krp -"
  # The memory, in MB, one replay takes on the host that runs it (an
  # obligation's, a GROW re-run's; the seed's and CONFIRM's at least, see
  # campaign_replay_need_mb): half its heap, half the VM's native symbolic
  # state, and the charge execute.sh holds it to, grown while its host has
  # room (campaign_watch_workload).  The pool starts an
  # obligation only on a host with that much available beyond what the starts
  # there in the last ramp window will still claim (campaign_host_try_start),
  # whichever campaign started them -- the hosts are shared, and so is this
  # accounting; the host's solver is charged at its own start
  # (campaign_start_solver).  No default: the need is the case's, measured
  # (each replay states its peak), and a campaign that states none is refused.
  "obligation_memory_mb CAUSYNTH_OBLIGATION_MEMORY_MB krp -"
  # How many obligations the capped explorations running at once keep in
  # flight together, on all their hosts: each starts one more only while it
  # runs fewer than its share, this over the capped explorations running
  # now, at least one (campaign_stream_has_slot), so one running alone takes
  # them all and ten take a tenth each.  An ad-hoc sweep states its hosts'
  # obligation slots here (tools/adhoc/sweep.sh, campaign_pool_slots): one
  # case's pool kept 27-32 Solr replays in flight on all ten lifts while
  # the sweep's other cases waited for room (a40).  0 -- the default, a
  # named acceptance run's -- is no cap: the hosts' memory and cores alone
  # decide.
  "stream_max_in_flight CAUSYNTH_STREAM_MAX_IN_FLIGHT krp 0"
  # The most heap, in MB, an engine JVM of the head is given -- one whose
  # main has no measured need starts there, and one that runs out of its
  # need runs again there (engine_java) -- and the heap of a solver asked
  # again (campaign_solve_obligation_alone).  Empty: the launcher's default.
  # A case whose corpus outgrows it states its own (hdfs-11741: 202 sessions
  # by wave 4 ran the planner out of 8 GB).
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
  # The deepest wave EXPLORE plans: a wave is a generation of worlds, one
  # past the deepest wave whose obligation published a landed session
  # (PIPELINE §7.9).
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
  # The system's own DOOR rows, which replace the engine catalog's of their
  # transport and direction (causynth.LibraryCatalog, SYMBOL-SCOPE §4.2).
  "causynth_system_doors CAUSYNTH_SYSTEM_DOORS krp -"
  # How many classes of the lineage roots SEED may add to the case's scope
  # where the slice stops at it (plan.ScopeGrowth, SYMBOL-SCOPE §2.4),
  # nearest the throw first; 0 keeps the declared scope as it is.
  "causynth_scope_growth_budget CAUSYNTH_SCOPE_GROWTH_BUDGET krp 24"
  # The directory holding each target's static slice, <root>/<target
  # name>/, as `slice` wrote it (tools/adhoc/slice.sh): what `record` (a
  # pre-screen) and a batch campaign (an ad-hoc sweep's case) weave and
  # aggregate each target on, instead of a static pass of their own.
  "causynth_static_root CAUSYNTH_STATIC_ROOT krp -"
  # The wall clock a pre-screen's recording may take after SEED's own.
  "record_timeout_s CAUSYNTH_RECORD_TIMEOUT_S krp 300"
  # How many times REPRODUCE runs a confirmed witness natively, and each
  # run's wall clock: this factor times the recording's own workload.
  "reproduce_runs CAUSYNTH_REPRODUCE_RUNS krp 10"
  "reproduce_time_factor CAUSYNTH_REPRODUCE_TIME_FACTOR krp 3"
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
  # override point, so every stage of a run -- and every peer of it --
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
  # replay JVM that deadlocks never returns, its obligation never lands, and
  # the exploration waits on it until an outer timeout kills the campaign
  # and every verdict already reached is lost.  A replay that exceeds this
  # is that obligation's own NOT_ADMITTED row, not the campaign's death.
  # Defaulted rather than required: an absent bound is exactly the unbounded
  # wait this exists to end.
  "replay_timeout_s CAUSYNTH_REPLAY_TIMEOUT_S krp 2400"
  # The wall clock the whole campaign may take from its start, in seconds:
  # the case's budget (experiments/accept/accept.sh passes what is left of
  # CASE_TIMEOUT_SECONDS).  The exploration, and each claim CONFIRM refutes,
  # are followed by more only while the reserve remains (campaign_reserve);
  # past that the exploration ends and the claim it has is published.
  "campaign_budget_s CAUSYNTH_CAMPAIGN_BUDGET_S krp 21600"
  # The least the stages after the exploration are kept of that budget, in
  # seconds: one COMPOSE and one CONFIRM, before the campaign has measured
  # either (campaign_reserve).
  "campaign_reserve_s CAUSYNTH_CAMPAIGN_RESERVE_S krp 600"
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
  if [[ -n "${causynth_system_doors}" ]]; then
    causynth_system_doors=$(resolve_path "${causynth_system_doors}")
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

# The engine JVM, started at what its main measurably needs and charged that
# -- on whichever host a campaign's head placed it, for as long as a JVM
# takes to reach its size (campaign_head_charged) -- and at the case's
# engine heap (engine_memory_mb,
# else the launcher's 8 GB) only when it outgrows that.  A head that charged
# every engine JVM 16 GB waited 35-69 minutes for room it did not use: the
# start needs its charge plus the 30 % reserve free (fast2, solr-18406 and
# hdfs-11741 planners).  The arguments are the JVM's own: options, -cp
# <classpath>, the main class, its arguments.
#
# A main with a measured need (campaign_engine_need_mb, or the caller's
# engine_need_mb) runs at it; one that runs out of heap there runs again at
# twice that heap, up to the engine heap, saying so each time, and every
# later start of that main in this shell starts at the heap it last ran out
# of, doubled (campaign_engine_outgrown).  One step at a time: a trace
# aggregation or a scheduler that outgrew 2 GB asked for the 16 GB engine
# heap at once, which no lift of a running sweep had free beside its 30 %
# reserve, and its case waited 75-85 min for it (a40s RestoreCmd-300,
# RequestApplyUpdatesOp-42).  Its standard output is passed on only from the
# run that finished, so a reader of it never sees an earlier run's half.  A
# main without a need, or whose need the engine heap does not exceed, runs
# at the engine heap.  Every run ends at its first out-of-heap error
# (-XX:+ExitOnOutOfMemoryError, the JVM's exit 3): at the engine heap too,
# where a planner left to the JVM collected for ten minutes and died with
# exit 1 of "GC overhead limit exceeded" (sweep a40h2, DataStreamer-638),
# so a caller can tell the most heap a head JVM is given from a crash.
campaign_engine_outgrown=""
campaign_jvm_out_of_heap_status=3
engine_java() {
  local heap=${engine_memory_mb:-8192} main="" start index next status
  local out
  for (( index = 1; index < $#; index++ )); do
    [[ "${!index}" == -cp ]] || continue
    next=$((index + 2))
    main=${!next}
    break
  done
  start=$(campaign_engine_start_mb "${main}" "${engine_need_mb:-}")
  while (( start < heap )); do
    out=$(mktemp) || return
    status=0
    campaign_head_charged "${start}" 120 \
      env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${start}" "${java_bin}" \
      -XX:+ExitOnOutOfMemoryError "$@" >"${out}" || status=$?
    if (( status != campaign_jvm_out_of_heap_status )); then
      cat -- "${out}"
      rm -f -- "${out}"
      return "${status}"
    fi
    rm -f -- "${out}"
    next=$(( 2 * start < heap ? 2 * start : heap ))
    campaign_engine_outgrown="$(sed "s| ${main}=[0-9]*||" \
      <<<"${campaign_engine_outgrown}") ${main}=${next}"
    printf '[campaign] %s ran out of its %s MB heap; run again at %s MB\n' \
      "${main##*.}" "${start}" "${next}" >&2
    start=${next}
  done
  campaign_head_charged "${heap}" 120 \
    env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
    -XX:+ExitOnOutOfMemoryError "$@"
}

# The heap, in MB, <main> starts at (engine_java): its measured need
# (<need>, else campaign_engine_need_mb), or the larger heap it outgrew its
# need to in this shell (campaign_engine_outgrown: ` <main>=<mb>` words),
# never more than the engine heap; the engine heap for a main with no need.
campaign_engine_start_mb() {
  local main=$1 need=${2:-} heap=${engine_memory_mb:-8192} grown
  [[ -n "${need}" ]] || need=$(campaign_engine_need_mb "${main}")
  [[ -n "${need}" ]] || need=${heap}
  grown=$(sed -n "s|.* ${main}=\([0-9]*\).*|\1|p" \
    <<<"${campaign_engine_outgrown}")
  (( ${grown:-0} <= need )) || need=${grown}
  printf '%s\n' "$(( need < heap ? need : heap ))"
}

# The heap, in MB, an engine main measurably needs, or nothing for the
# engine heap: the largest need over the cases measured, so no case's run
# lives at the edge of its heap (a JVM near its cap can collect for half an
# hour before it gives up).  Measured offline over round i1's ten cases,
# every stage at a 4 GB and an 8 GB cap (offline-ab.sh AB_HEAP_MB, peak RSS):
#   static pass (GraphCheckerMain; the weave   2.3-2.8 GB at 4 GB, all pass
#   is the same main)
#   trace aggregation, scheduler, CONFIRM     0.1-0.5 GB
#   (CausynthTraceRecorder, ConcolicScheduler, ConfirmMain; LineageScan 0.15
#   GB sampled live)
#   SEED's door step (ScopeGrowth --doors)    0.09-0.5 GB over 109 runs of
#                                             the nine HDFS and two Solr cases
#                                             (offline-ab SEED.static, 8 GB cap)
#   the woven-class verifier                  0.17-0.19 GB, three HDFS and two
#   (VerifyWovenClasses)                      Solr trees of round e1, 8 GB cap
#   planner (ExploreMain)                     0.2-3 GB, but hdfs-17960 5.9-7.8
#                                             GB and hdfs-11741 past 4 GB: at
#                                             4 GB 17960 collected for 30 min
#   composer (ComposeMain)                    1.4-4.3 GB; hdfs-11741 9.1 GB at
#                                             8 GB, and m1-11741 ran out of 8
#   GROW's exposed-region planner          0.13 GB, 0.4 s (V5-11741 round 5,
#   (ExposedRegionPlanMain)                its two rows: static inputs only)
#   ImportGateMain sizes itself (campaign_import_gate_heap_mb).  ScopeGrowth's
# growth step is the door step's main: measured as that.  A batch's PlanUnion
# unions the scheduler's plans and starts at the scheduler's need, unmeasured
# (no recorded round ran a batch), growing as any main does (engine_java).
# Unmeasured, GROW's planner started at the 16 GB engine heap, which no lift
# of a busy pool had free: V5-11741's GROW waited 40 min and more for it.
campaign_engine_need_mb() {
  case "$1" in
    *.GraphCheckerMain) echo 4096 ;;
    *.CausynthTraceRecorder|*.ConcolicScheduler|*.ConfirmMain|*.LineageScan \
      |*.ScopeGrowth|*.VerifyWovenClasses|*.ExposedRegionPlanMain \
      |*.PlanUnion) echo 2048 ;;
    *.ExploreMain|*.ComposeMain) echo 8192 ;;
  esac
}

# The room a head reserves on its host, in MB (campaign_head_reserve): what
# the largest of its engine JVMs that come back every round starts at -- a
# round's planner, a witness's composer (engine_java) -- not the case's
# engine heap, unless one of them outgrew its need.
campaign_head_need_mb() {
  local main start largest=0
  for main in edu.uva.liftlab.graphchecker.explore.ExploreMain \
      edu.uva.liftlab.graphchecker.compose.ComposeMain; do
    start=$(campaign_engine_start_mb "${main}")
    (( start <= largest )) || largest=${start}
  done
  printf '%s\n' "${largest}"
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
    "-Dcausynth.system.doors=${causynth_system_doors}" \
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
      schedule_max_jobs region_path_max_waves \
      compose_max_valuations causynth_loop_default_bound \
      obligation_memory_mb record_timeout_s reproduce_runs \
      reproduce_time_factor campaign_budget_s campaign_reserve_s; do
    require_positive_integer "${key}"
  done
  # A budget its reserve takes whole ends the exploration before it begins.
  (( campaign_budget_s > campaign_reserve_s )) \
    || die "campaign_budget_s (${campaign_budget_s}) must exceed its reserve \
campaign_reserve_s (${campaign_reserve_s}): the exploration would end before \
it began"
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
  [[ "${causynth_scope_growth_budget}" =~ ^[0-9]+$ ]] \
    || die "causynth_scope_growth_budget must be a non-negative integer: \
${causynth_scope_growth_budget}"
  [[ "${stream_max_in_flight}" =~ ^(0|[1-9][0-9]*)$ ]] \
    || die "stream_max_in_flight must be a non-negative integer: \
${stream_max_in_flight}"
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
  # The system's own class roots: a call into one of their classes outside
  # the scope is the scope frontier's, never a library call whose result
  # rests on its receiver (causynth.LibraryReceivers).
  if [[ -n "${causynth_lineage_roots}" ]]; then
    system_properties+=("-Dcausynth.lineage.roots=${causynth_lineage_roots}")
  fi
  system_properties+=("-Dcausynth.system.doors=${causynth_system_doors}")
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

# do_analyze as one step of <stage>: its output shown and kept in <log>, and
# a pass that fails fails the stage by name, with the refusal it threw (the
# deepest cause GraphCheckerMain printed).  Under errexit a failed pass ended
# the campaign with no stage, component or reason (sweep a40h2: INSTRUMENT's
# LOOP_BODY_ROOT_ENTRY_UNAVAILABLE was a bare stack trace).
campaign_analyze() {
  local stage=$1 log=$2 status=0
  mkdir -p -- "$(dirname "${log}")"
  run_capturing_status do_analyze > >(tee -- "${log}") 2>&1
  wait "$!"
  (( status == 0 )) && return 0
  campaign_fail "${stage}" GraphCheckerMain "${log}" \
    "the static pass failed with exit ${status}: $(campaign_thrown "${log}")"
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
# nothing is added or the budget is spent (SYMBOL-SCOPE §2.4).  First, and
# after every growth, outside the budget, the classes of the library doors
# the analysis scope calls (campaign_scope_doors).
campaign_analyze_grown_scope() {
  local grown changes summary
  grown=$(campaign_grown_scope)
  local -a roots=()
  rm -rf -- "${grown}"
  mkdir -p "${grown}"
  IFS=: read -r -a roots <<<"${causynth_lineage_roots}"
  (( ${#roots[@]} == 0 )) || campaign_scope_doors "${grown}" "${roots[@]}"
  while :; do
    campaign_analyze SEED "${causynth_output_dir}/static-pass.log"
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
    # What the scope grew may call a door the scope did not.
    campaign_scope_doors "${grown}" "${roots[@]}"
  done
}

# The door step (ScopeGrowth --doors, SYMBOL-SCOPE §4.2): the class families
# of the library doors a class of the analysis scope calls join it.
campaign_scope_doors() {
  local grown=$1 summary
  shift
  summary=$(run_java_main edu.uva.liftlab.graphchecker.plan.ScopeGrowth \
    --doors "${grown}" "${project_classes_dir}" "${project_classpath}" \
    "$@") \
    || campaign_fail SEED ScopeGrowth "${grown}" "door scope failed"
  campaign_log "scope growth: ${summary}"
}

# slice: SEED's static half alone -- the case's scope copied in by the setup
# adapter, then campaign_analyze_grown_scope -- writing what SEED's does into
# causynth_output_dir: candidate_dataflow_edges.jsonl.gz,
# static_scope_map.jsonl, region_skeletons.jsonl.gz, scope_frontier.jsonl,
# root_demand.jsonl and scope-classes/.  No workload runs and nothing is
# frozen: an ad-hoc selection reads it (tools/adhoc/slice.sh, score.py).  The
# discovery pass's woven classes go: the recording weaves its own
# (do_workload).
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

# run_configured_workload <trace-dir> [seconds] [plant] [charged_mb]: the
# workload in the recording weave (analysis_classes_dir, as SEED's static
# pass wove it), its trace into <trace-dir>, under a wall-clock bound of
# <seconds> when one is given (run_under_wall_clock_bound), with a native
# reproduction's plant (runtime.RecordingPlant) when one is named, and held
# to what its host was charged for it when it was (campaign_watch_workload).
run_configured_workload() {
  local trace_dir=$1
  local -a workload_env bound=()
  workload_env=(
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "CAUSYNTH_CUSTOM_JDK_HOME=${custom_jdk_home}"
    "CAUSYNTH_INSTRUMENTED_CLASSES_DIR=${analysis_classes_dir}"
    "CAUSYNTH_TRACE_OUTPUT_DIR=${trace_dir}"
    "CAUSYNTH_PLANT=${3:-}"
    "CAUSYNTH_CHARGED_MB=${4:-}"
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
  CAUSYNTH_TRACE_MODE=region-state campaign_analyze SEED "${trace_dir}/weave.log"
  # The recording runs uncharged where the head runs: what it needs is what
  # it measures (workload_rss_mb, 0.4-0.8 GB over round e1), so there is no
  # need yet to charge it with or to place it by (campaign_head_charged).
  local status=0 started=${SECONDS}
  run_configured_workload "${trace_dir}" || status=$?
  campaign_recorded_workload_s=$(( SECONDS - started ))
  (( status == 0 )) || campaign_fail SEED WORKLOAD "${trace_dir}" \
    "the recorded workload exited ${status}: the test failed, or its run" \
    "never opened a recording window (its output is above)"
  campaign_recorded_workload_rss_mb=$(cat "${trace_dir}/workload_rss_mb" \
    2>/dev/null) || campaign_recorded_workload_rss_mb=""
  require_file "static scope map" "${causynth_static_scope_map}"
  local -a declared=()
  [[ -z "${declared_target_occurrence}" ]] \
    || declared=(--target-occurrence "${declared_target_occurrence}")
  run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" --test "${trace_test}" "${declared[@]}" \
    --target "$(campaign_target_names | head -n 1)=${candidate_graph},\
${causynth_static_scope_map},${causynth_region_skeletons},${trace_dir}"
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
    # A static root written before the root demand has none: refused here,
    # by name, not by the copy below.
    require_file "root demand of ${name}" \
      "${causynth_static_root}/${name}/root_demand.jsonl"
  done
  for name in "${names[@]}"; do
    static="${causynth_static_root}/${name}"
    target="${causynth_output_dir}/targets/${name}"
    mkdir -p "${target}/runtime"
    cp -- "${static}/candidate_dataflow_edges.jsonl.gz" \
      "${static}/static_scope_map.jsonl" "${static}/scope_frontier.jsonl" \
      "${static}/root_demand.jsonl" \
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
  CAUSYNTH_TRACE_MODE=region-state campaign_analyze SEED "${trace_dir}/weave.log"
  ensure_output_directory "${trace_dir}"
  started=${SECONDS}
  run_capturing_status run_configured_workload "${trace_dir}" "${bound}"
  exit_status=${status}
  wall=$(( SECONDS - started ))
  campaign_recorded_workload_s=${wall}
  campaign_recorded_workload_rss_mb=$(cat "${trace_dir}/workload_rss_mb" \
    2>/dev/null) || campaign_recorded_workload_rss_mb=""
  case "${exit_status}" in
    "${campaign_adapter_timeout_status}"|"${campaign_adapter_killed_status}")
      [[ -z "${bound}" ]] || timed_out=true ;;
  esac
  # A target the recording does not serve is its own outcome: the
  # aggregation's status says only whether any was served.  Each target's
  # plan is about the declared occurrence's (r,c) of its own throw.
  [[ -z "${declared_target_occurrence}" ]] \
    || targets+=(--target-occurrence "${declared_target_occurrence}")
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
# fresh same-JVM seed replay -> strict import -> a streaming pool of worker
# obligations, planned round by round as sessions land and growing the woven
# region set by what replays exposed -> composition, solving, the claim and
# its publication.
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
# How long the recording's workload ran, in seconds, and its JVM's peak
# resident memory, in MB, as the adapter measured it (workload_rss_mb in the
# trace directory) -- do_workload, campaign_record_batch: the seed replay's
# bound is seed_replay_time_factor times the first; a native reproduction
# run is bounded by reproduce_time_factor times it and charged the second.
campaign_recorded_workload_s=""
campaign_recorded_workload_rss_mb=""
# This iteration's task-set membership, decoded once by PLAN from the frozen
# schedule index (PIPELINE §3), one owner per check.
# IMPORT, EXPLORE, the iteration manifest and COMPOSE read these rows; they do
# not re-decode the index, because re-deriving the same membership at five
# stages is five chances to disagree about one frozen file that is written
# once and never rewritten.
campaign_member_rows=""
# When the campaign started (bash SECONDS, this shell's), which its budget
# runs from (campaign_claim_room); and the witness attempt whose confirmed claim ended
# the exploration, whose confirmation the final CONFIRM takes for the same
# model (campaign_confirm).
campaign_started_s=${SECONDS}
campaign_witness_attempt=""

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

# The deepest throwable a failed engine JVM printed into <log> -- the root
# cause of a stack trace, or the error -XX:+ExitOnOutOfMemoryError ended it
# on -- or nothing: what a stage's failure names beside the JVM's exit.
campaign_thrown() {
  grep -E '^(Caused by: |Exception in thread "[^"]*" |Terminating due to )?[[:alnum:]_.$]+(Exception|Error)(: |$)' \
    -- "$1" 2>/dev/null | tail -n 1 \
    | sed -E 's/^(Caused by: |Exception in thread "[^"]*" |Terminating due to )//'
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
      then {iterationId,
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

campaign_preflight() {
  validate_config >/dev/null
  [[ -n "${concolic_replay_command}" ]] || die \
    "campaign requires concolic_replay_command: the workload adapter that replays one immutable task plan under the concolic VM"
  require_command_available jq
  require_command_available sha256sum
  campaign_log "maxJobs=${schedule_max_jobs} maxWaves=${region_path_max_waves}"
  campaign_log "obligation pool: host(s) \
${campaign_worker_hosts:-$(hostname) (local only)}, each as many as its \
memory admits, up to its cores"
  campaign_log "replay scratch: \
${campaign_local_scratch_root:-<shared home, as before>}"
  # Every peer is reached once before the seed replay, not for the first time
  # somewhere inside round 0 with a hundred obligations already planned.
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

# One command under a wall-clock bound, in its own process group, and that
# group gone when this returns.
#
# `timeout` is not given --foreground, so it puts itself and the command in a
# NEW process group (its own pid) and signals that whole group on expiry: the
# adapter's login shell, the workload's launcher and the replay JVM it forked
# all receive it -- a hung replay is a JVM several processes below the
# worker.  But `timeout` returns when ITS child does, and a TERM ends the
# login shell at once while the JVM below it still runs its shutdown hooks:
# solr-18406 ra1, five obligations past replay_timeout_s=2400, each JVM's
# close rewrote the verdict ADMITTED, naming the session the worker had
# withdrawn a second or two before, and the head waited for that session
# until the wave failed.  So the group is ended here, before the caller reads
# a byte the command wrote (campaign_end_process_group).
run_under_wall_clock_bound() {
  local seconds=$1 group status=0
  shift
  timeout --kill-after="${campaign_adapter_kill_grace_s}s" "${seconds}s" \
    "$@" &
  group=$!
  wait "${group}" || status=$?
  campaign_end_process_group "${group}"
  return "${status}"
}

# Nothing of process group <pgid> runs any more: what is left gets TERM, the
# kill grace, then KILL.  A KILLed process runs no code of its own again,
# even while a pending I/O keeps it listed, so KILL is where the wait ends.
campaign_end_process_group() {
  local group=$1 waited=0
  while kill -0 -- "-${group}" 2>/dev/null; do
    if (( waited >= campaign_adapter_kill_grace_s )); then
      kill -KILL -- "-${group}" 2>/dev/null || true
      return 0
    fi
    (( waited > 0 )) || kill -TERM -- "-${group}" 2>/dev/null || true
    sleep 1
    waited=$((waited + 1))
  done
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
# reaches it has hit something no declared budget describes, and it is
# answered as unfinished, naming the host (campaign_obligation_unfinished).
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
# manifest's provenance would be a lie about half the campaign.  And the
# workflow file itself lives on that same shared home and can be edited
# mid-run; forwarding the values means an edit cannot reach a worker,
# because every key it could change arrives already decided.
campaign_remote_env_assignments() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    [[ -n "${config_env}" && "${config_flags}" == *k* ]] || continue
    printf '%s=%s\n' "${config_env}" "${!config_key}"
  done
}

# The script one peer runs for one piece of a campaign's work: run_engine.sh
# in a peer mode, <mode> <args...> (--run-obligation, --run-placed), under
# <bound_s>, its stdout.log and stderr.log in <dir>, charged to the ledger
# its head charges (CAUSYNTH_HOST_LEDGER, under the same ceiling): a peer's
# own starts -- its host's solver, a replay that outgrows its charge
# (campaign_watch_workload) -- are the same hosts' rows.
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
  local script=$1 dir=$2 bound=$3 mode=$4
  shift 4
  local jar_sha assignment
  jar_sha=$(campaign_digest "${graphchecker_jar}")
  {
    printf '%s\n' '#!/usr/bin/env bash'
    printf '%s\n' \
      '# Generated by run_engine.sh for ONE piece of work on ONE host.' \
      '# Read the campaign_write_remote_worker_script comment for why each' \
      '# line is here.  Regenerated per obligation; never edited by hand.' \
      'set -uo pipefail' \
      '' \
      'wrapper_pid=$$' \
      'wrapper_parent=$(awk "{print \$4}" "/proc/${wrapper_pid}/stat" \' \
      '  2>/dev/null || echo 1)' \
      ''
    printf 'timeout --kill-after=%ss %ss \\\n' \
      "${campaign_adapter_kill_grace_s}" "${bound}"
    printf '  env \\\n'
    printf '    PATH=%q \\\n' "${PATH}"
    printf '    HOME=%q \\\n' "${HOME}"
    printf '    CAUSYNTH_LOCAL_SCRATCH=%q \\\n' "${campaign_local_scratch_root}"
    printf '    CAUSYNTH_HOST_LEDGER=%q \\\n' "${campaign_host_gate_root}"
    printf '    CAUSYNTH_HOST_MAX_USED_PCT=%q \\\n' \
      "${campaign_host_max_used_pct}"
    while IFS= read -r assignment; do
      printf '    %q \\\n' "${assignment}"
    done < <(campaign_remote_env_assignments)
    printf '  %q --config %q %q \\\n' \
      "${graphchecker_dir}/run_engine.sh" "${config_file}" "${mode}"
    printf '    --graphchecker-jar %q \\\n' "${graphchecker_jar}"
    printf '    --graphchecker-jar-sha256 %q \\\n' "${jar_sha}"
    printf '    --'
    printf ' %q' "$@"
    printf ' \\\n'
    printf '  >%q 2>%q &\n' "${dir}/stdout.log" "${dir}/stderr.log"
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

# One peer mode's work on <host>, from <dir> (campaign_write_remote_worker_
# script): its exit.  The payload writes stdout.log and stderr.log itself,
# on the shared home, so its logs read the same whichever machine ran it.
# What lands in ssh.log is ssh's OWN diagnostics -- a refused connection, a
# host key, a peer that has no /bin/bash -- which would otherwise be the one
# part of a failed remote run that nothing recorded.
campaign_dispatch_remote() {
  local host=$1 dir=$2 bound=$3 status=0
  shift 3
  campaign_write_remote_worker_script "${dir}/remote-worker.sh" "${dir}" \
    "${bound}" "$@"
  run_capturing_status campaign_ssh "${campaign_ssh_options[@]}" -- \
    "${host}" "exec /bin/bash $(printf '%q' "${dir}/remote-worker.sh")" \
    >"${dir}/ssh.log" 2>&1
  return "${status}"
}

# The peer's evidence, visible HERE.
#
# Bounded, never assumed: see campaign_remote_visibility_wait_s.  The
# directory is re-listed on each turn because it is the directory's cached
# listing, not the file's contents, that a fresh lookup has to get past.
campaign_await_remote_result() {
  local worker=$1 host=$2 obligation_id=$3
  local result="${worker}/obligation_result.jsonl"
  local staged="${worker}/sessions"
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
  # A verdict that names no session staged none.  The solver's own opened
  # none; a replay's opened one that the peer withdrew (killed on its bound,
  # or decided by a refusal), and a listing cached here may still hold it,
  # where the head would land it.
  if [[ -z "${session_id}" ]]; then
    while [[ -n "$(campaign_sessions_naming "${obligation_id}" \
        "${staged}")" ]]; do
      if [[ "${waited}" -ge "${campaign_remote_visibility_wait_s}" ]]; then
        campaign_log "obligation ${obligation_id} on ${host}: its result \
names no session but a session naming it is still under ${staged} here \
after ${waited}s"
        return 1
      fi
      ls "${staged}" >/dev/null 2>&1 || true
      sleep 1
      waited=$((waited + 1))
    done
    return 0
  fi
  while [[ ! -d "${staged}/${session_id}" ]]; do
    if [[ "${waited}" -ge "${campaign_remote_visibility_wait_s}" ]]; then
      campaign_log "obligation ${obligation_id} on ${host}: its result names \
session ${session_id} but ${staged}/${session_id} is still not visible \
here after ${waited}s"
      return 1
    fi
    ls "${staged}" >/dev/null 2>&1 || true
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
  local host pid
  local -a reaping=()
  [[ -n "${campaign_worker_hosts}" ]] || return 0
  [[ -n "${campaign_root}" ]] || return 0
  # Every peer at once: each waits out its own kill grace.
  for host in ${campaign_worker_hosts}; do
    campaign_host_is_local "${host}" && continue
    campaign_reap_on_host "${host}" "${campaign_root}" &
    reaping+=("$!")
  done
  for pid in "${reaping[@]}"; do
    wait "${pid}" || true
  done
  [[ "${#reaping[@]}" -eq 0 ]] || campaign_log "reaped this run's remote \
workers on ${#reaping[@]} host(s) matching ${campaign_root}"
}

# Every process of this user on <host> whose command line matches <pattern>:
# TERM, and KILL after the kill grace when any matched.  The pattern goes
# over stdin, so the shell doing the matching does not carry it.
campaign_reap_on_host() {
  local host=$1 pattern=$2 script
  script="pattern=$(printf '%q' "${pattern}")
pkill -TERM -u \"\$(id -u)\" -f \"\${pattern}\" 2>/dev/null || exit 0
sleep ${campaign_adapter_kill_grace_s}
pkill -KILL -u \"\$(id -u)\" -f \"\${pattern}\" 2>/dev/null || true"
  if campaign_host_is_local "${host}"; then
    bash -s <<<"${script}" >/dev/null 2>&1 || true
  else
    # Not campaign_ssh_options: that list carries -n, and this one speaks to
    # the far side through stdin.
    ssh -o BatchMode=yes -o ConnectTimeout=20 -- "${host}" 'bash -s' \
      <<<"${script}" >/dev/null 2>&1 || true
  fi
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
# campaign reads its PLAN again): the declared occurrence as the seed's
# aggregation resolved it against the recording -- a sweep's "first", a
# selector's k-th match, an address itself (RuntimeWorkflowDiscovery
# #declaredOccurrence), marked on its plan row and stated by the index, so no
# later stage counts a selector's k again over activations the question left
# out -- the frozen region plan, and the one task-set membership decode -- the
# index is frozen beside its rows and every later stage reads the rows.
campaign_plan_read() {
  local iteration_dir=$1
  local index="${iteration_dir}/runtime_workflow_schedule_index.json"
  local resolved
  resolved=$(jq -r '.target.occurrenceId // ""' "${index}")
  [[ -n "${resolved}" ]] \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the schedule index names no declared target occurrence"
  [[ "${resolved}" == "${declared_target_occurrence}" ]] \
    || campaign_log "declared target ${declared_target_occurrence} = ${resolved}"
  declared_target_occurrence=${resolved}
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

# One union instrumentation pass over the whole iteration plan, into a class
# tree: the iteration's own (INSTRUMENT), or a GROW generation's, which no
# replay reads before this returns -- a replay started earlier keeps the
# tree it started on (campaign_stream_grow).
campaign_instrument() {
  local iteration_dir=$1
  local classes=${2:-${iteration_dir}/instrumented-classes}
  local plan="${iteration_dir}/execution_task_plan.jsonl"
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
  campaign_analyze INSTRUMENT "$(dirname "${classes}")/instrument.log"
  unset CAUSYNTH_CONCOLIC_TASK_PLAN CAUSYNTH_CONCOLIC_TASK_ID
  [[ -n "$(find "${classes}" -name '*.class' -print -quit 2>/dev/null)" ]] \
    || campaign_fail INSTRUMENT CAMPAIGN "${classes}" \
      "union instrumentation wrote no class file"
  campaign_verify_woven_classes "${classes}"
}

# The JVM verifier is the authority on whether woven bytecode is executable,
# and INSTRUMENT is the stage that asks it.  Asked for the first time inside a
# replay instead, its answer arrives as a VerifyError hours into the campaign
# at a method the campaign never mentions, and REPLAY reports a failed
# workload method.  The class loader
# is the replay's own layout -- execute.sh composes ${classes}:${jar}:${cp} --
# so a class that links here links there.
campaign_verify_woven_classes() {
  local classes=$1
  local report
  report="$(dirname "${classes}")/woven_class_verification.log"
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
# $7 is the memory, in MB, its host was charged for the replay JVM, which
# sizes its heap and what it may hold (execute.sh, campaign_watch_workload).
# $8 says what an all-skipped result means to this caller. A seed replay is
# the iteration's only source of observed cases, so "required" (the default)
# makes REPLAY fail closed on one. A flip worker may legitimately replay a
# model the workload never realized, and campaign_obligation_worker already records
# that as REPLAY_NOT_ADMITTED, so it passes "tolerated" and keeps that
# recorded outcome instead of ending the campaign.
campaign_replay() {
  local role=$1 plan=$2 ids=$3 classes=$4 results=$5 worker=$6 charged=$7
  local region_results=${8:-required}
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
    "CAUSYNTH_CHARGED_MB=${charged}" \
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
      "the concolic replay ran no TARGET_REACH occurrence (exit ${status}); no session published a target row of a TARGET_SITE of ${causynth_static_scope_map}; the workload's terminating exception is in ${worker}/replay.log; the declared task: $(campaign_target_unanswered "${sessions}")"
  fi
  campaign_log "replay role=${role} exit=${status} sessions=${sessions}"
}


# Why a replay's sessions did not answer the declared occurrence: the
# TASK_UNANSWERED row they state for PLAN's TARGET member (the activations
# that came nearest and how each differed: another node, an anchor no
# message of the run minted), cut to 600 characters, or nothing.
campaign_target_unanswered() {
  local sessions=$1 task
  task=$(awk -F'\t' '$1 == "TARGET" {print $6; exit}' \
    <<<"${campaign_member_rows}")
  [[ -n "${task}" ]] || return 0
  find "${sessions}" -mindepth 2 -maxdepth 2 -name gaps.jsonl -print0 \
    | xargs -0 -r jq -r --arg task "${task}" \
      'select(.kind == "TASK_UNANSWERED" and .subject == $task) | .detail' \
    | head -n 1 | cut -c1-600
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

# REPLAY: the seed replay, charged its need (campaign_replay_need_mb) and
# placed where there is room (campaign_head_charged: it reads and writes only
# the iteration), under a wall clock derived from the recording
# (seed_replay_time_factor): the seed is the iteration's only source of
# observed cases, so a replay past it is a campaign failure at REPLAY, named,
# not a recorded verdict.
campaign_session_replay() {
  local iteration_dir=$1 bound need
  bound=$(( seed_replay_time_factor * campaign_recorded_workload_s ))
  (( bound >= replay_timeout_s )) || bound=${replay_timeout_s}
  need=$(campaign_replay_need_mb)
  campaign_head_charged "${need}" 300 campaign_seed_replay "${iteration_dir}" \
    "${causynth_static_scope_map}" "${need}" "${bound}" \
    "seed_replay_time_factor=${seed_replay_time_factor} x the recording's \
${campaign_recorded_workload_s}s workload and at least \
replay_timeout_s=${replay_timeout_s}"
}

# The memory, in MB, the seed and the CONFIRM replay are charged: the
# recording's own measured peak (workload_rss_mb, what a native run of it is
# charged, REPRODUCE) times campaign_replay_memory_factor when that is above
# one obligation's replay (obligation_memory_mb), else that.  A concolic
# replay outgrows its native recording: round x1's eleven seed replays
# peaked at 0.65 to 6.94 times it (hdfs-17960 4.89, solr-18413 3.65,
# solr-18406 6.94; the block-key cases under 1.2).  One that outgrows its
# charge still grows it while its host has real room
# (campaign_watch_workload).
campaign_replay_memory_factor=7
campaign_replay_need_mb() {
  local rss=${campaign_recorded_workload_rss_mb}
  if [[ "${rss}" =~ ^[0-9]+$ ]] \
      && (( rss * campaign_replay_memory_factor > obligation_memory_mb )); then
    printf '%s\n' "$(( rss * campaign_replay_memory_factor ))"
  else
    printf '%s\n' "${obligation_memory_mb}"
  fi
}

# campaign_seed_replay <iteration_dir> <scope_map> <charged_mb> <bound_s>
# <rule>: the seed replay itself, on whichever host its charge placed it
# (run_engine.sh --run-placed).  What it reads of its head is in its
# arguments -- a batch group's seed replays under its own scope map, and
# under the bound <rule> states -- or in the run's configuration.
campaign_seed_replay() {
  local iteration_dir=$1 causynth_static_scope_map=$2 charged=$3 bound=$4
  local rule=$5
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
  local campaign_sessions_dir="${iteration_dir}/sessions"
  mkdir -p "${campaign_sessions_dir}"
  # The seed replay is held to the RECORDING's schedule: the plan it runs
  # was built from that execution, so its occurrences are the recording's
  # in the recording's order.  A focused replay's prefix is its own task's,
  # beside its focus row (runtime.ScheduleLog#PREFIX_FILE).
  local recorded_schedule="${iteration_dir}/recorded_schedule.jsonl"
  [[ -s "${recorded_schedule}" ]] || recorded_schedule=""
  campaign_schedule_prefix="${recorded_schedule}" \
    campaign_adapter_timeout_s="${bound}" \
    campaign_adapter_timeout_rule="${bound}s, ${rule}" \
    campaign_replay worker "${plan}" "${ids}" \
    "${iteration_dir}/instrumented-classes" "${results}" "${seed}/focused" \
    "${charged}"
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

# The row contract, checked once per session, where every row passes through.
#
# A defect in a row is not one stage's problem: a row EXPLORE and COMPOSE
# each read as valid can still break the contract, and each stage that meets
# one reports something later and elsewhere.  contract.RowInvariants states
# the contract's own sentences, and the gate runs them
# here: a BLOCKING violation stops the campaign at IMPORT, naming the row, and
# a DIAGNOSTIC one is recorded and the campaign goes on.
#
# campaign_import_gate <iteration_dir> <iteration_id> [summary] [session...]
# gates the named session directories of ${iteration_dir}/sessions -- every
# one not gated yet when none is named (IMPORT: the seed) -- and summarises
# this gate's own sessions into ${summary} (${iteration_dir}/import_gate.json
# by default).  Each session is judged ONCE: ${iteration_dir}/import_gated.txt
# is the ledger of the sessions gated so far, and one it names is not judged
# again.  The rules over the SET -- one seed (invariant 1), the epoch's roots
# (11) -- are judged against the gated sessions still in the corpus, so
# gating a wave, or one session at a time, files exactly what one gate over
# the whole corpus would, each row once (contract.ImportGateMain).  One
# caller at a time: the campaign's head.
#
# The gate holds one session at a time, so its measured need -- its heap and
# its charge on the host it is placed on (engine_java) -- is what the corpus's
# largest session takes (campaign_import_gate_heap_mb), not the case's
# engine heap, which is sized for a JVM holding the whole corpus: charged
# 16 GB, the gate of one 6 MB session waited 7 minutes for room on a busy
# head, and a wave's gate 30 (accept-i1-solr-18406).
#
# Append-only, into the campaign's own gap file: a gap row a later stage
# overwrites was never evidence.
campaign_import_gate() {
  local iteration_dir=$1 iteration_id=$2
  local summary=${3:-${iteration_dir}/import_gate.json}
  local gaps="${iteration_dir}/campaign_gaps.jsonl"
  local blocking violations first session
  local -a gate=()
  shift $(( $# < 3 ? $# : 3 ))
  for session in "$@"; do
    [[ -d "${session}" \
       && "$(dirname -- "${session}")" -ef "${iteration_dir}/sessions" ]] \
      || campaign_fail IMPORT ImportGate "${session}" \
        "not a session directory of ${iteration_dir}/sessions"
    gate+=(--gate "$(basename -- "${session}")")
  done
  engine_need_mb=$(campaign_import_gate_heap_mb "${iteration_dir}/sessions") \
    run_java_main \
    edu.uva.liftlab.graphchecker.contract.ImportGateMain \
    --sessions "${iteration_dir}/sessions" "${gate[@]}" \
    --gated "${iteration_dir}/import_gated.txt" \
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

# The import gate's heap, in MB, over the session directories under ${1}: it
# holds one session at a time, read whole (the gate reads again a session it
# gated before when a new one brings a root), so 512 MB plus four times the
# largest session's size on disk.  Measured: SOLR-18406's 41 MB focused
# session gates in 64 MB of heap and not in 48 (accept-i1-solr-18406), and
# hdfs-11741's 175 sessions of up to 21 MB in 512.
campaign_import_gate_heap_mb() {
  local sessions=$1 entry size largest=0
  for entry in "${sessions}"/*/; do
    # A session withdrawn while it is measured is not one the gate reads.
    size=$(du -s -m -- "${entry}" 2>/dev/null) || continue
    size=${size%%[[:space:]]*}
    (( size <= largest )) || largest=${size}
  done
  printf '%s\n' "$(( 512 + 4 * largest ))"
}


# The session directories whose manifest names one obligation, one per line.
#
# Found by the manifest, which is the same lookup settled() does -- read the
# document and match one element of obligationIds exactly -- and never by
# diffing a directory: the corpus holds every obligation's sessions, and a
# manifest that cannot be read is a session half written: skipped, not
# guessed at.
campaign_sessions_naming() {
  local obligation_id=$1 sessions=$2 manifest
  # SessionDir.MANIFEST, one directory down: <sessions>/<sessionId>/.
  for manifest in "${sessions}"/*/manifest.json; do
    [[ -f "${manifest}" ]] || continue
    # `any(...; . == $id)` is an exact element match: an obligation id that
    # is a prefix of another's does not answer for it.
    jq -e --arg id "${obligation_id}" \
      'any((.obligationIds // [])[]; . == $id)' "${manifest}" \
      >/dev/null 2>&1 || continue
    dirname "${manifest}"
  done
}

# The sessions that name one obligation, out of <sessions> -- the worker's
# staging directory, or the corpus -- and under the worker that owned them.
#
# Four callers.  A replay killed on its bound has opened its session --
# SessionPublisher writes manifest.json at the OPEN -- and will never close
# it, so its rows state no verdict for the obligation the manifest names;
# Composer.settled reads exactly that pair as UNSTATED_VALUE/BLOCKING, and
# one hung JVM would withhold the whole candidate.  A replay a refusal
# decided ended there and names no session in its verdict (PIPELINE §7.6):
# what it wrote is a prefix of a run.  A worker that did not finish staged
# what it staged.  A replay that exposed a region ran without that region's
# hooks, and the re-run's session is the one the corpus keeps.  Each way the
# directory is MOVED under the worker, never deleted: it is the evidence of
# why the obligation's verdict is what it is, and the campaign keeps what it
# saw.
campaign_withdraw_sessions() {
  local obligation_id=$1 sessions=$2 quarantine=$3 why=$4
  local session_dir session_id withdrawn=0
  while IFS= read -r session_dir; do
    session_id=$(basename "${session_dir}")
    mkdir -p "${quarantine}"
    if mv -- "${session_dir}" "${quarantine}/${session_id}"; then
      withdrawn=$((withdrawn + 1))
      campaign_log "obligation ${obligation_id}: withdrew session \
${session_id} from ${sessions} to ${quarantine}/${session_id}: ${why}"
    else
      # Not the campaign's death, and not silent either: the session stays
      # where it is, and this line says what it is.
      campaign_log "obligation ${obligation_id}: could not withdraw session \
${session_id} from ${sessions}: ${why}; it stays there"
    fi
  done < <(campaign_sessions_naming "${obligation_id}" "${sessions}")
  if [[ "${withdrawn}" -eq 0 ]]; then
    campaign_log "obligation ${obligation_id}: no session under ${sessions} \
names it; nothing withdrawn"
  fi
}


# ---------------------------------------------------------------------------
# ONE SOLVER PER HOST
#
# An obligation's query is built over the whole corpus (explore.Corpus), and a
# solver JVM per obligation read all of it each time: hdfs-11741 i1, 22 of an
# obligation's 26 s was that read, and solvers took 5h18m of slot time at a
# median of 28 s each, each JVM 3.7-4.4 GB of an 8 GB heap no ledger row
# counted.  So the obligations of an exploration that run on one host are
# answered by ONE solver JVM there (ObligationSolverMain --serve), started
# when the first of them asks.  It answers each question from the corpus as
# it stands when it takes the question -- read again whenever a session
# landed in it or left it since (the head lands sessions as the exploration
# streams), each question from the corpus as read (Corpus#freshLowerings) --
# so its files are the ones a JVM of the question's own would write; and it
# ends once none has come for campaign_solver_idle_s.  Its directory is on
# the host's own disk, named by the corpus it answers from
# (explore.SolverService states the layout); its log, solver-<host>.log, is
# beside the corpus.
#
# The service is charged to the host ledger what it holds: a start's worth
# at its start (campaign_solver_start_mb), and as its resident memory grows
# past that, the growth, as a running JVM's (campaign_watch_workload: refused
# only when the host's real use would pass the ceiling, and then the JVM is
# ended and its question asked again of a solver of its own).  Its start
# never waits: a host with no room for one now answers the question in the
# question's own JVM, under the obligation's charge (campaign_obligation_worker),
# so no question waits behind a start that waits for memory (round x1: 11
# cases' solvers, each charged its 8 GB heap at its start, held their hosts'
# questions 50-75 minutes behind "starting" solvers).  An obligation's own
# charge (obligation_memory_mb) is then its replay's.
# ---------------------------------------------------------------------------

# How long a host's solver waits for another question before it ends: about
# a focused replay's length, so the obligations a host runs next find it
# still there, and a host the pool has left gives its memory back within
# minutes.
campaign_solver_idle_s=300

# The solver's heap, in MB: the 8 GB every solver JVM has had, which no
# solver of the i1 rounds outgrew (their solvers peaked at 7.0 GB RSS).  A
# question it cannot answer is asked once more of a solver of its own at the
# case's engine heap (campaign_obligation_worker).
campaign_solver_heap_mb=8192

# What a solver is charged at its start, in MB; the rest of what it holds is
# charged as it grows (campaign_solver_jvm).  Its heap is the corpus it
# reads and the query it lowers: 0.2 GB over hdfs-17897's three sessions,
# 5 GB over hdfs-11741 i1's 175.  Charged its 8 GB heap at its start,
# a solver waited minutes for room it did not use, and every question of its
# host waited behind it (e2: the first question of a host answered after 1-5
# minutes, the rest in a second; "one needs 8192 MB and 9474 MB stay free").
campaign_solver_start_mb=1024

# The solver directory of the corpus ${1} (an iteration's sessions), on this
# host: named by the host too, since a pid means something on one host only.
campaign_solver_dir() {
  printf '%s/graphchecker-solvers-%s/%s.%s\n' "${TMPDIR:-/tmp}" "$(id -un)" \
    "$(hostname -s)" "$(printf '%s' "$1" | sha256sum | cut -c1-16)"
}

# campaign_solve_obligation <obligation_id> <obligations> <sessions> <worker>:
# the obligation's question, answered by its host's solver into <worker>:
# 0 with the solver's files there, 1 with why it was not answered on stderr
# (a failure that is the obligation's answer, as a solver JVM's exit was), 3
# when the host had no room to start its solver now (the question is then
# its own JVM's, campaign_obligation_worker).
#
# A question no living solver will answer starts one: none runs, or the one
# named ended while the question still waited.  A question a solver took and
# ended on is not asked again, and a worker starts at most one solver, so a
# corpus no solver can read fails each obligation once, by name.  A question
# that waits for its solver says so (campaign_solver_wait_said).
campaign_solve_obligation() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4
  local dir name question answer server pid started=0 file
  local waited=${SECONDS} said=0
  dir=$(campaign_solver_dir "${sessions}")
  name="$(date +%s%N).${BASHPID}.${obligation_id}"
  question="${dir}/requests/${name}"
  answer="${dir}/answers/${name}.json"
  mkdir -p "${dir}/requests" "${dir}/answers" "${dir}/out"
  jq -n -c --arg obligations "${obligations}" --arg id "${obligation_id}" \
    --arg waiter "${BASHPID}" \
    '{obligations: $obligations, obligationId: $id, waiter: $waiter}' \
    >"${question}.part"
  mv -- "${question}.part" "${question}.json"
  while [[ ! -e "${answer}" ]]; do
    until campaign_host_lock "${dir}" "$(date +%s)"; do
      sleep 0.0$(( (RANDOM % 9) + 1 ))
    done
    server=$(cat "${dir}/server" 2>/dev/null) || server=""
    pid=${server##* }
    if [[ -n "${pid}" && -d "/proc/${pid}" || -e "${answer}" ]]; then
      rmdir "${dir}/lock"
      campaign_solver_wait_said "${obligation_id}" "${dir}" "${pid}" \
        "${waited}"
      sleep 0.2
      continue
    fi
    # No solver answers here any more.
    if [[ -e "${question}.taken" || "${started}" -ge 1 ]]; then
      rm -f -- "${question}.taken" "${question}.json"
      rmdir "${dir}/lock"
      file=$(campaign_solver_log "${sessions}")
      printf 'ObligationSolverMain: the solver of %s ended before it ' \
        "$(hostname -s)" >&2
      printf 'answered %s; its log is %s: %s\n' "${obligation_id}" "${file}" \
        "$(grep -v -E '^[[:space:]]+at ' "${file}" 2>/dev/null \
          | tail -n 1)" >&2
      return 1
    fi
    printf 'starting %s\n' "${BASHPID}" >"${dir}/server"
    rmdir "${dir}/lock"
    started=1
    campaign_start_solver "${dir}" "${sessions}" && continue
    # No room for a solver on this host now: the question leaves the queue,
    # and the next question finds no solver starting.
    rm -f -- "${question}.json"
    until campaign_host_lock "${dir}" "$(date +%s)"; do
      sleep 0.0$(( (RANDOM % 9) + 1 ))
    done
    [[ "$(cat "${dir}/server" 2>/dev/null)" != "starting ${BASHPID}" ]] \
      || rm -f -- "${dir}/server"
    rmdir "${dir}/lock"
    return 3
  done
  for file in "${dir}/out/${name}"/*; do
    [[ -e "${file}" ]] || continue
    mv -f -- "${file}" "${worker}/"
  done
  rmdir -- "${dir}/out/${name}" 2>/dev/null || true
  if [[ "$(jq -r '.exit' "${answer}")" != 0 ]]; then
    printf 'ObligationSolverMain: %s\n' "$(jq -r '.error' "${answer}")" >&2
    rm -f -- "${answer}"
    return 1
  fi
  rm -f -- "${answer}"
}

# How long a question waits for its host's solver before it says so, and how
# often it says so again, in seconds: a wait is never silent.
campaign_solver_wait_said_s=60
campaign_solver_wait_again_s=600

# campaign_solver_wait_said <obligation> <dir> <pid> <since>: says, once the
# question has waited campaign_solver_wait_said_s since <since> and every
# campaign_solver_wait_again_s after, what it waits for: the solver <pid> of
# this host and how many questions it has ahead of this one (the caller's
# `said` counts what was said).
campaign_solver_wait_said() {
  local obligation_id=$1 dir=$2 pid=$3 since=$4 waited ahead
  waited=$(( SECONDS - since ))
  (( waited >= campaign_solver_wait_said_s \
     + said * campaign_solver_wait_again_s )) || return 0
  said=$(( said + 1 ))
  ahead=$(find "${dir}/requests" -maxdepth 1 -name '*.json' 2>/dev/null \
    | wc -l)
  campaign_log "obligation ${obligation_id}: waited ${waited}s for the solver \
of $(hostname -s) (pid ${pid}), ${ahead} question(s) waiting"
}

# The log of the solvers that answer from the corpus ${1}, on this host.
campaign_solver_log() {
  printf '%s/solver-%s.log\n' "$(dirname "$1")" "$(hostname -s)"
}

# Starts the host's solver of the corpus <sessions> in <dir> if the host has
# room for its start (campaign_solver_start_mb) now, and names it in
# <dir>/server: the pid of the shell that runs the JVM, which ends with it.
# Returns without waiting for it; 1, starting nothing, when the host has no
# room now or its memory cannot be read: a start that waited for memory held
# every question of its corpus behind it.  The root domains are the
# declaration EXPLORE and COMPOSE read: an answer is only as free as the
# root domains behind the arm that produces it.
campaign_start_solver() {
  local dir=$1 sessions=$2 charge status=0
  campaign_host_try_charge localhost "${campaign_solver_start_mb}" 120
  (( status == 0 )) || return 1
  charge=${campaign_host_charge_id}
  {
    campaign_solver_jvm "${campaign_solver_heap_mb}" \
      "${campaign_solver_start_mb}" --serve "${dir}" \
      --sessions "${sessions}" \
      --idle-seconds "${campaign_solver_idle_s}" \
      </dev/null >>"$(campaign_solver_log "${sessions}")" 2>&1 || true
    campaign_host_release localhost "${charge}"
  } &
  printf '%s\n' "$!" >"${dir}/server.part"
  mv -f -- "${dir}/server.part" "${dir}/server"
}

# campaign_solver_jvm <heap_mb> <charged_mb> <ObligationSolverMain args...>:
# one solver JVM at <heap_mb> (run_java_main's, started here so its pid is
# the JVM's own: java_bin execs java), watched until it ends
# (campaign_watch_workload): what it grows past the <charged_mb> its host
# holds for it is asked of the host as it grows, and a host whose real use
# cannot take it ends it.  Its status.
campaign_solver_jvm() {
  local heap=$1 charged=$2 jvm status=0
  shift 2
  require_file "GraphChecker jar" "${graphchecker_jar}"
  (cd "${graphchecker_work_dir}" \
    && exec env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
      "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
      "-Dcausynth.system.doors=${causynth_system_doors}" \
      -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.explore.ObligationSolverMain \
      --z3 "${z3_bin}" \
      --solver-timeout-ms "${solver_timeout_ms}" \
      ${causynth_root_domains:+--root-domains "${causynth_root_domains}"} \
      "$@") &
  jvm=$!
  campaign_watch_workload "${jvm}" "${charged}"
  wait "${jvm}" || status=$?
  return "${status}"
}

# campaign_solve_obligation_alone <obligation_id> <obligations> <sessions>
# <worker> [now]: the question in a solver JVM of its own at the case's
# engine heap, its files straight into <worker>, its status the JVM's.
# `now`: at once, under the obligation's own charge (its replay's, which
# comes after), for a question whose host had no room for its solver --
# what the JVM grows past that charge is asked of the host as it grows.
# Otherwise once the host has room for the engine heap, charged that while it
# runs: for a question the host's solver, or a JVM of its own, could not
# answer (it ran out of heap or died), never the obligation's answer.
campaign_solve_obligation_alone() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 when=${5:-}
  local heap=${engine_memory_mb:-8192} charge="" charged status=0
  if [[ "${when}" == now ]]; then
    charged=${obligation_memory_mb}
  else
    campaign_await_host_memory localhost "${heap}" 120 || return 1
    charge=${campaign_host_charge_id}
    charged=${heap}
  fi
  run_capturing_status campaign_solver_jvm "${heap}" "${charged}" \
    --obligations "${obligations}" \
    --obligation-id "${obligation_id}" \
    --sessions "${sessions}" \
    --output-dir "${worker}"
  [[ -z "${charge}" ]] || campaign_host_release localhost "${charge}"
  return "${status}"
}

# One obligation: solve it, replay it focused, record its verdict.
#
# The obligation names ONE focused occurrence, the decision it flips, the root
# assignments to apply at the mints and the answers to apply at the attaches
# (CONTRACT-SPEC §3).  The solver reads the corpus <sessions>; the replay
# stages its session in ${worker}/sessions/, which the head lands in the
# corpus once it has read this function's output, the one ObligationResult
# row that says which verdict it reached (campaign_stream_land).
#
# A single obligation that could not be solved or replayed is that
# obligation's own result row, never the campaign's death.
campaign_obligation_worker() {
  local obligation_id=$1 obligations=$2 classes=$3 worker=$4 sessions=$5
  local seed_plan=$6
  local outcome status=0
  # Its start charged the host obligation_memory_mb, its replay's: a local
  # one is a subshell of the head, and its JVMs are not the head's; the
  # host's solver charges its own.
  local campaign_head_charging=0
  local result_row="${worker}/obligation_result.jsonl"
  run_capturing_status campaign_solve_obligation "${obligation_id}" \
    "${obligations}" "${sessions}" "${worker}"
  if [[ "${status}" -eq 3 ]]; then
    # No room for its host's solver now: answered in its own JVM at once,
    # not after a start that waits for memory.
    campaign_log "obligation ${obligation_id}: no room on $(hostname -s) \
to start its solver now; answered in a solver JVM of its own"
    run_capturing_status campaign_solve_obligation_alone "${obligation_id}" \
      "${obligations}" "${sessions}" "${worker}" now
  fi
  if [[ "${status}" -ne 0 ]]; then
    # A solver that ran out of heap or died answered nothing about the
    # obligation, and settles no question, whatever it left: asked once
    # more, of a solver of its own.  Twice: the worker did not finish
    # (campaign_obligation_unfinished), never an answer.
    rm -f -- "${worker}/question.txt" "${worker}/question.asked"
    campaign_log "obligation ${obligation_id}: its host's solver did not \
answer ($(grep -v -E '^[[:space:]]+at ' "${worker}/stderr.log" 2>/dev/null \
      | tail -n 1)); asked again of a solver of its own at \
${engine_memory_mb:-8192} MB"
    run_capturing_status campaign_solve_obligation_alone "${obligation_id}" \
      "${obligations}" "${sessions}" "${worker}"
    if [[ "${status}" -ne 0 ]]; then
      rm -f -- "${worker}/question.txt" "${worker}/question.asked"
      die "obligation ${obligation_id}: its solver failed twice, its \
host's and one of its own at ${engine_memory_mb:-8192} MB: $(grep -v -E \
        '^[[:space:]]+at ' "${worker}/stderr.log" 2>/dev/null | tail -n 1)"
    fi
  fi
  require_nonempty "obligation solver result" "${result_row}"
  require_nonempty "obligation query" "${worker}/obligation_query.smt2"
  outcome=$(jq -er '.verdict' "${result_row}")
  # The solver owns what a finished obligation is.  UNSAT and NOT_ADMITTED
  # are recorded terminal verdicts, not process failures, and the next round
  # reads them so the obligation is not proposed again; so is an ADMITTED
  # the solver reused from the same question a worker settled
  # (ObligationFactory#solve).
  case "${outcome}" in
    UNSAT|NOT_ADMITTED|ADMITTED) return 0 ;;
  esac
  [[ "${outcome}" == "SAT_MODEL_READY" ]] \
    || die "the obligation verdict is not solver-backed: ${outcome}"
  campaign_obligation_replay "${obligation_id}" "${classes}" "${worker}" \
    "${worker}/sessions" "${seed_plan}" "${obligation_memory_mb}"
}

# The replay half of an obligation: the solver's model, run focused, and the
# verdict the replay states for it, its session published under <sessions>.
# The worker calls it once the solver has answered SAT_MODEL_READY; GROW
# calls it again for an obligation whose replay exposed a region, in a
# directory of its own beside the worker, under the grown class tree; CONFIRM
# for the claim's world.  Every argument is the caller's, so it runs on
# whichever host its start was placed on (--run-placed): <charged_mb> is
# what that start charged its host for the replay JVM.
#
# Two files, one shape each.  execution_task_plan.jsonl is the PLAN, whose
# rows the workload session opener decodes (ConcolicTaskPlan.load ->
# plan.ExecutionTask.decode): a focused replay runs the SEED's plan, hard
# linked here so a row GROW appends to the seed plan is in every worker's.
# The obligation's own focus row is focused_task.jsonl, written by the
# solver and read unchanged by a re-run.
campaign_obligation_replay() {
  local obligation_id=$1 classes=$2 worker=$3 sessions=$4 seed_plan=$5
  local charged=$6
  # Charged as a whole by whoever starts it: the pool, GROW, or CONFIRM.
  local campaign_head_charging=0
  local plan="${worker}/execution_task_plan.jsonl"
  local focus="${worker}/focused_task.jsonl"
  local results="${worker}/concolic_region_results.jsonl"
  local result_row="${worker}/obligation_result.jsonl"
  local statement="${worker}/replay_verdict.jsonl"
  local outcome replay_tasks
  require_nonempty "obligation focus row" "${focus}"
  ln -f "${seed_plan}" "${plan}"
  replay_tasks=$(campaign_task_ids "${plan}")
  [[ -n "${replay_tasks}" ]] \
    || die "the seed plan names no task to replay: ${plan}"
  # Under a wall clock, because a replay JVM that never returns is not a slow
  # obligation but a stopped exploration: its obligation would never land.
  # On expiry the whole process group goes (the JVM is a grandchild of this
  # worker) and this obligation records the same terminal NOT_ADMITTED row a
  # failed solver records -- one obligation's answer, not the campaign's
  # death.
  campaign_sessions_dir="${sessions}" \
    campaign_adapter_timeout_s="${replay_timeout_s}" \
    campaign_adapter_timeout_rule="replay_timeout_s=${replay_timeout_s}" \
    campaign_replay worker "${plan}" "${replay_tasks}" "${classes}" \
      "${results}" "${worker}" "${charged}" tolerated
  # ONE WRITER.  The replay's process group is gone
  # (run_under_wall_clock_bound), so nothing of it writes after this line,
  # and the obligation's answer is written below, once: the replay's own
  # statement (RowRuntime#closeSession writes replay_verdict.jsonl), or the
  # bound's.
  if [[ -n "${campaign_replay_killed}" ]]; then
    # Killed, it decided nothing: its question stays unsettled.
    rm -f -- "${worker}/question.asked"
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
  # THE REPLAY OWNS THE VERDICT: the rows FocusedReplay.results built, the
  # same rows it publishes into the session, which is the evidence.  What is
  # checked is that the replay DID state one; none is neither an admission
  # nor a refusal.
  outcome=$(jq -r '.verdict // ""' "${statement}" 2>/dev/null) || outcome=""
  case "${outcome}" in
    ADMITTED|NOT_ADMITTED|UNSAT) ;;
    *) campaign_fail EXPLORE ObligationSolverMain "${statement}" \
        "the replay of ${obligation_id} stated no verdict for it \
(\"${outcome}\")" ;;
  esac
  # A verdict that names no session published none: a refusal decided every
  # obligation the replay carried, and it ended there (FocusedReplay
  # #refusedAt).  What it wrote before is a prefix of a run, which the replay
  # withdrew itself at its close (RowRuntime#closeSession); one its move left
  # listed is withdrawn here, on the host that ran the replay.
  [[ -n "$(jq -r '.sessionId // ""' "${statement}")" ]] \
    || campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
      "${worker}/refused-sessions" "a refusal decided every obligation its \
replay carried and the replay ended there, so its rows are a prefix of a run"
  # In place, as the solver's row was written: a head reading a peer's file
  # over NFS opens the same inode, fresh on open.
  cat -- "${statement}" >"${result_row}"
  # The replay decided it, so its answer settles the question its solver
  # asked -- unless the replay ended without a publication, which withdrew
  # the question itself (RowRuntime#closeSession).
  [[ ! -e "${worker}/question.asked" ]] \
    || mv -f -- "${worker}/question.asked" "${worker}/question.txt"
}


# ---------------------------------------------------------------------------
# THE POOL'S HOSTS
#
# A campaign's obligations are independent: each asks its host's solver,
# then runs its own replay JVM, writes into its own worker directory and
# stages its session there (${worker}/sessions/), from where the head lands
# it in the corpus.  `campaign_worker_hosts` empty is this machine alone,
# with no ssh anywhere; a stated list is every machine an obligation may run
# on.  How many run on one host at once is that host's to say: one more
# starts while the memory ledger admits its replay, up to the host's cores
# (campaign_stream_admit_host).  How many one exploration runs at once is,
# under a cap (stream_max_in_flight), its share of it: the cap over the
# capped explorations running now, each an entry of the ledger --
#
#   ${campaign_host_gate_root}/explorations/<id>  fresh while its head lives
#
# (campaign_stream_has_slot) -- so the cases a sweep runs at once share
# their hosts' obligation slots (campaign_pool_slots), and one alone takes
# them all.
# ---------------------------------------------------------------------------

# The pool's hosts, one per line: the stated list, or this machine.
campaign_worker_host_list() {
  local -a hosts=()
  read -r -a hosts <<<"${campaign_worker_hosts}"
  [[ ${#hosts[@]} -gt 0 ]] || hosts=(localhost)
  printf '%s\n' "${hosts[@]}"
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
# So every start asks the HOST first -- an obligation's, a campaign
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
# ramp; after it, what it holds is in MemAvailable.  A start is released
# the moment its command returns (campaign_host_release), whoever started
# it, so a head's JVMs, one after another, are never charged twice and an
# answer in seconds does not hold its host's room for the ramp.  A start
# that does not fit WAITS -- an obligation or a head's step goes to another
# host or later, never skipped -- and says so once.  A JVM that grows past
# its charge after its start asks the host again for the excess, by the
# same rule (campaign_watch_workload).
#
#   ${campaign_host_gate_root}/<host>/heads/<id>  "<mb>": a campaign head's
#                                                 room on its host
#
# HEAD ROOM.  A head runs its engine JVMs -- a planner round, a gate, COMPOSE
# -- on its own host first, between the obligations every campaign keeps
# starting there, and a pool keeps every host as full as the ledger allows:
# a head that waited for room like any start would wait for its own host to
# empty (stream1: hdfs-11741's head waited 25 min in SEED).  So a head reserves
# room for its next JVM (campaign_head_reserve): its file states the need,
# fresh while the head lives (campaign_head_heartbeat, at most
# campaign_head_reservation_stale_s apart), idle unless one of its JVMs runs
# (<id>.busy.<pid>: then that JVM's charge and its RSS stand for it).  A
# start that is no head's own counts the largest idle fresh reservation of
# the host as used; a head's own start counts none, so heads take turns as
# they always did and never block each other.
# ---------------------------------------------------------------------------

# shellcheck source=tools/lib/gc-env.sh
source "${graphchecker_dir}/tools/lib/gc-env.sh"
campaign_host_gate_root=${CAUSYNTH_HOST_LEDGER}
# How long an obligation's start is charged in full: the time its replay JVM
# takes to stand its cluster up (the host's solver is charged at its own
# start, campaign_start_solver).  A native run of REPRODUCE, and the excess
# a workload JVM grew past its charge (campaign_watch_workload), take the
# same ramp.
campaign_host_ramp_s=60
# Whether this shell is a campaign's head, whose engine JVMs and replays are
# placed and charged as its steps (do_campaign, campaign_head_charged); an
# obligation's replay is inside the obligation's charge.
campaign_head_charging=0
# The most of a host's memory a start may leave in use, in percent: what
# stays free is the page cache the JVMs read their jars and corpora through,
# the owner's own sessions, and the room JVMs past their ramp still grow into.
campaign_host_max_used_pct=${CAUSYNTH_HOST_MAX_USED_PCT}
[[ "${campaign_host_max_used_pct}" =~ ^[0-9]+$ ]] \
  && (( campaign_host_max_used_pct > 0 && campaign_host_max_used_pct <= 100 )) \
  || die "CAUSYNTH_HOST_MAX_USED_PCT must be a percentage in 1..100: \
${campaign_host_max_used_pct}"
# How often a waiting start asks again, and how old a MemAvailable reading
# may be before it is read again.
campaign_host_poll_s=5
# How long a host may stay unreachable over ssh -- its memory unreadable, a
# worker's connection refused before it started -- before the obligation
# fails by name.  sshd refuses connections under a round's burst of them.
campaign_ssh_patience_s=300
# A lock older than this was left by a campaign that died holding it.
campaign_host_lock_stale_s=30
# A head reservation, or a capped exploration's entry, older than this was
# left by a head that is gone.
campaign_head_reservation_stale_s=600
# This head's reservation file (campaign_head_reserve), or empty, and the
# process that holds it: a subshell of the head (a batch target) exits
# without giving it up.
campaign_head_reservation=""
campaign_head_pid=""
# The hold of the head step waiting for room now (campaign_head_place), or
# empty: a file stating its need among the reservations of the host it will
# take, which every start that is not this head's counts while it is fresh
# (campaign_host_head_room), as a head's reservation.
campaign_head_hold=""
# This exploration's entry among the capped ones (campaign_stream_enroll),
# or empty.
campaign_stream_entry=""
# Set while a head's own start asks the ledger (campaign_head_charged).
campaign_host_head_start=0

# The ledger's name for a host: this machine's short name for a local one,
# so a campaign on lift11 and one addressing lift11 over ssh share one entry.
campaign_host_key() {
  if campaign_host_is_local "$1"; then
    hostname -s
  else
    printf '%s\n' "$1"
  fi
}

# One command's output on one host.  Local: a plain shell.  Remote: the same
# batch-mode ssh every remote obligation uses.
campaign_host_read() {
  local host=$1 read_it=$2
  if campaign_host_is_local "${host}"; then
    bash -c "${read_it}"
  else
    campaign_ssh "${campaign_ssh_options[@]}" -o ConnectTimeout=20 -- \
      "${host}" "${read_it}"
  fi
}

# MemAvailable of one host, in MB.
campaign_host_available_mb() {
  campaign_host_read "$1" \
    "awk '/^MemAvailable:/ {print int(\$2 / 1024)}' /proc/meminfo"
}

# MemTotal of one host, in MB.
campaign_host_total_mb() {
  campaign_host_read "$1" \
    "awk '/^MemTotal:/ {print int(\$2 / 1024)}' /proc/meminfo"
}

# The cores of one host, from the ledger once read: they never move.
campaign_host_cores() {
  local host=$1 dir cores fresh
  dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
  mkdir -p "${dir}"
  if read -r cores 2>/dev/null <"${dir}/cores" \
      && [[ "${cores}" =~ ^[1-9][0-9]*$ ]]; then
    printf '%s\n' "${cores}"
    return 0
  fi
  cores=$(campaign_host_read "${host}" nproc | grep -E '^[0-9]+$' \
    | tail -n 1) || return 1
  [[ "${cores}" =~ ^[1-9][0-9]*$ ]] || return 1
  fresh=$(mktemp "${dir}/cores.XXXXXX") || return 1
  printf '%s\n' "${cores}" >"${fresh}"
  mv -f -- "${fresh}" "${dir}/cores"
  printf '%s\n' "${cores}"
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
  # A name of its own: the campaign's subshells share $$, and
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

# campaign_host_try_start <host> <need_mb> <ramp_s>: one try.  0 when the
# start may go now and is charged to the host, its row named in
# campaign_host_charge_id; 1 when it does not fit yet (why, in
# campaign_host_wait_reason); 2 when the host's memory cannot be read; 3 when
# another start holds the ledger's lock for the instant it takes to charge
# one.  Every start states its need -- what the JVM measurably takes -- and
# the ramp it takes to reach it; neither has a default.
campaign_host_wait_reason=""
campaign_host_charge_id=""
campaign_host_try_start() {
  local host=$1 need=$2 ramp=$3 key dir now available total
  local reserve charged kept held=0
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  reserve=$(( total * (100 - campaign_host_max_used_pct) / 100 ))
  [[ "${campaign_host_head_start}" == 1 ]] \
    || held=$(campaign_host_head_room "${dir}" "${now}")
  campaign_host_lock "${dir}" "${now}" || return 3
  kept=$(campaign_host_in_ramp "${dir}" "${now}")
  charged=$(awk '{ mb += $2 } END { print mb + 0 }' <<<"${kept}")
  [[ -z "${kept}" ]] || kept+=$'\n'
  if (( available - charged - held < need + reserve )); then
    printf '%s' "${kept}" >"${dir}/starts"
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${available} MB available, \
${charged} MB charged to starts still in their ramp and ${held} MB held for \
a head; one needs ${need} MB and ${reserve} MB stay free (at most \
${campaign_host_max_used_pct}% of ${total} MB in use)"
    return 1
  fi
  campaign_host_charge_row "${dir}" "${kept}" "${now}" "${need}" "${ramp}"
  return 0
}

# Writes <dir>/starts as <kept> plus one row charging <need_mb> for <ramp_s>
# from <now>, named in campaign_host_charge_id, and gives the ledger's lock
# back.
campaign_host_charge_row() {
  local dir=$1 kept=$2 now=$3 need=$4 ramp=$5
  campaign_host_charge_id="$(hostname -s).${BASHPID}.${now}.${RANDOM}"
  printf '%s%s %s %s %s\n' "${kept}" "${now}" "${need}" "${ramp}" \
    "${campaign_host_charge_id}" >"${dir}/starts"
  rmdir "${dir}/lock"
}

# campaign_host_try_grow <host> <mb>: a RUNNING JVM grows by <mb>.  What the
# ledger promises future starts -- their ramps, a head's room -- is no
# reason to end a JVM already running: the growth is refused (1, the reason
# in campaign_host_wait_reason) only when the host's real use, MemTotal less
# MemAvailable, would pass CAUSYNTH_HOST_MAX_USED_PCT with it.  Granted, it
# is charged on the ledger as a start (0, its row in
# campaign_host_charge_id), so the starts after it wait for it.  2 when the
# host's memory cannot be read, 3 while another holds the ledger's lock.
campaign_host_try_grow() {
  local host=$1 mb=$2 key dir now total available kept
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  campaign_host_lock "${dir}" "${now}" || return 3
  if (( total - available + mb > total * campaign_host_max_used_pct / 100 ))
  then
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${available} MB available of \
${total} MB, and ${mb} MB more would put over \
${campaign_host_max_used_pct}% of it in use"
    return 1
  fi
  kept=$(campaign_host_in_ramp "${dir}" "${now}")
  [[ -z "${kept}" ]] || kept+=$'\n'
  campaign_host_charge_row "${dir}" "${kept}" "${now}" "${mb}" \
    "${campaign_host_ramp_s}"
  return 0
}

# The largest idle, fresh head reservation of one host's ledger directory,
# in MB (HEAD ROOM above), this head's own hold aside; 0 when there is none.
campaign_host_head_room() {
  local dir=$1 now=$2 file need held=0 busy
  for file in "${dir}"/heads/*; do
    [[ -f "${file}" && "${file}" != *.busy.* \
       && "${file}" != "${campaign_head_hold}" ]] || continue
    for busy in "${file}".busy.*; do
      [[ -e "${busy}" ]] && continue 2
    done
    (( now - $(stat -c %Y "${file}" 2>/dev/null || echo 0) \
      < campaign_head_reservation_stale_s )) || continue
    read -r need 2>/dev/null <"${file}" || continue
    [[ "${need}" =~ ^[0-9]+$ ]] && (( need > held )) && held=${need}
  done
  printf '%s\n' "${held}"
}

# This head's room on its host (HEAD ROOM above), until the head exits
# (its EXIT trap, campaign_head_unreserve).
campaign_head_reserve() {
  local dir
  dir="${campaign_host_gate_root}/$(campaign_host_key localhost)/heads"
  mkdir -p "${dir}"
  campaign_head_pid=${BASHPID}
  campaign_head_reservation="${dir}/$(hostname -s).${BASHPID}.$(date +%s)"
  campaign_head_need_mb >"${campaign_head_reservation}"
  trap campaign_head_unreserve EXIT
}

# The head lives: its reservation stays fresh, and states what its next
# planner or composer starts at now (one that outgrew its need starts
# higher from then on); so do the hold of a step it waits to place and its
# capped exploration's entry.
campaign_head_heartbeat() {
  [[ -z "${campaign_head_reservation}" ]] \
    || campaign_head_need_mb >"${campaign_head_reservation}" 2>/dev/null \
    || true
  local fresh
  for fresh in "${campaign_head_hold}" "${campaign_stream_entry}"; do
    [[ -z "${fresh}" ]] || touch -c -- "${fresh}" 2>/dev/null || true
  done
}

# The head is done (or failed): its room, and a waiting step's hold, are the
# hosts' again.
campaign_head_unreserve() {
  [[ -z "${campaign_head_hold}" ]] || rm -f -- "${campaign_head_hold}"
  campaign_head_hold=""
  [[ -n "${campaign_head_reservation}" \
     && "${BASHPID}" == "${campaign_head_pid}" ]] || return 0
  rm -f -- "${campaign_head_reservation}" "${campaign_head_reservation}".busy.*
  campaign_head_reservation=""
}

# The rows of <dir>/starts still inside their own ramp at <now>, as they
# stand there, one per line.
campaign_host_in_ramp() {
  local dir=$1 now=$2 at mb row_ramp id
  [[ -f "${dir}/starts" ]] || return 0
  while read -r at mb row_ramp id; do
    [[ "${at}" =~ ^[0-9]+$ && "${mb}" =~ ^[0-9]+$ \
      && "${row_ramp}" =~ ^[0-9]+$ ]] || continue
    (( now - at < row_ramp )) || continue
    printf '%s %s %s %s\n' "${at}" "${mb}" "${row_ramp}" "${id}"
  done <"${dir}/starts"
}

# The room, in MB, one more start that is no head's own may take on <host>
# now, read without charging it (campaign_host_try_start decides, under the
# host's lock): MemAvailable less what the starts in their ramp will still
# claim, the room a head holds there, and the reserve.  2 when unreadable.
campaign_host_room() {
  local host=$1 dir now total available charged
  dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  charged=$(campaign_host_in_ramp "${dir}" "${now}" \
    | awk '{ mb += $2 } END { print mb + 0 }')
  printf '%s\n' "$(( available - charged \
    - $(campaign_host_head_room "${dir}" "${now}") \
    - total * (100 - campaign_host_max_used_pct) / 100 ))"
}

# campaign_pool_slots <need_mb> <host>...: how many starts of <need_mb> the
# hosts hold at once when each holds its charge -- on each host, as many as
# fit under its ceiling (CAUSYNTH_HOST_MAX_USED_PCT of its MemTotal) and no
# more than its cores, both from the ledger -- summed: the obligation slots
# an ad-hoc sweep's cases share (stream_max_in_flight, tools/adhoc/sweep.sh).
# A host whose memory or cores cannot be read adds none.
campaign_pool_slots() {
  local need=$1 host dir total cores fit slots=0
  shift
  for host in "$@"; do
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
    mkdir -p "${dir}"
    total=$(campaign_host_memory_total "${host}" "${dir}") || continue
    cores=$(campaign_host_cores "${host}") || continue
    fit=$(( total * campaign_host_max_used_pct / 100 / need ))
    (( fit <= cores )) || fit=${cores}
    slots=$(( slots + fit ))
  done
  printf '%s\n' "${slots}"
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

# campaign_host_try_start, the ledger's lock waited out -- another start
# holds it for the instant it takes to be charged: its answer, 0, 1 or 2, in
# the caller's `status`.
campaign_host_try_charge() {
  campaign_host_unlocked campaign_host_try_start "$@"
}

# <try> <args...> (campaign_host_try_start or campaign_host_try_grow), its
# answer 3 -- the ledger's lock held for the instant a charge takes --
# waited out: its other answer in the caller's `status`.
campaign_host_unlocked() {
  while true; do
    run_capturing_status "$@"
    (( status != 3 )) && return 0
    sleep 0.$(( (RANDOM % 9) + 1 ))
  done
}

# The resident memory of process <pid>, in MB; nothing once it is gone.
campaign_process_rss_mb() {
  awk '/^VmRSS:/ {print int($2 / 1024)}' "/proc/$1/status" 2>/dev/null
}

# How often a workload JVM's resident memory is read.
campaign_watch_interval_s=2

# campaign_watch_workload <pid> <charged_mb> [trace_dir]: one workload JVM
# watched until it ends (experiments/lib/execute.sh).  Its peak resident
# memory, in MB, goes to <trace_dir>/workload_rss_mb, a recording's: what a
# native run of it is charged (REPRODUCE); for a JVM its host was charged
# <charged_mb> for (0: none, a recording) it is said at its end beside that
# charge, the evidence a case's obligation_memory_mb is set from.  Such a
# JVM that grows past what its host holds for it asks the host for the
# excess (campaign_host_try_grow: refused only when the host's real use
# would pass CAUSYNTH_HOST_MAX_USED_PCT, never for what the ledger promised
# future starts) and holds what it was granted; one the host cannot take is
# ended there, and says so.  A replay whose native symbolic
# state ran away reached 27 GB and the kernel killed what it chose on the
# host (hdfs-17960 v96); one ended for 41 MB over its 2500 MB on a host with
# 28 GB free failed its case for nothing (accept-e1b-17960's seed replay),
# and one refused 6 MB on a host with 16 GB free, all of it promised to
# ramps and heads (accept-x1-17960's).
# What it was granted is released when it ends.
campaign_watch_workload() {
  local pid=$1 charged=$2 trace=${3:-} peak=0 held=$2 mb id
  local status=0 refused=""
  local -a grants=()
  while kill -0 "${pid}" 2>/dev/null; do
    mb=$(campaign_process_rss_mb "${pid}") || mb=""
    if (( ${mb:-0} > peak )); then
      peak=${mb}
      [[ -z "${trace}" ]] \
        || printf '%s\n' "${peak}" >"${trace}/workload_rss_mb"
    fi
    if (( charged > 0 && peak > held )); then
      campaign_host_unlocked campaign_host_try_grow localhost \
        "$(( peak - held ))"
      if (( status != 0 )); then
        refused="the host cannot take the $(( peak - held )) MB more \
(${campaign_host_wait_reason})"
        kill -KILL "${pid}" 2>/dev/null || true
        break
      fi
      grants+=("${campaign_host_charge_id}")
      held=${peak}
    fi
    sleep "${campaign_watch_interval_s}"
  done
  for id in "${grants[@]}"; do
    campaign_host_release localhost "${id}"
  done
  (( charged > 0 )) || return 0
  [[ -z "${refused}" ]] || echo "causynth: the workload JVM's resident \
memory reached ${peak} MB, over the ${held} MB its host holds for it, and \
${refused}; ended" >&2
  echo "causynth: the workload JVM's resident memory peaked at ${peak} MB; \
its host was charged ${charged} MB for it$( (( held == charged )) \
    || echo " and took ${held} MB as it grew")" >&2
}

# campaign_head_charged <need_mb> <ramp_s> <command...>: one heavy start of
# a campaign head -- an engine JVM of any stage, the seed or the CONFIRM
# replay, a native run of REPRODUCE -- goes where there is room
# (campaign_head_place), is charged there while it runs, and is released
# when it returns.  Every such step reads and writes only the run's shared
# directories (the case's scope copy among them, experiments/lib/case-env.sh)
# and takes the rest of what it reads of the head as its arguments, so it
# runs alike on whichever host it was placed on: here, or through the remote
# worker script (campaign_run_placed).  What a head runs uncharged stays on
# its host: the setup adapter's copy and the recording (do_workload).
# Outside a head it runs the command alone.  The command runs as a plain
# command, so errexit means inside it what it meant before: a failure that
# ends the shell leaves the charge to lapse with its ramp.
campaign_head_charged() {
  local need=$1 ramp=$2 id status busy="" host
  shift 2
  if [[ "${campaign_head_charging}" != 1 ]]; then
    "$@"
    return
  fi
  # Its words go to stderr: the command's stdout is often its artifact
  # (ImportGateMain's summary JSON).
  campaign_head_heartbeat
  campaign_head_place "${need}" "${ramp}" >&2
  host=${campaign_placed_host}
  id=${campaign_host_charge_id}
  if campaign_host_is_local "${host}"; then
    if [[ -n "${campaign_head_reservation}" ]]; then
      busy="${campaign_head_reservation}.busy.${BASHPID}"
      : >"${busy}"
    fi
    "$@"
    status=$?
  else
    campaign_run_placed "${host}" "$@"
    status=$?
  fi
  [[ -z "${busy}" ]] || rm -f -- "${busy}"
  campaign_head_heartbeat
  campaign_host_release "${host}" "${id}"
  return "${status}"
}

# Room for a head step of <need_mb> for <ramp_s>, charged: on the head's own
# host when it fits there (its own room is not held against it), else on
# the host of the pool with the most room under the ceiling
# (campaign_host_room), as the pool would place one more start; waited for
# when no host has it, said once, and how long when it gets room, so a
# step's wall time names its wait (tools/analysis/timeline.py).  While it
# waits it holds its need on the host with the most room when it began to
# wait (campaign_head_hold_room): every other start counts the hold there,
# so that host drains as its starts return, within a replay's lifetime,
# instead of being taken again one obligation at a time (a40h2
# BlockRecoveryWorker-530's 14 GB seed replay waited 70 min, V5-11741's
# 16 GB GROW step 40 min and more, while the pool kept every lift busy).
# The host is campaign_placed_host.
campaign_placed_host=""
campaign_head_place() {
  local need=$1 ramp=$2 host room best best_room said=false status=0
  local since=${SECONDS}
  while true; do
    campaign_host_head_start=1 campaign_host_try_charge localhost "${need}" \
      "${ramp}"
    if (( status == 0 )); then
      campaign_placed_host=localhost
      campaign_head_placed "${said}" "${need}" "${since}"
      return 0
    fi
    best=""
    best_room=-1
    while IFS= read -r host; do
      ! campaign_host_is_local "${host}" || continue
      room=$(campaign_host_room "${host}") || continue
      (( room >= need && room > best_room )) || continue
      best=${host}
      best_room=${room}
    done < <(campaign_worker_host_list)
    if [[ -n "${best}" ]]; then
      campaign_host_try_charge "${best}" "${need}" "${ramp}"
      if (( status == 0 )); then
        campaign_placed_host=${best}
        campaign_head_placed "${said}" "${need}" "${since}"
        return 0
      fi
    fi
    if [[ "${said}" == false ]]; then
      campaign_head_hold_room "${need}"
      campaign_log "waiting for memory for a head step of ${need} MB on any \
host: ${campaign_host_wait_reason}; held on ${campaign_head_hold_host:-no host}"
      said=true
    fi
    campaign_head_heartbeat
    sleep "${campaign_host_poll_s}"
  done
}

# campaign_head_hold_room <need_mb>: the waiting step's hold
# (campaign_head_hold), its need among the reservations of the pool's host
# with the most room now, campaign_head_hold_host.
campaign_head_hold_host=""
campaign_head_hold_room() {
  local need=$1 host room best_room="" dir
  campaign_head_hold_host=""
  while IFS= read -r host; do
    room=$(campaign_host_room "${host}") || continue
    [[ -z "${best_room}" ]] || (( room > best_room )) || continue
    campaign_head_hold_host=${host}
    best_room=${room}
  done < <(campaign_worker_host_list)
  [[ -n "${campaign_head_hold_host}" ]] || return 0
  dir="${campaign_host_gate_root}/$(campaign_host_key \
    "${campaign_head_hold_host}")/heads"
  mkdir -p "${dir}"
  campaign_head_hold="${dir}/$(hostname -s).${BASHPID}.$(date +%s).hold"
  printf '%s\n' "${need}" >"${campaign_head_hold}"
}

# campaign_head_placed <said> <need_mb> <since>: a head step that waited for
# room gives its hold up and says how long, once it has room.
campaign_head_placed() {
  [[ "$1" == true ]] || return 0
  [[ -z "${campaign_head_hold}" ]] || rm -f -- "${campaign_head_hold}"
  campaign_head_hold=""
  campaign_log "room for a head step of $2 MB on ${campaign_placed_host} \
after waiting $(( SECONDS - $3 )) s"
}

# How long a head step placed on a peer may run there: the case's whole
# budget (experiments/accept/accept.sh), past which nothing of it is read.
campaign_placed_bound_s=21600

# <command...> of the head -- a program, or a run_engine.sh function whose
# arguments are all it reads of the head -- run on <host> in the head's
# working directory (run_engine.sh --run-placed, through the remote worker
# script, so it ends with the head) with the CAUSYNTH_ and GRAPH_CHECKER_
# variables the head exports; its standard output and error are passed on
# as its own, and its status is the command's.
campaign_run_placed() {
  local host=$1 dir name status=0
  local -a exported=()
  shift
  dir=$(mktemp -d "${campaign_root}/placed.XXXXXX") || return
  for name in $(compgen -e); do
    [[ "${name}" == CAUSYNTH_* || "${name}" == GRAPH_CHECKER_* ]] \
      && exported+=("${name}=${!name}")
  done
  campaign_dispatch_remote "${host}" "${dir}" "${campaign_placed_bound_s}" \
    --run-placed "${PWD}" "${exported[@]}" -- "$@" || status=$?
  cat -- "${dir}/stdout.log" 2>/dev/null
  cat -- "${dir}/stderr.log" "${dir}/ssh.log" >&2 2>/dev/null
  rm -rf -- "${dir}"
  return "${status}"
}

# campaign_await_host_memory <host> <need_mb> <ramp_s>: blocks until one
# start fits on the host, then charges it there: 0.  2 when the host's
# memory cannot be read for campaign_ssh_patience_s, the waiter's named
# failure.  What starts on the host that runs it waits here: a host's
# solver (campaign_start_solver) and a question asked again of a solver of
# its own (campaign_solve_obligation_alone).  A head's step goes to any host
# with room (campaign_head_place), and an obligation's start is the pool's
# (campaign_stream_admit_host): neither waits on one host while another
# has room.
campaign_await_host_memory() {
  local host=$1 need=$2 ramp=$3
  local said=false status=0 unread_since="" since=${SECONDS}
  while true; do
    campaign_host_try_charge "${host}" "${need}" "${ramp}"
    case "${status}" in
      0)
        [[ "${said}" == false ]] || campaign_log "room for ${need} MB on \
${host} after $(( SECONDS - since ))s"
        return 0 ;;
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
      *) unread_since="" ;;
    esac
    if [[ "${said}" == false ]]; then
      campaign_log "waiting for memory on ${host}: \
${campaign_host_wait_reason}"
      said=true
    fi
    campaign_head_heartbeat
    sleep "${campaign_host_poll_s}"
  done
}

# campaign_stream_job <kind> <host> <charge> <id> <worker> <args...>: one
# start of the pool, on the host that admitted it and charged it <charge>:
# an OBLIGATION's worker (campaign_obligation_worker <args...>) or a GROW
# RERUN's replay (campaign_obligation_replay <args...>).  A local one is a
# subshell under `set -euo pipefail`; a remote one runs through the remote
# worker script, an obligation as --run-obligation (the script and ssh's own
# output beside its logs), a re-run as a placed step (campaign_run_placed);
# its stdout and stderr are <worker>'s either way.  Its row is released as
# soon as its work returned, before the head waits to see what a peer wrote
# (campaign_await_remote_result): an answer in seconds does not hold its
# host's room for the ramp.  A job the head reaps (campaign_stream_reap)
# leaves its row to lapse with the ramp.
campaign_stream_job() {
  local kind=$1 host=$2 charge=$3 id=$4 worker=$5 status=0
  shift 5
  local -a work=(campaign_obligation_worker "$@")
  [[ "${kind}" == OBLIGATION ]] || work=(campaign_obligation_replay "$@")
  if campaign_host_is_local "${host}"; then
    ( set -euo pipefail; "${work[@]}" ) >"${worker}/stdout.log" \
      2>"${worker}/stderr.log" || status=$?
  elif [[ "${kind}" == OBLIGATION ]]; then
    campaign_dispatch_remote "${host}" "${worker}" \
      "$(campaign_remote_worker_bound_s)" --run-obligation "$@" \
      || status=$?
  else
    campaign_run_placed "${host}" "${work[@]}" >"${worker}/stdout.log" \
      2>"${worker}/stderr.log" || status=$?
  fi
  campaign_host_release "${host}" "${charge}"
  campaign_host_is_local "${host}" && return "${status}"
  if (( status != 0 )); then
    campaign_log "${kind} ${id} on ${host}: the remote worker exited \
${status}; its logs, and ssh's own output, are in ${worker}"
    return "${status}"
  fi
  campaign_await_remote_result "${worker}" "${host}" "${id}"
}

# An obligation whose worker did not finish (it exited <status>, or the head
# could not see what it wrote), answered as itself: one obligation's answer,
# never the campaign's death.  Nothing of it may still run -- a peer's
# replay JVM is in a process group of its own, which the remote wrapper's
# watchdog does not reach -- so every process whose command line names its
# worker directory is ended on its host first; then the session it staged
# is withdrawn under the worker, and one row answers it, naming why.
campaign_obligation_unfinished() {
  local host=$1 obligation_id=$2 worker=$3 status=$4
  local why failure iteration_dir
  # What the worker said last: an engine failure (die, campaign_fail) names
  # itself on its stderr.
  failure=$(sed -n -E 's/^(Error: |  reason=)//p' "${worker}/stderr.log" \
    2>/dev/null | tail -n 1) || failure=""
  why="its worker on ${host} did not finish (exit ${status}: \
${failure:-it failed, or the head could not see what it wrote, as the \
campaign log says}); its logs are in ${worker}"
  campaign_log "obligation ${obligation_id}: ${why}"
  campaign_reap_on_host "${host}" "${worker}"
  campaign_withdraw_sessions "${obligation_id}" "${worker}/sessions" \
    "${worker}/unfinished-sessions" "${why}"
  # Its answer settles no question.
  rm -f -- "${worker}/question.txt" "${worker}/question.asked"
  jq -n -c --arg id "${obligation_id}" --arg detail "${why}" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: "NOT_ADMITTED", sessionId: "", detail: $detail}' \
    >"${worker}/obligation_result.jsonl"
  # Loud: the campaign's own gap row, which EMIT carries, counted in the
  # iteration manifest (unfinishedObligations).  The slots run on the head,
  # so the appends are one host's.
  iteration_dir=$(dirname "$(dirname "${worker}")")
  jq -n -c --arg id "${obligation_id}" --arg detail "${why}" \
    --arg epoch "$(basename "${iteration_dir}")" \
    '{schemaVersion: 1, sessionId: "", stage: "EXPLORE",
      kind: "ADMISSION_GAP", cls: "DIAGNOSTIC",
      subject: "OBLIGATION_UNFINISHED", detail: ($id + ": " + $detail),
      topologyEpoch: $epoch}' >>"${iteration_dir}/campaign_gaps.jsonl"
}


# ---------------------------------------------------------------------------
# EXPLORE: ONE STREAMING LOOP (PIPELINE §7.7, §7.9)
#
# No wave barrier.  The head starts queued obligations wherever the memory
# ledger admits one and collects each as it returns.  Its own JVM work -- the
# import gate over the sessions that landed with the round now owed, or a
# COMPOSE attempt at the witnesses among them -- is one STEP at a time, in
# the background (campaign_stream_step), so the pool goes on starting and
# collecting while a step waits for memory or runs.  The corpus and the ledger change only
# between two steps, in the head's hands (campaign_stream_step_start): a
# step reads them as a landed whole, and whatever returns meanwhile waits
# for the next one -- the busier the head, the more one step takes in.
#
# The loop's state is campaign_explore's locals, which the helpers below read
# and write through bash's dynamic scope:
#
#   stream_queue      "<kind> <round> <id> [<session>]" not started yet:
#                     OBLIGATION, or RERUN (GROW re-running the replay that
#                     exposed a region, its exposing session named)
#   stream_jobs       pid -> "<kind> <round> <id> <host> [<session>]"
#   stream_pending    "<kind> <round> <id> <host> <status> [<session>]": what
#                     returned since the last step began, not landed yet
#   stream_flying     obligation id -> its row, queued, running or not
#                     landed yet: a round's --in-flight
#   stream_host_jobs  host -> how many of this campaign's run there
#   stream_step_pid   the step running, or ""; stream_step_dir its directory
#                     (steps/NNNN/: what it gates and plans, or attempts)
#   stream_witnesses  sessions landed as witnesses, gated, not attempted yet
#   stream_swaps      re-runs that returned, whose sessions replace the
#                     exposing ones once no obligation runs
#   stream_landed     sessions landed since the last round
#   stream_hold       GROW's re-runs and swaps still owed: no obligation
#                     starts and no round is planned while any is
# ---------------------------------------------------------------------------

# EXPLORE.  Rounds of explore.ExploreMain over the corpus, each obligation
# solved and replayed on whichever host has room, until one of these ends:
#
#   WITNESSED   an admitted replay that observed the fatal at the declared
#               occurrence lands, COMPOSE over the corpus as it stands
#               publishes the claim the final stages accept, and CONFIRM
#               confirms it (campaign_stream_attempt): the queue is
#               cancelled and what runs is reaped (campaign_stream_end).
#   FIXED_POINT nothing proposed, exposed, queued, running or unlanded.
#   REGION_PATH_WAVE_BUDGET_REACHED  a round of wave region_path_max_waves
#               still owes work: it is not dispatched, the queue is
#               cancelled, and what runs lands.
#   CAMPAIGN_BUDGET_REACHED  between two steps, the campaign's budget has
#               no room for the stages after it (campaign_claim_room): as
#               at a witness, the queue is cancelled and what runs reaped.
#   PLANNER_HEAP_EXCEEDED  a round's planner outgrew the head's heap.
#
# Each end is stated in exploration.json, and a forced one as a DIAGNOSTIC
# row of campaign_gaps.jsonl; none fails the campaign, which goes on to
# COMPOSE over the corpus EXPLORE left.
campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local sessions="${iteration_dir}/sessions"
  local results="${iteration_dir}/obligation_results.jsonl"
  local attempts="${iteration_dir}/witness_attempts.jsonl"
  local stream_classes="${iteration_dir}/instrumented-classes"
  local stream_plan="${iteration_dir}/generations/g0/execution_task_plan.jsonl"
  local stream_round=0 stream_dirty=1 stream_landed=0 stream_hold=0
  local stream_generation=0 stream_next_host=0 stream_ticker=""
  local stream_waiting="" stream_admitted_host="" stream_stop=""
  local stream_share_said=""
  local stream_stop_detail="" stream_anchors="[]"
  local stream_step_pid="" stream_step_dir="" stream_steps=0
  local -a stream_queue=() stream_hosts=() stream_swaps=() stream_pending=()
  local -a stream_witnesses=()
  local -a stream_cancelled=() stream_reaped=() stream_round_args=()
  local -A stream_jobs=() stream_flying=()
  local -A stream_host_jobs=() stream_host_cores=() stream_host_unread=()
  local -A stream_solver_seen=()
  : >"${results}"
  : >"${attempts}"
  mkdir -p "$(dirname "${stream_plan}")"
  ln -f "${iteration_dir}/execution_task_plan.jsonl" "${stream_plan}"
  mapfile -t stream_hosts < <(campaign_worker_host_list)
  campaign_stream_round_args
  campaign_stream_enroll
  # A head that fails takes nothing it started with it: whatever still runs
  # is ended first, here and on every peer; then its share and its room go,
  # as they do when the head exits anywhere else (campaign_head_reserve).
  trap 'campaign_stream_reap; campaign_stream_unenroll
    campaign_head_unreserve' EXIT

  while true; do
    # Between two steps, so the round the last one planned is whole.
    if [[ -z "${stream_stop}" && -z "${stream_step_pid}" ]] \
        && ! campaign_claim_room; then
      stream_stop=CAMPAIGN_BUDGET_REACHED
      stream_stop_detail="$(( SECONDS - campaign_started_s ))s of the \
campaign's ${campaign_budget_s}s budget (campaign_budget_s) are spent, and \
the stages after the exploration are owed $(campaign_reserve)s of it \
(campaign_reserve)"
    fi
    if [[ "${stream_stop}" == WITNESSED \
        || "${stream_stop}" == CAMPAIGN_BUDGET_REACHED ]]; then
      campaign_stream_end
      break
    fi
    [[ -n "${stream_step_pid}" ]] || campaign_stream_step_start
    [[ -z "${stream_stop}" ]] || campaign_stream_drop cancelled
    campaign_stream_dispatch
    # With no step running, everything that returned has landed, and a
    # round owed is planning (campaign_stream_step_start): nothing left to
    # start or run is the end -- the stop already stated, else the fixed
    # point.
    if (( ${#stream_jobs[@]} + ${#stream_queue[@]} == 0 )) \
        && [[ -z "${stream_step_pid}" ]]; then
      if [[ -z "${stream_stop}" ]]; then
        stream_stop=FIXED_POINT
        stream_stop_detail="round $((stream_round - 1)) proposed nothing, \
exposed nothing, and nothing is queued, running or unlanded"
        campaign_log "exploration reached its fixed point: \
${stream_stop_detail}"
      fi
      break
    fi
    campaign_stream_wait
  done
  if [[ -n "${stream_ticker}" ]]; then
    kill "${stream_ticker}" 2>/dev/null || true
    wait "${stream_ticker}" 2>/dev/null || true
  fi
  campaign_stream_unenroll
  trap campaign_head_unreserve EXIT
  campaign_stream_promote_generation
  campaign_stream_truncation
  campaign_stream_manifest
  campaign_log "exploration stopped (${stream_stop}) after ${stream_round} \
round(s), $(grep -c '' "${results}" || true) obligation verdict(s); ran on: \
$(cat "${iteration_dir}"/obligations-*/*/host.txt 2>/dev/null \
  | LC_ALL=C sort | uniq -c | awk '{printf "%s=%s ", $2, $1}')"
}

# The planner's arguments that stay the same every round.
campaign_stream_round_args() {
  local declared
  declared=$(campaign_declared_target_occurrence)
  stream_round_args=(--static-scope-map "${causynth_static_scope_map}"
    --topology-epoch "${iteration_id}")
  [[ -z "${declared}" ]] \
    || stream_round_args+=(--target-occurrence "${declared}")
  [[ -z "${region_path_max_paths_per_region}" ]] || stream_round_args+=(
    --max-paths-per-region "${region_path_max_paths_per_region}")
  [[ -z "${region_path_max_flips_per_path}" ]] || stream_round_args+=(
    --max-flips-per-path "${region_path_max_flips_per_path}")
  [[ -z "${region_path_max_tasks}" ]] \
    || stream_round_args+=(--max-tasks "${region_path_max_tasks}")
  [[ -z "${region_path_max_world_depth}" ]] || stream_round_args+=(
    --max-world-depth "${region_path_max_world_depth}")
  # The same declaration COMPOSE reads.  An obligation's handoff answers are
  # constrained by their interaction's family, and a family arm is only as
  # constraining as the roots inside it: without the case's declared domain
  # every arm pins its answer to what the recording delivered, and no
  # rotation the case assumes could ever be explored.
  [[ -z "${causynth_root_domains}" ]] \
    || stream_round_args+=(--root-domains "${causynth_root_domains}")
}

# Whether a round is owed now: something answered since the last one, and
# either a session landed (the corpus grew) or nothing is left to wait for
# (the last answers may close the frontier).  Never while GROW's re-runs or
# swaps are owed: the corpus is about to change under the round.
campaign_stream_plan_due() {
  (( stream_dirty == 1 && stream_hold == 0 )) || return 1
  (( stream_landed > 0 )) && return 0
  (( ${#stream_jobs[@]} == 0 && ${#stream_queue[@]} == 0 ))
}

# Between two steps, in the head's hands, the next one, in steps/NNNN/.
# Witnesses gated and not yet attempted make it an ATTEMPT (`witnesses`,
# all of them): nothing lands while it runs, so it composes the corpus as
# it stood, and whatever returns meanwhile, a witness too, waits for the
# step after it -- at most one attempt at a time, the witnesses that come
# during one coalesced into the next.  Else what returned lands
# (campaign_stream_land), GROW's re-runs swap in once due, the staged
# sessions move into the corpus (campaign_stream_move), and the step takes
# them in when there is work: `gate`, the sessions that landed; `round`, the
# round now owed, with its in_flight.jsonl, taken here, where nothing is
# unlanded.
campaign_stream_step_start() {
  local dir name="" row
  local -a stream_staged=() gate=()
  if (( ${#stream_witnesses[@]} > 0 )) && [[ -z "${stream_stop}" ]]; then
    campaign_stream_step_dir
    printf '%s\n' "${stream_witnesses[@]}" >"${dir}/witnesses"
    stream_witnesses=()
  else
    (( ${#stream_pending[@]} == 0 )) || campaign_stream_land
    if campaign_stream_swap_due; then
      campaign_stream_swap
    fi
    (( ${#stream_staged[@]} == 0 )) || campaign_stream_move
    if [[ -z "${stream_stop}" ]] && campaign_stream_plan_due; then
      name=$(printf 'obligations-%04d' "${stream_round}")
    fi
    (( ${#gate[@]} > 0 )) || [[ -n "${name}" ]] || return 0
    campaign_stream_step_dir
    (( ${#gate[@]} == 0 )) || printf '%s\n' "${gate[@]}" >"${dir}/gate"
    if [[ -n "${name}" ]]; then
      for row in "${stream_flying[@]}"; do
        printf '%s\n' "${row}"
      done >"${dir}/in_flight.jsonl"
      printf '%s\n' "${name}" >"${dir}/round"
      stream_round=$((stream_round + 1))
      stream_dirty=0
      stream_landed=0
    fi
  fi
  campaign_stream_step "${dir}" &
  stream_step_pid=$!
  stream_step_dir=${dir}
}

# The next step's directory, made: the caller's `dir`.
campaign_stream_step_dir() {
  dir=$(printf '%s/steps/%04d' "${iteration_dir}" "${stream_steps}")
  stream_steps=$((stream_steps + 1))
  mkdir -p "${dir}"
}

# One step of the head's JVM work, in the background: an attempt at the
# witnesses <dir>/witnesses names, whose acceptance (<dir>/witnessed) ends
# the exploration; or the import gate over the sessions <dir>/gate names
# (one call: the head's) and the round <dir>/round names, planned into
# obligations-NNNN/.  A BLOCKING row fails the campaign at IMPORT here, and
# a planner that fails fails it at EXPLORE -- but one that ran out of the
# most heap a head JVM is given plans no round: the corpus outgrew what the
# head can hold, its round directory goes (its logs into the step) and
# <dir>/heap-exceeded ends the exploration on the rounds before it.  The
# head takes the rest once the step returns (campaign_stream_step_done), the
# engine mains that outgrew their need in it among them (<dir>/outgrown,
# engine_java).
campaign_stream_step() {
  local dir=$1 round_dir status=0
  local -a gate=() witnesses=()
  if [[ -s "${dir}/witnesses" ]]; then
    mapfile -t witnesses <"${dir}/witnesses"
    campaign_stream_attempt "${dir}" "${witnesses[@]}"
  else
    [[ ! -s "${dir}/gate" ]] || mapfile -t gate <"${dir}/gate"
    (( ${#gate[@]} == 0 )) || campaign_import_gate "${iteration_dir}" \
      "${iteration_id}" "${dir}/import_gate.json" "${gate[@]/#/${sessions}/}"
    if [[ -s "${dir}/round" ]]; then
      round_dir="${iteration_dir}/$(cat "${dir}/round")"
      [[ ! -e "${round_dir}" ]] || die \
        "obligation round directory already exists: ${round_dir}"
      mkdir -p "${round_dir}"
      # Copied as the planner starts: the round's time is the planner's own.
      cp -- "${dir}/in_flight.jsonl" "${round_dir}/in_flight.jsonl"
      run_java_main edu.uva.liftlab.graphchecker.explore.ExploreMain \
        --sessions "${sessions}" --results "${results}" \
        --in-flight "${round_dir}/in_flight.jsonl" \
        --round "$((10#${round_dir##*-}))" --output-dir "${round_dir}" \
        "${stream_round_args[@]}" \
        >"${round_dir}/stdout.log" 2>"${round_dir}/stderr.log" || status=$?
      if (( status == campaign_jvm_out_of_heap_status )); then
        mv -- "${round_dir}/stdout.log" "${round_dir}/stderr.log" "${dir}/"
        rm -r -- "${round_dir}"
        printf '%s\n' "the planner of $(basename "${round_dir}") ran out \
of the most heap a head JVM is given (engine_memory_mb=${engine_memory_mb:-8192}) \
over a corpus of $(du -s -m -- "${sessions}" | cut -f1) MB ($(campaign_thrown \
"${dir}/stderr.log"), ${dir}/stderr.log)" >"${dir}/heap-exceeded"
      elif (( status != 0 )); then
        campaign_fail EXPLORE ExploreMain "${round_dir}/stderr.log" \
          "the planner of $(basename "${round_dir}") failed with exit \
${status}: $(campaign_thrown "${round_dir}/stderr.log")"
      fi
    fi
  fi
  printf '%s\n' "${campaign_engine_outgrown}" >"${dir}/outgrown"
}

# The step returned: one that failed has said why on the campaign's stderr
# and ends the head; an accepted attempt ends the exploration; else its
# round, if it planned one, is taken (campaign_stream_take_round).
campaign_stream_step_done() {
  local status=$1 dir=${stream_step_dir}
  stream_step_pid=""
  stream_step_dir=""
  (( status == 0 )) || exit "${status}"
  campaign_engine_outgrown=$(cat "${dir}/outgrown")
  if [[ -s "${dir}/witnessed" ]]; then
    stream_stop=WITNESSED
    stream_stop_detail=$(cat "${dir}/witnessed")
    campaign_witness_attempt=$(cat "${dir}/attempt")
  elif [[ -s "${dir}/heap-exceeded" ]]; then
    # The round was never planned: the last one is the round before it.
    stream_round=$((stream_round - 1))
    stream_stop=PLANNER_HEAP_EXCEEDED
    stream_stop_detail=$(cat "${dir}/heap-exceeded")
  elif [[ -s "${dir}/round" ]]; then
    campaign_stream_take_round "${iteration_dir}/$(cat "${dir}/round")"
  fi
}

# A planned round, taken -- in this order -- through the wave budget, and
# GROW for its exposures, else its obligations into the queue.
campaign_stream_take_round() {
  local round_dir=$1 name exposures exposed proposed wave index
  local -a ids=() rows=()
  name=$(basename "${round_dir}")
  # The planner states both files every round; an empty obligations file is
  # nothing new to ask, and a growth file with no EXPOSED_REGION row a closed
  # region set.
  require_file "round growth rows" "${round_dir}/growth.jsonl"
  require_file "round obligations" "${round_dir}/obligations.jsonl"
  exposures=$(campaign_exposures "${round_dir}/growth.jsonl")
  exposed=$(printf '%s' "${exposures}" | grep -c '' || true)
  mapfile -t rows < "${round_dir}/obligations.jsonl"
  mapfile -t ids < <(jq -r '.obligationId' "${round_dir}/obligations.jsonl")
  proposed=${#ids[@]}
  wave=$(jq -er '.wave' "${round_dir}/explore_manifest.json") \
    || campaign_fail EXPLORE ExploreMain "${round_dir}" \
      "${name} states no wave"
  # The declared occurrence, as a target row spells it: what makes a landed
  # session a witness (campaign_stream_move).
  stream_anchors=$(jq -c '.anchorOccurrences' \
    "${round_dir}/explore_manifest.json")
  campaign_log "round $((10#${name##*-})) (wave ${wave}): ${proposed} \
obligation(s), ${exposed} exposure(s), $(grep -c '' \
"${round_dir}/in_flight.jsonl" || true) in flight, $(jq -r \
'.branchesStopped' "${round_dir}/explore_manifest.json") branch(es) stopped"
  if (( proposed + exposed > 0 && wave >= region_path_max_waves )); then
    stream_stop=REGION_PATH_WAVE_BUDGET_REACHED
    stream_stop_detail="${name} is of wave ${wave}, and the exploration \
reached its configured budget of region_path_max_waves=${region_path_max_waves} \
with ${proposed} obligation(s) still open and ${exposed} region exposure(s) \
not yet woven"
    campaign_stream_gap DIAGNOSTIC "${stream_stop}" "${stream_stop_detail}"
    stream_cancelled+=("${ids[@]}")
    return 0
  fi
  # A round that exposes regions grows the corpus first: what it proposes is
  # asked again over the grown one, once GROW's re-runs have swapped in.
  if (( exposed > 0 )); then
    campaign_stream_grow "${round_dir}"
    return 0
  fi
  for ((index = 0; index < proposed; index++)); do
    mkdir -p "${round_dir}/${ids[${index}]}"
    stream_flying[${ids[${index}]}]=${rows[${index}]}
    stream_queue+=("OBLIGATION ${name} ${ids[${index}]}")
  done
}

# One row of the exploration's own, <class> <subject> <detail>, as EMIT
# publishes it, and a log line: a forced end is DIAGNOSTIC coverage
# telemetry, never a campaign failure; a closure it ended on truncated is
# BLOCKING for a claim over it (campaign_stream_truncation).
campaign_stream_gap() {
  local cls=$1 kind=$2 detail=$3
  jq -n -c --arg cls "${cls}" --arg kind "${kind}" --arg detail "${detail}" \
    --arg epoch "${iteration_id}" \
    '{schemaVersion: 1, sessionId: "", stage: "EXPLORE",
      kind: "ADMISSION_GAP", cls: $cls,
      subject: $kind, detail: $detail, topologyEpoch: $epoch}' \
    >>"${iteration_dir}/campaign_gaps.jsonl"
  campaign_log "exploration: ${kind}: ${detail}"
}

# The closure the exploration ended on, judged.  An accepted witness ended
# it: nothing past that point is asked, so a truncation asks nothing more
# (each round's own row is DIAGNOSTIC, ExploreMain).  A planner that could
# not hold the corpus ended it with rounds still owed: BLOCKING.  Any other
# end: when its last round's closure was truncated at the task bound
# (--max-tasks, the manifest's `truncated`), a claim over it misses arms,
# BLOCKING.  The same
# holds for the occurrences PLAN left out to fit schedule_max_jobs (the
# index's `closureCut`, RuntimeWorkflowDiscovery.Workflow#nearest), stated
# whatever the end: DIAGNOSTIC under a witness, BLOCKING otherwise.
campaign_stream_truncation() {
  local last truncated cut cls=BLOCKING
  cut=$(jq -r '.closureCut // empty | "\(.occurrences) \(.keptDepth)"' \
    "${iteration_dir}/runtime_workflow_schedule_index.json")
  if [[ -n "${cut}" ]]; then
    [[ "${stream_stop}" != WITNESSED ]] || cls=DIAGNOSTIC
    campaign_stream_gap "${cls}" PLAN_CLOSURE_CUT "PLAN planned the \
closure only to demand depth ${cut#* } to fit schedule_max_jobs: ${cut%% *} \
deeper occurrence(s) were not planned, so a claim over it misses their arms \
(the exploration ended ${stream_stop})"
  fi
  [[ "${stream_stop}" != PLANNER_HEAP_EXCEEDED ]] \
    || campaign_stream_gap BLOCKING "${stream_stop}" "${stream_stop_detail}: \
the exploration ended on the rounds before it, so a claim over its corpus \
misses the arms the rounds still owed would ask"
  [[ "${stream_stop}" != WITNESSED ]] && (( stream_round > 0 )) || return 0
  last=$(printf '%s/obligations-%04d' "${iteration_dir}" \
    "$((stream_round - 1))")
  truncated=$(jq -r '.truncated' "${last}/explore_manifest.json")
  campaign_count EXPLORE ExploreMain "${last}/explore_manifest.json" \
    "the closure's occurrences not planned" "${truncated}"
  (( truncated > 0 )) || return 0
  campaign_stream_gap BLOCKING REGION_PATH_CLOSURE_TRUNCATED "the \
exploration ended (${stream_stop}) on $(basename "${last}")'s closure, \
truncated at its task bound: ${truncated} occurrence(s) were not planned \
(its gaps.jsonl names them), so a claim over it misses their arms"
}

# One COMPOSE over the corpus as it stands -- the stage's own entry,
# do_compose, into a scratch directory -- at the witnesses of step <dir>.  An observed fatal is not yet a composable witness: the families
# COMPOSE joins may need sessions later obligations would add.  Only an
# attempt that publishes the claim the final stages accept, SAT_CANDIDATE
# with its polarity deciding, and that CONFIRM confirms (campaign_confirm_claim,
# its replay in <campaign root>/witness-confirm/, out of the iteration) writes
# <dir>/witnessed, which ends the exploration; a refuted one is excluded from
# every composition after it (campaign_refute) and the exploration goes on.
# With no room left in the budget for a confirmation (campaign_claim_room),
# the claim is accepted as it stands and the final CONFIRM decides.
campaign_stream_attempt() {
  local step=$1 dir status=0 claim="" kind="" polarity=false
  local accepted=false confirmed=null reason="" started compose_ms=0
  local confirm_ms=0
  shift
  dir=$(printf '%s/witness-attempts/%04d' "${iteration_dir}" \
    "$(grep -c '' "${attempts}" || true)")
  mkdir -p "${dir}"
  started=$(date +%s%N)
  ( compose_sessions_dir="${sessions}"
    composed_smt="${dir}/candidate.smt2"
    composition_manifest="${dir}/candidate_composition_manifest.json"
    do_compose ) >"${dir}/compose.log" 2>&1 || status=$?
  compose_ms=$(( ($(date +%s%N) - started) / 1000000 ))
  if [[ "${status}" -eq 0 ]]; then
    claim=$(jq -r '.solver.campaignClaim.claim // ""' \
      "${dir}/candidate_composition_manifest.json" 2>/dev/null) || claim=""
    kind=$(jq -r '.solver.campaignClaim.findingKind // ""' \
      "${dir}/candidate_composition_manifest.json" 2>/dev/null) || kind=""
    polarity=$(jq -r '.solver.campaignClaim.polarityDecides == true' \
      "${dir}/candidate_composition_manifest.json" 2>/dev/null) \
      || polarity=false
  fi
  [[ "${claim}" == SAT_CANDIDATE && "${polarity}" == true ]] \
    && accepted=true
  if [[ "${accepted}" == true ]] && campaign_claim_room; then
    started=$(date +%s%N)
    campaign_confirm_claim "${iteration_dir}" "${dir}" \
      "${campaign_root}/witness-confirm/$(basename "${dir}")" \
      >>"${dir}/compose.log" 2>&1
    confirm_ms=$(( ($(date +%s%N) - started) / 1000000 ))
    confirmed=$(jq -r '.confirmed' "${dir}/confirm.json")
    reason=$(jq -r '.reason' "${dir}/confirm.json")
    [[ "${confirmed}" == true ]] || accepted=false
  fi
  jq -n -c --arg step "$(basename "${step}")" --arg dir "${dir}" \
    --argjson witnesses "$(printf '%s\n' "$@" | jq -R . | jq -s -c .)" \
    --arg claim "${claim}" --arg kind "${kind}" \
    --argjson polarity "${polarity}" --argjson accepted "${accepted}" \
    --argjson exit "${status}" --argjson confirmed "${confirmed}" \
    --arg reason "${reason}" --argjson composeMillis "${compose_ms}" \
    --argjson confirmMillis "${confirm_ms}" \
    '{step: $step, witnesses: $witnesses, dir: $dir, composeExit: $exit,
      claim: $claim, findingKind: $kind, polarityDecides: $polarity,
      confirmed: $confirmed, confirmReason: $reason,
      composeMillis: $composeMillis, confirmMillis: $confirmMillis,
      accepted: $accepted}' >>"${attempts}"
  campaign_log "witness $*: COMPOSE over the corpus as it stands \
(exit ${status}) claims ${claim:-nothing} ${kind} polarityDecides=${polarity} \
confirmed=${confirmed}: $([[ "${accepted}" == true ]] \
  && echo "the exploration ends" || echo "the exploration goes on")"
  [[ "${accepted}" == true ]] || return 0
  printf '%s\n' "${dir}" >"${step}/attempt"
  printf '%s\n' "an admitted replay ($*) observed the fatal at the declared \
occurrence and COMPOSE over the corpus as it stood published ${claim} \
${kind} with its polarity deciding (${dir}), confirmed=${confirmed}" \
    >"${step}/witnessed"
}

# The queued obligations, out of the queue: their worker directories (made
# at enqueue, holding nothing yet) gone, none of them in flight any more;
# GROW's queued re-runs stay.  `cancelled` names each in exploration.json
# (the exploration ends); `again` leaves them to the next round, which asks
# again what is still owed (a swap changed the corpus they were cut from).
campaign_stream_drop() {
  local why=$1 entry kind round id
  local -a kept=()
  for entry in "${stream_queue[@]}"; do
    read -r kind round id _ <<<"${entry}"
    if [[ "${kind}" != OBLIGATION ]]; then
      kept+=("${entry}")
      continue
    fi
    [[ "${why}" != cancelled ]] || stream_cancelled+=("${id}")
    unset 'stream_flying[$id]'
    rmdir -- "${iteration_dir}/${round}/${id}"
  done
  stream_queue=("${kept[@]}")
}

# WITNESSED, or CAMPAIGN_BUDGET_REACHED: the queue cancelled, and everything
# this campaign still runs ended -- its process trees here, its workers on
# every peer -- and moved out of the iteration with what it staged, as is
# what returned after the last step began, never landed: the corpus COMPOSE
# reads next is exactly the one the last step read.
campaign_stream_end() {
  local pid entry kind round id host status session dir
  local -a dropped=()
  for pid in "${!stream_jobs[@]}"; do
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    dropped+=("${kind} ${round} ${id}")
  done
  for entry in "${stream_pending[@]}"; do
    read -r kind round id host status session <<<"${entry}"
    dropped+=("${kind} ${round} ${id}")
  done
  campaign_stream_gap DIAGNOSTIC "${stream_stop}" "${stream_stop_detail}; \
${#stream_queue[@]} queued obligation(s) cancelled and ${#dropped[@]} \
unlanded one(s) reaped (exploration.json)"
  campaign_stream_drop cancelled
  stream_queue=()
  campaign_stream_reap
  for entry in "${dropped[@]}"; do
    read -r kind round id <<<"${entry}"
    stream_reaped+=("${id}")
    dir="${iteration_dir}/${round}/${id}"
    [[ "${kind}" == OBLIGATION ]] \
      || dir=$(campaign_stream_rerun_dir "${round}" "${id}")
    mkdir -p "${campaign_root}/explore-reaped/${round}"
    mv -- "${dir}" "${campaign_root}/explore-reaped/${round}/${id}"
  done
  stream_jobs=()
  stream_pending=()
}

# Everything this campaign still runs, ended: each job's process tree here,
# the step's and the ticker's (TERM, the kill grace, KILL), its workers on
# every peer, and each waited for.  The EXIT trap of a head that fails
# mid-exploration, and the witness's end.
campaign_stream_reap() {
  local pid
  local -a tree=()
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} ${stream_ticker}; do
    mapfile -t -O "${#tree[@]}" tree < <(campaign_process_tree "${pid}")
  done
  (( ${#tree[@]} > 0 )) || return 0
  kill -TERM "${tree[@]}" 2>/dev/null || true
  sleep "${campaign_adapter_kill_grace_s}"
  kill -KILL "${tree[@]}" 2>/dev/null || true
  campaign_reap_remote_workers
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} ${stream_ticker}; do
    wait "${pid}" 2>/dev/null || true
  done
  stream_step_pid=""
  stream_ticker=""
}

# <pid> and every process below it, deepest first.
campaign_process_tree() {
  local child
  for child in $(pgrep -P "$1" 2>/dev/null); do
    campaign_process_tree "${child}"
  done
  printf '%s\n' "$1"
}

# Starts what the queue holds, first first, while this exploration runs
# fewer than its share of stream_max_in_flight (campaign_stream_has_slot)
# and a host admits it: an obligation or a GROW re-run on the next host of
# the pool, round-robin, whose memory ledger admits one more start and that
# runs fewer of this campaign's than it has cores
# (campaign_stream_admit_host).  While GROW owes re-runs or swaps, only
# re-runs start.
campaign_stream_dispatch() {
  local entry
  while (( ${#stream_queue[@]} > 0 )); do
    entry=${stream_queue[0]}
    [[ "${entry}" == RERUN\ * ]] || (( stream_hold == 0 )) || return 0
    campaign_stream_has_slot || return 0
    campaign_stream_admit_host "${entry%% *}" || return 0
    stream_queue=("${stream_queue[@]:1}")
    campaign_stream_start "${entry}" "${stream_admitted_host}"
  done
}

# Whether this exploration runs fewer starts than its share of
# stream_max_in_flight: the cap over the capped explorations whose ledger
# entry is fresh (this one's among them, campaign_stream_enroll), at least
# one, read again at every start -- so the share grows as others end and
# shrinks as others begin, and what already runs past it runs out.  Always,
# with no cap.  1 when it runs its share, said once for every share it waits
# at.
campaign_stream_has_slot() {
  local fresh sharers share
  (( stream_max_in_flight > 0 )) || return 0
  fresh=$(( $(date +%s) - campaign_head_reservation_stale_s ))
  sharers=$(find "${campaign_host_gate_root}/explorations" -maxdepth 1 \
    -type f -newermt "@${fresh}" | grep -c '') || sharers=0
  (( sharers > 0 )) || sharers=1
  share=$(( stream_max_in_flight / sharers ))
  (( share > 0 )) || share=1
  (( ${#stream_jobs[@]} >= share )) || return 0
  if [[ "${stream_share_said}" != "${share}" ]]; then
    campaign_log "waiting for a slot: ${#stream_jobs[@]} start(s) run, this \
exploration's share ${share} of stream_max_in_flight=${stream_max_in_flight}, \
shared by ${sharers} capped exploration(s)"
    stream_share_said=${share}
  fi
  return 1
}

# A capped exploration's ledger entry, fresh while its head lives
# (campaign_head_heartbeat) and gone when it ends (campaign_explore): what
# the capped explorations running now count to share stream_max_in_flight
# (campaign_stream_has_slot).  None with no cap.
campaign_stream_enroll() {
  local dir="${campaign_host_gate_root}/explorations"
  (( stream_max_in_flight > 0 )) || return 0
  mkdir -p "${dir}"
  campaign_stream_entry="${dir}/$(hostname -s).${BASHPID}.$(date +%s)"
  : >"${campaign_stream_entry}"
}

campaign_stream_unenroll() {
  [[ -z "${campaign_stream_entry}" ]] || rm -f -- "${campaign_stream_entry}"
  campaign_stream_entry=""
}

# Picks the host for one start of <kind> (OBLIGATION or RERUN) and charges it
# there (stream_admitted_host): the pool from the host after the last one
# chosen, each start charged its replay's need, obligation_memory_mb, for an
# obligation's ramp; an OBLIGATION goes first to a host where this
# campaign's solver still serves (campaign_stream_warm: one started there
# within the solver's idle time), whose question is then answered without a
# solver of its own to start and its corpus to read.  A host is skipped
# while it runs as many of this campaign's as it has cores, or while the
# ledger has no room on it (campaign_host_try_start: no start leaves a host
# more than CAUSYNTH_HOST_MAX_USED_PCT full, and none takes a head's room).
# 1 when no host has room now, said once per wait.
campaign_stream_admit_host() {
  local kind=$1 host turn count pass is status=0
  count=${#stream_hosts[@]}
  for pass in warm cold; do
    [[ "${pass}" == cold || "${kind}" == OBLIGATION ]] || continue
    for ((turn = 0; turn < count; turn++)); do
      host=${stream_hosts[$(( (stream_next_host + turn) % count ))]}
      # An obligation tries each host once, in the pass of its warmth.
      is=cold
      [[ "${kind}" != OBLIGATION ]] || ! campaign_stream_warm "${host}" \
        || is=warm
      [[ "${is}" == "${pass}" ]] || continue
      campaign_stream_try_host "${host}" "${turn}" && return 0
    done
  done
  if [[ -z "${stream_waiting}" ]]; then
    campaign_log "waiting for room: no host admits one more start \
(${campaign_host_wait_reason})"
    stream_waiting=1
  fi
  return 1
}

# Whether this campaign started an obligation on <host> within its solver's
# idle time (campaign_solver_idle_s), so the host's solver of its corpus
# likely still serves.
campaign_stream_warm() {
  local seen=${stream_solver_seen[$1]:-}
  [[ -n "${seen}" ]] && (( $(date +%s) - seen < campaign_solver_idle_s ))
}

# One host's admission for campaign_stream_admit_host, <turn> places after
# the host after the last one chosen: 0 with it charged and chosen.
campaign_stream_try_host() {
  local host=$1 turn=$2 count=${#stream_hosts[@]} status=0
  campaign_stream_has_cores "${host}" || return 1
  campaign_host_try_charge "${host}" "${obligation_memory_mb}" \
    "${campaign_host_ramp_s}"
  case "${status}" in
    0)
      stream_admitted_host=${host}
      unset 'stream_host_unread[$host]'
      stream_next_host=$(( (stream_next_host + turn + 1) % count ))
      stream_waiting=""
      return 0 ;;
    2) campaign_stream_unreadable "${host}" ;;
    *) unset 'stream_host_unread[$host]' ;;
  esac
  return 1
}

# Whether <host> runs fewer of this campaign's starts than it has cores; its
# core count is read once.  An unreadable count is an unreadable host.
campaign_stream_has_cores() {
  local host=$1 cores
  if [[ -z "${stream_host_cores[${host}]+x}" ]]; then
    if ! cores=$(campaign_host_cores "${host}"); then
      campaign_stream_unreadable "${host}"
      return 1
    fi
    stream_host_cores[${host}]=${cores}
  fi
  (( ${stream_host_jobs[${host}]:-0} < ${stream_host_cores[${host}]} ))
}

# A host whose memory or cores could not be read: waited out within the ssh
# patience (sshd refuses connections under a round's burst of them), then
# the campaign's named failure, after everything it runs is ended.
campaign_stream_unreadable() {
  local host=$1
  [[ -n "${stream_host_unread[${host}]+x}" ]] \
    || stream_host_unread[${host}]=${SECONDS}
  (( SECONDS - stream_host_unread[${host}] < campaign_ssh_patience_s )) \
    && return 0
  campaign_fail EXPLORE CAMPAIGN "${host}" "the memory of host ${host} \
could not be read for ${campaign_ssh_patience_s}s"
}

# Starts one queue entry on <host>, in the background (campaign_stream_job),
# on the class tree and plan of the generation current now (a later GROW
# weaves a new one; this start keeps its own); the ledger row
# campaign_stream_admit_host charged is its own until it returns.
campaign_stream_start() {
  local entry=$1 host=$2 kind round id session worker
  local -a work=()
  read -r kind round id session <<<"${entry}"
  if [[ "${kind}" == OBLIGATION ]]; then
    worker="${iteration_dir}/${round}/${id}"
    work=("${id}" "${iteration_dir}/${round}/obligations.jsonl" \
      "${stream_classes}" "${worker}" "${sessions}" "${stream_plan}")
  else
    worker=$(campaign_stream_rerun_dir "${round}" "${id}")
    work=("${id}" "${stream_classes}" "${worker}" "${worker}/sessions" \
      "${stream_plan}" "${obligation_memory_mb}")
  fi
  printf '%s\n' "${host}" >"${worker}/host.txt"
  [[ "${kind}" != OBLIGATION ]] || stream_solver_seen[${host}]=$(date +%s)
  campaign_stream_job "${kind}" "${host}" "${campaign_host_charge_id}" \
    "${id}" "${worker}" "${work[@]}" &
  stream_jobs[$!]="${kind} ${round} ${id} ${host} ${session}"
  stream_host_jobs[${host}]=$(( ${stream_host_jobs[${host}]:-0} + 1 ))
}

# Waits for the next return -- a job's or the step's -- or for the poll
# interval at most (the queue may wait for room, and the head's room stays
# fresh).  What already ended is taken without waiting: bash reaps a child
# that ends while the head works, and `wait -n` then waits for the next.
campaign_stream_wait() {
  local pid finished="" status
  local -a ended=()
  campaign_head_heartbeat
  if [[ -z "${stream_ticker}" ]]; then
    sleep "${campaign_host_poll_s}" &
    stream_ticker=$!
  fi
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} "${stream_ticker}"; do
    kill -0 "${pid}" 2>/dev/null || ended+=("${pid}")
  done
  if (( ${#ended[@]} == 0 )); then
    status=0
    wait -n -p finished "${!stream_jobs[@]}" ${stream_step_pid} \
      "${stream_ticker}" || status=$?
    [[ -z "${finished}" ]] || campaign_stream_ended "${finished}" "${status}"
  fi
  for pid in "${ended[@]}"; do
    status=0
    wait "${pid}" || status=$?
    campaign_stream_ended "${pid}" "${status}"
  done
}

# One child the head waited for, ended with <status>: the ticker; the step
# (campaign_stream_step_done); or a job, whose host has its slot back (its
# ledger row it gave back itself, campaign_stream_job) and whose return
# waits in stream_pending for the next step to land it.
campaign_stream_ended() {
  local pid=$1 status=$2 kind round id host session
  if [[ "${pid}" == "${stream_ticker}" ]]; then
    stream_ticker=""
  elif [[ "${pid}" == "${stream_step_pid}" ]]; then
    campaign_stream_step_done "${status}"
  else
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    unset 'stream_jobs[$pid]'
    stream_host_jobs[${host}]=$(( stream_host_jobs[${host}] - 1 ))
    stream_pending+=("${kind} ${round} ${id} ${host} ${status} ${session}")
  fi
}

# What returned since the last step began, landed: each obligation's
# verdict into the ledger and the session it staged into stream_staged
# (campaign_stream_move); each re-run's into stream_swaps, for once no
# obligation runs.
campaign_stream_land() {
  local entry kind round id host status session worker verdict
  for entry in "${stream_pending[@]}"; do
    read -r kind round id host status session <<<"${entry}"
    if [[ "${kind}" == RERUN ]]; then
      stream_swaps+=("${round} ${id} ${session} ${status}")
      continue
    fi
    unset 'stream_flying[$id]'
    worker="${iteration_dir}/${round}/${id}"
    [[ "${status}" -eq 0 ]] || campaign_obligation_unfinished "${host}" \
      "${id}" "${worker}" "${status}"
    verdict=$(jq -r '.verdict // "?"' "${worker}/obligation_result.jsonl" \
      2>/dev/null) || verdict="?"
    session=$(jq -r '.sessionId // ""' "${worker}/obligation_result.jsonl" \
      2>/dev/null) || session=""
    campaign_log "obligation ${id}: host=${host} verdict=${verdict}"
    [[ -z "${session}" ]] \
      || stream_staged+=("${worker} ${worker}/sessions ${session}")
    cat -- "${worker}/obligation_result.jsonl" >>"${results}"
    stream_dirty=1
  done
  stream_pending=()
}

# Whether GROW's swaps are due: every re-run it owes has returned, and no
# obligation runs that started before them.
campaign_stream_swap_due() {
  local job
  (( ${#stream_swaps[@]} > 0 && ${#stream_swaps[@]} == stream_hold )) \
    || return 1
  for job in "${stream_jobs[@]}"; do
    [[ "${job}" != OBLIGATION\ * ]] || return 1
  done
}

# The sessions workers staged ("<worker> <staged dir> <session>"), into the
# corpus, each for the next step to gate (gate), and the WITNESSES among
# them for the attempt after it (stream_witnesses) while the exploration has
# not stopped: the replay ADMITTED, and its target row at the declared
# occurrence observed the fatal (ExploreMain#witnesses, the round's
# anchorOccurrences).
campaign_stream_move() {
  local entry worker staged session
  for entry in "${stream_staged[@]}"; do
    read -r worker staged session <<<"${entry}"
    [[ -d "${staged}/${session}" ]] || campaign_fail EXPLORE CAMPAIGN \
      "${staged}" "the verdict names session ${session}, which its worker \
did not stage"
    mv -- "${staged}/${session}" "${sessions}/${session}"
    gate+=("${session}")
    stream_landed=$((stream_landed + 1))
    [[ -z "${stream_stop}" \
       && "$(jq -r '.verdict // ""' "${worker}/obligation_result.jsonl")" \
          == ADMITTED ]] || continue
    # One answer over every row: jq -e reads the last input's output alone.
    jq -e -s --argjson anchors "${stream_anchors}" \
      'any(.[]; .observedFatal == true
              and (.occurrence as $at | any($anchors[]; . == $at)))' \
      "${sessions}/${session}/targets.jsonl" >/dev/null 2>&1 || continue
    stream_witnesses+=("${session}")
  done
  stream_staged=()
}

# The EXPOSED_REGION rows of a round's growth.jsonl, one `obligation region
# session` line each, sorted.
campaign_exposures() {
  jq -r 'select(.kind == "EXPOSED_REGION")
         | [.obligationId, .regionId, .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

# GROW (PIPELINE §7.8): a region a replay reached without its hooks is
# planned, woven in, and the replay that exposed it is run again under the
# same world, so a later round's closure sees the region's decisions and
# exports.
#
# One GROW is one GENERATION of the plan and the class tree:
# ExposedRegionPlanMain synthesises the task rows the exposures need
# (admissionBasis EXPOSED_BY), the generation's plan is the one before it
# plus those rows, written as a new file -- the iteration's plan and the seed
# plan are its links from now on -- and INSTRUMENT weaves it into the
# generation's own tree.  A start takes the generation current when it
# starts (campaign_stream_start), so whatever already runs keeps the plan
# and the classes it started on.  Each exposing obligation's replay is
# queued first, to re-run -- on whichever host of the pool admits it, as an
# obligation does -- in a directory of its own beside its worker; until
# every re-run has returned and swapped its session in
# (campaign_stream_swap), no obligation starts and no round is planned.
campaign_stream_grow() {
  local round_dir=$1 status=0 generation obligation_id session rerun
  local growth="${round_dir}/growth.jsonl"
  local rows="${round_dir}/exposed_region_plan.jsonl"
  local worker file
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
    >"${round_dir}/grow-stdout.log" 2>"${round_dir}/grow-stderr.log"
  [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE ExposedRegionPlanMain \
    "${round_dir}/grow-stderr.log" \
    "the exposed-region planner failed with exit ${status}: \
$(campaign_thrown "${round_dir}/grow-stderr.log")"
  require_nonempty "exposed region plan rows" "${rows}"
  stream_generation=$((stream_generation + 1))
  generation="${iteration_dir}/generations/g${stream_generation}"
  mkdir -p "${generation}"
  cat -- "${stream_plan}" "${rows}" >"${generation}/execution_task_plan.jsonl"
  ln -f "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/execution_task_plan.jsonl"
  ln -f "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  campaign_log "$(basename "${round_dir}"): grown by \
$(jq -r -s 'map(.regionId) | unique | join(",")' "${rows}") \
($(wc -l <"${rows}") task row(s)); weaving generation g${stream_generation}"
  campaign_instrument "${iteration_dir}" "${generation}/instrumented-classes"
  stream_plan="${generation}/execution_task_plan.jsonl"
  stream_classes="${generation}/instrumented-classes"
  while IFS=$'\t' read -r obligation_id session; do
    worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
      "${obligation_id}") || exit 1
    rerun="${worker}/grow-$(basename "${round_dir}")/${obligation_id}"
    mkdir -p "$(dirname "${rerun}")"
    mkdir "${rerun}" || campaign_fail EXPLORE CAMPAIGN "${rerun}" \
      "obligation ${obligation_id} was already re-run for this round"
    # What a replay reads of its worker: the focus row and the schedule cut.
    for file in focused_task.jsonl schedule_prefix.jsonl \
        schedule_suffix.jsonl; do
      [[ ! -e "${worker}/${file}" ]] || ln "${worker}/${file}" "${rerun}/"
    done
    stream_queue=("RERUN $(basename "${round_dir}") ${obligation_id} \
${session}" "${stream_queue[@]}")
    stream_hold=$((stream_hold + 1))
  done < <(campaign_exposures "${growth}" | cut -f1,3 | LC_ALL=C sort -u)
}

# The directory one exposing obligation's re-run for <round> runs in.
campaign_stream_rerun_dir() {
  local round=$1 obligation_id=$2 worker
  worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
    "${obligation_id}") || exit 1
  printf '%s/grow-%s/%s\n' "${worker}" "${round}" "${obligation_id}"
}

# Every re-run that returned, swapped in -- once no obligation runs, since
# one started before the swap may be cut from the exposing session -- and the
# queue cancelled, since what it holds may be cut from one too; the next
# round asks again what is still owed.
#
# One swap: the exposing session leaves the corpus for
# <worker>/before-<round>/ with what its replay wrote, the re-run's files
# become the worker's, its session is staged to land with the others
# (campaign_stream_move), and its verdict replaces the obligation's row in
# the ledger.
campaign_stream_swap() {
  local swap round id session status worker rerun aside file
  local queued=${#stream_queue[@]}
  for swap in "${stream_swaps[@]}"; do
    read -r round id session status <<<"${swap}"
    worker=$(campaign_obligation_worker_dir "${iteration_dir}" "${id}") \
      || exit 1
    rerun="${worker}/grow-${round}/${id}"
    [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE CAMPAIGN "${rerun}" \
      "the re-run of ${id} did not finish (exit ${status})"
    aside="${worker}/before-${round}"
    mkdir "${aside}" || campaign_fail EXPLORE CAMPAIGN "${aside}" \
      "obligation ${id} was already swapped for this round"
    campaign_withdraw_sessions "${id}" "${sessions}" "${aside}/sessions" \
      "it exposed a region that is woven now, and the re-run's session \
stands in its place"
    [[ ! -e "${sessions}/${session}" ]] || campaign_fail EXPLORE CAMPAIGN \
      "${sessions}/${session}" "the exposing session ${session} does not \
name obligation ${id}, so it was not withdrawn from the corpus"
    # The question the exposing replay settled was asked of the plan before
    # this generation, and goes aside with its answer.
    for file in replay.log concolic_region_results.jsonl \
        obligation_result.jsonl replay_verdict.jsonl question.txt \
        question.asked stdout.log stderr.log host.txt; do
      [[ ! -e "${worker}/${file}" ]] || mv -- "${worker}/${file}" "${aside}/"
      [[ ! -e "${rerun}/${file}" ]] || mv -- "${rerun}/${file}" "${worker}/"
    done
    session=$(jq -r '.sessionId // ""' "${worker}/obligation_result.jsonl")
    [[ -z "${session}" ]] \
      || stream_staged+=("${worker} ${rerun}/sessions ${session}")
    campaign_record_rerun "${iteration_dir}" "${id}" "${results}"
  done
  stream_hold=$((stream_hold - ${#stream_swaps[@]}))
  stream_swaps=()
  stream_dirty=1
  campaign_stream_drop again
  (( queued == 0 )) || campaign_log "the grown corpus asks again: ${queued} \
queued obligation(s) left to the next round"
}

# The obligation worker directory of one obligation, with its focus row.
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

# Once nothing runs: the last generation's tree is the iteration's
# (CONFIRM and REPRODUCE replay on instrumented-classes), and the trees of
# the generations before it, which nothing reads any more, are gone.
campaign_stream_promote_generation() {
  local generation
  (( stream_generation > 0 )) || return 0
  rm -rf -- "${iteration_dir}/instrumented-classes"
  mv -- "${stream_classes}" "${iteration_dir}/instrumented-classes"
  for generation in "${iteration_dir}"/generations/g*; do
    rm -rf -- "${generation}/instrumented-classes"
  done
}

# exploration.json: how EXPLORE ended, how many rounds and head steps it
# took, every COMPOSE attempt at a witness, and every obligation it dropped
# -- cancelled from the queue, or reaped before it landed -- by id.
campaign_stream_manifest() {
  jq -n \
    --arg stop "${stream_stop}" --arg detail "${stream_stop_detail}" \
    --argjson rounds "${stream_round}" --argjson steps "${stream_steps}" \
    --argjson generations "${stream_generation}" \
    --argjson answered "$(grep -c '' "${results}" || true)" \
    --argjson cancelled "$(printf '%s\n' "${stream_cancelled[@]}" \
      | jq -R 'select(length > 0)' | jq -s -c .)" \
    --argjson reaped "$(printf '%s\n' "${stream_reaped[@]}" \
      | jq -R 'select(length > 0)' | jq -s -c .)" \
    --slurpfile attempts "${attempts}" \
    '{schemaVersion: 1, kind: "EXPLORATION", stop: $stop, detail: $detail,
      rounds: $rounds, steps: $steps, generations: $generations,
      answered: $answered,
      witnessAttempts: $attempts, cancelled: $cancelled, reaped: $reaped}' \
    >"${iteration_dir}/exploration.json"
}

# Gap rows this iteration's stages wrote outside a session live in one file,
# ${iteration_dir}/campaign_gaps.jsonl, appended by whoever raises them and
# read once by EMIT.  Nothing collects or truncates it.
#
# Session gap rows stay where the replay wrote them: EMIT reads them straight
# out of the session directories, because a GapRow states its own class and
# nothing between the runtime and the report is in a position to change it.

# How many obligations of one iteration a worker did not finish
# (campaign_obligation_unfinished's gap rows).
campaign_unfinished_count() {
  local gaps="$1/campaign_gaps.jsonl"
  [[ -s "${gaps}" ]] || { printf '0\n'; return 0; }
  jq -s '[.[] | select(.subject == "OBLIGATION_UNFINISHED")] | length' \
    "${gaps}"
}

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
    --argjson unfinished "$(campaign_unfinished_count "${iteration_dir}")" \
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
     unfinishedObligations: $unfinished,
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
  # One claim at a time: a refuted one has moved to final/refuted/
  # (campaign_next_claim) before the next is composed.
  [[ ! -e "${campaign_final}/candidate.smt2" ]] || die \
    "the final directory already holds a claim: ${campaign_final}"
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
    "the composer failed with exit ${status} on inputs it was given: \
$(campaign_thrown "${campaign_final}/compose.log")"
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
# claim has nothing to confirm and the stage says so.  An unconfirmed claim
# is refuted (campaign_refute), and the campaign goes on to the next one
# while its budget has room (campaign_next_claim).  The exploration's
# witness was confirmed as it was accepted (campaign_stream_attempt): the
# same model, composed again over the same corpus, is not replayed twice.
campaign_confirm() {
  local iteration_dir=$1 claim
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  if [[ "${claim}" != SAT_CANDIDATE ]]; then
    campaign_log "claim=${claim}: nothing to confirm"
    return 0
  fi
  if [[ -s "${campaign_witness_attempt}/confirm.json" ]] \
      && [[ "$(campaign_claim_model "${campaign_final}/claim.json")" \
        == "$(campaign_claim_model "${campaign_witness_attempt}/claim.json")" ]]
  then
    cp -- "${campaign_witness_attempt}/confirm.json" \
      "${campaign_final}/confirm.json"
    campaign_log "the model is the exploration's witness, confirmed in \
${campaign_witness_attempt}"
  else
    campaign_confirm_claim "${iteration_dir}" "${campaign_final}" \
      "${campaign_final}/confirm"
  fi
  jq -r '"  confirmed=\(.confirmed) session=\(.sessionId) \(.reason)"' \
    "${campaign_final}/confirm.json"
}

# One claim confirmed (campaign_confirm): the one <claims>/claim.json states,
# beside its candidate_composition_manifest.json; ConfirmMain's worker, the
# replay's sessions and the log in <dir>, the verdict <claims>/confirm.json.
# It is refuted (campaign_refute) only when the verdict refutes it: the
# replay ran the model and disagreed, or ConfirmMain refused it by name.  A
# replay that timed out or published no verdict, or a decision that failed,
# leaves the model unconfirmed and open: a later attempt may claim it again.
campaign_confirm_claim() {
  local iteration_dir=$1 claims=$2 dir=$3
  local worker sessions status=0 reason need
  [[ ! -e "${dir}" ]] \
    || die "the confirmation directory already exists: ${dir}"
  worker="${dir}/worker"
  sessions="${dir}/sessions"
  mkdir -p "${worker}" "${sessions}"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${iteration_dir}" \
    --claim "${claims}/claim.json" \
    --manifest "${claims}/candidate_composition_manifest.json" \
    --output "${worker}" >"${dir}/confirm.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    reason=$(grep -m 1 'CONFIRM refused:' "${dir}/confirm.log" \
      || grep -v -E '^[[:space:]]+at ' "${dir}/confirm.log" \
        | tail -n 1)
    # A refusal ConfirmMain names is the claim's own: no run can realize
    # it.  Any other exit says nothing about the model.
    campaign_confirm_verdict false \
      "${reason:-ConfirmMain exited ${status}}" "" \
      "$([[ "${reason}" == *'CONFIRM refused:'* ]] && echo true \
        || echo false)" >"${claims}/confirm.json"
  elif [[ -s "${worker}/realized.json" ]]; then
    # The selected session already took every edge the model chose, with
    # the moved roots at the model's values, and observed the fatal: that
    # run is the confirmation, and a replay of its world would test only
    # whether a race the order does not hold goes the same way twice.
    jq -c '.' "${worker}/realized.json" >"${claims}/confirm.json"
  else
    # The replay, exactly as an obligation's, charged as the seed replay is
    # (campaign_replay_need_mb) wherever there is room.  A campaign_fail
    # inside it ends a campaign; here, in a subshell, it ends the
    # confirmation as "no verdict", which is one more way of not agreeing
    # with the model.
    need=$(campaign_replay_need_mb)
    ( campaign_head_charged "${need}" 300 \
        campaign_obligation_replay CONFIRM \
        "${iteration_dir}/instrumented-classes" "${worker}" "${sessions}" \
        "${iteration_dir}/seed-replay/execution_task_plan.jsonl" "${need}" ) \
      >>"${dir}/confirm.log" 2>&1 || status=$?
    if [[ "${status}" -ne 0 ]]; then
      campaign_confirm_verdict false "the confirmation replay published no \
verdict (exit ${status}); its log is ${dir}/confirm.log" "" false \
        >"${claims}/confirm.json"
    else
      run_capturing_status run_java_main \
        edu.uva.liftlab.graphchecker.explore.ConfirmMain \
        --claim "${claims}/claim.json" --output "${worker}" \
        --sessions "${sessions}" >"${claims}/confirm.json" \
        2>>"${dir}/confirm.log"
      [[ "${status}" -eq 0 ]] || campaign_confirm_verdict false "the \
confirmation decision exited ${status}; its log is ${dir}/confirm.log" "" \
        false >"${claims}/confirm.json"
    fi
  fi
  require_nonempty "confirmation" "${claims}/confirm.json"
  [[ "$(jq -r '.refutes' "${claims}/confirm.json")" != true ]] \
    || campaign_refute "${iteration_dir}" "${claims}"
}

# A claim's model, one line: its finding kind, the path it selected, the arms
# it chose there, its valuation and its moved roots, a clock by its cell at
# the model's instant (compose.Refutations reads the same).
campaign_claim_model() {
  jq -c '.claim as $c | $c.valuationOrdinal as $o | (.valuations // [])[]
    | select(.ordinal == $o) | {findingKind: $c.kind,
      pathId: .selectedPathId,
      arms: ([(.selectedArms // [])[].selector] | sort),
      assignment: (.assignment // {}), moved: ($c.movedRoots // {})}' "$1"
}

# A claim the program did not agree with, refuted: its model, where it was
# claimed and the confirmation's reason, one row of
# <iteration>/refuted_claims.jsonl, which every later composition of the
# iteration excludes (compose.Refutations) and EMIT publishes.
campaign_refute() {
  local iteration_dir=$1 claims=$2
  campaign_claim_model "${claims}/claim.json" \
    | jq -c --slurpfile confirmation "${claims}/confirm.json" \
      --arg claimed "${claims}" \
      '{schemaVersion: 1, kind: "REFUTED_CLAIM", model: ., claimed: $claimed,
        reason: $confirmation[0].reason}' \
    >>"${iteration_dir}/refuted_claims.jsonl"
  campaign_log "refuted: $(jq -r '.reason' "${claims}/confirm.json")"
}

# Whether the campaign's budget (campaign_budget_s from its start) has room
# for one more claim past the exploration: its reserve (campaign_reserve).
campaign_claim_room() {
  (( campaign_budget_s - (SECONDS - campaign_started_s) \
    >= $(campaign_reserve) ))
}

# What the stages after the exploration are owed, in seconds: one COMPOSE and
# one CONFIRM, each as long as the longest this campaign measured -- its
# stage metrics and its witness attempts; the seed's REPLAY stands for a
# CONFIRM replay none has run yet -- and never less than campaign_reserve_s.
campaign_reserve() {
  local measured
  measured=$( {
      awk -F '\t' '$1 == "COMPOSE" || $1 == "CONFIRM" || $1 == "REPLAY" {
        print $1, $2 }' "${campaign_stage_metrics}" 2>/dev/null
      jq -r '"COMPOSE \(.composeMillis // 0)", "CONFIRM \(.confirmMillis // 0)"' \
        "${campaign_root}/iteration-0000/witness_attempts.jsonl" 2>/dev/null
    } | awk '$1 == "COMPOSE" { if ($2 > c) c = $2; next }
        { if ($2 > r) r = $2 }
        END { printf "%d\n", (c + r) / 1000 }')
  echo $(( measured > campaign_reserve_s ? measured : campaign_reserve_s ))
}

# Whether the final stages owe the next claim: the last was a SAT_CANDIDATE
# the program refuted, its model is refuted once -- recorded, so the next
# composition excludes it, and not a model it was told was refuted already
# -- and the budget has room.  The refuted claim's artifacts move to
# final/refuted/NNNN/ first, so final/ holds the claim EMIT publishes.
campaign_next_claim() {
  local iteration_dir=$1 dir name model seen=0
  [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      == SAT_CANDIDATE && -s "${campaign_final}/confirm.json" \
    && "$(jq -r '.refutes' "${campaign_final}/confirm.json")" == true ]] \
    || return 1
  model=$(campaign_claim_model "${campaign_final}/claim.json")
  [[ -z "${model}" || ! -s "${iteration_dir}/refuted_claims.jsonl" ]] \
    || seen=$(jq -c '.model' "${iteration_dir}/refuted_claims.jsonl" \
      | grep -c -x -F -- "${model}" || true)
  if (( seen != 1 )); then
    campaign_log "the refuted claim's model is refuted ${seen} time(s), \
not once: the next composition could repeat it, so there is no next claim"
    return 1
  fi
  if ! campaign_claim_room; then
    campaign_log "the campaign budget (campaign_budget_s=${campaign_budget_s}) \
has no room for another claim"
    return 1
  fi
  dir=$(printf '%s/refuted/%04d' "${campaign_final}" \
    "$(find "${campaign_final}/refuted" -mindepth 1 -maxdepth 1 2>/dev/null \
      | grep -c '' || true)")
  mkdir -p "${dir}"
  for name in candidate.smt2 candidate_composition_manifest.json claim.json \
      compose.log confirm confirm.json; do
    [[ ! -e "${campaign_final}/${name}" ]] \
      || mv -- "${campaign_final}/${name}" "${dir}/"
  done
  campaign_log "the claim was refuted (${dir}): composing the next one"
}

# REPRODUCE (ADHOC-INFRA WP5.D), after EMIT: a confirmed witness run again
# natively -- the recording weave on the stock JDK, planting the fault
# markers the confirmation's world plants and watching the target's guards
# for their fatal arm at the claim's anchor (explore.ConfirmMain --plant, the
# code that wrote CONFIRM's world; runtime.RecordingPlant).  reproduce_runs
# runs, all at once, each a head step charged the recording's measured peak
# resident memory wherever there is room (campaign_reproduce_one) and
# bounded by reproduce_time_factor times the recording's own workload; a run
# ends as soon as the planted world takes the fatal arm at the anchor, its
# one question answered.  Each run states its answer itself
# (campaign_reproduce_run); final/reproduce.json counts them -- runs, how
# many planted a marker, took the target's fatal arm, took it at the claim's
# own anchor -- and names the runs that stated none.  A native run holds no
# schedule, so the planted occurrence may not recur: the rate ranks a finding
# (tools/adhoc/findings.py) and never refutes it, and nothing here moves the
# claim, CONFIRM's decision or what EMIT published.  A world a native run
# cannot plant (a clock, an attach's answer, any root but a marker), or a
# recording that measured no peak memory, is a reproduce.json with no run and
# the reason.  Only a confirmed SAT_CANDIDATE is reproduced.
campaign_reproduce() {
  local iteration_dir=$1
  local dir="${campaign_final}/reproduce" status=0 bound run reason="" pid
  local -a pids=()
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
    --static-scope-map "${causynth_static_scope_map}" \
    --plant "${dir}/plant.jsonl" >"${dir}/plant.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    reason="no native run: $(sed -n 's/^CONFIRM refused: //p' \
      "${dir}/plant.log" | head -n 1)"
  elif [[ ! "${campaign_recorded_workload_rss_mb}" =~ ^[0-9]+$ ]]; then
    reason="no native run: the recording measured no peak resident memory \
(workload_rss_mb) to charge one with"
  fi
  if [[ -n "${reason}" ]]; then
    jq -n --arg reason "${reason}" '{schemaVersion: 1, kind: "REPRODUCTION",
      runs: 0, planted: 0, fatal: 0, atAnchor: 0, reason: $reason}' \
      >"${campaign_final}/reproduce.json"
    campaign_log "reproduce: ${reason}"
    return 0
  fi
  bound=$(( reproduce_time_factor * campaign_recorded_workload_s ))
  campaign_log "reproduce: ${reproduce_runs} native run(s) at once, each \
charged ${campaign_recorded_workload_rss_mb} MB and bounded by ${bound}s \
(reproduce_time_factor=${reproduce_time_factor} x the recording's \
${campaign_recorded_workload_s}s)"
  for ((run = 0; run < reproduce_runs; run++)); do
    campaign_reproduce_one "${dir}/run-$((run + 1))" "${bound}" \
      "${dir}/plant.jsonl" &
    pids+=("$!")
  done
  for pid in "${pids[@]}"; do
    wait "${pid}" || true
  done
  find "${dir}" -mindepth 2 -maxdepth 2 -name answer.json -print0 \
    | xargs -0 -r cat \
    | jq -s --argjson runs "${reproduce_runs}" '
      {schemaVersion: 1, kind: "REPRODUCTION", runs: $runs,
       planted: map(select(.planted)) | length,
       fatal: map(select(.fatal)) | length,
       atAnchor: map(select(.atAnchor)) | length,
       reason: (if length < $runs
         then "\($runs - length) of \($runs) run(s) stated no answer"
         else "" end)}' >"${campaign_final}/reproduce.json"
  jq -r '"  reproduced at the anchor in \(.atAnchor) of \(.runs) native run(s) (\(.planted) planted, \(.fatal) fatal)"' \
    "${campaign_final}/reproduce.json"
}

# One native run of REPRODUCE into <run>: a head step charged the
# recording's peak memory for an obligation's ramp, wherever there is room
# (campaign_head_charged), and released as it returns.  A run placed on a
# peer has its answer waited for until the shared home shows it here
# (campaign_remote_visibility_wait_s); one that never shows states none.
campaign_reproduce_one() {
  local run=$1 bound=$2 plant=$3 waited=0
  mkdir -p "${run}"
  campaign_head_charged "${campaign_recorded_workload_rss_mb}" \
    "${campaign_host_ramp_s}" campaign_reproduce_run "${analysis_classes_dir}" \
    "${run}" "${bound}" "${plant}" "${campaign_recorded_workload_rss_mb}" \
    || campaign_log "reproduce: $(basename "${run}") exited nonzero; its \
logs are in ${run}"
  campaign_host_is_local "${campaign_placed_host}" && return 0
  while [[ ! -s "${run}/answer.json" ]] \
      && (( waited < campaign_remote_visibility_wait_s )); do
    ls "${run}" >/dev/null 2>&1 || true
    sleep 1
    waited=$((waited + 1))
  done
}

# One native run, on the host it was placed on, which it names in
# <run>/host.txt: the workload in the recording weave <classes> with
# <plant>, charged <charged_mb>, its trace into <run>, under <seconds>, its
# output in <run>.  Whatever
# the workload's exit -- a planted fault may well fail the test, and a run
# that answered ends early -- its answer is <run>/answer.json, read off its
# trace's plant rows (a run killed mid-row loses only that row): {exit,
# planted, fatal, atAnchor}.
campaign_reproduce_run() {
  local analysis_classes_dir=$1 run=$2 bound=$3 plant=$4 charged=$5 status=0
  local trace="${run}/runtime_trace.jsonl"
  hostname -s >"${run}/host.txt"
  run_capturing_status run_configured_workload "${run}" "${bound}" "${plant}" \
    "${charged}" >"${run}/stdout.log" 2>"${run}/stderr.log"
  [[ -s "${trace}" ]] || trace=/dev/null
  jq -n -c -R --argjson exit "${status}" '
    reduce (inputs | select(contains("\"event\":\"PLANT_")) | fromjson?)
        as $row ({exit: $exit, planted: false, fatal: false,
                  atAnchor: false};
      if $row.event == "PLANT_APPLIED" then .planted = true
      elif $row.event == "PLANT_FATAL"
      then .fatal = true | .atAnchor = (.atAnchor or $row.atAnchor)
      else . end)' "${trace}" >"${run}/answer.json.part"
  mv -f -- "${run}/answer.json.part" "${run}/answer.json"
}

# The one shape of final/confirm.json.
campaign_confirm_verdict() {
  local confirmed=$1 reason=$2 session_id=$3 refutes=$4
  jq -n --argjson confirmed "${confirmed}" --arg reason "${reason}" \
    --arg sessionId "${session_id}" --argjson refutes "${refutes}" \
    '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: $confirmed,
      refutes: $refutes, reason: $reason, sessionId: $sessionId}'
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
  # worker's or a round's are EXPLORE, and a campaign row states its own stage
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
  # Every claim CONFIRM refuted on the way, in order: the filtered false
  # positives (tools/adhoc/triage.py), whatever the claim published.
  local refuted="${iteration_dir}/refuted_claims.jsonl"
  [[ -s "${refuted}" ]] || refuted=/dev/null
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --argjson confirmation "${confirmation}" \
    --slurpfile refutedClaims "${refuted}" \
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
     refutedClaims: $refutedClaims,
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
     # What each moved root is (CLOCK, FAULT, CONFIG, READ, HOOK), and
     # whether the witness moves configuration only: the one rule of
     # COMPOSE, which a sweep ranks such a witness by, after the others.
     movedRootCategories: $decided.movedRootCategories,
     configurationOnly: $decided.configurationOnly,
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
}

# The campaign's exit, read off the result EMIT published.  A published
# artifact set is not an accepted candidate: a run that reached no witness
# and no closed refutation exits 2 with its own named reason, because a
# top-level zero exit is not completion; one that names BLOCKING gaps, 3.
campaign_exit_verdict() {
  local gapCount
  gapCount=$(jq -r '.gapCount' "${campaign_final}/gaps.json")
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
      # Each member's campaign ended there: its own log says where.
      for name in ${members[$group]}; do
        sed -n '/^\[campaign:error\]/,$p' "${groups}/group-${group}.log" \
          >>"${causynth_output_dir}/targets/${name}/campaign.log"
      done
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
  # As campaign_plan freezes it: a recording that states no schedule has none.
  [[ ! -s "${causynth_output_dir}/runtime/schedule.jsonl" ]] \
    || cp -f "${causynth_output_dir}/runtime/schedule.jsonl" \
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
# its causynth_output_dir (so every stage -- and every peer of its pool,
# which derive their paths from it -- reads its slice and its region plan
# there), its spec that one target's line, and its campaign root
# targets/<name>/schedule/.  In a subshell of its own.
campaign_batch_enter() {
  local name=$1
  causynth_output_dir="${causynth_output_dir}/targets/${name}"
  derive_output_paths
  causynth_target_spec="${causynth_output_dir}/target.yaml"
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  mkdir -p "${campaign_root}"
  touch "${campaign_stage_metrics}"
  campaign_init_local_scratch_root
}

# A planned target's campaign from EXPLORE on, over its group's seed <group>
# (campaign_batch_group): its iteration takes the group's union plan (a copy:
# GROW writes its own generations), its woven classes and seed session (hard
# links: GROW weaves its own trees), and its census and import gate (the
# gate's ledger with them: the seed is gated, and each landed session's gate
# judges the set against it); its
# own PLAN is read again (campaign_plan_read).
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
    "${group}/import_gated.txt" "${group}/woven_class_verification.log" \
    "${iteration_dir}/"
  # The gate writes its gap rows only when a row states one.
  [[ ! -e "${group}/campaign_gaps.jsonl" ]] \
    || cp -- "${group}/campaign_gaps.jsonl" "${iteration_dir}/"
  campaign_log "target ${name}: campaign root ${campaign_root}, seed of \
${group}"
  campaign_iteration_explore "${iteration_dir}" iteration-0000
}

# What every peer entry (--run-obligation, --run-placed) checks before its
# work, on this machine.
#
# The peer loads the same configuration file the campaign loaded, from the
# same shared home, and every path in it resolves identically -- but two
# values are NOT in that file and must arrive already decided, or this worker
# silently does different work from the local workers of the same campaign.
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
#     while the campaign runs cannot reach a worker.
# The positional arguments after "--" are left in campaign_peer_args.
campaign_peer_args=()
campaign_peer_enter() {
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
  [[ -n "${jar}" ]] || die "a peer requires --graphchecker-jar: \
the campaign's frozen jar is not derivable from the configuration"
  [[ -n "${jar_sha}" ]] || die "a peer requires --graphchecker-jar-sha256"
  graphchecker_jar=${jar}
  require_file "GraphChecker jar" "${graphchecker_jar}"
  actual_sha=$(campaign_digest "${graphchecker_jar}")
  [[ "${actual_sha}" == "${jar_sha}" ]] || die "the GraphChecker jar this \
worker was handed is not the one the campaign froze: ${graphchecker_jar} is \
${actual_sha}, the campaign says ${jar_sha}"
  # The same gate the head's PREFLIGHT ran, so a peer that resolved a
  # nonsense configuration says so here rather than inside a workload JVM.
  validate_config >/dev/null
  require_command_available jq
  require_command_available sha256sum
  # Set from the CAUSYNTH_LOCAL_SCRATCH the campaign forwarded, so this
  # worker's scratch lands on THIS machine's local disk under the same
  # per-run root every other worker of the run uses.
  campaign_init_local_scratch_root
  campaign_log "peer $(hostname): jar ${graphchecker_jar} (${actual_sha}), \
scratch ${campaign_local_scratch_root:-<shared home>}"
  campaign_peer_args=("$@")
}

# ONE step of somebody else's campaign head, on this machine
# (campaign_run_placed): <workdir> <NAME=VALUE>... -- <command...>.  The
# head's exported variables are exported here, so the command -- a program,
# or a run_engine.sh function whose arguments are all it reads of the head
# -- sees the environment it would have seen there; its standard output is
# the command's alone.
do_run_placed() {
  campaign_peer_enter "$@" >&2
  set -- "${campaign_peer_args[@]}"
  [[ $# -ge 1 ]] && cd -- "$1" \
    || die "--run-placed: no working directory ${1:-}"
  shift
  while [[ $# -gt 0 && "$1" != -- ]]; do
    export "${1?}"
    shift
  done
  [[ $# -ge 2 ]] || die "--run-placed takes a working directory, the \
head's assignments, -- and a command"
  shift
  "$@"
}

# ONE obligation of somebody else's campaign, on this machine.
do_run_obligation() {
  campaign_peer_enter "$@"
  set -- "${campaign_peer_args[@]}"
  [[ $# -eq 6 ]] || die "--run-obligation takes six positional arguments \
(id obligations classes worker sessions seed-plan), got $#"
  campaign_obligation_worker "$@"
}

# One campaign, one iteration.  What a replay learns past the recording's
# topology is taken up inside EXPLORE's loop (GROW), so there is nothing
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
  # This shell is the head: its engine JVMs and its replays are charged
  # wherever they are placed, its own host first (campaign_head_charged),
  # and its host keeps room for the next one (campaign_head_reserve).
  campaign_head_charging=1
  campaign_head_reserve

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
  campaign_claim_stages "${iteration_dir}"
  # A refuted claim does not end the campaign while its budget has room:
  # the next composition excludes it (campaign_next_claim).
  while campaign_next_claim "${iteration_dir}"; do
    campaign_claim_stages "${iteration_dir}"
  done
  campaign_stage EMIT campaign_emit "${iteration_dir}"
  # After the verdict is published, never before it: REPRODUCE ranks a
  # confirmed finding and moves no claim.
  campaign_stage REPRODUCE campaign_reproduce "${iteration_dir}"
  campaign_exit_verdict
}

# One claim of the iteration: composed, solved, decided and confirmed.
campaign_claim_stages() {
  campaign_stage COMPOSE campaign_compose "$1"
  campaign_stage SOLVE campaign_solve
  campaign_stage DECIDE campaign_decide
  campaign_stage CONFIRM campaign_confirm "$1"
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
  campaign|slice|record|config|validate|--run-obligation|--run-placed)
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
      --run-placed) do_run_placed "$@" ;;
    esac
    ;;
  *)
    die "unknown command '${command_name}' (run './run_engine.sh help')"
    ;;
esac
