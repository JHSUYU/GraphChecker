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
  ./run_engine.sh --config FILE reproduce
  ./run_engine.sh --config FILE --run-obligation \
      --graphchecker-jar JAR --graphchecker-jar-sha256 SHA -- \
      ID OBLIGATIONS SESSIONS WORKER CHARGED_MB
  ./run_engine.sh help

Commands:
  campaign    Run the complete campaign for one configuration: validate, seed,
              then one iteration of plan/instrument/replay/import/explore
              (a streaming pool of obligations, growing the woven region
              set as replays expose it) and
              compose/solve/decide/confirm/reproduce/emit.
  reproduce   REPRODUCE alone over a finished campaign: the configuration's
              output directory (CAUSYNTH_OUTPUT_DIR, a copy of one, so the
              original is never written; tools/rounds/reproduce-again.sh)
              holds a confirmed claim and no reproduction yet
  config      Print the normalized workflow configuration
  validate    Validate required workflow configuration fields
  help        Print this help message

  --run-obligation
              Solve ONE obligation that some campaign planned, and
              nothing else (its replay is a placed step of its own).
              This is what `campaign_worker_hosts` runs
              over ssh on a peer; the campaign generates the invocation into
              the obligation's own worker directory, so it is not a command
              to be typed.  The five positional arguments are exactly what
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
  # Whether the exploration shares its hosts' replay slots with the other
  # explorations that share them (a sweep's cases, tools/adhoc/sweep.sh):
  # it starts one more only while it runs fewer than its share, the slots
  # its hosts hold at its measured replay charge (campaign_pool_slots,
  # campaign_replay_need_mb) over the sharing explorations running now, at
  # least one (campaign_stream_has_slot), so one running alone takes them
  # all and ten take a tenth each.  One case's pool kept 27-32 Solr replays
  # in flight on all ten lifts while the sweep's other cases waited for room
  # (a40).  false -- the default, a named acceptance run's -- shares
  # nothing: the hosts' memory and cores alone decide.
  "stream_shared_pool CAUSYNTH_STREAM_SHARED_POOL krp false"
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
  # How many times REPRODUCE runs a confirmed witness natively, and each
  # run's wall clock: this factor times the recording's own workload, at
  # least reproduce_min_s (campaign_reproduce_bound).
  "reproduce_runs CAUSYNTH_REPRODUCE_RUNS krp 10"
  "reproduce_time_factor CAUSYNTH_REPRODUCE_TIME_FACTOR krp 3"
  "reproduce_min_s CAUSYNTH_REPRODUCE_MIN_S krp 300"
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
  # seconds, however short the stages it is measured from (campaign_reserve).
  "campaign_reserve_s CAUSYNTH_CAMPAIGN_RESERVE_S krp 600"
  # How many times the final stages decide a claim again after CONFIRM
  # refuted one or gave it no verdict (campaign_next_claim): each excludes
  # that claim's region (compose.Refutations), and past this many the last
  # claim is published as it stands, by name, however much budget is left.
  "campaign_max_claims CAUSYNTH_CAMPAIGN_MAX_CLAIMS krp 8"
  # The wall clock the SEED replay may take, as a multiple of how long the
  # recording's workload ran (SEED times it), and never less than one
  # focused replay's replay_timeout_s.  Unbounded, a seed replay that
  # stopped progressing held its case to the case budget and died unnamed
  # (11 of h4's 111 cases, 7 of q5's 154, at 5400 s); a replay past this
  # fails the campaign at REPLAY naming it.  The seed replays the 09-29
  # sweeps finished took up to 38x their recording, one of 78 took 63x.
  "seed_replay_time_factor CAUSYNTH_SEED_REPLAY_TIME_FACTOR krp 40"
  # The most trace the recording may write, in MB: past it the workload is
  # ended and SEED fails RECORDING_BOUND, by name (campaign_watch_workload;
  # one that writes nothing for campaign_unbounded_stall_s, RECORDING_STALLED).
  # The aggregation holds every row it reads in memory, a little more than
  # their bytes: hdfs-adhoc-49 (TestSnapshot, 36 clusters) writes 8.5 GB
  # of the rows it reads, which no 8 GB aggregation held; the HDFS
  # regression cases write 1-19 MB, the largest ad-hoc checks ~1 GB.
  "recording_max_trace_mb CAUSYNTH_RECORDING_MAX_TRACE_MB krp 4096"
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
  z3_bin=${z3_bin:-${Z3_BIN}}
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
  # The discovery artifacts, one layout under the resolved output directory.
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
# -- on whichever host a campaign's head placed it, for as long as it runs
# (campaign_head_charged) -- and at the case's
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
# campaign_jvm_footprint_mb <heap_mb>: what an engine JVM run at -Xmx<heap_mb>
# is charged and held on its host: its heap and the JVM's own memory beside
# it (metaspace, code cache, the collector's tables, thread stacks), a
# sixteenth of the heap and 384 MB.  Charged at its heap alone, a served
# planner that filled it passed its charge on a host near the ceiling and was
# ended (solr-adhoc-07 RX4: 8375 MB resident at an 8192 MB heap).
campaign_jvm_footprint_mb() {
  printf '%s\n' "$(( $1 + $1 / 16 + 384 ))"
}

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
    campaign_head_charged "$(campaign_jvm_footprint_mb "${start}")" \
      campaign_engine_jvm \
      "${campaign_root:+${campaign_root}/engine_peak_mb}" \
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
  campaign_head_charged "$(campaign_jvm_footprint_mb "${heap}")" \
    campaign_engine_jvm \
    "${campaign_root:+${campaign_root}/engine_peak_mb}" \
    env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
    -XX:+ExitOnOutOfMemoryError "$@"
}

# campaign_engine_jvm <peak_file> <command...>: one engine JVM of a head
# (engine_java), run where its step was placed and watched until it ends
# (campaign_watch_workload, charging nothing past its step's charge): its
# peak resident memory joins <peak_file> (the campaign's
# ${campaign_root}/engine_peak_mb, the largest any of its engine JVMs
# reached; none named outside a campaign), what the head's held room is
# sized by (campaign_head_need_mb).  Its status is the JVM's.
campaign_engine_jvm() {
  local file=$1 jvm dir peak status=0
  shift
  dir=$(mktemp -d) || return
  "$@" &
  jvm=$!
  campaign_watch_workload "${jvm}" 0 "${dir}"
  wait "${jvm}" || status=$?
  read -r peak 2>/dev/null <"${dir}/workload_rss_mb" || peak=0
  rm -rf -- "${dir}"
  campaign_engine_peak "${file}" "${peak}"
  return "${status}"
}

# campaign_engine_peak <peak_file> <peak_mb>: an engine JVM's peak folded
# into <peak_file>, the largest any of the campaign's reached (none named
# outside a campaign).
campaign_engine_peak() {
  local file=$1 peak=$2 held tmp
  [[ -n "${file}" && "${peak}" =~ ^[0-9]+$ ]] || return 0
  read -r held 2>/dev/null <"${file}" || held=0
  if (( peak > ${held:-0} )); then
    tmp=$(mktemp "${file}.XXXXXX") \
      && printf '%s\n' "${peak}" >"${tmp}" && mv -f -- "${tmp}" "${file}"
  fi
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
# growth step is the door step's main: measured as that.  Unmeasured, GROW's planner started at the 16 GB engine heap, which no lift
# of a busy pool had free: V5-11741's GROW waited 40 min and more for it.
campaign_engine_need_mb() {
  case "$1" in
    *.GraphCheckerMain) echo 4096 ;;
    *.CausynthTraceRecorder|*.ConcolicScheduler|*.ConfirmMain|*.LineageScan \
      |*.ScopeGrowth|*.VerifyWovenClasses|*.ExposedRegionPlanMain) \
      echo 2048 ;;
    *.ExploreMain|*.ComposeMain) echo 8192 ;;
  esac
}

# The room a head reserves on its host, in MB (campaign_head_reserve): its
# measured step need -- the largest peak any of its engine JVMs reached
# (${campaign_root}/engine_peak_mb, campaign_engine_jvm) times 1.25, rounded
# up to 128 MB, at least 1024 and at most the engine heap's JVM footprint
# (campaign_jvm_footprint_mb), read again at every heartbeat; before any was
# measured, the footprint the largest of its engine JVMs that come back every
# round starts at -- a round's planner, a
# witness's composer (engine_java) -- not the case's engine heap, unless one
# of them outgrew its need.  An idle 8 GB hold for steps that peaked at a
# median 0.7 GB (p90 3.7, p99 7.8; 609 planners and composers of sweep HG5A
# and round MCH2) kept 8 GB of every lift from the pool.  A step its held
# room does not cover is placed by its own charge (campaign_head_charged).
campaign_head_need_mb() {
  local main start largest=0 peak heap
  heap=$(campaign_jvm_footprint_mb "${engine_memory_mb:-8192}")
  if [[ -n "${campaign_root}" ]] \
      && read -r peak 2>/dev/null <"${campaign_root}/engine_peak_mb" \
      && [[ "${peak}" =~ ^[1-9][0-9]*$ ]]; then
    largest=$(( (peak * 5 + 511) / 512 * 128 ))
    (( largest >= 1024 )) || largest=1024
    printf '%s\n' "$(( largest < heap ? largest : heap ))"
    return 0
  fi
  for main in edu.uva.liftlab.graphchecker.explore.ExploreMain \
      edu.uva.liftlab.graphchecker.compose.ComposeMain; do
    start=$(campaign_jvm_footprint_mb "$(campaign_engine_start_mb "${main}")")
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
      recording_max_trace_mb schedule_max_jobs region_path_max_waves \
      compose_max_valuations causynth_loop_default_bound reproduce_runs \
      reproduce_time_factor reproduce_min_s campaign_budget_s \
      campaign_reserve_s \
      campaign_max_claims; do
    require_positive_integer "${key}"
  done
  # A budget its reserve takes whole ends the exploration before it begins.
  (( campaign_budget_s > campaign_reserve_s )) \
    || die "campaign_budget_s (${campaign_budget_s}) must exceed its reserve \
campaign_reserve_s (${campaign_reserve_s}): the exploration would end before \
it began"
  # The stages a campaign may be asked to stop after.  Refused here rather
  # than in do_campaign so that `validate` and PREFLIGHT both name it before
  # any work starts: a value this table does not carry would otherwise match
  # nothing, run the whole campaign, and be read back as a measurement run
  # that never stopped.
  case "${campaign_stop_after}" in
    ''|SEED|IMPORT) ;;
    *) die "campaign_stop_after must be empty, SEED or IMPORT: \
${campaign_stop_after}" ;;
  esac
  [[ "${causynth_scope_growth_budget}" =~ ^[0-9]+$ ]] \
    || die "causynth_scope_growth_budget must be a non-negative integer: \
${causynth_scope_growth_budget}"
  [[ "${stream_shared_pool}" == true || "${stream_shared_pool}" == false ]] \
    || die "stream_shared_pool must be true or false: ${stream_shared_pool}"
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
  require_directory "project classes" "${project_classes_dir}"
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
  system_properties+=("-Dcausynth.io.doors=$(campaign_io_doors)")
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
  # The pass's JVM runs on GraphChecker's jar alone: Soot reads the analysed
  # classpath (-x) itself, and no class of the case is loaded into the JVM.
  run_in_directory "${graphchecker_work_dir}" engine_java \
    "${system_properties[@]}" \
    -cp "${graphchecker_jar}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${project_classes_dir}" \
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

# The demanded doors the static pass chose (causynth.DemandedDoors, a local
# file operation on the traced flow, SYMBOL-SCOPE §4.6): every pass weaves
# them before any analysis (do_analyze).
campaign_io_doors() {
  printf '%s\n' "${causynth_output_dir}/io_doors.jsonl"
}

# The static pass, with the scope grown where the slice stops at it until
# nothing is added or the budget is spent (SYMBOL-SCOPE §2.4).  First, and
# after every growth, outside the budget, the classes of the library doors
# the analysis scope calls (campaign_scope_doors).  A pass that chose more
# demanded doors runs again over them, outside the budget too: a door moves
# the unit indices of its method, so the scope map is the woven body's.
campaign_analyze_grown_scope() {
  local grown changes summary doors=0 chosen
  grown=$(campaign_grown_scope)
  local -a roots=()
  rm -rf -- "${grown}"
  rm -f -- "$(campaign_io_doors)"
  mkdir -p "${grown}"
  IFS=: read -r -a roots <<<"${causynth_lineage_roots}"
  (( ${#roots[@]} == 0 )) || campaign_scope_doors "${grown}" "${roots[@]}"
  while :; do
    campaign_analyze SEED "${causynth_output_dir}/static-pass.log"
    chosen=$(grep -c . "$(campaign_io_doors)" 2>/dev/null || true)
    if (( ${chosen:-0} > doors )); then
      doors=${chosen}
      campaign_log "demanded doors: ${doors} chosen; the static pass runs \
again over them"
      continue
    fi
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

# run_configured_workload <trace-dir> [seconds] [plant] [charged_mb]
# [max_trace_mb] [order_timeout_ms]: the
# workload in the recording weave (analysis_classes_dir, as SEED's static
# pass wove it), its trace into <trace-dir> and no more than <max_trace_mb>
# of it (the recording's, campaign_watch_workload), under a wall-clock bound of
# <seconds> when one is given (run_under_wall_clock_bound), with a native
# reproduction's plant (runtime.RecordingPlant) when one is named, its ORDER
# rows each held at most <order_timeout_ms> (runtime.Confirmation), and held
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
    "CAUSYNTH_RECORDING_MAX_TRACE_MB=${5:-0}"
    "CAUSYNTH_ORDER_TIMEOUT_MS=${6:-}"
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
  run_configured_workload "${trace_dir}" "" "" "" "${recording_max_trace_mb}" \
    || status=$?
  campaign_recorded_workload_s=$(( SECONDS - started ))
  local ended=""
  ended=$(cat "${trace_dir}/${campaign_recording_end_marker}" 2>/dev/null) \
    || ended=""
  [[ -z "${ended}" ]] \
    || campaign_fail SEED "${ended%%:*}" "${trace_dir}" "${ended}"
  (( status == 0 )) || campaign_fail SEED WORKLOAD "${trace_dir}" \
    "the recorded workload exited ${status}: the test failed, or its run" \
    "never opened a recording window (its output is above)"
  campaign_recorded_workload_rss_mb=$(cat "${trace_dir}/workload_rss_mb" \
    2>/dev/null) || campaign_recorded_workload_rss_mb=""
  require_file "static scope map" "${causynth_static_scope_map}"
  local -a declared=()
  [[ -z "${declared_target_occurrence}" ]] \
    || declared=(--target-occurrence "${declared_target_occurrence}")
  # The spec's one target (the static pass refuses more,
  # causynth.CausynthTargetResolver), aggregated on SEED's slice into the
  # trace directory.
  local name
  name=$(awk '$1 == "exception_target:" {print $2; exit}' \
    "${causynth_target_spec}")
  run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" --test "${trace_test}" "${declared[@]}" \
    --target "${name}=${candidate_graph},${causynth_static_scope_map},\
${causynth_region_skeletons},${trace_dir}"
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
# trace directory) -- do_workload: the seed replay's
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
      | IN("SAT_CANDIDATE", "UNSAT_CLOSED", "RUN_DEFECT"))
    and ($r.campaignClaim.blockers | type) == "array"
    and ($r.campaignClaim.blockerCount | type) == "number"
    and ($r.campaignClaim.claimReason | type) == "string"
    and ($r.campaignClaim.whyNotAccepted | type) == "string"
    and (($r.campaignClaim.findingKind // "")
      | IN("MARKER_FLIPPED", "CLOCK_SKEW", "MESSAGE_PAIRING_FLIPPED",
           "STATE_PAIRING_FLIPPED", "FORMULA_SAT",
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
            # A file gone before it is hashed is no part of the state (a
            # JVM attach's .attach_pid<pid> in a workload's directory,
            # round HG5A hdfs-adhoc-33); one still there that cannot be
            # read fails the digest.
            { find "${repo}/${entry}" -type f -print0 2>/dev/null || :; } \
              | LC_ALL=C sort -z | while IFS= read -r -d '' file; do
                  sha256sum -- "${file}" 2>/dev/null \
                    || [[ ! -e "${file}" ]] || exit 1
                done || exit 1
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
  campaign_log "replay scratch: ${campaign_local_scratch_root}"
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
# campaign_obligation_replay (replay_timeout_s) and campaign_session_replay
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
# A peer is handed its head's root (CAUSYNTH_LOCAL_SCRATCH).
campaign_local_scratch_root=""

campaign_init_local_scratch_root() {
  local run_key
  if [[ -n "${CAUSYNTH_LOCAL_SCRATCH:-}" ]]; then
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
# A remote SOLVE (--run-obligation) answers to its solver's
# `solver_timeout_ms`; its host's solver takes one question at a time, so a
# question may first wait behind the ones it took, for as long as a replay
# may run (`replay_timeout_s`, the pool's turnover).  This outer bound is a
# backstop against a remote side that is wedged somewhere else (a hung ssh
# channel, an NFS mount that stopped answering): the sum of the two, plus
# this margin for JVM start-up and the shared home.  It is not a policy
# about obligations; one that reaches it has hit something no declared
# budget describes, and it is answered as unfinished, naming the host
# (campaign_obligation_unfinished).  A REPLAY is a placed step, under
# `replay_timeout_s` inside it (campaign_obligation_replay).
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

# campaign_await_visible <file>...: the files a head step that may have
# been placed on a peer wrote, visible here before the head reads them: a
# file not visible yet has its directory re-listed each second (a negative
# lookup the head cached -- the head itself checked the name was free
# before the step -- hides a file the peer created until the directory's
# attribute cache expires), bounded by campaign_remote_visibility_wait_s.
# A visible file costs nothing; what never shows is the caller's to refuse.
# (The engine JVM's placement is made in a subshell, run_in_directory, so
# its caller cannot tell where it ran.)
campaign_await_visible() {
  local file waited=0
  for file in "$@"; do
    while [[ ! -s "${file}" ]] \
        && (( waited < campaign_remote_visibility_wait_s )); do
      ls "$(dirname "${file}")" >/dev/null 2>&1 || true
      sleep 1
      waited=$((waited + 1))
    done
  done
}

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
    for assignment in "${gc_env_names[@]}"; do
      printf '    %s=%q \\\n' "${assignment}" "${!assignment}"
    done
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

# The peer's evidence, visible HERE: <worker>'s result and the session it
# names under <staged>, the directory the job staged its sessions to.
#
# Bounded, never assumed: see campaign_remote_visibility_wait_s.  The
# directory is re-listed on each turn because it is the directory's cached
# listing, not the file's contents, that a fresh lookup has to get past.
campaign_await_remote_result() {
  local worker=$1 host=$2 obligation_id=$3 staged=$4
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
  local catalog_sha plan_sha
  : >"${marker}"
  campaign_analyze_grown_scope
  do_workload
  require_fresh "static candidate data-flow graph" "${candidate_graph}" \
    "${marker}"
  require_fresh "runtime region plan" "${runtime_region_plan}" "${marker}"
  # The seed's static catalog and runtime region plan are digested into the
  # campaign's provenance, and both seed skeleton views snapshot inside the
  # campaign.  The configured analysis and runtime roots are already
  # generation-local; the snapshot keeps the exact static/runtime pair beside
  # the final provenance.
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
  # A refusal of the scheduler's (DECLARED_TARGET_OCCURRENCE_MISSING, ...)
  # ends the stage by name, as any stage's throwable does.
  local plan_log="${iteration_dir}/plan.log"
  run_capturing_status do_schedule 2>"${plan_log}"
  cat -- "${plan_log}" >&2
  (( status == 0 )) || campaign_fail PLAN ConcolicScheduler "${plan_log}" \
    "the scheduler failed with exit ${status}: $(campaign_thrown "${plan_log}")"
  # The declared occurrence as the seed's aggregation resolved it against the
  # recording -- a declared "first", a selector's k-th match, an address
  # itself (RuntimeWorkflowDiscovery#declaredOccurrence) -- marked on its plan
  # row and stated by the index, so no later stage counts a selector's k
  # again over activations the question left out.
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
  runtime_region_plan="${frozen}"
  # The one task-set membership decode: the index is frozen beside its rows
  # and every later stage reads the rows.
  if ! campaign_member_rows=$(campaign_decode_index_members "${index}"); then
    campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index has an invalid membership schema"
  fi
  [[ -n "${campaign_member_rows}" ]] || campaign_fail PLAN ConcolicScheduler \
    "${index}" "the region-path schedule index names no target member"
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
# model the workload never realized, and campaign_obligation_replay already records
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
    "CAUSYNTH_HEAP_BASIS_MB=${campaign_replay_heap_basis_mb:-${charged}}" \
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
    "CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root}/$(basename \
      "${worker}")" \
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
# <scope-map> (its method's), or "" when none did.
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

# REPLAY: the seed replay, placed where there is room (campaign_head_charged:
# it reads and writes only the iteration), under a wall clock derived from
# the recording (seed_replay_time_factor): the seed is the iteration's only
# source of observed cases, so a replay past it is a campaign failure at
# REPLAY, named, not a recorded verdict.  No replay of the campaign has been
# measured yet, so its need is the recording's own measured peak
# (workload_rss_mb, what a native run of it is charged, REPRODUCE) times
# campaign_replay_memory_factor: a concolic replay outgrows its native
# recording, and round x1's eleven seed replays peaked at 0.65 to 6.94 times
# it (hdfs-17960 4.89, solr-18413 3.65, solr-18406 6.94; the block-key cases
# under 1.2).  Its peak is the campaign's first measured replay need
# (campaign_replay_measured): every replay after it is charged from what the
# campaign's replays measured, never from the recording again.  That need
# sizes the replay's heap; the seed replay is CHARGED less at its start,
# campaign_seed_charge_factor times the recording's peak, and granted what it
# grows past that while its host has real room (campaign_watch_workload), as
# every replay is: HDFS seed replays peaked at 0.5 to 1.4 times their
# recording (rounds HG9, HI2: 177-1062 MB charged 2.6-11 GB), and charged
# seven times it, four of HI2's first wave held 44 GB of the cluster's
# ledger over under 4 GB of real use while every lift's real use stood at
# 20-36 %.
campaign_replay_memory_factor=7
campaign_seed_charge_factor=2
campaign_session_replay() {
  local iteration_dir=$1 bound need charge
  [[ "${campaign_recorded_workload_rss_mb}" =~ ^[1-9][0-9]*$ ]] \
    || campaign_fail REPLAY WORKLOAD "${iteration_dir}" "the recording \
measured no peak resident memory (workload_rss_mb) to charge the seed replay \
with"
  bound=$(( seed_replay_time_factor * campaign_recorded_workload_s ))
  (( bound >= replay_timeout_s )) || bound=${replay_timeout_s}
  need=$(( campaign_recorded_workload_rss_mb * campaign_replay_memory_factor ))
  charge=$(( campaign_recorded_workload_rss_mb * campaign_seed_charge_factor ))
  (( charge >= campaign_replay_min_need_mb )) \
    || charge=${campaign_replay_min_need_mb}
  charge=$(campaign_replay_charge_mb "${charge}")
  campaign_head_charged "${charge}" campaign_seed_replay "${iteration_dir}" \
    "${causynth_static_scope_map}" "${charge}" "${bound}" \
    "seed_replay_time_factor=${seed_replay_time_factor} x the recording's \
${campaign_recorded_workload_s}s workload and at least \
replay_timeout_s=${replay_timeout_s}" "${need}"
  campaign_replay_measured "${iteration_dir}/seed-result/focused"
  (( campaign_replay_peak_mb > 0 )) || campaign_fail REPLAY WORKLOAD \
    "${iteration_dir}/seed-result/focused" "the seed replay stated no peak \
resident memory (workload_rss_mb): no replay after it has a measured need"
}

# The largest resident peak, in MB, a replay of this campaign has stated so
# far (campaign_replay_measured): the seed replay's, then every obligation's,
# GROW re-run's and CONFIRM replay's that returned.  0 before the seed's.
campaign_replay_peak_mb=0
# The least measured need, in MB.
campaign_replay_min_need_mb=512
# The resident peaks of the replays after the seed's (an obligation's, a GROW
# re-run's, a CONFIRM's) as they returned, and what a replay of the stream
# is charged at its start once enough of them did (campaign_replay_typical).
campaign_replay_peaks=()
campaign_replay_typical_mb=0
# How many replays after the seed's must have returned before the stream
# charges the typical replay instead of the largest.
campaign_replay_typical_after=8

# The memory, in MB, one replay of this campaign needs once one was measured
# -- an obligation's, a GROW re-run's, a CONFIRM's: the largest peak its
# replays stated so far times 1.5, rounded up to 128 MB, at least
# campaign_replay_min_need_mb.  An obligation replay peaks near its own seed
# replay (round HG4, seed / obligations, MB: hdfs-11741 674 / 662-715,
# hdfs-17897 552 / 540-555, hdfs-17899-bug1 548 / 548-550, hdfs-adhoc-07
# 238 / 134-257), while the static 2500 MB per obligation and seven times
# the recording per CONFIRM replay held the lifts' ledger at 11-22 GB over
# 3-7 GB of real use (sweep HG5A): adhoc-07's 151 replays of ~93 s waited a
# median 35 min for a slot.  One that outgrows the need grows its charge
# while its host has real room (campaign_watch_workload) and raises the
# need of every start after it (hdfs-adhoc-15: seed 514, obligations
# 939-2003).  The need sizes the replay JVM's heap (CAUSYNTH_HEAP_BASIS_MB,
# execute.sh); the charge it starts with is campaign_replay_charge_mb's.
campaign_replay_need_mb() {
  campaign_need_of_peak_mb "${campaign_replay_peak_mb}"
}

# The need, in MB, of a JVM whose measured resident peak was <peak_mb>: the
# peak times 1.5, rounded up to 128 MB, at least campaign_replay_min_need_mb
# -- a replay's (campaign_replay_need_mb), and a solver's asked again after
# one died (campaign_obligation_worker).
campaign_need_of_peak_mb() {
  local need=$(( ($1 * 3 + 255) / 256 * 128 ))
  (( need >= campaign_replay_min_need_mb )) \
    || need=${campaign_replay_min_need_mb}
  printf '%s\n' "${need}"
}

# campaign_replay_measured <worker_dir>: the resident peak the replay of
# <worker_dir> stated (workload_rss_mb, experiments/lib/execute.sh), taken
# into the measured need (campaign_replay_need_mb), said when the need moves.
# A worker whose replay never ran states none and adds nothing.
campaign_replay_measured() {
  local peak first=$(( campaign_replay_peak_mb == 0 )) before
  read -r peak 2>/dev/null <"$1/workload_rss_mb" || return 0
  [[ "${peak}" =~ ^[0-9]+$ ]] || return 0
  (( first )) || campaign_replay_typical "${peak}"
  (( peak > campaign_replay_peak_mb )) || return 0
  before=$(campaign_replay_need_mb)
  campaign_replay_peak_mb=${peak}
  (( first )) || [[ "$(campaign_replay_need_mb)" != "${before}" ]] || return 0
  campaign_log "a replay peaked at ${peak} MB (${1}): every replay from now \
on needs $(campaign_replay_need_mb) MB and is charged \
$(campaign_replay_charge_mb "$(campaign_replay_need_mb)") MB"
}

# campaign_replay_typical <peak_mb>: one more replay after the seed's
# returned at <peak_mb>.  Once campaign_replay_typical_after of them have,
# the stream charges a replay at their 90th percentile times 1.25, rounded up
# to 128 MB, at least campaign_replay_min_need_mb and at most the need
# (campaign_stream_charge_mb), while its heap stays sized by the need: one
# replay that outgrows its charge grows it while its host has real room
# (campaign_watch_workload).  Charged at the largest peak times 1.5, the
# lifts' ledgers held 21-22 GB over 8-11 GB of real use and no host admitted
# one more start (solr-adhoc-21 RX4: peaks p50 918, p90 1242, max 2234 MB,
# each replay charged 3456 MB; solr-adhoc-40 LD1: p50 1583, max 3454 MB, the
# seed's).  Said when it moves.
campaign_replay_typical() {
  local p90 typical
  campaign_replay_peaks+=("$1")
  (( ${#campaign_replay_peaks[@]} >= campaign_replay_typical_after )) \
    || return 0
  p90=$(printf '%s\n' "${campaign_replay_peaks[@]}" | LC_ALL=C sort -n \
    | awk '{ peak[NR] = $1 } END { i = int(NR * 0.9); if (i < NR) i++;
             print peak[i] }')
  typical=$(( (p90 * 5 + 511) / 512 * 128 ))
  (( typical >= campaign_replay_min_need_mb )) \
    || typical=${campaign_replay_min_need_mb}
  (( typical != campaign_replay_typical_mb )) || return 0
  campaign_replay_typical_mb=${typical}
  campaign_log "the replays after the seed's peaked at ${p90} MB or less \
in 9 of 10 (${#campaign_replay_peaks[@]} returned): a replay of the stream is \
charged $(campaign_stream_charge_mb REPLAY) MB at its start"
}

# campaign_replay_charge_mb <need>: what a replay of that need is charged at
# its start: the need, at most half a host's ceiling.  A charge only an idle
# host can hold waits for one forever on a shared cluster (round HG1: four
# HDFS seed replays charged 20.6 GB, seven times a 2.9 GB recording, waited
# 75 minutes for a host under 22 GB); what the replay grows past it the
# ledger grants while its host has real room (campaign_watch_workload).
campaign_replay_charge_mb() {
  local need=$1 cap
  cap=$(( $(awk '/^MemTotal:/ {print int($2 / 1024)}' /proc/meminfo) \
    * campaign_host_max_used_pct / 200 ))
  printf '%s\n' "$(( need < cap ? need : cap ))"
}

# campaign_seed_replay <iteration_dir> <scope_map> <charged_mb> <bound_s>
# <rule> <need_mb>: the seed replay itself, on whichever host its charge placed it
# (run_engine.sh --run-placed).  What it reads of its head is in its
# arguments -- its scope map, and the bound <rule> states -- or in the run's
# configuration.
campaign_seed_replay() {
  local iteration_dir=$1 causynth_static_scope_map=$2 charged=$3 bound=$4
  local rule=$5 need=${6:-$3}
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
    campaign_replay_heap_basis_mb="${need}" \
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
# (explore.Service states the layout); its log, solver-<host>.log, is
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
# charge is a solver's start (campaign_solver_start_mb); its replay is a
# start of its own, charged then (campaign_stream_ended).
# ---------------------------------------------------------------------------

# How long a host's solver waits for another question before it ends: about
# a focused replay's length, so the obligations a host runs next find it
# still there, and a host the pool has left gives its memory back within
# minutes.
campaign_solver_idle_s=300

# A solver's heap, in MB, for the corpus <sessions> (the host's solver and a
# question's own JVM alike): campaign_solver_start_heap_mb until a solver of
# it ran out of heap (-XX:+ExitOnOutOfMemoryError, exit 3), then the heap it
# outgrew doubled, up to the case's engine heap (engine_memory_mb), as
# engine_java grows an engine JVM; stated beside the corpus (solver_heap_mb)
# for every host.  Its live set is the corpus it reads and the query it
# lowers: 0.2 GB over hdfs-17897's three sessions, 5 GB over hdfs-11741 i1's
# 175, 0.85 GB after a full collection in a solr-adhoc-10 host solver
# (SL1-10, 2026-10-12) that the parallel collector had let grow to 6.2 GB
# resident, and others of it to 10.6-12.5 GB, at a 16 GB heap: one per host
# and campaign, they filled every lift's ledger.  A fixed 8 GB was outgrown
# once a closure doubled (hdfs-adhoc-07 EX1, ~1500 sessions: an hour of
# garbage collection with 24 questions queued, then OutOfMemoryError), which
# the doubling meets.
campaign_solver_start_heap_mb=2048

campaign_solver_heap_mb() {
  local engine=${engine_memory_mb:-8192} heap=${campaign_solver_start_heap_mb}
  local stated="$(dirname "${1:-.}")/solver_heap_mb"
  [[ ! -s "${stated}" ]] || heap=$(<"${stated}")
  (( heap <= engine )) || heap=${engine}
  printf '%s\n' "${heap}"
}

# campaign_solver_outgrown <sessions> <heap_mb>: a solver of the corpus ran
# out of its <heap_mb> heap; every later one starts at twice it, up to the
# engine heap, never below what another solver already outgrew.
campaign_solver_outgrown() {
  local stated="$(dirname "$1")/solver_heap_mb" next=$(( 2 * $2 ))
  (( next <= ${engine_memory_mb:-8192} )) || next=${engine_memory_mb:-8192}
  (( next > $(campaign_solver_heap_mb "$1") )) || return 0
  printf '%s\n' "${next}" >"${stated}.$$" && mv -f -- "${stated}.$$" "${stated}"
}

# What a solver JVM of the corpus <sessions> is charged, in MB: its heap's
# footprint (campaign_jvm_footprint_mb), the host's solver at its start and a
# question's own JVM alike; what it grows past that is charged as it grows
# (campaign_solver_jvm).  Charged its 8 GB heap at its start, a solver waited
# minutes for room it did not use (e2: "one needs 8192 MB and 9474 MB stay
# free"); charged 1 GB while its heap was 16 GB, a host solver's growth filled
# the ledger and a question's own JVM charged a question's 512 MB was ended at
# its first growth on a full host (SL1-10).
campaign_solver_need_mb() {
  campaign_jvm_footprint_mb "$(campaign_solver_heap_mb "${1:-}")"
}

# A solver's start on a corpus no solver outgrew, in MB (what the stream
# charges a solve on a cold host, campaign_stream_charge_mb).
campaign_solver_start_mb=$(campaign_jvm_footprint_mb \
  "${campaign_solver_start_heap_mb}")

# What a question its host's serving solver answers is charged, in MB: its z3
# run, a child of that solver (the solver JVM's own charge is its JVM's).
# Charged a solver's start, a sweep's questions held 51 GB of the ten lifts'
# ledger over z3 runs of a median 1 MB, p90 369 MB, at most 1.8 GB (118 z3
# processes, HI1/HI2), and new campaigns waited for room their lifts had.
campaign_question_mb=512

# THE SOLVE'S TWO LANES.  A question is first asked at campaign_solver_first_ms
# (campaign_solver_first_tier_ms, never past solver_timeout_ms): a host's
# solver answers one question at a time, and one that runs its z3 to the
# full budget held every question of its host behind it (SP4-10, 2026-10-12:
# 12 READ-door and routed-alias flips ran their z3 races 1000-1180 s of
# 1810 s while 292 questions waited and the answered ones took a median 1 s,
# p90 4 s).  One undecided then is no answer yet: its obligation leaves the
# solve queue for the hard lane (campaign_stream_ended), asked again at the
# full budget in a solver JVM of its own once no other start waits
# (campaign_stream_dispatch), still in flight meanwhile, so no fixed point is
# declared before it; undecided at the full budget, it lands NOT_ADMITTED and
# is a named SOLVER_TIMEOUT (campaign_solver_timeouts, a RUN_DEFECT under any
# claim but a SAT_CANDIDATE).
campaign_solver_first_tier_ms=60000

campaign_solver_first_ms() {
  local first=${campaign_solver_first_tier_ms}
  (( solver_timeout_ms <= 0 || first < solver_timeout_ms )) \
    || first=${solver_timeout_ms}
  printf '%s\n' "${first}"
}

# Whether the first ask is shorter than the full budget, so an undecided one
# is owed its hard-lane ask.
campaign_solver_two_lanes() {
  (( $(campaign_solver_first_ms) < solver_timeout_ms ))
}

# How long a question waits behind its host's busy solver before it is
# withdrawn from its queue and answered in a solver JVM of its own, in
# seconds: one long question never holds the others of its host.
campaign_solver_busy_patience_s=30

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
# when the host had no room to start its solver now, 5 when its solver still
# had not taken it after campaign_solver_busy_patience_s (withdrawn from its
# queue: the solver can no longer take it) -- either way the question is
# then its own JVM's (campaign_obligation_worker).
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
      # Busy past its patience: withdrawn unless the solver took it first
      # (Service takes a question by the same atomic rename).
      if (( SECONDS - waited >= campaign_solver_busy_patience_s )) \
          && [[ ! -e "${answer}" ]] \
          && mv -- "${question}.json" "${question}.withdrawn" 2>/dev/null; then
        rm -f -- "${question}.withdrawn"
        return 5
      fi
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
# room for its start (campaign_solver_need_mb) now, and names it in
# <dir>/server: the pid of the shell that runs the JVM, which ends with it.
# Returns without waiting for it; 1, starting nothing, when the host has no
# room now or its memory cannot be read: a start that waited for memory held
# every question of its corpus behind it.  The root domains are the
# declaration EXPLORE and COMPOSE read: an answer is only as free as the
# root domains behind the arm that produces it.
campaign_start_solver() {
  local dir=$1 sessions=$2 charge status=0 heap need
  heap=$(campaign_solver_heap_mb "${sessions}")
  need=$(campaign_jvm_footprint_mb "${heap}")
  campaign_host_try_charge localhost "${need}"
  (( status == 0 )) || return 1
  charge=${campaign_host_charge_id}
  {
    # The solver outlives the obligation that started it: it holds its
    # charge itself.
    campaign_host_keep localhost "${charge}"
    status=0
    campaign_solver_jvm "${heap}" "${need}" "$(campaign_solver_first_ms)" \
      --serve "${dir}" \
      --sessions "${sessions}" \
      --idle-seconds "${campaign_solver_idle_s}" \
      </dev/null >>"$(campaign_solver_log "${sessions}")" 2>&1 || status=$?
    (( status != campaign_jvm_out_of_heap_status )) \
      || campaign_solver_outgrown "${sessions}" "${heap}"
    campaign_host_release localhost "${charge}"
  } &
  printf '%s\n' "$!" >"${dir}/server.part"
  mv -f -- "${dir}/server.part" "${dir}/server"
}

# campaign_solver_jvm <heap_mb> <charged_mb> <budget_ms> <ObligationSolverMain
# args...>: one solver JVM at <heap_mb>, each z3 run under <budget_ms>, ended
# at its first out-of-heap error (exit 3) (run_java_main's, started here so its pid is
# the JVM's own: java_bin execs java), watched until it ends
# (campaign_watch_workload): what it grows past the <charged_mb> its host
# holds for it is asked of the host as it grows, and a host whose real use
# cannot take it ends it.  Its status.
campaign_solver_jvm() {
  local heap=$1 charged=$2 budget=$3 jvm status=0
  shift 3
  require_file "GraphChecker jar" "${graphchecker_jar}"
  (cd "${graphchecker_work_dir}" \
    && exec env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
      "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
      "-Dcausynth.system.doors=${causynth_system_doors}" \
      -cp "${graphchecker_jar}" \
      -XX:+ExitOnOutOfMemoryError \
      edu.uva.liftlab.graphchecker.explore.ObligationSolverMain \
      --z3 "${z3_bin}" \
      --solver-timeout-ms "${budget}" \
      ${causynth_root_domains:+--root-domains "${causynth_root_domains}"} \
      "$@") &
  jvm=$!
  campaign_watch_workload "${jvm}" "${charged}"
  wait "${jvm}" || status=$?
  return "${status}"
}

# campaign_solve_obligation_alone <obligation_id> <obligations> <sessions>
# <worker> <charged_mb> <budget_ms>: the question in a solver JVM of its own
# at its corpus's solver heap (campaign_solver_heap_mb; out of it, exit 3, the
# next one doubles), its z3 runs under <budget_ms> (its lane's), its
# files straight into <worker>, its status the JVM's,
# on this host under a charge of <charged_mb> its caller holds here: the
# obligation's own (a solver's start) for a question whose host had no room
# for its solver, or the one campaign_solve_obligation_placed took.  What
# the JVM grows past it is asked of the host as it grows
# (campaign_watch_workload).
campaign_solve_obligation_alone() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 charged=$5
  local budget=$6 status=0 heap
  heap=$(campaign_solver_heap_mb "${sessions}")
  run_capturing_status campaign_solver_jvm "${heap}" \
    "${charged}" "${budget}" \
    --obligations "${obligations}" \
    --obligation-id "${obligation_id}" \
    --sessions "${sessions}" \
    --output-dir "${worker}"
  (( status != campaign_jvm_out_of_heap_status )) \
    || campaign_solver_outgrown "${sessions}" "${heap}"
  return "${status}"
}

# How long a solver asked again waits for a host of the pool with room for
# its need (campaign_solve_obligation_placed) before its obligation fails by
# name: minutes, while the pool's replays end and give their room back, never
# the worker's whole bound (hdfs-adhoc-11 CW4b/CW5: workers waited 3900 s for
# 16384 MB on the one host they ran on, and were killed unanswered; 60 s left
# hdfs-adhoc-07 HF3 five obligations unanswered beside ~120 replays).
campaign_solver_place_patience_s=600

# campaign_solve_obligation_placed <obligation_id> <obligations> <sessions>
# <worker> <need_mb> <budget_ms>: a question asked again of a solver of its
# own at its lane's budget, placed
# as any start is: on the pool's host with the most room for <need_mb>
# (campaign_host_room), charged there while it runs -- this host or a peer
# (--run-placed, from a directory under <worker>).  4, with why in
# campaign_host_wait_reason, when no host has the room within
# campaign_solver_place_patience_s; else the JVM's status.
campaign_solve_obligation_placed() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 need=$5
  local budget=$6
  local host room best best_room since=${SECONDS} charge status=0
  while true; do
    best=""
    best_room=-1
    while IFS= read -r host; do
      room=$(campaign_host_room "${host}") || continue
      (( room >= need && room > best_room )) || continue
      best=${host}
      best_room=${room}
    done < <(campaign_worker_host_list)
    if [[ -n "${best}" ]]; then
      campaign_host_try_charge "${best}" "${need}"
      (( status != 0 )) || break
    else
      campaign_host_wait_reason="no host of the pool has ${need} MB of room"
    fi
    (( SECONDS - since < campaign_solver_place_patience_s )) || return 4
    sleep "${campaign_host_poll_s}"
  done
  charge=${campaign_host_charge_id}
  status=0
  if campaign_host_is_local "${best}"; then
    run_capturing_status campaign_solve_obligation_alone "${obligation_id}" \
      "${obligations}" "${sessions}" "${worker}" "${need}" "${budget}"
  else
    # Its placed directory under the worker: a peer has no campaign root.
    local campaign_root=${worker}
    run_capturing_status campaign_run_placed "${best}" \
      campaign_solve_obligation_alone "${obligation_id}" "${obligations}" \
      "${sessions}" "${worker}" "${need}" "${budget}" >&2
  fi
  campaign_host_release "${best}" "${charge}"
  return "${status}"
}

# One obligation SOLVED: its question answered into <worker>, the one
# ObligationResult row that says which verdict it reached.
#
# The obligation names ONE focused occurrence, the decision it flips, the root
# assignments to apply at the mints and the answers to apply at the attaches
# (CONTRACT-SPEC §3).  The solver reads the corpus <sessions>.  UNSAT,
# NOT_ADMITTED and a reused ADMITTED are the obligation's answer, which the
# head lands (campaign_stream_land); SAT_MODEL_READY leaves the model's focus
# row in <worker>, and the head queues the obligation's REPLAY
# (campaign_obligation_replay, a start of its own charged the replay's need,
# campaign_stream_ended), so no solve holds a replay's charge.
#
# A single obligation that could not be solved is that obligation's own
# result row, never the campaign's death.  <charged_mb> is what its start
# charged its host: what a solver JVM starts at (campaign_solver_start_mb),
# under which its question is answered at once when its host has no room for
# its solver.  <lane>: empty, the first ask (its host's solver, at the first
# budget); HARD, the full budget in a solver JVM of its own, for a question
# the first ask left undecided (campaign_solver_first_tier_ms).
campaign_obligation_worker() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 charged=$5
  local lane=${6:-} budget outcome status=0 peak need="" held="" measured=0
  # Its start charged the host <charged_mb>: a local one is a subshell of the
  # head, and its JVMs are not the head's; the host's solver charges its own.
  local campaign_head_charging=0
  campaign_watch_peak_mb=0
  local result_row="${worker}/obligation_result.jsonl"
  budget=$(campaign_solver_first_ms)
  if [[ "${lane}" == HARD ]]; then
    budget=${solver_timeout_ms}
    status=4
  else
    run_capturing_status campaign_solve_obligation "${obligation_id}" \
      "${obligations}" "${sessions}" "${worker}"
  fi
  case "${status}" in
    3) campaign_log "obligation ${obligation_id}: no room on $(hostname -s) \
to start its solver now; answered in a solver JVM of its own" ;;
    4) campaign_log "obligation ${obligation_id}: undecided in \
$(campaign_solver_first_ms) ms; asked at the full ${budget} ms in a solver \
JVM of its own" ;;
    5) campaign_log "obligation ${obligation_id}: its host's solver was busy \
past ${campaign_solver_busy_patience_s}s; answered in a solver JVM of its own" ;;
  esac
  if [[ "${status}" -ge 3 ]]; then
    # Answered in its own JVM at once, not after a start that waits for
    # memory nor behind a question its host's solver is busy with: here
    # under this start's charge when it covers that JVM's need, else placed
    # as any start by that need (a question's charge, 512 MB, on a warm host).
    need=$(campaign_solver_need_mb "${sessions}")
    if (( charged >= need )); then
      run_capturing_status campaign_solve_obligation_alone "${obligation_id}" \
        "${obligations}" "${sessions}" "${worker}" "${charged}" "${budget}"
    else
      run_capturing_status campaign_solve_obligation_placed \
        "${obligation_id}" "${obligations}" "${sessions}" "${worker}" \
        "${need}" "${budget}"
      (( status != 4 )) || die "obligation ${obligation_id}: no host has \
room for a solver of its own of ${need} MB within \
${campaign_solver_place_patience_s}s: ${campaign_host_wait_reason}"
    fi
  fi
  if [[ "${status}" -ne 0 ]]; then
    # A solver that ran out of heap, died, or was ended at what its host
    # could hold answered nothing about the obligation, and settles no
    # question, whatever it left: asked once more, of a solver of its own at
    # its corpus's solver heap (doubled if one ran out of it), placed as any
    # start by that JVM's footprint, or by what the first one measurably held
    # (its watched peak) with the usual margin (campaign_need_of_peak_mb)
    # where that is more -- never by what other solvers held (SL1-10: a
    # question that held 1.2 GB asked 12.5 GB, the largest host solver's
    # peak, and no host had it) -- at most the footprint of the engine heap,
    # on any host with that room (campaign_solve_obligation_placed); one that
    # runs out of heap again is asked again at the doubled heap, up to the
    # engine heap, as engine_java grows an engine JVM (SL2-10: questions of
    # the routed-alias content outgrew 2, 4 and 8 GB, and a single retry left
    # 11 of them unfinished).  Failed otherwise, or no host with the room: the
    # worker did not finish (campaign_obligation_unfinished), by name, never
    # an answer.
    rm -f -- "${worker}/question.txt" "${worker}/question.asked"
    peak=${campaign_watch_peak_mb}
    need=$(campaign_solver_need_mb "${sessions}")
    (( peak <= 0 || $(campaign_need_of_peak_mb "${peak}") <= need )) \
      || need=$(campaign_need_of_peak_mb "${peak}")
    measured=$(campaign_jvm_footprint_mb "${engine_memory_mb:-8192}")
    (( need <= measured )) || need=${measured}
    held="held ${peak} MB"
    (( peak > 0 )) || held="ran in its host's solver, unwatched"
    campaign_log "obligation ${obligation_id}: its solver did not answer \
($(grep -v -E '^[[:space:]]+at ' "${worker}/stderr.log" 2>/dev/null \
      | tail -n 1)); asked again of a solver of its own, ${need} MB for a \
first that ${held}, on any host with the room"
    run_capturing_status campaign_solve_obligation_placed "${obligation_id}" \
      "${obligations}" "${sessions}" "${worker}" "${need}" "${budget}"
    while (( status == campaign_jvm_out_of_heap_status )) \
        && (( need < measured )); do
      need=$(campaign_solver_need_mb "${sessions}")
      campaign_log "obligation ${obligation_id}: its solver of its own ran \
out of heap; asked again at $(campaign_solver_heap_mb "${sessions}") MB \
(${need} MB)"
      run_capturing_status campaign_solve_obligation_placed \
        "${obligation_id}" "${obligations}" "${sessions}" "${worker}" \
        "${need}" "${budget}"
    done
    if [[ "${status}" -eq 4 ]]; then
      die "obligation ${obligation_id}: its solver did not answer, and no \
host has room for a solver of its own of ${need} MB (the first \
${held}) within ${campaign_solver_place_patience_s}s: \
${campaign_host_wait_reason}"
    elif [[ "${status}" -ne 0 ]]; then
      rm -f -- "${worker}/question.txt" "${worker}/question.asked"
      die "obligation ${obligation_id}: its solver failed twice, its \
host's and one of its own of ${need} MB: $(grep -v -E \
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
  # (ObligationFactory#solve).  SAT_MODEL_READY is owed its replay.
  case "${outcome}" in
    UNSAT|NOT_ADMITTED|ADMITTED|SAT_MODEL_READY) ;;
    *) die "the obligation verdict is not solver-backed: ${outcome}" ;;
  esac
}

# The replay half of an obligation: the solver's model, run focused, and the
# verdict the replay states for it, its session published under <sessions>.
# The pool runs it as the REPLAY of an obligation its solver answered
# SAT_MODEL_READY, in its worker, on the class tree and plan its solve
# started on; GROW again for an obligation whose replay exposed a region, in
# a directory of its own beside the worker, under the grown class tree;
# CONFIRM for the claim's world.  Every argument is the caller's, so it runs on
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
  local charged=$6 need=${7:-$6}
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
    campaign_replay_heap_basis_mb="${need}" \
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
      | campaign_write_whole "${result_row}"
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
  # A verdict that names no session published none: a refusal, or nothing
  # moving for a while (REPLAY_NO_PROGRESS), decided every obligation the
  # replay carried, and it ended there (FocusedReplay#refusedAt).  What it
  # wrote before is a prefix of a run, which the replay withdrew itself at
  # its close (RowRuntime#closeSession); one its move left listed is
  # withdrawn here, on the host that ran the replay.
  [[ -n "$(jq -r '.sessionId // ""' "${statement}")" ]] \
    || campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
      "${worker}/refused-sessions" "a refusal or a stall decided every \
obligation its replay carried and the replay ended there, so its rows are a \
prefix of a run"
  # A new inode over the solver's row (campaign_write_whole); a head reading
  # it over NFS opens the new one.
  campaign_write_whole "${result_row}" <"${statement}"
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
# in a shared pool (stream_shared_pool), its share of its hosts' slots at
# its measured replay charge (campaign_pool_slots): those slots over the
# sharing explorations running now, each an entry of the ledger --
#
#   ${campaign_host_gate_root}/explorations/<id>  fresh while its head lives
#
# (campaign_stream_has_slot) -- so the cases a sweep runs at once share
# their hosts, and one alone takes them all.
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
#   ${campaign_host_gate_root}/<host>/charges/<mb>.<id>
#                                                 one live start's charge of
#                                                 <mb>, its lease the file's
#                                                 mtime
#   ${campaign_host_gate_root}/<host>/available  "<epoch> <mb>": MemAvailable,
#                                                 read at most every poll
#   ${campaign_host_gate_root}/<host>/total      "<mb>": MemTotal, read once
#
# A start of <mb> may go when two things leave it room under the host's
# ceiling, CAUSYNTH_HOST_MAX_USED_PCT of MemTotal (tools/lib/gc-env.sh):
# what the host's live charges promise, and what it really uses (MemTotal
# less MemAvailable), each with the room a head holds there (HEAD ROOM
# below) and <mb>.  A start's charge holds for the whole life of what it
# started, not only while that grows into it: a JVM below its charge grows
# into it later, and what the host promised it is room no other start may
# take meanwhile (Solr obligation replays grow for minutes toward their
# 6000 MB; counted only for their first 60 s, rounds SB11 and SB13 filled
# lift12-15 and lift06 to 29-30 GB).  A charge lives by a lease: the shell
# that took it renews it while it lives (campaign_host_keep), and it is
# released the moment what it ran returns (campaign_host_release), whoever
# started it, so a head's JVMs, one after another, are never charged twice.
# A run killed before its release leaves charges that lapse with their
# lease.  A start that does not fit WAITS -- an obligation or a head's step
# goes to another host or later, never skipped -- and says so once.  A JVM
# that grows past its charge asks the host again for the excess, by the
# real-use half of the rule alone (campaign_watch_workload), and holds what
# it was granted the same way.
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
# A charge's lease: how long it counts past its last renewal, and how often
# the shell that holds it renews it (campaign_host_keep).  The lease spans
# NFS's attribute cache (60 s at most) beside a renewal, so a live charge
# is never read as lapsed on another lift.
campaign_host_lease_s=120
campaign_host_renew_s=10
# Whether this shell is a campaign's head, whose engine JVMs and replays are
# placed and charged as its steps (do_campaign, campaign_head_charged); an
# obligation's replay is inside the obligation's charge.
campaign_head_charging=0
# The most of a host's memory a start may leave charged or in use, in
# percent: what stays free is the page cache the JVMs read their jars and
# corpora through, the owner's own sessions, and what no charge covers.
campaign_host_max_used_pct=${CAUSYNTH_HOST_MAX_USED_PCT}
[[ "${campaign_host_max_used_pct}" =~ ^[0-9]+$ ]] \
  && (( campaign_host_max_used_pct > 0 && campaign_host_max_used_pct <= 100 )) \
  || die "CAUSYNTH_HOST_MAX_USED_PCT must be a percentage in 1..100: \
${campaign_host_max_used_pct}"
# How often a waiting start asks again, and how old a MemAvailable reading
# may be before it is read again.
campaign_host_poll_s=5
# How old a reading the shells that do not refresh it may still use
# (campaign_host_memory_reading: one shell per host refreshes).
campaign_host_reading_keep_s=30
# How long a host may stay unreachable over ssh -- its memory unreadable, a
# worker's connection refused before it started -- before the obligation
# fails by name.  sshd refuses connections under a round's burst of them.
campaign_ssh_patience_s=300
# A lock older than this was left by a campaign that died holding it.
campaign_host_lock_stale_s=30
# A head reservation, or a sharing exploration's entry, older than this was
# left by a head that is gone.
campaign_head_reservation_stale_s=600
# This head's reservation file (campaign_head_reserve), or empty, and the
# process that holds it: a subshell of the head exits without giving it up.
campaign_head_reservation=""
campaign_head_pid=""
# The hold of the head step waiting for room now (campaign_head_place), or
# empty: a file stating its need among the reservations of the host it will
# take, which every start that is not this head's counts while it is fresh
# (campaign_host_head_room), as a head's reservation.
campaign_head_hold=""
# This exploration's entry among the sharing ones (campaign_stream_enroll),
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
  local host=$1 dir=$2 now=$3 at=0 mb="" fresh refresh=${2}/refresh
  read -r at mb 2>/dev/null <"${dir}/available" || true
  [[ "${at}" =~ ^[0-9]+$ && "${mb}" =~ ^[0-9]+$ ]] || at=0
  if (( now - at < campaign_host_poll_s )); then
    printf '%s\n' "${mb}"
    return 0
  fi
  # One shell refreshes a host's reading, the one holding ${refresh}; the
  # others keep the last reading while it is younger than
  # campaign_host_reading_keep_s.  Every waiter refreshing every host at
  # once (an ssh each, then a rename into this NFS directory) held 254
  # processes in D state on one lift (2026-10-06).  Past that age a waiter
  # reads the host itself and publishes nothing.
  if ! mkdir "${refresh}" 2>/dev/null; then
    if (( now - at < campaign_host_reading_keep_s )); then
      printf '%s\n' "${mb}"
      return 0
    fi
    (( now - $(stat -c %Y "${refresh}" 2>/dev/null || echo "${now}") \
      < campaign_host_lock_stale_s )) || rmdir "${refresh}" 2>/dev/null
    mkdir "${refresh}" 2>/dev/null || refresh=""
  fi
  mb=$(campaign_host_available_mb "${host}" | grep -E '^[0-9]+$' | tail -n 1)
  # A name of its own: the campaign's subshells share $$, and
  # every campaign on every lift writes this ledger.
  if [[ "${mb}" =~ ^[0-9]+$ && -n "${refresh}" ]] \
      && fresh=$(mktemp "${dir}/available.XXXXXX"); then
    printf '%s %s\n' "${now}" "${mb}" >"${fresh}"
    mv -f -- "${fresh}" "${dir}/available"
  fi
  [[ -z "${refresh}" ]] || rmdir "${refresh}" 2>/dev/null
  [[ "${mb}" =~ ^[0-9]+$ ]] || return 1
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

# campaign_host_try_start <host> <need_mb>: one try.  0 when the start may
# go now and is charged to the host, held by this shell (campaign_host_hold)
# and named in campaign_host_charge_id; 1 when it does not fit yet (why, in
# campaign_host_wait_reason); 2 when the host's memory cannot be read; 3 when
# another start holds the ledger's lock for the instant it takes to charge
# one.  Every start states its need -- what it measurably takes -- with no
# default.
campaign_host_wait_reason=""
campaign_host_charge_id=""
campaign_host_try_start() {
  local host=$1 need=$2 key dir now available total limit charged used
  local held=0
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  limit=$(campaign_host_limit_mb "${total}")
  used=$(( total - available ))
  [[ "${campaign_host_head_start}" == 1 ]] \
    || held=$(campaign_host_head_room "${dir}" "${now}")
  campaign_host_lock "${dir}" "${now}" || return 3
  charged=$(campaign_host_charged "${dir}" "${now}")
  if (( charged + held + need > limit || used + held + need > limit )); then
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${charged} MB charged to what it \
runs, ${used} MB in use and ${held} MB held for a head; one needs ${need} MB \
and at most ${limit} MB (${campaign_host_max_used_pct}% of ${total} MB) may \
be charged or in use"
    return 1
  fi
  campaign_host_charge_row "${dir}" "${need}"
  return 0
}

# The most of a host of <total_mb> its charges, or its real use, may reach:
# CAUSYNTH_HOST_MAX_USED_PCT of it.
campaign_host_limit_mb() {
  printf '%s\n' "$(( $1 - $1 * (100 - campaign_host_max_used_pct) / 100 ))"
}

# The MB the live charges of the host directory <dir> hold at <now>: each
# renewed within its lease.  One past ten leases was left by a run that is
# gone, and is removed.
campaign_host_charged() {
  local dir=$1 now=$2
  [[ -d "${dir}/charges" ]] || { echo 0; return 0; }
  find "${dir}/charges" -maxdepth 1 -type f -printf '%T@ %f\n' 2>/dev/null \
    | awk -v now="${now}" -v lease="${campaign_host_lease_s}" \
        -v dir="${dir}/charges" '
        { age = now - int($1); split($2, name, ".") }
        age < lease && name[1] ~ /^[0-9]+$/ { mb += name[1]; next }
        age >= 10 * lease { system("rm -f -- \"" dir "/" $2 "\"") }
        END { print mb + 0 }'
}

# Charges <need_mb> to the host directory <dir>, whose lock this shell
# holds, and gives the lock back: the charge, named in
# campaign_host_charge_id, is held by this shell (campaign_host_hold).
campaign_host_charge_row() {
  local dir=$1 need=$2
  campaign_host_charge_id="${need}.$(hostname -s).${BASHPID}.$(date +%s).\
${RANDOM}"
  mkdir -p "${dir}/charges"
  : >"${dir}/charges/${campaign_host_charge_id}"
  rmdir "${dir}/lock"
  campaign_host_hold "${dir}/charges/${campaign_host_charge_id}"
}

# campaign_host_keep <host> <id>: the charge <id> on <host> is held by this
# shell too, one the shell that took it hands over (the host's solver, which
# outlives the obligation that started it).
campaign_host_keep() {
  campaign_host_hold "${campaign_host_gate_root}/$(campaign_host_key \
"$1")/charges/$2"
}

# The charge <file> renewed every campaign_host_renew_s while this shell
# lives and the charge stands: by a process of its own, no child of this
# shell (a head's `wait` never waits for it), which ends within a renewal
# of either.  Its programs are the commands, never a function of this shell's
# by their name (the shell test's `sleep`).
campaign_host_hold() {
  local file=$1 owner=${BASHPID}
  ( ( while kill -0 "${owner}" 2>/dev/null && [[ -e "${file}" ]]; do
        command touch -c -- "${file}" 2>/dev/null || true
        command sleep "${campaign_host_renew_s}"
      done ) </dev/null >/dev/null 2>&1 & )
}

# campaign_host_try_grow <host> <mb>: a RUNNING JVM grows by <mb>.  What the
# ledger promises others -- their charges, a head's room -- is no reason to
# end a JVM already running: the growth is refused (1, the reason in
# campaign_host_wait_reason) only when the host's real use, MemTotal less
# MemAvailable, would pass CAUSYNTH_HOST_MAX_USED_PCT with it.  Granted, it
# is charged on the ledger as a start and held by this shell (0, its charge
# in campaign_host_charge_id), so the starts after it wait for it.  2 when the
# host's memory cannot be read, 3 while another holds the ledger's lock.
campaign_host_try_grow() {
  local host=$1 mb=$2 key dir now total available limit
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  limit=$(campaign_host_limit_mb "${total}")
  campaign_host_lock "${dir}" "${now}" || return 3
  if (( total - available + mb > limit )); then
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${available} MB available of \
${total} MB, and ${mb} MB more would put over \
${campaign_host_max_used_pct}% of it in use"
    return 1
  fi
  campaign_host_charge_row "${dir}" "${mb}"
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
# sharing exploration's entry.
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

# The room, in MB, one more start that is no head's own may take on <host>
# now, read without charging it (campaign_host_try_start decides, under the
# host's lock): the least of what the live charges and the real use leave
# under the ceiling, less the room a head holds there.  2 when unreadable.
campaign_host_room() {
  local host=$1 dir now total available limit charged used
  dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  limit=$(campaign_host_limit_mb "${total}")
  charged=$(campaign_host_charged "${dir}" "${now}")
  used=$(( total - available ))
  (( charged > used )) || charged=${used}
  printf '%s\n' "$(( limit - charged \
    - $(campaign_host_head_room "${dir}" "${now}") ))"
}

# campaign_pool_slots <need_mb> <host>...: how many starts of <need_mb> the
# hosts hold at once when each holds its charge -- on each host, as many as
# fit under its ceiling (CAUSYNTH_HOST_MAX_USED_PCT of its MemTotal) and no
# more than its cores, both from the ledger -- summed: the slots a shared
# pool's explorations share at their measured replay charge
# (campaign_stream_has_slot, stream_shared_pool).
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

# Drops one start's charge: what it ran has returned, and whatever it held
# is back in MemAvailable.  Its holder stops renewing it.
campaign_host_release() {
  rm -f -- "${campaign_host_gate_root}/$(campaign_host_key "$1")/charges/$2"
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
# How long a JVM with a trace directory -- the recording, a native
# reproduction: a cluster test whose waits never time out (the trees'
# CausynthBounds) -- may write nothing at all, no trace row and no line of
# output, before it is taken for hung.  A healthy one writes every few
# seconds; one waiting for a notification it lost waits its 6 h bound
# (solr-bugs-reindex-cleanup SB16: an Overseer command's waitForState after
# its source's deletion, an hour without a byte).
campaign_unbounded_stall_s=600
# The file a trace directory's watcher leaves there when it ended the
# workload, its first word the reason -- RECORDING_BOUND (the trace passed
# recording_max_trace_mb), RECORDING_STALLED (it wrote nothing for
# campaign_unbounded_stall_s) -- and the rest why: the reason SEED fails by
# (do_workload), and the acceptance report's first.
campaign_recording_end_marker=RECORDING_ENDED

# How many bytes a JVM watched with trace directory <dir> has put where its
# progress shows: the files of <dir> (its rows; a native run's output) and
# its own output and error where they are files.  Never its sockets: a hung
# cluster test still pings its ZooKeeper.
campaign_workload_output_bytes() {
  local pid=$1 dir=$2
  {
    find "${dir}" -type f -printf '%s\n' 2>/dev/null
    stat -L -c '%s' "/proc/${pid}/fd/1" "/proc/${pid}/fd/2" 2>/dev/null
  } | awk '{bytes += $1} END {print bytes + 0}'
}

# campaign_watch_workload <pid> <charged_mb> [dir] [max_trace_mb]: one
# workload JVM watched until it ends (experiments/lib/execute.sh).  Its peak
# resident memory, in MB, goes to <dir>/workload_rss_mb: a recording's trace
# directory, what a native run of it is charged (REPRODUCE); a replay's
# worker directory, the campaign's measured replay need
# (campaign_replay_measured).  For a JVM its host was charged <charged_mb>
# for (0: none, a recording) the peak is also said at its end beside that
# charge.  Such a
# JVM that grows past what its host holds for it asks the host for the
# excess (campaign_host_try_grow: refused only when the host's real use
# would pass CAUSYNTH_HOST_MAX_USED_PCT, never for what the ledger promised
# future starts) and holds what it was granted; one the host cannot take is
# ended there, and says so.  A replay whose native symbolic
# state ran away reached 27 GB and the kernel killed what it chose on the
# host (hdfs-17960 v96); one ended for 41 MB over its 2500 MB on a host with
# 28 GB free failed its case for nothing (accept-e1b-17960's seed replay),
# and one refused 6 MB on a host with 16 GB free, all of it promised to
# starts and heads (accept-x1-17960's).
# What it was granted is held by the watcher (campaign_host_hold) and
# released when it ends; its peak is campaign_watch_peak_mb once it has
# (a solver asked again places its JVM by it, campaign_obligation_worker).
# A JVM given <max_trace_mb> (a recording's, 0 for none: a native run's)
# is one with a trace directory <dir> and no bound on its waits.  It is ended,
# saying why in <dir>/${campaign_recording_end_marker}, once its trace
# (<dir>/runtime_trace.jsonl) passes <max_trace_mb> (RECORDING_BOUND: never a
# trace cut short and aggregated as if whole), or once it added nothing to
# <dir> or its output for campaign_unbounded_stall_s (RECORDING_STALLED,
# campaign_workload_output_bytes), its threads first dumped on its own
# output (SIGQUIT).
campaign_watch_peak_mb=0
campaign_watch_workload() {
  local pid=$1 charged=$2 dir=${3:-} max_mb=${4:-0} traced=${4:+1}
  local peak=0 held=$2 mb id status=0 refused="" written=0 ended=""
  local output="" wrote="" since=${SECONDS}
  local -a grants=()
  [[ -z "${traced}" ]] || rm -f -- "${dir}/${campaign_recording_end_marker}"
  while kill -0 "${pid}" 2>/dev/null; do
    if (( max_mb > 0 )); then
      written=$(stat -c %s "${dir}/runtime_trace.jsonl" 2>/dev/null) \
        || written=0
      if (( written > max_mb * 1048576 )); then
        ended="RECORDING_BOUND: the recording's trace passed \
recording_max_trace_mb (${max_mb} MB) at $(( written / 1048576 )) MB, more \
rows than SEED's aggregation holds; the workload was ended"
        kill -KILL "${pid}" 2>/dev/null || true
        break
      fi
    fi
    if [[ -n "${traced}" ]]; then
      output=$(campaign_workload_output_bytes "${pid}" "${dir}")
      if [[ "${output}" != "${wrote}" ]]; then
        wrote=${output}
        since=${SECONDS}
      elif (( SECONDS - since >= campaign_unbounded_stall_s )); then
        ended="RECORDING_STALLED: the workload JVM wrote nothing -- no \
trace row, no output -- for $(( SECONDS - since ))s, and nothing it waits for \
ever times out; its threads are dumped on its output; ended"
        kill -QUIT "${pid}" 2>/dev/null || true
        sleep 2
        kill -KILL "${pid}" 2>/dev/null || true
        break
      fi
    fi
    mb=$(campaign_process_rss_mb "${pid}") || mb=""
    if (( ${mb:-0} > peak )); then
      peak=${mb}
      [[ -z "${dir}" ]] \
        || printf '%s\n' "${peak}" >"${dir}/workload_rss_mb"
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
  campaign_watch_peak_mb=${peak}
  if [[ -n "${ended}" ]]; then
    printf '%s\n' "${ended}" >"${dir}/${campaign_recording_end_marker}"
    echo "causynth: ${ended}" >&2
  fi
  (( charged > 0 )) || return 0
  [[ -z "${refused}" ]] || echo "causynth: the workload JVM's resident \
memory reached ${peak} MB, over the ${held} MB its host holds for it, and \
${refused}; ended" >&2
  echo "causynth: the workload JVM's resident memory peaked at ${peak} MB; \
its host was charged ${charged} MB for it$( (( held == charged )) \
    || echo " and took ${held} MB as it grew")" >&2
}

# campaign_head_charged <need_mb> <command...>: one heavy start of
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
# ends the shell leaves the charge to lapse with its lease.
campaign_head_charged() {
  local need=$1 id status busy="" host
  shift
  if [[ "${campaign_head_charging}" != 1 ]]; then
    "$@"
    return
  fi
  # Its words go to stderr: the command's stdout is often its artifact
  # (ImportGateMain's summary JSON).
  campaign_head_heartbeat
  campaign_head_place "${need}" >&2
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

# Room for a head step of <need_mb>, charged: on the head's own
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
  local need=$1 host room best best_room said=false status=0
  local since=${SECONDS}
  while true; do
    campaign_host_head_start=1 campaign_host_try_charge localhost "${need}"
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
      campaign_host_try_charge "${best}" "${need}"
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

# campaign_stream_job <kind> <host> <charge> <id> <worker> <args...>: one
# start of the pool, on the host that admitted it and charged it <charge>:
# an OBLIGATION's solve (campaign_obligation_worker <args...>), the REPLAY of
# one its solver answered SAT_MODEL_READY or a GROW RERUN's replay
# (campaign_obligation_replay <args...>), or an attempt's CONFIRM replay
# (campaign_confirm_replay <args...>).  A local one is a subshell under
# `set -euo pipefail`; a remote one runs through the remote worker script, a
# solve as --run-obligation (the script and ssh's own output beside its
# logs), a replay as a placed step (campaign_run_placed); its stdout and
# stderr are <worker>'s either way, a REPLAY's as replay-stdout.log and
# replay-stderr.log beside its solve's.  Its charge, which the
# head holds, is released as soon as its work returned, before the head
# waits to see what a peer wrote (campaign_await_remote_result), and again
# by the head once the job ended however it did (campaign_stream_ended,
# campaign_stream_reap).
campaign_stream_job() {
  local kind=$1 host=$2 charge=$3 id=$4 worker=$5 status=0
  shift 5
  local -a work=(campaign_obligation_worker "$@")
  # Where the job stages its sessions: an obligation's and a re-run's under
  # their worker, a CONFIRM replay's beside it (campaign_confirm_plan).
  local staged="${worker}/sessions" logs="${worker}/"
  case "${kind}" in
    REPLAY) work=(campaign_obligation_replay "$@"); logs="${worker}/replay-" ;;
    RERUN) work=(campaign_obligation_replay "$@") ;;
    HARD) logs="${worker}/hard-" ;;
    CONFIRM) work=(campaign_confirm_replay "$@"); staged="$1/sessions" ;;
  esac
  if campaign_host_is_local "${host}"; then
    ( set -euo pipefail; "${work[@]}" ) >"${logs}stdout.log" \
      2>"${logs}stderr.log" || status=$?
  elif [[ "${kind}" == OBLIGATION || "${kind}" == HARD ]]; then
    campaign_dispatch_remote "${host}" "${worker}" \
      "$(campaign_remote_worker_bound_s)" --run-obligation "$@" \
      || status=$?
  else
    campaign_run_placed "${host}" "${work[@]}" >"${logs}stdout.log" \
      2>"${logs}stderr.log" || status=$?
  fi
  campaign_host_release "${host}" "${charge}"
  campaign_host_is_local "${host}" && return "${status}"
  if (( status != 0 )); then
    campaign_log "${kind} ${id} on ${host}: the remote worker exited \
${status}; its logs, and ssh's own output, are in ${worker}"
    return "${status}"
  fi
  campaign_await_remote_result "${worker}" "${host}" "${id}" "${staged}"
}

# campaign_write_whole <file>: its standard input becomes <file> as a new
# inode (<file>.part renamed over it), never a rewrite in place: an
# obligation's answer is rewritten on another host than the one that wrote
# its solver's row (its REPLAY's), and a host whose NFS client held the old
# row cached rewrote it past a truncate it lost -- the replay's row, then
# the tail of the solver's (MCH1: three such rows in hdfs-17899-bug1 and
# hdfs-17897 failed the planner on a malformed line).
campaign_write_whole() {
  cat >"$1.part" && mv -f -- "$1.part" "$1"
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
  local -a said=()
  for failure in "${worker}/stderr.log" "${worker}/replay-stderr.log"; do
    [[ ! -e "${failure}" ]] || said+=("${failure}")
  done
  failure=""
  (( ${#said[@]} == 0 )) || failure=$(sed -n -E \
    's/^(Error: |  reason=)//p' "${said[@]}" | tail -n 1) || failure=""
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
    | campaign_write_whole "${worker}/obligation_result.jsonl"
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
# import gate over the sessions that landed with the round now owed and the
# verdicts of the confirmation replays that returned, or a COMPOSE attempt at
# the witnesses among them -- is one STEP at a time, in the background
# (campaign_stream_step), so the pool goes on starting and collecting while a
# step waits for memory or runs; an attempt's confirmation replay is a job of
# the pool, never a step.  The corpus and the ledger change only
# between two steps, in the head's hands (campaign_stream_step_start): a
# step reads them as a landed whole, and whatever returns meanwhile waits
# for the next one -- the busier the head, the more one step takes in.
#
# The loop's state is campaign_explore's locals, which the helpers below read
# and write through bash's dynamic scope:
#
#   stream_queue      "<kind> <round> <id> [<session>]" not started yet:
#                     OBLIGATION (its solve); REPLAY (the replay of one its
#                     solver answered SAT_MODEL_READY, the class tree and
#                     plan its solve started on in place of a session);
#                     RERUN (GROW re-running the replay that exposed a
#                     region, its exposing session named); or CONFIRM (an
#                     attempt's confirmation replay, round "-", the
#                     attempt's number its id)
#   stream_jobs       pid -> "<kind> <round> <id> <host> [<session>]"
#   stream_pending    "<kind> <round> <id> <host> <status> [<session>]": what
#                     returned since the last step began, not landed yet
#   stream_flying     obligation id -> its row, from its queueing until its
#                     answer lands -- solving, its REPLAY queued or
#                     replaying: a round's --in-flight
#   stream_host_jobs  host -> how many of this campaign's run there
#   stream_host_solves host -> how many of them are solves
#                     (campaign_stream_solves_per_host)
#   stream_step_pid   the step running, or ""; stream_step_dir its directory
#                     (steps/NNNN/: what it gates and plans, or attempts)
#   stream_witnesses  sessions landed as witnesses, gated, not attempted yet
#   stream_confirming attempt -> its claim's model, while its confirmation
#                     is queued, runs or is not decided yet
#   stream_deferred   witnesses whose attempt claimed a model under
#                     confirmation: attempted again once a verdict lands
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
#               publishes the claim the final stages accept, and its
#               CONFIRM, a job of the pool, confirms it (campaign_stream_attempt,
#               campaign_stream_decide): the queue is cancelled, what runs
#               is reaped, and the corpus is the one that attempt composed
#               (campaign_stream_end).
#   FIXED_POINT nothing proposed, exposed, queued, running or unlanded.
#   REGION_PATH_WAVE_BUDGET_REACHED  a round of wave region_path_max_waves
#               still owes work: it is not dispatched, the queue is
#               cancelled, and what runs lands.
#   CAMPAIGN_BUDGET_REACHED  between two steps, the campaign's budget has
#               no room for the stages after it (campaign_claim_room): as
#               at a witness, the queue is cancelled and what runs reaped.
#   PLANNER_HEAP_EXCEEDED  a round's planner outgrew the head's heap.
#
# Each end is stated in exploration.json with the work it left owed, and a
# forced one as a DIAGNOSTIC row of campaign_gaps.jsonl; whether it cut the
# exploration short is judged once, at EMIT, against the claim published
# (campaign_exploration_cut).  None fails the campaign, which goes on to
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
  local stream_waiting="" stream_admitted_host="" stream_admitted_mb=""
  local stream_stop=""
  local stream_share_said="" stream_round_due=false
  local stream_stop_detail="" stream_anchors="[]"
  local stream_step_pid="" stream_step_dir="" stream_steps=0
  local -a stream_queue=() stream_hosts=() stream_swaps=() stream_pending=()
  local -a stream_witnesses=() stream_deferred=() stream_after_witness=()
  local -a stream_cancelled=() stream_reaped=() stream_round_args=()
  local -a stream_reruns_dropped=() stream_confirms_reaped=()
  local -A stream_jobs=() stream_job_charge=() stream_job_worker=()
  local -A stream_job_tree=() stream_flying=() stream_pool_slots=()
  local -A stream_host_jobs=() stream_host_cores=() stream_host_unread=()
  local -A stream_host_solves=() stream_host_hard=()
  local -a stream_hard=()
  local -A stream_solver_seen=() stream_confirming=()
  # An open witness chain (campaign_stream_attempt): the producers it names,
  # those already grown, and the witnesses attempted again once they are.
  local -A stream_chain=() stream_chain_grown=()
  local -a stream_chain_witnesses=()
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
  trap 'campaign_stream_reap; campaign_planner_stop; campaign_stream_unenroll
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
      # A round owed and not planned: answers landed since the last one,
      # or GROW's re-runs or swaps still owed.
      (( stream_dirty == 0 && stream_hold == 0 )) || stream_round_due=true
    fi
    if [[ "${stream_stop}" == WITNESSED \
        || "${stream_stop}" == CAMPAIGN_BUDGET_REACHED ]]; then
      campaign_stream_end
      break
    fi
    [[ -n "${stream_step_pid}" ]] || campaign_stream_step_start
    [[ -z "${stream_stop}" ]] || campaign_stream_drop
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
  campaign_planner_stop
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
# either a session landed (the corpus grew) or no question is left to wait
# for (the last answers may close the frontier; a confirmation's verdict
# changes no frontier).  Never while GROW's re-runs or swaps are owed: the
# corpus is about to change under the round.
campaign_stream_plan_due() {
  local entry
  (( stream_dirty == 1 && stream_hold == 0 )) || return 1
  (( stream_landed > 0 )) && return 0
  for entry in "${stream_jobs[@]}" "${stream_queue[@]}"; do
    [[ "${entry}" == CONFIRM\ * ]] || return 1
  done
}

# Whether a witness's confirmation is owed its verdict: queued, running, or
# returned and not yet landed.  Its verdict goes first: no attempt starts
# meanwhile, since one that confirms ends the exploration, and an attempt
# composes the corpus again (hdfs-11741 CC7: attempt 0001 started a second
# before attempt 0000's ADMITTED confirmation returned, and that verdict
# waited behind it).
campaign_stream_confirm_owed() {
  local entry
  for entry in "${stream_jobs[@]}" "${stream_queue[@]}" \
      "${stream_pending[@]}"; do
    [[ "${entry}" != CONFIRM\ * ]] || return 0
  done
  return 1
}

# Between two steps, in the head's hands, the next one, in steps/NNNN/.
# Witnesses gated and not yet attempted make it an ATTEMPT (`witnesses`,
# all of them, and `confirming`, the models whose confirmation is still
# owed) unless a confirmation is owed its verdict, which goes first
# (campaign_stream_confirm_owed):
# nothing lands while an attempt runs, so it composes the corpus as it
# stood, and whatever returns meanwhile, a witness too, waits for the step
# after it -- at most one attempt at a time, the witnesses that come during
# one coalesced into the next.  Else what returned lands
# (campaign_stream_land), GROW's re-runs swap in once due, the staged
# sessions move into the corpus (campaign_stream_move), and the step takes
# them in when there is work: `gate`, the sessions that landed; `confirms`,
# the confirmation replays that returned, to decide; `round`, the round now
# owed, with its in_flight.jsonl, taken here, where nothing is unlanded.
campaign_stream_step_start() {
  local dir name="" row entry
  local -a stream_staged=() gate=() confirms=()
  if (( ${#stream_witnesses[@]} > 0 )) && [[ -z "${stream_stop}" ]] \
      && ! campaign_stream_confirm_owed; then
    campaign_stream_step_dir
    printf '%s\n' "${stream_witnesses[@]}" >"${dir}/witnesses"
    for entry in "${stream_confirming[@]}"; do
      printf '%s\n' "${entry}"
    done >"${dir}/confirming"
    stream_witnesses=()
  else
    (( ${#stream_pending[@]} == 0 )) || campaign_stream_land
    if campaign_stream_swap_due; then
      campaign_stream_swap
      (( ${#stream_chain[@]} == 0 )) || campaign_stream_chain_reattempt
    fi
    (( ${#stream_staged[@]} == 0 )) || campaign_stream_move
    if [[ -z "${stream_stop}" ]] && campaign_stream_plan_due; then
      name=$(printf 'obligations-%04d' "${stream_round}")
    fi
    (( ${#gate[@]} + ${#confirms[@]} > 0 )) || [[ -n "${name}" ]] \
      || return 0
    campaign_stream_step_dir
    (( ${#gate[@]} == 0 )) || printf '%s\n' "${gate[@]}" >"${dir}/gate"
    (( ${#confirms[@]} == 0 )) \
      || printf '%s\n' "${confirms[@]}" >"${dir}/confirms"
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
# witnesses <dir>/witnesses names; or the import gate over the sessions
# <dir>/gate names (one call: the head's), the verdicts on the confirmation
# replays <dir>/confirms names (campaign_stream_decide), and -- unless one of
# them confirmed its claim -- the round <dir>/round names, planned into
# obligations-NNNN/ by the exploration's planner (campaign_stream_plan).  An
# accepted witness (<dir>/witnessed) ends the
# exploration.  A BLOCKING row fails the campaign at IMPORT here, and
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
    [[ ! -s "${dir}/confirms" ]] || campaign_stream_decide "${dir}"
    if [[ -s "${dir}/round" && -s "${dir}/witnessed" ]]; then
      # The exploration ends here: the round owed is never planned.
      : >"${dir}/round-skipped"
    elif [[ -s "${dir}/round" ]]; then
      round_dir="${iteration_dir}/$(cat "${dir}/round")"
      [[ ! -e "${round_dir}" ]] || die \
        "obligation round directory already exists: ${round_dir}"
      mkdir -p "${round_dir}"
      # Copied as the planner starts: the round's time is the planner's own.
      cp -- "${dir}/in_flight.jsonl" "${round_dir}/in_flight.jsonl"
      campaign_stream_plan "${round_dir}" >"${round_dir}/stdout.log" \
        2>"${round_dir}/stderr.log" || status=$?
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

# ---------------------------------------------------------------------------
# THE PLANNER SERVICE.  One planner JVM serves an exploration's rounds
# (explore.ExploreMain --serve, explore.Service): what it read for a round it
# keeps for the next -- the corpus's rows, the static map, the slot table --
# so a round reads only the sessions landed since, and its files are the ones
# a planner of its own writes (offline-ab.sh EXPLORE.serve).  A planner JVM
# per round read the whole corpus each time: hdfs-adhoc-07 EX1-07d's 16
# planners took 1h51m of EXPLORE's 2h25m, a late round ~15 min (PERFORMANCE
# §5).  The round's step starts it when none lives, as a head step: placed by
# the usual rule (campaign_head_place), at what the planner starts at
# (campaign_engine_start_mb), charged there for its life (campaign_host_keep)
# and grown as a watched JVM (campaign_watch_workload); a round is one
# question, asked on its host, where its questions wait on that host's own
# disk (campaign_planner_dir).  Its state, under ${iteration_dir}/planner/:
#   pid      the head's shell that holds it (it ends with the service)
#   jvm      the planner JVM's pid on its host, as it states it
#   host, charge, heap, id   where it runs, its charge, its heap, which start
#   busy     the head's room it takes, when it runs on the head's host
#   status   its exit, once it ended
# Its log is ${iteration_dir}/planner.log.  It runs out of heap (exit 3):
# started again at twice its heap up to engine_memory_mb, the round asked
# again; at the engine heap the round is PLANNER_HEAP_EXCEEDED, as a planner
# JVM's was.  Any other end fails EXPLORE with its deepest throwable.  The
# exploration's end stops it (campaign_planner_stop), and so does the head's
# EXIT trap: its JVM by the pid it stated, on its host, and the shell that
# holds it.  stop-run.sh finds it as it finds the run's other processes, by
# the run's output directory on its command line (--sessions).
# ---------------------------------------------------------------------------

# Where the planner instance <id> of the corpus <sessions> takes its
# questions, on the host that runs it (explore.Service states the layout).
campaign_planner_dir() {
  printf '%s/graphchecker-planners-%s/%s.%s\n' "${TMPDIR:-/tmp}" \
    "$(id -un)" "$(printf '%s' "$1" | sha256sum | cut -c1-16)" "$2"
}

# How long a question waits for a planner just started to name itself, in
# seconds: its JVM names itself before it reads anything.
campaign_planner_start_wait_s=300

# The round <round_dir> (obligations-NNNN, its in_flight.jsonl copied in),
# planned by the exploration's planner: started first when none lives -- at
# twice its heap when the one before ran out of heap (campaign_planner_ended)
# -- and asked again when it ended without answering.  Its status: 0
# planned; 3 the planner ran out of the engine heap; anything else failed,
# the deepest throwable said on stderr.
campaign_stream_plan() {
  local round_dir=$1 state="${iteration_dir}/planner" status since
  local main=edu.uva.liftlab.graphchecker.explore.ExploreMain
  mkdir -p "${state}"
  while true; do
    if ! campaign_planner_alive; then
      if [[ -s "${state}/id" ]]; then
        campaign_planner_ended "${round_dir}" || return
      fi
      campaign_planner_start "$(campaign_engine_start_mb "${main}")"
    fi
    status=0
    campaign_planner_round "${round_dir}" || status=$?
    (( status == 5 )) || return "${status}"
    # The planner ended without answering: its holding shell states its
    # exit once it is gone.
    since=${SECONDS}
    while campaign_planner_alive \
        && (( SECONDS - since < campaign_adapter_kill_grace_s )); do
      sleep 1
    done
    if campaign_planner_alive; then
      printf 'the planner service on %s stopped answering %s and did not \
end (its log: %s)\n' "$(cat "${state}/host")" "$(basename "${round_dir}")" \
        "${iteration_dir}/planner.log" >&2
      return 1
    fi
  done
}

# The exploration's planner ended: 0 when it ran out of a heap below the
# engine heap (the next starts at twice it, campaign_engine_outgrown), else
# its end said on stderr -- 3 when it ran out of the engine heap, 1 for any
# other end -- with the deepest throwable of its log.
campaign_planner_ended() {
  local round_dir=$1 state="${iteration_dir}/planner" status heap next
  local main=edu.uva.liftlab.graphchecker.explore.ExploreMain
  local engine=${engine_memory_mb:-8192}
  status=$(cat "${state}/status" 2>/dev/null) || status=""
  heap=$(cat "${state}/heap")
  if [[ "${status}" == "${campaign_jvm_out_of_heap_status}" ]] \
      && (( heap < engine )); then
    next=$(( 2 * heap < engine ? 2 * heap : engine ))
    campaign_engine_outgrown="$(sed "s| ${main}=[0-9]*||" \
      <<<"${campaign_engine_outgrown}") ${main}=${next}"
    printf '[campaign] %s ran out of its %s MB heap; run again at %s MB\n' \
      "${main##*.}" "${heap}" "${next}" >&2
    return 0
  fi
  printf 'the planner service on %s ended with exit %s before %s (its log: \
%s)\n' "$(cat "${state}/host")" "${status:-unknown}" \
    "$(basename "${round_dir}")" "${iteration_dir}/planner.log" >&2
  campaign_thrown "${iteration_dir}/planner.log" >&2
  [[ "${status}" == "${campaign_jvm_out_of_heap_status}" ]] && return 3
  return 1
}

# Whether the exploration's planner lives: its holding shell, on this host.
campaign_planner_alive() {
  local pid
  pid=$(cat "${iteration_dir}/planner/pid" 2>/dev/null) || return 1
  [[ -n "${pid}" ]] && kill -0 "${pid}" 2>/dev/null
}

# Starts the exploration's planner at <heap_mb>, placed and charged as a
# head step (campaign_head_place, waiting for room as one does), the charge
# held by the shell that holds it for as long as it runs.
campaign_planner_start() {
  local heap=$1 state="${iteration_dir}/planner" host charge id busy=""
  campaign_head_place "$(campaign_jvm_footprint_mb "${heap}")" >&2
  host=${campaign_placed_host}
  charge=${campaign_host_charge_id}
  id="$(date +%s%N)"
  rm -f -- "${state}/status"
  printf '%s\n' "${host}" >"${state}/host"
  printf '%s\n' "${charge}" >"${state}/charge"
  printf '%s\n' "${heap}" >"${state}/heap"
  printf '%s\n' "${id}" >"${state}/id"
  {
    campaign_host_keep "${host}" "${charge}"
    if campaign_host_is_local "${host}" \
        && [[ -n "${campaign_head_reservation}" ]]; then
      busy="${campaign_head_reservation}.busy.${BASHPID}"
      : >"${busy}"
      printf '%s\n' "${busy}" >"${state}/busy"
    fi
    status=0
    if campaign_host_is_local "${host}"; then
      campaign_planner_serve "${heap}" "${id}" \
        "${campaign_root:+${campaign_root}/engine_peak_mb}" \
        "${iteration_dir}/planner.log" "${state}/jvm" \
        --sessions "${sessions}" --results "${results}" \
        "${stream_round_args[@]}" || status=$?
    else
      campaign_run_placed "${host}" campaign_planner_serve "${heap}" "${id}" \
        "${campaign_root:+${campaign_root}/engine_peak_mb}" \
        "${iteration_dir}/planner.log" "${state}/jvm" \
        --sessions "${sessions}" --results "${results}" \
        "${stream_round_args[@]}" || status=$?
    fi
    [[ -z "${busy}" ]] || rm -f -- "${busy}"
    campaign_host_release "${host}" "${charge}"
    printf '%s\n' "${status}" >"${state}/status.part"
    mv -f -- "${state}/status.part" "${state}/status"
  } </dev/null >>"${iteration_dir}/planner.log" 2>&1 &
  printf '%s\n' "$!" >"${state}/pid"
  campaign_log "the planner service starts on ${host} at ${heap} MB" >&2
}

# campaign_planner_serve <heap_mb> <id> <peak_file> <log> <jvm_file>
# <ExploreMain args...>: the planner instance <id>, run on this host until it
# is ended, its questions in campaign_planner_dir: a JVM at <heap_mb> watched
# as it grows past it (campaign_watch_workload), its pid stated in
# <jvm_file> (the head stops it by it, campaign_planner_stop), its peak
# folded into <peak_file> (the head's step need, campaign_engine_peak), its
# output appended to <log>.  Its status is the JVM's.
campaign_planner_serve() {
  local heap=$1 id=$2 peak_file=$3 log=$4 jvm_file=$5 dir watched jvm
  local status=0 peak
  shift 5
  local sessions=""
  local -a args=("$@")
  local index
  for (( index = 0; index < ${#args[@]} - 1; index++ )); do
    [[ "${args[index]}" != --sessions ]] || sessions=${args[index + 1]}
  done
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  # The exploration's planners that ended here before this one; never its
  # own, where its first question may already wait.
  local ended
  for ended in "${dir%.*}".*; do
    [[ "${ended}" == "${dir}" ]] || rm -rf -- "${ended}"
  done
  mkdir -p "${dir}/requests"
  require_file "GraphChecker jar" "${graphchecker_jar}"
  (cd "${graphchecker_work_dir}" \
    && exec env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
      -XX:+ExitOnOutOfMemoryError \
      "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
      "-Dcausynth.system.doors=${causynth_system_doors}" \
      -cp "${graphchecker_jar}" \
      edu.uva.liftlab.graphchecker.explore.ExploreMain --serve "${dir}" \
      "$@") </dev/null >>"${log}" 2>&1 &
  jvm=$!
  printf '%s\n' "${jvm}" >"${dir}/server.part"
  mv -f -- "${dir}/server.part" "${dir}/server"
  printf '%s\n' "${jvm}" >"${jvm_file}"
  watched=$(mktemp -d) || return
  campaign_watch_workload "${jvm}" "$(campaign_jvm_footprint_mb "${heap}")" \
    "${watched}" 2>>"${log}"
  wait "${jvm}" || status=$?
  read -r peak 2>/dev/null <"${watched}/workload_rss_mb" || peak=0
  # Its server file stays, naming a pid gone: a question asked after says
  # no planner answers there (campaign_planner_ask).
  rm -rf -- "${watched}" "${dir}/requests" "${dir}/answers" "${dir}/out"
  campaign_engine_peak "${peak_file}" "${peak}"
  return "${status}"
}

# The round <round_dir> asked of the exploration's planner, on its host:
# here, or there through the remote worker script (campaign_run_placed).
# campaign_planner_ask's status.
campaign_planner_round() {
  local round_dir=$1 state="${iteration_dir}/planner" host id status=0
  host=$(cat "${state}/host")
  id=$(cat "${state}/id")
  local -a ask=(campaign_planner_ask "${sessions}" "${id}" \
    "$((10#${round_dir##*-}))" "${round_dir}/in_flight.jsonl" "${round_dir}")
  if campaign_host_is_local "${host}"; then
    "${ask[@]}" || status=$?
  else
    campaign_run_placed "${host}" "${ask[@]}" || status=$?
  fi
  return "${status}"
}

# campaign_planner_ask <sessions> <id> <round> <in_flight> <round_dir>, on
# the planner's host: the round put to the planner instance <id> and its
# answer waited for.  0 planned; 1 failed, its error on stderr; 5 no planner
# answers there (none named itself within campaign_planner_start_wait_s, or
# the one named is gone): the question is taken back.
campaign_planner_ask() {
  local sessions=$1 id=$2 round=$3 in_flight=$4 round_dir=$5
  local dir name answer pid gone="" since=${SECONDS}
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  mkdir -p "${dir}/requests"
  name="$(date +%s%N).${BASHPID}"
  answer="${dir}/answers/${name}.json"
  jq -n -c --argjson round "${round}" --arg inFlight "${in_flight}" \
    --arg outputDir "${round_dir}" --arg waiter "${BASHPID}" \
    '{round: $round, inFlight: $inFlight, outputDir: $outputDir,
      waiter: $waiter}' >"${dir}/requests/${name}.part"
  mv -- "${dir}/requests/${name}.part" "${dir}/requests/${name}.json"
  while [[ ! -e "${answer}" ]]; do
    pid=$(cat "${dir}/server" 2>/dev/null) || pid=""
    if [[ -n "${pid}" ]]; then
      gone=$([[ -d "/proc/${pid}" ]] || echo 1)
    else
      gone=$(( SECONDS - since >= campaign_planner_start_wait_s ? 1 : 0 ))
    fi
    if [[ "${gone}" == 1 && ! -e "${answer}" ]]; then
      rm -f -- "${dir}/requests/${name}.json" "${dir}/requests/${name}.taken"
      return 5
    fi
    sleep 0.2
  done
  if [[ "$(jq -r '.exit' "${answer}")" != 0 ]]; then
    printf '%s\n' "$(jq -r '.error' "${answer}")" >&2
    rm -f -- "${answer}"
    return 1
  fi
  rm -f -- "${answer}"
}

# The exploration's planner, ended: its JVM, by the pid it stated, on its
# host -- a peer's outlived the shell that held it: the ssh session of its
# remote worker stayed its parent, so the worker's watch never saw the head
# go (SG2-3/-4/-6/-10, alive 75-105 minutes after their campaigns ended) --
# then its holding shell and what it runs, its charge and the head's room it
# took given back.
campaign_planner_stop() {
  local state="${iteration_dir}/planner" pid file host
  [[ -d "${state}" ]] || return 0
  pid=$(cat "${state}/jvm" 2>/dev/null) || pid=""
  host=$(cat "${state}/host" 2>/dev/null) || host=""
  if [[ -n "${pid}" && -n "${host}" ]]; then
    campaign_planner_kill "${host}" "${pid}" "$(cat "${state}/id")"
  fi
  pid=$(cat "${state}/pid" 2>/dev/null) || pid=""
  if [[ -n "${pid}" ]] && kill -0 "${pid}" 2>/dev/null; then
    local -a tree=()
    mapfile -t tree < <(campaign_process_tree "${pid}")
    kill -TERM "${tree[@]}" 2>/dev/null || true
    sleep 1
    kill -KILL "${tree[@]}" 2>/dev/null || true
  fi
  [[ ! -s "${state}/charge" ]] || campaign_host_release \
    "$(cat "${state}/host")" "$(cat "${state}/charge")"
  file=$(cat "${state}/busy" 2>/dev/null) || file=""
  [[ -z "${file}" ]] || rm -f -- "${file}"
  rm -f -- "${state}/pid" "${state}/jvm" "${state}/charge" "${state}/busy"
}

# campaign_planner_kill <host> <pid> <id>: the planner JVM <pid> on <host>
# ended, TERM then KILL, each only while its command line names its
# instance <id> (a pid the host gave another process since, even in the
# second between the two, is left alone).
campaign_planner_kill() {
  local host=$1 pid=$2 id=$3 script
  script="named() { ps -o args= -p ${pid} 2>/dev/null | grep -qF -- ${id}; }
named || exit 0
kill -TERM ${pid} 2>/dev/null; sleep 1
named && kill -KILL ${pid} 2>/dev/null; exit 0"
  if campaign_host_is_local "${host}"; then
    bash -c "${script}"
  else
    campaign_ssh "${campaign_ssh_options[@]}" -- "${host}" "${script}" \
      </dev/null || true
  fi
}

# The step returned: one that failed has said why on the campaign's stderr
# and ends the head.  An attempt that owes a confirmation queues its replay
# first in the pool (CONFIRM, its model under confirmation); witnesses whose
# model was under confirmation wait for a verdict (stream_deferred), and go
# back to be attempted once one lands without ending the exploration.  An
# accepted witness ends the exploration; else the step's round, if it
# planned one, is taken (campaign_stream_take_round).
campaign_stream_step_done() {
  local status=$1 dir=${stream_step_dir} id
  stream_step_pid=""
  stream_step_dir=""
  (( status == 0 )) || exit "${status}"
  campaign_engine_outgrown=$(cat "${dir}/outgrown")
  if [[ -s "${dir}/confirm" ]]; then
    id=$(cat "${dir}/confirm")
    stream_confirming[${id}]=$(cat \
      "${iteration_dir}/witness-attempts/${id}/model")
    stream_queue=("CONFIRM - ${id}" "${stream_queue[@]}")
  fi
  [[ ! -s "${dir}/chain" ]] || campaign_stream_open "${dir}"
  [[ ! -s "${dir}/deferred" ]] || mapfile -t -O "${#stream_deferred[@]}" \
    stream_deferred <"${dir}/deferred"
  if [[ -s "${dir}/decided" ]]; then
    while read -r id; do
      unset 'stream_confirming[$id]'
    done <"${dir}/decided"
    stream_witnesses+=("${stream_deferred[@]}")
    stream_deferred=()
  fi
  if [[ -s "${dir}/witnessed" ]]; then
    stream_stop=WITNESSED
    stream_stop_detail=$(cat "${dir}/witnessed")
    campaign_witness_attempt=$(cat "${dir}/attempt")
    [[ ! -e "${dir}/round-skipped" ]] || stream_round=$((stream_round - 1))
  elif [[ -s "${dir}/heap-exceeded" ]]; then
    # The round was never planned: the last one is the round before it.
    stream_round=$((stream_round - 1))
    stream_stop=PLANNER_HEAP_EXCEEDED
    stream_stop_detail=$(cat "${dir}/heap-exceeded")
  elif [[ -s "${dir}/round" ]]; then
    campaign_stream_take_round "${iteration_dir}/$(cat "${dir}/round")"
  fi
}

# The witness chain an attempt left open (<dir>/chain): its producers not
# grown yet become the chain the rounds grow (campaign_stream_chain_round),
# the queued obligations are cancelled, and its witnesses wait to be
# attempted again once the GROW swaps in (campaign_stream_chain_reattempt).
# A chain whose every producer was grown already cannot close: the
# exploration goes on as before, and the claim it reaches names it
# (WITNESS_CHAIN_OPEN).
campaign_stream_open() {
  local dir=$1 producer
  local -a fresh=()
  while read -r producer; do
    [[ -n "${stream_chain_grown[${producer}]+x}" ]] || fresh+=("${producer}")
  done <"${dir}/chain"
  stream_chain=()
  if (( ${#fresh[@]} == 0 )); then
    campaign_log "the witness's chain is open, and every producer it names \
was grown already: it cannot close"
    return 0
  fi
  for producer in "${fresh[@]}"; do
    stream_chain[${producer}]=1
  done
  mapfile -t stream_chain_witnesses <"${dir}/chain-witnesses"
  campaign_stream_drop
  campaign_log "the witness's chain is open: EXPLORE grows its \
${#fresh[@]} producer(s) and attempts it again; the queued obligations are \
cancelled"
}

# Once a GROW of an open chain swapped in: the chain's witnesses still in
# the corpus are attempted again (a re-run lands as a witness of its own,
# campaign_stream_move), and the chain is the attempt's to state anew.
campaign_stream_chain_reattempt() {
  local witness
  for witness in "${stream_chain_witnesses[@]}"; do
    [[ ! -d "${sessions}/${witness}" ]] || stream_witnesses+=("${witness}")
  done
  stream_chain_witnesses=()
  stream_chain=()
}

# A planned round, taken -- in this order -- through the wave budget, and
# GROW for its exposures, else its obligations into the queue.
campaign_stream_take_round() {
  local round_dir=$1 name exposures exposed proposed wave index
  local -a ids=() rows=()
  name=$(basename "${round_dir}")
  # The planner states both files every round; an empty obligations file is
  # nothing new to ask, and a growth file with no exposure (EXPOSED_REGION,
  # UNPLANNED_INPUT) nothing to grow.
  require_file "round growth rows" "${round_dir}/growth.jsonl"
  require_file "round obligations" "${round_dir}/obligations.jsonl"
  # A doors-only occurrence a value demand reached grows the plan as an
  # exposure does (campaign_stream_grow).
  exposures=$(campaign_exposures "${round_dir}/growth.jsonl"; \
    campaign_unpauses "${round_dir}/growth.jsonl")
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
with ${proposed} obligation(s) still open and ${exposed} exposure(s) \
not yet woven"
    campaign_stream_gap DIAGNOSTIC "${stream_stop}" "${stream_stop_detail}"
    stream_cancelled+=("${ids[@]}")
    return 0
  fi
  # While a witness's chain is open, a round grows the exposures of that
  # chain's producers and nothing else, and queues none of its obligations
  # (PIPELINE §7.9).
  if (( ${#stream_chain[@]} > 0 )); then
    campaign_stream_chain_round "${round_dir}" "${ids[@]}"
    return 0
  fi
  # A round that exposes regions grows the corpus first; what it proposes
  # is queued behind GROW's re-runs, as what was queued before it is, and
  # starts once they have swapped in (no solve starts before): in flight
  # from now on, so no later round proposes it again.  Dropped and re-asked
  # round after round, a backlog of consecutive growing rounds waited for
  # the first round that grew nothing (solr-bugs-reindex-cleanup Z10: four
  # growths in a row, 951 of round 5's 980 proposals asked before, Z9's
  # witness flip asked in round 1 and queued in round 5, never answered).
  (( exposed == 0 )) || campaign_stream_grow "${round_dir}"
  for ((index = 0; index < proposed; index++)); do
    mkdir -p "${round_dir}/${ids[${index}]}"
    stream_flying[${ids[${index}]}]=${rows[${index}]}
    stream_queue+=("OBLIGATION ${name} ${ids[${index}]}")
  done
}

# A round planned while a witness's chain is open: its exposures of the
# chain's producers (growth-chain.jsonl) grown, each producer once, and its
# obligations cancelled, named in exploration.json -- the exploration goes
# on only to close that chain; its unplanned inputs wait, counted (a session
# names them again, and a later round grows them).
campaign_stream_chain_round() {
  local round_dir=$1 occurrence grow=0
  shift
  stream_cancelled+=("$@")
  # A doors-only occurrence a value demand reached is run whole whatever
  # chain is open: dropping its mark asks no obligation.
  jq -c --argjson chain "$(printf '%s\n' "${!stream_chain[@]}" \
      | jq -R . | jq -s -c .)" \
    'select(.kind == "DOORS_ONLY_UNPAUSED" or .kind == "EXPOSED_REGION"
       and (.occurrence as $at | any($chain[]; . == $at)))' \
    "${round_dir}/growth.jsonl" >"${round_dir}/growth-chain.jsonl"
  while read -r occurrence; do
    stream_chain_grown[${occurrence}]=1
    grow=$((grow + 1))
  done < <(jq -r 'select(.kind == "EXPOSED_REGION") | .occurrence' \
    "${round_dir}/growth-chain.jsonl" | sort -u)
  grow=$((grow + $(campaign_unpauses "${round_dir}/growth-chain.jsonl" \
    | grep -c '' || true)))
  campaign_log "$(basename "${round_dir}"): the witness's chain is open: \
${grow} of its producer(s) exposed here grow, and the round's $# \
obligation(s) and $(jq -c 'select(.kind == "UNPLANNED_INPUT")' \
"${round_dir}/growth.jsonl" | grep -c '' || true) unplanned input(s) wait"
  (( grow == 0 )) || campaign_stream_grow "${round_dir}" \
    "${round_dir}/growth-chain.jsonl"
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

# The closure the exploration ended on, judged, and a forced end's
# DIAGNOSTIC row with what it left owed (whether that cut the exploration
# short is EMIT's, campaign_exploration_cut).  An accepted witness ended
# it: nothing past that point is asked, so a truncation asks nothing more
# (each round's own row is DIAGNOSTIC, ExploreMain).  Any other end: when its last round's
# closure was truncated at the task bound (--max-tasks, the manifest's
# `truncated`), a claim over it misses arms, BLOCKING.  The same holds for
# the occurrences PLAN left out to fit schedule_max_jobs (the index's
# `closureCut`, RuntimeWorkflowDiscovery.Workflow#nearest), stated whatever
# the end: DIAGNOSTIC under a witness, BLOCKING otherwise.
campaign_stream_truncation() {
  local last truncated cut cls=BLOCKING
  [[ "${stream_stop}" == FIXED_POINT \
      || "${stream_stop}" == REGION_PATH_WAVE_BUDGET_REACHED ]] \
    || campaign_stream_gap DIAGNOSTIC "${stream_stop}" "${stream_stop_detail}; \
${#stream_cancelled[@]} queued obligation(s) cancelled, ${#stream_reaped[@]} \
unlanded job(s) and ${#stream_confirms_reaped[@]} confirmation(s) reaped, \
${#stream_reruns_dropped[@]} GROW re-run(s) dropped, a round due: \
${stream_round_due}, and ${#stream_after_witness[@]} session(s) that landed \
after the accepted attempt composed out of the corpus (exploration.json; \
whether it cut the exploration short is EMIT's to judge, \
campaign_exploration_cut)"
  cut=$(jq -r '.closureCut // empty | "\(.occurrences) \(.keptDepth)"' \
    "${iteration_dir}/runtime_workflow_schedule_index.json")
  if [[ -n "${cut}" ]]; then
    [[ "${stream_stop}" != WITNESSED ]] || cls=DIAGNOSTIC
    campaign_stream_gap "${cls}" PLAN_CLOSURE_CUT "PLAN planned the \
closure only to demand depth ${cut#* } to fit schedule_max_jobs: ${cut%% *} \
deeper occurrence(s) were not planned, so a claim over it misses their arms \
(the exploration ended ${stream_stop})"
  fi
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
# do_compose, into a scratch directory -- at the witnesses of step <step>.
# An observed fatal is not yet a composable witness: the families COMPOSE
# joins may need sessions later obligations would add.  Its corpus is kept
# (corpus.txt), and what it composed (attempt.json).  Only a claim the final
# stages accept, SAT_CANDIDATE with its polarity deciding, is confirmed, its
# task planned here (campaign_confirm_plan, its replay in <campaign
# root>/witness-confirm/, out of the iteration): a verdict known now is
# decided now; else its replay is owed (<step>/confirm), a job of the pool
# (campaign_stream_step_done), decided once it returns
# (campaign_stream_decide), while landing, planning and later attempts go on.
# A model already under confirmation is not confirmed twice: its witnesses
# wait (<step>/deferred).  With no room left in the budget for a
# confirmation (campaign_claim_room), the claim is accepted as it stands and
# the final CONFIRM decides.
campaign_stream_attempt() {
  local step=$1 dir status=0 claim="" kind="" polarity=false started
  local compose_ms model
  shift
  dir=$(printf '%s/witness-attempts/%04d' "${iteration_dir}" \
    "$(find "${iteration_dir}/witness-attempts" -mindepth 1 -maxdepth 1 \
      -type d 2>/dev/null | grep -c '' || true)")
  mkdir -p "${dir}"
  find "${sessions}" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' \
    | LC_ALL=C sort >"${dir}/corpus.txt"
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
  jq -n -c --arg step "$(basename "${step}")" --arg dir "${dir}" \
    --arg attempt "$(basename "${dir}")" \
    --argjson witnesses "$(printf '%s\n' "$@" | jq -R . | jq -s -c .)" \
    --arg claim "${claim}" --arg kind "${kind}" \
    --argjson polarity "${polarity}" --argjson exit "${status}" \
    --argjson composeMillis "${compose_ms}" \
    '{attempt: $attempt, step: $step, witnesses: $witnesses, dir: $dir,
      composeExit: $exit, claim: $claim, findingKind: $kind,
      polarityDecides: $polarity, composeMillis: $composeMillis}' \
    >"${dir}/attempt.json"
  campaign_log "witness $*: COMPOSE over the corpus as it stands \
(exit ${status}) claims ${claim:-nothing} ${kind} polarityDecides=${polarity}"
  if [[ "${status}" -eq 0 && "${polarity}" == true ]] \
      && campaign_stream_open_chain "${step}" "${dir}" "$@"; then
    return 0
  fi
  if [[ "${claim}" != SAT_CANDIDATE || "${polarity}" != true ]]; then
    campaign_stream_attempt_row "${dir}" null "" 0 false
  elif ! campaign_claim_room; then
    campaign_stream_attempt_row "${dir}" null "" 0 true
    campaign_stream_witnessed "${step}" "${dir}" null
  else
    model=$(campaign_claim_model "${dir}/claim.json")
    if grep -q -x -F -- "${model}" "${step}/confirming"; then
      printf '%s\n' "$@" >"${step}/deferred"
      campaign_stream_attempt_row "${dir}" null "its model is under \
confirmation by an earlier attempt: its witnesses are attempted again once \
that verdict lands" 0 false
      return 0
    fi
    campaign_confirm_plan "${iteration_dir}" "${dir}" \
      "${campaign_root}/witness-confirm/$(basename "${dir}")"
    if [[ ! -s "${dir}/confirm.json" ]]; then
      printf '%s\n' "${model}" >"${dir}/model"
      basename "${dir}" >"${step}/confirm"
      campaign_log "witness $*: its confirmation replay is queued"
      return 0
    fi
    campaign_confirm_settle "${iteration_dir}" "${dir}"
    campaign_stream_confirmed "${step}" "${dir}" 0
  fi
}

# A witness attempt whose COMPOSE names an open chain (ComposeMain
# #campaignClaim: openChain, cone.py's open links of the claimed path) is
# not confirmed -- a claim never stands on a value no attested producer
# made: its row says so, and the producers its arrivals name, with its
# witnesses, go to the head (<step>/chain, <step>/chain-witnesses), which
# grows them and attempts the witnesses again (campaign_stream_open).  False
# where the chain is closed.
campaign_stream_open_chain() {
  local step=$1 dir=$2 manifest=$2/candidate_composition_manifest.json open
  shift 2
  open=$(jq '.solver.campaignClaim.openChain // [] | length' \
    "${manifest}" 2>/dev/null) || open=0
  (( open > 0 )) || return 1
  jq -r '.solver.campaignClaim.openChain[].producer | select(. != "")' \
    "${manifest}" | LC_ALL=C sort -u >"${step}/chain"
  printf '%s\n' "$@" >"${step}/chain-witnesses"
  if [[ -s "${step}/chain" ]]; then
    campaign_stream_attempt_row "${dir}" null "its causal chain is open: \
${open} value(s) its path's fatal condition rests on no attested producer \
made (openChain); EXPLORE grows the $(grep -c '' "${step}/chain") \
producer(s) they name and attempts its witnesses again" 0 false
  else
    campaign_stream_attempt_row "${dir}" null "its causal chain is open: \
${open} value(s) its path's fatal condition rests on no attested producer \
made (openChain), and none names a producer EXPLORE could grow" 0 false
  fi
}

# The verdicts on the confirmation replays that returned (<step>/confirms:
# "<attempt> <exit>"), each decided (campaign_confirm_decide, refuted by
# campaign_confirm_settle) in attempt order; the earliest attempt confirmed,
# by attempt order and not by finish time, is the witness, and a later one
# confirmed in the same landing states it (supersededBy).  The decided
# attempts are <step>/decided.
campaign_stream_decide() {
  local step=$1 attempt replayed dir confirm chosen="" started
  while read -r attempt replayed; do
    dir="${iteration_dir}/witness-attempts/${attempt}"
    confirm="${campaign_root}/witness-confirm/${attempt}"
    campaign_confirm_decide "${dir}" "${confirm}" "${replayed}"
    campaign_confirm_settle "${iteration_dir}" "${dir}"
    printf '%s\n' "${attempt}" >>"${step}/decided"
    started=$(cat "${confirm}/started-at")
    if [[ -n "${chosen}" \
        && "$(jq -r '.confirmed' "${dir}/confirm.json")" == true ]]; then
      campaign_stream_attempt_row "${dir}" true "$(jq -r '.reason' \
        "${dir}/confirm.json")" "$(( $(date +%s%3N) - started ))" false \
        "${chosen}"
      continue
    fi
    campaign_stream_confirmed "${step}" "${dir}" \
      "$(( $(date +%s%3N) - started ))"
    [[ -n "${chosen}" || ! -s "${step}/witnessed" ]] || chosen=${attempt}
  done < <(LC_ALL=C sort "${step}/confirms")
}

# The verdict on attempt <dir>'s claim (<dir>/confirm.json), its replay
# <confirm_ms> long: its row, and, confirmed, the witness of <step>.
campaign_stream_confirmed() {
  local step=$1 dir=$2 confirm_ms=$3 confirmed
  confirmed=$(jq -r '.confirmed' "${dir}/confirm.json")
  campaign_stream_attempt_row "${dir}" "${confirmed}" \
    "$(jq -r '.reason' "${dir}/confirm.json")" "${confirm_ms}" \
    "$([[ "${confirmed}" == true ]] && echo true || echo false)"
  [[ "${confirmed}" != true ]] \
    || campaign_stream_witnessed "${step}" "${dir}" "${confirmed}"
}

# Attempt <dir> accepted, confirmed=<confirmed>: the witness that ends the
# exploration (<step>/witnessed, <step>/attempt).
campaign_stream_witnessed() {
  local step=$1 dir=$2 confirmed=$3
  printf '%s\n' "${dir}" >"${step}/attempt"
  jq -r --arg confirmed "${confirmed}" '"an admitted replay (\(.witnesses
    | join(" "))) observed the fatal at the declared occurrence and COMPOSE
    over the corpus as it stood published \(.claim) \(.findingKind) with its
    polarity deciding (\(.dir)), confirmed=\($confirmed)"' \
    "${dir}/attempt.json" | tr '\n' ' ' | sed 's/  */ /g' >"${step}/witnessed"
  campaign_log "witness attempt $(basename "${dir}") accepted: the \
exploration ends"
}

# One attempt's row of witness_attempts.jsonl, once its outcome is known:
# what it composed (attempt.json) and confirmed (true, false, or null:
# none), the confirmation's reason, how long its replay took, whether it is
# the accepted witness, and the earlier attempt that is, when one confirmed
# in the same landing (supersededBy).
campaign_stream_attempt_row() {
  local dir=$1 confirmed=$2 reason=$3 confirm_ms=$4 accepted=$5
  local superseded=${6:-}
  jq -c --argjson confirmed "${confirmed}" --arg reason "${reason}" \
    --argjson confirmMillis "${confirm_ms}" --argjson accepted "${accepted}" \
    --arg superseded "${superseded}" \
    '. + {confirmed: $confirmed, confirmReason: $reason,
      confirmMillis: $confirmMillis, accepted: $accepted}
     + (if $superseded == "" then {} else {supersededBy: $superseded} end)' \
    "${dir}/attempt.json" >>"${attempts}"
}

# The queued obligations, cancelled: out of the queue, their worker
# directories (made at enqueue, holding nothing yet) gone, none of them in
# flight any more, each named in exploration.json; the queued REPLAYs of
# obligations already solved, GROW's queued re-runs and the queued
# confirmations stay.
campaign_stream_drop() {
  local entry kind round id
  local -a kept=()
  for entry in "${stream_queue[@]}"; do
    read -r kind round id _ <<<"${entry}"
    if [[ "${kind}" != OBLIGATION ]]; then
      kept+=("${entry}")
      continue
    fi
    stream_cancelled+=("${id}")
    unset 'stream_flying[$id]'
    rmdir -- "${iteration_dir}/${round}/${id}"
  done
  stream_queue=("${kept[@]}")
}

# WITNESSED, or CAMPAIGN_BUDGET_REACHED: the queue cancelled, and everything
# this campaign still runs ended -- its process trees here, its workers on
# every peer -- and moved out of the iteration with what it staged, as is
# what returned after the last step began, never landed, and an obligation
# solved whose REPLAY is still queued; a confirmation
# queued, running or undecided is its attempt's row, reaped; a GROW re-run
# queued, or returned and not swapped in, is dropped, its directory with
# it (a witness's confirmation holds every swap, so the sessions its attempt
# composed are all still in the corpus).  At a witness
# the sessions that landed after its attempt composed (not in its
# corpus.txt) leave the corpus for explore-reaped/after-witness/: the corpus
# COMPOSE reads next is exactly the one the accepted attempt read.
campaign_stream_end() {
  local pid entry kind round id host status session dir
  local -a dropped=() confirms=() withdrawn=() dropped_reruns=()
  for pid in "${!stream_jobs[@]}"; do
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    dropped+=("${kind} ${round} ${id}")
  done
  for entry in "${stream_pending[@]}"; do
    read -r kind round id host status session <<<"${entry}"
    dropped+=("${kind} ${round} ${id}")
  done
  campaign_stream_drop
  for entry in "${stream_hard[@]}"; do
    read -r kind round id _ <<<"${entry}"
    dropped+=("${kind} ${round} ${id}")
  done
  stream_hard=()
  for entry in "${stream_queue[@]}"; do
    read -r kind round id _ <<<"${entry}"
    case "${kind}" in
      CONFIRM) confirms+=("${id}") ;;
      REPLAY) dropped+=("${kind} ${round} ${id}") ;;
      # A GROW re-run never run: its exposing round's growth and the
      # obligations it holds are owed.
      RERUN) dropped_reruns+=("${round} ${id}") ;;
    esac
  done
  stream_queue=()
  # So is one that returned and never swapped in (a confirmation held it,
  # campaign_stream_swap_due): the exposing session stays in the corpus.
  # Either's directory, with what it staged, leaves its worker.
  for entry in "${stream_swaps[@]}"; do
    read -r round id _ <<<"${entry}"
    dropped_reruns+=("${round} ${id}")
  done
  stream_swaps=()
  for entry in "${dropped_reruns[@]}"; do
    read -r round id <<<"${entry}"
    stream_reruns_dropped+=("${id}")
    mkdir -p "${campaign_root}/explore-reaped/${round}"
    mv -- "$(campaign_stream_rerun_dir "${round}" "${id}")" \
      "${campaign_root}/explore-reaped/${round}/${id}"
  done
  campaign_stream_reap
  for entry in "${dropped[@]}"; do
    read -r kind round id <<<"${entry}"
    if [[ "${kind}" == CONFIRM ]]; then
      confirms+=("${id}")
      continue
    fi
    stream_reaped+=("${id}")
    dir="${iteration_dir}/${round}/${id}"
    [[ "${kind}" != RERUN ]] \
      || dir=$(campaign_stream_rerun_dir "${round}" "${id}")
    mkdir -p "${campaign_root}/explore-reaped/${round}"
    mv -- "${dir}" "${campaign_root}/explore-reaped/${round}/${id}"
  done
  for id in "${confirms[@]}"; do
    campaign_stream_attempt_row "${iteration_dir}/witness-attempts/${id}" \
      null "its confirmation was reaped when the exploration ended \
${stream_stop}" 0 false
  done
  if [[ "${stream_stop}" == WITNESSED ]]; then
    while read -r session; do
      mkdir -p "${campaign_root}/explore-reaped/after-witness"
      mv -- "${sessions}/${session}" \
        "${campaign_root}/explore-reaped/after-witness/${session}"
      withdrawn+=("${session}")
    done < <(find "${sessions}" -mindepth 1 -maxdepth 1 -type d \
        -printf '%f\n' | LC_ALL=C sort \
      | LC_ALL=C comm -23 - "${campaign_witness_attempt}/corpus.txt")
  fi
  stream_confirms_reaped=("${confirms[@]}")
  stream_after_witness=("${withdrawn[@]}")
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
  for pid in "${!stream_jobs[@]}"; do
    campaign_stream_release "${pid}"
  done
  stream_step_pid=""
  stream_ticker=""
}

# The charge the head took for job <pid> (campaign_stream_admit_host),
# released: the job ended, or was ended.
campaign_stream_release() {
  local kind round id host
  [[ -n "${stream_job_charge[$1]:-}" ]] || return 0
  read -r kind round id host _ <<<"${stream_jobs[$1]}"
  campaign_host_release "${host}" "${stream_job_charge[$1]}"
  unset 'stream_job_charge[$1]'
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
# fewer than its share of the pool (campaign_stream_has_slot)
# and a host admits it: an obligation's solve, an obligation's REPLAY, a
# GROW re-run or a confirmation on the next host of the pool, round-robin,
# whose memory ledger admits one more start and that runs fewer of this
# campaign's than it has cores (campaign_stream_admit_host).  While GROW
# owes re-runs or swaps, no obligation's solve starts: a replay and a
# confirmation read no corpus.
campaign_stream_dispatch() {
  local entry
  while (( ${#stream_queue[@]} + ${#stream_hard[@]} > 0 )); do
    campaign_stream_collect_jobs
    # The hard lane once no other start waits (campaign_solver_first_tier_ms).
    entry=${stream_queue[0]:-${stream_hard[0]:-}}
    [[ -n "${entry}" ]] || return 0
    [[ "${entry}" != OBLIGATION\ * && "${entry}" != HARD\ * ]] \
      || (( stream_hold == 0 )) || return 0
    campaign_stream_has_slot || return 0
    campaign_stream_admit_host "${entry%% *}" || return 0
    if (( ${#stream_queue[@]} > 0 )); then
      stream_queue=("${stream_queue[@]:1}")
    else
      stream_hard=("${stream_hard[@]:1}")
    fi
    campaign_stream_start "${entry}" "${stream_admitted_host}"
  done
}

# Whether this exploration runs fewer starts than its share of a shared pool
# (stream_shared_pool): the slots its hosts hold at the replay charge it
# measured (campaign_pool_slots, campaign_stream_charge_mb) over the sharing
# explorations whose ledger entry is fresh (this one's among them,
# campaign_stream_enroll), at least one, read again at every start -- so the
# share follows the measured need, grows as others end and shrinks as others
# begin, and what already runs past it runs out.  Always outside a shared
# pool.  1 when it runs its share, said once for every share it waits at.
campaign_stream_has_slot() {
  local fresh sharers share slots charge
  [[ "${stream_shared_pool}" == true ]] || return 0
  fresh=$(( $(date +%s) - campaign_head_reservation_stale_s ))
  sharers=$(find "${campaign_host_gate_root}/explorations" -maxdepth 1 \
    -type f -newermt "@${fresh}" | grep -c '') || sharers=0
  (( sharers > 0 )) || sharers=1
  charge=$(campaign_stream_charge_mb)
  # Its hosts' MemTotal and cores never move: their slots are read once per
  # charge.
  [[ -n "${stream_pool_slots[${charge}]:-}" ]] \
    || stream_pool_slots[${charge}]=$(campaign_pool_slots "${charge}" \
      "${stream_hosts[@]}")
  slots=${stream_pool_slots[${charge}]}
  share=$(( slots / sharers ))
  (( share > 0 )) || share=1
  (( ${#stream_jobs[@]} >= share )) || return 0
  if [[ "${stream_share_said}" != "${share}" ]]; then
    campaign_log "waiting for a slot: ${#stream_jobs[@]} start(s) run, this \
exploration's share ${share} of its hosts' ${slots} slot(s) at ${charge} MB, \
shared by ${sharers} exploration(s)"
    stream_share_said=${share}
  fi
  return 1
}

# A sharing exploration's ledger entry, fresh while its head lives
# (campaign_head_heartbeat) and gone when it ends (campaign_explore): what
# the explorations sharing the pool now count to share its slots
# (campaign_stream_has_slot).  None outside a shared pool.
campaign_stream_enroll() {
  local dir="${campaign_host_gate_root}/explorations"
  [[ "${stream_shared_pool}" == true ]] || return 0
  mkdir -p "${dir}"
  campaign_stream_entry="${dir}/$(hostname -s).${BASHPID}.$(date +%s)"
  : >"${campaign_stream_entry}"
}

campaign_stream_unenroll() {
  [[ -z "${campaign_stream_entry}" ]] || rm -f -- "${campaign_stream_entry}"
  campaign_stream_entry=""
}

# Picks the host for one start of <kind> (OBLIGATION, REPLAY, RERUN or
# CONFIRM) and charges it there (stream_admitted_host, stream_admitted_mb):
# the pool from the host after the last one chosen, each start charged its
# need for as long as it runs (campaign_stream_charge_mb); an OBLIGATION
# goes first to a host where this
# campaign's solver still serves (campaign_stream_warm: one started there
# within the solver's idle time), whose question is then answered without a
# solver of its own to start and its corpus to read.  A host is skipped
# while it runs as many of this campaign's as it has cores, or while the
# ledger has no room on it (campaign_host_try_start: no start leaves a host
# more than CAUSYNTH_HOST_MAX_USED_PCT charged or full, and none takes a
# head's room).
# 1 when no host has room now, said once per wait.
campaign_stream_admit_host() {
  local kind=$1 host turn count pass is status=0 mb
  count=${#stream_hosts[@]}
  for pass in warm cold; do
    [[ "${pass}" == cold || "${kind}" == OBLIGATION ]] || continue
    mb=$(campaign_stream_charge_mb "${kind}" "${pass}")
    for ((turn = 0; turn < count; turn++)); do
      host=${stream_hosts[$(( (stream_next_host + turn) % count ))]}
      # An obligation tries each host once, in the pass of its warmth.
      is=cold
      [[ "${kind}" != OBLIGATION ]] || ! campaign_stream_warm "${host}" \
        || is=warm
      [[ "${is}" == "${pass}" ]] || continue
      campaign_stream_try_host "${host}" "${turn}" "${mb}" "${kind}" \
        && return 0
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

# What one start of <kind> of the pool is charged now, on a host of <warmth>
# (warm: this campaign's solver likely still serves there, campaign_stream_warm;
# else cold): an OBLIGATION's solve on a warm host what its question's z3 run
# holds (campaign_question_mb; the host's solver JVM is charged on its own),
# on a cold one what a solver JVM starts at (campaign_solver_start_mb: its
# question is answered in a JVM of its own, under this charge, when its host
# has no room for its solver); either grows as its JVM does
# (campaign_watch_workload); a replay -- a
# REPLAY, a RERUN, a CONFIRM, and the pool's slots (campaign_stream_has_slot)
# -- the campaign's measured replay need (campaign_replay_need_mb), or the
# typical replay's once enough returned (campaign_replay_typical), at most
# half a host's ceiling (campaign_replay_charge_mb).  A solve charged a
# replay waited for room it never used (HG5A-11, hdfs-adhoc-19: its eight
# obligations waited 12 of EXPLORE's 13 minutes for room for a 2500 MB
# replay each, and their solver refused all eight: none replayed).
campaign_stream_charge_mb() {
  if [[ "${1:-}" == OBLIGATION && "${2:-cold}" == warm ]]; then
    printf '%s\n' "${campaign_question_mb}"
  elif [[ "${1:-}" == OBLIGATION || "${1:-}" == HARD ]]; then
    campaign_solver_need_mb "${sessions:-}"
  else
    local need
    need=$(campaign_replay_need_mb)
    (( campaign_replay_typical_mb == 0 \
       || campaign_replay_typical_mb >= need )) \
      || need=${campaign_replay_typical_mb}
    campaign_replay_charge_mb "${need}"
  fi
}

# How many of a campaign's solves one host holds at once.  Its solver
# answers one question at a time (ObligationSolverMain --serve), so a second
# keeps it busy and more add no answer, only their charges while they wait
# in its queue: EX1-adhoc-07c, 13-18 questions waiting per lift, 512 MB each,
# held 7-9 GB of every lift's ledger and no replay started for ten minutes.
# The rest wait uncharged in the pool's queue.
campaign_stream_solves_per_host=2

# How many hard-lane solves (campaign_solver_first_tier_ms) one host holds at
# once: each runs its z3 race for up to the full budget in a JVM of its own.
campaign_stream_hard_per_host=1

# One host's admission for campaign_stream_admit_host, <turn> places after
# the host after the last one chosen, charged <mb>, for a start of <kind>
# (an OBLIGATION only while the host holds fewer than
# campaign_stream_solves_per_host): 0 with it charged and chosen.
campaign_stream_try_host() {
  local host=$1 turn=$2 mb=$3 kind=${4:-} count=${#stream_hosts[@]} status=0
  campaign_stream_has_cores "${host}" || return 1
  [[ "${kind}" != OBLIGATION ]] || (( ${stream_host_solves[${host}]:-0} \
    < campaign_stream_solves_per_host )) || return 1
  [[ "${kind}" != HARD ]] || (( ${stream_host_hard[${host}]:-0} \
    < campaign_stream_hard_per_host )) || return 1
  campaign_host_try_charge "${host}" "${mb}"
  case "${status}" in
    0)
      stream_admitted_host=${host}
      stream_admitted_mb=${mb}
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
# weaves a new one; this start keeps its own) -- an obligation's REPLAY on
# the ones its solve started on, which its entry carries
# (campaign_stream_ended) -- charged what campaign_stream_admit_host charged
# (stream_admitted_mb), its own until it returns.  Where it started is
# stated in its worker: host.txt, a REPLAY's replay-host.txt beside its
# solve's.
campaign_stream_start() {
  local entry=$1 host=$2 kind round id session worker need
  local classes=${stream_classes} plan=${stream_plan} started=host.txt
  local -a work=()
  read -r kind round id session <<<"${entry}"
  need=$(campaign_replay_need_mb)
  case "${kind}" in
    OBLIGATION)
      worker="${iteration_dir}/${round}/${id}"
      work=("${id}" "${iteration_dir}/${round}/obligations.jsonl" \
        "${sessions}" "${worker}" "${stream_admitted_mb}") ;;
    HARD)
      worker="${iteration_dir}/${round}/${id}"
      started=hard-host.txt
      work=("${id}" "${iteration_dir}/${round}/obligations.jsonl" \
        "${sessions}" "${worker}" "${stream_admitted_mb}" HARD) ;;
    REPLAY)
      worker="${iteration_dir}/${round}/${id}"
      read -r classes plan <<<"${session}"
      session=""
      started=replay-host.txt
      work=("${id}" "${classes}" "${worker}" "${worker}/sessions" \
        "${plan}" "${stream_admitted_mb}" "${need}") ;;
    CONFIRM)
      # On the generation current now, as an obligation's replay; the
      # replay's own worker is the job's, its logs beside it.
      worker="${campaign_root}/witness-confirm/${id}/worker"
      date +%s%3N >"$(dirname "${worker}")/started-at"
      work=("$(dirname "${worker}")" "${classes}" "${plan}" \
        "${stream_admitted_mb}" "${need}") ;;
    RERUN)
      worker=$(campaign_stream_rerun_dir "${round}" "${id}")
      work=("${id}" "${classes}" "${worker}" "${worker}/sessions" \
        "${plan}" "${stream_admitted_mb}" "${need}") ;;
  esac
  printf '%s\n' "${host}" >"${worker}/${started}"
  [[ "${kind}" != OBLIGATION ]] || stream_solver_seen[${host}]=$(date +%s)
  campaign_stream_job "${kind}" "${host}" "${campaign_host_charge_id}" \
    "${id}" "${worker}" "${work[@]}" &
  stream_jobs[$!]="${kind} ${round} ${id} ${host} ${session}"
  stream_job_charge[$!]=${campaign_host_charge_id}
  stream_job_worker[$!]=${worker}
  stream_job_tree[$!]="${classes} ${plan}"
  stream_host_jobs[${host}]=$(( ${stream_host_jobs[${host}]:-0} + 1 ))
  [[ "${kind}" != OBLIGATION ]] \
    || stream_host_solves[${host}]=$(( ${stream_host_solves[${host}]:-0} + 1 ))
  [[ "${kind}" != HARD ]] \
    || stream_host_hard[${host}]=$(( ${stream_host_hard[${host}]:-0} + 1 ))
}

# The jobs that ended, taken without waiting (campaign_stream_ended), between
# two starts of a dispatch: an obligation solved SAT_MODEL_READY has its
# REPLAY first in the queue before the next start, not behind the burst of
# starts the dispatch is in (MCH1: each start's ledger round over ten lifts
# took about a second, and REPLAYs started 13-50 s after their solve).
campaign_stream_collect_jobs() {
  local pid status
  for pid in "${!stream_jobs[@]}"; do
    ! kill -0 "${pid}" 2>/dev/null || continue
    status=0
    wait "${pid}" || status=$?
    campaign_stream_ended "${pid}" "${status}"
  done
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
# (campaign_stream_step_done); or a job, whose host has its slot and its
# charge back (campaign_stream_release) and whose replay's peak joins the
# measured need (campaign_replay_measured).  An obligation its solver
# answered SAT_MODEL_READY is owed its replay: its REPLAY goes first in the
# queue at once, never waiting for a step -- still in flight, still within
# the exploration's share and its host's cores -- on the class tree and plan
# its solve started on, charged then -- behind only a witness's confirmation
# and GROW's re-runs queued first, which end the exploration or hold every
# solve (hdfs-11741 AR1: 473 replays of solves that returned later started
# ahead of the witness's confirmation, which ran four hours after the witness
# landed).  Every other return waits in stream_pending for the next step to
# land it.
campaign_stream_ended() {
  local pid=$1 status=$2 kind round id host session worker answer
  if [[ "${pid}" == "${stream_ticker}" ]]; then
    stream_ticker=""
  elif [[ "${pid}" == "${stream_step_pid}" ]]; then
    campaign_stream_step_done "${status}"
  else
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    worker=${stream_job_worker[${pid}]}
    campaign_stream_release "${pid}"
    campaign_replay_measured "${worker}"
    stream_host_jobs[${host}]=$(( stream_host_jobs[${host}] - 1 ))
    [[ "${kind}" != OBLIGATION ]] \
      || stream_host_solves[${host}]=$(( stream_host_solves[${host}] - 1 ))
    [[ "${kind}" != HARD ]] \
      || stream_host_hard[${host}]=$(( stream_host_hard[${host}] - 1 ))
    answer=""
    [[ "${status}" -ne 0 || ( "${kind}" != OBLIGATION && "${kind}" != HARD ) ]] \
      || answer=$(jq -r '"\(.verdict // "")|\(.detail // "")"' \
        "${worker}/obligation_result.jsonl" 2>/dev/null) || answer=""
    if [[ "${answer}" == SAT_MODEL_READY\|* ]]; then
      campaign_log "obligation ${id}: solved on ${host}, its replay queued"
      campaign_stream_queue_replay \
        "REPLAY ${round} ${id} ${stream_job_tree[${pid}]}"
    elif [[ "${kind}" == OBLIGATION \
        && "${answer}" == NOT_ADMITTED\|SOLVER_TIMEOUT\ * ]] \
        && campaign_solver_two_lanes; then
      # Undecided at the first budget: still in flight, asked again in the
      # hard lane; its first answer kept beside its worker's.
      campaign_log "obligation ${id}: undecided in \
$(campaign_solver_first_ms) ms on ${host}; asked again at the full \
${solver_timeout_ms} ms once no other start waits"
      mv -f -- "${worker}/obligation_result.jsonl" \
        "${worker}/obligation_result.first.jsonl"
      stream_hard+=("HARD ${round} ${id}")
    else
      stream_pending+=("${kind} ${round} ${id} ${host} ${status} ${session}")
    fi
    unset 'stream_jobs[$pid]' 'stream_job_worker[$pid]' 'stream_job_tree[$pid]'
  fi
}

# Puts one REPLAY first in the queue, behind the CONFIRM and RERUN entries
# that lead it (campaign_stream_ended).
campaign_stream_queue_replay() {
  local at=0
  while (( at < ${#stream_queue[@]} )) \
      && [[ "${stream_queue[at]}" == CONFIRM\ * \
         || "${stream_queue[at]}" == RERUN\ * ]]; do
    at=$((at + 1))
  done
  stream_queue=("${stream_queue[@]:0:at}" "$1" "${stream_queue[@]:at}")
}

# What returned since the last step began, landed: each obligation's
# verdict into the ledger and the session it staged into stream_staged
# (campaign_stream_move); each re-run's into stream_swaps, for once no
# obligation runs; each confirmation into `confirms`, for the step to decide.
campaign_stream_land() {
  local entry kind round id host status session worker verdict
  for entry in "${stream_pending[@]}"; do
    read -r kind round id host status session <<<"${entry}"
    if [[ "${kind}" == RERUN ]]; then
      stream_swaps+=("${round} ${id} ${session} ${status}")
      continue
    fi
    if [[ "${kind}" == CONFIRM ]]; then
      confirms+=("${id} ${status}")
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
    if [[ "${kind}" == HARD && "${verdict}" == NOT_ADMITTED ]] && jq -e \
        '.detail // "" | startswith("SOLVER_TIMEOUT")' \
        "${worker}/obligation_result.jsonl" >/dev/null 2>&1; then
      jq -c --arg host "${host}" '{obligationId, detail, host: $host}' \
        "${worker}/obligation_result.jsonl" \
        >>"${iteration_dir}/solver_timeouts.jsonl"
    fi
    [[ -z "${session}" ]] \
      || stream_staged+=("${worker} ${worker}/sessions ${session}")
    cat -- "${worker}/obligation_result.jsonl" >>"${results}"
    stream_dirty=1
  done
  stream_pending=()
}

# Whether GROW's swaps are due: every re-run it owes has returned, no
# obligation's solve runs that started before them (a solver reads the
# corpus; a REPLAY reads none), and no witness's confirmation is queued,
# runs or waits for its verdict (stream_confirming): it confirms against the
# corpus its attempt composed, and a swap would withdraw the session it
# confirms (solr-bugs-tra-start-overwrite Z2M, Z2N: the witness was the
# exposing session, withdrawn a second after its confirmation was queued;
# its re-run did not take the flip, and in Z2N the confirmed claim's final
# COMPOSE lost it).  A confirmed one ends the exploration with
# the swaps owed (campaign_stream_end); a refuted one lets them swap.
campaign_stream_swap_due() {
  local job
  (( ${#stream_swaps[@]} > 0 && ${#stream_swaps[@]} == stream_hold \
     && ${#stream_confirming[@]} == 0 )) || return 1
  for job in "${stream_jobs[@]}"; do
    [[ "${job}" != OBLIGATION\ * && "${job}" != HARD\ * ]] || return 1
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

# The exposures of a round's growth.jsonl, one `obligation grown session`
# line each, sorted: an EXPOSED_REGION row's region, an UNPLANNED_INPUT
# row's `<task> <input>#<k>`.
campaign_exposures() {
  jq -r 'select(.kind == "EXPOSED_REGION" or .kind == "UNPLANNED_INPUT")
         | [.obligationId, (.regionId // "\(.taskId) \(.symbol)#\(.k)"),
            .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

# The DOORS_ONLY_UNPAUSED rows of a round's growth.jsonl (a doors-only
# occurrence a value demand reached, ClosurePlanner#plan), one `obligation
# occurrence session` line each, sorted; the obligation and session are ""
# where no admitted focused replay ran it.
campaign_unpauses() {
  jq -r 'select(.kind == "DOORS_ONLY_UNPAUSED")
         | [.obligationId, .occurrence, .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

# GROW (PIPELINE §7.8): a region a replay reached without its hooks, a
# marker invocation only a flipped world made, or a doors-only occurrence a
# value demand reached is planned -- the region woven in -- and the replay
# that exposed it is run again under the same world, so a later round's
# closure sees the region's decisions and exports, flips the new root, or
# takes the occurrence's values.
#
# One GROW is one GENERATION of the plan and the class tree:
# ExposedRegionPlanMain writes the generation's whole plan -- the one before
# it with the reached doors-only occurrences' marks dropped, each grown
# invocation an input of its task's row, plus the task rows the exposed
# regions need (admissionBasis EXPOSED_BY) -- as a new file, kept beside the
# round too (grown_plan.jsonl); the iteration's plan and the seed plan are
# its links from now on, and INSTRUMENT weaves it into the generation's own
# tree where it has new task rows.  A start takes the generation current
# when it starts (campaign_stream_start), so whatever already runs keeps the
# plan and the classes it started on.  Each exposing obligation's replay is
# queued first, to re-run -- on whichever host of the pool admits it, as an
# obligation does -- in a directory of its own beside its worker; until
# every re-run has returned and swapped its session in
# (campaign_stream_swap), no obligation starts and no round is planned.
campaign_stream_grow() {
  local round_dir=$1 status=0 generation obligation_id session rerun
  local growth=${2:-${round_dir}/growth.jsonl} rerun_count=0
  local worker file unpaused
  # An exposure names the obligation whose replay is re-run.  One that names
  # none was exposed by the seed replay, and the seed is not re-run: the
  # recording reached that region too, so it is PLAN's to name, not GROW's.
  [[ -z "$(campaign_exposures "${growth}" | awk -F'\t' '$1 == ""')" ]] \
    || campaign_fail EXPLORE ExploreMain "${growth}" \
      "an exposure names no obligation; only a focused replay's exposure \
can be grown into"
  stream_generation=$((stream_generation + 1))
  generation="${iteration_dir}/generations/g${stream_generation}"
  mkdir -p "${generation}"
  # A doors-only occurrence a value demand reached runs whole from this
  # generation on: its task row loses the mark.
  unpaused=$(campaign_unpauses "${growth}" | cut -f2 | jq -R . | jq -s -c .)
  jq -c --argjson unpaused "${unpaused}" \
    'if .doorsOnly == true and (.occurrenceId as $at
       | any($unpaused[]; . == $at)) then del(.doorsOnly) else . end' \
    "${stream_plan}" >"${generation}/unpaused_plan.jsonl"
  if [[ -n "$(campaign_exposures "${growth}")" ]]; then
    run_capturing_status run_java_main \
      edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain \
      --iteration "${iteration_dir}" \
      --static-scope-map "${causynth_static_scope_map}" \
      --plan "${generation}/unpaused_plan.jsonl" \
      --growth "${growth}" \
      --output "${generation}/execution_task_plan.jsonl" \
      >"${round_dir}/grow-stdout.log" 2>"${round_dir}/grow-stderr.log"
    [[ "${status}" -eq 0 ]] || campaign_fail EXPLORE ExposedRegionPlanMain \
      "${round_dir}/grow-stderr.log" \
      "GROW's planner failed with exit ${status}: \
$(campaign_thrown "${round_dir}/grow-stderr.log")"
    rm -f -- "${generation}/unpaused_plan.jsonl"
  else
    mv -- "${generation}/unpaused_plan.jsonl" \
      "${generation}/execution_task_plan.jsonl"
  fi
  require_nonempty "the grown generation's plan" \
    "${generation}/execution_task_plan.jsonl"
  ln -f "${generation}/execution_task_plan.jsonl" \
    "${round_dir}/grown_plan.jsonl"
  ln -f "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/execution_task_plan.jsonl"
  ln -f "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  stream_plan="${generation}/execution_task_plan.jsonl"
  # Only new task rows are new weaving: a grown input stands at the hook its
  # marker's planned input has (the weave hooks a local definition by
  # method, unit and local, never by invocation), and dropping a doors-only
  # mark weaves nothing.
  if jq -e -s 'any(.[]; .kind == "EXPOSED_REGION")' "${growth}" \
      >/dev/null; then
    campaign_log "$(basename "${round_dir}"): grown by \
$(campaign_exposures "${growth}" | cut -f2 | LC_ALL=C sort -u \
  | paste -sd, -) ($(campaign_exposures "${growth}" | grep -c '') \
exposure(s)), $(jq 'length' <<<"${unpaused}") doors-only occurrence(s) run \
whole; weaving generation g${stream_generation}"
    campaign_instrument "${iteration_dir}" \
      "${generation}/instrumented-classes"
    stream_classes="${generation}/instrumented-classes"
  else
    campaign_log "$(basename "${round_dir}"): grown by \
$(campaign_exposures "${growth}" | cut -f2 | LC_ALL=C sort -u \
  | paste -sd, -) ($(campaign_exposures "${growth}" | grep -c '') \
exposure(s)), $(jq 'length' <<<"${unpaused}") doors-only occurrence(s) run \
whole; generation g${stream_generation} weaves nothing new"
  fi
  while IFS=$'\t' read -r obligation_id session; do
    worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
      "${obligation_id}") || exit 1
    rerun="${worker}/grow-$(basename "${round_dir}")/${obligation_id}"
    mkdir -p "$(dirname "${rerun}")"
    mkdir "${rerun}" || campaign_fail EXPLORE CAMPAIGN "${rerun}" \
      "obligation ${obligation_id} was already re-run for this round"
    # What a replay reads of its worker: the focus row, the schedule cut and
    # the edges its world's pairings hold it to.
    for file in focused_task.jsonl schedule_prefix.jsonl \
        schedule_suffix.jsonl expected_edges.jsonl; do
      [[ ! -e "${worker}/${file}" ]] || ln "${worker}/${file}" "${rerun}/"
    done
    stream_queue=("RERUN $(basename "${round_dir}") ${obligation_id} \
${session}" "${stream_queue[@]}")
    stream_hold=$((stream_hold + 1))
    rerun_count=$((rerun_count + 1))
  done < <({ campaign_exposures "${growth}"; campaign_unpauses "${growth}"; } \
    | awk -F'\t' '$1 != ""' | cut -f1,3 | LC_ALL=C sort -u)
  # A doors-only occurrence no focused replay ran is re-run by none: the
  # next round is owed all the same, so a closure still demanding it states
  # it (BLOCKING at the fixed point, ExploreMain) rather than the driver
  # ending on a plan that changed under it.
  (( rerun_count > 0 )) || stream_dirty=1
}

# The directory one exposing obligation's re-run for <round> runs in.
campaign_stream_rerun_dir() {
  local round=$1 obligation_id=$2 worker
  worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
    "${obligation_id}") || exit 1
  printf '%s/grow-%s/%s\n' "${worker}" "${round}" "${obligation_id}"
}

# Every re-run that returned, swapped in -- once no obligation runs, since a
# solver reads the corpus as it starts.  The queue stays first, in flight
# for the next round, which proposes only what none of it asks: an
# obligation it holds cut from an exposing session is answered by its solver
# by name (the corpus no longer states its path), and a later round asks it
# again of the re-run's session.
#
# One swap: the exposing session leaves the corpus for
# <worker>/before-<round>/ with a copy of what its replay wrote, the
# re-run's files become the worker's, its session is staged to land with
# the others (campaign_stream_move), and its verdict replaces the
# obligation's row in the ledger.  A worker file is renamed over or
# removed, never moved aside: a peer whose NFS client looked its name up
# lately opens the inode it cached, and one still linked aside reads as
# current (Z2M: the import gate on lift06, 8 s after the swap, read the
# exposing session's answer and found no worker stating the re-run's focus
# row); a deleted one fails stale and the client looks the name up again,
# as campaign_write_whole relies on.
campaign_stream_swap() {
  local swap round id session status worker rerun aside file
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
        question.asked stdout.log stderr.log host.txt replay-stdout.log \
        replay-stderr.log replay-host.txt workload_rss_mb; do
      [[ ! -e "${worker}/${file}" ]] || cp -p -- "${worker}/${file}" "${aside}/"
      if [[ -e "${rerun}/${file}" ]]; then
        mv -f -- "${rerun}/${file}" "${worker}/${file}"
      else
        rm -f -- "${worker}/${file}"
      fi
    done
    session=$(jq -r '.sessionId // ""' "${worker}/obligation_result.jsonl")
    [[ -z "${session}" ]] \
      || stream_staged+=("${worker} ${rerun}/sessions ${session}")
    campaign_record_rerun "${iteration_dir}" "${id}" "${results}"
  done
  stream_hold=$((stream_hold - ${#stream_swaps[@]}))
  stream_swaps=()
  stream_dirty=1
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
  # No generation wove a tree of its own (grown inputs only, doors-only
  # marks dropped): its tree is still the iteration's.
  [[ "${stream_classes}" != "${iteration_dir}/instrumented-classes" ]] \
    || return 0
  rm -rf -- "${iteration_dir}/instrumented-classes"
  mv -- "${stream_classes}" "${iteration_dir}/instrumented-classes"
  for generation in "${iteration_dir}"/generations/g*; do
    rm -rf -- "${generation}/instrumented-classes"
  done
}

# exploration.json: how EXPLORE ended, how many rounds and head steps it
# took, every COMPOSE attempt at a witness (by attempt order), every
# obligation it dropped -- cancelled from the queue, or reaped before it
# landed -- by id, the GROW re-runs dropped (queued, or returned and not
# swapped in) and the confirmations reaped, whether a round was due when
# the budget stopped it, and the sessions that left the corpus after the
# witness's attempt composed: what EMIT judges a cut by
# (campaign_exploration_cut).
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
    --argjson afterWitness "$(printf '%s\n' "${stream_after_witness[@]}" \
      | jq -R 'select(length > 0)' | jq -s -c .)" \
    --argjson rerunsDropped "$(printf '%s\n' \
      "${stream_reruns_dropped[@]}" | jq -R 'select(length > 0)' \
      | jq -s -c .)" \
    --argjson confirmsReaped "$(printf '%s\n' \
      "${stream_confirms_reaped[@]}" | jq -R 'select(length > 0)' \
      | jq -s -c .)" \
    --argjson roundDue "${stream_round_due}" \
    --slurpfile attempts "${attempts}" \
    '{schemaVersion: 1, kind: "EXPLORATION", stop: $stop, detail: $detail,
      rounds: $rounds, steps: $steps, generations: $generations,
      answered: $answered,
      witnessAttempts: ($attempts | sort_by(.attempt)), cancelled: $cancelled,
      reaped: $reaped, rerunsDropped: $rerunsDropped,
      confirmsReaped: $confirmsReaped, roundDue: $roundDue,
      afterWitness: $afterWitness}' \
    >"${iteration_dir}/exploration.json"
}

# The declared bounds this campaign's search touched, as result.json's
# `bounded` (the owner's bound rule, RULES: a generous declared bound may cut
# the search only as a named, rare last resort, counted every round): null
# when none did, else {by: [the configuration key of each], detail}.  They
# are the wave budget (region_path_max_waves, the stop
# REGION_PATH_WAVE_BUDGET_REACHED); the paths a round cuts from per task
# (region_path_max_paths_per_region), only where the LAST round planned
# deferred some -- an earlier round's deferral is work the rounds after it
# read first, and a fixed point defers none -- and the world depth a round
# cuts from (region_path_max_world_depth), ObligationFactory's rows naming the
# bound in their subject; the tasks one anchor's closure plans (region_path_max_tasks:
# the last round's `truncated`, as campaign_stream_truncation judges it, since
# a later round plans what an earlier one left); the occurrences PLAN plans
# (schedule_max_jobs, the schedule index's `closureCut`); and the claims
# decided again after CONFIRM refuted one (campaign_max_claims).  A round's
# max-flips-per-path is no such bound -- the next round asks the decisions it
# left -- nor is the time budget (campaign_exploration_cut).
campaign_bounds() {
  local iteration_dir=$1 decided refutes=false
  decided=$(find "${campaign_final}/refuted" -mindepth 1 -maxdepth 1 \
    2>/dev/null | grep -c '' || true)
  [[ ! -s "${campaign_final}/confirm.json" ]] \
    || refutes=$(jq '.refutes == true' "${campaign_final}/confirm.json")
  jq -n -c \
    --slurpfile exploration <(cat "${iteration_dir}/exploration.json" \
      2>/dev/null) \
    --slurpfile index <(cat \
      "${iteration_dir}/runtime_workflow_schedule_index.json" 2>/dev/null) \
    --slurpfile rounds <(cat "${iteration_dir}"/obligations-*/\
explore_manifest.json 2>/dev/null) \
    --slurpfile gaps "${campaign_final}/gaps.json" \
    --slurpfile last <(cat "$(printf '%s\n' "${iteration_dir}"/obligations-* \
      | LC_ALL=C sort | tail -n 1)/gaps.jsonl" 2>/dev/null) \
    --slurpfile inputs <(cat "${iteration_dir}"/obligations-*/gaps.jsonl \
      2>/dev/null | grep -F 'unplanned-input-max=' || true) \
    --argjson decided "${decided}" --argjson refutes "${refutes}" \
    --argjson maxClaims "${campaign_max_claims}" '
    def bound($bound): select(.subject | test(" " + $bound + "=[0-9]+$"));
    def rows($bound): [$gaps[0].telemetryGaps[]?, $gaps[0].gaps[]?
      | bound($bound)];
    [$last[] | bound("max-paths-per-region")] as $paths
    | ([$inputs[] | bound("unplanned-input-max") | .subject] | unique)
      as $inputs
    | rows("max-world-depth") as $depth
    | rows("loop-body-bound") as $loops
    | ($rounds | last | .truncated // 0) as $truncated
    | ($index[0].closureCut // null) as $cut
    | [($rounds | last | .openArms // [])[] | select(.state == "BOUNDED")]
      as $armsBounded
    | [ (select($exploration[0].stop == "REGION_PATH_WAVE_BUDGET_REACHED")
         | {by: "region_path_max_waves", detail: $exploration[0].detail}),
        (select(($paths | length) > 0)
         | {by: "region_path_max_paths_per_region",
            detail: ("the last round deferred \($paths | length) task(s)"
              + " past \($paths[0].subject | sub(".* "; "")) recorded paths"
              + " that offer an owed arm")}),
        (select(($depth | length) > 0)
         | {by: "region_path_max_world_depth",
            detail: ("\($depth | length) task round(s) cut from no path"
              + " in a world deeper than"
              + " \($depth[0].subject | sub(".* "; ""))")}),
        (select(($loops | length) > 0)
         | {by: "loop_body_bound",
            detail: ("\($loops | length) path(s) at the anchor a loop"
              + " bound cut before they reached it, before or after they"
              + " left the way to the throw (bodies: " + ($loops | map(.subject
              | sub(".*="; "")) | unique | join(", ")) + ")")}),
        (select(($inputs | length) > 0)
         | {by: "unplanned_input_max",
            detail: ("\($inputs | length) marker invocation(s) past the"
              + " \($inputs[0] | sub(".*="; "")) of one occurrence GROW"
              + " plans inputs for stayed concrete, in any round")}),
        (select($truncated > 0)
         | {by: "region_path_max_tasks",
            detail: ("the last round planned its closure without"
              + " \($truncated) occurrence(s), at the task bound")}),
        (select(($armsBounded | length) > 0)
         | {by: "open_arm_max_refuted_worlds",
            detail: ("\($armsBounded | length) open decider arm(s) asked no"
              + " more past their refuted worlds: " + ($armsBounded
              | map("\(.siteId)=\(.outcome) of \(.anchor)") | join(", ")))}),
        (select($cut != null)
         | {by: "schedule_max_jobs",
            detail: ("PLAN planned the closure only to demand depth"
              + " \($cut.keptDepth): \($cut.occurrences) deeper"
              + " occurrence(s) not planned")}),
        (select($refutes and $decided >= $maxClaims)
         | {by: "campaign_max_claims",
            detail: ("the claim was decided again \($decided) time(s) and"
              + " the refuted claim is published")}) ]
    | if length == 0 then null
      else {by: map(.by), detail: (map(.detail) | join("; "))} end'
}

# THE ONE PLACE an end of the exploration is judged a cut, at EMIT, off
# exploration.json and the claim the final stages reached (owner 2026-10-04,
# only SAT or UNSAT: an UNSAT over a corpus missing arms says nothing about
# them).  It owed work where queued obligations were cancelled, unlanded
# jobs or confirmations reaped, GROW re-runs dropped with the exposing
# round's obligations, a round was due when the budget stopped it, or the
# planner could not hold the corpus (PLANNER_HEAP_EXCEEDED); WITNESSED
# owes the same, and a witness that stands (the claim a SAT_CANDIDATE,
# which CONFIRM validates) owes nothing -- one refuted (a false positive),
# followed by a claim composed again over the trimmed corpus with no new
# EXPLORE
# (campaign_next_claim), owes it all.  FIXED_POINT and the declared nesting
# bound REGION_PATH_WAVE_BUDGET_REACHED, which defines the explored space,
# owe nothing.  An exploration that owed work under a claim that is no
# SAT_CANDIDATE is one BLOCKING EXPLORATION_CUT row naming the stop and the
# counts, so EMIT publishes no UNSAT over it (RUN_DEFECT); under a
# SAT_CANDIDATE the row is DIAGNOSTIC.
campaign_exploration_cut() {
  local iteration_dir=$1 claim
  [[ -s "${iteration_dir}/exploration.json" ]] || return 0
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  jq -c --arg claim "${claim}" --arg epoch "$(basename "${iteration_dir}")" '
    (.cancelled // [] | length) as $c | (.reaped // [] | length) as $r
    | (.confirmsReaped // [] | length) as $k
    | (.rerunsDropped // [] | length) as $g | (.roundDue == true) as $due
    | select(.stop == "PLANNER_HEAP_EXCEEDED"
        or ((.stop == "CAMPAIGN_BUDGET_REACHED" or .stop == "WITNESSED")
            and ($c + $r + $k + $g > 0 or $due)))
    | {schemaVersion: 1, sessionId: "", stage: "EXPLORE",
       kind: "ADMISSION_GAP",
       cls: (if $claim == "SAT_CANDIDATE" then "DIAGNOSTIC" else "BLOCKING"
             end),
       subject: "EXPLORATION_CUT", topologyEpoch: $epoch,
       detail: ("the exploration ended \(.stop) owing work: \($c) queued "
         + "obligation(s) cancelled, \($r) unlanded job(s) and \($k) "
         + "confirmation(s) reaped, \($g) GROW re-run(s) dropped, a round "
         + "due: \($due); the claim is \($claim), so "
         + (if $claim == "SAT_CANDIDATE" then "the witness stands as "
            + "CONFIRM decides it"
            else "no UNSAT closes over a corpus missing those arms" end))}' \
    "${iteration_dir}/exploration.json" >>"${iteration_dir}/campaign_gaps.jsonl"
}

# The open decider arms the declared anchor's runs left phi without and no run
# took (ExploreMain#openArms, the last round's manifest), judged once here: an
# arm whose flip came to no verdict -- a replay that never reached the
# decision -- leaves the UNSAT that closes over it none, one ADMISSION_GAP row
# each, BLOCKING under any claim but a SAT_CANDIDATE (whose witness stands as
# CONFIRM decides it).  Every arm is named in result.json concrete[] (OPEN_ARM)
# and only an UNSAT one leaves unsatClosureComplete true.
campaign_open_arms() {
  local iteration_dir=$1 claim last="" round
  for round in "${iteration_dir}"/obligations-*/explore_manifest.json; do
    [[ -s "${round}" ]] && last=${round}
  done
  [[ -n "${last}" ]] || return 0
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  jq -c --arg claim "${claim}" --arg epoch "$(basename "${iteration_dir}")" '
    (.openArms // [])[] | select(.state == "UNANSWERED")
    | {schemaVersion: 1, sessionId: "", stage: "EXPLORE",
       kind: "ADMISSION_GAP",
       cls: (if $claim == "SAT_CANDIDATE" then "DIAGNOSTIC" else "BLOCKING"
             end),
       subject: "OPEN_ARM_UNANSWERED", topologyEpoch: $epoch,
       detail: ("the open arm \(.siteId)=\(.outcome) of \(.anchor) was left"
         + " out of phi by the runs that reached it, and its flip (asked at"
         + " \(.asked | join(", "))) came to no verdict on \(.paths.UNANSWERED)"
         + " path(s): no run took the arm, so no UNSAT closes over it")}' \
    "${last}" >>"${iteration_dir}/campaign_gaps.jsonl"
}

# The obligations the hard lane left undecided at the full budget
# (campaign_solver_first_tier_ms, solver_timeouts.jsonl): each an arm no
# verdict answered, one ADMISSION_GAP row SOLVER_TIMEOUT, BLOCKING under any
# claim but a SAT_CANDIDATE (whose witness stands as CONFIRM decides it).
campaign_solver_timeouts() {
  local iteration_dir=$1 claim
  [[ -s "${iteration_dir}/solver_timeouts.jsonl" ]] || return 0
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  jq -c --arg claim "${claim}" --arg epoch "$(basename "${iteration_dir}")" '
    {schemaVersion: 1, sessionId: "", stage: "EXPLORE",
     kind: "ADMISSION_GAP",
     cls: (if $claim == "SAT_CANDIDATE" then "DIAGNOSTIC" else "BLOCKING" end),
     subject: "SOLVER_TIMEOUT", topologyEpoch: $epoch,
     detail: ("obligation \(.obligationId) on \(.host): \(.detail), at the"
       + " full budget after the first; its arm has no verdict, so no UNSAT"
       + " closes over it")}' \
    "${iteration_dir}/solver_timeouts.jsonl" \
    >>"${iteration_dir}/campaign_gaps.jsonl"
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
  # One claim at a time: one CONFIRM did not confirm has moved to
  # final/refuted/ (campaign_next_claim) before the next is composed.
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
  # Its claim before it: refuted, moved away, its name looked up free here.
  campaign_await_visible "${composed_smt}" "${composition_manifest}"
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
# hold is a CONFIRM_MISMATCH (PIPELINE §10).  A replay that did not reach
# the fatal at the anchor -- it ran to its end without it, an ORDER it could
# not hold, a stall, a timeout, a replay that published no verdict -- is a
# FALSE POSITIVE (owner 2026-10-08): the claim is refuted (campaign_refute),
# excluded from every later composition, and the campaign goes on to the next
# claim while its budget has room (campaign_next_claim).  A confirmation no
# replay ran -- a task ConfirmMain refused by name, a decision that failed --
# is a defect of the engine, no verdict: EMIT publishes the claim RUN_DEFECT.
# Only a SAT_CANDIDATE is confirmed; any other claim has nothing to confirm
# and the stage says so.  The exploration's
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

# One claim confirmed, in a row: planned (campaign_confirm_plan), its replay
# run wherever there is room (campaign_confirm_replay, charged the measured
# replay need, campaign_replay_need_mb, whose peak it joins), and decided
# (campaign_confirm_decide).  The final CONFIRM's;
# an exploration's attempt runs the same three apart, its replay a job of the
# pool (campaign_stream_attempt).
campaign_confirm_claim() {
  local iteration_dir=$1 claims=$2 dir=$3 need charge status=0
  campaign_confirm_plan "${iteration_dir}" "${claims}" "${dir}"
  if [[ ! -s "${claims}/confirm.json" ]]; then
    need=$(campaign_replay_need_mb)
    charge=$(campaign_replay_charge_mb "${need}")
    ( campaign_head_charged "${charge}" campaign_confirm_replay "${dir}" \
        "${iteration_dir}/instrumented-classes" \
        "${iteration_dir}/seed-replay/execution_task_plan.jsonl" \
        "${charge}" "${need}" ) || status=$?
    campaign_replay_measured "${dir}/worker"
    campaign_confirm_decide "${claims}" "${dir}" "${status}"
  fi
  campaign_confirm_settle "${iteration_dir}" "${claims}"
}

# The claim <claims>/claim.json states, beside its
# candidate_composition_manifest.json, planned: ConfirmMain's task into
# <dir>/worker, its log <dir>/confirm.log.  A verdict known now is written
# to <claims>/confirm.json: a claim ConfirmMain refutes by name ("CONFIRM
# refutes:", the run as recorded: no run of it is a counterfactual), a
# refusal it names ("CONFIRM refused:", rows that state no runnable model --
# a defect of the run, which refutes nothing) or any other exit of it (which
# says nothing about the model), or the selected session itself the run
# (realized.json: every edge the model chose is its own, with the moved roots
# at the model's values, and it observed the fatal -- a replay of its world
# would test only whether a race the order does not hold goes the same way
# twice).  Otherwise the replay is owed.
campaign_confirm_plan() {
  local iteration_dir=$1 claims=$2 dir=$3 worker status=0 reason
  [[ ! -e "${dir}" ]] \
    || die "the confirmation directory already exists: ${dir}"
  worker="${dir}/worker"
  mkdir -p "${worker}" "${dir}/sessions"
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${iteration_dir}" \
    --claim "${claims}/claim.json" \
    --manifest "${claims}/candidate_composition_manifest.json" \
    --output "${worker}" >"${dir}/confirm.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    reason=$(grep -m 1 -E 'CONFIRM (refutes|refused):' "${dir}/confirm.log" \
      || grep -v -E '^[[:space:]]+at ' "${dir}/confirm.log" \
        | tail -n 1)
    campaign_confirm_verdict false \
      "${reason:-ConfirmMain exited ${status}}" "" \
      "$([[ "${reason}" == *'CONFIRM refutes:'* ]] && echo true \
        || echo false)" >"${claims}/confirm.json"
  elif [[ -s "${worker}/realized.json" ]]; then
    jq -c '.' "${worker}/realized.json" >"${claims}/confirm.json"
  fi
}

# The replay of the claim planned in <dir>, exactly as an obligation's, on
# the class tree and plan named, its JVM charged <charged_mb> of a need of
# <need_mb>, wherever its start was placed (run_engine.sh --run-placed).  A
# campaign_fail inside it ends it as "no verdict" (its caller's subshell),
# one more way of not agreeing with the model.
campaign_confirm_replay() {
  local dir=$1 classes=$2 plan=$3 charged=$4 need=$5
  campaign_obligation_replay CONFIRM "${classes}" "${dir}/worker" \
    "${dir}/sessions" "${plan}" "${charged}" "${need}" \
    >>"${dir}/confirm.log" 2>&1
}

# The verdict on the claim <claims>/claim.json from the replay of <dir>, which
# exited <status>: read off the session it published (ConfirmMain
# --sessions) into <claims>/confirm.json.  A replay that published no verdict
# (killed at its bound, stalled, crashed) never reached the fatal: it refutes
# the model, a false positive (owner 2026-10-08).  A decision that failed is
# the engine's defect and decides nothing.
campaign_confirm_decide() {
  local claims=$1 dir=$2 replayed=$3 status=0
  if [[ "${replayed}" -ne 0 ]]; then
    campaign_confirm_verdict false "the confirmation replay published no \
verdict (exit ${replayed}): it never reached the fatal at the anchor; its \
log is ${dir}/confirm.log" "" true >"${claims}/confirm.json"
    return 0
  fi
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --claim "${claims}/claim.json" --output "${dir}/worker" \
    --sessions "${dir}/sessions" >"${claims}/confirm.json" \
    2>>"${dir}/confirm.log"
  [[ "${status}" -eq 0 ]] || campaign_confirm_verdict false "the \
confirmation decision exited ${status}; its log is ${dir}/confirm.log" "" \
    false >"${claims}/confirm.json"
}

# A verdict written: the claim refuted (campaign_refute) when the verdict
# refutes it -- a replay that did not reach the fatal at the anchor, or a
# claim ConfirmMain refuted by name (the run as recorded); one neither
# confirmed nor refuted (a refusal no replay ran, a failed decision) is the
# engine's defect, excluded from nothing: EMIT publishes it RUN_DEFECT.
campaign_confirm_settle() {
  local iteration_dir=$1 claims=$2
  require_nonempty "confirmation" "${claims}/confirm.json"
  if [[ "$(jq -r '.refutes' "${claims}/confirm.json")" == true ]]; then
    campaign_refute "${iteration_dir}" "${claims}"
  elif [[ "$(jq -r '.confirmed' "${claims}/confirm.json")" != true ]]; then
    campaign_log "no verdict, a defect of the engine: $(jq -r '.reason' \
"${claims}/confirm.json")"
  fi
}

# One model of an iteration as every composition of it names the model
# (compose.Refutations#atPath): each arm by its kind and digest -- the path
# ordinal a selector spells is one composition's -- and every other field as
# it is; a jq definition, key.
campaign_model_key='def key: .arms |= ((. // []) | map(sub("__[0-9]+__"; "__")));'

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

# What the stages after the exploration are owed, in seconds: COMPOSE and
# EMIT, which reads the corpus COMPOSE read, each as long as the longest
# COMPOSE this campaign measured -- its stage metrics and its witness
# attempts; the last planner round, which reads the same corpus, stands for
# a COMPOSE none has run yet -- CONFIRM as long as the longest CONFIRM --
# the seed's REPLAY stands for a CONFIRM replay none has run yet -- and
# REPRODUCE its own bound (campaign_reproduce_bound; its native runs go out
# at once); never less than
# campaign_reserve_s.  (HG4: hdfs-11741's EMIT, 118 s in HG3, was killed at
# the case timeout when the reserve owed COMPOSE and CONFIRM alone; HR1:
# hdfs-adhoc-07's first COMPOSE, over 556 sessions after planner rounds of 4
# min, had the floor's 10 min; SL1: hdfs-adhoc-37's 23-min seed replay,
# standing for REPRODUCE as well as CONFIRM, left its exploration one round.)
campaign_reserve() {
  local measured
  measured=$( {
      awk -F '\t' '$1 == "COMPOSE" || $1 == "CONFIRM" || $1 == "REPLAY" {
        print $1, $2 }' "${campaign_stage_metrics}" 2>/dev/null
      jq -r '"COMPOSE \(.composeMillis // 0)", "CONFIRM \(.confirmMillis // 0)"' \
        "${campaign_root}/iteration-0000/witness_attempts.jsonl" 2>/dev/null
      campaign_last_round_millis
    } | awk '$1 == "COMPOSE" { if ($2 > c) c = $2; next }
        $1 == "PLANNER" { p = $2; next }
        { if ($2 > r) r = $2 }
        END { printf "%d\n", (2 * (c > 0 ? c : p) + r) / 1000 }')
  measured=$(( measured + $(campaign_reproduce_bound) ))
  echo $(( measured > campaign_reserve_s ? measured : campaign_reserve_s ))
}

# How long one native run of REPRODUCE may take, in seconds:
# reproduce_time_factor times the recording's workload, at least
# reproduce_min_s.  A short recording's own time says little of how long ten
# native runs at once on a busy cluster take (hdfs-17960: an 8 s recording,
# NP1's ten runs all cut at 24 s before their window opened, NP2's 11-16 s;
# hdfs-17897 NP7: a 9 s recording, its ten runs 119-187 s, every one at the
# anchor).
campaign_reproduce_bound() {
  local bound=$(( reproduce_time_factor * ${campaign_recorded_workload_s:-0} ))
  echo $(( bound > reproduce_min_s ? bound : reproduce_min_s ))
}

# "PLANNER <ms>": the wall of the last round the planner finished, from
# its in_flight.jsonl, copied as the planner starts (campaign_stream_step),
# to its explore_manifest.json, written as it ends; nothing before one has.
campaign_last_round_millis() {
  local manifest started ended last=""
  for manifest in "${campaign_root}"/iteration-0000/obligations-[0-9]*/explore_manifest.json; do
    started=$(stat -c %Y "${manifest%/*}/in_flight.jsonl" 2>/dev/null) \
      && ended=$(stat -c %Y "${manifest}" 2>/dev/null) \
      && last="PLANNER $(( (ended - started) * 1000 ))"
  done
  [[ -z "${last}" ]] || echo "${last}"
}

# Whether the final stages owe the next claim: the last was a SAT_CANDIDATE
# CONFIRM refuted -- a false positive, its model recorded once in
# refuted_claims.jsonl (campaign_model_key) -- so the next composition
# excludes it, and it is not a model the composition was told
# to exclude already -- the budget has room, and fewer than
# campaign_max_claims claims were decided again.  The claim's artifacts move
# to final/refuted/NNNN/ first, so final/ holds the claim EMIT publishes.
campaign_next_claim() {
  local iteration_dir=$1 dir name model seen=0 decided
  [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      == SAT_CANDIDATE && -s "${campaign_final}/confirm.json" \
    && "$(jq -r '.confirmed' "${campaign_final}/confirm.json")" != true ]] \
    || return 1
  model=$(campaign_claim_model "${campaign_final}/claim.json")
  [[ -z "${model}" ]] || seen=$(cat "${iteration_dir}/refuted_claims.jsonl" \
      2>/dev/null | jq -c --argjson model "${model}" "${campaign_model_key}"'
      select((.model | key) == ($model | key))' | grep -c '' || true)
  if (( seen != 1 )); then
    campaign_log "the claim's model is excluded ${seen} time(s), not once: \
the next composition could repeat it, so there is no next claim"
    return 1
  fi
  if ! campaign_claim_room; then
    campaign_log "the campaign budget (campaign_budget_s=${campaign_budget_s}) \
has no room for another claim"
    return 1
  fi
  decided=$(find "${campaign_final}/refuted" -mindepth 1 -maxdepth 1 \
    2>/dev/null | grep -c '' || true)
  if (( decided >= campaign_max_claims )); then
    campaign_log "the claim was decided again ${decided} time(s), the bound \
(campaign_max_claims=${campaign_max_claims}): the last claim is published"
    return 1
  fi
  dir=$(printf '%s/refuted/%04d' "${campaign_final}" "${decided}")
  mkdir -p "${dir}"
  for name in candidate.smt2 candidate_composition_manifest.json claim.json \
      compose.log confirm confirm.json; do
    [[ ! -e "${campaign_final}/${name}" ]] \
      || mv -- "${campaign_final}/${name}" "${dir}/"
  done
  campaign_log "the claim was refuted (${dir}): composing the next one"
}

# REPRODUCE (PIPELINE §10b), after EMIT: a confirmed witness run again
# natively -- the recording weave on the stock JDK, planting what the
# confirmation's world plants and holds (its fault markers, its trees' hook
# roots, its clock jumps, configurations, accessor reads and answers at the
# calls the plant-run agent hands it, its ORDER rows, and the order the
# session CONFIRM saw ran in from the moved roots on: campaign_confirmed_
# session, explore.RealizedOrder) and watching the
# target's guards for their fatal arm at the claim's anchor
# (explore.ConfirmMain --plant, the code that wrote CONFIRM's world;
# runtime.RecordingPlant, runtime.PlantAgent).  reproduce_runs runs, all at
# once, each a head step charged the recording's measured peak resident
# memory wherever there is room (campaign_reproduce_one) and bounded by
# campaign_reproduce_bound; a run ends as
# soon as the planted world takes the fatal arm at the anchor, its one
# question answered.  Each run states its answer itself
# (campaign_reproduce_run); final/reproduce.json counts them -- runs, how
# many applied every row of the plant, took the target's fatal arm, took it
# at the claim's own anchor, reproduced (at the anchor with every ROOT and
# ANSWER row applied and every ORDER held: what tools/adhoc/findings.py
# rates), could not hold an ORDER in time (unheld; unheldLate: what it
# waited for came after all, unheldMissing: it never came), and still held
# one when the run ended -- and names the runs that stated none.  The
# realized order makes REPRODUCE run the world CONFIRM saw; it never touches
# CONFIRM: the rate ranks a finding (tools/adhoc/findings.py) and never
# refutes it, and nothing here moves the claim, CONFIRM's decision or what
# EMIT published.  A world a
# native run cannot plant (NATIVE_PLANT_UNSUPPORTED: a root minted other
# than at a call's return, an answer at no call-return capture, a world that
# plants nothing), or a recording that measured no peak memory, is a
# reproduce.json with no run and the reason.  Only a confirmed
# SAT_CANDIDATE is reproduced.
campaign_reproduce() {
  local iteration_dir=$1
  local dir="${campaign_final}/reproduce" status=0 bound run reason="" pid
  local confirmed
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
  confirmed=$(campaign_confirmed_session "${iteration_dir}")
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.explore.ConfirmMain \
    --iteration "${iteration_dir}" --claim "${campaign_final}/claim.json" \
    --manifest "${composition_manifest}" \
    --static-scope-map "${causynth_static_scope_map}" \
    --confirmed-session "${confirmed}" \
    --plant "${dir}/plant.jsonl" >"${dir}/plant.log" 2>&1
  if [[ "${status}" -ne 0 ]]; then
    reason="no native run: $(sed -n -E 's/^CONFIRM (refused|refutes): //p' \
      "${dir}/plant.log" | head -n 1)"
  elif [[ ! "${campaign_recorded_workload_rss_mb}" =~ ^[0-9]+$ ]]; then
    reason="no native run: the recording measured no peak resident memory \
(workload_rss_mb) to charge one with"
  fi
  if [[ -n "${reason}" ]]; then
    jq -n --arg reason "${reason}" '{schemaVersion: 1, kind: "REPRODUCTION",
      runs: 0, planted: 0, fatal: 0, atAnchor: 0, reproduced: 0, unheld: 0,
      unheldLate: 0, unheldMissing: 0, holding: 0, reason: $reason}' \
      >"${campaign_final}/reproduce.json"
    campaign_log "reproduce: ${reason}"
    return 0
  fi
  bound=$(campaign_reproduce_bound)
  campaign_log "reproduce: ${reproduce_runs} native run(s) at once, each \
charged ${campaign_recorded_workload_rss_mb} MB and bounded by ${bound}s \
(reproduce_time_factor=${reproduce_time_factor} x the recording's \
${campaign_recorded_workload_s}s, at least reproduce_min_s=${reproduce_min_s})"
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
       reproduced: map(select(.reproduced)) | length,
       unheld: map(select(any(.unapplied[];
         .why == "LATE" or .why == "MISSING"))) | length,
       unheldLate: map(select(any(.unapplied[]; .why == "LATE"))) | length,
       unheldMissing: map(select(any(.unapplied[]; .why == "MISSING")))
         | length,
       holding: map(select(any(.unapplied[]; .why == "HOLDING"))) | length,
       reason: (if length < $runs
         then "\($runs - length) of \($runs) run(s) stated no answer"
         else "" end)}' >"${campaign_final}/reproduce.json"
  jq -r '"  reproduced in \(.reproduced) of \(.runs) native run(s): the fatal at the anchor with every root planted and every order held (\(.planted) applied the whole plant, \(.fatal) fatal, \(.atAnchor) at the anchor, \(.unheld) an order unheld -- \(.unheldLate) one that came late, \(.unheldMissing) one that never came --, \(.holding) an order still holding)"' \
    "${campaign_final}/reproduce.json"
}

# The session CONFIRM saw (final/confirm.json's sessionId): the selected
# session itself where it realized the claim, else its replay's own, in the
# final stages' confirm/ or an exploration attempt's witness-confirm/NNNN/.
campaign_confirmed_session() {
  local iteration_dir=$1 id dir
  id=$(jq -r '.sessionId // empty' "${campaign_final}/confirm.json")
  for dir in "${iteration_dir}/sessions/${id}" \
      "${campaign_final}/confirm/sessions/${id}" \
      "$(dirname "${iteration_dir}")"/witness-confirm/*/sessions/"${id}"; do
    if [[ -n "${id}" && -d "${dir}" ]]; then
      printf '%s\n' "${dir}"
      return 0
    fi
  done
  printf '%s\n' "${campaign_final}/confirm/sessions/${id:-none}"
}

# One native run of REPRODUCE into <run>: a head step charged the
# recording's peak memory, wherever there is room (campaign_head_charged),
# and released as it returns.  A run placed on a
# peer has its answer waited for until the shared home shows it here
# (campaign_await_visible); one that never shows states none.
campaign_reproduce_one() {
  local run=$1 bound=$2 plant=$3
  mkdir -p "${run}"
  campaign_head_charged "${campaign_recorded_workload_rss_mb}" \
    campaign_reproduce_run "${analysis_classes_dir}" \
    "${run}" "${bound}" "${plant}" "${campaign_recorded_workload_rss_mb}" \
    || campaign_log "reproduce: $(basename "${run}") exited nonzero; its \
logs are in ${run}"
  campaign_host_is_local "${campaign_placed_host}" \
    || campaign_await_visible "${run}/answer.json"
}

# One native run, on the host it was placed on, which it names in
# <run>/host.txt: the workload in the recording weave <classes> with
# <plant>, charged <charged_mb>, its trace into <run>, under <seconds>, its
# output in <run>.  Whatever
# the workload's exit -- a planted fault may well fail the test, and a run
# that answered ends early -- its answer is <run>/answer.json, read off its
# trace's plant rows (a run killed mid-row loses only that row): {exit,
# rows, applied, unapplied, planted, rootsPlanted, ordersHeld, fatal,
# atAnchor, reproduced} -- the plant's rows to apply (ROOT, ANSWER and ORDER
# of either scope: a CLOCK_SITE or TARGET row is context), how many the run
# applied, each one it did not with why (an ORDER whose wait timed out:
# LATE when what it waited for came after all, MISSING when it never came
# in this run -- its event's identity is not this run's; HOLDING: still
# waiting when the run ended; UNWRITTEN: a value it could not plant -- a
# HOOK row's field write, a value the call's type cannot hold, a timed
# wait's timeout the program could not have reached, at any call of the row
# even after one applied it; NOT_REACHED),
# whether it applied every row, every ROOT and ANSWER row (clock jumps,
# configurations and answers included) and held every ORDER, whether it
# took the target's fatal arm and at the anchor, and whether it reproduced:
# the fatal arm at the anchor with every ROOT and ANSWER row applied and no
# ORDER timed out -- a run that did not plant the model's world, or ran
# another order than the world CONFIRM saw, and reaches the fatal anyway is
# the program's own race, no reproduction.  An ORDER is held at most half
# the run's bound (causynth.confirm.order.timeout.ms), so an unrealizable
# order is stated before the bound ends the run; the first one timed out
# releases every hold of the run (PIPELINE §10b).
campaign_reproduce_run() {
  local analysis_classes_dir=$1 run=$2 bound=$3 plant=$4 charged=$5 status=0
  local trace="${run}/runtime_trace.jsonl"
  hostname -s >"${run}/host.txt"
  run_capturing_status run_configured_workload "${run}" "${bound}" "${plant}" \
    "${charged}" "" "$(( bound * 500 ))" \
    >"${run}/stdout.log" 2>"${run}/stderr.log"
  [[ -s "${trace}" ]] || trace=/dev/null
  jq -n -c -R --argjson exit "${status}" --slurpfile plant "${plant}" '
    [inputs | select(contains("\"event\":\"PLANT_")) | fromjson?] as $rows
    | [$plant[] | select(.kind == "ROOT" or .kind == "ANSWER"
        or .kind == "ORDER")] as $planted
    | def stated($event): [$rows[] | select(.event == $event) | .row];
      def why($row):
        if any(stated("PLANT_LATE")[]; . == $row) then "LATE"
        elif any(stated("PLANT_UNHELD")[]; . == $row) then "MISSING"
        elif any(stated("PLANT_UNWRITTEN")[]; . == $row) then "UNWRITTEN"
        elif any(stated("PLANT_HOLDING")[]; . == $row) then "HOLDING"
        else "NOT_REACHED" end;
      def event($e): "\($e.kind) \($e.site) @ \($e.context) #\($e.k)";
      def ends: if (.before | type) == "object"
        then "\(event(.before)) -> \(event(.after))"
        else "\(.before) -> \(.after)" end;
      stated("PLANT_APPLIED") as $applied
    | [$planted[] | . as $p | select((any($applied[]; . == $p.row) | not)
        or any(stated("PLANT_UNWRITTEN")[]; . == $p.row))
        | {row, kind, planted: (.rootId // .endpoint // ends),
           why: why($p.row)}] as $unapplied
    | ($planted | length) as $count
    | any($rows[]; .event == "PLANT_FATAL" and .atAnchor) as $atAnchor
    | (all($unapplied[]; .kind == "ORDER")) as $roots
    | (any($unapplied[]; .why == "LATE" or .why == "MISSING") | not)
      as $held
    | {exit: $exit, rows: $count, applied: ($count - ($unapplied | length)),
       unapplied: $unapplied,
       planted: ($count > 0 and ($unapplied | length) == 0),
       rootsPlanted: $roots, ordersHeld: $held,
       fatal: any($rows[]; .event == "PLANT_FATAL"),
       atAnchor: $atAnchor, reproduced: ($atAnchor and $roots and $held)}' \
    "${trace}" >"${run}/answer.json.part"
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
  campaign_exploration_cut "${iteration_dir}"
  campaign_open_arms "${iteration_dir}"
  campaign_solver_timeouts "${iteration_dir}"
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
  # SAT_CANDIDATE: one the program refuted is published as SAT_UNCONFIRMED
  # with the first mismatch named, one whose confirmation published no
  # verdict as RUN_DEFECT.  Any other claim was never confirmed and carries
  # null.
  local confirmation=null
  if [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      == SAT_CANDIDATE ]]; then
    require_nonempty "confirmation" "${campaign_final}/confirm.json"
    campaign_require_json "confirmation" "${campaign_final}/confirm.json" \
      || campaign_fail EMIT CONFIRM "${campaign_final}/confirm.json" \
        "the confirmation is malformed"
    jq -e '(.confirmed | type) == "boolean" and (.refutes | type) == "boolean"
        and (.reason | type) == "string"' \
      "${campaign_final}/confirm.json" >/dev/null \
      || campaign_fail EMIT CONFIRM "${campaign_final}/confirm.json" \
        "the confirmation states no boolean confirmed and refutes and string reason"
    confirmation=$(cat "${campaign_final}/confirm.json")
  fi
  # Every claim CONFIRM refuted on the way, in order: the filtered false
  # positives (tools/adhoc/triage.py), whatever the claim published.
  local refuted="${iteration_dir}/refuted_claims.jsonl"
  [[ -s "${refuted}" ]] || refuted=/dev/null
  # What the last EXPLORE round found decided on no symbol (ExploreMain's
  # concreteAnchors): information beside the verdict, never a gap.
  local explored=/dev/null round
  for round in "${iteration_dir}"/obligations-*/explore_manifest.json; do
    [[ -s "${round}" ]] && explored=${round}
  done
  # The formula the claim is about, SAT or UNSAT: the file z3 re-solves.
  require_nonempty "composed formula" "${campaign_final}/candidate.smt2"
  # Its path relative to the case directory, so a result moved between hosts
  # or read off a sweep names no lift's absolute tree.
  local formula_path
  formula_path=$(realpath --relative-to="${causynth_output_dir}" \
    "${campaign_final}/candidate.smt2")
  local bounded
  bounded=$(campaign_bounds "${iteration_dir}") \
    || campaign_fail EMIT CAMPAIGN "${iteration_dir}" \
      "the declared bounds the search touched could not be read"
  # The planned occurrences run paused but for their doors (control
  # producers, RuntimeSelectedRegionFinalizer#DOORS_ONLY): one plan row each.
  local doors_only
  doors_only=$(grep -c '"doorsOnly":true' -- "${runtime_region_plan}") \
    || doors_only=0
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --argjson confirmation "${confirmation}" \
    --argjson bounded "${bounded}" \
    --argjson doorsOnly "${doors_only}" \
    --arg formula "${formula_path}" \
    --arg formulaSha "$(campaign_digest "${campaign_final}/candidate.smt2")" \
    --slurpfile refutedClaims "${refuted}" \
    --slurpfile composedDocuments "${composition_manifest}" \
    --slurpfile exploreDocuments "${explored}" \
    --slurpfile gapDocuments "${campaign_final}/gaps.json" \
    --slurpfile planCatalog <(head -n 1 -- "${runtime_region_plan}") '
    $composedDocuments[0] as $c | ($c.solver // {}) as $r |
    $gapDocuments[0] as $gaps |
    ($r.campaignClaim) as $decided |
    ($r.reachability // "UNKNOWN") as $reachability |
    # An open decider arm no run took closes only by its UNSAT flip, or at
    # its named bound (campaign_open_arms, campaign_bounds).
    (($r.unsatClosureComplete // false)
     and ([($exploreDocuments[0].openArms // [])[]
           | select(.state != "UNSAT" and .state != "BOUNDED")]
          | length == 0))
      as $unsatClosureComplete |
    ($gaps.gapCount) as $gapCount |
    ($gaps.telemetryCount) as $telemetryCount |
    (($c.finalStatusRefusals // []) | length) as $blockers |
    # The formula decides, SAT or UNSAT.  A SAT claim is what CONFIRM made
    # of it: confirmed, refuted (SAT_UNCONFIRMED), or no verdict -- a replay
    # that timed out or published none, a decision that failed -- which is
    # a defect of the run (RUN_DEFECT), never a refutation.  An UNSAT closes
    # only where no stage named a defect.  Every defect is in defects[].
    ($confirmation != null and $confirmation.confirmed != true
     and $confirmation.refutes != true) as $noVerdict |
    ($decided.claim == "SAT_CANDIDATE"
     and $confirmation.confirmed == true) as $confirmedSat |
    (if $confirmedSat then "SAT_CANDIDATE"
     elif $decided.claim == "SAT_CANDIDATE" and $noVerdict then "RUN_DEFECT"
     elif $decided.claim == "SAT_CANDIDATE" then "SAT_UNCONFIRMED"
     elif $gapCount > 0 then "RUN_DEFECT"
     else $decided.claim end) as $claim |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     provenance: $provenance,
     claim: $claim,
     claimReason: (if $claim == "SAT_UNCONFIRMED"
       then "the confirmation replay did not agree with the model: "
            + $confirmation.reason
       elif $noVerdict
       then "the confirmation of the formula'"'"'s witness published no verdict: "
            + $confirmation.reason
       elif $claim == "RUN_DEFECT" and $decided.claim != "RUN_DEFECT"
       then "the formula decided " + $decided.claim + ", and the run named "
            + ($gapCount | tostring) + " defect(s) that leave no verdict"
       else $decided.claimReason end),
     # What the composition itself decided, whatever the run made of it,
     # and the formula it decided it on (z3 reproduces the verdict on it):
     # its path relative to the case directory, so a result moved between
     # hosts or read off a sweep names no absolute tree of any lift.
     formulaClaim: $decided.claim,
     formula: {path: $formula, sha256: $formulaSha},
     blockers: $decided.blockers,
     # ClaimPolicy counts its own blockers; re-counting the array here let
     # the published count drift from the policy that decided the claim.
     blockerCount: $decided.blockerCount,
     whyNotAccepted: (if $claim == "SAT_UNCONFIRMED"
       then "SAT_UNCONFIRMED: " + $confirmation.reason
       elif $noVerdict
       then "RUN_DEFECT: CONFIRM published no verdict: " + $confirmation.reason
       elif $claim == "RUN_DEFECT" and $decided.claim != "RUN_DEFECT"
       then "RUN_DEFECT: the run named " + ($gapCount | tostring)
            + " defect(s): " + ([$gaps.gaps[] | .code] | unique | join(", "))
       else $decided.whyNotAccepted end),
     # The confirmation itself, so a reader of result.json sees which
     # session answered and why, not only that the claim was downgraded.
     confirmation: $confirmation,
     refutedClaims: $refutedClaims,
     # The excluded models an UNSAT rests on: the refuted_claim__ labels its
     # unsat core names (ComposeMain#campaignClaim), the false positives
     # CONFIRM filtered,
     # each the model it excludes -- a region the verdict rests on beside the
     # corpus -- and each world a replay refuted for an open decider arm whose
     # flip then came back UNSAT or stopped at its bound (REFUTED_WORLD,
     # ExploreMain#openArms).
     restsOnRefutations: (($decided.restsOnRefutations // [])
       + [($exploreDocuments[0].openArms // [])[]
          | select(.state == "UNSAT" or .state == "BOUNDED")
          | . as $arm | (.refutedWorlds // [])[]
          | {kind: "REFUTED_WORLD", anchor: $arm.anchor,
             siteId: $arm.siteId, outcome: $arm.outcome} + .]),
     # The admitted paths COMPOSE refused by name, each with its first
     # refusal: no disjunct of the formula, never silent.
     refusedPaths: ($decided.refusedPaths // []),
     # Whether the forced world reached the marked throw (PIPELINE §7.10):
     # the state of the FORCE run, its verdict detail (FORCED_TARGET and how
     # the occurrence ended, or FORCE_DIVERGED and where), its forced flip
     # and the seed flips it deferred or that were asked after it.
     force: ($exploreDocuments[0].force // null),
     # The declared bounds the search touched (campaign_bounds): null, or
     # {by, detail}.  A verdict over a search a bound cut is named, never
     # read as the end of the closure itself.
     bounded: $bounded,
     # The writers PLAN did not cross to as confined (CLOSURE_CONFINED, the
     # region plan catalog'"'"'s gap rows): null, or their sum, by owner
     # class, and the first rows.  An UNSAT reading looks at the anchor'"'"'s
     # demanded fields among them: the recorded heap is partial.
     # How many planned occurrences ran paused but for their doors: the
     # control producers, which contribute no value (SYMBOL-SCOPE §4.4,
     # RuntimeSelectedRegionFinalizer#DOORS_ONLY).
     doorsOnlyOccurrences: $doorsOnly,
     confinedWriters: ([($planCatalog[0].gaps // [])[]
         | select(.kind == "CLOSURE_CONFINED")] as $rows
       | if ($rows | length) == 0 then null
         else {writers: ($rows | map(.writers) | add),
               rows: ($rows | length),
               byOwnerClass: ($rows | group_by(.ownerClass)
                 | map({key: .[0].ownerClass,
                        value: (map(.writers) | add)})
                 | from_entries),
               first: [$rows[:3][]
                 | {reader, field, scope, ownerClass, writers, first}]}
         end),
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
     # A closed negative states how many tree hooks ran on their own
     # concrete value: no task of the plan declared their source
     # (HOOK_UNDECLARED, one per hook and activation).
     undeclaredHookCount: (if $claim == "UNSAT_CLOSED"
       then ([$gaps.telemetryGaps[] | select(.code == "HOOK_UNDECLARED")
              | [.subject, .detail]] | unique | length)
       else null end),
     # The claim is what ClaimPolicy decided; acceptance is that claim
     # together with the named gaps, because the stages the policy cannot
     # see -- IMPORT, EXPLORE and the static plan -- raise their own blocking
     # gaps.  This is the conjunction the exit code below already tests,
     # published so a reader of result.json alone does not have to infer it
     # from two numbers.
     accepted: (($claim == "SAT_CANDIDATE" or $claim == "UNSAT_CLOSED")
                and $gapCount == 0),
     blockingGapCodes: ($gaps.byCode // {}),
     # The defects of the run or the engine, each a bug to fix: the BLOCKING
     # gaps, whichever stage raised them, and a confirmation that published
     # no verdict.
     defects: ([$gaps.gaps[] | {stage, code, subject, detail}]
       + (if $noVerdict
          then [{stage: "CONFIRM", code: "CONFIRM_NO_VERDICT",
                 subject: ($confirmation.sessionId // ""),
                 detail: $confirmation.reason}]
          else [] end)
       # A causal chain EXPLORE could not close: a value a fatal condition the
       # verdict rests on names that no attested producer made -- the witness
       # path for a SAT, every path for an UNSAT.
       + [($decided.findingKind // "") as $kind | ($decided.openChain // [])[]
          | {stage: "COMPOSE", code: (if $kind == "NO_SUPPORTED_WITNESS"
               then "UNSAT_CHAIN_OPEN" else "WITNESS_CHAIN_OPEN" end),
             subject: .symbol,
             detail: ("no producer the corpus attests made this value"
               + (if .producer == "" then "" else "; its arrival names "
                  + .producer + ", which EXPLORE did not grow" end))}]),
     # What the decision rested on concretely: each anchor every admitted
     # path decided on no symbol (EXPLORE), each open decider arm no run
     # took (EXPLORE, with its flip), and each value COMPOSE stated as a
     # constant or left free, with what it rests on (Composer.Concrete).
     concrete: ([($exploreDocuments[0].concreteAnchors // [])[]
                 | {kind: "ANCHOR"} + .]
                + [($exploreDocuments[0].openArms // [])[]
                   | {kind: "OPEN_ARM"} + .] + ($c.concrete // [])),
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
# artifact set is not an accepted candidate: a SAT claim CONFIRM did not
# agree with exits 2 with its reason, because a top-level zero exit is not
# completion; a run that named defects, 3 -- no verdict (RUN_DEFECT), or a
# confirmed witness beside a defect of the run.
campaign_exit_verdict() {
  local gapCount
  gapCount=$(jq -r '.gapCount' "${campaign_final}/gaps.json")
  case "$(jq -r '.claim' "${campaign_final}/result.json")" in
    SAT_CANDIDATE|UNSAT_CLOSED|RUN_DEFECT) ;;
    *)
      jq -r '"[campaign] no accepted candidate: claim=\(.claim) reason=\(.claimReason)"' \
        "${campaign_final}/result.json" >&2
      jq -r 'select((.whyNotAccepted // "") != "") | .whyNotAccepted' \
        "${campaign_final}/result.json" >&2
      exit 2
      ;;
  esac
  # Every defect is a hard failure, whichever stage raised it.  The
  # telemetry array holds only the rows their own producer classed as unable
  # to change a chain, and each of those carries its reason there.
  [[ "${gapCount}" -eq 0 && "$(jq -r '.claim' "${campaign_final}/result.json")" \
      != RUN_DEFECT ]] || {
    jq -r '"[campaign] no accepted verdict: claim=\(.claim) (the formula "
      + .formulaClaim + "), and the run named "
      + (.defects | length | tostring) + " defect(s); "
      + (.telemetryCount | tostring) + " diagnostic row(s) withhold nothing"' \
      "${campaign_final}/result.json" >&2
    echo "  named defects: ${campaign_final}/result.json defects[]" >&2
    exit 3
  }
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
scratch ${campaign_local_scratch_root}"
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

# ONE obligation of somebody else's campaign, solved on this machine.
do_run_obligation() {
  campaign_peer_enter "$@"
  set -- "${campaign_peer_args[@]}"
  [[ $# -eq 5 || $# -eq 6 ]] || die "--run-obligation takes five or six \
positional arguments (id obligations sessions worker charged-mb [lane]), got $#"
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
  campaign_stage SEED campaign_seed
  # A measurement of the slice and the recording stops here: the static
  # artifacts, the trace and its region plan are published.
  if [[ "${campaign_stop_after}" == "SEED" ]]; then
    campaign_log "stopping after SEED: campaign_stop_after=SEED"
    return 0
  fi
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
  campaign_stage EXPLORE campaign_explore "${iteration_dir}" "${iteration_id}"
  campaign_publish_iteration_manifest "${iteration_dir}" "${iteration_id}"
  campaign_claim_stages "${iteration_dir}"
  # A claim CONFIRM refuted or gave no verdict on does not end the campaign
  # while its budget has room: the next composition excludes it
  # (campaign_next_claim).
  while campaign_next_claim "${iteration_dir}"; do
    campaign_claim_stages "${iteration_dir}"
  done
  campaign_stage EMIT campaign_emit "${iteration_dir}"
  # After the verdict is published, never before it: REPRODUCE ranks a
  # confirmed finding and moves no claim.
  campaign_stage REPRODUCE campaign_reproduce "${iteration_dir}"
  campaign_exit_verdict
}

# REPRODUCE alone (`reproduce`): the stage over a finished campaign's output
# directory, a copy of one (tools/rounds/reproduce-again.sh links what it
# reads), with the claim, manifest and confirmation EMIT published and no
# reproduction yet.  The recording's own time is not kept apart from SEED's,
# so SEED's time is what the runs' bound is a factor of
# (campaign_reproduce_bound).
do_reproduce() {
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  require_file "a confirmation" "${campaign_final}/confirm.json"
  require_file "a composition manifest" "${composition_manifest}"
  [[ ! -e "${campaign_final}/reproduce.json" ]] \
    || die "this campaign already holds a reproduction: ${campaign_final}"
  campaign_recorded_workload_rss_mb=$(cat \
    "$(dirname "${runtime_region_plan}")/workload_rss_mb" 2>/dev/null) \
    || campaign_recorded_workload_rss_mb=""
  campaign_recorded_workload_s=$(awk -F'\t' '$1 == "SEED" {
    print int($2 / 1000) }' "${campaign_root}/stage_metrics.tsv" 2>/dev/null)
  campaign_init_local_scratch_root
  campaign_head_charging=1
  campaign_head_reserve
  campaign_reproduce "${campaign_root}/iteration-0000"
  cat "${campaign_final}/reproduce.json"
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
  campaign|config|validate|reproduce|--run-obligation|--run-placed)
    [[ -n "${config_file}" ]] || die "${command_name} requires --config FILE"
    initialize_config "${config_file}"
    case "${command_name}" in
      campaign)
        [[ $# -eq 0 ]] || die "campaign takes no extra arguments"
        do_campaign
        ;;
      reproduce)
        [[ $# -eq 0 ]] || die "reproduce takes no extra arguments"
        do_reproduce
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
