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
      ID OBLIGATIONS SESSIONS WORKER CHARGED_MB [CHARGE_ID|HARD]
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

workflow_config_keys=(
  "campaign_setup_command CAUSYNTH_CAMPAIGN_SETUP_COMMAND krp -"
  "concolic_replay_command CAUSYNTH_CONCOLIC_REPLAY_COMMAND krp -"
  "campaign_worker_hosts CAUSYNTH_CAMPAIGN_WORKER_HOSTS krp -"
  "stream_shared_pool CAUSYNTH_STREAM_SHARED_POOL krp false"
  "stream_stop_at_witness CAUSYNTH_STREAM_STOP_AT_WITNESS krp true"
  "engine_memory_mb GRAPH_CHECKER_ENGINE_MEMORY_MB krp -"
  "campaign_stop_after CAUSYNTH_CAMPAIGN_STOP_AFTER krp -"
  "region_path_max_paths_per_region CAUSYNTH_REGION_PATH_MAX_PATHS_PER_REGION krp -"
  "region_path_max_flips_per_path CAUSYNTH_REGION_PATH_MAX_FLIPS_PER_PATH krp -"
  "region_path_max_tasks CAUSYNTH_REGION_PATH_MAX_TASKS krp -"
  "region_path_max_world_depth CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH krp -"
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
  "causynth_loop_default_bound CAUSYNTH_LOOP_DEFAULT_BOUND krp -"
  "causynth_lineage_roots CAUSYNTH_LINEAGE_ROOTS krp -"
  "causynth_system_doors CAUSYNTH_SYSTEM_DOORS krp -"
  "causynth_client_fault_transports CAUSYNTH_CLIENT_FAULT_TRANSPORTS krp -"
  "causynth_doors_only_roots CAUSYNTH_DOORS_ONLY_ROOTS krp -"
  "causynth_export_guard_writers CAUSYNTH_EXPORT_GUARD_WRITERS krp false"
  "causynth_system_view CAUSYNTH_SYSTEM_VIEW krp -"
  "causynth_scope_growth_budget CAUSYNTH_SCOPE_GROWTH_BUDGET krp 24"
  "reproduce_runs CAUSYNTH_REPRODUCE_RUNS krp 10"
  "reproduce_time_factor CAUSYNTH_REPRODUCE_TIME_FACTOR krp 3"
  "reproduce_min_s CAUSYNTH_REPRODUCE_MIN_S krp 300"
  "reproduce_charge_pct CAUSYNTH_REPRODUCE_CHARGE_PCT krp 130"
  "causynth_root_domains CAUSYNTH_ROOT_DOMAINS krp -"
  "custom_jdk_home CAUSYNTH_CUSTOM_JDK_HOME krp -"
  "z3_bin CAUSYNTH_Z3 krp -"
  "workload_work_dir CAUSYNTH_WORKLOAD_WORK_DIR krp -"
  "workload_command CAUSYNTH_WORKLOAD_COMMAND krp -"
  "trace_test CAUSYNTH_TRACE_TEST krp -"
  "candidate_graph - rp -"
  "runtime_region_plan - rp -"
  "causynth_static_scope_map - rp -"
  "causynth_region_skeletons - rp -"
  "analysis_classes_dir - rp -"
  "schedule_output_dir - rp -"
  "schedule_max_jobs CAUSYNTH_SCHEDULE_MAX_JOBS krp -"
  "solver_timeout_ms CAUSYNTH_SOLVER_TIMEOUT_MS krp -"
  "replay_timeout_s CAUSYNTH_REPLAY_TIMEOUT_S krp 2400"
  "campaign_budget_s CAUSYNTH_CAMPAIGN_BUDGET_S krp 21600"
  "campaign_reserve_s CAUSYNTH_CAMPAIGN_RESERVE_S krp 600"
  "campaign_max_claims CAUSYNTH_CAMPAIGN_MAX_CLAIMS krp 8"
  "seed_replay_time_factor CAUSYNTH_SEED_REPLAY_TIME_FACTOR krp 40"
  "view_hold_max_ms CAUSYNTH_VIEW_HOLD_MAX_MS krp 3000"
  "recording_max_trace_mb CAUSYNTH_RECORDING_MAX_TRACE_MB krp 4096"
  "compose_max_valuations CAUSYNTH_COMPOSE_MAX_VALUATIONS krp 16"
  "declared_target_occurrence CAUSYNTH_TARGET_OCCURRENCE krp -"
)

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

load_config_file() {
  local path=$1
  local raw key value
  while IFS= read -r raw || [[ -n "${raw}" ]]; do
    raw=$(trim "${raw}")
    [[ -z "${raw}" || "${raw}" == \#* ]] && continue
    [[ "${raw}" == *=* ]] || continue
    key=$(trim "${raw%%=*}")
    value=$(trim "${raw#*=}")
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

campaign_jvm_footprint_mb() {
  printf '%s\n' "$(( $1 + $1 / 16 + 384 ))"
}

campaign_engine_outgrown=""
campaign_jvm_out_of_heap_status=3
campaign_engine_oom=(-XX:+ExitOnOutOfMemoryError -XX:GCTimeLimit=70
  -XX:GCHeapFreeLimit=5
  -XX:NewRatio=4)
campaign_engine_stack=-Xss512m
engine_java() {
  local heap=${engine_memory_mb:-8192} main="" start index next status
  local out most floor
  local -a room=()
  for (( index = 1; index < $#; index++ )); do
    [[ "${!index}" == -cp ]] || continue
    next=$((index + 2))
    main=${!next}
    break
  done
  start=$(campaign_engine_start_mb "${main}" "${engine_need_mb:-}")
  if [[ "${campaign_head_charging}" == 1 ]] \
      && (( $(campaign_jvm_charge_mb "${main}" "${heap}") \
        > $(campaign_head_most_mb localhost) )); then
    most=$(campaign_head_most_mb)
    floor=0
    [[ -z "${engine_need_mb:-}$(campaign_engine_need_mb "${main}")" \
       && " ${campaign_engine_outgrown} " != *" ${main}="* ]] \
      || floor=${start}
    if (( most > 0 )); then
      while (( heap > floor )) \
          && (( $(campaign_jvm_charge_mb "${main}" "${heap}") > most )); do
        heap=$(( heap - 1024 > floor ? heap - 1024 : floor ))
      done
      (( start <= heap )) || start=${heap}
      (( $(campaign_jvm_charge_mb "${main}" "${heap}") <= most )) \
        || die "${main##*.} needs ${start} MB of heap, charged \
$(campaign_jvm_charge_mb "${main}" "${start}") MB: no host of the pool can \
ever hold it, the most one holds with no charge standing being ${most} MB"
      (( heap == ${engine_memory_mb:-8192} )) \
        || printf '[campaign] %s may grow to %s MB of heap, the most a host \
of the pool can ever hold (%s MB)\n' "${main##*.}" "${heap}" "${most}" >&2
    fi
  fi
  [[ "$(campaign_z3_room_mb "${main}" "${heap}")" != \
      "${campaign_z3_least_room_mb}" ]] \
    || printf '[campaign] %s at %s MB leaves no z3 room under the host'"'"'s \
ceiling: its z3s run in the least, %s MB\n' "${main##*.}" "${heap}" \
      "${campaign_z3_least_room_mb}" >&2
  while (( start < heap )); do
    out=$(mktemp) || return
    status=0
    campaign_z3_room_flag room "${main}" "${start}"
    campaign_head_charged "${room[@]}" \
      "$(campaign_jvm_charge_mb "${main}" "${start}")" \
      campaign_engine_jvm \
      "${campaign_root:+${campaign_root}/engine_peak_mb}" \
      env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${start}" "${java_bin}" \
      "${campaign_engine_oom[@]}" "${campaign_engine_stack}" "$@" \
      >"${out}" || status=$?
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
  campaign_z3_room_flag room "${main}" "${heap}"
  campaign_head_charged "${room[@]}" \
    "$(campaign_jvm_charge_mb "${main}" "${heap}")" \
    campaign_engine_jvm \
    "${campaign_root:+${campaign_root}/engine_peak_mb}" \
    env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
    "${campaign_engine_oom[@]}" "${campaign_engine_stack}" "$@"
}

campaign_compose_z3_least_room_mb=2048
campaign_compose_z3_most_room_mb=18432
campaign_z3_least_room_mb=256
campaign_z3_room_mb() {
  local main=$1 heap=$2 room limit
  case "${main}" in
    edu.uva.liftlab.graphchecker.compose.ComposeMain) ;;
    edu.uva.liftlab.graphchecker.explore.ObligationSolverMain)
      campaign_solver_z3_room_mb ""
      return 0 ;;
    *)
      printf '0\n'
      return 0 ;;
  esac
  local campaign_host_max_used_pct=${campaign_head_max_used_pct}
  limit=$(campaign_host_limit_mb "$(campaign_host_total_mb localhost \
    | tail -n 1)")
  room=$(( limit - $(campaign_jvm_footprint_mb "${heap}") ))
  (( room <= campaign_compose_z3_least_room_mb )) \
    || room=${campaign_compose_z3_least_room_mb}
  (( room >= campaign_z3_least_room_mb )) || room=${campaign_z3_least_room_mb}
  printf '%s\n' "${room}"
}

campaign_z3_room_flag() {
  local -n flag=$1
  local mb
  mb=$(campaign_z3_room_mb "$2" "$3")
  flag=()
  (( mb == 0 )) || flag=(--room "${mb}")
}

campaign_z3_room_granted_mb=0
campaign_z3_room_grant_id=""
campaign_z3_room_grant() {
  local host=$1 room=$2 more status=0
  campaign_z3_room_granted_mb=${room}
  campaign_z3_room_grant_id=""
  more=$(campaign_host_room "${host}") || return 0
  (( room + more <= campaign_compose_z3_most_room_mb )) \
    || more=$(( campaign_compose_z3_most_room_mb - room ))
  (( more > 0 )) || return 0
  campaign_host_head_start=1 campaign_host_try_charge "${host}" "${more}"
  (( status == 0 )) || return 0
  campaign_z3_room_granted_mb=$(( room + more ))
  campaign_z3_room_grant_id=${campaign_host_charge_id}
}

campaign_compose_z3_pair_mb=2048
campaign_compose_z3_host_most_mb=16384
campaign_z3_hosts=""
campaign_z3_hosts_grants=()
campaign_z3_hosts_grant() {
  local placed=$1 host name more status=0
  campaign_z3_hosts=""
  campaign_z3_hosts_grants=()
  while IFS= read -r host; do
    [[ "$(campaign_host_key "${host}")" != \
        "$(campaign_host_key "${placed}")" ]] || continue
    more=$(campaign_host_room "${host}") || continue
    (( more <= campaign_compose_z3_host_most_mb )) \
      || more=${campaign_compose_z3_host_most_mb}
    more=$(( more / campaign_compose_z3_pair_mb * campaign_compose_z3_pair_mb ))
    (( more > 0 )) || continue
    campaign_host_try_charge "${host}" "${more}"
    (( status == 0 )) || continue
    name=${host}
    ! campaign_host_is_local "${host}" || name=$(hostname -s)
    campaign_z3_hosts+="${campaign_z3_hosts:+,}${name}=${more}"
    campaign_z3_hosts_grants+=("${host} ${campaign_host_charge_id}")
  done < <(campaign_worker_host_list)
}

campaign_jvm_charge_mb() {
  printf '%s\n' "$(( $(campaign_jvm_footprint_mb "$2") \
    + $(campaign_z3_room_mb "$1" "$2") ))"
}

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

campaign_engine_peak() {
  local file=$1 peak=$2 held tmp at
  [[ -n "${file}" && "${peak}" =~ ^[0-9]+$ ]] || return 0
  [[ -d "$(dirname -- "${file}")" ]] || return 0
  until mkdir "${file}.lock" 2>/dev/null; do
    if at=$(stat -c %Y "${file}.lock" 2>/dev/null) \
        && (( $(date +%s) - at >= 10 )); then
      rmdir "${file}.lock" 2>/dev/null || true
    fi
    sleep 0.1
  done
  read -r held 2>/dev/null <"${file}" || held=0
  if (( peak > ${held:-0} )); then
    tmp=$(mktemp "${file}.XXXXXX") \
      && printf '%s\n' "${peak}" >"${tmp}" && mv -f -- "${tmp}" "${file}"
  fi
  rmdir "${file}.lock" 2>/dev/null || true
}

campaign_engine_start_mb() {
  local main=$1 need=${2:-} heap=${engine_memory_mb:-8192} grown
  [[ -n "${need}" ]] || need=$(campaign_engine_need_mb "${main}")
  [[ -n "${need}" ]] || need=${heap}
  grown=$(sed -n "s|.* ${main}=\([0-9]*\).*|\1|p" \
    <<<"${campaign_engine_outgrown}")
  (( ${grown:-0} <= need )) || need=${grown}
  printf '%s\n' "$(( need < heap ? need : heap ))"
}

campaign_engine_need_mb() {
  case "$1" in
    *.GraphCheckerMain|*.ComposeMain) echo 4096 ;;
    *.GapLedgerMain) echo 6144 ;;
    *.CausynthTraceRecorder|*.ConcolicScheduler|*.ConfirmMain|*.LineageScan \
      |*.ScopeGrowth|*.VerifyWovenClasses|*.ExposedRegionPlanMain \
      |*.WeaveKey) \
      echo 2048 ;;
  esac
}

campaign_head_need_mb() {
  local main start largest=0 peak heap room compose
  compose=edu.uva.liftlab.graphchecker.compose.ComposeMain
  heap=$(campaign_jvm_footprint_mb "${engine_memory_mb:-8192}")
  room=$(campaign_z3_room_mb "${compose}" \
    "$(campaign_engine_start_mb "${compose}")")
  if [[ -n "${campaign_root}" ]] \
      && read -r peak 2>/dev/null <"${campaign_root}/engine_peak_mb" \
      && [[ "${peak}" =~ ^[1-9][0-9]*$ ]]; then
    largest=$(( (peak * 5 + 511) / 512 * 128 ))
    (( largest >= 1024 )) || largest=1024
    printf '%s\n' "$(( (largest < heap ? largest : heap) + room ))"
    return 0
  fi
  for main in edu.uva.liftlab.graphchecker.explore.ExploreMain "${compose}"; do
    start=$(campaign_jvm_charge_mb "${main}" \
      "$(campaign_engine_start_mb "${main}")")
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
    runtime_classpath="${runtime_classpath}:${project_classpath}"
  fi
  run_in_directory "${graphchecker_work_dir}" engine_java \
    "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
    "-Dcausynth.system.doors=${causynth_system_doors}" \
    "-Dcausynth.doors.only.roots=${causynth_doors_only_roots}" \
    "-Dcausynth.export.guard.writers=${causynth_export_guard_writers:-false}" \
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
  require_file "loop body bound declarations" "${causynth_loop_bounds}"
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
  fi
  if [[ -n "${causynth_root_domains}" ]]; then
    require_file "declared root domains" "${causynth_root_domains}"
  fi
  local key
  for key in solver_timeout_ms replay_timeout_s seed_replay_time_factor \
      recording_max_trace_mb schedule_max_jobs region_path_max_waves \
      compose_max_valuations causynth_loop_default_bound reproduce_runs \
      reproduce_time_factor reproduce_min_s reproduce_charge_pct \
      campaign_budget_s \
      campaign_reserve_s \
      campaign_max_claims; do
    require_positive_integer "${key}"
  done
  (( campaign_budget_s > campaign_reserve_s )) \
    || die "campaign_budget_s (${campaign_budget_s}) must exceed its reserve \
campaign_reserve_s (${campaign_reserve_s}): the exploration would end before \
it began"
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
  [[ "${stream_stop_at_witness}" == true || "${stream_stop_at_witness}" == false ]] \
    || die "stream_stop_at_witness must be true or false: ${stream_stop_at_witness}"
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
  if [[ -s "$(campaign_grown_scope)/${scope_growth_manifest}" ]]; then
    system_properties+=("-Dcausynth.process.dirs=$(campaign_grown_scope)")
  fi
  if [[ -n "${causynth_lineage_roots}" ]]; then
    system_properties+=("-Dcausynth.lineage.roots=${causynth_lineage_roots}")
  fi
  system_properties+=("-Dcausynth.system.doors=${causynth_system_doors}")
  system_properties+=("-Dcausynth.system.view=${causynth_system_view}")
  system_properties+=("-Dcausynth.doors.only.roots=${causynth_doors_only_roots}")
  system_properties+=("-Dcausynth.io.doors=$(campaign_io_doors)")
  if [[ -n "${causynth_communication_mappings}" ]]; then
    require_file "communication mapping" "${causynth_communication_mappings}"
    system_properties+=(
      "-Dcausynth.communication.mappings=${causynth_communication_mappings}"
    )
  fi
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
  system_properties+=(
    "-Dcausynth.region.skeletons=${causynth_region_skeletons}"
  )
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
      "-Dcausynth.concolic.campaign.max.tasks=${schedule_max_jobs}"
    )
  fi
  require_file "GraphChecker jar" "${graphchecker_jar}"
  run_in_directory "${graphchecker_work_dir}" engine_java \
    "${system_properties[@]}" \
    -cp "${graphchecker_jar}" \
    edu.uva.liftlab.graphchecker.GraphCheckerMain \
    -i "${project_classes_dir}" \
    -x "${project_classpath}" \
    -o "${analysis_classes_dir}"
}

campaign_analyze() {
  local stage=$1 log=$2 status=0
  mkdir -p -- "$(dirname "${log}")"
  run_capturing_status do_analyze > >(tee -- "${log}") 2>&1
  wait "$!"
  (( status == 0 )) && return 0
  campaign_fail "${stage}" GraphCheckerMain "${log}" \
    "the static pass failed with exit ${status}: $(campaign_thrown "${log}")"
}

campaign_lineage_classes() {
  local out="${causynth_output_dir}/lineage-classes"
  local -a roots=()
  if [[ ! -d "${out}" ]]; then
    IFS=: read -r -a roots <<<"${causynth_lineage_roots}"
    [[ -z "${trace_test}" || ! -d "${project_test_classes_dir}" ]] \
      || roots+=("${project_test_classes_dir}#${trace_test%%#*}")
    rm -rf -- "${out}.partial"
    mkdir -p "${out}.partial"
    run_java_main edu.uva.liftlab.graphchecker.plan.LineageScan \
      "${out}.partial" "${project_classes_dir}:$(campaign_grown_scope)" \
      "${roots[@]}" >&2 || return 1
    mv -- "${out}.partial" "${out}"
  fi
  printf '%s\n' "${out}"
}

scope_growth_manifest=GROWN
campaign_grown_scope() {
  printf '%s\n' "${causynth_output_dir}/scope-classes"
}

campaign_io_doors() {
  printf '%s\n' "${causynth_output_dir}/io_doors.jsonl"
}

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
    campaign_scope_doors "${grown}" "${roots[@]}"
  done
}

campaign_scope_doors() {
  local grown=$1 summary
  shift
  summary=$(run_java_main edu.uva.liftlab.graphchecker.plan.ScopeGrowth \
    --doors "${grown}" "${project_classes_dir}" "${project_classpath}" \
    "$@") \
    || campaign_fail SEED ScopeGrowth "${grown}" "door scope failed"
  campaign_log "scope growth: ${summary}"
}

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
  require_file "candidate data-flow graph" "${candidate_graph}"
  args+=(--candidate-graph "${candidate_graph}")
  require_file "static scope map" "${causynth_static_scope_map}"
  args+=(--static-scope-map "${causynth_static_scope_map}")
  args+=(--max-jobs "${schedule_max_jobs}")
  [[ -z "${declared_target_occurrence}" ]] \
    || args+=(--target-occurrence "${declared_target_occurrence}")
  run_java_main edu.uva.liftlab.graphchecker.plan.ConcolicScheduler \
    "${args[@]}"
}

do_compose() {
  ensure_output_directory "$(dirname "${composed_smt}")"
  local -a selection=() cap=()
  local declared engine_need_mb status said composed
  engine_need_mb=$(campaign_solver_heap_mb "${compose_sessions_dir}" \
    "${campaign_solver_live_pct}")
  declared=$(campaign_declared_target_occurrence)
  [[ -z "${declared}" ]] || selection+=(--anchor "${declared}")
  [[ -z "${causynth_root_domains}" ]] \
    || selection+=(--root-domains "${causynth_root_domains}")
  [[ -z "${compose_reuse_dir:-}" ]] \
    || selection+=(--reuse "${compose_reuse_dir}")
  said=$(mktemp) || return
  while true; do
    status=0
    run_java_main edu.uva.liftlab.graphchecker.compose.ComposeMain \
      --sessions "${compose_sessions_dir}" \
      --static-scope-map "${causynth_static_scope_map}" \
      --output "${composed_smt}" \
      --manifest "${composition_manifest}" \
      --solver-timeout-ms "${solver_timeout_ms}" \
      --max-valuations "${compose_max_valuations}" \
      --z3 "${z3_bin}" \
      "${cap[@]}" "${selection[@]}" 2> >(tee -- "${said}" >&2) \
      || status=$?
    wait "$!" 2>/dev/null || true
    (( status == campaign_jvm_out_of_heap_status )) || break
    composed=$(grep -oE '\([0-9]+ composed\)' "${said}" | tail -n 1 \
      | tr -dc '0-9')
    [[ -n "${composed}" ]] && (( composed > 1 )) || break
    cap=(--max-paths "$(( composed / 2 ))")
    printf '[campaign] ComposeMain ran out of the engine heap with %s path(s) \
composed: composed again with at most %s\n' "${composed}" \
      "$(( composed / 2 ))" >&2
  done
  rm -f -- "${said}"
  return "${status}"
}

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
    "CAUSYNTH_VIEW_HOLD_MAX_MS=${view_hold_max_ms}"
    "CAUSYNTH_VIEW_HOLD_MAX_RECORDED_MS=${view_hold_max_ms}"
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
  CAUSYNTH_TRACE_MODE=region-state campaign_analyze SEED "${trace_dir}/weave.log"
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
  local name
  name=$(awk '$1 == "exception_target:" {print $2; exit}' \
    "${causynth_target_spec}")
  run_java_main edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder \
    --trace-dir "${trace_dir}" --test "${trace_test}" "${declared[@]}" \
    --target "${name}=${candidate_graph},${causynth_static_scope_map},\
${causynth_region_skeletons},${trace_dir}"
}


campaign_root=""
campaign_final=""
campaign_stage_metrics=""
campaign_provenance=""
campaign_recorded_workload_s=""
campaign_recorded_workload_rss_mb=""
campaign_member_rows=""
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

campaign_thrown() {
  grep -E '^(Caused by: |Exception in thread "[^"]*" |Terminating due to )?[[:alnum:]_.$]+(Exception|Error)(: |$)' \
    -- "$1" 2>/dev/null | tail -n 1 \
    | sed -E 's/^(Caused by: |Exception in thread "[^"]*" |Terminating due to )//'
}

campaign_count() {
  local stage=$1 component=$2 artifact=$3 label=$4 value=$5
  case "${value}" in
    ''|*[!0-9]*)
      campaign_fail "${stage}" "${component}" "${artifact}" \
        "${label} is not a count: '${value}'" ;;
  esac
}

require_nonempty() {
  [[ -s "$2" ]] || die "$1 is missing or empty: $2"
}

require_fresh() {
  require_nonempty "$1" "$2"
  [[ "$2" -nt "$3" ]] || die "$1 predates the stage that had to write it: $2"
}

campaign_digest() {
  [[ -f "$1" ]] || die "cannot digest a missing artifact: $1"
  sha256sum -- "$1" | awk '{print $1}'
}

campaign_require_json() {
  local label=$1 path=$2
  [[ -s "${path}" ]] || {
    echo "${label} is missing or empty: ${path}" >&2
    return 1
  }
  jq -e -s 'length == 1 and (.[0] | type) == "object"' \
    "${path}" >/dev/null
}

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

campaign_tree_digest() {
  [[ -e "$1" ]] || { printf 'absent'; return 0; }
  if [[ -f "$1" ]]; then
    campaign_digest "$1"
    return 0
  fi
  (cd "$1" && find . -type f -print0 \
    | xargs -0 -r -n 256 -P 16 sha256sum | LC_ALL=C sort -k 2) \
    | sha256sum | awk '{print $1}'
}

campaign_kind_digest() {
  case "$1" in
    file) campaign_digest "$2" ;;
    optional) campaign_optional_digest "$2" ;;
    tree) campaign_tree_digest "$2" ;;
    string) printf '%s' "$2" | sha256sum | awk '{print $1}' ;;
    *) return 2 ;;
  esac
}

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
  if ! porcelain=$(git -C "${repo}" --no-optional-locks status --porcelain)
  then
    return 1
  fi
  if ! worktree=$( { printf '%s\n' "${porcelain}"
      printf '%s\n' "${porcelain}" | awk '{print $NF}' \
        | while IFS= read -r entry; do
            [[ -n "${entry}" ]] || continue
            [[ -e "${repo}/${entry}" ]] || continue
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

campaign_adapter_timeout_s=""
campaign_adapter_timeout_rule=""

campaign_adapter_timeout_status=124
campaign_adapter_killed_status=137

campaign_adapter_kill_grace_s=30

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

campaign_local_scratch_root=""

campaign_init_local_scratch_root() {
  local run_key
  if [[ -n "${CAUSYNTH_LOCAL_SCRATCH:-}" ]]; then
    campaign_local_scratch_root=${CAUSYNTH_LOCAL_SCRATCH}
    return 0
  fi
  run_key=$(printf '%s' "${campaign_root}" | sha256sum | cut -c1-16)
  campaign_local_scratch_root="/localtmp/$(id -un)/graphchecker/${run_key}"
}


campaign_ssh_options=(
  -o BatchMode=yes
  -o ServerAliveInterval=30
  -o ServerAliveCountMax=3
  -n
)

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

campaign_remote_watchdog_interval_s=5

campaign_remote_bound_margin_s=300

campaign_remote_worker_bound_s() {
  printf '%s\n' "$(( replay_timeout_s + (solver_timeout_ms + 999) / 1000 \
    + campaign_remote_bound_margin_s ))"
}

campaign_remote_visibility_wait_s=120

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

campaign_remote_env_assignments() {
  local row config_key config_env config_flags config_default
  for row in "${workflow_config_keys[@]}"; do
    read_config_key_row "${row}"
    [[ -n "${config_env}" && "${config_flags}" == *k* ]] || continue
    printf '%s=%s\n' "${config_env}" "${!config_key}"
  done
}

campaign_write_remote_worker_script() {
  local script=$1 logs=$2 bound=$3 mode=$4
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
    printf '  >%q 2>%q &\n' "${logs}stdout.log" "${logs}stderr.log"
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

campaign_dispatch_remote() {
  local host=$1 logs=$2 bound=$3 status=0
  shift 3
  campaign_write_remote_worker_script "${logs}remote-worker.sh" "${logs}" \
    "${bound}" "$@"
  run_capturing_status campaign_ssh "${campaign_ssh_options[@]}" -- \
    "${host}" "exec /bin/bash $(printf '%q' "${logs}remote-worker.sh")" \
    >"${logs}ssh.log" 2>&1
  return "${status}"
}

campaign_await_remote_result() {
  local worker=$1 host=$2 obligation_id=$3 staged=$4 kind=${5:-}
  local result="${worker}/obligation_result.jsonl"
  local waited=0 session_id=""
  until [[ -s "${worker}/solve_again" || -s "${worker}/replay_again" ]] \
      || { [[ -s "${result}" ]] && { [[ "${kind}" != REPLAY ]] \
        || [[ "$(jq -r '.verdict // ""' "${result}" 2>/dev/null)" \
          != SAT_MODEL_READY ]]; }; }; do
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
  ls "${worker}" >/dev/null 2>&1 || true
  [[ ! -s "${worker}/solve_again" && ! -s "${worker}/replay_again" ]] \
    || return 0
  session_id=$(jq -r '.sessionId // ""' "${result}" 2>/dev/null) || session_id=""
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

campaign_reap_remote_workers() {
  local host pid
  local -a reaping=()
  [[ -n "${campaign_worker_hosts}" ]] || return 0
  [[ -n "${campaign_root}" ]] || return 0
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

campaign_stream_stop_solvers() {
  local host pid
  local -a stopping=()
  [[ -n "${sessions:-}" ]] || return 0
  while IFS= read -r host; do
    campaign_reap_on_host "${host}" \
      "ObligationSolverMain .*--sessions ${sessions}( |\$)" &
    stopping+=("$!")
  done < <(campaign_worker_host_list)
  for pid in "${stopping[@]}"; do
    wait "${pid}" || true
  done
}

campaign_reap_on_host() {
  local host=$1 pattern=$2 script
  script="pattern=$(printf '%q' "${pattern}")
pkill -TERM -u \"\$(id -u)\" -f \"\${pattern}\" 2>/dev/null || exit 0
for at in \$(seq $(( campaign_adapter_kill_grace_s * 2 ))); do
  pgrep -u \"\$(id -u)\" -f \"\${pattern}\" >/dev/null 2>&1 || exit 0
  sleep 0.5
done
pkill -KILL -u \"\$(id -u)\" -f \"\${pattern}\" 2>/dev/null || true"
  if campaign_host_is_local "${host}"; then
    bash -s <<<"${script}" >/dev/null 2>&1 || true
  else
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
    "GRAPHCHECKER_JAR=${graphchecker_jar}"
    "$@"
  )
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

campaign_seed() {
  local marker="${campaign_root}/.seed-started"
  local catalog_sha plan_sha
  : >"${marker}"
  campaign_analyze_grown_scope
  do_workload
  require_fresh "static candidate data-flow graph" "${candidate_graph}" \
    "${marker}"
  require_fresh "runtime region plan" "${runtime_region_plan}" "${marker}"
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
  local recorded_schedule
  recorded_schedule="$(dirname "${runtime_region_plan}")/schedule.jsonl"
  if [[ -s "${recorded_schedule}" ]]; then
    cp -f "${recorded_schedule}" "${iteration_dir}/recorded_schedule.jsonl"
  fi
  local recorded_chain
  recorded_chain="$(dirname "${runtime_region_plan}")/zk_chain.jsonl"
  if [[ -s "${recorded_chain}" ]]; then
    cp -f "${recorded_chain}" "${iteration_dir}/zk_chain.jsonl"
  fi
  schedule_output_dir="${iteration_dir}"
  local plan_log="${iteration_dir}/plan.log"
  run_capturing_status do_schedule 2>"${plan_log}"
  cat -- "${plan_log}" >&2
  (( status == 0 )) || campaign_fail PLAN ConcolicScheduler "${plan_log}" \
    "the scheduler failed with exit ${status}: $(campaign_thrown "${plan_log}")"
  local resolved
  resolved=$(jq -r '.target.occurrenceId // ""' "${index}")
  [[ -n "${resolved}" ]] \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the schedule index names no declared target occurrence"
  [[ "${resolved}" == "${declared_target_occurrence}" ]] \
    || campaign_log "declared target ${declared_target_occurrence} = ${resolved}"
  declared_target_occurrence=${resolved}
  runtime_region_plan="${frozen}"
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
  jq -e --arg region_hash "${region_hash}" \
    --argjson region_size "${region_size}" '
      .regionPlan.sha256 == $region_hash
        and .regionPlan.sizeBytes == $region_size
    ' "${index}" >/dev/null \
    || campaign_fail PLAN ConcolicScheduler "${index}" \
      "the region-path schedule index does not commit the frozen region plan"

  mkdir -p "${seed_dir}"
  ln -f "${plan}" "${seed_plan}"

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

campaign_weave_key() {
  local plan=$1 key status=0
  key=$(run_in_directory "${graphchecker_work_dir}" engine_java \
    "-Dcausynth.concolic.task.plan=${plan}" \
    "-Dcausynth.concolic.task.id=$(campaign_task_ids "${plan}")" \
    "-Dcausynth.concolic.campaign.max.tasks=${schedule_max_jobs}" \
    -cp "${graphchecker_jar}" edu.uva.liftlab.graphchecker.causynth.WeaveKey) \
    || status=$?
  [[ "${status}" -eq 0 && "${key}" =~ ^[0-9a-f]{64}$ ]] \
    || campaign_fail INSTRUMENT WeaveKey "${plan}" \
      "the plan's weave key could not be read (exit ${status}): ${key}"
  printf '%s\n' "${key}"
}

campaign_instrument() {
  local iteration_dir=$1
  local classes=${2:-${iteration_dir}/instrumented-classes}
  local key=${3:-}
  local plan=${4:-${iteration_dir}/execution_task_plan.jsonl}
  local ids
  ids=$(campaign_task_ids "${plan}")
  [[ -n "${ids}" ]] || campaign_fail INSTRUMENT CAMPAIGN "${plan}" \
    "the campaign plan published no task id"
  [[ -n "${key}" ]] || key=$(campaign_weave_key "${plan}") || exit 1
  rm -rf -- "${classes}"
  local analysis_classes_dir="${classes}"
  export CAUSYNTH_CONCOLIC_TASK_PLAN="${plan}"
  export CAUSYNTH_CONCOLIC_TASK_ID="${ids}"
  campaign_analyze INSTRUMENT "$(dirname "${classes}")/instrument.log"
  unset CAUSYNTH_CONCOLIC_TASK_PLAN CAUSYNTH_CONCOLIC_TASK_ID
  [[ -n "$(find "${classes}" -name '*.class' -print -quit 2>/dev/null)" ]] \
    || campaign_fail INSTRUMENT CAMPAIGN "${classes}" \
      "union instrumentation wrote no class file"
  campaign_verify_woven_classes "${classes}"
  printf '%s\n' "${key}" >"$(dirname "${classes}")/weave_key"
}

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

campaign_replay_killed=""
campaign_replay_refused_mb=""
campaign_refused_file=workload_refused_mb
campaign_out_of_heap_file=workload_out_of_heap_mb
campaign_ending_file=workload_ending
campaign_host_end_used_pct=85

campaign_replay() {
  local role=$1 plan=$2 ids=$3 classes=$4 results=$5 worker=$6 charged=$7
  local region_results=${8:-required}
  local status=0 started=${SECONDS}
  campaign_replay_killed=""
  campaign_replay_refused_mb=""
  local heap
  heap=$(campaign_replay_heap_mb "${campaign_replay_heap_basis_mb:-${charged}}")
  local sessions="${campaign_sessions_dir:-$(dirname "${results}")/sessions}"
  mkdir -p "${sessions}"
  require_nonempty "concolic execution task plan" "${plan}"
  [[ ! -e "${worker}/replay.log" ]] || die \
    "replay output already exists; worker directories are written once: ${worker}"
  mkdir -p "${worker}" "$(dirname "${results}")"
  run_capturing_status \
    campaign_run_adapter "replay(${role})" "${concolic_replay_command}" \
    "CAUSYNTH_CHARGED_MB=${charged}" \
    "CAUSYNTH_HEAP_BASIS_MB=${campaign_replay_heap_basis_mb:-${charged}}" \
    "CAUSYNTH_CONCOLIC_TASK_PLAN=${plan}" \
    "CAUSYNTH_CONCOLIC_TASK_ID=${ids}" \
    "CAUSYNTH_CONCOLIC_RESULTS=${results}" \
    "CAUSYNTH_CONCOLIC_SESSIONS=${sessions}" \
    "CAUSYNTH_CONCOLIC_CLASSES=${classes}" \
    "CAUSYNTH_CONCOLIC_WORKER_DIR=${worker}" \
    "CAUSYNTH_CONCOLIC_MAX_TASKS=${schedule_max_jobs}" \
    "CAUSYNTH_VIEW_HOLD_MAX_MS=$(campaign_view_hold_wall_ms "${worker}")" \
    "CAUSYNTH_VIEW_HOLD_MAX_RECORDED_MS=${view_hold_max_ms}" \
    "CAUSYNTH_TRACE_TEST=${trace_test}" \
    "CAUSYNTH_TRACE_MODE=replay-context" \
    "CAUSYNTH_SCHEDULE_PREFIX=${campaign_schedule_prefix:-}" \
    "CAUSYNTH_STATIC_SCOPE_MAP=${causynth_static_scope_map}" \
    "CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root}/$(basename \
      "${worker}")" \
    >"${worker}/replay.log" 2>&1
  if (( status == campaign_jvm_out_of_heap_status )); then
    printf '%s\n' "${heap}" >"${worker}/${campaign_out_of_heap_file}"
    campaign_replay_killed="ran out of its ${heap} MB heap (exit ${status})"
    campaign_log "replay role=${role} ${campaign_replay_killed}: ${sessions}"
    return 0
  fi
  if [[ -n "${campaign_adapter_timeout_s}" ]] \
      && { [[ "${status}" -eq "${campaign_adapter_timeout_status}" ]] \
        || [[ "${status}" -eq "${campaign_adapter_killed_status}" ]]; }; then
    local lived=$(( SECONDS - started ))
    if [[ "${status}" -eq "${campaign_adapter_timeout_status}" ]] \
        || (( lived >= campaign_adapter_timeout_s )); then
      campaign_replay_killed="exceeded ${campaign_adapter_timeout_rule}"
    elif read -r campaign_replay_refused_mb 2>/dev/null \
        <"${worker}/${campaign_refused_file}" \
        && [[ "${campaign_replay_refused_mb}" =~ ^[0-9]+$ ]]; then
      campaign_replay_killed="was ended at ${campaign_replay_refused_mb} MB \
after ${lived}s: its host could not take its growth (its watcher, \
campaign_watch_workload)"
    else
      campaign_replay_refused_mb=""
      campaign_replay_killed="was killed (exit ${status}) after ${lived}s, \
inside its ${campaign_adapter_timeout_s}s bound: by its memory \
reservation (the replay log says so), the kernel's memory killer or an \
operator"
    fi
    campaign_log "replay role=${role} ${campaign_replay_killed} \
(exit ${status}): ${sessions}"
    if [[ "${region_results}" == required ]]; then
      campaign_fail REPLAY WORKLOAD "${sessions}" \
        "the concolic replay ${campaign_replay_killed}; what it published is \
a truncated run and its log is in ${worker}/replay.log"
    fi
    return 0
  fi
  if [[ "${region_results}" == required ]]; then
    local live="" activations
    while IFS= read -r -d '' activations; do
      live=$(campaign_rows "${activations}" | head -c 1) || live=""
      [[ -z "${live}" ]] || break
    done < <(find "${sessions}" -mindepth 2 -maxdepth 2 \
      -name activations.jsonl.gz -print0 2>/dev/null)
    [[ -n "${live}" ]] || campaign_fail REPLAY WORKLOAD "${sessions}" \
      "the concolic replay published no activation row (exit ${status}); the workload terminated before its selected regions ran and its exception is in ${worker}/replay.log"
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


campaign_target_unanswered() {
  local sessions=$1 task
  task=$(awk -F'\t' '$1 == "TARGET" {print $6; exit}' \
    <<<"${campaign_member_rows}")
  [[ -n "${task}" ]] || return 0
  local -a gaps=()
  mapfile -d '' gaps < <(find "${sessions}" -mindepth 2 -maxdepth 2 \
    -name gaps.jsonl.gz -print0)
  campaign_rows "${gaps[@]}" | jq -r --arg task "${task}" \
      'select(.kind == "TASK_UNANSWERED" and .subject == $task) | .detail' \
    | head -n 1 | cut -c1-600
}

campaign_target_reached() {
  local sessions=$1 map=$2
  local -a rows=()
  mapfile -d '' rows < <(find "${sessions}" -mindepth 2 -maxdepth 2 \
    -name targets.jsonl.gz -print0)
  (( ${#rows[@]} > 0 )) || return 0
  campaign_rows "${rows[@]}" | jq -r -n --slurpfile map "${map}" '
    [$map[] | select(.role == "TARGET_SITE") | .siteId
     | sub("#u[0-9]+$"; "")] as $methods
    | [inputs | .anchorSiteId
       | select(. as $site | any($methods[] + "#"; . as $method
           | $site | startswith($method)))]
    | first // ""'
}

campaign_replay_memory_factor=7
campaign_seed_charge_factor=2

campaign_view_hold_max() {
  local iteration_dir=$1 recorded replayed slowdown cut_window=""
  local recorded_file="${causynth_output_dir}/runtime/window_ms"
  local replayed_file="${iteration_dir}/seed-result/focused/window_ms"
  recorded=$(cat "${recorded_file}" 2>/dev/null) || recorded=""
  replayed=$(cat "${replayed_file}" 2>/dev/null) || replayed=""
  [[ "${recorded%$'\t'cut}" =~ ^[1-9][0-9]*$ \
      && "${replayed%$'\t'cut}" =~ ^[0-9]+$ ]] \
    || campaign_fail REPLAY VIEW_HOLD_MAX "${iteration_dir}" "the recording's \
or the seed replay's window stated no duration (${recorded_file}: \
'${recorded}', ${replayed_file}: '${replayed}'), so the view hold's bound \
cannot be scaled to this VM's slowdown"
  [[ "${recorded}" != *$'\t'cut ]] || cut_window="recording"
  [[ "${replayed}" != *$'\t'cut ]] || cut_window="${cut_window:+${cut_window},}seed-replay"
  recorded=${recorded%$'\t'cut} replayed=${replayed%$'\t'cut}
  slowdown=$(( (replayed + recorded - 1) / recorded ))
  (( slowdown >= 1 )) || slowdown=1
  [[ -z "${cut_window}" ]] || echo "[campaign] view_hold_max: the ${cut_window} window was \
cut (its run ended inside it), so the slowdown ${slowdown} rests on part of \
the workload's window" >&2
  printf '%s\t%s\t%s\n' "${slowdown}" "$(( view_hold_max_ms * slowdown ))" \
    "${cut_window}" >"$(dirname "${iteration_dir}")/view_hold_max.tsv"
}

campaign_view_hold_wall_ms() {
  local dir=$1 level
  for level in 1 2 3 4 5; do
    dir=$(dirname "${dir}")
    if [[ -s "${dir}/view_hold_max.tsv" ]]; then
      cut -f2 "${dir}/view_hold_max.tsv"
      return 0
    fi
  done
}

campaign_session_replay() {
  local iteration_dir=$1 bound need charge runs heap aside session
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
  for runs in 1 2; do
    campaign_head_charged "${charge}" campaign_seed_replay "${iteration_dir}" \
      "${causynth_static_scope_map}" "${charge}" "${bound}" \
      "seed_replay_time_factor=${seed_replay_time_factor} x the recording's \
${campaign_recorded_workload_s}s workload and at least \
replay_timeout_s=${replay_timeout_s}" "${need}"
    read -r heap 2>/dev/null \
      <"${iteration_dir}/seed-result/focused/${campaign_out_of_heap_file}" \
      || break
    aside="${iteration_dir}/seed-result/ended-1"
    (( runs == 1 )) && campaign_replay_heap_raised "${heap}" "the seed \
replay, set aside in ${aside}" || campaign_fail REPLAY WORKLOAD \
      "${iteration_dir}/seed-result/focused" "the seed replay ran out of its \
${heap} MB heap $( (( runs == 1 )) && echo "-- the most a replay's heap is" \
      || echo "a second time")"
    mkdir -p -- "${aside}/sessions"
    mv -f -- "${iteration_dir}/seed-result/focused" "${aside}/"
    for session in "${iteration_dir}"/sessions/seed-result-*; do
      [[ ! -e "${session}" ]] || mv -f -- "${session}" "${aside}/sessions/"
    done
    (( need >= 2 * campaign_replay_heap_floor_mb )) \
      || need=$(( 2 * campaign_replay_heap_floor_mb ))
  done
  campaign_replay_measured "${iteration_dir}/seed-result/focused"
  (( campaign_replay_peak_mb > 0 )) || campaign_fail REPLAY WORKLOAD \
    "${iteration_dir}/seed-result/focused" "the seed replay stated no peak \
resident memory (workload_rss_mb): no replay after it has a measured need"
  campaign_view_hold_max "${iteration_dir}"
}

campaign_replay_peak_mb=0
campaign_replay_min_need_mb=512
campaign_replay_peaks=()
campaign_replay_peak_p90_mb=0
campaign_replay_least_heap_mb=4096
campaign_replay_heap_floor_mb=0
campaign_replay_means=()
campaign_replay_typical_mb=0
campaign_replay_spike_mb=0
campaign_replay_spikes=4
campaign_replay_cores=1
campaign_replay_seed_cores=1
campaign_replay_cores_x100=()
campaign_replay_typical_after=8

campaign_replay_need_mb() {
  if (( ${#campaign_replay_peaks[@]} < campaign_replay_typical_after )); then
    campaign_need_of_peak_mb "${campaign_replay_peak_mb}"
  else
    campaign_need_of_peak_mb "${campaign_replay_peak_p90_mb}"
  fi
}

campaign_replay_heap_mb() {
  local heap=$(( $1 / 2 ))
  (( heap >= campaign_replay_least_heap_mb )) \
    || heap=${campaign_replay_least_heap_mb}
  printf '%s\n' "${heap}"
}

campaign_replay_basis_mb() {
  local need
  need=$(campaign_replay_need_mb)
  (( need >= 2 * campaign_replay_heap_floor_mb )) \
    || need=$(( 2 * campaign_replay_heap_floor_mb ))
  printf '%s\n' "${need}"
}

campaign_replay_heap_raised() {
  local cap
  cap=$(campaign_replay_charge_mb 2147483647)
  (( $1 < cap )) || return 1
  (( 2 * $1 > campaign_replay_heap_floor_mb )) || return 0
  campaign_replay_heap_floor_mb=$(( 2 * $1 < cap ? 2 * $1 : cap ))
  campaign_log "a replay ran out of its $1 MB heap (${2}): it runs once \
more, and every replay from now on, at ${campaign_replay_heap_floor_mb} MB"
}

campaign_replay_full_need_mb() {
  local full peak
  full=$(campaign_replay_need_mb)
  peak=$(campaign_need_of_peak_mb "$1")
  (( full >= peak )) || full=${peak}
  campaign_replay_charge_mb "${full}"
}

campaign_need_of_peak_mb() {
  local need=$(( ($1 * 3 + 255) / 256 * 128 ))
  (( need >= campaign_replay_min_need_mb )) \
    || need=${campaign_replay_min_need_mb}
  printf '%s\n' "${need}"
}

campaign_replay_measured() {
  local peak mean first=$(( campaign_replay_peak_mb == 0 )) before
  read -r peak 2>/dev/null <"$1/workload_rss_mb" || return 0
  [[ "${peak}" =~ ^[0-9]+$ ]] || return 0
  read -r mean 2>/dev/null <"$1/workload_rss_mean_mb" || mean=${peak}
  [[ "${mean}" =~ ^[0-9]+$ ]] || mean=${peak}
  before=$(campaign_replay_need_mb)
  (( first )) || campaign_replay_typical "${peak}" "${mean}"
  campaign_replay_cores_measured "$1" "${first}"
  if (( peak > campaign_replay_peak_mb )); then
    campaign_replay_peak_mb=${peak}
    if (( ${#campaign_replay_peaks[@]} < campaign_replay_typical_after )); then
      (( ! first )) || campaign_replay_typical_mb=$(campaign_replay_life_mb \
        "$(( mean * 5 / 4 ))")
      campaign_replay_spike_mb=$(( peak > campaign_replay_typical_mb \
        ? peak - campaign_replay_typical_mb : 0 ))
    fi
  fi
  (( first )) || [[ "$(campaign_replay_need_mb)" != "${before}" ]] || return 0
  campaign_log "a replay peaked at ${peak} MB (${1}): every replay from now \
on needs $(campaign_replay_need_mb) MB (its heap's basis); a replay of the \
stream is charged $(campaign_stream_charge_mb REPLAY) MB at its start, with \
room for ${campaign_replay_spikes} ends of ${campaign_replay_spike_mb} MB \
beside it"
}

campaign_replay_cores_measured() {
  local x100 cores
  read -r x100 2>/dev/null <"$1/workload_cores_x100" || return 0
  [[ "${x100}" =~ ^[0-9]+$ ]] || return 0
  if (( $2 )); then
    campaign_replay_seed_cores=$(( (x100 + 99) / 100 ))
    (( campaign_replay_seed_cores >= 1 )) || campaign_replay_seed_cores=1
    cores=${campaign_replay_seed_cores}
  else
    campaign_replay_cores_x100+=("${x100}")
    (( ${#campaign_replay_cores_x100[@]} >= campaign_replay_typical_after )) \
      || return 0
    cores=$(( ($(campaign_percentile_90 "${campaign_replay_cores_x100[@]}") \
      + 99) / 100 ))
    (( cores >= campaign_replay_seed_cores )) \
      || cores=${campaign_replay_seed_cores}
  fi
  (( cores != campaign_replay_cores )) || return 0
  campaign_replay_cores=${cores}
  campaign_log "a replay keeps ${cores} core(s) busy (the seed's alone: \
${campaign_replay_seed_cores}; ${#campaign_replay_cores_x100[@]} after it \
returned): a host takes as many replays as its cores hold at that"
}

campaign_replay_life_mb() {
  local life=$(( ($1 + 127) / 128 * 128 ))
  (( life >= campaign_replay_min_need_mb )) \
    || life=${campaign_replay_min_need_mb}
  printf '%s\n' "${life}"
}

campaign_replay_typical() {
  local p90 p90_peak typical
  campaign_replay_peaks+=("$1")
  campaign_replay_means+=("${2:-$1}")
  (( ${#campaign_replay_peaks[@]} >= campaign_replay_typical_after )) \
    || return 0
  p90=$(campaign_percentile_90 "${campaign_replay_means[@]}")
  p90_peak=$(campaign_percentile_90 "${campaign_replay_peaks[@]}")
  campaign_replay_peak_p90_mb=${p90_peak}
  typical=$(campaign_replay_life_mb "${p90}")
  campaign_replay_spike_mb=$(( p90_peak > typical ? p90_peak - typical : 0 ))
  (( ${#campaign_replay_peaks[@]} > campaign_replay_typical_after \
     && typical == campaign_replay_typical_mb )) && return 0
  campaign_replay_typical_mb=${typical}
  campaign_log "the replays after the seed's held ${p90} MB or less over \
their lives in 9 of 10, and peaked at their ends at ${p90_peak} MB or less \
(${#campaign_replay_peaks[@]} returned): a replay of the stream is charged \
$(campaign_stream_charge_mb REPLAY) MB at its start, its end's growth as it \
grows, and a host admits one only with room for \
${campaign_replay_spikes} ends of ${campaign_replay_spike_mb} MB beside it"
}

campaign_percentile_90() {
  printf '%s\n' "$@" | LC_ALL=C sort -n \
    | awk '{ v[NR] = $1 } END { i = int(NR * 0.9); if (i < NR) i++;
             print v[i] + 0 }'
}

campaign_replay_charge_mb() {
  local need=$1 cap
  cap=$(( $(awk '/^MemTotal:/ {print int($2 / 1024)}' /proc/meminfo) \
    * campaign_host_max_used_pct / 200 ))
  printf '%s\n' "$(( need < cap ? need : cap ))"
}

campaign_seed_replay() {
  local iteration_dir=$1 causynth_static_scope_map=$2 charged=$3 bound=$4
  local rule=$5 need=${6:-$3}
  local seed="${iteration_dir}/seed-result"
  local plan="${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  local results="${seed}/concolic_region_results.jsonl"
  local ids
  ids=$(campaign_task_ids "${plan}")
  local campaign_sessions_dir="${iteration_dir}/sessions"
  mkdir -p "${campaign_sessions_dir}"
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
        targets gaps schedule; do
      path="${session}${kind}.jsonl.gz"
      if [[ ! -e "${path}" ]]; then
        missing="${missing} ${name}/${kind}.jsonl.gz"
        continue
      fi
      rows=$(campaign_rows "${path}" | wc -l)
      jq -n -c --arg session "${name}" --arg kind "${kind}" \
        --arg epoch "${iteration_id}" --argjson rows "${rows}" \
        '{schemaVersion: 1, kind: "SESSION_CENSUS", topologyEpoch: $epoch,
          sessionId: $session, rowKind: $kind, rows: $rows}' >>"${census}"
    done
    [[ -s "${session}expressions.jsonl.gz" ]] \
      || missing="${missing} ${name}/expressions.jsonl.gz"
  done
  [[ "${count}" -gt 0 ]] || campaign_fail IMPORT SessionDir "${sessions}" \
    "the replay published no session directory"
  [[ -z "${missing}" ]] || campaign_fail IMPORT SessionDir "${sessions}" \
    "a replay session published no file for:${missing}"
  require_nonempty "replay session census" "${census}"
  campaign_log "sessions: ${count}, rows: $(jq -r -s '[.[].rows] | add // 0' \
    "${census}")"
  find "${sessions%/}" -mindepth 1 -maxdepth 1 -type d | LC_ALL=C sort \
    >"${iteration_dir}/import_gate.list"
  campaign_import_gate "${iteration_dir}" "${iteration_id}" \
    "${iteration_dir}/import_gate.json" "${iteration_dir}/import_gate.list"
}

campaign_zk_keys() {
  local iteration_dir=$1
  local chain="${iteration_dir}/zk_chain.jsonl"
  local plan="${iteration_dir}/execution_task_plan.jsonl"
  local log="${iteration_dir}/zk-keys.log"
  [[ -s "${chain}" ]] || return 0
  run_capturing_status run_java_main \
    edu.uva.liftlab.graphchecker.compose.ZkKeysMain \
    --sessions "${iteration_dir}/sessions" \
    --anchor "${declared_target_occurrence}" \
    --static-scope-map "${causynth_static_scope_map}" \
    ${causynth_root_domains:+--root-domains "${causynth_root_domains}"} \
    --zk-chain "${chain}" \
    --plan "${plan}" >"${log}" 2>&1
  (( status == 0 )) || campaign_fail ZKKEYS ZkKeysMain "${log}" \
    "the seed's keys failed with exit ${status}: $(campaign_thrown "${log}")"
  ln -f "${plan}" "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  campaign_log "$(tail -n 1 "${log}")"
}

campaign_import_gate() {
  local iteration_dir=$1 iteration_id=$2 summary=$3 list=$4 replaced=${5:-}
  local gaps="${iteration_dir}/campaign_gaps.jsonl"
  local blocking violations first
  require_nonempty "the import gate's sessions" "${list}"
  engine_need_mb=$(campaign_import_gate_heap_mb "${list}") \
    run_java_main \
    edu.uva.liftlab.graphchecker.contract.ImportGateMain \
    --iteration "${iteration_dir}" --gate-list "${list}" \
    --gated "${iteration_dir}/import_gated" \
    --out "${gaps}" \
    --topology-epoch "${iteration_id}" \
    ${replaced:+--replaced "${replaced}"} >"${summary}"
  require_nonempty "import gate summary" "${summary}"
  violations=$(jq -r '.violations' "${summary}")
  campaign_count IMPORT ImportGate "${summary}" \
    "the import gate's violation count" "${violations}"
  blocking=$(jq -r '.blocking' "${summary}")
  campaign_count IMPORT ImportGate "${summary}" \
    "the import gate's blocking count" "${blocking}"
  first=$(jq -r '.firstBlockingSubject // ""' "${summary}")
  campaign_log "import gate: $(jq -r '.sessions' "${summary}") session(s), \
${violations} row invariant violation(s), ${blocking} blocking"
  [[ "${blocking}" -eq 0 ]] || campaign_fail IMPORT ImportGate "${gaps}" \
    "${blocking} row invariants violated: ${first}"
}

campaign_import_gate_heap_mb() {
  local largest
  local -a dirs=()
  mapfile -t dirs < <(cut -f1 -- "$1")
  largest=$(campaign_rows_bytes "${dirs[@]}" \
    | awk '$2 > n {n = $2} END {printf "%d\n", n / 1048576}')
  printf '%s\n' "$(( 512 + 4 * largest ))"
}


campaign_sessions_naming() {
  local obligation_id=$1 sessions=$2 manifest
  for manifest in "${sessions}"/*/manifest.json; do
    [[ -f "${manifest}" ]] || continue
    jq -e --arg id "${obligation_id}" \
      'any((.obligationIds // [])[]; . == $id)' "${manifest}" \
      >/dev/null 2>&1 || continue
    dirname "${manifest}"
  done
}

campaign_withdraw_sessions() {
  local obligation_id=$1 sessions=$2 quarantine=$3 why=$4 only=${5:-}
  local session_dir session_id withdrawn=0
  while IFS= read -r session_dir; do
    session_id=$(basename "${session_dir}")
    [[ -z "${only}" || "${session_id}" == "${only}" ]] || continue
    mkdir -p "${quarantine}"
    if mv -- "${session_dir}" "${quarantine}/${session_id}"; then
      withdrawn=$((withdrawn + 1))
      campaign_log "obligation ${obligation_id}: withdrew session \
${session_id} from ${sessions} to ${quarantine}/${session_id}: ${why}"
    else
      campaign_log "obligation ${obligation_id}: could not withdraw session \
${session_id} from ${sessions}: ${why}; it stays there"
    fi
  done < <(campaign_sessions_naming "${obligation_id}" "${sessions}")
  if [[ "${withdrawn}" -eq 0 ]]; then
    campaign_log "obligation ${obligation_id}: no session under ${sessions} \
names it; nothing withdrawn"
  fi
}



campaign_solver_idle_s=300

campaign_solver_live_pct=50
campaign_solver_gc_pct=150
campaign_solver_least_heap_mb=2048

campaign_rows() {
  local file
  for file in "$@"; do
    [[ -f "${file}" ]] || continue
    if [[ "${file}" == *.gz ]]; then
      gzip -cdq -- "${file}" 2>/dev/null || true
    else
      cat -- "${file}"
    fi
  done
}

campaign_rows_unfinished=4294901760

campaign_rows_bytes() {
  local listed="" file
  (( $# > 0 )) || return 0
  listed=$(find "$@" -maxdepth 1 -type f -name '*.gz' -size +19c -print0 \
    2>/dev/null | xargs -0 -r gzip -lq -- 2>/dev/null) || true
  {
    find "$@" -maxdepth 1 -type f ! -name '*.gz' -printf '%h %s\n' 2>/dev/null
    awk -v unfinished="${campaign_rows_unfinished}" '$2 != unfinished {
      dir = $4; sub("/[^/]*$", "", dir); print dir, $2}' <<<"${listed}"
    while IFS= read -r file; do
      [[ -n "${file}" ]] || continue
      printf '%s %s\n' "${file%/*}" "$(campaign_rows "${file}" | wc -c)"
    done < <(awk -v unfinished="${campaign_rows_unfinished}" \
        '$2 == unfinished {print $4 ".gz"}' <<<"${listed}"
      find "$@" -maxdepth 1 -type f -name '*.gz' -size -20c 2>/dev/null)
  } | awk '{n[$1] += $2} END {for (dir in n) {name = dir;
      sub(".*/", "", name); printf "%s %d\n", name, n[dir]}}'
}

campaign_session_bytes() {
  local sessions=$1 kept name size
  local -A known=()
  local -a now=() fresh=()
  [[ -n "${sessions}" && -d "${sessions}" ]] || return 0
  kept="$(dirname "${sessions}")/session_bytes"
  if [[ -s "${kept}" ]]; then
    while read -r name size; do
      [[ -z "${name}" ]] || known[${name}]=${size}
    done <"${kept}"
  fi
  mapfile -t now < <(find "${sessions}" -mindepth 1 -maxdepth 1 -type d \
    -printf '%f\n' | LC_ALL=C sort)
  for name in "${now[@]}"; do
    [[ -n "${known[${name}]:-}" ]] || fresh+=("${sessions}/${name}")
  done
  if (( ${#fresh[@]} > 0 )); then
    while read -r name size; do
      [[ -z "${name}" ]] || known[${name}]=${size}
    done < <(campaign_rows_bytes "${fresh[@]}")
  fi
  for name in "${now[@]}"; do
    printf '%s %s\n' "${name}" "${known[${name}]:-0}"
  done >"${kept}.${BASHPID}"
  cat -- "${kept}.${BASHPID}"
  mv -f -- "${kept}.${BASHPID}" "${kept}"
}

campaign_corpus_mb_fresh_s=60
campaign_corpus_mb() {
  local sessions=$1 stated at="" mb=""
  [[ -n "${sessions}" && -d "${sessions}" ]] || { printf '0\n'; return 0; }
  stated="$(dirname "${sessions}")/corpus_mb"
  { read -r at mb <"${stated}"; } 2>/dev/null || at=""
  if [[ -n "${at}" && -n "${mb}" ]] \
      && (( EPOCHSECONDS - at < campaign_corpus_mb_fresh_s )); then
    printf '%s\n' "${mb}"
    return 0
  fi
  mb=$(campaign_session_bytes "${sessions}" \
    | awk '{n += $2} END {printf "%d\n", n / 1048576}')
  [[ "${mb}" =~ ^[0-9]+$ ]] || mb=0
  printf '%s %s\n' "$(date +%s)" "${mb}" >"${stated}.$$" \
    && mv -f -- "${stated}.$$" "${stated}"
  printf '%s\n' "${mb}"
}

campaign_solver_now_mb() {
  local now outgrown=0 stated="$(dirname "${1:-.}")/solver_outgrown_mb"
  local pct=${2:-}
  [[ -n "${pct}" ]] || pct=$(campaign_solver_measured_pct "${1:-}")
  now=$(( $(campaign_corpus_mb "${1:-}") * pct \
    * campaign_solver_gc_pct / 10000 ))
  [[ ! -s "${stated}" ]] || outgrown=$(<"${stated}")
  (( now >= outgrown )) || now=${outgrown}
  (( now >= campaign_solver_least_heap_mb )) \
    || now=${campaign_solver_least_heap_mb}
  printf '%s\n' "${now}"
}

campaign_solver_heap_mb() {
  local most heap
  most=$(campaign_solver_most_heap_mb)
  heap=$(( 2 * $(campaign_solver_now_mb "${1:-}" "${2:-}") ))
  (( heap <= most )) || heap=${most}
  printf '%s\n' "${heap}"
}

campaign_solver_max_heap_mb=16384
campaign_solver_most_heap_mb() {
  local engine=${engine_memory_mb:-8192}
  printf '%s\n' "$(( engine < campaign_solver_max_heap_mb ? engine \
    : campaign_solver_max_heap_mb ))"
}

campaign_solver_retire_mb() {
  (( $1 < $(campaign_solver_most_heap_mb) )) || { printf '0\n'; return 0; }
  printf '%s\n' "$(( $1 * 10000 / (${2:-${campaign_solver_live_pct}} \
    * campaign_solver_gc_pct) ))"
}

campaign_solver_measured_pct() {
  cat -- "$(dirname "${1:-.}")/solver_live"/* 2>/dev/null \
    | awk -v least="${campaign_solver_live_pct}" '
        $2 > corpus || ($2 == corpus && $1 > live) {live = $1; corpus = $2}
        END {
          if (corpus > 0) print int((100 * live + corpus - 1) / corpus)
          else print least
        }'
}

campaign_solver_outgrown() {
  local stated="$(dirname "$1")/solver_outgrown_mb" held=0
  [[ ! -s "${stated}" ]] || held=$(<"${stated}")
  (( $2 > held )) || return 0
  printf '%s\n' "$2" >"${stated}.$$" && mv -f -- "${stated}.$$" "${stated}"
}

campaign_solver_need_mb() {
  local now heap
  now=$(campaign_solver_now_mb "${1:-}")
  heap=$(campaign_solver_heap_mb "${1:-}")
  (( now <= heap )) || now=${heap}
  printf '%s\n' "$(( $(campaign_jvm_footprint_mb "${now}") \
    + $(campaign_solver_z3_mb) ))"
}

campaign_hard_z3_room_mb=4096
campaign_solver_z3_room_mb() {
  if [[ "${1:-}" == HARD ]]; then
    printf '%s\n' "${campaign_hard_z3_room_mb}"
  else
    campaign_solver_z3_mb
  fi
}

campaign_question_mb=1152
campaign_solver_races=2

campaign_solver_z3_mb() {
  printf '%s\n' "$(( campaign_solver_races * campaign_question_mb ))"
}

campaign_solver_first_tier_ms=60000

campaign_solver_first_ms() {
  local first=${campaign_solver_first_tier_ms}
  (( solver_timeout_ms <= 0 || first < solver_timeout_ms )) \
    || first=${solver_timeout_ms}
  printf '%s\n' "${first}"
}

campaign_solver_two_lanes() {
  (( $(campaign_solver_first_ms) < solver_timeout_ms ))
}

campaign_solver_seats_most=8
campaign_solver_seats() {
  printf '%s\n' "${campaign_solver_seats_most}"
}

campaign_solver_dir() {
  printf '%s/graphchecker-solvers-%s/%s.%s\n' "${TMPDIR:-/tmp}" "$(id -un)" \
    "$(hostname -s)" "$(printf '%s' "$1" | sha256sum | cut -c1-16)"
}

campaign_solver_ended_for_memory() {
  local status heap
  read -r status heap 2>/dev/null <"$1/ended.$2" || return 1
  (( status == 137 )) && return 0
  (( status == campaign_jvm_out_of_heap_status )) \
    && (( ${heap:-0} < $(campaign_solver_most_heap_mb) ))
}

campaign_solve_obligation() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 charge=${5:-}
  local dir name question answer server pid started=0 file seen=""
  local waited=${SECONDS} said=0 decided=""
  dir=$(campaign_solver_dir "${sessions}")
  name="$(date +%s%N).${BASHPID}.${obligation_id}"
  question="${dir}/requests/${name}"
  answer="${dir}/answers/${name}.json"
  mkdir -p "${dir}/requests" "${dir}/answers" "${dir}/out"
  [[ ! -s "${worker}/obligation_model.json" ]] \
    || decided="${worker}/obligation_model.json"
  jq -n -c --arg obligations "${obligations}" --arg id "${obligation_id}" \
    --arg waiter "${BASHPID}" --arg decided "${decided}" \
    '{obligations: $obligations, obligationId: $id, waiter: $waiter,
      decided: $decided}' >"${question}.part"
  mv -- "${question}.part" "${question}.json"
  while [[ ! -e "${answer}" ]]; do
    until campaign_host_lock "${dir}" "$(date +%s)"; do
      sleep 0.0$(( (RANDOM % 9) + 1 ))
    done
    server=$(cat "${dir}/server" 2>/dev/null) || server=""
    pid=${server##* }
    [[ -z "${server}" ]] || seen=${server}
    if [[ -n "${pid}" && -d "/proc/${pid}" || -e "${answer}" ]]; then
      rmdir "${dir}/lock"
      campaign_solver_wait_said "${obligation_id}" "${dir}" "${pid}" \
        "${waited}"
      sleep 0.2
      continue
    fi
    [[ -z "${seen}" || "$(cat "${dir}/retired" 2>/dev/null)" != "${seen}" ]] \
      || started=0
    if [[ -e "${question}.taken" || "${started}" -ge 1 ]]; then
      rm -f -- "${question}.taken" "${question}.json"
      rmdir "${dir}/lock"
      file=$(campaign_solver_log "${sessions}")
      printf 'ObligationSolverMain: the solver of %s ended before it ' \
        "$(hostname -s)" >&2
      printf 'answered %s; its log is %s: %s\n' "${obligation_id}" "${file}" \
        "$(grep -v -E '^[[:space:]]+at ' "${file}" 2>/dev/null \
          | tail -n 1)" >&2
      campaign_solver_ended_for_memory "${dir}" "${pid}" && return 4
      return 1
    fi
    printf 'starting %s\n' "${BASHPID}" >"${dir}/server"
    rmdir "${dir}/lock"
    started=1
    campaign_start_solver "${dir}" "${sessions}" "${charge}" && continue
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

campaign_solver_wait_said_s=60
campaign_solver_wait_again_s=600

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

campaign_solver_log() {
  printf '%s/solver-%s.log\n' "$(dirname "$1")" "$(hostname -s)"
}

campaign_start_solver() {
  local dir=$1 sessions=$2 handed=${3:-} charge="" status=0 heap need
  local charges
  heap=$(campaign_solver_heap_mb "${sessions}")
  need=$(campaign_solver_need_mb "${sessions}")
  charges="${campaign_host_gate_root}/$(campaign_host_key localhost)/charges"
  if [[ -n "${handed}" ]] && (( ${handed%%.*} >= need )) \
      && mv -- "${charges}/${handed}" "${charges}/${handed}.solver" \
        2>/dev/null; then
    charge="${handed}.solver"
    need=${handed%%.*}
  else
    campaign_host_try_charge localhost "${need}"
    (( status == 0 )) || return 1
    charge=${campaign_host_charge_id}
  fi
  {
    campaign_close_inherited_fds
    campaign_host_keep localhost "${charge}"
    status=0
    campaign_solver_jvm "${heap}" "${need}" "$(campaign_solver_first_ms)" \
      "$(campaign_solver_z3_mb)" \
      --serve "${dir}" \
      --seats "$(campaign_solver_seats "${sessions}")" \
      --question-room-mb "${campaign_question_mb}" \
      --sessions "${sessions}" \
      --idle-seconds "${campaign_solver_idle_s}" \
      --retire-past-mb "$(campaign_solver_retire_mb "${heap}" \
        "$(campaign_solver_measured_pct "${sessions}")")" \
      </dev/null >>"$(campaign_solver_log "${sessions}")" 2>&1 || status=$?
    (( status != campaign_jvm_out_of_heap_status )) \
      || campaign_solver_outgrown "${sessions}" "${heap}"
    printf '%s %s\n' "${status}" "${heap}" >"${dir}/ended.${BASHPID}"
    campaign_host_release localhost "${charge}"
  } &
  printf '%s\n' "$!" >"${dir}/server.part"
  mv -f -- "${dir}/server.part" "${dir}/server"
}

campaign_solver_jvm() {
  local heap=$1 charged=$2 budget=$3 room=$4 jvm status=0
  shift 4
  require_file "GraphChecker jar" "${graphchecker_jar}"
  (cd "${graphchecker_work_dir}" \
    && exec env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
      "${campaign_engine_stack}" \
      "-Dcausynth.loop.default.bound=${causynth_loop_default_bound}" \
      "-Dcausynth.system.doors=${causynth_system_doors}" \
      -cp "${graphchecker_jar}" \
      "${campaign_engine_oom[@]}" \
      edu.uva.liftlab.graphchecker.explore.ObligationSolverMain \
      --z3 "${z3_bin}" \
      --solver-timeout-ms "${budget}" \
      --z3-room-mb "${room}" \
      ${causynth_root_domains:+--root-domains "${causynth_root_domains}"} \
      "$@") &
  jvm=$!
  campaign_watch_workload "${jvm}" "${charged}"
  wait "${jvm}" || status=$?
  return "${status}"
}

campaign_failure_said() {
  local said
  said=$(campaign_thrown "$1") || said=""
  [[ -n "${said}" ]] || said=$(grep -v -E '^([[:space:]]+at |causynth: )' \
    -- "$1" 2>/dev/null | tail -n 1) || said=""
  printf '%s\n' "${said}"
}

campaign_decide_heap_mb=512

campaign_decide_need_mb() {
  printf '%s\n' "$(( $(campaign_jvm_footprint_mb "${campaign_decide_heap_mb}") \
    + $(campaign_solver_z3_room_mb HARD) ))"
}

campaign_obligation_again() {
  local worker=$1 why=$2
  campaign_log "obligation $(basename "${worker}"): ${why}; asked again of \
a host's solver"
  jq -n -c --arg why "${why}" '{why: $why}' \
    | campaign_write_whole "${worker}/solve_again"
  rm -f -- "${worker}/obligation_result.jsonl" "${worker}/question.txt" \
    "${worker}/question.asked"
}

campaign_solver_memory_asks=4
campaign_obligation_worker() {
  local obligation_id=$1 obligations=$2 sessions=$3 worker=$4 charged=$5
  local charge=${6:-} outcome status=0 why log memory_asks
  local campaign_head_charging=0
  local result_row="${worker}/obligation_result.jsonl"
  if [[ "${charge}" == HARD ]]; then
    campaign_obligation_decide "${obligation_id}" "${obligations}" \
      "${worker}" "${charged}"
    return
  fi
  log="$(campaign_stream_logs OBLIGATION "${worker}")stderr.log"
  run_capturing_status campaign_solve_obligation "${obligation_id}" \
    "${obligations}" "${sessions}" "${worker}" "${charge}"
  case "${status}" in
    0) rm -f -- "${worker}/asked_again" ;;
    3)
      rm -f -- "${worker}/asked_again"
      campaign_obligation_again "${worker}" "no room on $(hostname -s) to \
start its solver now"
      return 0 ;;
    *)
      memory_asks=$(grep -c '' "${worker}/asked_again_memory" 2>/dev/null) \
        || memory_asks=0
      if (( status == 4 && memory_asks < campaign_solver_memory_asks )); then
        echo >>"${worker}/asked_again_memory"
        campaign_obligation_again "${worker}" "its host's solver ended for \
memory before it answered"
        return 0
      fi
      why=$(campaign_failure_said "${log}")
      [[ ! -e "${worker}/asked_again" ]] || die "obligation \
${obligation_id}: its host's solver did not answer it, asked twice: \
${why:-it said nothing}"
      : >"${worker}/asked_again"
      campaign_obligation_again "${worker}" "its host's solver did not \
answer (${why:-it said nothing})"
      return 0 ;;
  esac
  require_nonempty "obligation solver result" "${result_row}"
  require_nonempty "obligation query" "${worker}/obligation_query.smt2.gz"
  outcome=$(jq -er '.verdict' "${result_row}")
  case "${outcome}" in
    UNSAT|NOT_ADMITTED|ADMITTED|SAT_MODEL_READY) ;;
    *) die "the obligation verdict is not solver-backed: ${outcome}" ;;
  esac
}

campaign_obligation_decide() {
  local obligation_id=$1 obligations=$2 worker=$3 charged=$4 status=0 log
  log="$(campaign_stream_logs HARD "${worker}")stderr.log"
  run_capturing_status campaign_solver_jvm "${campaign_decide_heap_mb}" \
    "${charged}" "${solver_timeout_ms}" "$(campaign_solver_z3_room_mb HARD)" \
    --decide "${worker}" \
    --obligations "${obligations}" \
    --obligation-id "${obligation_id}"
  (( status == 0 )) || die "obligation ${obligation_id}: its hard-lane ask \
failed (exit ${status}): $(campaign_failure_said "${log}")"
  rm -f -- "${worker}/asked_again"
  if [[ ! -s "${worker}/obligation_result.jsonl" \
        && -s "${worker}/obligation_model.json" ]]; then
    campaign_obligation_again "${worker}" "the hard lane found a model; \
its host's solver finishes the flip with it"
    return 0
  fi
  require_nonempty "obligation solver result" \
    "${worker}/obligation_result.jsonl"
}

campaign_obligation_replay() {
  local obligation_id=$1 classes=$2 worker=$3 sessions=$4 seed_plan=$5
  local charged=$6 need=${7:-$6}
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
  campaign_sessions_dir="${sessions}" \
    campaign_adapter_timeout_s="${replay_timeout_s}" \
    campaign_adapter_timeout_rule="replay_timeout_s=${replay_timeout_s}" \
    campaign_replay_heap_basis_mb="${need}" \
    campaign_replay worker "${plan}" "${replay_tasks}" "${classes}" \
      "${results}" "${worker}" "${charged}" tolerated
  if [[ ( -n "${campaign_replay_refused_mb}" \
        || -s "${worker}/${campaign_out_of_heap_file}" ) \
      && ! -s "${statement}" ]]; then
    campaign_replay_set_aside "${obligation_id}" "${worker}" "${sessions}" \
      "${charged}"
    return 0
  fi
  if [[ -n "${campaign_replay_killed}" && ! -s "${statement}" ]]; then
    campaign_replay_bounded "${obligation_id}" "${worker}" "${sessions}" \
      "replay ${campaign_replay_killed}"
    return 0
  fi
  [[ -z "${campaign_replay_killed}" ]] || campaign_log "obligation \
${obligation_id}: its replay stated its verdict and then \
${campaign_replay_killed}; the statement is its answer"
  outcome=$(jq -r '.verdict // ""' "${statement}" 2>/dev/null) || outcome=""
  case "${outcome}" in
    ADMITTED|NOT_ADMITTED|UNSAT) ;;
    *) campaign_fail EXPLORE ObligationSolverMain "${statement}" \
        "the replay of ${obligation_id} stated no verdict for it \
(\"${outcome}\")" ;;
  esac
  [[ -n "$(jq -r '.sessionId // ""' "${statement}")" ]] \
    || campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
      "${worker}/refused-sessions" "a refusal or a stall decided every \
obligation its replay carried and the replay ended there, so its rows are a \
prefix of a run"
  campaign_write_whole "${result_row}" <"${statement}"
  [[ ! -e "${worker}/question.asked" ]] \
    || mv -f -- "${worker}/question.asked" "${worker}/question.txt"
}


campaign_replay_bounded() {
  local obligation_id=$1 worker=$2 sessions=$3 why=$4
  rm -f -- "${worker}/question.asked"
  campaign_log "obligation ${obligation_id}: ${why}"
  campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
    "${worker}/timed-out-sessions" "its manifest names this obligation \
and its rows state no verdict, which no later stage may read as a corpus \
session"
  jq -n -c --arg id "${obligation_id}" --arg detail "REPLAY_BOUNDED: ${why}" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: "NOT_ADMITTED", sessionId: "", detail: $detail}' \
    | campaign_write_whole "${worker}/obligation_result.jsonl"
}

campaign_replay_ended_files=(replay.log concolic_region_results.jsonl
  workload_rss_mb workload_rss_mean_mb workload_cores_x100
  "${campaign_refused_file}" "${campaign_out_of_heap_file}"
  "${campaign_ending_file}")
campaign_replay_set_aside() {
  local obligation_id=$1 worker=$2 sessions=$3 charged=$4 aside file
  local ended=0 heap=-
  read -r heap 2>/dev/null <"${worker}/${campaign_out_of_heap_file}" \
    || heap=-
  for aside in "${worker}"/ended-*; do
    [[ ! -d "${aside}" ]] || ended=$((ended + 1))
  done
  aside="${worker}/ended-$((ended + 1))"
  mkdir -p -- "${aside}"
  for file in "${campaign_replay_ended_files[@]}"; do
    [[ ! -e "${worker}/${file}" ]] || mv -f -- "${worker}/${file}" "${aside}/"
  done
  campaign_withdraw_sessions "${obligation_id}" "${sessions}" \
    "${aside}/sessions" "its replay was ended for memory before it stated \
anything, and it is asked again"
  campaign_log "obligation ${obligation_id}: replay ${campaign_replay_killed}; \
its run is set aside in ${aside}, and it is asked again at its full need"
  printf '%s %s %s %s\n' "${campaign_replay_refused_mb:-0}" "${charged}" \
    "${aside}" "${heap}" | campaign_write_whole "${worker}/replay_again"
}


campaign_worker_host_list() {
  local -a hosts=()
  read -r -a hosts <<<"${campaign_worker_hosts}"
  [[ ${#hosts[@]} -gt 0 ]] || hosts=(localhost)
  printf '%s\n' "${hosts[@]}"
}

campaign_local_host_names=""

campaign_host_is_local() {
  local host=$1
  if [[ -z "${campaign_local_host_names}" ]]; then
    campaign_local_host_names=" localhost $(hostname 2>/dev/null) \
$(hostname -s 2>/dev/null) "
  fi
  [[ -z "${host}" || "${campaign_local_host_names}" == *" ${host} "* ]]
}


# shellcheck source=tools/lib/gc-env.sh
source "${graphchecker_dir}/tools/lib/gc-env.sh"
campaign_host_gate_root=${CAUSYNTH_HOST_LEDGER}
campaign_host_lease_s=120
campaign_host_renew_s=10
campaign_head_charging=0
campaign_host_max_used_pct=${CAUSYNTH_HOST_MAX_USED_PCT}
campaign_head_max_used_pct=88
[[ "${campaign_host_max_used_pct}" =~ ^[0-9]+$ ]] \
  && (( campaign_host_max_used_pct > 0 && campaign_host_max_used_pct <= 100 )) \
  || die "CAUSYNTH_HOST_MAX_USED_PCT must be a percentage in 1..100: \
${campaign_host_max_used_pct}"
campaign_host_poll_s=5
campaign_host_reading_keep_s=30
campaign_ssh_patience_s=300
campaign_host_lock_stale_s=30
campaign_head_reservation_stale_s=600
campaign_head_reservation=""
campaign_head_pid=""
campaign_head_hold=""
campaign_stream_entry=""
campaign_host_head_start=0

campaign_host_key() {
  if campaign_host_is_local "$1"; then
    hostname -s
  else
    printf '%s\n' "$1"
  fi
}

campaign_host_read() {
  local host=$1 read_it=$2
  if campaign_host_is_local "${host}"; then
    bash -c "${read_it}"
  else
    campaign_ssh "${campaign_ssh_options[@]}" -o ConnectTimeout=20 -- \
      "${host}" "${read_it}"
  fi
}

campaign_host_available_mb() {
  campaign_host_read "$1" \
    "awk '/^MemAvailable:/ {print int(\$2 / 1024)}' /proc/meminfo"
}

campaign_host_total_mb() {
  campaign_host_read "$1" \
    "awk '/^MemTotal:/ {print int(\$2 / 1024)}' /proc/meminfo"
}

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

campaign_host_memory_reading() {
  local host=$1 dir=$2 now=$3 at=0 mb="" fresh refresh=${2}/refresh
  read -r at mb 2>/dev/null <"${dir}/available" || true
  [[ "${at}" =~ ^[0-9]+$ && "${mb}" =~ ^[0-9]+$ ]] || at=0
  if (( now - at < campaign_host_poll_s )); then
    printf '%s\n' "${mb}"
    return 0
  fi
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
  if [[ "${mb}" =~ ^[0-9]+$ && -n "${refresh}" ]] \
      && fresh=$(mktemp "${dir}/available.XXXXXX"); then
    printf '%s %s\n' "${now}" "${mb}" >"${fresh}"
    mv -f -- "${fresh}" "${dir}/available"
  fi
  [[ -z "${refresh}" ]] || rmdir "${refresh}" 2>/dev/null
  [[ "${mb}" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "${mb}"
}

campaign_host_lock() {
  local dir=$1 now=$2 lock_at
  mkdir "${dir}/lock" 2>/dev/null && return 0
  lock_at=$(stat -c %Y "${dir}/lock" 2>/dev/null || echo "${now}")
  if (( now - lock_at >= campaign_host_lock_stale_s )); then
    rmdir "${dir}/lock" 2>/dev/null || true
  fi
  return 3
}

campaign_host_wait_reason=""
campaign_host_charge_id=""
campaign_host_try_start() {
  local host=$1 need=$2 spare=${3:-0} key dir now available total limit
  local used held=0
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
  campaign_host_admit "${dir}" "${total}" "${limit}" "${used}" "${held}" \
    "${need}" "${spare}"
}

campaign_host_admitted_charged=0
campaign_host_admit() {
  local dir=$1 total=$2 limit=$3 used=$4 held=$5 need=$6 spare=$7
  local now=${EPOCHSECONDS}
  campaign_host_lock "${dir}" "${now}" || return 3
  campaign_host_admitted_charged=$(campaign_host_charged "${dir}" "${now}")
  if ! campaign_host_fits "${campaign_host_admitted_charged}" "${used}" \
      "${held}" "${need}" "${spare}" "${limit}"; then
    rmdir "${dir}/lock"
    campaign_host_refused "${dir##*/}" "${campaign_host_admitted_charged}" \
      "${used}" "${held}" "${need}" "${spare}" "${limit}" "${total}"
    return 1
  fi
  campaign_host_charge_row "${dir}" "${need}"
  return 0
}

campaign_host_fits() {
  (( $1 + $3 + $4 + $5 <= $6 && $2 + $3 + $4 + $5 <= $6 ))
}

campaign_host_refused() {
  local beside=""
  (( $6 == 0 )) || beside=" and $6 MB room beside it"
  campaign_host_wait_reason="$1 has $2 MB charged to what it runs, $3 MB \
in use and $4 MB held for a head; one needs $5 MB${beside} and at most $7 MB \
(${campaign_host_max_used_pct}% of $8 MB) may be charged or in use"
}

campaign_host_limit_mb() {
  local pct=${2:-${campaign_host_max_used_pct}}
  printf '%s\n' "$(( $1 - $1 * (100 - pct) / 100 ))"
}

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

campaign_host_charge_row() {
  local dir=$1 need=$2 id
  [[ -d "${dir}/charges" ]] || mkdir -p "${dir}/charges"
  while :; do
    id="${need}.$(hostname -s).${BASHPID}.${EPOCHSECONDS}.${RANDOM}"
    [[ -e "${dir}/charges/${id}" ]] || break
  done
  campaign_host_charge_id=${id}
  : >"${dir}/charges/${campaign_host_charge_id}"
  rmdir "${dir}/lock"
  campaign_host_hold "${dir}/charges/${campaign_host_charge_id}"
}

campaign_host_keep() {
  campaign_host_hold "${campaign_host_gate_root}/$(campaign_host_key \
"$1")/charges/$2"
}

campaign_close_inherited_fds() {
  local fd
  for fd in /proc/"${BASHPID}"/fd/*; do
    fd=${fd##*/}
    [[ "${fd}" =~ ^[0-9]+$ ]] && (( fd > 2 )) || continue
    eval "exec ${fd}>&-" 2>/dev/null || true
  done
}

campaign_host_hold() {
  local file=$1 owner=${BASHPID}
  ( ( campaign_close_inherited_fds
      while kill -0 "${owner}" 2>/dev/null && [[ -e "${file}" ]]; do
        command touch -c -- "${file}" 2>/dev/null || true
        command sleep "${campaign_host_renew_s}"
      done ) </dev/null >/dev/null 2>&1 & )
}

campaign_host_try_grow() {
  local host=$1 mb=$2 pct=${3:-${campaign_host_max_used_pct}}
  local key dir now total available limit
  key=$(campaign_host_key "${host}")
  dir="${campaign_host_gate_root}/${key}"
  mkdir -p "${dir}"
  now=$(date +%s)
  total=$(campaign_host_memory_total "${host}" "${dir}") || return 2
  available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
    || return 2
  limit=$(campaign_host_limit_mb "${total}" "${pct}")
  campaign_host_lock "${dir}" "${now}" || return 3
  if (( total - available + mb > limit )); then
    rmdir "${dir}/lock"
    campaign_host_wait_reason="${key} has ${available} MB available of \
${total} MB, and ${mb} MB more would put over ${pct}% of it in use"
    return 1
  fi
  campaign_host_charge_row "${dir}" "${mb}"
  return 0
}

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

campaign_head_reserve() {
  local dir
  dir="${campaign_host_gate_root}/$(campaign_host_key localhost)/heads"
  mkdir -p "${dir}"
  campaign_head_pid=${BASHPID}
  campaign_head_reservation="${dir}/$(hostname -s).${BASHPID}.$(date +%s)"
  campaign_head_need_mb >"${campaign_head_reservation}"
  trap campaign_head_unreserve EXIT
}

campaign_head_heartbeat() {
  [[ -z "${campaign_head_reservation}" ]] \
    || campaign_head_need_mb >"${campaign_head_reservation}" 2>/dev/null \
    || true
  local fresh
  for fresh in "${campaign_head_hold}" "${campaign_stream_entry}"; do
    [[ -z "${fresh}" ]] || touch -c -- "${fresh}" 2>/dev/null || true
  done
}

campaign_head_unreserve() {
  [[ -z "${campaign_head_hold}" ]] || rm -f -- "${campaign_head_hold}"
  campaign_head_hold=""
  [[ -n "${campaign_head_reservation}" \
     && "${BASHPID}" == "${campaign_head_pid}" ]] || return 0
  rm -f -- "${campaign_head_reservation}" "${campaign_head_reservation}".busy.*
  campaign_head_reservation=""
}

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

campaign_host_system_mb=2048
campaign_head_most_mb() {
  local host dir now total available limit charged used most=0 own
  local campaign_host_max_used_pct=${campaign_head_max_used_pct}
  now=$(date +%s)
  while IFS= read -r host; do
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
    mkdir -p "${dir}"
    total=$(campaign_host_memory_total "${host}" "${dir}") || continue
    available=$(campaign_host_memory_reading "${host}" "${dir}" "${now}") \
      || continue
    limit=$(campaign_host_limit_mb "${total}")
    charged=$(campaign_host_charged "${dir}" "${now}")
    used=$(( total - available ))
    own=$(( used > charged ? used - charged : 0 ))
    (( own <= campaign_host_system_mb )) || own=${campaign_host_system_mb}
    (( limit - own <= most )) || most=$(( limit - own ))
  done < <(if (( $# > 0 )); then printf '%s\n' "$@"; else
      { echo localhost; campaign_worker_host_list; } | awk '!seen[$0]++'; fi)
  printf '%s\n' "${most}"
}

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

campaign_pool_can_hold() {
  local mb=$1 host dir total now
  shift
  now=$(date +%s)
  for host in "$@"; do
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
    mkdir -p "${dir}"
    total=$(campaign_host_memory_total "${host}" "${dir}") || return 0
    (( $(campaign_host_limit_mb "${total}") \
       - $(campaign_host_head_reserved "${dir}" "${now}") < mb )) || return 0
  done
  return 1
}

campaign_host_head_reserved() {
  local dir=$1 now=$2 file need held=0
  for file in "${dir}"/heads/*; do
    [[ -f "${file}" && "${file}" != *.busy.* && "${file}" != *.hold ]] \
      || continue
    (( now - $(stat -c %Y "${file}" 2>/dev/null || echo 0) \
      < campaign_head_reservation_stale_s )) || continue
    read -r need 2>/dev/null <"${file}" || continue
    [[ "${need}" =~ ^[0-9]+$ ]] && (( need > held )) && held=${need}
  done
  printf '%s\n' "${held}"
}

campaign_host_release() {
  rm -f -- "${campaign_host_gate_root}/$(campaign_host_key "$1")/charges/$2"
}

campaign_host_try_charge() {
  campaign_host_unlocked campaign_host_try_start "$@"
}

campaign_host_unlocked() {
  while true; do
    run_capturing_status "$@"
    (( status != 3 )) && return 0
    sleep 0.$(( (RANDOM % 9) + 1 ))
  done
}

campaign_process_rss_mb() {
  awk '/^VmRSS:/ {print int($2 / 1024)}' "/proc/$1/status" 2>/dev/null
}

campaign_watch_interval_s=2
campaign_unbounded_stall_s=600
campaign_recording_end_marker=RECORDING_ENDED

campaign_workload_output_bytes() {
  local pid=$1 dir=$2
  {
    find "${dir}" -type f -printf '%s\n' 2>/dev/null
    stat -L -c '%s' "/proc/${pid}/fd/1" "/proc/${pid}/fd/2" 2>/dev/null
  } | awk '{bytes += $1} END {print bytes + 0}'
}

campaign_clock_ticks=$(getconf CLK_TCK 2>/dev/null) || campaign_clock_ticks=100
campaign_watch_workload() {
  local pid=$1 charged=$2 dir=${3:-} max_mb=${4:-0} traced=${4:+1}
  local ending
  local peak=0 held=$2 mb id status=0 refused="" written=0 ended=""
  local sum=0 reads=0 ticks=0 started=${EPOCHREALTIME/./} lasted=0
  local output="" wrote="" since=${SECONDS}
  local -a grants=() stat=()
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
    if [[ -n "${mb}" ]]; then
      sum=$(( sum + mb ))
      reads=$(( reads + 1 ))
    fi
    if read -r -a stat 2>/dev/null <"/proc/${pid}/stat"; then
      ticks=$(( stat[13] + stat[14] ))
      lasted=$(( ${EPOCHREALTIME/./} - started ))
    fi
    if (( ${mb:-0} > peak )); then
      peak=${mb}
      [[ -z "${dir}" ]] \
        || printf '%s\n' "${peak}" >"${dir}/workload_rss_mb"
    fi
    if (( charged > 0 && peak > held )); then
      ending=""
      [[ -z "${dir}" || ! -e "${dir}/${campaign_ending_file}" ]] \
        || ending=${campaign_host_end_used_pct}
      campaign_host_unlocked campaign_host_try_grow localhost \
        "$(( peak - held ))" "${ending}"
      if (( status != 0 )); then
        refused="the host cannot take the $(( peak - held )) MB more \
(${campaign_host_wait_reason})"
        kill -KILL "${pid}" 2>/dev/null || true
        [[ -z "${dir}" ]] \
          || printf '%s\n' "${peak}" >"${dir}/${campaign_refused_file}"
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
  [[ -z "${dir}" ]] || (( reads == 0 )) \
    || printf '%s\n' "$(( sum / reads ))" >"${dir}/workload_rss_mean_mb"
  [[ -z "${dir}" ]] || (( lasted < 1000000 )) \
    || printf '%s\n' "$(( ticks * 100000000 / campaign_clock_ticks \
      / lasted ))" >"${dir}/workload_cores_x100"
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

campaign_head_charged() {
  local need id status busy="" host room="" grant="" remote
  if [[ "$1" == --room ]]; then
    room=$2
    shift 2
  fi
  need=$1
  shift
  if [[ "${campaign_head_charging}" != 1 ]]; then
    "$@" ${room:+--z3-room-mb "${room}"}
    return
  fi
  campaign_head_heartbeat
  campaign_head_place "${need}" >&2
  host=${campaign_placed_host}
  id=${campaign_host_charge_id}
  if campaign_host_is_local "${host}" \
      && [[ -n "${campaign_head_reservation}" ]]; then
    busy="${campaign_head_reservation}.busy.${BASHPID}"
    : >"${busy}"
  fi
  campaign_z3_hosts_grants=()
  if [[ -n "${room}" ]]; then
    campaign_z3_room_grant "${host}" "${room}"
    grant=${campaign_z3_room_grant_id}
    set -- "$@" --z3-room-mb "${campaign_z3_room_granted_mb}"
    if [[ "${campaign_compose_final:-}" == 1 ]]; then
      campaign_z3_hosts_grant "${host}"
      [[ -z "${campaign_z3_hosts}" ]] \
        || set -- "$@" --z3-hosts "${campaign_z3_hosts}"
      echo "[campaign] the final composer's z3s run on \
${#campaign_z3_hosts_grants[@]} more host(s): ${campaign_z3_hosts:-none}" >&2
    fi
  fi
  if campaign_host_is_local "${host}"; then
    "$@"
    status=$?
  else
    campaign_run_placed "${host}" "$@"
    status=$?
  fi
  [[ -z "${busy}" ]] || rm -f -- "${busy}"
  campaign_head_heartbeat
  [[ -z "${grant}" ]] || campaign_host_release "${host}" "${grant}"
  for remote in "${campaign_z3_hosts_grants[@]}"; do
    campaign_host_release ${remote}
  done
  campaign_host_release "${host}" "${id}"
  return "${status}"
}

campaign_placed_host=""
campaign_head_place() {
  local need=$1 host room best best_room said=false status=0 most
  local since=${SECONDS}
  local campaign_host_max_used_pct=${campaign_head_max_used_pct}
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
      most=$(campaign_head_most_mb)
      (( most == 0 || need <= most )) || die "a head step of ${need} MB: no \
host of the pool can ever hold it, the most one holds with no charge standing \
being ${most} MB"
      campaign_head_hold_room "${need}"
      campaign_log "waiting for memory for a head step of ${need} MB on any \
host: ${campaign_host_wait_reason}; held on ${campaign_head_hold_host:-no host}"
      said=true
    fi
    campaign_head_heartbeat
    sleep "${campaign_host_poll_s}"
  done
}

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

campaign_head_placed() {
  [[ "$1" == true ]] || return 0
  [[ -z "${campaign_head_hold}" ]] || rm -f -- "${campaign_head_hold}"
  campaign_head_hold=""
  campaign_log "room for a head step of $2 MB on ${campaign_placed_host} \
after waiting $(( SECONDS - $3 )) s"
}

campaign_placed_bound_s=21600

campaign_run_placed() {
  local host=$1 dir name status=0
  local -a exported=()
  shift
  dir=$(mktemp -d "${campaign_root}/placed.XXXXXX") || return
  for name in $(compgen -e); do
    [[ "${name}" == CAUSYNTH_* || "${name}" == GRAPH_CHECKER_* ]] \
      && exported+=("${name}=${!name}")
  done
  campaign_dispatch_remote "${host}" "${dir}/" "${campaign_placed_bound_s}" \
    --run-placed "${PWD}" "${exported[@]}" -- "$@" || status=$?
  cat -- "${dir}/stdout.log" 2>/dev/null
  cat -- "${dir}/stderr.log" "${dir}/ssh.log" >&2 2>/dev/null
  rm -rf -- "${dir}"
  return "${status}"
}

campaign_stream_solves() {
  [[ "$1" == OBLIGATION || "$1" == HARD ]]
}

campaign_stream_logs() {
  case "$1" in
    HARD) printf '%s/hard-\n' "$2" ;;
    OBLIGATION)
      if [[ -e "$2/again-host.txt" ]]; then
        printf '%s/again-\n' "$2"
      else
        printf '%s/\n' "$2"
      fi ;;
    REPLAY) printf '%s/replay-\n' "$2" ;;
    *) printf '%s/\n' "$2" ;;
  esac
}

campaign_stream_job() {
  local kind=$1 host=$2 charge=$3 id=$4 worker=$5 status=0
  shift 5
  local -a work=(campaign_obligation_worker "$@")
  local staged="${worker}/sessions" logs
  logs=$(campaign_stream_logs "${kind}" "${worker}")
  case "${kind}" in
    REPLAY|RERUN) work=(campaign_obligation_replay "$@") ;;
    CONFIRM) work=(campaign_confirm_replay "$@"); staged="$1/sessions" ;;
  esac
  if campaign_host_is_local "${host}"; then
    ( set -euo pipefail; "${work[@]}" ) >"${logs}stdout.log" \
      2>"${logs}stderr.log" || status=$?
  elif campaign_stream_solves "${kind}"; then
    campaign_dispatch_remote "${host}" "${logs}" \
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
  campaign_await_remote_result "${worker}" "${host}" "${id}" "${staged}" \
    "${kind}"
}

campaign_write_whole() {
  cat >"$1.part" && mv -f -- "$1.part" "$1"
}

campaign_obligation_unfinished() {
  local host=$1 obligation_id=$2 worker=$3 status=$4 kind=$5
  local why failure
  failure=$(sed -n -E 's/^(Error: |  reason=)//p' \
    "$(campaign_stream_logs "${kind}" "${worker}")stderr.log" 2>/dev/null \
    | tail -n 1) || failure=""
  why="its worker on ${host} did not finish (exit ${status}: \
${failure:-it failed, or the head could not see what it wrote, as the \
campaign log says}); its logs are in ${worker}"
  campaign_log "obligation ${obligation_id}: ${why}"
  campaign_reap_on_host "${host}" "${worker}"
  campaign_obligation_unanswered "${obligation_id}" "${worker}" "${why}"
}

campaign_obligation_unanswered() {
  local obligation_id=$1 worker=$2 why=$3 iteration_dir
  campaign_withdraw_sessions "${obligation_id}" "${worker}/sessions" \
    "${worker}/unfinished-sessions" "${why}"
  rm -f -- "${worker}/question.txt" "${worker}/question.asked"
  jq -n -c --arg id "${obligation_id}" --arg detail "${why}" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: "NOT_ADMITTED", sessionId: "", detail: $detail}' \
    | campaign_write_whole "${worker}/obligation_result.jsonl"
  iteration_dir=$(dirname "$(dirname "${worker}")")
  jq -n -c --arg id "${obligation_id}" --arg detail "${why}" \
    --arg epoch "$(basename "${iteration_dir}")" \
    '{schemaVersion: 1, sessionId: "", stage: "EXPLORE",
      kind: "ADMISSION_GAP", cls: "DIAGNOSTIC",
      subject: "OBLIGATION_UNFINISHED", detail: ($id + ": " + $detail),
      topologyEpoch: $epoch}' >>"${iteration_dir}/campaign_gaps.jsonl"
}



campaign_plan_blocker() {
  [[ -s "$1/concolic_region_plan.jsonl" ]] || return 0
  head -n 1 "$1/concolic_region_plan.jsonl" | jq -r '[.gaps[]?
    | select(.cls == "BLOCKING" and .kind == "TARGET_FATAL_IN_RECORDING")
    | .subject][0] // empty' 2>/dev/null || true
}

campaign_explore() {
  local iteration_dir=$1 iteration_id=$2
  local sessions="${iteration_dir}/sessions"
  local results="${iteration_dir}/obligation_results.jsonl"
  local attempts="${iteration_dir}/witness_attempts.jsonl"
  local stream_classes="${iteration_dir}/instrumented-classes"
  local stream_plan="${iteration_dir}/generations/g0/execution_task_plan.jsonl"
  local stream_round=0 stream_dirty=1 stream_landed=0 stream_hold=0
  local stream_generation=0 stream_ticker=""
  local stream_waiting="" stream_admitted_host="" stream_admitted_mb=""
  local stream_stop=""
  local stream_share_said="" stream_round_due=false
  local stream_stop_detail="" stream_anchors="[]"
  local stream_step_pid="" stream_step_dir="" stream_steps=0
  local stream_round_pid="" stream_round_dir=""
  local stream_round_returned="" stream_round_dropped=""
  local -a stream_gate_owed=() stream_gate_running=()
  local stream_grow_pid="" stream_grow_round="" stream_grow_growth=""
  local stream_grow_returned=""
  local -a stream_queue=() stream_hosts=() stream_swaps=() stream_pending=()
  local -a stream_witnesses=() stream_deferred=() stream_after_witness=()
  local -a stream_cancelled=() stream_reaped=() stream_round_args=()
  local -a stream_reruns_dropped=() stream_confirms_reaped=()
  local -A stream_jobs=() stream_job_charge=() stream_job_worker=()
  local -A stream_job_since=()
  local stream_admitted_pass="" stream_seated_ms=0 stream_seated_n=0
  local stream_read_mb_s=0
  local -A stream_job_tree=() stream_flying=() stream_pool_slots=()
  local -A stream_job_cores=()
  local -A stream_entry_need=()
  local -A stream_host_busy=() stream_host_cores=() stream_host_unread=()
  local -A stream_host_solves=()
  local -A stream_host_ledger=() stream_host_view=()
  local stream_admitted_cores="" stream_sharers="" stream_reading=""
  local -a stream_hard=()
  local -A stream_solver_seen=() stream_confirming=() stream_queued_at=()
  local -A stream_reruns=() stream_growing=() stream_withdrawn=() \
    stream_rests=() stream_worlds=() stream_world_of=()
  local -a stream_duplicates=()
  local -a stream_uncaptured=()
  local -A stream_chain=() stream_chain_grown=()
  local -a stream_chain_witnesses=()
  : >"${results}"
  : >"${attempts}"
  : >"${iteration_dir}/withdrawn.txt"
  mkdir -p "$(dirname "${stream_plan}")"
  ln -f "${iteration_dir}/execution_task_plan.jsonl" "${stream_plan}"
  mapfile -t stream_hosts < <(campaign_worker_host_list)
  campaign_stream_round_args
  campaign_stream_enroll
  campaign_stream_read_hosts
  trap 'campaign_stream_reap; campaign_planner_stop; campaign_stream_stop_solvers
    campaign_stream_unenroll; campaign_stream_unread_hosts
    campaign_head_unreserve' EXIT
  local blocked
  blocked=$(campaign_plan_blocker "${iteration_dir}")
  if [[ -n "${blocked}" ]]; then
    stream_stop=TARGET_FATAL_IN_RECORDING
    stream_stop_detail="PLAN named the declared occurrence ${blocked} \
TARGET_FATAL_IN_RECORDING (BLOCKING): it throws as recorded, so no \
counterfactual is asked of it and no claim can stand on this corpus"
    campaign_log "exploration skipped: ${stream_stop_detail}"
  fi

  while true; do
    if [[ -z "${stream_step_pid}" && -n "${stream_grow_returned}" \
        && "${stream_stop}" != WITNESSED \
        && "${stream_stop}" != CAMPAIGN_BUDGET_REACHED ]]; then
      campaign_stream_grow_take
    fi
    if [[ -z "${stream_stop}" && -z "${stream_step_pid}" \
        && -z "${stream_grow_pid}${stream_grow_returned}" \
        && -n "${stream_round_returned}" ]]; then
      campaign_stream_round_take
    fi
    if [[ "${stream_stop}" != WITNESSED && -z "${stream_step_pid}" ]] \
        && ! campaign_claim_room; then
      stream_stop_detail="${stream_stop:+the exploration stopped \
${stream_stop} (${stream_stop_detail}) and drained what ran; }\
$(( SECONDS - campaign_started_s ))s of the \
campaign's ${campaign_budget_s}s budget (campaign_budget_s) are spent, and \
the stages after the exploration are owed $(campaign_reserve)s of it \
(campaign_reserve)"
      stream_stop=CAMPAIGN_BUDGET_REACHED
      (( stream_dirty == 0 && stream_hold == 0 )) || stream_round_due=true
    fi
    if [[ "${stream_stop}" == WITNESSED \
        || "${stream_stop}" == CAMPAIGN_BUDGET_REACHED \
        || "${stream_stop}" == TARGET_FATAL_IN_RECORDING ]]; then
      campaign_stream_end
      break
    fi
    if [[ -z "${stream_step_pid}" ]]; then
      campaign_stream_round_start
      campaign_stream_step_start
    fi
    campaign_stream_round_start
    [[ -z "${stream_stop}" ]] || campaign_stream_drop
    campaign_stream_dispatch
    if campaign_stream_idle; then
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
  campaign_stream_stop_solvers
  campaign_stream_unenroll
  campaign_stream_unread_hosts
  trap campaign_head_unreserve EXIT
  campaign_stream_promote_generation
  campaign_stream_uncaptured
  campaign_stream_truncation
  campaign_stream_manifest
  campaign_log "exploration stopped (${stream_stop}) after ${stream_round} \
round(s), $(grep -c '' "${results}" || true) obligation verdict(s); ran on: \
$(cat "${iteration_dir}"/obligations-*/*/host.txt 2>/dev/null \
  | LC_ALL=C sort | uniq -c | awk '{printf "%s=%s ", $2, $1}')"
}

campaign_stream_idle() {
  (( ${#stream_jobs[@]} + ${#stream_queue[@]} + ${#stream_hard[@]} \
     + ${#stream_swaps[@]} + ${#stream_gate_owed[@]} == 0 )) \
    && [[ -z "${stream_step_pid}${stream_round_pid}" \
          && -z "${stream_round_returned}" \
          && -z "${stream_grow_pid}${stream_grow_returned}" ]]
}

campaign_stream_uncaptured() {
  local session
  local -A named=()
  [[ "${stream_stop}" != WITNESSED ]] || return 0
  for session in "${stream_uncaptured[@]}"; do
    [[ -d "${sessions}/${session}" ]] || continue
    named[${session}]=1
  done
  (( ${#named[@]} > 0 )) || return 0
  printf '%s\n' "${!named[@]}" | LC_ALL=C sort \
    >"${iteration_dir}/uncaptured_sessions.txt"
  campaign_log "${#named[@]} session(s) whose GROW re-run did not land are \
composed uncaptured: ${iteration_dir}/uncaptured_sessions.txt"
}

campaign_stream_round_args() {
  local declared
  declared=$(campaign_declared_target_occurrence)
  stream_round_args=(--static-scope-map "${causynth_static_scope_map}"
    --topology-epoch "${iteration_id}")
  [[ -z "${declared}" ]] \
    || stream_round_args+=(--target-occurrence "${declared}")
  [[ -z "${causynth_client_fault_transports}" ]] || stream_round_args+=(
    --system-doors "${causynth_system_doors}"
    --client-fault-transports "${causynth_client_fault_transports}")
  [[ -z "${causynth_system_view}" ]] \
    || stream_round_args+=(--system-view "${causynth_system_view}")
  [[ -z "${region_path_max_paths_per_region}" ]] || stream_round_args+=(
    --max-paths-per-region "${region_path_max_paths_per_region}")
  [[ -z "${region_path_max_flips_per_path}" ]] || stream_round_args+=(
    --max-flips-per-path "${region_path_max_flips_per_path}")
  [[ -z "${region_path_max_tasks}" ]] \
    || stream_round_args+=(--max-tasks "${region_path_max_tasks}")
  [[ -z "${region_path_max_world_depth}" ]] || stream_round_args+=(
    --max-world-depth "${region_path_max_world_depth}")
  [[ -z "${causynth_root_domains}" ]] \
    || stream_round_args+=(--root-domains "${causynth_root_domains}")
}

campaign_stream_plan_due() {
  local entry
  (( stream_dirty == 1 )) || return 1
  (( stream_landed > 0 )) && return 0
  for entry in "${stream_jobs[@]}"; do
    [[ "${entry}" == CONFIRM\ * || "${entry}" == HARD\ * ]] || return 1
  done
  for entry in "${stream_queue[@]}" "${stream_pending[@]}" \
      "${stream_gate_owed[@]}" "${stream_gate_running[@]}"; do
    [[ "${entry}" == CONFIRM\ * ]] || return 1
  done
}

campaign_stream_confirm_owed() {
  local entry
  for entry in "${stream_jobs[@]}" "${stream_queue[@]}" \
      "${stream_pending[@]}"; do
    [[ "${entry}" != CONFIRM\ * ]] || return 0
  done
  return 1
}

campaign_stream_step_start() {
  local dir entry kind round id host status session
  local -a stream_staged=() confirms=()
  if (( ${#stream_witnesses[@]} > 0 )) && [[ -z "${stream_stop}" ]] \
      && ! campaign_stream_confirm_owed; then
    campaign_stream_step_dir
    printf '%s\n' "${stream_witnesses[@]}" >"${dir}/witnesses"
    for entry in "${stream_confirming[@]}"; do
      printf '%s\n' "${entry}"
    done >"${dir}/confirming"
    stream_witnesses=()
  else
    (( ${#stream_swaps[@]} == 0 )) || campaign_stream_swap
    (( ${#stream_staged[@]} == 0 )) || campaign_stream_move
    for entry in "${stream_pending[@]}"; do
      read -r kind round id host status _ <<<"${entry}"
      confirms+=("${id} ${status}")
    done
    stream_pending=()
    (( ${#stream_gate_owed[@]} + ${#confirms[@]} > 0 )) || return 0
    campaign_stream_step_dir
    if (( ${#stream_gate_owed[@]} > 0 )); then
      for entry in "${stream_gate_owed[@]}"; do
        printf '%s\n' "${entry#*$'\t'}"
      done >"${dir}/gate"
      for entry in "${stream_gate_owed[@]}"; do
        read -r kind round id host status session <<<"${entry%%$'\t'*}"
        [[ "${kind}" != RERUN ]] || printf '%s\n' "${session}"
      done >"${dir}/replaced"
      stream_gate_running=("${stream_gate_owed[@]}")
      stream_gate_owed=()
    fi
    (( ${#confirms[@]} == 0 )) \
      || printf '%s\n' "${confirms[@]}" >"${dir}/confirms"
  fi
  campaign_stream_step "${dir}" &
  stream_step_pid=$!
  stream_step_dir=${dir}
}

campaign_stream_step_dir() {
  dir=$(printf '%s/steps/%04d' "${iteration_dir}" "${stream_steps}")
  stream_steps=$((stream_steps + 1))
  mkdir -p "${dir}"
}

campaign_stream_step() {
  local dir=$1
  local -a witnesses=()
  if [[ -s "${dir}/witnesses" ]]; then
    mapfile -t witnesses <"${dir}/witnesses"
    campaign_stream_attempt "${dir}" "${witnesses[@]}"
  else
    [[ ! -s "${dir}/gate" ]] || campaign_import_gate "${iteration_dir}" \
      "${iteration_id}" "${dir}/import_gate.json" "${dir}/gate" \
      "${dir}/replaced"
    [[ ! -s "${dir}/confirms" ]] || campaign_stream_decide "${dir}"
  fi
  printf '%s\n' "${campaign_engine_outgrown}" >"${dir}/outgrown"
}

campaign_stream_round_start() {
  local dir row
  [[ -z "${stream_stop}" && -z "${stream_round_pid}" \
     && -z "${stream_round_returned}" ]] || return 0
  campaign_stream_plan_due || return 0
  dir=$(printf '%s/planning-%04d' "${iteration_dir}" "${stream_round}")
  [[ ! -e "${dir}" ]] || die "round directory already exists: ${dir}"
  mkdir -p "${dir}"
  for row in "${stream_flying[@]}"; do
    printf '%s\n' "${row}"
  done >"${dir}/in_flight.jsonl"
  cp -- "${results}" "${dir}/answers.jsonl"
  find "${sessions}" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' \
    | LC_ALL=C sort >"${dir}/corpus.txt"
  stream_round=$((stream_round + 1))
  stream_dirty=0
  stream_landed=0
  campaign_stream_round "${dir}" &
  stream_round_pid=$!
  stream_round_dir=${dir}
}

campaign_stream_round() {
  local dir=$1 name status=0
  name="obligations-${1##*-}"
  campaign_stream_plan "${dir}" >"${dir}/stdout.log" 2>"${dir}/stderr.log" \
    || status=$?
  if (( status == campaign_jvm_out_of_heap_status )) \
      && [[ -s "${dir}/heap-predicted" ]]; then
    printf '%s\n' "the planner of ${name}: $(cat "${dir}/heap-predicted")" \
      >"${dir}/heap-exceeded"
  elif (( status == campaign_jvm_out_of_heap_status )); then
    printf '%s\n' "the planner of ${name} ran out of the most heap a head \
JVM is given (engine_memory_mb=${engine_memory_mb:-8192}) over a corpus of \
$(campaign_corpus_mb "${sessions}") MB ($(campaign_thrown \
"${dir}/stderr.log"), ${campaign_root}/explore-reaped/$(basename \
"${dir}")/stderr.log)" >"${dir}/heap-exceeded"
  elif (( status != 0 )); then
    campaign_fail EXPLORE ExploreMain "${dir}/stderr.log" \
      "the planner of ${name} failed with exit ${status}: \
$(campaign_failure_said "${dir}/stderr.log")"
  fi
  printf '%s\n' "${campaign_engine_outgrown}" >"${dir}/outgrown"
}

campaign_stream_round_done() {
  local status=$1
  stream_round_pid=""
  (( status == 0 )) || exit "${status}"
  campaign_stream_outgrown "${stream_round_dir}/outgrown"
  stream_round_returned=${stream_round_dir}
  stream_round_dir=""
}

campaign_stream_round_take() {
  local dir=${stream_round_returned} round_dir
  stream_round_returned=""
  if [[ -s "${dir}/heap-exceeded" ]]; then
    stream_stop=PLANNER_HEAP_EXCEEDED
    stream_stop_detail=$(cat "${dir}/heap-exceeded")
    campaign_stream_round_drop "${dir}"
    return 0
  fi
  round_dir="${iteration_dir}/obligations-${dir##*-}"
  [[ ! -e "${round_dir}" ]] || die \
    "obligation round directory already exists: ${round_dir}"
  mv -- "${dir}" "${round_dir}"
  campaign_stream_take_round "${round_dir}"
}

campaign_stream_round_drop() {
  local dir=$1
  mkdir -p "${campaign_root}/explore-reaped"
  mv -- "${dir}" "${campaign_root}/explore-reaped/$(basename "${dir}")"
  stream_round=$((stream_round - 1))
  stream_round_dropped=$(basename "${dir}")
  stream_round_due=true
}

campaign_stream_outgrown() {
  local word main
  local -A grown=()
  for word in ${campaign_engine_outgrown} $(cat -- "$1"); do
    main=${word%=*}
    (( ${word##*=} <= ${grown[${main}]:-0} )) || grown[${main}]=${word##*=}
  done
  campaign_engine_outgrown=""
  for main in "${!grown[@]}"; do
    campaign_engine_outgrown+=" ${main}=${grown[${main}]}"
  done
}


campaign_planner_dir() {
  printf '%s/graphchecker-planners-%s/%s.%s\n' "${TMPDIR:-/tmp}" \
    "$(id -un)" "$(printf '%s' "$1" | sha256sum | cut -c1-16)" "$2"
}

campaign_planner_start_wait_s=300

campaign_stream_plan() {
  local round_dir=$1 state="${iteration_dir}/planner" status since
  local engine=${engine_memory_mb:-8192}
  mkdir -p "${state}"
  while true; do
    if ! campaign_planner_alive; then
      if [[ -s "${state}/id" ]]; then
        campaign_planner_ended "${round_dir}" || return
      fi
      campaign_planner_start "${engine}" \
        "$(campaign_jvm_footprint_mb "${engine}")"
    fi
    status=0
    campaign_planner_round "${round_dir}" || status=$?
    (( status == 5 )) || return "${status}"
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

campaign_planner_ended() {
  local round_dir=$1 state="${iteration_dir}/planner" status
  status=$(cat "${state}/status" 2>/dev/null) || status=""
  printf 'the planner service on %s ended with exit %s before %s (its log: \
%s)\n' "$(cat "${state}/host")" "${status:-unknown}" \
    "$(basename "${round_dir}")" "${iteration_dir}/planner.log" >&2
  campaign_thrown "${iteration_dir}/planner.log" >&2
  [[ "${status}" == "${campaign_jvm_out_of_heap_status}" ]] && return 3
  return 1
}

campaign_planner_alive() {
  local pid
  pid=$(cat "${iteration_dir}/planner/pid" 2>/dev/null) || return 1
  [[ -n "${pid}" ]] && kill -0 "${pid}" 2>/dev/null
}

campaign_planner_start() {
  local heap=$1 need=$2 state="${iteration_dir}/planner" host charge id
  local busy=""
  campaign_head_place "${need}" >&2
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
        "${iteration_dir}/planner.log" "${state}/jvm" "${need}" \
        --sessions "${sessions}" "${stream_round_args[@]}" || status=$?
    else
      campaign_run_placed "${host}" campaign_planner_serve "${heap}" "${id}" \
        "${campaign_root:+${campaign_root}/engine_peak_mb}" \
        "${iteration_dir}/planner.log" "${state}/jvm" "${need}" \
        --sessions "${sessions}" "${stream_round_args[@]}" || status=$?
    fi
    [[ -z "${busy}" ]] || rm -f -- "${busy}"
    campaign_host_release "${host}" "${charge}"
    printf '%s\n' "${status}" >"${state}/status.part"
    mv -f -- "${state}/status.part" "${state}/status"
  } </dev/null >>"${iteration_dir}/planner.log" 2>&1 &
  printf '%s\n' "$!" >"${state}/pid"
  campaign_log "the planner service starts on ${host} at ${heap} MB, \
charged ${need}" >&2
}

campaign_planner_serve() {
  local heap=$1 id=$2 peak_file=$3 log=$4 jvm_file=$5 charged=$6
  local dir watched jvm status=0 peak
  shift 6
  local sessions=""
  local -a args=("$@")
  local index
  for (( index = 0; index < ${#args[@]} - 1; index++ )); do
    [[ "${args[index]}" != --sessions ]] || sessions=${args[index + 1]}
  done
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  local ended
  for ended in "${dir%.*}".*; do
    [[ "${ended}" == "${dir}" ]] || rm -rf -- "${ended}"
  done
  mkdir -p "${dir}/requests"
  require_file "GraphChecker jar" "${graphchecker_jar}"
  (cd "${graphchecker_work_dir}" \
    && exec env "GRAPH_CHECKER_ENGINE_MEMORY_MB=${heap}" "${java_bin}" \
      "${campaign_engine_oom[@]}" "${campaign_engine_stack}" \
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
  campaign_host_max_used_pct=${campaign_head_max_used_pct} \
    campaign_watch_workload "${jvm}" "${charged}" "${watched}" "" \
    2>>"${log}"
  wait "${jvm}" || status=$?
  read -r peak 2>/dev/null <"${watched}/workload_rss_mb" || peak=0
  rm -rf -- "${watched}" "${dir}/requests" "${dir}/answers" "${dir}/out"
  campaign_engine_peak "${peak_file}" "${peak}"
  return "${status}"
}

campaign_planner_round() {
  local round_dir=$1 state="${iteration_dir}/planner" host id status=0
  host=$(cat "${state}/host")
  id=$(cat "${state}/id")
  local -a ask=(campaign_planner_ask "${sessions}" "${id}" \
    "$((10#${round_dir##*-}))" "${round_dir}/in_flight.jsonl" "${round_dir}" \
    "${round_dir}/answers.jsonl" "${round_dir}/corpus.txt")
  if campaign_host_is_local "${host}"; then
    "${ask[@]}" || status=$?
  else
    campaign_run_placed "${host}" "${ask[@]}" || status=$?
  fi
  return "${status}"
}

campaign_planner_ask() {
  local sessions=$1 id=$2 round=$3 in_flight=$4 round_dir=$5 answers=$6
  local corpus=$7 dir name answer pid gone="" since=${SECONDS} said=""
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  mkdir -p "${dir}/requests"
  name="$(date +%s%N).${BASHPID}"
  answer="${dir}/answers/${name}.json"
  jq -n -c --argjson round "${round}" --arg inFlight "${in_flight}" \
    --arg results "${answers}" --arg corpus "${corpus}" \
    --arg outputDir "${round_dir}" --arg waiter "${BASHPID}" \
    '{round: $round, inFlight: $inFlight, results: $results,
      corpus: $corpus, outputDir: $outputDir,
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
  said=$(jq -r '.exit' "${answer}")
  if [[ "${said}" == "${campaign_jvm_out_of_heap_status}" ]]; then
    jq -r '.error' "${answer}" | tee "${round_dir}/heap-predicted" >&2
    rm -f -- "${answer}"
    return "${campaign_jvm_out_of_heap_status}"
  elif [[ "${said}" != 0 ]]; then
    printf '%s\n' "$(jq -r '.error' "${answer}")" >&2
    rm -f -- "${answer}"
    return 1
  fi
  rm -f -- "${answer}"
}

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

campaign_stream_step_done() {
  local status=$1 dir=${stream_step_dir} id
  stream_step_pid=""
  stream_step_dir=""
  (( status == 0 )) || exit "${status}"
  campaign_stream_outgrown "${dir}/outgrown"
  (( ${#stream_gate_running[@]} == 0 )) || campaign_stream_land_gated
  if [[ -s "${dir}/confirm" ]]; then
    id=$(cat "${dir}/confirm")
    stream_confirming[${id}]=$(cat \
      "${iteration_dir}/witness-attempts/${id}/model")
    campaign_stream_enqueue "CONFIRM - ${id}"
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
  fi
}

campaign_stream_open() {
  local dir=$1 producer witness
  local -a fresh=()
  while read -r producer; do
    [[ -n "${stream_chain_grown[${producer}]+x}" ]] || fresh+=("${producer}")
  done <"${dir}/chain"
  stream_chain=()
  if (( ${#fresh[@]} == 0 )); then
    while read -r witness; do
      [[ ! -d "${sessions}/${witness}" ]] || stream_witnesses+=("${witness}")
    done <"${dir}/chain-witnesses"
    campaign_log "the witness's chain is open, and every producer it names \
was grown already: its witnesses are attempted again, and CONFIRM decides"
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

campaign_stream_chain_reattempt() {
  local witness
  for witness in "${stream_chain_witnesses[@]}"; do
    [[ ! -d "${sessions}/${witness}" ]] || stream_witnesses+=("${witness}")
  done
  stream_chain_witnesses=()
  stream_chain=()
}

campaign_stream_take_round() {
  local round_dir=$1 name exposures exposed proposed wave index
  local growth=$1/growth.jsonl
  local -a ids=() rows=()
  name=$(basename "${round_dir}")
  require_file "round growth rows" "${growth}"
  require_file "round obligations" "${round_dir}/obligations.jsonl"
  if (( ${#stream_growing[@]} + ${#stream_withdrawn[@]} > 0 )); then
    campaign_stream_growth_new "${round_dir}" "${growth}" \
      "${round_dir}/growth-new.jsonl"
    growth="${round_dir}/growth-new.jsonl"
  fi
  exposures=$(campaign_exposures "${growth}"; campaign_unpauses "${growth}")
  exposed=$(printf '%s' "${exposures}" | grep -c '' || true)
  mapfile -t rows < "${round_dir}/obligations.jsonl"
  mapfile -t ids < <(jq -r '.obligationId' "${round_dir}/obligations.jsonl")
  proposed=${#ids[@]}
  wave=$(jq -er '.wave' "${round_dir}/explore_manifest.json") \
    || campaign_fail EXPLORE ExploreMain "${round_dir}" \
      "${name} states no wave"
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
  if (( ${#stream_chain[@]} > 0 )); then
    campaign_stream_chain_round "${round_dir}" "${growth}" "${ids[@]}"
    return 0
  fi
  (( exposed == 0 )) || campaign_stream_grow "${round_dir}" "${growth}"
  for ((index = 0; index < proposed; index++)); do
    mkdir -p "${round_dir}/${ids[${index}]}"
    stream_flying[${ids[${index}]}]=${rows[${index}]}
    campaign_stream_enqueue "OBLIGATION ${name} ${ids[${index}]}"
  done
}

campaign_stream_growth_new() {
  local round_dir=$1 growth=$2 out=$3 lists="$3.in-flight" held=0 key=""
  campaign_json_strings "${lists}.reruns" "${!stream_reruns[@]}"
  campaign_json_strings "${lists}.withdrawn" "${!stream_withdrawn[@]}"
  for key in "${!stream_growing[@]}"; do
    printf '%s\t%s\n' "${key}" "${stream_growing[${key}]#* }"
  done | jq -R -s -c 'split("\n") | map(select(length > 0) | split("\t")
      | {key: .[0], value: .[1]}) | from_entries' >"${lists}.growing"
  jq -c --slurpfile reruns "${lists}.reruns" \
    --slurpfile withdrawn "${lists}.withdrawn" \
    --slurpfile growing "${lists}.growing" \
    --rawfile corpus "${round_dir}/corpus.txt" \
    "${campaign_growth_subject}"'
     def set: map({(.): true}) | add // {};
     ($reruns[0] | set) as $owed | ($withdrawn[0] | set) as $gone
     | ($corpus | split("\n") | map(select(length > 0)) | set) as $read
     | select((subject as $s | $s != null
               and ($owed["\(.obligationId // "") \(.sessionId // "")"]
                    or $gone[.sessionId // ""]
                    or ($growing[0][$s] as $by | $by != null and $read[$by])))
              | not)' \
    "${growth}" >"${out}"
  rm -f -- "${lists}".*
  held=$(( $(grep -c '' "${growth}" || true) - $(grep -c '' "${out}" \
    || true) ))
  (( held == 0 )) || campaign_log "$(basename "${round_dir}"): ${held} \
growth row(s) in flight, captured by GROW's re-runs"
}

campaign_growth_subject='def subject:
  if .kind == "EXPOSED_REGION" or .kind == "DOORS_ONLY_UNPAUSED"
     or .kind == "ZK_EDGE" then .occurrence
  elif .kind == "UNPLANNED_INPUT" then "\(.taskId) \(.symbol)#\(.k)"
  else null end;'

campaign_stream_chain_round() {
  local round_dir=$1 growth=$2 occurrence grow=0
  shift 2
  stream_cancelled+=("$@")
  campaign_json_strings "${round_dir}/witness-chain.json" \
    "${!stream_chain[@]}"
  jq -c --slurpfile chain "${round_dir}/witness-chain.json" \
    '($chain[0] | map({(.): true}) | add // {}) as $held
     | select(.kind == "DOORS_ONLY_UNPAUSED"
       or (.kind == "EXPOSED_REGION" or .kind == "ZK_EDGE")
       and $held[.occurrence])' \
    "${growth}" >"${round_dir}/growth-chain.jsonl"
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
"${growth}" | grep -c '' || true) unplanned input(s) wait"
  (( grow == 0 )) || campaign_stream_grow "${round_dir}" \
    "${round_dir}/growth-chain.jsonl"
}

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
truncated: ${truncated} occurrence(s) were not planned, static candidates past \
its task bound and occurrences the rows connect past the closure ceiling (its \
gaps.jsonl names them), so a claim over it misses their arms"
}

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
  campaign_json_strings "${dir}/witnesses.json" "$@"
  jq -n -c --arg step "$(basename "${step}")" --arg dir "${dir}" \
    --arg attempt "$(basename "${dir}")" \
    --slurpfile witnesses "${dir}/witnesses.json" \
    --arg claim "${claim}" --arg kind "${kind}" \
    --argjson polarity "${polarity}" --argjson exit "${status}" \
    --argjson composeMillis "${compose_ms}" \
    '{attempt: $attempt, step: $step, witnesses: $witnesses[0], dir: $dir,
      composeExit: $exit, claim: $claim, findingKind: $kind,
      polarityDecides: $polarity, composeMillis: $composeMillis}' \
    >"${dir}/attempt.json"
  campaign_log "witness $*: COMPOSE over the corpus as it stands \
(exit ${status}) claims ${claim:-nothing} ${kind} polarityDecides=${polarity}"
  [[ "${status}" -ne 0 || "${polarity}" != true ]] \
    || campaign_stream_open_chain "${step}" "${dir}" "$@"
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

campaign_stream_open_chain() {
  local step=$1 dir=$2 manifest=$2/candidate_composition_manifest.json open
  local producer
  local -a fresh=()
  shift 2
  open=$(jq '.solver.campaignClaim.openChain // [] | length' \
    "${manifest}" 2>/dev/null) || open=0
  (( open > 0 )) || return 0
  while read -r producer; do
    [[ -n "${stream_chain_grown[${producer}]+x}" ]] || fresh+=("${producer}")
  done < <(jq -r '.solver.campaignClaim.openChain[].producer
    | select(. != "")' "${manifest}" | LC_ALL=C sort -u)
  if (( ${#fresh[@]} == 0 )); then
    campaign_log "witness $*: its causal chain is open over ${open} \
value(s) no attested producer made, none naming a producer EXPLORE could \
still grow: CONFIRM decides"
    return 0
  fi
  printf '%s\n' "${fresh[@]}" >"${step}/chain"
  printf '%s\n' "$@" >"${step}/chain-witnesses"
  campaign_log "witness $*: its causal chain is open over ${open} value(s) \
no attested producer made: CONFIRM decides, and EXPLORE grows the \
${#fresh[@]} producer(s) they name meanwhile, for an attempt again should \
CONFIRM refute it"
}

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

campaign_stream_confirmed() {
  local step=$1 dir=$2 confirm_ms=$3 confirmed
  confirmed=$(jq -r '.confirmed' "${dir}/confirm.json")
  campaign_stream_attempt_row "${dir}" "${confirmed}" \
    "$(jq -r '.reason' "${dir}/confirm.json")" "${confirm_ms}" \
    "$([[ "${confirmed}" == true ]] && echo true || echo false)"
  [[ "${confirmed}" != true ]] \
    || campaign_stream_witnessed "${step}" "${dir}" "${confirmed}"
}

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

campaign_stream_drop() {
  local entry kind round id again
  local -a kept=()
  for entry in "${stream_queue[@]}"; do
    read -r kind round id again <<<"${entry}"
    if [[ "${kind}" != OBLIGATION || -n "${again}" ]]; then
      kept+=("${entry}")
      continue
    fi
    stream_cancelled+=("${id}")
    unset 'stream_flying[$id]' 'stream_queued_at[$entry]'
    rmdir -- "${iteration_dir}/${round}/${id}"
  done
  stream_queue=("${kept[@]}")
}

campaign_stream_end() {
  local pid entry kind round id host status session dir
  local -a dropped=() confirms=() withdrawn=() dropped_reruns=()
  for pid in "${!stream_jobs[@]}"; do
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    dropped+=("${kind} ${round} ${id} ${session}")
  done
  for entry in "${stream_pending[@]}"; do
    read -r kind round id host status session <<<"${entry}"
    dropped+=("${kind} ${round} ${id} ${session}")
  done
  for entry in "${stream_gate_owed[@]}" "${stream_gate_running[@]}"; do
    read -r kind round id host status session <<<"${entry%%$'\t'*}"
    if [[ "${kind}" == RERUN ]]; then
      stream_swaps+=("${round} ${id} ${session} ${status}")
    else
      dropped+=("${kind} ${round} ${id} ${session}")
    fi
  done
  stream_gate_owed=()
  stream_gate_running=()
  campaign_stream_drop
  for entry in "${stream_hard[@]}"; do
    read -r kind round id _ <<<"${entry}"
    dropped+=("${kind} ${round} ${id}")
  done
  stream_hard=()
  for entry in "${stream_queue[@]}"; do
    read -r kind round id session <<<"${entry}"
    case "${kind}" in
      CONFIRM) confirms+=("${id}") ;;
      REPLAY|OBLIGATION) dropped+=("${kind} ${round} ${id}") ;;
      RERUN) dropped_reruns+=("${round} ${id} ${session}") ;;
    esac
  done
  stream_queue=()
  stream_queued_at=()
  for entry in "${stream_swaps[@]}"; do
    read -r round id session _ <<<"${entry}"
    dropped_reruns+=("${round} ${id} ${session}")
  done
  stream_swaps=()
  for entry in "${dropped_reruns[@]}"; do
    read -r round id session <<<"${entry}"
    stream_reruns_dropped+=("${id}")
    stream_uncaptured+=("${session}")
    mkdir -p "${campaign_root}/explore-reaped/${round}"
    mv -- "${stream_reruns["${id} ${session}"]}" \
      "${campaign_root}/explore-reaped/${round}/${id}"
  done
  campaign_stream_reap
  if [[ -n "${stream_grow_round}" ]]; then
    mapfile -t -O "${#stream_uncaptured[@]}" stream_uncaptured < <(
      { campaign_exposures "${stream_grow_growth}"
        campaign_unpauses "${stream_grow_growth}"; } \
        | awk -F'\t' '$3 != "" {print $3}')
    mkdir -p "${campaign_root}/explore-reaped"
    mv -- "${iteration_dir}/generations/g${stream_generation}" \
      "${campaign_root}/explore-reaped/g${stream_generation}"
    stream_generation=$((stream_generation - 1))
    stream_grow_round=""
    stream_grow_growth=""
    stream_grow_returned=""
    stream_round_due=true
  fi
  if [[ -n "${stream_round_dir}" ]]; then
    campaign_planner_stop
    campaign_stream_round_drop "${stream_round_dir}"
    stream_round_dir=""
  fi
  if [[ -n "${stream_round_returned}" ]]; then
    campaign_stream_round_drop "${stream_round_returned}"
    stream_round_returned=""
  fi
  for entry in "${dropped[@]}"; do
    read -r kind round id session <<<"${entry}"
    if [[ "${kind}" == CONFIRM ]]; then
      confirms+=("${id}")
      continue
    fi
    stream_reaped+=("${id}")
    dir="${iteration_dir}/${round}/${id}"
    if [[ "${kind}" == RERUN ]]; then
      dir=${stream_reruns["${id} ${session}"]}
      stream_uncaptured+=("${session}")
    fi
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

campaign_frozen_tree() {
  local pid grown=1
  local -A seen=()
  tree=()
  while (( grown )); do
    grown=0
    while IFS= read -r pid; do
      [[ -n "${pid}" && -z "${seen[${pid}]:-}" ]] || continue
      kill -STOP "${pid}" 2>/dev/null || continue
      seen[${pid}]=1
      tree+=("${pid}")
      grown=1
    done < <(for pid in "$@" "${tree[@]}"; do
        campaign_process_tree "${pid}"
      done)
  done
}

campaign_stream_reap() {
  local pid hold
  local -a tree=() roots=()
  local -A ended=()
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} ${stream_round_pid} \
      ${stream_grow_pid} ${stream_ticker}; do
    roots+=("${pid}")
  done
  campaign_frozen_tree "${roots[@]}"
  (( ${#tree[@]} > 0 )) || return 0
  for pid in "${tree[@]}"; do
    ended[${pid}]=1
  done
  kill -TERM "${tree[@]}" 2>/dev/null || true
  kill -CONT "${tree[@]}" 2>/dev/null || true
  sleep "${campaign_adapter_kill_grace_s}"
  campaign_frozen_tree "${roots[@]}" "${tree[@]}"
  kill -KILL "${tree[@]}" 2>/dev/null || true
  campaign_reap_remote_workers
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} ${stream_round_pid} \
      ${stream_grow_pid} ${stream_ticker}; do
    wait "${pid}" 2>/dev/null || true
  done
  for pid in "${!stream_jobs[@]}"; do
    campaign_stream_release "${pid}"
  done
  for pid in "${tree[@]}"; do
    ended[${pid}]=1
  done
  for hold in "${campaign_host_gate_root}"/*/heads/"$(hostname -s)".*.hold; do
    [[ -e "${hold}" ]] || continue
    pid=${hold#*/heads/"$(hostname -s)".}
    [[ -z "${ended[${pid%%.*}]:-}" ]] || rm -f -- "${hold}"
  done
  stream_step_pid=""
  stream_round_pid=""
  stream_grow_pid=""
  stream_ticker=""
}

campaign_stream_release() {
  local kind round id host mb at charged held used recent
  [[ -n "${stream_job_charge[$1]:-}" ]] || return 0
  read -r kind round id host _ <<<"${stream_jobs[$1]}"
  campaign_host_release "${host}" "${stream_job_charge[$1]}"
  mb=${stream_job_charge[$1]%%.*}
  if [[ "${mb}" =~ ^[0-9]+$ && -n "${stream_host_view[${host}]:-}" ]]; then
    read -r at charged held used recent <<<"${stream_host_view[${host}]}"
    charged=$(( charged > mb ? charged - mb : 0 ))
    recent=$(( ${recent:-0} > mb ? recent - mb : 0 ))
    stream_host_view[${host}]="${at} ${charged} ${held} ${used} ${recent}"
  fi
  unset 'stream_job_charge[$1]'
}

campaign_process_tree() {
  local child
  for child in $(pgrep -P "$1" 2>/dev/null); do
    campaign_process_tree "${child}"
  done
  printf '%s\n' "$1"
}

campaign_stream_wait_bound_s=600
campaign_stream_dispatch() {
  local entry kind at first started now refused oldest="" kinds need=""
  local admit_at
  local -A stream_pass_memo=()
  while (( ${#stream_queue[@]} + ${#stream_hard[@]} > 0 )); do
    campaign_stream_collect_jobs
    campaign_stream_has_slot || return 0
    if (( ${#stream_queue[@]} == 0 )); then
      admit_at=${EPOCHREALTIME/./}
      campaign_stream_admit_host HARD || return 0
      stream_admit_us=$(( ${EPOCHREALTIME/./} - admit_at ))
      entry=${stream_hard[0]}
      stream_hard=("${stream_hard[@]:1}")
      campaign_stream_start "${entry}" "${stream_admitted_host}"
      continue
    fi
    now=${EPOCHSECONDS}
    if [[ -z "${oldest}" ]]; then
      oldest=${now}
      for at in "${stream_queued_at[@]}"; do
        (( at >= oldest )) || oldest=${at}
      done
    fi
    first=-1
    if (( now - oldest >= campaign_stream_wait_bound_s )); then
      for at in "${!stream_queue[@]}"; do
        entry=${stream_queue[at]}
        if (( now - ${stream_queued_at[${entry}]:-${now}} \
            >= campaign_stream_wait_bound_s )); then
          first=${at}
          break
        fi
      done
      (( first >= 0 )) || oldest=""
    fi
    started=-1
    refused=" "
    kinds=0
    for at in "${!stream_queue[@]}"; do
      entry=${stream_queue[at]}
      kind=${entry%% *}
      need=${stream_entry_need[${entry}]:-}
      (( first < 0 || at == first )) \
        || [[ "${kind}" == CONFIRM || "${kind}" == RERUN ]] || continue
      [[ "${refused}" != *" ${kind}${need:+:${need}} "* ]] || continue
      admit_at=${EPOCHREALTIME/./}
      if campaign_stream_admit_host "${kind}" "${need}"; then
        stream_admit_us=$(( ${EPOCHREALTIME/./} - admit_at ))
        started=${at}
        break
      fi
      campaign_stream_event refuse "${kind}" \
        "$(( ${EPOCHREALTIME/./} - admit_at ))"
      refused+="${kind}${need:+:${need}} "
      [[ -n "${need}" ]] || kinds=$((kinds + 1))
      (( kinds < 4 )) || break
    done
    (( started >= 0 )) || return 0
    entry=${stream_queue[started]}
    stream_queue=("${stream_queue[@]:0:started}" \
      "${stream_queue[@]:started+1}")
    unset 'stream_queued_at[$entry]' 'stream_entry_need[$entry]'
    [[ "${entry}" != OBLIGATION\ * ]] || unset 'stream_pass_memo[solves]'
    campaign_stream_start "${entry}" "${stream_admitted_host}"
  done
}

campaign_stream_has_slot() {
  local fresh sharers share slots charge at now=${EPOCHSECONDS}
  [[ "${stream_shared_pool}" == true ]] || return 0
  read -r at sharers <<<"${stream_sharers:-0 0}"
  if (( now - at >= campaign_host_poll_s )); then
    fresh=$(( now - campaign_head_reservation_stale_s ))
    sharers=$(find "${campaign_host_gate_root}/explorations" -maxdepth 1 \
      -type f -newermt "@${fresh}" | grep -c '') || sharers=0
    stream_sharers="${now} ${sharers}"
  fi
  (( sharers > 0 )) || sharers=1
  charge=${stream_pass_memo[slot]:-}
  if [[ -z "${charge}" ]]; then
    charge=$(campaign_stream_charge_mb)
    stream_pass_memo[slot]=${charge}
  fi
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

campaign_stream_admit_host() {
  local kind=$1 need=${2:-} host pass mb cores
  local -a order=()
  campaign_stream_memo "${kind} cores" campaign_stream_kind_cores "${kind}"
  cores=${stream_pass_memo["${kind} cores"]}
  for pass in warm cold; do
    [[ "${pass}" == cold ]] || campaign_stream_seated "${kind}" || continue
    [[ "${pass}" == warm ]] || ! campaign_stream_seated "${kind}" \
      || campaign_stream_solver_due || continue
    if [[ -n "${need}" ]]; then
      mb=${need}
    else
      campaign_stream_memo "${kind} ${pass}" campaign_stream_charge_mb \
        "${kind}" "${pass}"
      mb=${stream_pass_memo["${kind} ${pass}"]}
    fi
    campaign_stream_by_room "${kind}" "${pass}"
    for host in "${order[@]}"; do
      if campaign_stream_try_host "${host}" "${mb}" "${kind}" "${cores}" \
          "${need}"; then
        stream_admitted_pass=${pass}
        return 0
      fi
    done
  done
  if [[ -z "${stream_waiting}" ]]; then
    campaign_log "waiting for room: no host admits one more start \
(${campaign_host_wait_reason})"
    stream_waiting=1
  fi
  return 1
}

campaign_stream_unread_room=-1073741824
campaign_stream_by_room() {
  local kind=$1 pass=$2 host at best is dir="" total="" limit=0 seen=""
  local charged=0 held=0 used=0 recent=0
  local -a hosts=() rooms=()
  for host in "${stream_hosts[@]}"; do
    is=cold
    ! campaign_stream_seated "${kind}" || ! campaign_stream_warm "${host}" \
      || is=warm
    [[ "${is}" == "${pass}" ]] || continue
    hosts+=("${host}")
    if campaign_stream_view "${host}" "${EPOCHSECONDS}"; then
      read -r dir total limit <<<"${stream_host_ledger[${host}]}"
      read -r seen charged held used recent <<<"${stream_host_view[${host}]}"
      used=$(( used + ${recent:-0} ))
      rooms+=("$(( limit - held - (charged > used ? charged : used) ))")
    else
      rooms+=("${campaign_stream_unread_room}")
    fi
  done
  order=()
  while (( ${#order[@]} < ${#hosts[@]} )); do
    best=-1
    for ((at = 0; at < ${#hosts[@]}; at++)); do
      [[ -n "${rooms[at]}" ]] || continue
      (( best >= 0 && rooms[at] <= rooms[best] )) || best=${at}
    done
    order+=("${hosts[best]}")
    rooms[best]=""
  done
}

campaign_stream_memo() {
  local key=$1
  shift
  [[ -z "${stream_pass_memo[${key}]:-}" ]] || return 0
  stream_pass_memo[${key}]=$("$@")
}

campaign_stream_solver_due() {
  local host solvers=0 queued=0 oldest=${EPOCHSECONDS} entry at read_ms
  local seat=${campaign_solver_seat_seed_ms}
  local rate=${campaign_solver_read_seed_mb_s}
  (( ${stream_seated_n:-0} < campaign_solver_seat_least )) \
    || seat=$(( stream_seated_ms / stream_seated_n ))
  (( ${stream_read_mb_s:-0} <= 0 )) || rate=${stream_read_mb_s}
  for host in "${stream_hosts[@]}"; do
    campaign_stream_warm "${host}" \
      || (( ${stream_host_solves[${host}]:-0} > 0 )) || continue
    solvers=$((solvers + 1))
  done
  (( solvers > 0 )) || return 0
  if [[ -z "${stream_pass_memo[solves]:-}" ]]; then
    for entry in "${stream_queue[@]}"; do
      [[ "${entry}" == OBLIGATION\ * ]] || continue
      queued=$((queued + 1))
      at=${stream_queued_at[${entry}]:-${EPOCHSECONDS}}
      (( at >= oldest )) || oldest=${at}
    done
    stream_pass_memo[solves]="${queued} ${oldest}"
  fi
  read -r queued oldest <<<"${stream_pass_memo[solves]}"
  campaign_stream_memo corpus campaign_corpus_mb "${sessions:-}"
  campaign_stream_memo seats campaign_solver_seats "${sessions:-}"
  read_ms=$(( stream_pass_memo[corpus] * 1000 / rate ))
  (( queued * seat > solvers * stream_pass_memo[seats] * read_ms \
     || (EPOCHSECONDS - oldest) * 1000 > read_ms ))
}

campaign_solver_seat_seed_ms=2000
campaign_solver_read_seed_mb_s=160
campaign_solver_seat_least=4

campaign_stream_seated_returned() {
  local since pass now seconds
  read -r since pass <<<"${stream_job_since[$1]:-}"
  [[ -n "${since}" ]] || return 0
  now=$(( ${EPOCHREALTIME/./} / 1000 ))
  if [[ "${pass}" == warm ]]; then
    stream_seated_ms=$(( ${stream_seated_ms:-0} + now - since ))
    stream_seated_n=$(( ${stream_seated_n:-0} + 1 ))
  elif (( ${stream_read_mb_s:-0} <= 0 )); then
    seconds=$(( (now - since + 999) / 1000 ))
    stream_read_mb_s=$(( $(campaign_corpus_mb "${sessions:-}") / seconds ))
    (( stream_read_mb_s > 0 )) || stream_read_mb_s=1
  fi
}

campaign_stream_warm() {
  local seen=${stream_solver_seen[$1]:-}
  [[ -n "${seen}" ]] && (( EPOCHSECONDS - seen < campaign_solver_idle_s ))
}

campaign_stream_charge_mb() {
  local need
  if [[ "${1:-}" == OBLIGATION && "${2:-cold}" == warm ]]; then
    printf '0\n'
  elif [[ "${1:-}" == OBLIGATION ]]; then
    campaign_solver_need_mb "${sessions:-}"
  elif [[ "${1:-}" == HARD ]]; then
    campaign_decide_need_mb
  else
    need=$(campaign_replay_need_mb)
    (( campaign_replay_typical_mb == 0 \
       || campaign_replay_typical_mb >= need )) \
      || need=${campaign_replay_typical_mb}
    campaign_replay_charge_mb "${need}"
  fi
}

campaign_stream_try_host() {
  local host=$1 mb=$2 kind=${3:-} cores=${4:-1} own=${5:-} status=0
  local spare=$(( campaign_replay_spikes * campaign_replay_spike_mb ))
  campaign_stream_has_cores "${host}" "${cores}" || return 1
  ! campaign_stream_seated "${kind}" || campaign_stream_has_seat "${host}" \
    || return 1
  [[ -z "${own}" ]] || spare=0
  case "${kind}" in
    OBLIGATION|HARD) campaign_stream_try_charge "${host}" "${mb}" ;;
    *) campaign_stream_try_charge "${host}" "${mb}" "${spare}" ;;
  esac
  case "${status}" in
    0)
      stream_admitted_host=${host}
      stream_admitted_mb=${mb}
      stream_admitted_cores=${cores}
      unset 'stream_host_unread[$host]'
      stream_waiting=""
      return 0 ;;
    2) campaign_stream_unreadable "${host}" ;;
    *) unset 'stream_host_unread[$host]' ;;
  esac
  return 1
}

campaign_stream_has_cores() {
  local host=$1 need=${2:-1} cores
  if [[ -z "${stream_host_cores[${host}]+x}" ]]; then
    if ! cores=$(campaign_host_cores "${host}"); then
      campaign_stream_unreadable "${host}"
      return 1
    fi
    stream_host_cores[${host}]=${cores}
  fi
  (( ${stream_host_busy[${host}]:-0} == 0 \
     || ${stream_host_busy[${host}]:-0} + need \
       <= ${stream_host_cores[${host}]} ))
}

campaign_stream_kind_cores() {
  case "${1:-}" in
    OBLIGATION|HARD) printf '2\n' ;;
    *) printf '%s\n' "${campaign_replay_cores}" ;;
  esac
}

campaign_stream_seated() {
  [[ "${1:-}" == OBLIGATION ]]
}

campaign_stream_has_seat() {
  local host=$1 solves=${stream_host_solves[$1]:-0}
  if campaign_stream_warm "${host}"; then
    campaign_stream_memo seats campaign_solver_seats "${sessions:-}"
    (( solves < stream_pass_memo[seats] ))
  else
    (( solves == 0 ))
  fi
}

campaign_stream_try_charge() {
  local host=$1 need=$2 spare=${3:-0} dir total limit at charged held used
  local recent=0
  status=0
  if ! campaign_stream_view "${host}" "${EPOCHSECONDS}"; then
    status=2
    return 0
  fi
  read -r dir total limit <<<"${stream_host_ledger[${host}]}"
  read -r at charged held used recent <<<"${stream_host_view[${host}]}"
  if ! campaign_host_fits "${charged}" "${used}" "${held}" "${need}" \
      "${spare}" "${limit}"; then
    campaign_host_refused "${dir##*/}" "${charged}" "${used}" "${held}" \
      "${need}" "${spare}" "${limit}" "${total}"
    status=1
    return 0
  fi
  held=$(campaign_host_head_room "${dir}" "${EPOCHSECONDS}")
  campaign_host_unlocked campaign_host_admit "${dir}" "${total}" \
    "${limit}" "${used}" "${held}" "${need}" "${spare}"
  charged=${campaign_host_admitted_charged}
  (( status != 0 )) || charged=$(( charged + need ))
  (( status != 0 )) || recent=$(( ${recent:-0} + need ))
  stream_host_view[${host}]="${at} ${charged} ${held} ${used} ${recent:-0}"
}

campaign_stream_view() {
  local host=$1 now=$2 dir total limit at available
  if [[ -z "${stream_host_ledger[${host}]:-}" ]]; then
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
    mkdir -p "${dir}"
    total=$(campaign_host_memory_total "${host}" "${dir}") || return 1
    stream_host_ledger[${host}]="${dir} ${total} \
$(campaign_host_limit_mb "${total}")"
  fi
  read -r at _ <<<"${stream_host_view[${host}]:-0}"
  (( now - at >= campaign_host_poll_s )) || return 0
  read -r dir total limit <<<"${stream_host_ledger[${host}]}"
  available=$(campaign_host_poll_s=${campaign_host_reading_keep_s} \
    campaign_host_memory_reading "${host}" "${dir}" "${now}") || return 1
  stream_host_view[${host}]="${now} $(campaign_host_charged "${dir}" \
"${now}") $(campaign_host_head_room "${dir}" "${now}") \
$(( total - available )) 0"
}

campaign_stream_read_hosts() {
  local host dir owner=${BASHPID}
  stream_reading="${iteration_dir}/reading"
  : >"${stream_reading}"
  for host in "${stream_hosts[@]}"; do
    dir="${campaign_host_gate_root}/$(campaign_host_key "${host}")"
    mkdir -p "${dir}"
    ( ( campaign_close_inherited_fds
        while kill -0 "${owner}" 2>/dev/null \
          && [[ -e "${stream_reading}" ]]; do
          campaign_host_memory_reading "${host}" "${dir}" "${EPOCHSECONDS}" \
            || true
          command sleep "$(( campaign_host_poll_s > 0 ? campaign_host_poll_s \
            : 1 ))"
        done ) </dev/null >/dev/null 2>&1 & )
  done
}

campaign_stream_unread_hosts() {
  [[ -z "${stream_reading}" ]] || rm -f -- "${stream_reading}"
  stream_reading=""
}

campaign_stream_unreadable() {
  local host=$1
  [[ -n "${stream_host_unread[${host}]+x}" ]] \
    || stream_host_unread[${host}]=${SECONDS}
  (( SECONDS - stream_host_unread[${host}] < campaign_ssh_patience_s )) \
    && return 0
  campaign_fail EXPLORE CAMPAIGN "${host}" "the memory of host ${host} \
could not be read for ${campaign_ssh_patience_s}s"
}

campaign_stream_event() {
  local IFS=$'\t'
  [[ -n "${iteration_dir:-}" ]] || return 0
  { printf '%s\t%s\n' "${EPOCHREALTIME}" "$*" \
      >>"${iteration_dir}/stream_events.tsv"; } 2>/dev/null || true
}

campaign_stream_start() {
  local entry=$1 host=$2 kind round id session worker need
  local classes=${stream_classes} plan=${stream_plan} started=host.txt
  local -a work=()
  read -r kind round id session <<<"${entry}"
  need=$(campaign_replay_basis_mb)
  (( need >= stream_admitted_mb )) || need=${stream_admitted_mb}
  case "${kind}" in
    OBLIGATION)
      worker="${iteration_dir}/${round}/${id}"
      [[ "${session}" != again ]] || started=again-host.txt
      session=""
      work=("${id}" "${iteration_dir}/${round}/obligations.jsonl" \
        "${sessions}" "${worker}" "${stream_admitted_mb}" \
        "${campaign_host_charge_id}") ;;
    HARD)
      worker="${iteration_dir}/${round}/${id}"
      session=""
      started=$(basename "$(campaign_stream_logs "${kind}" \
        "${worker}")host.txt")
      work=("${id}" "${iteration_dir}/${round}/obligations.jsonl" \
        "${sessions}" "${worker}" "${stream_admitted_mb}" HARD) ;;
    REPLAY)
      worker="${iteration_dir}/${round}/${id}"
      read -r classes plan <<<"${session}"
      session=""
      unset 'stream_rests[$id]'
      started=replay-host.txt
      work=("${id}" "${classes}" "${worker}" "${worker}/sessions" \
        "${plan}" "${stream_admitted_mb}" "${need}") ;;
    CONFIRM)
      worker="${campaign_root}/witness-confirm/${id}/worker"
      date +%s%3N >"$(dirname "${worker}")/started-at"
      work=("$(dirname "${worker}")" "${classes}" "${plan}" \
        "${stream_admitted_mb}" "${need}") ;;
    RERUN)
      worker=${stream_reruns["${id} ${session}"]}
      work=("${id}" "${classes}" "${worker}" "${worker}/sessions" \
        "${plan}" "${stream_admitted_mb}" "${need}") ;;
  esac
  campaign_stream_event admit "${kind}" "${id}" "${host}" \
    "${stream_admit_us:-0}" "$(campaign_stream_logs "${kind}" "${worker}")"
  { printf '%s\n' "${host}" >"${worker}/${started}"
    campaign_stream_job "${kind}" "${host}" "${campaign_host_charge_id}" \
      "${id}" "${worker}" "${work[@]}"; } &
  stream_jobs[$!]="${kind} ${round} ${id} ${host} ${session}"
  stream_job_charge[$!]=${campaign_host_charge_id}
  ! campaign_stream_seated "${kind}" || stream_job_since[$!]="$(( \
    ${EPOCHREALTIME/./} / 1000 )) ${stream_admitted_pass:-}"
  stream_job_worker[$!]=${worker}
  stream_job_tree[$!]="${classes} ${plan}"
  stream_job_cores[$!]=${stream_admitted_cores}
  campaign_stream_host_count "${host}" "${kind}" 1 "${stream_job_cores[$!]}"
}

campaign_stream_host_count() {
  local host=$1 kind=$2 delta=$3 cores=${4:-}
  [[ -n "${cores}" ]] || cores=$(campaign_stream_kind_cores "${kind}")
  stream_host_busy[${host}]=$(( ${stream_host_busy[${host}]:-0} \
    + delta * cores ))
  ! campaign_stream_seated "${kind}" \
    || stream_host_solves[${host}]=$(( ${stream_host_solves[${host}]:-0} \
      + delta ))
}

campaign_stream_collect_jobs() {
  local pid status
  for pid in "${!stream_jobs[@]}"; do
    ! kill -0 "${pid}" 2>/dev/null || continue
    status=0
    wait "${pid}" || status=$?
    campaign_stream_ended "${pid}" "${status}"
    stream_pass_memo=()
  done
}

campaign_stream_wait() {
  local pid finished="" status
  local -a ended=()
  campaign_head_heartbeat
  if [[ -z "${stream_ticker}" ]]; then
    sleep "${campaign_host_poll_s}" &
    stream_ticker=$!
  fi
  for pid in "${!stream_jobs[@]}" ${stream_step_pid} ${stream_round_pid} \
      ${stream_grow_pid} "${stream_ticker}"; do
    kill -0 "${pid}" 2>/dev/null || ended+=("${pid}")
  done
  if (( ${#ended[@]} == 0 )); then
    status=0
    wait -n -p finished "${!stream_jobs[@]}" ${stream_step_pid} \
      ${stream_round_pid} ${stream_grow_pid} "${stream_ticker}" || status=$?
    [[ -z "${finished}" ]] || campaign_stream_ended "${finished}" "${status}"
  fi
  for pid in "${ended[@]}"; do
    status=0
    wait "${pid}" || status=$?
    campaign_stream_ended "${pid}" "${status}"
  done
}

campaign_stream_ended() {
  local pid=$1 status=$2 kind round id host session worker answer again
  local rests="" world="" requeued=0
  if [[ "${pid}" == "${stream_ticker}" ]]; then
    stream_ticker=""
  elif [[ "${pid}" == "${stream_step_pid}" ]]; then
    campaign_stream_step_done "${status}"
  elif [[ "${pid}" == "${stream_round_pid}" ]]; then
    campaign_stream_round_done "${status}"
  elif [[ "${pid}" == "${stream_grow_pid}" ]]; then
    campaign_stream_grow_done "${status}"
  else
    read -r kind round id host session <<<"${stream_jobs[${pid}]}"
    worker=${stream_job_worker[${pid}]}
    campaign_stream_event collect "${kind}" "${id}" "${host}" "${status}"
    campaign_stream_release "${pid}"
    campaign_replay_measured "${worker}"
    campaign_stream_host_count "${host}" "${kind}" -1 \
      "${stream_job_cores[${pid}]:-}"
    answer=""
    again=""
    if [[ "${status}" -eq 0 ]] && campaign_stream_replays "${kind}" \
        && campaign_stream_replay_again "${kind}" "${round}" "${id}" \
          "${session}" "${worker}" "${stream_job_tree[${pid}]}"; then
      requeued=1
    elif campaign_stream_killed_again "${kind}" "${round}" "${id}" \
        "${host}" "${status}" "${worker}" "${stream_job_tree[${pid}]}"; then
      requeued=1
    elif [[ "${status}" -eq 0 ]] && campaign_stream_solves "${kind}"; then
      again=$(jq -r '.why // ""' "${worker}/solve_again" 2>/dev/null) \
        || again=""
      [[ -n "${again}" ]] \
        || answer=$(jq -r '"\(.verdict // "")|\(.detail // "")"' \
          "${worker}/obligation_result.jsonl" 2>/dev/null) || answer=""
    fi
    if campaign_stream_seated "${kind}" && [[ -n "${answer}" ]]; then
      stream_solver_seen[${host}]=$(date +%s)
      campaign_stream_seated_returned "${pid}"
    elif campaign_stream_seated "${kind}" && [[ -n "${again}" ]]; then
      unset 'stream_solver_seen[$host]'
    fi
    if (( requeued )); then
      :
    elif [[ -n "${again}" ]]; then
      rm -f -- "${worker}/solve_again"
      campaign_stream_solve_again "${kind}" "${round}" "${id}" "${host}" \
        "${worker}" "${again}"
    elif [[ "${answer}" == SAT_MODEL_READY\|* ]]; then
      rests=$(jq -r '.pathSessionId // ""' "${worker}/focused_task.jsonl" \
        2>/dev/null) || rests=""
      world=$(jq -r '.world // ""' "${worker}/focused_task.jsonl" \
        2>/dev/null) || world=""
      if [[ -n "${rests}" && -n "${stream_withdrawn[${rests}]:-}" ]]; then
        campaign_stream_replay_drop \
          "REPLAY ${round} ${id} ${stream_job_tree[${pid}]}" "${rests}"
      elif [[ -n "${world}" && -n "${stream_worlds[${world}]:-}" ]]; then
        campaign_stream_duplicate "${kind} ${round} ${id} ${host} 0" \
          "${world}" "${stream_worlds[${world}]}"
      else
        if [[ -n "${world}" ]]; then
          stream_worlds[${world}]=${id}
          stream_world_of[${id}]=${world}
        fi
        campaign_log "obligation ${id}: solved on ${host}, its replay queued"
        [[ -z "${rests}" ]] || stream_rests[${id}]=${rests}
        campaign_stream_enqueue \
          "REPLAY ${round} ${id} ${stream_job_tree[${pid}]}"
      fi
    elif [[ "${kind}" != HARD && -s "${worker}/obligation_ask.json" \
        && ( "${answer}" == NOT_ADMITTED\|SOLVER_MEMOUT\ * \
             || "${answer}" == NOT_ADMITTED\|SOLVER_TIMEOUT\ * ) ]] \
        && { [[ "${answer}" == *SOLVER_MEMOUT* ]] \
             || campaign_solver_two_lanes; }; then
      mv -f -- "${worker}/obligation_result.jsonl" \
        "${worker}/obligation_result.first.jsonl"
      campaign_stream_hard "${round}" "${id}" "${host}" "${worker}" \
        "undecided on ${host} (${answer#*|})"
    else
      campaign_stream_collected \
        "${kind} ${round} ${id} ${host} ${status} ${session}"
    fi
    unset 'stream_jobs[$pid]' 'stream_job_worker[$pid]' \
      'stream_job_tree[$pid]' 'stream_job_since[$pid]' 'stream_job_cores[$pid]'
  fi
}

campaign_stream_solve_again() {
  local kind=$1 round=$2 id=$3 host=$4 worker=$5 why=$6 charge
  charge=$(campaign_solver_need_mb "${sessions:-}")
  if ! campaign_pool_can_hold "${charge}" "${stream_hosts[@]}"; then
    campaign_obligation_unanswered "${id}" "${worker}" "no host of the pool \
can hold its solver of ${charge} MB (${why})"
    campaign_log "obligation ${id}: no host of the pool can hold its solver \
of ${charge} MB; answered NOT_ADMITTED"
    campaign_stream_land "${kind} ${round} ${id} ${host} 0"
    return 0
  fi
  campaign_log "obligation ${id}: ${why}; asked again of a host's solver"
  campaign_stream_enqueue "OBLIGATION ${round} ${id} again"
}

campaign_stream_replays() {
  [[ "${1:-}" == REPLAY || "${1:-}" == RERUN || "${1:-}" == CONFIRM ]]
}

campaign_killed_attempts=2

campaign_stream_killed_again() {
  local kind=$1 round=$2 id=$3 host=$4 status=$5 worker=$6 tree=$7
  local ended=0 aside file path=""
  [[ "${kind}" == REPLAY ]] || return 1
  (( status == 255 || status > 128 )) || return 1
  ! campaign_host_is_local "${host}" || return 1
  ls -- "${worker}" >/dev/null 2>&1 || true
  [[ ! -s "${worker}/obligation_result.jsonl" ]] || return 1
  for aside in "${worker}"/killed-*; do
    [[ ! -d "${aside}" ]] || ended=$((ended + 1))
  done
  (( ended < campaign_killed_attempts )) || return 1
  aside="${worker}/killed-$((ended + 1))"
  mkdir -p -- "${aside}"
  for file in "${campaign_replay_ended_files[@]}" stdout.log stderr.log \
      ssh.log replay-stdout.log replay-stderr.log replay-host.txt; do
    [[ ! -e "${worker}/${file}" ]] || mv -f -- "${worker}/${file}" "${aside}/"
  done
  campaign_reap_on_host "${host}" "${worker}"
  campaign_withdraw_sessions "${id}" "${worker}/sessions" \
    "${aside}/sessions" "its replay's worker on ${host} ended with exit \
${status} before it answered, and it is asked again"
  campaign_log "REPLAY ${id} on ${host}: its worker ended with exit \
${status} (its ssh connection lost, or a signal) before it answered: no \
verdict; set aside in ${aside} and asked again"
  path=$(jq -r '.pathSessionId // ""' "${worker}/focused_task.jsonl" \
    2>/dev/null) || path=""
  if [[ -n "${path}" && -n "${stream_withdrawn[${path}]:-}" ]]; then
    campaign_stream_replay_drop "REPLAY ${round} ${id} ${tree}" "${path}"
    return 0
  fi
  campaign_stream_enqueue "REPLAY ${round} ${id} ${tree}"
}

campaign_stream_replay_again() {
  local kind=$1 round=$2 id=$3 session=$4 worker=$5 tree=$6 refused=""
  local charged="" aside="" file="" full entry heap="" ran=0 again=0
  ls -- "${worker}" >/dev/null 2>&1 || true
  [[ -s "${worker}/replay_again" ]] || return 1
  read -r refused charged aside heap <"${worker}/replay_again"
  rm -f -- "${worker}/replay_again"
  [[ "${refused}" =~ ^[0-9]+$ ]] || refused=0
  [[ "${heap}" =~ ^[0-9]+$ ]] || heap=""
  for file in "$(campaign_stream_logs "${kind}" "${worker}")"{stdout.log,\
stderr.log,host.txt}; do
    [[ ! -e "${file}" || ! -d "${aside}" ]] || mv -f -- "${file}" "${aside}/"
  done
  (( refused <= campaign_replay_peak_mb )) \
    || campaign_replay_peak_mb=${refused}
  full=$(campaign_replay_full_need_mb "${refused}")
  case "${kind}" in
    REPLAY) entry="REPLAY ${round} ${id} ${tree}" ;;
    RERUN) entry="RERUN ${round} ${id} ${session}" ;;
    CONFIRM) entry="CONFIRM - ${id}" ;;
  esac
  if [[ -n "${heap}" ]]; then
    for file in "${worker}"/ended-*/"${campaign_out_of_heap_file}"; do
      [[ ! -s "${file}" ]] || ran=$((ran + 1))
    done
    (( ran >= 2 )) || ! campaign_replay_heap_raised "${heap}" \
      "${kind} ${id}" || again=1
  else
    (( full <= refused )) || again=1
  fi
  if (( again )); then
    if [[ "${kind}" == REPLAY ]]; then
      file=$(jq -r '.pathSessionId // ""' "${worker}/focused_task.jsonl" \
        2>/dev/null) || file=""
      if [[ -n "${file}" && -n "${stream_withdrawn[${file}]:-}" ]]; then
        campaign_stream_replay_drop "${entry}" "${file}"
        return 0
      fi
      [[ -z "${file}" ]] || stream_rests[${id}]=${file}
    fi
    if [[ -n "${heap}" ]]; then
      campaign_stream_enqueue "${entry}"
      return 0
    fi
    campaign_log "${kind} ${id}: its replay was ended at ${refused} MB, \
charged ${charged} MB, as its host could not take its growth: queued again \
at its full need, ${full} MB"
    stream_entry_need[${entry}]=${full}
    campaign_stream_enqueue "${entry}"
    return 0
  fi
  if [[ "${kind}" == CONFIRM ]]; then
    id=CONFIRM
    file="$(dirname "${worker}")/sessions"
  else
    file="${worker}/sessions"
  fi
  if [[ -n "${heap}" ]] && (( ran >= 2 )); then
    campaign_replay_bounded "${id}" "${worker}" "${file}" "replay ran out \
of its heap twice, the second time at ${heap} MB"
  elif [[ -n "${heap}" ]]; then
    campaign_replay_bounded "${id}" "${worker}" "${file}" "replay ran out \
of its ${heap} MB heap, the most a replay's heap is"
  else
    campaign_replay_bounded "${id}" "${worker}" "${file}" "replay was ended \
at ${refused} MB as its host could not take its growth, and its full need, \
${full} MB, is the most a replay is charged"
  fi
  return 1
}

campaign_stream_hard() {
  local round=$1 id=$2 host=$3 worker=$4 why=$5 charge
  charge=$(campaign_decide_need_mb)
  if ! campaign_pool_can_hold "${charge}" "${stream_hosts[@]}"; then
    campaign_obligation_unanswered "${id}" "${worker}" "no host of the pool \
can hold its hard-lane ask of ${charge} MB (${why})"
    campaign_log "obligation ${id}: no host of the pool can hold its \
hard-lane ask of ${charge} MB; answered NOT_ADMITTED"
    campaign_stream_land "HARD ${round} ${id} ${host} 0"
    return 0
  fi
  campaign_log "obligation ${id}: ${why}; its hard-lane ask of ${charge} MB \
queued (${solver_timeout_ms} ms, a z3 room of ${campaign_hard_z3_room_mb} MB, \
no corpus read) once no other start waits"
  stream_hard+=("HARD ${round} ${id}")
}

campaign_stream_enqueue() {
  local entry=$1 at=0
  case "${entry%% *}" in
    CONFIRM|RERUN) stream_queue=("${entry}" "${stream_queue[@]}") ;;
    *)
      if campaign_stream_fault_replay "${entry}"; then
        stream_queue+=("${entry}")
      else
        while (( at < ${#stream_queue[@]} )) \
            && [[ "${stream_queue[at]}" != REPLAY\ * ]]; do
          at=$((at + 1))
        done
        stream_queue=("${stream_queue[@]:0:at}" "${entry}" \
          "${stream_queue[@]:at}")
      fi ;;
  esac
  stream_queued_at[${entry}]=$(date +%s)
}

campaign_stream_fault_replay() {
  local kind round id
  read -r kind round id _ <<<"$1"
  [[ "${kind}" == REPLAY ]] || return 1
  [[ "$(jq -r '.faultFlip // false' \
    "${iteration_dir}/${round}/${id}/focused_task.jsonl" 2>/dev/null)" \
    == true ]]
}

campaign_stream_collected() {
  local entry=$1 kind round id host status session worker named=""
  read -r kind round id host status session <<<"${entry}"
  case "${kind}" in
    CONFIRM)
      stream_pending+=("${entry}")
      return 0 ;;
    RERUN)
      worker=${stream_reruns["${id} ${session}"]}
      (( status != 0 )) || named=$(jq -r '.sessionId // ""' \
        "${worker}/obligation_result.jsonl" 2>/dev/null) || named=""
      if [[ -z "${named}" ]]; then
        stream_swaps+=("${round} ${id} ${session} ${status}")
        return 0
      fi ;;
    *)
      worker="${iteration_dir}/${round}/${id}"
      [[ "${status}" -eq 0 ]] || campaign_obligation_unfinished "${host}" \
        "${id}" "${worker}" "${status}" "${kind}"
      named=$(jq -r '.sessionId // ""' "${worker}/obligation_result.jsonl" \
        2>/dev/null) || named=""
      if [[ -z "${named}" ]]; then
        campaign_stream_land "${entry}"
        return 0
      fi ;;
  esac
  [[ -d "${worker}/sessions/${named}" ]] || campaign_fail EXPLORE CAMPAIGN \
    "${worker}/sessions" "the verdict names session ${named}, which its \
worker did not stage"
  stream_gate_owed+=("${entry}"$'\t'"${worker}/sessions/${named}"$'\t'"${worker}")
}

campaign_stream_duplicate() {
  local entry=$1 world=$2 first=$3 kind round id host status worker
  read -r kind round id host status <<<"${entry}"
  worker="${iteration_dir}/${round}/${id}"
  jq -n -c --arg id "${id}" --arg detail "DUPLICATE_WORLD: its model plants \
world ${world}, which obligation ${first} already replays (queued, running or \
landed): that replay answers it, the path it was asked from changing only the \
schedule prefix, which is timing" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: "DUPLICATE_WORLD", sessionId: "", detail: $detail}' \
    | campaign_write_whole "${worker}/obligation_result.jsonl"
  [[ ! -e "${worker}/question.asked" ]] \
    || mv -f -- "${worker}/question.asked" "${worker}/question.txt"
  stream_duplicates+=("${id}:${first}")
  campaign_log "obligation ${id}: world ${world} is obligation ${first}'s; \
DUPLICATE_WORLD, no replay"
  campaign_stream_land "${entry} -"
}

campaign_stream_land() {
  local kind round id host status session worker verdict
  read -r kind round id host status session <<<"$1"
  unset 'stream_flying[$id]'
  worker="${iteration_dir}/${round}/${id}"
  verdict=$(jq -r '.verdict // "?"' "${worker}/obligation_result.jsonl" \
    2>/dev/null) || verdict="?"
  if [[ "${kind}" == REPLAY && "${verdict}" != ADMITTED \
      && "$(declare -p stream_world_of 2>/dev/null)" == "declare -A"* ]] \
      && [[ -n "${stream_world_of[${id}]:-}" ]]; then
    unset "stream_worlds[${stream_world_of[${id}]}]"
  fi
  campaign_log "obligation ${id}: host=${host} verdict=${verdict}"
  if [[ "${kind}" == HARD && "${verdict}" == NOT_ADMITTED ]] && jq -e \
      '.detail // "" | startswith("SOLVER_TIMEOUT")
         or startswith("SOLVER_MEMOUT")' \
      "${worker}/obligation_result.jsonl" >/dev/null 2>&1; then
    jq -c --arg host "${host}" '{obligationId, detail, host: $host}' \
      "${worker}/obligation_result.jsonl" \
      >>"${iteration_dir}/solver_timeouts.jsonl"
  fi
  cat -- "${worker}/obligation_result.jsonl" >>"${results}"
  stream_dirty=1
}

campaign_stream_land_gated() {
  local line entry staged worker kind round id host status session
  local -a stream_staged=()
  for line in "${stream_gate_running[@]}"; do
    entry=${line%%$'\t'*}
    staged=${line#*$'\t'}
    worker=${staged#*$'\t'}
    staged=${staged%%$'\t'*}
    read -r kind round id host status session <<<"${entry}"
    if [[ "${kind}" == RERUN ]]; then
      stream_swaps+=("${round} ${id} ${session} ${status}")
      continue
    fi
    stream_staged=("${worker} $(dirname "${staged}") $(basename "${staged}")")
    campaign_stream_move
    campaign_stream_land "${entry}"
  done
  stream_gate_running=()
}

campaign_stream_swap_due() {
  local session=$1 attempt="" witness=""
  for witness in "${stream_witnesses[@]}" "${stream_deferred[@]}"; do
    [[ "${witness}" != "${session}" ]] || return 1
  done
  for attempt in "${!stream_confirming[@]}"; do
    [[ -f "${iteration_dir}/witness-attempts/${attempt}/corpus.txt" ]] \
      || return 1
    ! grep -qxF -- "${session}" \
      "${iteration_dir}/witness-attempts/${attempt}/corpus.txt" || return 1
  done
  [[ -n "${stream_round_dir}" && ! -e "${stream_round_dir}/corpus_read" ]] \
    || return 0
  ls -- "${stream_round_dir}" >/dev/null 2>&1 || true
  [[ -e "${stream_round_dir}/corpus_read" ]] \
    || ! grep -qxF -- "${session}" "${stream_round_dir}/corpus.txt"
}

campaign_stream_move() {
  local entry worker staged session
  for entry in "${stream_staged[@]}"; do
    read -r worker staged session <<<"${entry}"
    [[ -d "${staged}/${session}" ]] || campaign_fail EXPLORE CAMPAIGN \
      "${staged}" "the verdict names session ${session}, which its worker \
did not stage"
    mv -- "${staged}/${session}" "${sessions}/${session}"
    stream_landed=$((stream_landed + 1))
    [[ -z "${stream_stop}" && "${stream_stop_at_witness}" == true ]] \
      && campaign_stream_fatal \
      "${worker}/obligation_result.jsonl" "${sessions}/${session}" || continue
    stream_witnesses+=("${session}")
  done
  stream_staged=()
}

campaign_json_strings() {
  local file=$1
  shift
  printf '%s\n' "$@" | jq -R 'select(length > 0)' | jq -s -c . >"${file}"
}

campaign_exposures() {
  jq -r 'select(.kind == "EXPOSED_REGION" or .kind == "UNPLANNED_INPUT")
         | [.obligationId, (.regionId // "\(.taskId) \(.symbol)#\(.k)"),
            .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

campaign_unpauses() {
  jq -r 'select(.kind == "DOORS_ONLY_UNPAUSED" or .kind == "ZK_EDGE")
         | [.obligationId, .occurrence, .sessionId] | @tsv' "$1" \
    | LC_ALL=C sort -u
}

campaign_stream_grow() {
  local round_dir=$1 generation
  local growth=${2:-${round_dir}/growth.jsonl}
  local planned_only
  planned_only=$(campaign_exposures "${growth}" | awk -F'\t' '$1 == ""' \
    | grep -c '' || true)
  (( planned_only == 0 )) || campaign_log "$(basename "${round_dir}"): \
${planned_only} exposure(s) only the seed ran grow the plan alone: no replay \
is re-run for them, the anchor's path re-runs once they are planned \
(PathReruns)"
  stream_generation=$((stream_generation + 1))
  generation="${iteration_dir}/generations/g${stream_generation}"
  mkdir -p "${generation}"
  campaign_stream_grow_build "${round_dir}" "${growth}" "${generation}" \
    "${stream_plan}" "${stream_classes}" &
  stream_grow_pid=$!
  stream_grow_round=${round_dir}
  stream_grow_growth=${growth}
  stream_hold=$((stream_hold + 1))
}

campaign_stream_grow_build() {
  local round_dir=$1 growth=$2 generation=$3 plan=$4 classes=$5 status=0
  local unpaused key held
  campaign_unpauses "${growth}" | cut -f2 | jq -R . | jq -s -c . \
    >"${generation}/unpaused.json"
  unpaused=$(jq 'length' "${generation}/unpaused.json")
  jq -c --slurpfile unpaused "${generation}/unpaused.json" \
    '($unpaused[0] | map({(.): true}) | add // {}) as $held
     | if .doorsOnly == true and .doorsOnlyDeclared != true
          and $held[.occurrenceId] then del(.doorsOnly)
       else . end' \
    "${plan}" >"${generation}/unpaused_plan.jsonl"
  if [[ -n "$(campaign_exposures "${growth}")" ]] \
      || jq -e -s 'any(.[]; .kind == "ZK_EDGE")' "${growth}" >/dev/null; then
    run_capturing_status run_java_main \
      edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain \
      --iteration "${iteration_dir}" \
      --static-scope-map "${causynth_static_scope_map}" \
      --plan "${generation}/unpaused_plan.jsonl" \
      --growth "${growth}" \
      --output "${generation}/execution_task_plan.jsonl" \
      --zk-chain "${iteration_dir}/zk_chain.jsonl" \
      --zk-chain-output "${generation}/zk_chain.jsonl" \
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
  key=$(campaign_weave_key "${generation}/execution_task_plan.jsonl") \
    || exit 1
  held="$(dirname "${classes}")/weave_key"
  require_nonempty "the weave key of the tree GROW stands on" "${held}"
  if [[ "${key}" != "$(cat -- "${held}")" ]]; then
    campaign_log "$(basename "${round_dir}"): grown by \
$(campaign_exposures "${growth}" | cut -f2 | LC_ALL=C sort -u \
  | paste -sd, -) ($(campaign_exposures "${growth}" | grep -c '') \
exposure(s)), ${unpaused} doors-only occurrence(s) run \
whole; weaving generation $(basename "${generation}")"
    campaign_instrument "${iteration_dir}" \
      "${generation}/instrumented-classes" "${key}" \
      "${generation}/execution_task_plan.jsonl"
  else
    campaign_log "$(basename "${round_dir}"): grown by \
$(campaign_exposures "${growth}" | cut -f2 | LC_ALL=C sort -u \
  | paste -sd, -) ($(campaign_exposures "${growth}" | grep -c '') \
exposure(s)), ${unpaused} doors-only occurrence(s) run \
whole; generation $(basename "${generation}") weaves the tree it stands on \
(weave key ${key:0:12})"
  fi
  printf '%s\n' "${campaign_engine_outgrown}" >"${generation}/outgrown"
}

campaign_stream_grow_done() {
  local status=$1
  stream_grow_pid=""
  (( status == 0 )) || exit "${status}"
  stream_grow_returned=1
}

campaign_link_whole() {
  ln -f -- "$1" "$2.link.${BASHPID}"
  mv -f -- "$2.link.${BASHPID}" "$2"
}

campaign_stream_grow_take() {
  local round_dir=${stream_grow_round} growth=${stream_grow_growth}
  local generation="${iteration_dir}/generations/g${stream_generation}"
  local obligation_id session rerun worker file subject="" rerun_count=0
  stream_grow_returned=""
  stream_grow_round=""
  stream_grow_growth=""
  stream_hold=$((stream_hold - 1))
  campaign_stream_outgrown "${generation}/outgrown"
  campaign_link_whole "${generation}/execution_task_plan.jsonl" \
    "${round_dir}/grown_plan.jsonl"
  campaign_link_whole "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/execution_task_plan.jsonl"
  campaign_link_whole "${generation}/execution_task_plan.jsonl" \
    "${iteration_dir}/seed-replay/execution_task_plan.jsonl"
  [[ ! -f "${generation}/zk_chain.jsonl" ]] || campaign_link_whole \
    "${generation}/zk_chain.jsonl" "${iteration_dir}/zk_chain.jsonl"
  stream_plan="${generation}/execution_task_plan.jsonl"
  [[ ! -d "${generation}/instrumented-classes" ]] \
    || stream_classes="${generation}/instrumented-classes"
  while IFS=$'\t' read -r obligation_id session; do
    worker=$(campaign_obligation_worker_dir "${iteration_dir}" \
      "${obligation_id}" "${session}") || exit 1
    if [[ -e "${worker}/grow-dropped" ]]; then
      campaign_log "obligation ${obligation_id}: its re-run was dropped \
before, so it is not re-run again"
      continue
    fi
    rerun="${worker}/grow-$(basename "${round_dir}")/${obligation_id}"
    mkdir -p "$(dirname "${rerun}")"
    mkdir "${rerun}" || campaign_fail EXPLORE CAMPAIGN "${rerun}" \
      "obligation ${obligation_id} was already re-run for this round"
    for file in focused_task.jsonl schedule_prefix.jsonl.gz \
        schedule_suffix.jsonl.gz expected_edges.jsonl; do
      [[ ! -e "${worker}/${file}" ]] || ln "${worker}/${file}" "${rerun}/"
    done
    campaign_stream_enqueue "RERUN $(basename "${round_dir}") \
${obligation_id} ${session}"
    stream_reruns["${obligation_id} ${session}"]=${rerun}
    stream_hold=$((stream_hold + 1))
    rerun_count=$((rerun_count + 1))
  done < <({ campaign_exposures "${growth}"; campaign_unpauses "${growth}"; } \
    | awk -F'\t' '$1 != ""' | cut -f1,3 | LC_ALL=C sort -u)
  while IFS=$'\t' read -r obligation_id subject session; do
    [[ -z "${stream_reruns["${obligation_id} ${session}"]:-}" ]] \
      || stream_growing[${subject}]="${obligation_id} ${session}"
  done < <(jq -r "${campaign_growth_subject}"' subject as $s
      | select($s != null and (.obligationId // "") != "")
      | [.obligationId, $s, .sessionId // ""] | @tsv' "${growth}")
  (( rerun_count > 0 )) || stream_dirty=1
  (( ${#stream_chain[@]} == 0 || stream_hold > 0 )) \
    || campaign_stream_chain_reattempt
}

campaign_stream_swap_jobs=16
campaign_stream_swap() {
  local swap="" round="" id="" exposing="" status="" key="" worker=""
  local rerun="" session="" ids="" file="" verdict="" pid="" rests=""
  local entry="" kind="" changed=0 unstated="" why=""
  local -a due=() held=() withdrawing=() pids=() kept=() dropped=()
  local -A named=() swapping=() answered=() answer_session=()
  for swap in "${stream_swaps[@]}"; do
    read -r round id exposing status <<<"${swap}"
    key="${id} ${exposing}"
    rerun=${stream_reruns[${key}]}
    session=""
    why=""
    if [[ "${status}" -ne 0 ]]; then
      why="did not finish (exit ${status})"
    else
      session=$(jq -r '.sessionId // ""' "${rerun}/obligation_result.jsonl")
      verdict=$(jq -r '.verdict // ""' "${rerun}/obligation_result.jsonl")
    fi
    if [[ "${status}" -eq 0 && "${verdict}" != ADMITTED ]]; then
      why="is ${verdict}$([[ -n "${session}" ]] || printf ', no session'): \
$(jq -r '.detail // ""' "${rerun}/obligation_result.jsonl")"
    elif [[ "${status}" -eq 0 ]] && ! campaign_stream_fatal \
        "${rerun}/obligation_result.jsonl" "${rerun}/sessions/${session}"; then
      unstated=$(campaign_stream_unstated "${session}" "${exposing}") \
        || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}/import_gated" \
          "obligation ${id}: the gate's ledger states no unstated flips of \
${exposing} or of its re-run's ${session}"
      [[ -z "${unstated}" ]] || why="states no decision of a flip of its \
world that ${exposing} states ($(paste -sd ';' <<<"${unstated}"))"
    fi
    if [[ -n "${why}" ]]; then
      campaign_stream_rerun_drop "${round}" "${key}" "${session}" "${why}"
      changed=1
    elif campaign_stream_swap_due "${exposing}"; then
      due+=("${swap}")
    else
      held+=("${swap}")
    fi
  done
  stream_swaps=("${held[@]}")
  if (( ${#due[@]} > 0 )); then
    changed=1
    while IFS=$'\t' read -r file ids; do
      named[${file}]=" ${ids} "
    done < <(for swap in "${due[@]}"; do
        read -r round id exposing status <<<"${swap}"
        [[ ! -f "${sessions}/${exposing}/manifest.json" ]] \
          || printf '%s\0' "${sessions}/${exposing}/manifest.json"
      done | xargs -0 -r jq -r '[input_filename,
          ((.obligationIds // []) | map(tostring) | join(" "))] | @tsv' \
        2>/dev/null || true)
    for swap in "${due[@]}"; do
      read -r round id exposing status <<<"${swap}"
      if [[ ! -d "${sessions}/${exposing}" ]]; then
        campaign_log "obligation ${id}: no session under ${sessions} names \
it; nothing withdrawn"
        continue
      fi
      [[ "${named[${sessions}/${exposing}/manifest.json]:-}" \
          == *" ${id} "* ]] || campaign_fail EXPLORE CAMPAIGN \
        "${sessions}/${exposing}" "the exposing session ${exposing} does not \
name obligation ${id}, so it was not withdrawn from the corpus"
      withdrawing+=("${exposing}")
    done
    (( ${#withdrawing[@]} == 0 )) \
      || printf '%s\n' "${withdrawing[@]}" >>"${iteration_dir}/withdrawn.txt"
    for session in "${withdrawing[@]}"; do
      stream_withdrawn[${session}]=1
    done
    for swap in "${due[@]}"; do
      read -r round id exposing status <<<"${swap}"
      rerun=${stream_reruns["${id} ${exposing}"]}
      campaign_stream_swap_worker "${id}" "${round}" "${exposing}" \
        "$(dirname "$(dirname "${rerun}")")" "${rerun}" &
      pids+=("$!")
      swapping[$!]=${id}
      (( ${#pids[@]} < campaign_stream_swap_jobs )) || {
        for pid in "${pids[@]}"; do
          wait "${pid}" || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}" \
            "obligation ${swapping[${pid}]}: its re-run's swap failed"
        done
        pids=()
      }
    done
    for pid in "${pids[@]}"; do
      wait "${pid}" || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}" \
        "obligation ${swapping[${pid}]}: its re-run's swap failed"
    done
    while IFS=$'\t' read -r file verdict session; do
      answered[${file}]=${verdict}
      answer_session[${file}]=${session}
    done < <(for swap in "${due[@]}"; do
        read -r round id exposing status <<<"${swap}"
        rerun=${stream_reruns["${id} ${exposing}"]}
        printf '%s\0' "$(dirname "$(dirname "${rerun}")")/obligation_result.jsonl"
      done | xargs -0 -r jq -r '[input_filename, .verdict // "?",
          .sessionId // ""] | @tsv')
    for swap in "${due[@]}"; do
      read -r round id exposing status <<<"${swap}"
      printf '%s %s\n' "${id}" "${exposing}"
    done | jq -R . | jq -s -c . >"${results}.swapped"
    jq -c --slurpfile swapped "${results}.swapped" \
      '($swapped[0] | map({(.): true}) | add // {}) as $gone
       | select($gone["\(.obligationId) \(.sessionId // "")"] | not)' \
      "${results}" >"${results}.tmp"
    for swap in "${due[@]}"; do
      read -r round id exposing status <<<"${swap}"
      key="${id} ${exposing}"
      rerun=${stream_reruns[${key}]}
      worker=$(dirname "$(dirname "${rerun}")")
      [[ -n "${answered[${worker}/obligation_result.jsonl]:-}" ]] \
        || campaign_fail EXPLORE CAMPAIGN "${worker}" "obligation ${id}: its \
re-run swapped in with no answer"
      cat -- "${worker}/obligation_result.jsonl" >>"${results}.tmp"
      session=${answer_session[${worker}/obligation_result.jsonl]}
      [[ -z "${session}" \
         || -e "${iteration_dir}/import_gated/${session}.json" ]] \
        || campaign_fail EXPLORE CAMPAIGN "${rerun}" "obligation ${id}: its \
re-run's session ${session} would swap in ungated"
      [[ -z "${session}" ]] \
        || stream_staged+=("${worker} ${rerun}/sessions ${session}")
      campaign_log "obligation ${id}: re-run under the grown tree, \
verdict=${answered[${worker}/obligation_result.jsonl]}"
      campaign_stream_rerun_done "${key}"
    done
    mv -- "${results}.tmp" "${results}"
    rm -f -- "${results}.swapped"
  fi
  (( changed == 1 )) || return 0
  for entry in "${stream_queue[@]}"; do
    read -r kind round id _ <<<"${entry}"
    rests=${stream_rests[${id}]:-}
    if [[ "${kind}" == REPLAY && -n "${rests}" \
        && -n "${stream_withdrawn[${rests}]:-}" ]]; then
      dropped+=("${entry}")
    else
      kept+=("${entry}")
    fi
  done
  stream_queue=("${kept[@]}")
  for entry in "${dropped[@]}"; do
    read -r kind round id _ <<<"${entry}"
    campaign_stream_replay_drop "${entry}" "${stream_rests[${id}]}"
  done
  stream_dirty=1
  (( ${#stream_chain[@]} == 0 || stream_hold > 0 )) \
    || campaign_stream_chain_reattempt
}

campaign_stream_unstated() {
  local session=$1 exposing=$2
  jq -n -r \
    --slurpfile rerun "${iteration_dir}/import_gated/${session}.json" \
    --slurpfile before "${iteration_dir}/import_gated/${exposing}.json" \
    '($rerun[0].unstated - $before[0].unstated)[]'
}

campaign_stream_rerun_drop() {
  local round=$1 key=$2 session=$3 why=$4
  local id=${2% *} exposing=${2#* }
  printf '%s\n' "${round}" \
    >>"$(dirname "$(dirname "${stream_reruns[${key}]}")")/grow-dropped"
  [[ -z "${session}" ]] || rm -f -- \
    "${iteration_dir}/import_gated/${session}.json" \
    "${iteration_dir}/import_gated/${session}.named.json.gz"
  campaign_stream_gap DIAGNOSTIC "${id} grow-rerun-dropped=0" "its re-run \
under the grown tree${session:+, session ${session},} ${why}: dropped, \
${exposing} stays in the corpus, the regions the re-run exposed stay \
uncaptured in that world, and no flip on them is asked there"
  campaign_stream_rerun_done "${key}" dropped
}

campaign_stream_fatal() {
  [[ "$(jq -r '.verdict // ""' "$1")" == ADMITTED ]] || return 1
  campaign_rows "$2/targets.jsonl.gz" \
    | jq -e -s --argjson anchors "${stream_anchors}" \
    'any(.[]; .observedFatal == true
            and (.occurrence as $at | any($anchors[]; . == $at)))' \
    >/dev/null 2>&1
}

campaign_swap_files=(replay.log concolic_region_results.jsonl
  obligation_result.jsonl replay_verdict.jsonl question.txt question.asked
  stdout.log stderr.log host.txt replay-stdout.log replay-stderr.log
  replay-host.txt workload_rss_mb)
campaign_stream_swap_worker() {
  local id=$1 round=$2 exposing=$3 worker=$4 rerun=$5 file=""
  local aside="$4/before-$2"
  local -a present=() over=() gone=()
  mkdir -- "${aside}" || {
    printf 'obligation %s was already swapped for %s: %s\n' "${id}" \
      "${round}" "${aside}" >&2
    return 1
  }
  if [[ -d "${sessions}/${exposing}" ]]; then
    mkdir -p -- "${aside}/sessions" \
      && mv -- "${sessions}/${exposing}" "${aside}/sessions/${exposing}" \
      || return 1
    campaign_log "obligation ${id}: withdrew session ${exposing} from \
${sessions} to ${aside}/sessions/${exposing}: it exposed a region that is \
woven now, and the re-run's session stands in its place"
  fi
  for file in "${campaign_swap_files[@]}"; do
    [[ ! -e "${worker}/${file}" ]] || present+=("${worker}/${file}")
    if [[ -e "${rerun}/${file}" ]]; then
      over+=("${rerun}/${file}")
    else
      gone+=("${worker}/${file}")
    fi
  done
  (( ${#present[@]} == 0 )) || cp -p -- "${present[@]}" "${aside}/" \
    || return 1
  (( ${#over[@]} == 0 )) || mv -f -t "${worker}" -- "${over[@]}" || return 1
  (( ${#gone[@]} == 0 )) || rm -f -- "${gone[@]}"
}

campaign_stream_rerun_done() {
  local key=$1 dropped=${2:-} subject=""
  if [[ -n "${dropped}" ]]; then
    stream_uncaptured+=("${key#* }")
    for subject in "${!stream_growing[@]}"; do
      [[ "${stream_growing[${subject}]}" != "${key}" ]] \
        || unset 'stream_growing[$subject]'
    done
  fi
  unset 'stream_reruns[$key]'
  stream_hold=$((stream_hold - 1))
}

campaign_stream_replay_drop() {
  local entry=$1 session=$2 kind="" round="" id=""
  read -r kind round id _ <<<"${entry}"
  unset 'stream_queued_at[$entry]' 'stream_rests[$id]' 'stream_flying[$id]'
  stream_reaped+=("${id}")
  mkdir -p "${campaign_root}/explore-reaped/${round}"
  mv -- "${iteration_dir}/${round}/${id}" \
    "${campaign_root}/explore-reaped/${round}/${id}"
  campaign_log "obligation ${id}: its replay is dropped before it \
started: its path rests on ${session}, which GROW's swap withdrew"
}

campaign_obligation_worker_dir() {
  local iteration_dir=$1 obligation_id=$2 session=$3 worker="" found=""
  for worker in "${iteration_dir}"/obligations-*/"${obligation_id}"; do
    [[ -n "${session}" && -s "${worker}/focused_task.jsonl" \
        && "$(jq -r '.sessionId // ""' "${worker}/obligation_result.jsonl" \
          2>/dev/null)" == "${session}" ]] || continue
    [[ -z "${found}" ]] || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}" \
      "two workers of obligation ${obligation_id} name session ${session}: \
${found} ${worker}"
    found=${worker}
  done
  [[ -n "${found}" ]] || campaign_fail EXPLORE CAMPAIGN "${iteration_dir}" \
    "no worker of the exposing obligation ${obligation_id} with a focus row \
landed session ${session:-(none)}"
  printf '%s\n' "${found}"
}

campaign_stream_promote_generation() {
  local generation
  (( stream_generation > 0 )) || return 0
  [[ "${stream_classes}" != "${iteration_dir}/instrumented-classes" ]] \
    || return 0
  rm -rf -- "${iteration_dir}/instrumented-classes"
  mv -- "${stream_classes}" "${iteration_dir}/instrumented-classes"
  mv -f -- "$(dirname "${stream_classes}")/weave_key" \
    "${iteration_dir}/weave_key"
  for generation in "${iteration_dir}"/generations/g*; do
    rm -rf -- "${generation}/instrumented-classes"
  done
}

campaign_stream_manifest() {
  local lists="${iteration_dir}/.exploration-lists"
  mkdir -p "${lists}"
  campaign_json_strings "${lists}/cancelled.json" "${stream_cancelled[@]}"
  campaign_json_strings "${lists}/reaped.json" "${stream_reaped[@]}"
  campaign_json_strings "${lists}/afterWitness.json" \
    "${stream_after_witness[@]}"
  campaign_json_strings "${lists}/rerunsDropped.json" \
    "${stream_reruns_dropped[@]}"
  campaign_json_strings "${lists}/confirmsReaped.json" \
    "${stream_confirms_reaped[@]}"
  campaign_json_strings "${lists}/duplicateWorlds.json" \
    "${stream_duplicates[@]}"
  jq -n \
    --arg stop "${stream_stop}" --arg detail "${stream_stop_detail}" \
    --argjson rounds "${stream_round}" --argjson steps "${stream_steps}" \
    --argjson generations "${stream_generation}" \
    --argjson answered "$(grep -c '' "${results}" || true)" \
    --slurpfile cancelled "${lists}/cancelled.json" \
    --slurpfile reaped "${lists}/reaped.json" \
    --slurpfile afterWitness "${lists}/afterWitness.json" \
    --slurpfile rerunsDropped "${lists}/rerunsDropped.json" \
    --slurpfile confirmsReaped "${lists}/confirmsReaped.json" \
    --slurpfile duplicateWorlds "${lists}/duplicateWorlds.json" \
    --argjson roundDue "${stream_round_due}" \
    --arg roundDropped "${stream_round_dropped}" \
    --slurpfile attempts "${attempts}" \
    '{schemaVersion: 1, kind: "EXPLORATION", stop: $stop, detail: $detail,
      rounds: $rounds, steps: $steps, generations: $generations,
      answered: $answered,
      witnessAttempts: ($attempts | sort_by(.attempt)),
      cancelled: $cancelled[0], reaped: $reaped[0],
      rerunsDropped: $rerunsDropped[0],
      confirmsReaped: $confirmsReaped[0],
      duplicateWorlds: $duplicateWorlds[0], roundDue: $roundDue,
      roundDropped: (if $roundDropped == "" then null else $roundDropped end),
      afterWitness: $afterWitness[0]}' \
    >"${iteration_dir}/exploration.json"
  rm -rf -- "${lists}"
}

campaign_bounds() {
  local iteration_dir=$1 decided unconfirmed=false
  decided=$(find "${campaign_final}/refuted" -mindepth 1 -maxdepth 1 \
    2>/dev/null | grep -c '' || true)
  [[ ! -s "${campaign_final}/confirm.json" ]] \
    || unconfirmed=$(jq '.confirmed != true' "${campaign_final}/confirm.json")
  jq -n -c \
    --slurpfile exploration <(cat "${iteration_dir}/exploration.json" \
      2>/dev/null) \
    --slurpfile index <(cat \
      "${iteration_dir}/runtime_workflow_schedule_index.json" 2>/dev/null) \
    --slurpfile rounds <(cat "${iteration_dir}"/obligations-*/\
explore_manifest.json 2>/dev/null) \
    --slurpfile gaps "${iteration_dir}/emit_gaps.json" \
    --slurpfile last <(campaign_rows "$(printf '%s\n' \
      "${iteration_dir}"/obligations-* | LC_ALL=C sort | tail -n 1)/\
gaps.jsonl.gz") \
    --slurpfile inputs <(campaign_rows "${iteration_dir}"/obligations-*/\
gaps.jsonl.gz | grep -F 'unplanned-input-max=' || true) \
    --slurpfile confirmHolds <(campaign_rows \
      "$(dirname "${iteration_dir}")"/witness-confirm/*/sessions/*/gaps.jsonl.gz \
      "${campaign_final}"/confirm/sessions/*/gaps.jsonl.gz \
      | grep -F ' view-hold-max=' || true) \
    --argjson decided "${decided}" --argjson unconfirmed "${unconfirmed}" \
    --argjson maxClaims "${campaign_max_claims}" '
    def bound($bound): select(.subject | test(" " + $bound + "=[0-9]+$"));
    def rows($bound): [$gaps[0].telemetryGaps[]?, $gaps[0].gaps[]?
      | bound($bound)];
    [$last[] | bound("max-paths-per-region")] as $paths
    | ([$inputs[] | bound("unplanned-input-max") | .subject] | unique)
      as $inputs
    | rows("max-world-depth") as $depth
    | rows("pairing-bound") as $pairing
    | rows("loop-body-bound") as $loops
    | rows("daemon-tick-bound") as $ticks
    | rows("ordered-map-unmodeled") as $sorted
    | rows("grow-rerun-dropped") as $dropped
    | (rows("view-hold-max") + [$confirmHolds[] | bound("view-hold-max")])
      as $holds
    | ($rounds | last | .ceilingCut // 0) as $ceiling
    | (($rounds | last | .truncated // 0) - $ceiling) as $truncated
    | ($index[0].closureCut // null) as $cut
    | [($rounds | last | .openArms // [])[] | select(.state == "BOUNDED")]
      as $armsBounded
    | ($rounds | last | .boundedFlips // []) as $killed
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
        (select(($pairing | length) > 0)
         | {by: "pairing_flip_per_read",
            detail: ("\($pairing | length) read(s) of a node'"'"'s view offered"
              + " only the \($pairing[0].subject | sub(".*="; "")) newest of"
              + " the older decodes before it")}),
        (select(($loops | length) > 0)
         | {by: "loop_body_bound",
            detail: ("\($loops | length) path(s) at the anchor a loop"
              + " bound cut before they reached it, before or after they"
              + " left the way to the throw (bodies: " + ($loops | map(.subject
              | sub(".*="; "")) | unique | join(", ")) + ")")}),
        (select(($ticks | length) > 0)
         | {by: "daemon_tick_bound",
            detail: ("\($ticks | map(.subject) | unique | length)"
              + " producer(s) begun by a daemon tick past the recording'"'"'s"
              + " last: the store content leaves they wrote are held at their"
              + " versions'"'"' values, or an arm handed their message is"
              + " refused (" + ($ticks
              | map(.subject | sub(" daemon-tick-bound=.*"; "")) | unique
              | join(", ")) + ")")}),
        (select(($sorted | length) > 0)
         | {by: "ordered_map_unmodeled",
            detail: ("\($sorted | map(.subject) | unique | length) site(s)"
              + " held a sorted container no VM model knows (TreeMap,"
              + " ConcurrentSkipList*, TreeSet or a view or wrapper of one):"
              + " its state is unversioned and its queries decided on the"
              + " run'"'"'s contents (" + ($sorted
              | map(.subject | sub(" ordered-map-unmodeled=.*"; "")) | unique
              | join(", ")) + ")")}),
        (select(($dropped | length) > 0)
         | {by: "grow_rerun_dropped",
            detail: ("\($dropped | length) GROW re-run(s) dropped, their"
              + " exposing session kept (one that did not finish, published"
              + " no session, or stated no decision of a flip of its world"
              + " its exposing session states): the regions they exposed"
              + " stay uncaptured in those worlds and no flip on them is"
              + " asked there (" + ($dropped | map(.subject
              | sub(" grow-rerun-dropped=.*"; "")) | unique | join(", "))
              + ")")}),
        (select(($holds | length) > 0)
         | {by: "view_hold_max",
            detail: ("\($holds | length) pairing hold(s) of a node'"'"'s view"
              + " gave way past VIEW_HOLD_MAX (" + ($holds[0].subject
              | sub(".*="; "")) + " ms of recorded time): their reader had"
              + " not read")}),
        (select(($inputs | length) > 0)
         | {by: "unplanned_input_max",
            detail: ("\($inputs | length) marker invocation(s) past the"
              + " \($inputs[0] | sub(".*="; "")) of one occurrence GROW"
              + " plans inputs for stayed concrete, in any round")}),
        (select($truncated > 0)
         | {by: "region_path_max_tasks",
            detail: ("the last round planned its closure without"
              + " \($truncated) static candidate(s), at the task bound")}),
        (select($ceiling > 0)
         | {by: "region_path_closure_ceiling",
            detail: ("the last round planned its closure without"
              + " \($ceiling) occurrence(s) the rows connect, past the"
              + " closure ceiling")}),
        (select(($armsBounded | length) > 0)
         | {by: "open_arm_max_refuted_worlds",
            detail: ("\($armsBounded | length) open decider arm(s) asked no"
              + " more past their refuted worlds: " + ($armsBounded
              | map("\(.siteId)=\(.outcome) of \(.anchor)") | join(", ")))}),
        (select(($killed | length) > 0)
         | {by: "replay_timeout_s",
            detail: ("\($killed | length) flip(s) whose replays were killed"
              + " twice (past replay_timeout_s, or inside it by their memory"
              + " reservation) answered nothing, held open: "
              + ($killed | map(if .force then "FORCE" else "\(.siteId
                | sub("^<(?:[^:]*\\.)?(?<c>[^.:]+): [^ ]+ (?<m>[^(]+)\\(.*>(?<u>#u[0-9]+)$";
                  "\(.c).\(.m)\(.u)"))#\(.ordinal)=\(.outcome)" end)
              | group_by(.) | map(if length > 1 then "\(.[0]) x\(length)"
                else .[0] end) | join(", ")))}),
        (select($cut != null)
         | {by: "schedule_max_jobs",
            detail: ("PLAN planned the closure only to demand depth"
              + " \($cut.keptDepth): \($cut.occurrences) deeper"
              + " occurrence(s) not planned")}),
        (select($unconfirmed and $decided >= $maxClaims)
         | {by: "campaign_max_claims",
            detail: ("the claim was decided again \($decided) time(s) and"
              + " the unconfirmed claim is published")}) ]
    | if length == 0 then null
      else {by: map(.by), detail: (map(.detail) | join("; "))} end'
}

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
         + " path(s): no run took the arm, so no UNSAT closes over it"
         + (if ((.refused // []) | length) > 0
            then "; its query was refused at the arm: \(.refused | join("; "))"
            else "" end))}' \
    "${last}" >>"${iteration_dir}/campaign_gaps.jsonl"
}

campaign_solver_timeouts() {
  local iteration_dir=$1 claim
  [[ -s "${iteration_dir}/solver_timeouts.jsonl" ]] || return 0
  claim=$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}")
  jq -c --arg claim "${claim}" --arg epoch "$(basename "${iteration_dir}")" '
    {schemaVersion: 1, sessionId: "", stage: "EXPLORE",
     kind: "ADMISSION_GAP",
     cls: (if $claim == "SAT_CANDIDATE" then "DIAGNOSTIC" else "BLOCKING" end),
     subject: (if (.detail // "") | startswith("SOLVER_MEMOUT")
       then "SOLVER_MEMOUT" else "SOLVER_TIMEOUT" end),
     topologyEpoch: $epoch,
     detail: ("obligation \(.obligationId) on \(.host): \(.detail), in the"
       + " hard lane after the first ask; its arm has no verdict, so no UNSAT"
       + " closes over it")}' \
    "${iteration_dir}/solver_timeouts.jsonl" \
    >>"${iteration_dir}/campaign_gaps.jsonl"
}


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
    if ! find "${worker}" -mindepth 2 -maxdepth 2 \
        -type d -path '*/obligations-*/*' -printf '%f\n' \
        | LC_ALL=C sort \
        | jq -R -s -c --arg role "${role}" --arg campaign "${campaign_id}" \
          --arg region "${region}" --arg occurrence "${occurrence}" \
          --arg goal "${goal}" --arg task "${task}" --arg dir "${worker}" \
          '{role: $role, campaignId: $campaign, regionId: $region,
            occurrenceId: $occurrence, goalId: $goal, taskId: $task,
            workerDir: $dir,
            obligationDigests: (split("\n") | map(select(length > 0)))}' \
          >>"${members}"; then
      campaign_fail EMIT CAMPAIGN "${worker}" \
        "failed to enumerate path obligation digests"
    fi
  done <<<"${campaign_member_rows}"
  if ! plan_sha=$(campaign_digest "${plan}"); then
    campaign_fail EMIT CAMPAIGN "${plan}" \
      "failed to digest the active observed execution task plan"
  fi
  if ! index_sha=$(campaign_digest "${index}"); then
    campaign_fail EMIT CAMPAIGN "${index}" \
      "failed to digest the frozen schedule index"
  fi
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


campaign_compose() {
  local iteration_dir=$1
  local started ended millis status=0
  local compose_reuse_dir=${campaign_witness_attempt}
  local campaign_compose_final=1
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
  campaign_await_visible "${composed_smt}" "${composition_manifest}"
  require_nonempty "candidate SMT" "${composed_smt}"
  require_nonempty "candidate composition manifest" "${composition_manifest}"
  campaign_compose_bounded "${iteration_dir}" "${composition_manifest}"
  printf '%s\t%s\n' "COMPOSE[anchor]" "${millis}" \
    >>"${campaign_stage_metrics}"
  campaign_log "composed $(jq -r '.anchor // ""' "${composition_manifest}") \
in ${millis}ms status=$(jq -r '.finalStatus // ""' "${composition_manifest}")"
}



campaign_compose_bounded() {
  local iteration_dir=$1 manifest=$2 bounded composed
  bounded=$(jq '[.solver.campaignClaim.refusedPaths[]?
    | select(.reason | startswith("ADMISSION_GAP COMPOSE_HEAP_BOUND:"))]
    | length' "${manifest}") || bounded=0
  (( bounded > 0 )) || return 0
  ! grep -q '"subject":"COMPOSE_HEAP_BOUND"' \
    "${iteration_dir}/campaign_gaps.jsonl" 2>/dev/null || return 0
  composed=$(jq '.paths | length' "${manifest}") || composed=0
  jq -n -c --arg epoch "${iteration_id}" --arg detail "COMPOSE left \
${bounded} admitted path(s) out past its heap bound (its old generation past \
its share after a sweep, compose.Composer#HEAP_SHARE): the claim is over the \
${composed} composed, so it misses their arms" \
    '{schemaVersion: 1, sessionId: "", stage: "COMPOSE",
      kind: "ADMISSION_GAP", cls: "BLOCKING", subject: "COMPOSE_HEAP_BOUND",
      detail: $detail, topologyEpoch: $epoch}' \
    >>"${iteration_dir}/campaign_gaps.jsonl"
  campaign_log "compose: COMPOSE_HEAP_BOUND: ${bounded} path(s) left out"
}

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

campaign_confirm_claim() {
  local iteration_dir=$1 claims=$2 dir=$3 need charge status=0 runs heap
  local refused full="" why
  campaign_confirm_plan "${iteration_dir}" "${claims}" "${dir}"
  if [[ ! -s "${claims}/confirm.json" ]]; then
    for runs in 1 2; do
      status=0
      need=$(campaign_replay_basis_mb)
      charge=$(campaign_replay_charge_mb "$(campaign_replay_need_mb)")
      if [[ -n "${full}" ]]; then
        charge=${full}
        (( need >= full )) || need=${full}
      fi
      ( campaign_head_charged "${charge}" campaign_confirm_replay "${dir}" \
          "${iteration_dir}/instrumented-classes" \
          "${iteration_dir}/seed-replay/execution_task_plan.jsonl" \
          "${charge}" "${need}" ) || status=$?
      campaign_replay_measured "${dir}/worker"
      [[ -s "${dir}/worker/replay_again" ]] || break
      read -r refused _ _ heap <"${dir}/worker/replay_again"
      rm -f -- "${dir}/worker/replay_again"
      [[ "${refused}" =~ ^[0-9]+$ ]] || refused=0
      [[ "${heap}" =~ ^[0-9]+$ ]] || heap=""
      if [[ -n "${heap}" ]]; then
        why="ran out of its ${heap} MB heap"
        (( runs == 1 )) && campaign_replay_heap_raised "${heap}" CONFIRM \
          && continue
      else
        why="was ended at ${refused} MB as its host could not take its growth"
        full=$(campaign_replay_full_need_mb "${refused}")
        (( runs == 1 && full > refused )) && continue
      fi
      campaign_replay_bounded CONFIRM "${dir}/worker" "${dir}/sessions" \
        "the confirmation replay ${why}, the $( (( runs == 1 )) \
          && echo "most a replay is given" || echo "second time")"
      break
    done
    campaign_confirm_decide "${claims}" "${dir}" "${status}"
  fi
  campaign_confirm_settle "${iteration_dir}" "${claims}"
}

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

campaign_confirm_replay() {
  local dir=$1 classes=$2 plan=$3 charged=$4 need=$5
  campaign_obligation_replay CONFIRM "${classes}" "${dir}/worker" \
    "${dir}/sessions" "${plan}" "${charged}" "${need}" \
    >>"${dir}/confirm.log" 2>&1
}

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

campaign_confirm_settle() {
  local iteration_dir=$1 claims=$2 outcome=undecided
  require_nonempty "confirmation" "${claims}/confirm.json"
  [[ "$(jq -r '.confirmed' "${claims}/confirm.json")" != true ]] || return 0
  [[ "$(jq -r '.refutes' "${claims}/confirm.json")" != true ]] \
    || outcome=refuted
  campaign_refute "${iteration_dir}" "${claims}" "${outcome}"
}

campaign_model_key='def key: .arms |= ((. // []) | map(sub("__[0-9]+__"; "__")));'

campaign_claim_model() {
  jq -c --slurpfile manifest "${1%/*}/candidate_composition_manifest.json" '
    def ordinal: (capture("^.*?__(?<o>[0-9]+)__") | .o) // "";
    .claim as $c | $c.valuationOrdinal as $o | (.valuations // [])[]
    | select(.ordinal == $o) | .selectedPathId as $p
    | ([($manifest[0].paths // [])[] | select(.pathId == $p)
        | .selector | ordinal] | first // "") as $at
    | {findingKind: $c.kind, pathId: $p,
      arms: ([(.selectedArms // [])[].selector
        | select($at == "" or ordinal == $at)] | sort),
      assignment: (.assignment // {}), moved: ($c.movedRoots // {})}' "$1"
}

campaign_refute() {
  local iteration_dir=$1 claims=$2 outcome=$3
  campaign_claim_model "${claims}/claim.json" \
    | jq -c --slurpfile confirmation "${claims}/confirm.json" \
      --arg claimed "${claims}" --arg outcome "${outcome}" \
      '{schemaVersion: 1, kind: "REFUTED_CLAIM", model: ., claimed: $claimed,
        outcome: $outcome, reason: $confirmation[0].reason}' \
    >>"${iteration_dir}/refuted_claims.jsonl"
  campaign_log "COMPOSE SAT -> CONFIRM ${outcome}: $(jq -r '.reason' \
"${claims}/confirm.json") -> excluded"
}

campaign_claim_room() {
  (( campaign_budget_s - (SECONDS - campaign_started_s) \
    >= $(campaign_reserve) ))
}

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
  measured=$(( measured + 2 * $(campaign_reproduce_bound) ))
  echo $(( measured > campaign_reserve_s ? measured : campaign_reserve_s ))
}

campaign_reproduce_bound() {
  local bound=$(( reproduce_time_factor * ${campaign_recorded_workload_s:-0} ))
  echo $(( bound > reproduce_min_s ? bound : reproduce_min_s ))
}

campaign_last_round_millis() {
  local manifest started ended last=""
  for manifest in "${campaign_root}"/iteration-0000/obligations-[0-9]*/explore_manifest.json; do
    started=$(stat -c %Y "${manifest%/*}/in_flight.jsonl" 2>/dev/null) \
      && ended=$(stat -c %Y "${manifest}" 2>/dev/null) \
      && last="PLANNER $(( (ended - started) * 1000 ))"
  done
  [[ -z "${last}" ]] || echo "${last}"
}

campaign_claim_artifacts=(candidate.smt2 candidate_composition_manifest.json
  claim.json compose_inputs.sha256 compose.log confirm confirm.json reproduce
  reproduce.json)

campaign_claims_decided() {
  local kind count total=0
  for kind in refuted unreproduced; do
    count=$(find "${campaign_final}/${kind}" -mindepth 1 -maxdepth 1 \
      2>/dev/null | grep -c '' || true)
    total=$(( total + count ))
  done
  echo "${total}"
}

campaign_move_claim() {
  local into=$1 name
  mkdir -p "${into}"
  for name in "${campaign_claim_artifacts[@]}"; do
    [[ ! -e "${campaign_final}/${name}" ]] \
      || mv -- "${campaign_final}/${name}" "${into}/"
  done
}

campaign_next_claim() {
  local iteration_dir=$1 dir model seen=0 decided refuted
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
  decided=$(campaign_claims_decided)
  if (( decided >= campaign_max_claims )); then
    campaign_log "the claim was decided again ${decided} time(s), the bound \
(campaign_max_claims=${campaign_max_claims}): the last claim is published"
    return 1
  fi
  refuted=$(find "${campaign_final}/refuted" -mindepth 1 -maxdepth 1 \
    2>/dev/null | grep -c '' || true)
  dir=$(printf '%s/refuted/%04d' "${campaign_final}" "${refuted}")
  campaign_move_claim "${dir}"
  campaign_log "the claim was excluded (${dir}): composing the next one"
}

campaign_unreproduced() {
  local iteration_dir=$1 reproduce="${campaign_final}/reproduce.json"
  local runs kept decided dir model
  [[ "$(jq -r '.solver.campaignClaim.claim' "${composition_manifest}")" \
      == SAT_CANDIDATE && -s "${campaign_final}/confirm.json" \
    && "$(jq -r '.confirmed' "${campaign_final}/confirm.json")" == true \
    && -s "${reproduce}" ]] || return 1
  runs=$(jq -r '.runs // 0' "${reproduce}")
  [[ "${runs}" =~ ^[0-9]+$ ]] || runs=0
  (( runs > 0 )) \
    && [[ "$(jq -r '.reproduced // 0' "${reproduce}")" == 0 ]] || return 1
  if ! campaign_claim_room; then
    campaign_log "the confirmed claim reproduced in 0 of ${runs} native \
run(s), and the campaign budget (campaign_budget_s=${campaign_budget_s}) has \
no room for another claim"
    return 1
  fi
  decided=$(campaign_claims_decided)
  if (( decided >= campaign_max_claims )); then
    campaign_log "the confirmed claim reproduced in 0 of ${runs} native \
run(s), and ${decided} claim(s) were decided, the bound \
(campaign_max_claims=${campaign_max_claims})"
    return 1
  fi
  kept=$(find "${campaign_final}/unreproduced" -mindepth 1 -maxdepth 1 \
    2>/dev/null | grep -c '' || true)
  dir=$(printf '%s/unreproduced/%04d' "${campaign_final}" "${kept}")
  model=$(campaign_claim_model "${campaign_final}/claim.json")
  [[ -n "${model}" ]] || return 1
  jq -n -c --argjson model "${model}" --arg claimed "${dir}" \
    --arg reason "confirmed in the VM, reproduced in 0 of ${runs} native \
run(s): kept as a fallback verdict and excluded, so the next claim is tried" \
    '{schemaVersion: 1, kind: "REFUTED_CLAIM", model: $model,
      claimed: $claimed, outcome: "unreproduced", reason: $reason}' \
    >>"${iteration_dir}/refuted_claims.jsonl"
  campaign_move_claim "${dir}"
  campaign_log "the confirmed claim reproduced in 0 of ${runs} native \
run(s): kept $( (( kept == 0 )) && echo "as the fallback verdict" \
    || echo "beside the fallback") (${dir}) and excluded: composing the next \
one"
}

campaign_fallback() {
  local fallback="${campaign_final}/unreproduced/0000" stood=true
  local superseded="" reason
  [[ -d "${fallback}" ]] || return 0
  if [[ "$(jq -r '.solver.campaignClaim.claim // ""' "${composition_manifest}" \
        2>/dev/null)" == SAT_CANDIDATE \
      && "$(jq -r '.confirmed' "${campaign_final}/confirm.json" 2>/dev/null)" \
        == true \
      && "$(jq -r '.reproduced // 0' "${campaign_final}/reproduce.json" \
        2>/dev/null)" =~ ^[1-9][0-9]*$ ]]; then
    stood=false
    reason="a later claim reproduced natively: it is the verdict, and the \
fallback stays beside it"
  else
    superseded="${campaign_final}/superseded"
    campaign_move_claim "${superseded}"
    cp -r -- "${fallback}"/. "${campaign_final}/"
    reason="no later claim reproduced natively: the first confirmed claim \
stands, reproduced in 0 of $(jq -r '.runs' "${campaign_final}/reproduce.json") \
native run(s); what the loop ended on is ${superseded}"
  fi
  jq -n --arg fallback "${fallback}" --argjson stood "${stood}" \
    --arg superseded "${superseded}" --arg reason "${reason}" \
    '{schemaVersion: 1, kind: "FALLBACK", fallback: $fallback, stood: $stood,
      superseded: $superseded, reason: $reason}' \
    >"${campaign_final}/fallback.json"
  campaign_log "fallback: ${reason}"
}

campaign_reproduce() {
  local iteration_dir=$1
  local dir="${campaign_final}/reproduce" status=0 bound run reason="" pid
  local charge
  local confirmed
  local control="" checked=0 turn_orders=0 implied_orders=0
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
      unheldLate: 0, unheldMissing: 0, holding: 0, checked: 0,
      checkedObserved: 0, turnOrders: 0, impliedOrders: 0, reason: $reason,
      control: {runs: 0, fatal: 0, atAnchor: 0, reason: ""}}' \
      >"${campaign_final}/reproduce.json"
    campaign_log "reproduce: ${reason}"
    return 0
  fi
  jq -c 'select(.kind == "TARGET")' "${dir}/plant.jsonl" \
    >"${dir}/control.jsonl"
  bound=$(campaign_reproduce_bound)
  charge=$(( campaign_recorded_workload_rss_mb * reproduce_charge_pct / 100 ))
  campaign_log "reproduce: ${reproduce_runs} native run(s) at once, then \
${reproduce_runs} control run(s) behind them, each \
charged ${charge} MB (reproduce_charge_pct=${reproduce_charge_pct} of the \
recording's ${campaign_recorded_workload_rss_mb} MB peak) and bounded by \
${bound}s (reproduce_time_factor=${reproduce_time_factor} x the recording's \
${campaign_recorded_workload_s}s, at least reproduce_min_s=${reproduce_min_s})"
  for ((run = 0; run < reproduce_runs; run++)); do
    campaign_reproduce_one "${dir}/run-$((run + 1))" "${bound}" \
      "${dir}/plant.jsonl" "${charge}" false &
    pids+=("$!")
  done
  for ((run = 0; run < reproduce_runs; run++)); do
    while [[ ! -e "${dir}/run-$((run + 1))/host.txt" ]] \
        && kill -0 "${pids[run]}" 2>/dev/null; do
      sleep "${campaign_host_poll_s}"
    done
  done
  for ((run = 0; run < reproduce_runs; run++)); do
    campaign_reproduce_one "${dir}/control/run-$((run + 1))" "${bound}" \
      "${dir}/control.jsonl" "${charge}" true &
    pids+=("$!")
  done
  for pid in "${pids[@]}"; do
    wait "${pid}" || true
  done
  control=$(find "${dir}/control" -mindepth 2 -maxdepth 2 -name answer.json \
      -print0 | xargs -0 -r cat \
    | jq -s -c --argjson runs "${reproduce_runs}" '{runs: $runs,
        fatal: map(select(.fatal)) | length,
        atAnchor: map(select(.atAnchor)) | length,
        reason: (if length < $runs
          then "\($runs - length) of \($runs) run(s) stated no answer"
          else "" end)}')
  checked=$(jq -s '[.[] | select(.kind == "ORDER" and .check == true)]
    | length' "${dir}/plant.jsonl")
  turn_orders=$(grep -c '^REPRODUCE leaves out ORDER ' "${dir}/plant.log" \
    || true)
  implied_orders=$(grep -c '^REPRODUCE leaves out implied ORDER ' \
    "${dir}/plant.log" || true)
  find "${dir}" -mindepth 2 -maxdepth 2 -name answer.json -print0 \
    | xargs -0 -r cat \
    | jq -s --argjson runs "${reproduce_runs}" --argjson control "${control}" \
      --argjson checked "${checked}" --argjson turns "${turn_orders:-0}" \
      --argjson implied "${implied_orders:-0}" '
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
       checked: $checked,
       checkedObserved: map(select($checked > 0
         and .ordersObserved == $checked)) | length,
       turnOrders: $turns, impliedOrders: $implied,
       reason: (if length < $runs
         then "\($runs - length) of \($runs) run(s) stated no answer"
         else "" end),
       control: $control}' >"${campaign_final}/reproduce.json"
  jq -r '"  reproduced in \(.reproduced) of \(.runs) native run(s): the fatal at the anchor with every root planted and every order held (\(.planted) applied the whole plant, \(.fatal) fatal, \(.atAnchor) at the anchor, \(.unheld) an order unheld -- \(.unheldLate) one that came late, \(.unheldMissing) one that never came --, \(.holding) an order still holding; \(.checked) order(s) checked, not held, observed in order in \(.checkedObserved) run(s); \(.turnOrders) order(s) of turn-counted roots and \(.impliedOrders) order(s) implied by the replies one client thread received not planted, plant.log names them); control \(.control.atAnchor) of \(.control.runs): the fatal at the anchor with nothing the model chose planted (\(.control.fatal) fatal)"' \
    "${campaign_final}/reproduce.json"
}

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

campaign_reproduce_one() {
  local run=$1 bound=$2 plant=$3 charge=$4 control=$5
  mkdir -p "${run}"
  campaign_head_charged "${charge}" \
    campaign_reproduce_run "${analysis_classes_dir}" \
    "${run}" "${bound}" "${plant}" "${charge}" "${control}" \
    || campaign_log "reproduce: $(basename "${run}") exited nonzero; its \
logs are in ${run}"
  campaign_host_is_local "${campaign_placed_host}" \
    || campaign_await_visible "${run}/answer.json"
}

campaign_reproduce_run() {
  local analysis_classes_dir=$1 run=$2 bound=$3 plant=$4 charged=$5
  local control=$6 status=0
  local trace="${run}/runtime_trace.jsonl"
  hostname -s >"${run}/host.txt"
  run_capturing_status run_configured_workload "${run}" "${bound}" "${plant}" \
    "${charged}" "" "$(( bound * 500 ))" \
    >"${run}/stdout.log" 2>"${run}/stderr.log"
  [[ -s "${trace}" ]] || trace=/dev/null
  jq -n -c -R --argjson exit "${status}" --slurpfile plant "${plant}" \
    --argjson control "${control}" '
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
      (stated("PLANT_APPLIED") + stated("PLANT_OBSERVED")) as $applied
    | [$planted[] | . as $p | select((any($applied[]; . == $p.row) | not)
        or any(stated("PLANT_UNWRITTEN")[]; . == $p.row))
        | {row, kind, planted: (.rootId // .endpoint // ends),
           checked: (.check == true), why: why($p.row)}] as $unapplied
    | [$planted[] | select(.check == true)] as $checks
    | ($planted | length) as $count
    | any($rows[]; .event == "PLANT_FATAL" and .atAnchor) as $atAnchor
    | (all($unapplied[]; .kind == "ORDER")) as $roots
    | (any($unapplied[]; .why == "LATE" or .why == "MISSING") | not)
      as $held
    | {exit: $exit, rows: $count, applied: ($count - ($unapplied | length)),
       unapplied: $unapplied,
       planted: ($count > 0 and ($unapplied | length) == 0),
       rootsPlanted: $roots, ordersHeld: $held,
       ordersChecked: ($checks | length),
       ordersObserved: [$checks[] | . as $c
         | select(any(stated("PLANT_OBSERVED")[]; . == $c.row))] | length,
       fatal: any($rows[]; .event == "PLANT_FATAL"),
       atAnchor: $atAnchor, control: $control,
       reproduced: (($control | not) and $atAnchor and $roots and $held)}' \
    "${trace}" >"${run}/answer.json.part"
  mv -f -- "${run}/answer.json.part" "${run}/answer.json"
}

campaign_confirm_verdict() {
  local confirmed=$1 reason=$2 session_id=$3 refutes=$4
  jq -n --argjson confirmed "${confirmed}" --arg reason "${reason}" \
    --arg sessionId "${session_id}" --argjson refutes "${refutes}" \
    '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: $confirmed,
      refutes: $refutes, reason: $reason, sessionId: $sessionId}'
}

campaign_artifact_digests() {
  local gaps_read=$1 name path bytes sha row
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
    if [[ "${name}" == gaps.json ]]; then
      sha=$(jq -r --argjson bytes "${bytes}" \
        'select(.published.bytes == $bytes) | .published.sha256' \
        "${gaps_read}") || return 1
      [[ "${sha}" =~ ^[0-9a-f]{64}$ ]] || {
        echo "the gaps EMIT reads state no digest of ${path} as it is" >&2
        return 1
      }
    elif ! sha=$(campaign_digest "${path}"); then return 1; fi
    if ! row=$(jq -n -c --arg name "${name}" --arg path "${path}" \
        --argjson bytes "${bytes}" --arg sha256 "${sha}" \
        '{name: $name, path: $path, bytes: $bytes, sha256: $sha256}'); then
      return 1
    fi
    rows+=("${row}")
  done
  printf '%s\n' "${rows[@]}" | jq -c -s .
}

campaign_json_file() {
  local destination=$1 content=$2
  printf '%s\n' "${content}" >"${destination}" || return 1
  printf '%s' "${destination}"
}

campaign_write_gaps() {
  local composition=$1 iteration_dir=$2 output=$3 read=$4
  local statics="${causynth_output_dir}/communication_gaps.jsonl.gz"
  require_nonempty "static communication gaps" "${statics}"
  require_nonempty "runtime region plan" "${runtime_region_plan}"
  run_java_main edu.uva.liftlab.graphchecker.contract.GapLedgerMain \
    --iteration "${iteration_dir}" --composition "${composition}" \
    --static "${statics}" --plan "${runtime_region_plan}" \
    --provenance "${campaign_provenance}" --out "${output}" --read "${read}"
}

campaign_emit() {
  local iteration_dir=$1
  local session_rows session_bytes gapCount
  local artifacts_json stages_json iterations_json
  campaign_verify_frozen_inputs

  campaign_require_json "candidate composition manifest" \
    "${composition_manifest}" || campaign_fail EMIT ComposeMain \
      "${composition_manifest}" "required composition JSON is malformed"
  require_nonempty "replay session census" \
    "${iteration_dir}/session_census.jsonl"

  campaign_exploration_cut "${iteration_dir}"
  campaign_open_arms "${iteration_dir}"
  campaign_solver_timeouts "${iteration_dir}"
  local gaps_read="${iteration_dir}/emit_gaps.json"
  campaign_write_gaps "${composition_manifest}" "${iteration_dir}" \
    "${campaign_final}/gaps.json" "${gaps_read}" \
    || campaign_fail EMIT GapLedgerMain "${campaign_final}/gaps.json" \
      "the gap ledger could not be written"
  require_nonempty "campaign gaps" "${campaign_final}/gaps.json"
  campaign_require_json "the gaps EMIT reads" "${gaps_read}" \
    || campaign_fail EMIT GapLedgerMain "${gaps_read}" \
      "the gaps EMIT reads are malformed"

  campaign_require_claim "${composition_manifest}"
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
  local refuted="${iteration_dir}/refuted_claims.jsonl"
  [[ -s "${refuted}" ]] || refuted=/dev/null
  local explored=/dev/null round
  for round in "${iteration_dir}"/obligations-*/explore_manifest.json; do
    [[ -s "${round}" ]] && explored=${round}
  done
  require_nonempty "composed formula" "${campaign_final}/candidate.smt2"
  local formula_path
  formula_path=$(realpath --relative-to="${causynth_output_dir}" \
    "${campaign_final}/candidate.smt2")
  local bounded
  bounded=$(campaign_bounds "${iteration_dir}") \
    || campaign_fail EMIT CAMPAIGN "${iteration_dir}" \
      "the declared bounds the search touched could not be read"
  local doors_only
  doors_only=$(grep -c '"doorsOnly":true' -- "${runtime_region_plan}") \
    || doors_only=0
  local view_hold="null" held_tsv="$(dirname "${iteration_dir}")/view_hold_max.tsv"
  [[ ! -s "${held_tsv}" ]] || view_hold=$(awk -F'\t' -v recorded="${view_hold_max_ms}" \
    '{printf "{\"recordedMs\":%d,\"slowdown\":%d,\"wallMs\":%d,\"cutWindow\":\"%s\"}", recorded, $1, $2, $3}' \
    "${held_tsv}")
  jq -n \
    --argjson provenance "${campaign_provenance}" \
    --argjson confirmation "${confirmation}" \
    --argjson bounded "${bounded}" \
    --argjson doorsOnly "${doors_only}" \
    --argjson viewHoldMax "${view_hold}" \
    --arg formula "${formula_path}" \
    --arg formulaSha "$(campaign_digest "${campaign_final}/candidate.smt2")" \
    --slurpfile refutedClaims "${refuted}" \
    --slurpfile composedDocuments "${composition_manifest}" \
    --slurpfile exploreDocuments "${explored}" \
    --slurpfile gapDocuments "${gaps_read}" \
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
    # of it: confirmed, or not (SAT_UNCONFIRMED) -- refuted by a replay or
    # by ConfirmMain, or decided by no replay (a refusal, a failed
    # decision: also a CONFIRM_NO_VERDICT defect) -- a false positive whose
    # model the next claim excluded, so the last claim is unconfirmed only
    # where the claim bound or the budget ran out (owner 2026-10-08, no
    # refused split); every SAT excluded, the UNSAT the formula then decides
    # is the claim.
    # An UNSAT closes only where no stage named a defect.  Every defect is
    # in defects[].
    ($confirmation != null and $confirmation.confirmed != true
     and $confirmation.refutes != true) as $noVerdict |
    ($decided.claim == "SAT_CANDIDATE"
     and $confirmation.confirmed == true) as $confirmedSat |
    (if $confirmedSat then "SAT_CANDIDATE"
     elif $decided.claim == "SAT_CANDIDATE" then "SAT_UNCONFIRMED"
     elif $gapCount > 0 then "RUN_DEFECT"
     else $decided.claim end) as $claim |
    {schemaVersion: 1,
     kind: "CAMPAIGN_RESULT",
     provenance: $provenance,
     claim: $claim,
     claimReason: (if $claim == "SAT_UNCONFIRMED" and $noVerdict
       then "no confirmation replay decided the model: "
            + $confirmation.reason
       elif $claim == "SAT_UNCONFIRMED"
       then "the confirmation replay did not agree with the model: "
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
     # The realism bound of a view hold the replays ran under: VIEW_HOLD_MAX
     # in recorded ms, the measured slowdown S of the VM, and their product
     # in wall ms (campaign_view_hold_max); null before a seed replay.
     viewHoldMax: $viewHoldMax,
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
     # gaps, whichever stage raised them, and a confirmation no replay
     # decided (its claim SAT_UNCONFIRMED all the same).
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

  session_rows=$(jq -r -s '[.[].rows] | add // 0' \
    "${iteration_dir}/session_census.jsonl") || campaign_fail EMIT CAMPAIGN \
    "${iteration_dir}/session_census.jsonl" "the session census is malformed"
  session_bytes=$(find "${iteration_dir}/sessions" -type f \
    -name '*.jsonl.gz' -printf '%s\n' \
    | awk '{n += $1} END {print n + 0}')
  if ! artifacts_json=$(campaign_artifact_digests "${gaps_read}"); then
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

  gapCount=$(jq -r '.gapCount' "${gaps_read}")
  campaign_count EMIT GapLedger "${gaps_read}" \
    "the published blocking gap count" "${gapCount}"
  campaign_log "artifacts in ${campaign_final}"
  jq -r '"  claim=\(.claim) reachability=\(.reachability) blockers=\(.blockerCount) gaps=\(.gapCount) telemetry=\(.telemetryCount) finalStatus=\(.finalStatus)"' \
    "${campaign_final}/result.json"
  jq -r 'select((.whyNotAccepted // "") != "") | .whyNotAccepted' \
    "${campaign_final}/result.json"
}

campaign_exit_verdict() {
  local gapCount
  gapCount=$(jq -r '.gapCount' "${campaign_final}/result.json")
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
  validate_config >/dev/null
  require_command_available jq
  require_command_available sha256sum
  campaign_init_local_scratch_root
  campaign_log "peer $(hostname) at ${EPOCHREALTIME}: jar \
${graphchecker_jar} (${actual_sha}), scratch ${campaign_local_scratch_root}"
  campaign_peer_args=("$@")
}

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

do_run_obligation() {
  campaign_peer_enter "$@"
  set -- "${campaign_peer_args[@]}"
  [[ $# -eq 5 || $# -eq 6 ]] || die "--run-obligation takes five or six \
positional arguments (id obligations sessions worker charged-mb \
[charge-id|HARD]), got $#"
  campaign_obligation_worker "$@"
}

do_campaign() {
  local iteration_id=iteration-0000
  local iteration_dir
  campaign_root="${schedule_output_dir}"
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${campaign_root}/stage_metrics.tsv"
  iteration_dir="${campaign_root}/${iteration_id}"
  export CAUSYNTH_ZK_CHAIN="${iteration_dir}/zk_chain.jsonl"
  [[ ! -e "${iteration_dir}" && ! -e "${campaign_final}" ]] \
    || die "this campaign root already holds a published run: ${campaign_root}"
  ensure_output_directory "${campaign_root}"
  mkdir -- "${campaign_root}/frozen-inputs" || campaign_fail \
    FREEZE_TOOL CAMPAIGN "${campaign_root}" \
    "the campaign root is already reserved by another run"
  : >"${campaign_stage_metrics}"
  campaign_init_local_scratch_root
  campaign_head_charging=1
  campaign_head_reserve

  campaign_stage PREFLIGHT campaign_preflight
  campaign_stage FREEZE_TOOL campaign_freeze_graphchecker_jar
  if [[ -n "${campaign_setup_command}" ]]; then
    campaign_stage SETUP campaign_setup
  fi
  campaign_stage FREEZE campaign_freeze
  campaign_stage SEED campaign_seed
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
  if [[ "${campaign_stop_after}" == "IMPORT" ]]; then
    campaign_log "stopping after IMPORT: campaign_stop_after=IMPORT"
    return 0
  fi
  campaign_stage ZKKEYS campaign_zk_keys "${iteration_dir}"
  campaign_stage EXPLORE campaign_explore "${iteration_dir}" "${iteration_id}"
  campaign_publish_iteration_manifest "${iteration_dir}" "${iteration_id}"
  campaign_claim_stages "${iteration_dir}"
  while :; do
    while campaign_next_claim "${iteration_dir}"; do
      campaign_claim_stages "${iteration_dir}"
    done
    campaign_stage REPRODUCE campaign_reproduce "${iteration_dir}"
    campaign_unreproduced "${iteration_dir}" || break
    campaign_claim_stages "${iteration_dir}"
  done
  campaign_fallback
  campaign_stage EMIT campaign_emit "${iteration_dir}"
  campaign_exit_verdict
}

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

campaign_claim_stages() {
  campaign_stage COMPOSE campaign_compose "$1"
  campaign_stage SOLVE campaign_solve
  campaign_stage DECIDE campaign_decide
  campaign_stage CONFIRM campaign_confirm "$1"
}

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
