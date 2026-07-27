#!/usr/bin/env bash

set -euo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
runner="${graphchecker_dir}/run_engine.sh"
config=${CAUSYNTH_WORKFLOW_CONFIG:-"${fixture_dir}/workflow.properties"}
if [[ "${config}" != /* ]]; then
  config="${PWD}/${config}"
fi
config=$(realpath -m -- "${config}")

die() {
  echo "[three-thread-rpc] $*" >&2
  exit 1
}

trim_value() {
  local value=$1
  value="${value#"${value%%[![:space:]]*}"}"
  value="${value%"${value##*[![:space:]]}"}"
  printf '%s' "${value}"
}

workflow_property() {
  local requested=$1
  local required=${2:-true}
  local raw key value="" found=false
  while IFS= read -r raw || [[ -n "${raw}" ]]; do
    raw=$(trim_value "${raw}")
    [[ -z "${raw}" || "${raw}" == \#* || "${raw}" != *=* ]] \
      && continue
    key=$(trim_value "${raw%%=*}")
    [[ "${key}" == "${requested}" ]] || continue
    value=$(trim_value "${raw#*=}")
    if [[ ${#value} -ge 2 ]]; then
      if [[ "${value:0:1}" == '"' && "${value: -1}" == '"' ]] \
          || [[ "${value:0:1}" == "'" && "${value: -1}" == "'" ]]; then
        value=${value:1:${#value}-2}
      fi
    fi
    found=true
  done < "${config}"
  if [[ "${found}" == "true" && -n "${value}" ]]; then
    printf '%s\n' "${value}"
  elif [[ "${required}" == "true" ]]; then
    die "workflow configuration has no ${requested}"
  fi
}

[[ -f "${config}" ]] || die "workflow configuration not found: ${config}"
normalized_config=$("${runner}" --config "${config}" config)

configured_value() {
  local key=$1
  local value
  value=$(sed -n "s/^${key}=//p" <<< "${normalized_config}")
  [[ -n "${value}" ]] || die "workflow configuration has no ${key}"
  printf '%s\n' "${value}"
}

work_root=$(configured_value causynth_output_dir)
work_root=$(dirname "${work_root}")
project_repo=$(configured_value project_repo)
project_test_classes=$(configured_value project_test_classes_dir)
original_classes=$(configured_value project_classes_dir)
instrumented_classes=$(configured_value analysis_classes_dir)
static_graph=$(configured_value static_graph)
runtime_edge_validations=$(configured_value runtime_edge_validations)
graphchecker_jar=$(configured_value graphchecker_jar)
maven_bin=$(configured_value maven_bin)
fixture_class=$(workflow_property fixture_class)
fixture_support_class=$(workflow_property fixture_support_class false)
trace_test=$(workflow_property trace_test)
custom_jdk_docker_image=$(workflow_property custom_jdk_docker_image)
custom_jdk_library_path=$(workflow_property custom_jdk_library_path false)
fixture_variant=$(workflow_property fixture_variant false)
fixture_package=${fixture_class%.*}
fixture_package=${fixture_package//./\/}
fixture_simple_class=${fixture_class##*.}
region_plan=$(configured_value runtime_region_plan)
target_schedule=$(configured_value schedule_output_dir)
target_classes="${work_root}/concolic-target-classes"
producer_campaign_root="${work_root}/producer-campaign"
target_campaign_root="${work_root}/target-campaign"
candidate_root="${work_root}/candidate"

usage() {
  cat <<'EOF'
Usage: experiments/generic/three-thread-rpc/run.sh <command> [args]

  prepare                 Build GraphChecker and isolate fixture classes
  analyze                 Static analysis plus trace instrumentation
  trace                   Run a non-bug concrete discovery execution
  discover                Resolve channel producers and target from evidence
  schedule-target         Schedule one unforced consumer target seed
  seed-target             Capture/import the unforced target seed query
  explore-target          Close target-function paths and build reach query
  schedule-producer CH    Schedule one channel's OUTPUT_RELATION_CLOSURE goal
  instrument CH           Instrument that producer's scheduled execution goal
  replay CH [b1 b2]       Run one real custom-JDK concolic capture
  import CH               Strictly import that producer capture
  explore-producer CH     Close and merge one producer path worklist
  candidate-compose       Compose producer relations with the target seed
  candidate-smt           Run the clean workflow through candidate SMT
  candidate-solve         Check the candidate SMT with Z3
  candidate-manifest      Refresh hashes for an existing solved candidate
  candidate               Run the clean workflow through candidate SMT + Z3
  smoke                   prepare + analyze + trace + discovery + target
  all                     Alias for candidate
  clean                   Remove only the configured fixture work products

No command writes SMT text or a reachability formula. Local channels are
discovered from runtime-confirmed shared-field read-from evidence; this
fixture has no declared RPC mapping.
The terminal artifact is deliberately CANDIDATE_ONLY.  Promoting it to a
trusted result by a natural replay is a documented follow-up TODO.
Producer seed pipelines use up to eight region workers by default. Path
exploration then uses bounded waves of independent custom-JDK processes;
CAUSYNTH_CONCOLIC_JOBS defaults to nproc (40 on the current server), and N=1
preserves serial path execution.
EOF
}

require_file() {
  [[ -f "$2" ]] || die "$1 not found: $2"
}

require_directory() {
  [[ -d "$2" ]] || die "$1 directory not found: $2"
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

sha256_file() {
  local path=$1
  require_command sha256sum
  sha256sum "${path}" | awk '{print $1}'
}

workflow_discovery() {
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.RuntimeWorkflowDiscovery \
    --region-plan "${region_plan}" "$@"
}

validate_discovery_inputs() {
  require_file "runtime region plan" "${region_plan}"
  require_file "runtime edge validations" "${runtime_edge_validations}"
  require_file "static data-flow graph" "${static_graph}"
}

discovered_producer_channels() {
  workflow_discovery --command producer-channels
}

producer_binding() {
  workflow_discovery --command producer-binding --channel "$1"
}

target_binding() {
  workflow_discovery --command target-binding
}

channel_schedule() {
  printf '%s/schedule-%s\n' "${work_root}" \
    "$(printf '%s' "$1" | tr '[:upper:]' '[:lower:]')"
}

channel_classes() {
  printf '%s/concolic-%s-classes\n' "${work_root}" \
    "$(printf '%s' "$1" | tr '[:upper:]' '[:lower:]')"
}

scheduled_task() {
  local channel=$1
  local schedule
  schedule=$(channel_schedule "${channel}") || return $?
  require_file "scheduled producer task" \
    "${schedule}/execution_task_plan.jsonl"
  workflow_discovery --command scheduled-task --channel "${channel}" \
    --task-plan "${schedule}/execution_task_plan.jsonl"
}

scheduled_target_task() {
  require_file "scheduled target task" \
    "${target_schedule}/execution_task_plan.jsonl"
  workflow_discovery --command scheduled-target-task \
    --task-plan "${target_schedule}/execution_task_plan.jsonl"
}

do_prepare() {
  if [[ "${GRAPH_CHECKER_SKIP_BUILD:-false}" == "true" ]]; then
    require_file "prebuilt GraphChecker jar" "${graphchecker_jar}"
    require_directory "prebuilt project test classes" \
      "${project_test_classes}"
  else
    (cd "${graphchecker_dir}" && "${maven_bin}" -q -DskipTests package)
  fi
  local source_dir="${project_test_classes}/${fixture_package}"
  local destination="${original_classes}/${fixture_package}"
  require_directory "compiled fixture package" "${source_dir}"
  mkdir -p "${destination}"
  # This directory is a reproducible build product dedicated to this fixture.
  find "${destination}" -maxdepth 1 -type f -name '*.class' -delete
  find "${source_dir}" -maxdepth 1 -type f \
    -name "${fixture_simple_class}*.class" ! -name '*Test*.class' \
    -exec cp -f {} "${destination}/" \;
  [[ -f "${destination}/${fixture_simple_class}.class" ]] \
    || die "fixture class isolation failed"
  if [[ -n "${fixture_support_class}" ]]; then
    [[ "${fixture_support_class%.*}" == "${fixture_class%.*}" ]] \
      || die "fixture support class must share the fixture package"
    local support_simple_class=${fixture_support_class##*.}
    find "${source_dir}" -maxdepth 1 -type f \
      -name "${support_simple_class}*.class" ! -name '*Test*.class' \
      -exec cp -f {} "${destination}/" \;
    [[ -f "${destination}/${support_simple_class}.class" ]] \
      || die "fixture support class isolation failed"
  fi
}

do_analyze() {
  require_directory "isolated fixture classes" \
    "${original_classes}"
  (cd "${graphchecker_dir}" && CAUSYNTH_INSTRUMENT_TRACE=true \
    "${runner}" --config "${config}" analyze)
}

do_trace() {
  require_directory "trace-instrumented classes" \
    "${instrumented_classes}"
  (cd "${graphchecker_dir}" && "${runner}" --config "${config}" workload)
  require_file "runtime region plans" "${region_plan}"
  require_file "runtime edge validations" "${runtime_edge_validations}"
}

do_discover() {
  validate_discovery_inputs
  workflow_discovery --command discover
}

do_schedule_target() {
  local region instance goal binding
  validate_discovery_inputs
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region instance goal <<< "${binding}"
  (cd "${graphchecker_dir}" && "${runner}" --config "${config}" schedule \
    --region-id "${region}" --region-instance-id "${instance}" \
    --goal-id "${goal}")
  jq -e -s 'length == 1' \
    "${target_schedule}/execution_task_plan.jsonl" >/dev/null \
    || die "target scheduler did not emit exactly one task"
}

do_schedule_producer() {
  local channel=$1
  local region instance goal output binding
  validate_discovery_inputs
  binding=$(producer_binding "${channel}") || return $?
  IFS=$'\t' read -r region instance goal <<< "${binding}"
  output=$(channel_schedule "${channel}") || return $?
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_SCHEDULE_OUTPUT_DIR="${output}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${region}" --region-instance-id "${instance}" \
      --goal-id "${goal}")
}

do_instrument() {
  local channel=$1
  local schedule classes task
  validate_discovery_inputs
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  task=$(scheduled_task "${channel}") || return $?
  instrument_plan "${schedule}/execution_task_plan.jsonl" \
    "${task}" "${classes}"
}

instrument_plan() {
  local plan=$1
  local task=$2
  local classes=$3
  require_file "concolic execution task plan" "${plan}"
  [[ -s "${plan}" ]] || die "concolic execution task plan is empty: ${plan}"
  jq -e -s --arg task "${task}" '
    length == 1 and .[0].taskId == $task
  ' "${plan}" >/dev/null \
    || die "task plan is not the requested singleton ${task}: ${plan}"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${classes}" \
    CAUSYNTH_INSTRUMENT_CONCOLIC=true \
    CAUSYNTH_CONCOLIC_TASK_PLAN="${plan}" \
    CAUSYNTH_CONCOLIC_TASK_ID="${task}" \
    "${runner}" --config "${config}" analyze)
}

run_custom_plan() {
  local plan=$1
  local task=$2
  local classes=$3
  local results=$4
  local b1=$5
  local b2=$6
  local accept_nonzero=$7
  local worker_dir=${8:-}
  local jdk java_path replay_status
  local resolved_library_path="" java_library_path=""
  local -a java_env worker_jvm_args
  java_env=()
  worker_jvm_args=()
  require_file "concolic execution task plan" "${plan}"
  require_directory "concolic fixture classes" "${classes}"
  [[ ! -e "${results}" ]] || die "capture output already exists: ${results}"
  mkdir -p "$(dirname "${results}")"
  jdk=$(configured_value custom_jdk_home) || return $?
  java_path="${jdk}/bin/java"
  [[ -x "${java_path}" ]] || die "custom JDK is not built: ${java_path}"
  if [[ -n "${custom_jdk_library_path}" ]]; then
    resolved_library_path=${custom_jdk_library_path}
    if [[ "${resolved_library_path}" != /* ]]; then
      resolved_library_path="${graphchecker_dir}/${resolved_library_path}"
    fi
    resolved_library_path=$(realpath -m -- "${resolved_library_path}")
    [[ -d "${resolved_library_path}" ]] \
      || die "custom JDK native library directory not found: ${resolved_library_path}"
    java_library_path="${resolved_library_path}${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
    java_env+=(LD_LIBRARY_PATH="${java_library_path}")
  fi
  jq -e -s --arg task "${task}" '
    length == 1 and .[0].taskId == $task
  ' "${plan}" >/dev/null \
    || die "task plan is not the requested singleton ${task}: ${plan}"

  local -a java_args fixture_variant_args
  fixture_variant_args=()
  if [[ -n "${worker_dir}" ]]; then
    mkdir -p "${worker_dir}/tmp"
    worker_jvm_args=(
      -Xms32m
      -Xmx1g
      -XX:+UseSerialGC
      -Djava.io.tmpdir="${worker_dir}/tmp"
      -XX:ErrorFile="${worker_dir}/hs_err_pid%p.log"
    )
  fi
  if [[ -n "${fixture_variant}" ]]; then
    fixture_variant_args+=(
      -Dcausynth.fixture.variant="${fixture_variant}"
    )
  fi
  java_args=(
    "${worker_jvm_args[@]}"
    -Xint
    -Dcausynth.trace.test="${trace_test}"
    -Dcausynth.concolic.task.plan="${plan}"
    -Dcausynth.concolic.task.id="${task}"
    -Dcausynth.concolic.results="${results}"
    "${fixture_variant_args[@]}"
    -cp "${classes}:${graphchecker_jar}"
    "${fixture_class}" "${b1}" "${b2}"
  )
  if env -u CAUSYNTH_TRACE_OUTPUT_DIR \
      "${java_env[@]}" "${java_path}" -version >/dev/null 2>&1; then
    if (cd "${graphchecker_dir}" && env -u CAUSYNTH_CONCOLIC_TASK_ID \
        -u CAUSYNTH_TRACE_OUTPUT_DIR \
        "${java_env[@]}" \
        "${java_path}" "${java_args[@]}"); then
      replay_status=0
    else
      replay_status=$?
    fi
  else
    command -v docker >/dev/null 2>&1 \
      || die "custom JDK needs libffi.so.6 and Docker is unavailable"
    local -a container_args
    container_args=("${java_args[@]}")
    local index
    for index in "${!container_args[@]}"; do
      container_args[index]=${container_args[index]//${graphchecker_dir}/\/graphchecker}
    done
    if docker run --rm -v "${graphchecker_dir}:/graphchecker" \
        -w /graphchecker "${custom_jdk_docker_image}" \
        "/graphchecker/${java_path#${graphchecker_dir}/}" \
        "${container_args[@]}"; then
      replay_status=0
    else
      replay_status=$?
    fi
  fi
  [[ -s "${results}" ]] || die \
    "custom-JDK replay emitted no concolic result (exit ${replay_status}): ${results}"
  if [[ "${replay_status}" -ne 0 && "${accept_nonzero}" != "true" ]]; then
    die "custom-JDK replay failed with exit ${replay_status}: ${results}"
  fi
  if [[ "${replay_status}" -ne 0 ]]; then
    jq -e -s --arg task "${task}" '
      [.[] | select(.taskId == $task)] | length == 1
    ' "${results}" >/dev/null \
      || die "nonzero replay emitted no selected raw task result"
    echo "[three-thread-rpc] accepted expected nonzero replay exit ${replay_status}; selected raw evidence exists"
  fi
}

run_custom_java() {
  local channel=$1
  local b1=$2
  local b2=$3
  local schedule classes task results
  validate_discovery_inputs
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  task=$(scheduled_task "${channel}") || return $?
  results="${schedule}/concolic_region_results.jsonl"
  run_custom_plan "${schedule}/execution_task_plan.jsonl" \
    "${task}" "${classes}" "${results}" "${b1}" "${b2}" false
}

do_import() {
  local channel=$1
  local schedule
  validate_discovery_inputs
  schedule=$(channel_schedule "${channel}") || return $?
  scheduled_task "${channel}" >/dev/null
  import_plan "${schedule}/execution_task_plan.jsonl" \
    "${schedule}/concolic_region_results.jsonl" \
    "${schedule}/concolic_region_summaries.jsonl" "${schedule}"
}

import_plan() {
  local plan=$1
  local results=$2
  local summaries=$3
  local output_dir=$4
  require_file "import execution task plan" "${plan}"
  [[ -s "${results}" ]] || die "raw concolic result is missing or empty: ${results}"
  mkdir -p "${output_dir}"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_RAW_RESULTS="${results}" \
    CAUSYNTH_IMPORT_TASK_PLAN="${plan}" \
    CAUSYNTH_IMPORTED_SUMMARIES="${summaries}" \
    CAUSYNTH_IMPORT_DIAGNOSTICS="${output_dir}/concolic_import_diagnostics.jsonl" \
    "${runner}" --config "${config}" import)
}

run_graphchecker_main() {
  local main_class=$1
  shift
  local jar java_bin
  jar=$(configured_value graphchecker_jar) || return $?
  java_bin=$(configured_value java_bin) || return $?
  require_file "GraphChecker jar" "${jar}"
  (cd "${graphchecker_dir}" && "${java_bin}" -cp "${jar}" \
    "${main_class}" "$@")
}

debug_enabled() {
  case "${GRAPH_CHECKER_DEBUG:-false}" in
    1|true|TRUE|yes|YES|on|ON) return 0 ;;
    *) return 1 ;;
  esac
}

debug_merged_relation() {
  local merged=$1
  debug_enabled || return 0
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_MERGED_SUMMARIES="${merged}" \
      "${runner}" --config "${config}" debug-stage merge)
}

producer_iteration_directory() {
  local campaign=$1
  local iteration=$2
  if debug_enabled; then
    printf '%s/iteration-%04d\n' "${campaign}" "${iteration}"
  else
    printf '%s/current\n' "${campaign}"
  fi
}

discard_successful_iteration() {
  local campaign=$1
  local scratch="${campaign}/current"
  debug_enabled && return 0
  [[ "${campaign}" == "${work_root}/"* ]] \
    || die "refusing to clean path scratch outside work root: ${campaign}"
  [[ "${scratch}" == "${campaign}/current" ]] \
    || die "invalid producer scratch path: ${scratch}"
  [[ -d "${scratch}" && ! -L "${scratch}" ]] \
    || die "producer scratch is missing or unsafe: ${scratch}"
  find "${scratch}" -mindepth 1 -delete
  rmdir "${scratch}"
}

discard_successful_campaign_state() {
  local campaign=$1
  local state="${campaign}/.state"
  debug_enabled && return 0
  [[ "${campaign}" == "${work_root}/"* ]] \
    || die "refusing to clean path state outside work root: ${campaign}"
  [[ "${state}" == "${campaign}/.state" ]] \
    || die "invalid producer state path: ${state}"
  [[ -d "${state}" && ! -L "${state}" ]] \
    || die "producer state is missing or unsafe: ${state}"
  find "${state}" -mindepth 1 -delete
  rmdir "${state}"
}

combine_jsonl_unique() {
  local identity_field=$1
  local output=$2
  shift 2
  [[ $# -gt 0 ]] || die "no JSONL inputs supplied for ${output}"
  local input
  for input in "$@"; do
    require_file "JSONL input" "${input}"
  done
  mkdir -p "$(dirname "${output}")"
  local temporary
  temporary=$(mktemp "${output}.tmp.XXXXXX")
  if ! jq -c -s --arg identity "${identity_field}" '
      def comparable:
        if $identity == "summaryId" then del(.taskId) else . end;
      reduce .[] as $row (
        {order: [], rows: {}};
        ($row[$identity] // "") as $key
        | if ($row | type) != "object" or ($key | type) != "string"
            or ($key | length) == 0 then
            error("missing JSONL identity " + $identity)
          elif (.rows | has($key))
              and (.rows[$key] | comparable) != ($row | comparable) then
            error("conflicting duplicate " + $identity + ":" + $key)
          elif (.rows | has($key)) then .
          else .order += [$key] | .rows[$key] = $row
          end)
      | .order[] as $key | .rows[$key]
    ' "$@" >"${temporary}"; then
    rm -f "${temporary}"
    die "could not combine JSONL inputs for ${output}"
  fi
  [[ -s "${temporary}" ]] || {
    rm -f "${temporary}"
    die "combined JSONL output is empty: ${output}"
  }
  mv -f "${temporary}" "${output}"
}

producer_campaign_directory() {
  printf '%s/%s\n' "${producer_campaign_root}" \
    "$(printf '%s' "$1" | tr '[:upper:]' '[:lower:]')"
}

run_path_task() {
  local query_key=$1
  local worklist=$2
  local execution_tasks=$3
  local classes=$4
  local task_dir=$5
  local z3=$6
  local solver_timeout=$7
  local solver_status solver_outcome replay_task raw imported

  mkdir -p "${task_dir}/tmp"
  set +e
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipSolver \
    --worklist "${worklist}" \
    --task-plan "${execution_tasks}" \
    --query-key "${query_key}" \
    --output-dir "${task_dir}" \
    --z3 "${z3}" \
    --solver-timeout-ms "${solver_timeout}"
  solver_status=$?
  set -e
  require_file "producer path solver result" \
    "${task_dir}/path_flip_solver_result.json"
  [[ "${solver_status}" -eq 0 ]] \
    || die "producer path solver failed with exit ${solver_status}"
  solver_outcome=$(jq -er '.status' \
    "${task_dir}/path_flip_solver_result.json") \
    || die "producer path solver emitted no status"

  if [[ "${solver_outcome}" == "UNSAT" ]]; then
    jq -c '{
      schemaVersion: 1,
      kind: "PATH_EXPLORATION_RECORD",
      queryKey,
      regionId,
      sourcePathKey,
      sourceSummaryId,
      status,
      solverInputHash
    }' "${task_dir}/path_flip_solver_result.json" \
      >"${task_dir}/exploration_record.jsonl"
    return 0
  fi

  [[ "${solver_outcome}" == "SAT_MODEL_READY" ]] \
    || die "producer path flip is not solver-backed"
  replay_task=$(jq -er -s '
    if length == 1 then .[0].taskId
    else error("expected one exact replay task")
    end
  ' "${task_dir}/execution_task_plan.jsonl") \
    || die "producer path flip has no exact replay task"

  raw="${task_dir}/concolic_region_results.jsonl"
  imported="${task_dir}/concolic_region_summaries.jsonl"
  run_custom_plan "${task_dir}/execution_task_plan.jsonl" \
    "${replay_task}" "${classes}" "${raw}" false false true \
    "${task_dir}"
  import_plan "${task_dir}/execution_task_plan.jsonl" "${raw}" \
    "${imported}" "${task_dir}"
  jq -e -c -s \
    --slurpfile executionTask "${task_dir}/execution_task_plan.jsonl" \
    --slurpfile raw "${raw}" '
    if length == 1
      and ($executionTask | length) == 1
      and ($raw | length) == 1
      and .[0].relationallyComplete == true
      and .[0].taskId == $executionTask[0].taskId
      and .[0].regionInstanceId == $executionTask[0].regionInstanceId
      and .[0].goalId == $executionTask[0].goalId
      and .[0].regionId == $executionTask[0].regionId
      and $raw[0].taskId == $executionTask[0].taskId
      and ($executionTask[0].goalKind != "OUTPUT_RELATION_CLOSURE"
        or (.[0].normalExit == true
          and (.[0].outputExpressions | keys | sort)
            == (.[0].outputClosure.members
              | map(.output.portId) | sort)))
    then {
      schemaVersion: 1,
      kind: "PATH_EXPLORATION_RECORD",
      queryKey: $executionTask[0].pathQueryKey,
      regionId: $executionTask[0].regionId,
      taskId: $executionTask[0].taskId,
      regionInstanceId: $executionTask[0].regionInstanceId,
      goalId: $executionTask[0].goalId,
      status: (if $executionTask[0].goalKind == "OUTPUT_RELATION_CLOSURE"
        then "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
        else "VALIDATED_FRESH_TARGET_PATH_FLIP_REPLAY"
        end)
    }
    else error("imported replay did not satisfy the canonical admission")
    end
  ' "${imported}" >"${task_dir}/exploration_record.jsonl" \
    || die "path replay admission failed; inspect ${task_dir}/execution_task_plan.jsonl, ${raw}, ${imported}, and ${task_dir}/concolic_import_diagnostics.jsonl"
}

wait_for_path_wave() {
  local pid failed=false
  for pid in "$@"; do
    if ! wait "${pid}"; then
      failed=true
    fi
  done
  [[ "${failed}" == "false" ]]
}

report_path_worklist_failure() {
  local planner_dir=$1
  local manifest="${planner_dir}/region_path_manifest.json"
  local worklist="${planner_dir}/region_path_worklist.jsonl"
  echo "[three-thread-rpc] path planner debug artifacts:" >&2
  echo "  manifest: ${manifest}" >&2
  echo "  worklist: ${worklist}" >&2
  jq -r '
    "  state=\(.state)",
    (.gaps[]?
      | "  blocking-gap kind=\(.kind) reason=\(.reason) site=\(.siteId) occurrence=\(.occurrence) path=\(.pathKey)"),
    (.deferredObservations[]?
      | "  deferred-observation kind=\(.kind) reason=\(.reason) site=\(.siteId) occurrence=\(.occurrence) path=\(.pathKey)")
  ' "${manifest}" >&2 || true
}

report_path_wave_failure() {
  local wave_dir=$1
  local task_dir query
  local -a task_dirs=()
  echo "[three-thread-rpc] failed path wave artifacts: ${wave_dir}" >&2
  echo "  planner manifest: ${wave_dir}/region_path_manifest.json" >&2
  echo "  planner worklist: ${wave_dir}/region_path_worklist.jsonl" >&2
  mapfile -t task_dirs < <(find "${wave_dir}" -mindepth 1 -maxdepth 1 \
    -type d -name 'task-*' | LC_ALL=C sort)
  for task_dir in "${task_dirs[@]}"; do
    [[ ! -s "${task_dir}/exploration_record.jsonl" ]] || continue
    query=${task_dir##*/task-}
    echo "  failed query: ${query}" >&2
    echo "    stderr: ${task_dir}/stderr.log" >&2
    echo "    solver: ${task_dir}/path_flip_solver_result.json" >&2
    echo "    raw result: ${task_dir}/concolic_region_results.jsonl" >&2
    echo "    import diagnostics: ${task_dir}/concolic_import_diagnostics.jsonl" >&2
    if [[ -s "${task_dir}/path_flip_solver_result.json" ]]; then
      jq -r '
        "    solver-status=\(.status // "missing") solver=\(.solverStatus // "missing") reason=\(.reason // "")"
      ' "${task_dir}/path_flip_solver_result.json" >&2 || true
    fi
    if [[ -s "${task_dir}/stderr.log" ]]; then
      echo "    stderr tail:" >&2
      tail -n 40 "${task_dir}/stderr.log" \
        | sed 's/^/      /' >&2
    fi
  done
}

publish_path_wave() {
  local wave_dir=$1
  local state_dir=$2
  local summaries=$3
  local execution_tasks=$4
  local raw_results=$5
  local records=$6
  local task_dir
  local -a task_dirs summary_inputs task_inputs raw_inputs record_inputs

  mapfile -t task_dirs < <(find "${wave_dir}" -mindepth 1 -maxdepth 1 \
    -type d -name 'task-*' | LC_ALL=C sort)
  [[ ${#task_dirs[@]} -gt 0 ]] || die "path wave has no task directories"
  summary_inputs=("${summaries}")
  task_inputs=("${execution_tasks}")
  raw_inputs=("${raw_results}")
  record_inputs=("${records}")

  for task_dir in "${task_dirs[@]}"; do
    require_file "path exploration record" \
      "${task_dir}/exploration_record.jsonl"
    record_inputs+=("${task_dir}/exploration_record.jsonl")
    if [[ -s "${task_dir}/execution_task_plan.jsonl" ]]; then
      require_file "path replay raw result" \
        "${task_dir}/concolic_region_results.jsonl"
      require_file "path replay imported summary" \
        "${task_dir}/concolic_region_summaries.jsonl"
      task_inputs+=("${task_dir}/execution_task_plan.jsonl")
      raw_inputs+=("${task_dir}/concolic_region_results.jsonl")
      summary_inputs+=("${task_dir}/concolic_region_summaries.jsonl")
    fi
  done

  combine_jsonl_unique summaryId "${state_dir}/next_summaries.jsonl" \
    "${summary_inputs[@]}"
  combine_jsonl_unique taskId "${state_dir}/next_execution_tasks.jsonl" \
    "${task_inputs[@]}"
  combine_jsonl_unique taskId "${state_dir}/next_raw_results.jsonl" \
    "${raw_inputs[@]}"
  combine_jsonl_unique queryKey "${state_dir}/next_records.jsonl" \
    "${record_inputs[@]}"
  mv -f "${state_dir}/next_summaries.jsonl" "${summaries}"
  mv -f "${state_dir}/next_execution_tasks.jsonl" "${execution_tasks}"
  mv -f "${state_dir}/next_raw_results.jsonl" "${raw_results}"
  mv -f "${state_dir}/next_records.jsonl" "${records}"
}

explore_region_paths() {
  local label=$1
  local region=$2
  local goal=$3
  local schedule=$4
  local classes=$5
  local campaign=$6
  local summaries execution_tasks raw_results records state_dir planner_dir
  local z3 solver_timeout planner_status query_key iteration jobs task_dir
  local wave_limit
  local bound_spec bound_property bound_option bound_value
  local -a planner_bound_args=() wave_query_keys=() worker_pids=()
  require_file "${label} seed summary" \
    "${schedule}/concolic_region_summaries.jsonl"
  require_directory "${label} concolic classes" "${classes}"
  [[ ! -e "${campaign}" ]] \
    || die "${label} campaign already exists: ${campaign}"
  mkdir -p "${campaign}"
  state_dir="${campaign}/.state"
  mkdir -p "${state_dir}"
  summaries="${campaign}/observed_path_summaries.jsonl"
  execution_tasks="${state_dir}/observed_execution_tasks.jsonl"
  raw_results="${campaign}/raw_results.jsonl"
  records="${campaign}/path_exploration_records.jsonl"
  : >"${records}"
  combine_jsonl_unique summaryId "${summaries}" \
    "${schedule}/concolic_region_summaries.jsonl"
  combine_jsonl_unique taskId "${execution_tasks}" \
    "${schedule}/execution_task_plan.jsonl"
  combine_jsonl_unique taskId "${raw_results}" \
    "${schedule}/concolic_region_results.jsonl"
  z3=$(configured_value z3_bin) || return $?
  solver_timeout=$(configured_value solver_timeout_ms) || return $?
  jobs=${CAUSYNTH_CONCOLIC_JOBS:-$(nproc)}
  [[ "${jobs}" =~ ^[1-9][0-9]*$ ]] \
    || die "CAUSYNTH_CONCOLIC_JOBS must be a positive integer"
  for bound_spec in \
      "producer_max_paths_per_region:max-paths-per-region" \
      "producer_max_flips_per_path:max-flips-per-path" \
      "producer_max_path_tasks:max-tasks"; do
    bound_property=${bound_spec%%:*}
    bound_option=${bound_spec#*:}
    bound_value=$(workflow_property "${bound_property}" false)
    [[ -n "${bound_value}" ]] || continue
    [[ "${bound_value}" =~ ^[1-9][0-9]*$ ]] \
      || die "${bound_property} must be a positive integer"
    planner_bound_args+=("--${bound_option}" "${bound_value}")
  done

  iteration=1
  while true; do
    planner_dir=$(producer_iteration_directory "${campaign}" "${iteration}")
    [[ ! -e "${planner_dir}" ]] \
      || die "producer iteration scratch already exists: ${planner_dir}"
    mkdir -p "${planner_dir}"
    set +e
    run_graphchecker_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
      --summaries "${summaries}" \
      --task-plan "${execution_tasks}" \
      --records "${records}" \
      --output-dir "${planner_dir}" \
      --region-id "${region}" \
      --goal-id "${goal}" \
      "${planner_bound_args[@]}"
    planner_status=$?
    set -e
    require_file "${label} path worklist manifest" \
      "${planner_dir}/region_path_manifest.json"
    if [[ "${planner_status}" -eq 2 ]]; then
      jq -e '.state == "GAPPED" or .state == "NOT_STARTED"' \
        "${planner_dir}/region_path_manifest.json" >/dev/null \
        || die "${label} path planner failed with exit ${planner_status}"
      report_path_worklist_failure "${planner_dir}"
      die "${label} path worklist is not executable; inspect ${planner_dir}/region_path_manifest.json"
    fi
    [[ "${planner_status}" -eq 0 ]] \
      || die "${label} path planner failed with exit ${planner_status}"
    if jq -e '.state == "CLOSED"' \
        "${planner_dir}/region_path_manifest.json" >/dev/null; then
      [[ ! -s "${planner_dir}/region_path_worklist.jsonl" ]] \
        || die "closed ${label} worklist retained pending tasks"
      cp -f "${planner_dir}/region_path_manifest.json" \
        "${campaign}/region_path_closure.json"
      cp -f "${planner_dir}/merged_region_summaries.jsonl" \
        "${campaign}/merged_region_summaries.jsonl"
      break
    fi
    jq -e '.state == "PENDING"' \
      "${planner_dir}/region_path_manifest.json" >/dev/null \
      || die "${label} path planner emitted neither pending nor closed state"
    wave_limit=${jobs}
    mapfile -t wave_query_keys < <(jq -r -s \
      --argjson limit "${wave_limit}" '
      sort_by(.queryKey) | .[0:$limit][] | .queryKey
    ' "${planner_dir}/region_path_worklist.jsonl")
    [[ ${#wave_query_keys[@]} -gt 0 ]] \
      || die "pending ${label} worklist has no deterministic query key"

    worker_pids=()
    echo "[three-thread-rpc] ${label} wave ${iteration}: running ${#wave_query_keys[@]} path worker(s), cap=${jobs}"
    for query_key in "${wave_query_keys[@]}"; do
      task_dir="${planner_dir}/task-${query_key}"
      mkdir -p "${task_dir}"
      (
        set -euo pipefail
        run_path_task "${query_key}" \
          "${planner_dir}/region_path_worklist.jsonl" \
          "${execution_tasks}" "${classes}" "${task_dir}" "${z3}" \
          "${solver_timeout}"
      ) >"${task_dir}/stdout.log" 2>"${task_dir}/stderr.log" &
      worker_pids+=("$!")
    done
    if ! wait_for_path_wave "${worker_pids[@]}"; then
      report_path_wave_failure "${planner_dir}"
      die "${label} path wave ${iteration} failed; inspect ${planner_dir}"
    fi
    publish_path_wave "${planner_dir}" "${state_dir}" "${summaries}" \
      "${execution_tasks}" "${raw_results}" "${records}"
    discard_successful_iteration "${campaign}"
    iteration=$((iteration + 1))
  done
  echo "[three-thread-rpc] ${label} path worklist closed after $((iteration - 1)) wave(s)"
}

do_explore_producer() {
  local channel=$1
  local schedule classes campaign region instance goal binding
  validate_discovery_inputs
  binding=$(producer_binding "${channel}") || return $?
  IFS=$'\t' read -r region instance goal <<< "${binding}"
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  campaign=$(producer_campaign_directory "${channel}") || return $?
  explore_region_paths "producer ${channel}" "${region}" "${goal}" "${schedule}" \
    "${classes}" "${campaign}"

  debug_merged_relation "${campaign}/merged_region_summaries.jsonl"
  jq -e -s --arg region "${region}" '
    length == 1
    and .[0].outputClosure.producer.regionId == $region
    and .[0].relationallyComplete == true
  ' "${campaign}/merged_region_summaries.jsonl" >/dev/null \
    || die "producer merged relation is not complete for channel ${channel}"
  discard_successful_iteration "${campaign}"
  discard_successful_campaign_state "${campaign}"
}

do_explore_target() {
  local binding region instance goal campaign exception_type
  validate_discovery_inputs
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region instance goal <<< "${binding}"
  campaign="${target_campaign_root}"
  explore_region_paths "target" "${region}" "${goal}" "${target_schedule}" \
    "${target_classes}" "${campaign}"
  exception_type=$(jq -er '
    .exception | select(type == "string" and length > 0)
  ' "${work_root}/analysis/target_resolved.json") \
    || die "target attestation has no exception"
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.TargetReachPathQueryBuilder \
    --summaries "${campaign}/observed_path_summaries.jsonl" \
    --path-manifest "${campaign}/region_path_closure.json" \
    --seed-query "${target_schedule}/branch_queries.jsonl" \
    --exception-type "${exception_type}" \
    --output "${target_schedule}/branch_queries.jsonl" >/dev/null
  jq -e -s '
    length == 1
    and .[0].kind == "TARGET_REACH_PATH_SET_QUERY"
    and .[0].constraintAuthority
      == "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1"
  ' "${target_schedule}/branch_queries.jsonl" >/dev/null \
    || die "closed target reach query is incomplete"
  discard_successful_iteration "${campaign}"
  discard_successful_campaign_state "${campaign}"
  echo "[three-thread-rpc] target reach paths: $(jq -r '.paths | length' "${target_schedule}/branch_queries.jsonl")"
}

run_producer_seed_pipeline() {
  local channel=$1
  do_schedule_producer "${channel}"
  do_instrument "${channel}"
  run_custom_java "${channel}" false false
  do_import "${channel}"
}

wait_for_producer_batch() {
  local pid failed=false
  for pid in "$@"; do
    if ! wait "${pid}"; then
      failed=true
    fi
  done
  [[ "${failed}" == "false" ]]
}

run_producers_parallel() {
  local channel max_jobs
  local -a channels producer_pids=()
  mapfile -t channels < <(discovered_producer_channels | LC_ALL=C sort)
  [[ ${#channels[@]} -gt 0 ]] || die "runtime discovery found no producers"

  max_jobs=${CAUSYNTH_REGION_JOBS:-8}
  [[ "${max_jobs}" =~ ^[1-9][0-9]*$ ]] \
    || die "CAUSYNTH_REGION_JOBS must be a positive integer"
  if (( max_jobs > ${#channels[@]} )); then
    max_jobs=${#channels[@]}
  fi

  echo "[three-thread-rpc] running ${#channels[@]} producer demand(s) with ${max_jobs} worker process(es)"
  for channel in "${channels[@]}"; do
    (
      set -euo pipefail
      run_producer_seed_pipeline "${channel}"
      do_explore_producer "${channel}"
      echo "[three-thread-rpc] producer ${channel} path campaign complete"
    ) &
    producer_pids+=("$!")
    if (( ${#producer_pids[@]} >= max_jobs )); then
      wait_for_producer_batch "${producer_pids[@]}" \
        || die "producer region pipeline failed"
      producer_pids=()
    fi
  done

  if (( ${#producer_pids[@]} > 0 )); then
    wait_for_producer_batch "${producer_pids[@]}" \
      || die "producer region pipeline failed"
  fi

}

do_candidate_compose() {
  local target_region target_instance target_goal binding channel campaign
  local producer_binding_row producer_region producer_summary
  local compose_summaries
  local -a channels merged_inputs
  require_file "target seed summary" \
    "${target_schedule}/concolic_region_summaries.jsonl"
  require_file "target candidate branch query" \
    "${target_schedule}/branch_queries.jsonl"
  [[ ! -e "${candidate_root}" ]] \
    || die "candidate output already exists: ${candidate_root}"
  mkdir -p "${candidate_root}"
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r target_region target_instance target_goal <<< "${binding}"
  mapfile -t channels < <(discovered_producer_channels | LC_ALL=C sort)
  [[ ${#channels[@]} -gt 0 ]] || die "runtime discovery found no producers"
  merged_inputs=()
  for channel in "${channels[@]}"; do
    producer_binding_row=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r producer_region _ <<< "${producer_binding_row}"
    campaign=$(producer_campaign_directory "${channel}") || return $?
    producer_summary="${campaign}/merged_region_summaries.jsonl"
    require_file "merged producer summary" "${producer_summary}"
    jq -e -s --arg region "${producer_region}" '
      length == 1
      and .[0].outputClosure.producer.regionId == $region
      and (.[0].summaryId | type == "string" and length > 0)
      and .[0].relationallyComplete == true
    ' "${producer_summary}" >/dev/null \
      || die "producer relation is incomplete for channel ${channel}"
    merged_inputs+=("${producer_summary}")
  done
  jq -e -s --argjson expected "${#merged_inputs[@]}" '
    length == $expected
    and ([.[].summaryId] | unique | length) == $expected
  ' "${merged_inputs[@]}" >/dev/null \
    || die "producer relation identities are not unique"
  compose_summaries=$(IFS=:; printf '%s' "${merged_inputs[*]}")
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_FATAL_QUERIES="${target_schedule}/branch_queries.jsonl" \
    CAUSYNTH_COMPOSE_SUMMARIES="${compose_summaries}" \
    CAUSYNTH_COMPOSED_SMT="${candidate_root}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${candidate_root}/candidate_composition_manifest.json" \
    CAUSYNTH_FATAL_REGION="${target_region}" \
    CAUSYNTH_FATAL_REGION_INSTANCE_ID="${target_instance}" \
    "${runner}" --config "${config}" compose)
  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_COMPOSED_SMT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.gaps | type == "array" and length == 0)
  ' "${candidate_root}/candidate_composition_manifest.json" >/dev/null \
    || die "composition is not a structurally complete candidate model"
}

do_candidate_solve() {
  require_file "candidate SMT" "${candidate_root}/candidate.smt2"
  require_file "candidate composition manifest" \
    "${candidate_root}/candidate_composition_manifest.json"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_COMPOSED_SMT="${candidate_root}/candidate.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${candidate_root}/candidate_composition_manifest.json" \
    CAUSYNTH_REACH_REPORT="${candidate_root}/candidate_boolean_model.json" \
    "${runner}" --config "${config}" reach)
  if jq -e '
    .schemaVersion == 3
    and .kind == "BOOLEAN_REACH_CONDITION_REPORT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and .reachCondition.reachability == "REACHABLE"
    and (.gaps | type == "array" and length == 0)
    and (.valuations | type == "array" and length > 0)
    and all(.valuations[];
      .status == "sat" or .status == "unsat")
    and any(.valuations[]; .status == "sat")
  ' "${candidate_root}/candidate_boolean_model.json" >/dev/null; then
    :
  elif jq -e '
    .schemaVersion == 3
    and .kind == "BOOLEAN_REACH_CONDITION_REPORT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and .reachCondition.reachability == "UNREACHABLE"
    and (.gaps | type == "array" and length == 0)
    and (.valuations | type == "array" and length > 0)
    and all(.valuations[]; .status == "unsat")
    and .reachCondition.formula == "false"
  ' "${candidate_root}/candidate_boolean_model.json" >/dev/null; then
    echo "[three-thread-rpc] candidate SMT is UNSAT"
  else
    die "candidate model is neither a complete SAT nor a complete UNSAT result"
  fi
}

do_seed_target() {
  local instance goal task region binding summary
  validate_discovery_inputs
  task=$(scheduled_target_task) || return $?
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region instance goal <<< "${binding}"
  instrument_plan "${target_schedule}/execution_task_plan.jsonl" \
    "${task}" "${target_classes}"
  run_custom_plan "${target_schedule}/execution_task_plan.jsonl" \
    "${task}" "${target_classes}" \
    "${target_schedule}/concolic_region_results.jsonl" false false false
  import_plan "${target_schedule}/execution_task_plan.jsonl" \
    "${target_schedule}/concolic_region_results.jsonl" \
    "${target_schedule}/concolic_region_summaries.jsonl" \
    "${target_schedule}"
  summary="${target_schedule}/concolic_region_summaries.jsonl"
  if ! jq -e -s --arg region "${region}" --arg task "${task}" \
      --arg instance "${instance}" \
      --arg goal "${goal}" '
      length == 1
      and .[0].regionId == $region
      and .[0].regionInstanceId == $instance
      and .[0].taskId == $task
      and .[0].goalId == $goal
      and .[0].relationallyComplete == true
      and .[0].goalKind == "TARGET_REACH_CLOSURE"
    ' "${summary}" >/dev/null; then
    die "target seed import is not one valid target-branch observation"
  fi
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_SCHEDULE_SUMMARIES="${summary}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${region}" --region-instance-id "${instance}" \
      --goal-id "${goal}")
  if ! jq -e -s --arg region "${region}" --arg instance "${instance}" \
      --arg goal "${goal}" '
      length == 1
      and .[0].regionId == $region
      and .[0].regionInstanceId == $instance
      and .[0].goalId == $goal
      and .[0].schemaVersion == 1
      and .[0].kind == "TARGET_BRANCH_SOLVER_QUERY"
      and .[0].readyForSolver == true
      and .[0].replayContract.kind == "BINARY_BRANCH_REPLAY_CONTRACT"
      and .[0].solverPathContext.kind == "NON_BRANCH_SOLVER_PATH_CONTEXT"
    ' "${target_schedule}/branch_queries.jsonl" >/dev/null; then
    die "target seed scheduler did not emit one solver-ready candidate query"
  fi
  echo "[three-thread-rpc] target seed query: ${target_schedule}/branch_queries.jsonl"
}

do_clean() {
  local allowed_root="${project_repo}/target"
  [[ "${work_root}" == "${allowed_root}/"* ]] \
    || die "refusing to clean work root outside ${allowed_root}: ${work_root}"
  [[ "${work_root}" != "${allowed_root}" ]] \
    || die "refusing to clean the complete project target directory"
  [[ ! -L "${work_root}" ]] \
    || die "refusing to clean symlinked work root: ${work_root}"
  if [[ -e "${work_root}" && ! -d "${work_root}" ]]; then
    die "work root exists but is not a directory: ${work_root}"
  fi
  if [[ -d "${work_root}" ]]; then
    find "${work_root}" -mindepth 1 -delete
  fi
  echo "[three-thread-rpc] cleaned ${work_root}"
}

require_clean_work_root() {
  local first_entry=""
  if [[ -d "${work_root}" ]]; then
    first_entry=$(find "${work_root}" -mindepth 1 -print -quit)
  fi
  [[ -z "${first_entry}" ]] || die \
    "all requires an empty fixture work root; run '$0 clean' first"
}

write_candidate_manifest() {
  local smt="${candidate_root}/candidate.smt2"
  local composition="${candidate_root}/candidate_composition_manifest.json"
  local reach="${candidate_root}/candidate_boolean_model.json"
  local output="${candidate_root}/candidate_result_manifest.json"
  local status
  require_file "candidate SMT" "${smt}"
  require_file "candidate composition manifest" "${composition}"
  require_file "candidate reach model" "${reach}"
  status=$(jq -er '.reachCondition.reachability
    | select(. == "REACHABLE" or . == "UNREACHABLE")' "${reach}") \
    || die "candidate reach model has no exact reachability status"
  jq -n \
    --arg status "${status}" \
    --arg smt "$(realpath -m -- "${smt}")" \
    --arg smt_hash "$(sha256_file "${smt}")" \
    --arg composition "$(realpath -m -- "${composition}")" \
    --arg composition_hash "$(sha256_file "${composition}")" \
    --arg reach "$(realpath -m -- "${reach}")" \
    --arg reach_hash "$(sha256_file "${reach}")" '
      {
        schemaVersion: 2,
        kind: "CONCOLIC_CANDIDATE_RESULT",
        state: "CANDIDATE_READY",
        trustState: "CANDIDATE_ONLY",
        reachability: $status,
        candidateSmtArtifact: {path: $smt, sha256: $smt_hash},
        compositionManifestArtifact: {path: $composition,
          sha256: $composition_hash},
        candidateReachModelArtifact: {path: $reach, sha256: $reach_hash}
      }
    ' >"${output}"
  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_CANDIDATE_RESULT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.reachability == "REACHABLE"
      or .reachability == "UNREACHABLE")
  ' "${output}" >/dev/null || die "candidate manifest is incomplete"
}

do_candidate_smt() {
  require_clean_work_root
  do_prepare
  do_analyze
  do_trace
  do_discover
  do_schedule_target
  do_seed_target
  do_explore_target
  run_producers_parallel
  do_candidate_compose
}

do_candidate() {
  do_candidate_smt
  do_candidate_solve
  write_candidate_manifest
  echo "[three-thread-rpc] complete Z3-checked candidate workflow"
}

do_all() { do_candidate; }

command_name=${1:-help}
shift || true
case "${command_name}" in
  help|-h|--help) usage ;;
  prepare) do_prepare ;;
  analyze) do_analyze ;;
  trace) do_trace ;;
  discover) [[ $# -eq 0 ]] || die "discover takes no arguments"; do_discover ;;
  schedule-target) [[ $# -eq 0 ]] || die "schedule-target takes no arguments"; do_schedule_target ;;
  seed-target) [[ $# -eq 0 ]] || die "seed-target takes no arguments"; do_seed_target ;;
  explore-target) [[ $# -eq 0 ]] || die "explore-target takes no arguments"; do_explore_target ;;
  schedule-producer) [[ $# -eq 1 ]] || die "schedule-producer needs one discovered channel"; do_schedule_producer "$1" ;;
  instrument) [[ $# -eq 1 ]] || die "instrument needs one discovered channel"; do_instrument "$1" ;;
  replay)
    [[ $# -ge 1 && $# -le 3 ]] || die "replay needs CHANNEL [b1 b2]"
    run_custom_java "$1" "${2:-false}" "${3:-false}"
    ;;
  import) [[ $# -eq 1 ]] || die "import needs one discovered channel"; do_import "$1" ;;
  explore-producer) [[ $# -eq 1 ]] || die "explore-producer needs one discovered channel"; do_explore_producer "$1" ;;
  candidate-compose) [[ $# -eq 0 ]] || die "candidate-compose takes no arguments"; do_candidate_compose ;;
  candidate-smt) [[ $# -eq 0 ]] || die "candidate-smt takes no arguments"; do_candidate_smt ;;
  candidate-solve) [[ $# -eq 0 ]] || die "candidate-solve takes no arguments"; do_candidate_solve ;;
  candidate-manifest) [[ $# -eq 0 ]] || die "candidate-manifest takes no arguments"; write_candidate_manifest ;;
  candidate) [[ $# -eq 0 ]] || die "candidate takes no arguments"; do_candidate ;;
  smoke)
    do_prepare
    do_analyze
    do_trace
    do_discover
    do_schedule_target
    ;;
  all) [[ $# -eq 0 ]] || die "all takes no arguments"; do_all ;;
  clean) [[ $# -eq 0 ]] || die "clean takes no arguments"; do_clean ;;
  *) die "unknown command: ${command_name}" ;;
esac
