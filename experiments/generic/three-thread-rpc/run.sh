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
static_regions=$(configured_value static_regions)
static_graph=$(configured_value static_graph)
runtime_edge_validations=$(configured_value runtime_edge_validations)
graphchecker_jar=$(configured_value graphchecker_jar)
maven_bin=$(configured_value maven_bin)
fixture_class=$(workflow_property fixture_class)
fixture_test_class=$(workflow_property fixture_test_class)
trace_test=$(workflow_property trace_test)
custom_jdk_docker_image=$(workflow_property custom_jdk_docker_image)
fixture_variant=$(workflow_property fixture_variant false)
fixture_package=${fixture_class%.*}
fixture_package=${fixture_package//./\/}
fixture_simple_class=${fixture_class##*.}
topology_file=$(configured_value rpc_mapping_file)
activation_plan=$(configured_value runtime_activation_plan)
target_schedule=$(configured_value schedule_output_dir)
target_classes="${work_root}/concolic-target-classes"
producer_campaign_root="${work_root}/producer-campaign"
bootstrap_root="${work_root}/bootstrap"
campaign_root="${work_root}/campaign"
final_root="${work_root}/final"
campaign_snapshot_regions=""
campaign_snapshot_activations=""
campaign_snapshot_edges=""
campaign_snapshot_roots=""
campaign_snapshot_summaries=""
campaign_snapshot_path_records=""
campaign_snapshot_static_graph=""
campaign_snapshot_completion=""

usage() {
  cat <<'EOF'
Usage: experiments/generic/three-thread-rpc/run.sh <command> [args]

  test                    Run the three-real-thread JUnit contract
  prepare                 Build GraphChecker and isolate fixture classes
  analyze                 Static analysis plus trace instrumentation
  trace                   Run a non-bug concrete discovery execution
  discover                Resolve channel producers and target from evidence
  schedule-target         Schedule one unforced consumer target seed
  seed-target             Capture/import the unforced target seed query
  schedule-producer CH    Schedule one declared channel's OUTPUT_CLOSURE
  instrument CH           Instrument that producer's scheduled activation
  replay CH [b1 b2]       Run one real custom-JDK concolic capture
  import CH               Strictly import that producer capture
  explore-producer CH     Close and merge one producer path worklist
  bootstrap-compose       Compose producer relations with the target seed
  bootstrap-project       Derive the SAT Boolean model and replay ALL bundle
  bootstrap-replay        Naturally reach/import/reschedule the target bug
  campaign                Close the bounded fixed-runtime concolic campaign
  final                   Final compose + relationship proof + reach report
  smoke                   test + prepare + analyze + trace + discovery + target
  all                     Run the complete clean-worktree workflow above
  clean                   Remove only the configured fixture work products

No command writes SMT text or a reachability formula. RPC topology is declared
by rpc_mapping_file; runtime read-from evidence still comes from the trace.
Only the validated final composition is allowed to publish the reach report;
the bootstrap Boolean report is explicitly replay-only.
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

validate_discovery_inputs() {
  require_command jq
  require_file "RPC topology" "${topology_file}"
  require_file "runtime activation plan" "${activation_plan}"
  jq -e -s '
    length > 0
    and all(.[];
      .kind == "RPC_TOPOLOGY"
      and (.channel | type == "string" and length > 0)
      and (.channel | test("^[A-Za-z0-9._-]+$"))
      and (.fromCell | type == "string" and length > 0)
      and (.toCell | type == "string" and length > 0))
    and (([.[].channel | ascii_downcase] | unique | length) == length)
  ' "${topology_file}" >/dev/null \
    || die "RPC topology must contain unique, safe, complete channel rows"
  jq -e -s '
    length > 0
    and all(.[];
      (.activationId | type == "string" and length > 0)
      and (.regionId | type == "string" and length > 0)
      and (.captureGoal.kind | type == "string" and length > 0))
    and (([.[].activationId] | unique | length) == length)
  ' "${activation_plan}" >/dev/null \
    || die "runtime activation plan has missing or duplicate identities"
}

declared_channels() {
  jq -r '.channel' "${topology_file}"
}

declared_channel() {
  local requested=$1
  local -a matches
  mapfile -t matches < <(jq -r --arg requested "${requested}" '
    select((.channel | ascii_downcase) == ($requested | ascii_downcase))
    | .channel
  ' "${topology_file}")
  [[ ${#matches[@]} -eq 1 ]] \
    || die "channel is not declared exactly once in rpc-topology.jsonl: ${requested}"
  printf '%s\n' "${matches[0]}"
}

topology_value() {
  local channel=$1
  local property=$2
  local value
  value=$(jq -er -s --arg channel "${channel}" --arg property "${property}" '
    .[] | select(.channel == $channel) | .[$property]
  ' "${topology_file}") \
    || die "topology property ${property} is missing for channel ${channel}"
  [[ -n "${value}" ]] \
    || die "topology property ${property} is empty for channel ${channel}"
  printf '%s\n' "${value}"
}

producer_binding() {
  local requested=$1
  local channel from_cell to_cell
  local -a matches
  channel=$(declared_channel "${requested}") || return $?
  from_cell=$(topology_value "${channel}" fromCell) || return $?
  to_cell=$(topology_value "${channel}" toCell) || return $?
  mapfile -t matches < <(jq -r \
    --arg fromCell "${from_cell}" --arg toCell "${to_cell}" '
    . as $activation
    | select(
        .captureGoal.kind == "OUTPUT_CLOSURE"
        and .requestedOutput.cell == $fromCell
        and any(.edgeBindings[]?;
          .fromRegion == $activation.regionId
          and .fromOutputCell == $fromCell
          and .rawFromPort == $toCell
          and .canonicalOutputAliasUsed == true
          and .aliasProofComplete == true))
    | [.regionId, .activationId] | @tsv
  ' "${activation_plan}")
  [[ ${#matches[@]} -eq 1 ]] || die \
    "expected one evidence-backed OUTPUT_CLOSURE for channel ${channel}; found ${#matches[@]}"
  printf '%s\n' "${matches[0]}"
}

target_binding() {
  local channel producer_region producer_activation from_cell to_cell
  local target_region target_activation
  local binding
  local -a channels downstream_regions target_regions target_activations
  mapfile -t channels < <(declared_channels)
  [[ ${#channels[@]} -gt 0 ]] || die "RPC topology declares no channels"
  target_regions=()
  for channel in "${channels[@]}"; do
    binding=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r producer_region producer_activation \
      <<< "${binding}"
    from_cell=$(topology_value "${channel}" fromCell) || return $?
    to_cell=$(topology_value "${channel}" toCell) || return $?
    mapfile -t downstream_regions < <(jq -s -r \
      --arg activation "${producer_activation}" \
      --arg producerRegion "${producer_region}" \
      --arg fromCell "${from_cell}" \
      --arg toCell "${to_cell}" '
      . as $plans
      | $plans[]
      | select(.activationId == $activation and .regionId == $producerRegion)
      | .edgeBindings[]?
      | select(.fromRegion == $producerRegion
          and .fromOutputCell == $fromCell
          and .rawFromPort == $toCell
          and .canonicalOutputAliasUsed == true
          and .aliasProofComplete == true)
      | .toRegion as $candidate
      | select(any($plans[];
          .regionId == $candidate
          and .captureGoal.kind == "TARGET_BRANCH"
          and .replayable == true))
      | $candidate
    ' "${activation_plan}" | sort -u)
    [[ ${#downstream_regions[@]} -eq 1 ]] || die \
      "channel ${channel} must have one exact producer-to-target binding"
    target_regions+=("${downstream_regions[0]}")
  done
  mapfile -t target_regions < <(printf '%s\n' "${target_regions[@]}" | sort -u)
  [[ ${#target_regions[@]} -eq 1 ]] || die \
    "declared RPC channels do not converge on one runtime target region"
  target_region=${target_regions[0]}
  mapfile -t target_activations < <(jq -r --arg region "${target_region}" '
    select(.regionId == $region
        and .captureGoal.kind == "TARGET_BRANCH"
        and .replayable == true)
    | .activationId
  ' "${activation_plan}")
  [[ ${#target_activations[@]} -eq 1 ]] || die \
    "expected one TARGET_BRANCH activation for discovered target ${target_region}"
  target_activation=${target_activations[0]}
  printf '%s\t%s\n' "${target_region}" "${target_activation}"
}

channel_schedule() {
  local channel
  channel=$(declared_channel "$1") || return $?
  printf '%s/schedule-%s\n' "${work_root}" \
    "$(printf '%s' "${channel}" | tr '[:upper:]' '[:lower:]')"
}

channel_classes() {
  local channel
  channel=$(declared_channel "$1") || return $?
  printf '%s/concolic-%s-classes\n' "${work_root}" \
    "$(printf '%s' "${channel}" | tr '[:upper:]' '[:lower:]')"
}

scheduled_activation() {
  local requested=$1
  local channel region source_activation from_cell schedule binding
  local -a matches
  channel=$(declared_channel "${requested}") || return $?
  binding=$(producer_binding "${channel}") || return $?
  IFS=$'\t' read -r region source_activation \
    <<< "${binding}"
  from_cell=$(topology_value "${channel}" fromCell) || return $?
  schedule=$(channel_schedule "${channel}") || return $?
  require_file "scheduled producer activation" \
    "${schedule}/scheduled_activation_plan.jsonl"
  mapfile -t matches < <(jq -r \
    --arg region "${region}" --arg sourceActivation "${source_activation}" \
    --arg fromCell "${from_cell}" '
    select(
      .activationBundleMemberRole == "PRIMARY"
      and .activationId == $sourceActivation
      and .regionId == $region
      and .captureGoal.kind == "OUTPUT_CLOSURE"
      and .requestedOutput.cell == $fromCell)
    | .activationId
  ' "${schedule}/scheduled_activation_plan.jsonl")
  [[ ${#matches[@]} -eq 1 ]] || die \
    "expected one scheduled PRIMARY activation for channel ${channel}"
  printf '%s\n' "${matches[0]}"
}

scheduled_target_activation() {
  local region source_activation binding
  local -a matches
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region source_activation <<< "${binding}"
  require_file "scheduled target activation" \
    "${target_schedule}/scheduled_activation_plan.jsonl"
  mapfile -t matches < <(jq -r \
    --arg region "${region}" --arg activation "${source_activation}" '
    select(
      .activationBundleMemberRole == "PRIMARY"
      and .regionId == $region
      and .activationId == $activation
      and .captureGoal.kind == "TARGET_BRANCH")
    | .activationId
  ' "${target_schedule}/scheduled_activation_plan.jsonl")
  [[ ${#matches[@]} -eq 1 ]] || die \
    "expected one scheduled PRIMARY target activation; found ${#matches[@]}"
  printf '%s\n' "${matches[0]}"
}

do_test() {
  (cd "${graphchecker_dir}" && "${maven_bin}" -q \
    -Dtest="${fixture_test_class}" \
    test)
}

do_prepare() {
  (cd "${graphchecker_dir}" && "${maven_bin}" -q -DskipTests package)
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
  require_file "runtime activations" "${activation_plan}"
  require_file "runtime edge validations" "${runtime_edge_validations}"
}

do_discover() {
  local channel region activation target_region target_activation
  local binding
  local -a channels
  validate_discovery_inputs
  mapfile -t channels < <(declared_channels)
  printf 'kind\tchannel\tregion\tactivation\n'
  for channel in "${channels[@]}"; do
    binding=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r region activation <<< "${binding}"
    printf 'producer\t%s\t%s\t%s\n' \
      "${channel}" "${region}" "${activation}"
  done
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r target_region target_activation <<< "${binding}"
  printf 'target\t-\t%s\t%s\n' "${target_region}" "${target_activation}"
}

do_schedule_target() {
  local region activation binding
  validate_discovery_inputs
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region activation <<< "${binding}"
  (cd "${graphchecker_dir}" && "${runner}" --config "${config}" schedule \
    --region-id "${region}" --activation-id "${activation}")
  jq -e -s '
    length == 1
    and ((.[0].forcedBranches // []) | length) == 0
    and .[0].branchOverrideProhibited == true
  ' "${target_schedule}/scheduled_activation_plan.jsonl" >/dev/null \
    || die "target seed schedule permits a branch override"
}

do_schedule_producer() {
  local requested=$1
  local channel
  local region activation output binding
  validate_discovery_inputs
  channel=$(declared_channel "${requested}") || return $?
  binding=$(producer_binding "${channel}") || return $?
  IFS=$'\t' read -r region activation <<< "${binding}"
  output=$(channel_schedule "${channel}") || return $?
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_SCHEDULE_OUTPUT_DIR="${output}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${region}" --activation-id "${activation}" \
      --capture-only true --multiple-per-region true)
}

do_instrument() {
  local requested=$1
  local channel schedule classes activation static_output channel_slug
  validate_discovery_inputs
  channel=$(declared_channel "${requested}") || return $?
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  activation=$(scheduled_activation "${channel}") || return $?
  channel_slug=$(printf '%s' "${channel}" | tr '[:upper:]' '[:lower:]')
  static_output="${work_root}/concolic-${channel_slug}-static"
  instrument_plan "${schedule}/scheduled_activation_plan.jsonl" \
    "${activation}" "${classes}" "${static_output}"
}

instrument_plan() {
  local plan=$1
  local selection=$2
  local classes=$3
  local static_output=$4
  local selected="${selection}"
  local select_all=false
  require_file "concolic activation plan" "${plan}"
  [[ -s "${plan}" ]] || die "concolic activation plan is empty: ${plan}"
  if plan_requires_all "${plan}"; then
    select_all=true
    selected=""
  elif [[ "${selected}" == "ALL" ]]; then
    die "ALL selection requires activationSelectionRequired=ALL plan rows: ${plan}"
  fi
  [[ "${select_all}" == "true" || -n "${selected}" ]] \
    || die "exact activation selection is empty for non-bundle plan: ${plan}"
  if [[ "${select_all}" == "true" ]]; then
    (cd "${graphchecker_dir}" && \
      env -u CAUSYNTH_CONCOLIC_ACTIVATION_ID \
      CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${classes}" \
      CAUSYNTH_OUTPUT_DIR="${static_output}" \
      CAUSYNTH_INSTRUMENT_CONCOLIC=true \
      CAUSYNTH_CONCOLIC_ACTIVATION_PLAN="${plan}" \
      "${runner}" --config "${config}" analyze)
  else
    (cd "${graphchecker_dir}" && \
      CAUSYNTH_INSTRUMENTED_CLASSES_DIR="${classes}" \
      CAUSYNTH_OUTPUT_DIR="${static_output}" \
      CAUSYNTH_INSTRUMENT_CONCOLIC=true \
      CAUSYNTH_CONCOLIC_ACTIVATION_PLAN="${plan}" \
      CAUSYNTH_CONCOLIC_ACTIVATION_ID="${selected}" \
      "${runner}" --config "${config}" analyze)
  fi
}

plan_requires_all() {
  local plan=$1
  require_command jq
  jq -e -s 'any(.[]; .activationSelectionRequired == "ALL")' \
    "${plan}" >/dev/null
}

run_custom_plan() {
  local plan=$1
  local selection=$2
  local classes=$3
  local results=$4
  local b1=$5
  local b2=$6
  local accept_nonzero=$7
  local jdk java_path selected replay_status select_all=false
  require_file "concolic activation plan" "${plan}"
  require_directory "concolic fixture classes" "${classes}"
  [[ ! -e "${results}" ]] || die "capture output already exists: ${results}"
  mkdir -p "$(dirname "${results}")"
  jdk=$(configured_value custom_jdk_home) || return $?
  java_path="${jdk}/bin/java"
  [[ -x "${java_path}" ]] || die "custom JDK is not built: ${java_path}"
  selected="${selection}"
  if plan_requires_all "${plan}"; then
    select_all=true
    selected=""
  elif [[ "${selected}" == "ALL" ]]; then
    die "ALL selection requires activationSelectionRequired=ALL plan rows: ${plan}"
  fi
  [[ "${select_all}" == "true" || -n "${selected}" ]] \
    || die "exact activation selection is empty for non-bundle plan: ${plan}"

  local -a java_args fixture_variant_args
  fixture_variant_args=()
  if [[ -n "${fixture_variant}" ]]; then
    fixture_variant_args+=(
      -Dcausynth.fixture.variant="${fixture_variant}"
    )
  fi
  java_args=(
    -Xint
    -Dcausynth.trace.test="${trace_test}"
    -Dcausynth.concolic.activation.plan="${plan}"
    -Dcausynth.concolic.results="${results}"
    "${fixture_variant_args[@]}"
    -cp "${classes}:${graphchecker_jar}"
    "${fixture_class}" "${b1}" "${b2}"
  )
  if [[ "${select_all}" != "true" ]]; then
    java_args=(
      "${java_args[@]:0:3}"
      -Dcausynth.concolic.activation.id="${selected}"
      "${java_args[@]:3}"
    )
  fi
  if "${java_path}" -version >/dev/null 2>&1; then
    if (cd "${graphchecker_dir}" && env -u CAUSYNTH_CONCOLIC_ACTIVATION_ID \
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
    if [[ "${select_all}" == "true" ]]; then
      local -a primary_activations
      mapfile -t primary_activations < <(jq -r '
        select(.activationBundleMemberRole == "PRIMARY") | .activationId
      ' "${plan}")
      [[ ${#primary_activations[@]} -eq 1 ]] \
        || die "nonzero bundle replay requires one PRIMARY row"
      jq -e -s --arg activation "${primary_activations[0]}" '
        [.[] | select(.activationId == $activation)] | length == 1
      ' "${results}" >/dev/null \
        || die "nonzero replay emitted no raw PRIMARY target row"
    else
      jq -e -s --arg activation "${selected}" '
        [.[] | select(.activationId == $activation)] | length == 1
      ' "${plan}" >/dev/null \
        || die "nonzero exact replay selection is not unique in its plan"
      jq -e -s --arg activation "${selected}" '
        [.[] | select(.activationId == $activation)] | length == 1
      ' "${results}" >/dev/null \
        || die "nonzero exact replay emitted no selected raw result row"
    fi
    echo "[three-thread-rpc] accepted expected nonzero replay exit ${replay_status}; selected raw evidence exists"
  fi
}

run_custom_java() {
  local requested=$1
  local b1=$2
  local b2=$3
  local channel schedule classes activation results
  validate_discovery_inputs
  channel=$(declared_channel "${requested}") || return $?
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  activation=$(scheduled_activation "${channel}") || return $?
  results="${schedule}/concolic_region_results.jsonl"
  run_custom_plan "${schedule}/scheduled_activation_plan.jsonl" \
    "${activation}" "${classes}" "${results}" "${b1}" "${b2}" false
}

do_import() {
  local requested=$1
  local channel
  local schedule
  validate_discovery_inputs
  channel=$(declared_channel "${requested}") || return $?
  schedule=$(channel_schedule "${channel}") || return $?
  scheduled_activation "${channel}" >/dev/null
  import_plan "${schedule}/scheduled_activation_plan.jsonl" \
    "${schedule}/concolic_region_results.jsonl" \
    "${schedule}/concolic_region_summaries.jsonl" "${schedule}"
}

import_plan() {
  local plan=$1
  local results=$2
  local summaries=$3
  local output_dir=$4
  require_file "import activation plan" "${plan}"
  [[ -s "${results}" ]] || die "raw concolic result is missing or empty: ${results}"
  mkdir -p "${output_dir}"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_RAW_RESULTS="${results}" \
    CAUSYNTH_IMPORT_ACTIVATION_PLAN="${plan}" \
    CAUSYNTH_IMPORTED_SUMMARIES="${summaries}" \
    CAUSYNTH_IMPORT_DIAGNOSTICS="${output_dir}/concolic_import_diagnostics.jsonl" \
    CAUSYNTH_SUMMARY_CACHE_DIR="${output_dir}/concolic-summary-cache" \
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
      reduce .[] as $row (
        {order: [], rows: {}};
        ($row[$identity] // "") as $key
        | if ($row | type) != "object" or ($key | type) != "string"
            or ($key | length) == 0 then
            error("missing JSONL identity " + $identity)
          elif (.rows | has($key)) and .rows[$key] != $row then
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
  local channel
  channel=$(declared_channel "$1") || return $?
  printf '%s/%s\n' "${producer_campaign_root}" \
    "$(printf '%s' "${channel}" | tr '[:upper:]' '[:lower:]')"
}

do_explore_producer() {
  local requested=$1
  local channel schedule classes campaign region source_activation binding
  local summaries activations records planner_dir replay_activation raw imported
  local replay_verification
  local z3 solver_timeout planner_status query_key iteration selection_dir
  local -A seen_queries=()
  local -a _replay_activations=()
  validate_discovery_inputs
  channel=$(declared_channel "${requested}") || return $?
  binding=$(producer_binding "${channel}") || return $?
  IFS=$'\t' read -r region _ <<< "${binding}"
  schedule=$(channel_schedule "${channel}") || return $?
  classes=$(channel_classes "${channel}") || return $?
  source_activation=$(scheduled_activation "${channel}") || return $?
  require_file "producer seed summary" \
    "${schedule}/concolic_region_summaries.jsonl"
  require_directory "producer concolic classes" "${classes}"
  campaign=$(producer_campaign_directory "${channel}") || return $?
  [[ ! -e "${campaign}" ]] \
    || die "producer campaign already exists: ${campaign}"
  mkdir -p "${campaign}"
  summaries="${campaign}/combined_region_summaries.jsonl"
  activations="${campaign}/combined_activation_plan.jsonl"
  records="${campaign}/path_exploration_records.jsonl"
  : >"${records}"
  combine_jsonl_unique summaryId "${summaries}" \
    "${schedule}/concolic_region_summaries.jsonl"
  combine_jsonl_unique activationId "${activations}" \
    "${schedule}/scheduled_activation_plan.jsonl"
  z3=$(configured_value z3_bin) || return $?
  solver_timeout=$(configured_value solver_timeout_ms) || return $?

  iteration=1
  while true; do
    planner_dir=$(printf '%s/iteration-%04d' "${campaign}" "${iteration}")
    mkdir -p "${planner_dir}"
    set +e
    run_graphchecker_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
      --summaries "${summaries}" \
      --activations "${activations}" \
      --records "${records}" \
      --output-dir "${planner_dir}" \
      --z3 "${z3}" \
      --solver-timeout-ms "${solver_timeout}" \
      --region-id "${region}"
    planner_status=$?
    set -e
    require_file "producer path planner manifest" \
      "${planner_dir}/path_flip_plan_manifest.json"
    require_file "producer path worklist manifest" \
      "${planner_dir}/region_path_manifest.json"
    if [[ "${planner_status}" -eq 2 ]] \
        && jq -e '.status == "AMBIGUOUS_PATH_FLIP"
          and .selectedTaskCount > 1' \
          "${planner_dir}/path_flip_plan_manifest.json" >/dev/null; then
      query_key=$(jq -er -s \
        'sort_by(.queryKey) | .[0].queryKey' \
        "${planner_dir}/region_path_worklist.jsonl") \
        || die "ambiguous producer worklist has no deterministic query key"
      selection_dir="${planner_dir}/selected"
      mkdir -p "${selection_dir}"
      set +e
      run_graphchecker_main \
        edu.uva.liftlab.graphchecker.concolic.ConcolicPathFlipPlanner \
        --summaries "${summaries}" \
        --activations "${activations}" \
        --records "${records}" \
        --output-dir "${selection_dir}" \
        --z3 "${z3}" \
        --solver-timeout-ms "${solver_timeout}" \
        --region-id "${region}" \
        --query-key "${query_key}"
      planner_status=$?
      set -e
      planner_dir=${selection_dir}
      require_file "selected producer path planner manifest" \
        "${planner_dir}/path_flip_plan_manifest.json"
      require_file "selected producer path worklist manifest" \
        "${planner_dir}/region_path_manifest.json"
    fi
    if [[ "${planner_status}" -eq 2 ]]; then
      if jq -e '.status == "PATH_FLIP_NOT_REPLAYABLE"
          and .solverStatus == "UNSAT"
          and .selectedTaskCount == 1' \
          "${planner_dir}/path_flip_plan_manifest.json" >/dev/null; then
        query_key=$(jq -er '.queryKey' \
          "${planner_dir}/path_flip_plan_manifest.json") \
          || die "UNSAT producer path flip has no query identity"
        [[ -z "${seen_queries[${query_key}]+present}" ]] \
          || die "producer path worklist repeated UNSAT query ${query_key}"
        seen_queries[${query_key}]=present
        jq -e --arg query "${query_key}" '
          .status == "UNSAT" and .queryKey == $query
        ' "${planner_dir}/path_flip_solver_result.json" >/dev/null \
          || die "producer UNSAT result does not match its selected query"
        [[ ! -s "${planner_dir}/activation_plan.jsonl" ]] \
          || die "UNSAT producer path unexpectedly emitted a replay"
        jq -c '.' "${planner_dir}/path_flip_solver_result.json" \
          >>"${records}"
        echo "[three-thread-rpc] producer path proved UNSAT: ${query_key}"
        iteration=$((iteration + 1))
        continue
      fi
      jq -e '
        .status == "NO_MATCHING_PATH_FLIP"
        and .selectedTaskCount == 0
      ' "${planner_dir}/path_flip_plan_manifest.json" >/dev/null \
        || die "producer planner stopped without closing its selection"
      jq -e '.complete == true' \
        "${planner_dir}/region_path_manifest.json" >/dev/null \
        || die "producer path worklist is not closed"
      [[ ! -s "${planner_dir}/activation_plan.jsonl" ]] \
        || die "closed producer worklist retained an executable replay"
      cp -f "${planner_dir}/region_path_manifest.json" \
        "${campaign}/region_path_manifest.json"
      break
    fi
    [[ "${planner_status}" -eq 0 ]] \
      || die "producer path planner failed with exit ${planner_status}"
    jq -e '
      .complete == true
      and .status == "PATH_FLIP_REPLAY_READY"
      and .selectedTaskCount == 1
      and .branchOverrideAllowed == false
      and .runtimeValidationRequired == true
    ' "${planner_dir}/path_flip_plan_manifest.json" >/dev/null \
      || die "producer path flip is not one solver-backed replay"
    query_key=$(jq -er '.queryKey' \
      "${planner_dir}/path_flip_plan_manifest.json") \
      || die "producer path flip has no query identity"
    [[ -z "${seen_queries[${query_key}]+present}" ]] \
      || die "producer path worklist repeated query ${query_key}"
    seen_queries[${query_key}]=present
    replay_manifest_id=$(jq -er '.replayActivationId' \
      "${planner_dir}/path_flip_plan_manifest.json") \
      || die "producer path flip has no replay activation identity"
    mapfile -t _replay_activations < <(jq -r \
      --arg region "${region}" --arg replay "${replay_manifest_id}" '
      select(
        .activationId == $replay
        and .regionId == $region
        and .captureGoal.kind == "OUTPUT_CLOSURE"
        and .executionPhase == "REPLAY_OUTPUT_PATH_FLIP"
        and .replayMode == "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY"
        and .branchOverrideProhibited == true
        and .targetBranch.validationOnly == true
        and .targetBranch.branchOverrideAllowed == false
        and ((.modelAssignments // []) | length) > 0
        and ((.forcedBranches // []) | length) == 0
        and ((.replayMaterializations // []) | length) == 0
      )
      | .activationId
    ' "${planner_dir}/activation_plan.jsonl")
    [[ ${#_replay_activations[@]} -eq 1 ]] \
      || die "producer planner did not emit one unforced input-model replay"
    replay_activation=${_replay_activations[0]}
    raw="${planner_dir}/concolic_region_results.jsonl"
    imported="${planner_dir}/concolic_region_summaries.jsonl"
    replay_verification="${planner_dir}/path_replay_verification.json"
    run_custom_plan "${planner_dir}/activation_plan.jsonl" \
      "${replay_activation}" "${classes}" "${raw}" false false true
    import_plan "${planner_dir}/activation_plan.jsonl" "${raw}" \
      "${imported}" "${planner_dir}"
    run_graphchecker_main \
      edu.uva.liftlab.graphchecker.concolic.ConcolicPathReplayVerifier \
      --task "${planner_dir}/replay_validation_plan.json" \
      --activation-plan "${planner_dir}/activation_plan.jsonl" \
      --results "${raw}" \
      --summary "${imported}" \
      --output "${replay_verification}"
    jq -e --arg query "${query_key}" --arg region "${region}" \
      --arg activation "${replay_activation}" '
      .valid == true
      and .status == "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
      and .queryKey == $query
      and .regionId == $region
      and .activationId == $activation
      and (.observedPathKey | test("^[0-9a-f]{64}$"))
    ' "${replay_verification}" >/dev/null \
      || die "producer path replay did not pass the exact verifier"
    jq -c '.' "${replay_verification}" >>"${records}"
    combine_jsonl_unique summaryId "${campaign}/next_summaries.jsonl" \
      "${summaries}" "${imported}"
    mv -f "${campaign}/next_summaries.jsonl" "${summaries}"
    combine_jsonl_unique activationId "${campaign}/next_activations.jsonl" \
      "${activations}" "${planner_dir}/activation_plan.jsonl"
    mv -f "${campaign}/next_activations.jsonl" "${activations}"
    iteration=$((iteration + 1))
  done

  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.RegionSummaryMerger \
    --summaries "${summaries}" \
    --path-manifest "${campaign}/region_path_manifest.json" \
    --output "${campaign}/merged_region_summaries.jsonl" \
    --manifest "${campaign}/region_relation_merge_manifest.json"
  debug_merged_relation "${campaign}/merged_region_summaries.jsonl"
  jq -e '.complete == true and .mergedRelationCount == 1' \
    "${campaign}/region_relation_merge_manifest.json" >/dev/null \
    || die "producer guarded merge is incomplete for channel ${channel}"
  jq -e -s --arg region "${region}" '
    length == 1
    and .[0].regionId == $region
    and .[0].valid == true
    and .[0].relationallyComplete == true
    and .[0].regionRelation.complete == true
  ' "${campaign}/merged_region_summaries.jsonl" >/dev/null \
    || die "producer merged relation is not complete for channel ${channel}"
  echo "[three-thread-rpc] producer ${channel} path worklist closed after $((iteration - 1)) replay(s)"
}

declared_producer_regions() {
  local channel binding region
  local -a channels
  mapfile -t channels < <(declared_channels)
  for channel in "${channels[@]}"; do
    binding=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r region _ <<< "${binding}"
    printf '%s\n' "${region}"
  done
}

aggregate_producer_artifacts() {
  local channel campaign expected_regions actual_regions
  local -a channels merged_inputs summary_inputs activation_inputs
  [[ ! -e "${bootstrap_root}" ]] \
    || die "bootstrap output already exists: ${bootstrap_root}"
  mkdir -p "${bootstrap_root}"
  mapfile -t channels < <(declared_channels)
  [[ ${#channels[@]} -gt 0 ]] || die "RPC topology declares no producers"
  merged_inputs=()
  summary_inputs=()
  activation_inputs=()
  for channel in "${channels[@]}"; do
    campaign=$(producer_campaign_directory "${channel}") || return $?
    merged_inputs+=("${campaign}/merged_region_summaries.jsonl")
    summary_inputs+=("${campaign}/combined_region_summaries.jsonl")
    activation_inputs+=("${campaign}/combined_activation_plan.jsonl")
  done
  combine_jsonl_unique summaryId \
    "${bootstrap_root}/producer_merged_summaries.jsonl" \
    "${merged_inputs[@]}"
  combine_jsonl_unique summaryId \
    "${bootstrap_root}/producer_summary_ledger.jsonl" \
    "${summary_inputs[@]}"
  combine_jsonl_unique activationId \
    "${bootstrap_root}/producer_activation_ledger.jsonl" \
    "${activation_inputs[@]}"
  expected_regions=$(declared_producer_regions | sort -u)
  actual_regions=$(jq -r '.regionId' \
    "${bootstrap_root}/producer_merged_summaries.jsonl" | sort -u)
  [[ "${expected_regions}" == "${actual_regions}" ]] \
    || die "merged producer regions differ from runtime topology discovery"
  [[ "$(printf '%s\n' "${expected_regions}" | sed '/^$/d' | wc -l)" \
      -eq "${#channels[@]}" ]] \
    || die "declared channels do not resolve to distinct producer regions"
  jq -e -s --argjson expected "${#channels[@]}" '
    length == $expected
    and all(.[];
      .valid == true
      and .relationallyComplete == true
      and .regionRelation.complete == true)
  ' "${bootstrap_root}/producer_merged_summaries.jsonl" >/dev/null \
    || die "aggregated producer relations are incomplete"
}

do_bootstrap_compose() {
  local target_region target_activation binding channel producer_binding_row
  local producer_region
  local -a channels bounded_args
  require_file "target seed summary" \
    "${target_schedule}/concolic_region_summaries.jsonl"
  require_file "target bootstrap branch query" \
    "${target_schedule}/branch_queries.jsonl"
  require_file "target symbolic merge plan" \
    "${target_schedule}/symbolic_merge_plan.json"
  aggregate_producer_artifacts
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r target_region target_activation <<< "${binding}"
  mapfile -t channels < <(declared_channels)
  bounded_args=()
  for channel in "${channels[@]}"; do
    producer_binding_row=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r producer_region _ <<< "${producer_binding_row}"
    bounded_args+=(--bounded-upstream-region "${producer_region}")
  done
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_FATAL_QUERIES="${target_schedule}/branch_queries.jsonl" \
    CAUSYNTH_COMPOSE_SUMMARIES="${bootstrap_root}/producer_merged_summaries.jsonl:${target_schedule}/concolic_region_summaries.jsonl" \
    CAUSYNTH_MERGE_PLAN="${target_schedule}/symbolic_merge_plan.json" \
    CAUSYNTH_COMPOSED_SMT="${bootstrap_root}/composed_fatal.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${bootstrap_root}/composed_smt_manifest.json" \
    CAUSYNTH_RELATIONSHIP_CANDIDATES="${bootstrap_root}/symbolic_relationship_candidates.json" \
    CAUSYNTH_FATAL_REGION="${target_region}" \
    CAUSYNTH_FATAL_ACTIVATION_ID="${target_activation}" \
    "${runner}" --config "${config}" compose "${bounded_args[@]}")
  jq -e --argjson expected "${#channels[@]}" '
    .kind == "CONCOLIC_COMPOSED_SMT"
    and .compositionStage == "BOOTSTRAP"
    and .boundedComposition == true
    and ((.boundedUpstreamRegions // []) | length) == $expected
    and .structurallyComplete == true
    and .eligibleForBootstrapModel == true
    and .fatalReplayValidated == false
    and .complete == false
    and .eligibleToReportAutomaticRelationship == false
    and .caseProjectionCatalogComplete == true
  ' "${bootstrap_root}/composed_smt_manifest.json" >/dev/null \
    || die "composition is not a structurally complete bootstrap model"
  jq -e '
    .compositionStage == "BOOTSTRAP"
    and .structurallyComplete == true
    and .eligibleForBootstrapModel == true
    and .eligibleForAutomaticVerification == false
  ' "${bootstrap_root}/symbolic_relationship_candidates.json" >/dev/null \
    || die "bootstrap relationship catalog claims final eligibility"
}

do_bootstrap_project() {
  local z3 solver_timeout
  require_file "bootstrap SMT" "${bootstrap_root}/composed_fatal.smt2"
  require_file "bootstrap composition manifest" \
    "${bootstrap_root}/composed_smt_manifest.json"
  require_file "bootstrap relationship candidates" \
    "${bootstrap_root}/symbolic_relationship_candidates.json"
  z3=$(configured_value z3_bin) || return $?
  solver_timeout=$(configured_value solver_timeout_ms) || return $?
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_COMPOSED_SMT="${bootstrap_root}/composed_fatal.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${bootstrap_root}/composed_smt_manifest.json" \
    CAUSYNTH_RELATIONSHIP_CANDIDATES="${bootstrap_root}/symbolic_relationship_candidates.json" \
    CAUSYNTH_REACH_REPORT="${bootstrap_root}/bootstrap_boolean_model.json" \
    "${runner}" --config "${config}" reach \
      --mode BOOTSTRAP_REPLAY_MODEL)
  jq -e '
    .complete == true
    and .status == "COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL"
    and .extractionMode == "BOOTSTRAP_REPLAY_MODEL"
    and .replayBootstrapOnly == true
    and .reportableFinalReachCondition == false
    and .truthTableComplete == true
    and .satisfyingValuationCount > 0
  ' "${bootstrap_root}/bootstrap_boolean_model.json" >/dev/null \
    || die "bootstrap Boolean projection has no complete SAT replay model"
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicPrimitiveBootstrapProjector \
    --smt "${bootstrap_root}/composed_fatal.smt2" \
    --composition-manifest "${bootstrap_root}/composed_smt_manifest.json" \
    --reach-report "${bootstrap_root}/bootstrap_boolean_model.json" \
    --summaries "${bootstrap_root}/producer_summary_ledger.jsonl" \
    --activations "${bootstrap_root}/producer_activation_ledger.jsonl" \
    --target-activations "${target_schedule}/scheduled_activation_plan.jsonl" \
    --fatal-query "${target_schedule}/branch_queries.jsonl" \
    --output "${bootstrap_root}/activation_plan.jsonl" \
    --manifest "${bootstrap_root}/primitive_bootstrap_projection_manifest.json" \
    --z3 "${z3}" \
    --timeout-ms "${solver_timeout}"
  jq -e '
    .complete == true
    and .projectionComplete == true
    and .compositionStage == "BOOTSTRAP"
    and .activationSelection == "ALL"
    and .producerReplayActivationCount == .rootBooleanInputCount
    and .producerReplayActivationCount > 0
    and .downstreamModelAssignmentCount == 0
    and .downstreamReplayMaterializationCount == 0
    and .downstreamBranchOverrideCount == 0
    and .targetUnforcedReplayRequired == true
  ' "${bootstrap_root}/primitive_bootstrap_projection_manifest.json" >/dev/null \
    || die "primitive bootstrap projector did not emit a complete ALL model"
  jq -e -s --slurpfile manifest \
      "${bootstrap_root}/primitive_bootstrap_projection_manifest.json" '
    length == $manifest[0].activationBundleSize
    and all(.[]; .activationSelectionRequired == "ALL")
    and ([.[] | select(.activationBundleMemberRole == "PRIMARY")] | length) == 1
    and ([.[] | select(.activationBundleMemberRole == "REACHABILITY_SUPPORT")] | length)
      == $manifest[0].producerReplayActivationCount
    and all(.[] | select(.activationBundleMemberRole == "REACHABILITY_SUPPORT");
      ((.modelAssignments // []) | length) == 1
      and ((.forcedBranches // []) | length) == 0
      and ((.replayMaterializations // []) | length) == 0
      and .targetReplayRequired == false)
    and all(.[] | select(.activationBundleMemberRole == "PRIMARY");
      .activationId == $manifest[0].targetReplayActivationId
      and .executionPhase == "REPLAY_DIRECTED_TARGET"
      and .targetReplayRequired == true
      and .observationOnlyReplay == true
      and ((.modelAssignments // []) | length) == 0
      and ((.forcedBranches // []) | length) == 0
      and ((.replayMaterializations // []) | length) == 0
      and (.directedTargetQuery | type) == "object"
      and (.targetBranch | type) == "object")
  ' "${bootstrap_root}/activation_plan.jsonl" >/dev/null \
    || die "primitive bootstrap activation bundle violates replay policy"
}

do_bootstrap_replay() {
  local plan="${bootstrap_root}/activation_plan.jsonl"
  local results="${bootstrap_root}/concolic_region_results.jsonl"
  local summaries="${bootstrap_root}/concolic_region_summaries.jsonl"
  local validated_schedule="${bootstrap_root}/validated-target-schedule"
  local binding target_region target_activation
  require_file "primitive bootstrap activation plan" "${plan}"
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r target_region target_activation <<< "${binding}"
  instrument_plan "${plan}" ALL \
    "${bootstrap_root}/concolic-classes" \
    "${bootstrap_root}/concolic-static"
  run_custom_plan "${plan}" ALL \
    "${bootstrap_root}/concolic-classes" "${results}" \
    false false true
  import_plan "${plan}" "${results}" "${summaries}" "${bootstrap_root}"
  jq -e -s --arg region "${target_region}" \
      --arg activation "${target_activation}" '
    [.[] | select(
      .regionId == $region and .activationId == $activation)] as $target
    | ($target | length) == 1
      and $target[0].valid == true
      and $target[0].targetReplayValidated == true
      and $target[0].branchOverrideUsed == false
      and $target[0].executionAdmission.required == true
      and $target[0].executionAdmission.valid == true
      and $target[0].executionAdmission.branchOverrideAccepted == false
      and $target[0].executionAdmission.authority
        == "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION"
  ' "${summaries}" >/dev/null \
    || die "bootstrap target replay was not admitted as natural bug evidence"
  jq -c -s --arg region "${target_region}" \
      --arg activation "${target_activation}" '
    [.[] | select(.regionId == $region and .activationId == $activation)]
    | if length == 1 then .[0]
      else error("validated target summary is not unique") end
  ' "${summaries}" >"${bootstrap_root}/validated_target_summary.jsonl"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_SCHEDULE_OUTPUT_DIR="${validated_schedule}" \
    CAUSYNTH_SCHEDULE_SUMMARIES="${summaries}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${target_region}" \
      --activation-id "${target_activation}")
  jq -e -s --arg region "${target_region}" \
      --arg activation "${target_activation}" '
    length == 1
    and .[0].regionId == $region
    and .[0].activationId == $activation
    and .[0].readyForSolver == true
    and .[0].readyForReplay == false
    and .[0].replayAlreadyValidated == true
    and .[0].targetReplayValidated == true
    and ((.[0].validatedSummaryId // "") | length) > 0
    and ((.[0].replayValidationAuthority // "") | length) > 0
  ' "${validated_schedule}/branch_queries.jsonl" >/dev/null \
    || die "scheduler did not retain the replay-validated target query"
  echo "[three-thread-rpc] natural target replay validated: ${validated_schedule}/branch_queries.jsonl"
}

do_campaign_capture() {
  local plan=${CAUSYNTH_CAMPAIGN_ACTIVATION_PLAN:-}
  local selection=${CAUSYNTH_CAMPAIGN_ACTIVATION_ID:-}
  local results=${CAUSYNTH_CAMPAIGN_RESULTS:-}
  local discovery_mode=${CAUSYNTH_CAMPAIGN_RUNTIME_DISCOVERY_MODE:-}
  local execution_dir accept_nonzero=false
  [[ -n "${plan}" && -n "${selection}" && -n "${results}" ]] \
    || die "campaign-capture requires campaign activation/result environment"
  [[ "${discovery_mode}" == "FIXED_VALIDATED_GRAPH" ]] \
    || die "three-thread campaign only admits FIXED_VALIDATED_GRAPH executions"
  require_file "campaign attempt activation plan" "${plan}"
  execution_dir=$(dirname "${results}")
  if plan_requires_all "${plan}"; then
    [[ "${selection}" == "ALL" ]] \
      || die "campaign ALL bundle was not announced by the runner"
    accept_nonzero=true
  else
    [[ "${selection}" != "ALL" ]] \
      || die "campaign exact replay unexpectedly selected ALL"
  fi
  instrument_plan "${plan}" "${selection}" \
    "${execution_dir}/concolic-classes" \
    "${execution_dir}/concolic-static"
  run_custom_plan "${plan}" "${selection}" \
    "${execution_dir}/concolic-classes" "${results}" \
    false false "${accept_nonzero}"
}

do_campaign() {
  local z3 solver_timeout campaign_status channel campaign
  local target_summary="${bootstrap_root}/validated_target_summary.jsonl"
  local roots="${bootstrap_root}/validated-target-schedule/branch_queries.jsonl"
  local pointer="${campaign_root}/campaign_state_manifest.json"
  local -a channels args
  require_file "validated target summary" "${target_summary}"
  require_file "validated target root" "${roots}"
  if [[ -d "${campaign_root}" && ! -f "${pointer}" \
      && -n "$(find "${campaign_root}" -mindepth 1 -print -quit)" ]]; then
    die "partial campaign exists without an atomic state pointer: ${campaign_root}"
  fi
  z3=$(configured_value z3_bin) || return $?
  solver_timeout=$(configured_value solver_timeout_ms) || return $?
  args=(
    --regions "${static_regions}"
    --activations "${activation_plan}"
    --edges "${runtime_edge_validations}"
    --roots "${roots}"
    --static-graph "${static_graph}"
    --output-dir "${campaign_root}"
    --z3 "${z3}"
    --runtime-discovery-mode FIXED_VALIDATED_GRAPH
    --execution-timeout-ms 300000
    --max-iterations 128
    --max-executions 512
    --max-solver-queries 512
    --max-wall-clock-ms 3600000
    --solver-timeout-ms "${solver_timeout}"
    --summaries "${target_summary}"
  )
  mapfile -t channels < <(declared_channels)
  for channel in "${channels[@]}"; do
    campaign=$(producer_campaign_directory "${channel}") || return $?
    args+=(--resume-activations \
      "${campaign}/combined_activation_plan.jsonl")
    args+=(--summaries \
      "${campaign}/combined_region_summaries.jsonl")
  done
  args+=(-- "${fixture_dir}/run.sh" campaign-capture)
  set +e
  run_graphchecker_main \
    edu.uva.liftlab.graphchecker.concolic.ConcolicCampaignRunner \
    "${args[@]}"
  campaign_status=$?
  set -e
  if [[ "${campaign_status}" -eq 2 ]]; then
    require_file "bounded campaign checkpoint" "${pointer}"
    echo "[three-thread-rpc] campaign is bounded but incomplete; resume with '$0 campaign'" >&2
    return 2
  fi
  [[ "${campaign_status}" -eq 0 ]] \
    || die "concolic campaign failed with exit ${campaign_status}"
  jq -e '
    .kind == "CONCOLIC_REGION_CAMPAIGN"
    and .complete == true
    and .status == "COMPLETE_BOUNDED_FIXED_RUNTIME_GRAPH_CLOSURE"
    and .targetRootAdmissionComplete == true
    and .branchOverrideAccepted == false
    and .gapCount == 0
    and .graphWorklist.complete == true
    and .pathWorklist.complete == true
    and .relationMerge.complete == true
    and .transitionDiscovery.complete == true
    and .runtimeDiscoveryMode == "FIXED_VALIDATED_GRAPH"
    and .eligibleToReportBoundedFixedGraphRelationship == true
  ' "${campaign_root}/concolic_campaign_manifest.json" >/dev/null \
    || die "campaign finished without complete fixed-graph closure"
  require_file "atomic campaign state pointer" "${pointer}"
}

sha256_file() {
  local path=$1
  require_command sha256sum
  sha256sum "${path}" | awk '{print $1}'
}

validate_campaign_snapshot() {
  local pointer="${campaign_root}/campaign_state_manifest.json"
  local generation manifest_relative manifest expected_hash actual_hash
  local generation_dir completion_relative completion
  local role file file_hash line_count path actual_lines
  local -A seen_roles=()
  require_file "campaign state pointer" "${pointer}"
  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_CAMPAIGN_STATE_POINTER"
    and .complete == true
    and ((.generation // "") | length) > 0
    and ((.manifest // "") | length) > 0
    and ((.manifestSha256 // "") | length) == 64
    and ((.campaignCompleteManifest // "") | length) > 0
    and ((.campaignCompleteManifestSha256 // "") | length) == 64
  ' "${pointer}" >/dev/null || die "campaign state pointer is incomplete"
  generation=$(jq -er '.generation' "${pointer}")
  generation_dir=$(realpath -m \
    "${campaign_root}/state-generations/${generation}")
  manifest_relative=$(jq -er '.manifest' "${pointer}")
  manifest=$(realpath -m "${campaign_root}/${manifest_relative}")
  [[ "${manifest}" == "${generation_dir}/state_manifest.json" ]] \
    || die "campaign pointer escapes its immutable generation"
  require_file "campaign generation manifest" "${manifest}"
  expected_hash=$(jq -er '.manifestSha256' "${pointer}")
  actual_hash=$(sha256_file "${manifest}")
  [[ "${actual_hash}" == "${expected_hash}" ]] \
    || die "campaign generation manifest hash mismatch"
  jq -e --arg generation "${generation}" '
    .schemaVersion == 2
    and .kind == "CONCOLIC_CAMPAIGN_STATE_GENERATION"
    and .complete == true
    and .generation == $generation
    and ((.stateFiles // []) | length) == 7
  ' "${manifest}" >/dev/null || die "campaign generation is incomplete"
  completion_relative=$(jq -er '.campaignCompleteManifest' "${pointer}")
  completion=$(realpath -m "${campaign_root}/${completion_relative}")
  [[ "$(dirname "${completion}")" == "${generation_dir}" \
      && "$(basename "${completion}")" == "campaign_complete_manifest.json" ]] \
    || die "campaign completion manifest escapes its generation"
  require_file "campaign completion manifest" "${completion}"
  expected_hash=$(jq -er '.campaignCompleteManifestSha256' "${pointer}")
  [[ "$(sha256_file "${completion}")" == "${expected_hash}" \
      && "$(jq -er '.campaignCompleteManifestSha256' "${manifest}")" \
        == "${expected_hash}" ]] \
    || die "campaign completion manifest hash mismatch"
  jq -e '
    .kind == "CONCOLIC_REGION_CAMPAIGN"
    and .complete == true
    and .runtimeDiscoveryMode == "FIXED_VALIDATED_GRAPH"
    and .eligibleToReportBoundedFixedGraphRelationship == true
    and .targetRootAdmissionComplete == true
    and .gapCount == 0
    and .branchOverrideAccepted == false
  ' "${completion}" >/dev/null \
    || die "immutable campaign completion is not authoritative"

  while IFS=$'\t' read -r role file file_hash line_count; do
    [[ -n "${role}" && -n "${file}" && -n "${file_hash}" \
        && -n "${line_count}" ]] || die "malformed campaign state-file row"
    [[ "${file}" == "$(basename "${file}")" ]] \
      || die "campaign state file is not generation-local: ${file}"
    [[ -z "${seen_roles[${role}]+present}" ]] \
      || die "duplicate campaign state role: ${role}"
    seen_roles[${role}]=present
    path=$(realpath -m "${generation_dir}/${file}")
    [[ "$(dirname "${path}")" == "${generation_dir}" ]] \
      || die "campaign state file escapes its generation: ${role}"
    require_file "campaign ${role} artifact" "${path}"
    [[ "$(sha256_file "${path}")" == "${file_hash}" ]] \
      || die "campaign ${role} artifact hash mismatch"
    actual_lines=$(jq -c '.' "${path}" | wc -l)
    [[ "${actual_lines}" -eq "${line_count}" ]] \
      || die "campaign ${role} line count mismatch"
    case "${role}" in
      REGIONS) campaign_snapshot_regions=${path} ;;
      ACTIVATIONS) campaign_snapshot_activations=${path} ;;
      EDGES) campaign_snapshot_edges=${path} ;;
      ROOTS) campaign_snapshot_roots=${path} ;;
      SUMMARIES) campaign_snapshot_summaries=${path} ;;
      PATH_RECORDS) campaign_snapshot_path_records=${path} ;;
      STATIC_GRAPH) campaign_snapshot_static_graph=${path} ;;
      *) die "unknown campaign state role: ${role}" ;;
    esac
  done < <(jq -r '.stateFiles[] | [.role,.file,.sha256,.lineCount] | @tsv' \
    "${manifest}")
  for role in REGIONS ACTIVATIONS EDGES ROOTS SUMMARIES PATH_RECORDS STATIC_GRAPH; do
    [[ -n "${seen_roles[${role}]+present}" ]] \
      || die "campaign snapshot omitted role ${role}"
  done
  campaign_snapshot_completion=${completion}
}

final_target_binding() {
  local -a matches
  mapfile -t matches < <(jq -r '
    select(
      .captureGoal.kind == "TARGET_BRANCH"
      and .readyForSolver == true
      and .readyForReplay == false
      and .replayAlreadyValidated == true
      and .targetReplayValidated == true
      and ((.validatedSummaryId // "") | length) > 0)
    | [.regionId, .activationId] | @tsv
  ' "${campaign_snapshot_roots}")
  [[ ${#matches[@]} -eq 1 ]] \
    || die "campaign snapshot does not contain one validated target root"
  printf '%s\n' "${matches[0]}"
}

do_final() {
  local binding target_region target_activation channel producer_binding_row
  local producer_region expected_regions actual_regions
  local -a channels bounded_args
  [[ ! -e "${final_root}" ]] \
    || die "final output already exists: ${final_root}"
  validate_campaign_snapshot
  binding=$(final_target_binding) || return $?
  IFS=$'\t' read -r target_region target_activation <<< "${binding}"
  mkdir -p "${final_root}"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_STATIC_REGIONS="${campaign_snapshot_regions}" \
    CAUSYNTH_STATIC_GRAPH="${campaign_snapshot_static_graph}" \
    CAUSYNTH_ACTIVATION_PLAN="${campaign_snapshot_activations}" \
    CAUSYNTH_EDGE_VALIDATIONS="${campaign_snapshot_edges}" \
    CAUSYNTH_SCHEDULE_OUTPUT_DIR="${final_root}/schedule" \
    CAUSYNTH_SCHEDULE_SUMMARIES="${campaign_snapshot_summaries}" \
    CAUSYNTH_SCHEDULE_PATH_RECORDS="${campaign_snapshot_path_records}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${target_region}" \
      --activation-id "${target_activation}")
  jq -e -s --arg region "${target_region}" \
      --arg activation "${target_activation}" '
    length == 1
    and .[0].regionId == $region
    and .[0].activationId == $activation
    and .[0].readyForSolver == true
    and .[0].readyForReplay == false
    and .[0].replayAlreadyValidated == true
    and .[0].targetReplayValidated == true
    and ((.[0].validatedSummaryId // "") | length) > 0
    and ((.[0].replayValidationAuthority // "") | length) > 0
  ' "${final_root}/schedule/branch_queries.jsonl" >/dev/null \
    || die "final scheduler lost target replay validation"
  mapfile -t channels < <(declared_channels)
  bounded_args=()
  for channel in "${channels[@]}"; do
    producer_binding_row=$(producer_binding "${channel}") || return $?
    IFS=$'\t' read -r producer_region _ <<< "${producer_binding_row}"
    bounded_args+=(--bounded-upstream-region "${producer_region}")
  done
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_STATIC_REGIONS="${campaign_snapshot_regions}" \
    CAUSYNTH_FATAL_QUERIES="${final_root}/schedule/branch_queries.jsonl" \
    CAUSYNTH_COMPOSE_SUMMARIES="${campaign_snapshot_summaries}" \
    CAUSYNTH_MERGE_PLAN="${final_root}/schedule/symbolic_merge_plan.json" \
    CAUSYNTH_COMPOSED_SMT="${final_root}/composed_fatal.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${final_root}/composed_smt_manifest.json" \
    CAUSYNTH_RELATIONSHIP_CANDIDATES="${final_root}/symbolic_relationship_candidates.json" \
    CAUSYNTH_FATAL_REGION="${target_region}" \
    CAUSYNTH_FATAL_ACTIVATION_ID="${target_activation}" \
    "${runner}" --config "${config}" compose "${bounded_args[@]}")
  jq -e --argjson expected "${#channels[@]}" '
    .kind == "CONCOLIC_COMPOSED_SMT"
    and .compositionStage == "VALIDATED_FINAL"
    and .boundedComposition == true
    and ((.boundedUpstreamRegions // []) | length) == $expected
    and .structurallyComplete == true
    and .fatalReplayValidated == true
    and .complete == true
    and .eligibleForBootstrapModel == false
    and .eligibleToReportAutomaticRelationship == true
    and .caseProjectionCatalogComplete == true
  ' "${final_root}/composed_smt_manifest.json" >/dev/null \
    || die "final composition is not replay-validated and complete"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_COMPOSED_SMT="${final_root}/composed_fatal.smt2" \
    CAUSYNTH_RELATIONSHIP_CANDIDATES="${final_root}/symbolic_relationship_candidates.json" \
    CAUSYNTH_PROOF_REPORT="${final_root}/symbolic_relationship_proofs.json" \
    "${runner}" --config "${config}" solve)
  jq -e '
    .complete == true
    and .status == "COMPLETE_RELATIONSHIP_PROOF"
    and .automaticVerificationEligible == true
    and .baseSatisfiable == true
    and .verificationErrorCount == 0
    and .requiredRelationshipCount == .requiredRelationshipProvedCount
  ' "${final_root}/symbolic_relationship_proofs.json" >/dev/null \
    || die "final relationship proof is incomplete"
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_STATIC_REGIONS="${campaign_snapshot_regions}" \
    CAUSYNTH_COMPOSED_SMT="${final_root}/composed_fatal.smt2" \
    CAUSYNTH_COMPOSITION_MANIFEST="${final_root}/composed_smt_manifest.json" \
    CAUSYNTH_RELATIONSHIP_CANDIDATES="${final_root}/symbolic_relationship_candidates.json" \
    CAUSYNTH_REACH_REPORT="${final_root}/boolean_reach_condition.json" \
    "${runner}" --config "${config}" reach \
      --mode FINAL_REPORT)
  expected_regions=$(declared_producer_regions | sort -u)
  actual_regions=$(jq -r '.rootBooleanInputs[].regionId' \
    "${final_root}/boolean_reach_condition.json" | sort -u)
  [[ "${expected_regions}" == "${actual_regions}" ]] \
    || die "final condition roots do not match both discovered producers"
  jq -e --argjson expected "${#channels[@]}" '
    def assigned($row; $port):
      [$row.assignments[] | select(.portId == $port) | .value]
      | if length == 1 then .[0] else null end;
    .complete == true
    and .status == "COMPLETE_EXACT_BOOLEAN_REACH_CONDITION"
    and .extractionMode == "FINAL_REPORT"
    and .replayBootstrapOnly == false
    and .reportableFinalReachCondition == true
    and .truthTableComplete == true
    and .exactFiniteProjection == true
    and .rootBooleanInputCount == $expected
    and .satisfyingValuationCount > 0
    and .unsatisfyingValuationCount > 0
    and (.rootBooleanInputs as $inputs
      | .truthTable as $rows
      | all($inputs[];
          .portId as $port
          | any($rows[];
              . as $left
              | any($rows[];
                  . as $right
                  | $left.reachesBug != $right.reachesBug
                  and assigned($left; $port) != assigned($right; $port)
                  and all($inputs[] | select(.portId != $port);
                    .portId as $other
                    | assigned($left; $other)
                      == assigned($right; $other))))))
  ' "${final_root}/boolean_reach_condition.json" >/dev/null \
    || die "final exact reach condition does not depend on every producer Boolean"
  echo "[three-thread-rpc] final reach condition: ${final_root}/boolean_reach_condition.json"
}

do_seed_target() {
  local activation region binding summary
  validate_discovery_inputs
  activation=$(scheduled_target_activation) || return $?
  binding=$(target_binding) || return $?
  IFS=$'\t' read -r region _ <<< "${binding}"
  instrument_plan "${target_schedule}/scheduled_activation_plan.jsonl" \
    "${activation}" "${target_classes}" \
    "${work_root}/concolic-target-static"
  run_custom_plan "${target_schedule}/scheduled_activation_plan.jsonl" \
    "${activation}" "${target_classes}" \
    "${target_schedule}/concolic_region_results.jsonl" false false false
  import_plan "${target_schedule}/scheduled_activation_plan.jsonl" \
    "${target_schedule}/concolic_region_results.jsonl" \
    "${target_schedule}/concolic_region_summaries.jsonl" \
    "${target_schedule}"
  summary="${target_schedule}/concolic_region_summaries.jsonl"
  if ! jq -e -s --arg region "${region}" --arg activation "${activation}" '
      length == 1
      and .[0].regionId == $region
      and .[0].activationId == $activation
      and .[0].valid == true
      and .[0].targetReplayValidated == false
      and .[0].branchOverrideUsed == false
    ' "${summary}" >/dev/null; then
    die "target seed import is not one valid unforced observation"
  fi
  (cd "${graphchecker_dir}" && \
    CAUSYNTH_SCHEDULE_SUMMARIES="${summary}" \
    "${runner}" --config "${config}" schedule \
      --region-id "${region}" --activation-id "${activation}")
  if ! jq -e -s --arg region "${region}" --arg activation "${activation}" '
      length == 1
      and .[0].regionId == $region
      and .[0].activationId == $activation
      and .[0].readyForSolver == true
      and .[0].readyForReplay == false
      and .[0].targetReplayValidated == false
    ' "${target_schedule}/branch_queries.jsonl" >/dev/null; then
    die "target seed scheduler did not emit one solver-ready bootstrap query"
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

do_all() {
  local channel
  local -a channels
  require_clean_work_root
  do_test
  do_prepare
  do_analyze
  do_trace
  do_discover
  do_schedule_target
  do_seed_target
  mapfile -t channels < <(declared_channels)
  for channel in "${channels[@]}"; do
    do_schedule_producer "${channel}"
    do_instrument "${channel}"
    run_custom_java "${channel}" false false
    do_import "${channel}"
    do_explore_producer "${channel}"
  done
  do_bootstrap_compose
  do_bootstrap_project
  do_bootstrap_replay
  do_campaign
  do_final
  echo "[three-thread-rpc] complete end-to-end workflow"
}

command_name=${1:-help}
shift || true
case "${command_name}" in
  help|-h|--help) usage ;;
  test) do_test ;;
  prepare) do_prepare ;;
  analyze) do_analyze ;;
  trace) do_trace ;;
  discover) [[ $# -eq 0 ]] || die "discover takes no arguments"; do_discover ;;
  schedule-target) [[ $# -eq 0 ]] || die "schedule-target takes no arguments"; do_schedule_target ;;
  seed-target) [[ $# -eq 0 ]] || die "seed-target takes no arguments"; do_seed_target ;;
  schedule-producer) [[ $# -eq 1 ]] || die "schedule-producer needs one declared channel"; do_schedule_producer "$1" ;;
  instrument) [[ $# -eq 1 ]] || die "instrument needs one declared channel"; do_instrument "$1" ;;
  replay)
    [[ $# -ge 1 && $# -le 3 ]] || die "replay needs CHANNEL [b1 b2]"
    run_custom_java "$1" "${2:-false}" "${3:-false}"
    ;;
  import) [[ $# -eq 1 ]] || die "import needs one declared channel"; do_import "$1" ;;
  explore-producer) [[ $# -eq 1 ]] || die "explore-producer needs one declared channel"; do_explore_producer "$1" ;;
  bootstrap-compose) [[ $# -eq 0 ]] || die "bootstrap-compose takes no arguments"; do_bootstrap_compose ;;
  bootstrap-project) [[ $# -eq 0 ]] || die "bootstrap-project takes no arguments"; do_bootstrap_project ;;
  bootstrap-replay) [[ $# -eq 0 ]] || die "bootstrap-replay takes no arguments"; do_bootstrap_replay ;;
  campaign) [[ $# -eq 0 ]] || die "campaign takes no arguments"; do_campaign ;;
  campaign-capture) [[ $# -eq 0 ]] || die "campaign-capture takes no arguments"; do_campaign_capture ;;
  final) [[ $# -eq 0 ]] || die "final takes no arguments"; do_final ;;
  smoke)
    do_test
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
