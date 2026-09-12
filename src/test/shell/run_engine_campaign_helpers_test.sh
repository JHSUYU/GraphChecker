#!/usr/bin/env bash

set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
# shellcheck source=../../../run_engine.sh
source "${repo}/run_engine.sh"

test_tmp=$(mktemp -d)
cleanup() {
  [[ "${test_tmp}" == /tmp/* ]] || return 1
  rm -r -- "${test_tmp}"
}
trap cleanup EXIT

fail() {
  echo "run_engine campaign helper test failed: $*" >&2
  exit 1
}

emit_sequence=0
emit_fixture() {
  emit_sequence=$((emit_sequence + 1))
  emit_root="${test_tmp}/emit-${emit_sequence}"
  emit_iteration="${emit_root}/iteration-0000"
  emit_config="${emit_root}/workflow.properties"
  emit_bounds="${emit_root}/loop-bounds.jsonl"
  emit_classes="${emit_root}/classes"
  campaign_root="${emit_root}"
  campaign_final="${emit_root}/final"
  campaign_stage_metrics="${emit_root}/stage_metrics.tsv"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  reach_report="${campaign_final}/z3-result.json"

  mkdir -p "${campaign_final}" "${emit_classes}" \
    "${emit_iteration}/seed-result" \
    "${emit_iteration}/workers/task-target"
  printf 'workflow_path_base=project\n' >"${emit_config}"
  printf '# no retained condition loop\n' >"${emit_bounds}"
  printf 'production class bytes\n' >"${emit_classes}/Frozen.class"
  project_classpath="${emit_classes}"

  campaign_provenance=$(jq -n \
    --arg config "${emit_config}" \
    --arg configSha "$(campaign_digest "${emit_config}")" \
    --arg bounds "${emit_bounds}" \
    --arg boundsSha "$(campaign_digest "${emit_bounds}")" \
    --arg classes "${emit_classes}" \
    --arg classesSha "$(campaign_tree_digest "${emit_classes}")" \
    --arg classpath "${project_classpath}" \
    --arg classpathSha "$(printf '%s' "${project_classpath}" \
      | sha256sum | awk '{print $1}')" '
    {config: {path: $config, sha256: $configSha},
     loopBounds: {path: $bounds, sha256: $boundsSha},
     communicationMappings: {path: "", sha256: ""},
     productionClasses: {path: $classes, sha256: $classesSha},
     workload: {testClasses: {path: $classes, sha256: $classesSha},
                classpath: $classpath, classpathSha256: $classpathSha}}')

  printf 'EMIT\t7\n' >"${campaign_stage_metrics}"
  printf '(assert true)\n' >"${campaign_final}/candidate.smt2"
  jq -n '{schemaVersion: 2, kind: "CONCOLIC_COMPOSED_SMT",
    finalStatus: "FINAL_READY", finalStatusRefusals: [],
    pathSetComplete: false,
    symbolicPropagationComplete: false,
    symbolicPropagation: [{armCount: 2}],
    symbolicPropagationGaps: [{reason:"UNRELATED_FAMILY_OPEN",
                               subject:"CBF.fixture", detail:"telemetry"}],
    boundedLoopComposition: {gaps: [{reason:"LOOP_BOUND_OPEN",
                                     subject:"loop.fixture",
                                     detail:"telemetry"}]},
    guardedReadModelComplete: false,
    guardedReadModel: {
      schemaVersion: 1, kind: "DIRECT_GUARDED_READ_MODEL",
      authority: "VM_READ_TIME_CANDIDATE_SNAPSHOT_V1",
      complete: true, reads: []}, gaps: []}' \
    >"${composition_manifest}"
  jq -n '{schemaVersion: 3, kind: "BOOLEAN_REACH_CONDITION_REPORT",
    state: "sat", reachCondition: {reachability: "REACHABLE",
      degeneracyCheck: "CONSTRAINED_ROOT_SPACE"},
    unsatClosureComplete: false, gaps: [], valuations: []}' \
    >"${reach_report}"
  printf '%s\n' \
    '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[{"kind":"PATH_FLIP_NOT_ADMITTED","queryKey":"flip","reason":"UNEXPLORED"},{"kind":"PATH_FLIP_SOLVER_TIMEOUT","queryKey":"slow-flip","reason":"SOLVER_TIMEOUT"}]}' \
    >"${emit_iteration}/workers/task-target/path_closure.json"
  printf '%s\n' \
    '{"taskId":"task-target","published":true}' \
    >"${emit_iteration}/seed-result/concolic_region_results.jsonl"
  : >"${emit_iteration}/import_diagnostics.jsonl"
  : >"${emit_iteration}/topology_delta.jsonl"
  jq -n '{schemaVersion: 1, kind: "CAMPAIGN_ITERATION_MANIFEST",
    iterationId: "iteration-0000", parentIterationId: "",
    externalWorkerCount: 1, topologyDelta: {rows: 0, divergences: 0},
    members: [{role: "TARGET", taskId: "task-target",
               obligationDigests: []}]}' \
    >"${emit_iteration}/iteration_manifest.json"
}

run_emit() {
  emit_status=0
  ( campaign_emit "${emit_iteration}" ) \
    >"${emit_root}/emit.log" 2>&1 || emit_status=$?
}

# A connected SAT formula is a candidate even when coverage needed only for a
# closed UNSAT conclusion remains open. Those rows stay visible as telemetry.
emit_fixture
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a complete candidate was withheld: $(<"${emit_root}/emit.log")"
[[ $(jq -r '.claim' "${campaign_final}/result.json") == SAT_CANDIDATE ]] \
  || fail "the accepted SAT claim was not published"
[[ $(jq -r '.provenance.loopBounds.sha256' \
      "${campaign_final}/result.json") \
    == "$(campaign_digest "${emit_bounds}")" ]] \
  || fail "the result lost its loop-bound provenance"
[[ $(jq -r '.provenance.config.path' \
      "${campaign_final}/result.json") == "${emit_config}" ]] \
  || fail "the result names a different frozen config"
jq -e '.evidence.symbolicPropagationComplete == false
  and .evidence.consumerBoundaryArms == 2
  and .evidence.guardedReadModelComplete == false
  and .gapCount == 0
  and .telemetryCount >= 4' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its propagation provenance"

# A flip query the solver could not decide in its budget is an unexplored
# sibling path.  It is coverage telemetry, so it leaves a SAT candidate
# accepted; only the closed UNSAT conclusion is withheld by it.
jq -e '[.telemetryGaps[]
        | select(.stage == "EXPLORE" and .source == "PATH_WORKLIST"
            and .code == "PATH_FLIP_SOLVER_TIMEOUT"
            and .subject == "slow-flip")] | length == 1' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the solver-timeout path gap was not published as telemetry"
jq -e '[.gaps[] | select(.code == "PATH_FLIP_SOLVER_TIMEOUT")] | length == 0' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the solver-timeout path gap blocked an accepted SAT candidate"

# A published obligation wave records a solver timeout instead of failing the
# campaign, and contributes only its exploration record: no new path case.
wave_root="${test_tmp}/wave"
mkdir -p "${wave_root}/planner/slow-flip"
printf '%s\n' \
  '{"schemaVersion":1,"kind":"PATH_EXPLORATION_RECORD","queryKey":"slow-flip","status":"SOLVER_TIMEOUT","reason":"SOLVER_TIMEOUT"}' \
  >"${wave_root}/planner/slow-flip/exploration_record.jsonl"
printf '%s\n' '{"summaryId":"SUMMARY.SEED","taskId":"task-target"}' \
  >"${wave_root}/summaries.jsonl"
printf '%s\n' '{"taskId":"task-target"}' >"${wave_root}/tasks.jsonl"
: >"${wave_root}/records.jsonl"
campaign_publish_wave "${wave_root}/planner" "${wave_root}/summaries.jsonl" \
  "${wave_root}/tasks.jsonl" "${wave_root}/records.jsonl" \
  || fail "a solver-timeout obligation aborted the published wave"
[[ $(wc -l <"${wave_root}/summaries.jsonl") -eq 1 ]] \
  || fail "a solver-timeout obligation published a path case"
jq -e -s '[.[] | select(.queryKey == "slow-flip"
    and .status == "SOLVER_TIMEOUT")] | length == 1' \
  "${wave_root}/records.jsonl" >/dev/null \
  || fail "the solver-timeout exploration record was not published"

# EMIT re-hashes frozen inputs before publishing any result.
emit_fixture
printf 'schedule_max_jobs=1\n' >>"${emit_config}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a changed frozen config was accepted"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "a result was published for a drifted generation"
grep -q 'changed after it was frozen' "${emit_root}/emit.log" \
  || fail "the drifted frozen input was not named"

# CONFIG-1: the one workflow-key table answers all four questions about a key.
config_table_keys=()
for config_row in "${workflow_config_keys[@]}"; do
  read_config_key_row "${config_row}"
  [[ " ${config_table_keys[*]-} " != *" ${config_key} "* ]] \
    || fail "workflow key declared twice: ${config_key}"
  config_table_keys+=("${config_key}")
  [[ "${config_flags}" =~ ^[krp]+$ ]] \
    || fail "workflow key ${config_key} has unknown flags: ${config_flags}"
  # A key a config file may set is a key a run resets: otherwise one
  # campaign's value survives into the next.
  [[ "${config_flags}" != *k* || "${config_flags}" == *r* ]] \
    || fail "loadable workflow key ${config_key} is never reset"
  # An environment override is only reachable for a loadable key.
  [[ -z "${config_env}" || "${config_flags}" == *k* ]] \
    || fail "internal key ${config_key} names an environment override"
done
reset_config
for config_row in "${workflow_config_keys[@]}"; do
  read_config_key_row "${config_row}"
  [[ "${config_flags}" != *r* ]] \
    || [[ "${!config_key}" == "${config_default}" ]] \
    || fail "reset_config left ${config_key} at ${!config_key}"
  if [[ "${config_flags}" == *k* ]]; then
    known_config_key "${config_key}" \
      || fail "table key ${config_key} is not a known config key"
  else
    ! known_config_key "${config_key}" \
      || fail "internal key ${config_key} is loadable from a config file"
  fi
done
[[ "$(print_normalized_config | wc -l)" -eq 38 ]] \
  || fail "config prints a different number of keys than it used to"

# FREEZE-1: one dispatch decides how each kind of frozen input is digested.
digest_root="${test_tmp}/kind-digest"
mkdir -p "${digest_root}/tree"
printf 'one\n' >"${digest_root}/tree/a.txt"
[[ "$(campaign_kind_digest file "${digest_root}/tree/a.txt")" \
    == "$(campaign_digest "${digest_root}/tree/a.txt")" ]] \
  || fail "the file kind does not digest as a file"
[[ "$(campaign_kind_digest optional "${digest_root}/absent")" == "" ]] \
  || fail "an unconfigured optional input digested to something"
[[ "$(campaign_kind_digest tree "${digest_root}/tree")" \
    == "$(campaign_tree_digest "${digest_root}/tree")" ]] \
  || fail "the tree kind does not digest as a tree"
[[ "$(campaign_kind_digest string 'a:b')" \
    == "$(printf '%s' 'a:b' | sha256sum | awk '{print $1}')" ]] \
  || fail "the string kind does not digest the string it was handed"
campaign_kind_digest bogus x >/dev/null 2>&1 \
  && fail "an unknown frozen input kind produced a digest"

# A non-zero exit that is data leaves errexit exactly as it found it.
status=0
run_capturing_status bash -c 'exit 7'
[[ "${status}" -eq 7 ]] || fail "run_capturing_status lost the exit status"
[[ $- == *e* ]] || fail "run_capturing_status did not restore errexit"
set +e
run_capturing_status bash -c 'exit 0'
[[ $- != *e* ]] || fail "run_capturing_status turned errexit on"
set -e
capture_out="${test_tmp}/capture.log"
run_capturing_status bash -c 'echo captured; exit 3' >"${capture_out}"
[[ "${status}" -eq 3 && "$(cat "${capture_out}")" == "captured" ]] \
  || fail "run_capturing_status dropped the command's redirection"

# A stated count is numeric and above zero, named by its own key.
positive_key=4
require_positive_integer positive_key \
  || fail "a positive count was refused"
for positive_key in "" abc 0 -1 "3 4"; do
  ( require_positive_integer positive_key ) 2>/dev/null \
    && fail "an invalid count was accepted: '${positive_key}'"
done

# One terminal exploration record, written from the solver's own result.
record_worker="${test_tmp}/record-worker"
mkdir -p "${record_worker}"
printf '%s\n' '{"queryKey":"k","status":"SAT_MODEL_READY","reason":"x"}' \
  >"${record_worker}/path_flip_solver_result.json"
campaign_record_exploration "${record_worker}" k "t1,t2" \
  REPLAY_NOT_ADMITTED "no primary"
[[ "$(cat "${record_worker}/exploration_record.jsonl")" == \
    '{"queryKey":"k","status":"REPLAY_NOT_ADMITTED","reason":"no primary","schemaVersion":1,"kind":"PATH_EXPLORATION_RECORD","linkedTaskIds":["t1","t2"]}' ]] \
  || fail "the exploration record is not the bytes it used to be: \
$(cat "${record_worker}/exploration_record.jsonl")"

# A replay plan with no PRIMARY row publishes no exploration record at all,
# rather than a record whose every planned field is null.
primary_root="${test_tmp}/primary-record"
mkdir -p "${primary_root}"
primary_plan="${primary_root}/execution_task_plan.jsonl"
primary_record="${primary_root}/exploration_record.jsonl"
printf '%s\n' '{"taskId":"t1","linkedReplayRole":"COMPANION"}' \
  >"${primary_plan}"
( campaign_publish_primary_record "${primary_plan}" k "${primary_record}" ) \
  && fail "an exploration record was published without a PRIMARY task"
[[ ! -s "${primary_record}" ]] \
  || fail "a PRIMARY-less replay plan published a record: \
$(cat "${primary_record}")"
printf '%s\n' '{"taskId":"t2","linkedReplayRole":"PRIMARY","regionId":"R",
  "occurrenceId":"R#a1","goalId":"g","familySnapshotDigest":"d",
  "topologyEpoch":"e"}' >>"${primary_plan}"
campaign_publish_primary_record "${primary_plan}" k "${primary_record}" \
  || fail "the PRIMARY replay task published no exploration record"
jq -e '.taskId == "t2" and .queryKey == "k"
  and .status == "VALIDATED_FRESH_REGION_PATH_FLIP_REPLAY"' \
  "${primary_record}" >/dev/null \
  || fail "the exploration record does not name the PRIMARY task: \
$(cat "${primary_record}")"

echo "run_engine campaign helper tests passed"
