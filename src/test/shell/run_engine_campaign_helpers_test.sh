#!/usr/bin/env bash

set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
# shellcheck source=../../../run_engine.sh
source "${repo}/run_engine.sh"

test_tmp=$(mktemp -d)
cleanup() {
  local test_pid
  for test_pid in "${winner_pid:-}" "${loser_pid:-}"; do
    [[ -n "${test_pid}" ]] || continue
    kill "${test_pid}" >/dev/null 2>&1 || true
    wait "${test_pid}" >/dev/null 2>&1 || true
  done
  [[ "${test_tmp}" == /tmp/* ]] || return 1
  rm -r -- "${test_tmp}"
}
trap cleanup EXIT

fail() {
  echo "run_engine helper test failed: $*" >&2
  exit 1
}

expect_failure() {
  if "$@" >/dev/null 2>&1; then
    fail "command unexpectedly succeeded: $*"
  fi
}

index="${test_tmp}/index.json"
jq -n '{schemaVersion: 1,
  kind: "RUNTIME_TARGET_FIRST_SCHEDULE_INDEX",
  selectionAuthority: "RANKED_EXACT_RUNTIME_READ_FROM_CLOSURE_V1",
  target: {campaignId: "c", regionId: "target", occurrenceId: "t#1",
           goalId: "g-target", taskId: "task-target"},
  producers: [
    {campaignId: "c", regionId: "producer", occurrenceId: "p#1",
     goalId: "g-producer", taskId: "task-producer"}]}' >"${index}"

rows=$(campaign_decode_index_members "${index}")
[[ $(wc -l <<<"${rows}") -eq 2 ]] || fail "valid index lost a member"
[[ $(cut -f1 <<<"${rows}" | paste -sd, -) == "TARGET,PRODUCER" ]] \
  || fail "valid index emitted incorrect roles"

target_only="${test_tmp}/target-only.json"
jq '.producers = []' "${index}" >"${target_only}"
rows=$(campaign_decode_index_members "${target_only}")
[[ $(wc -l <<<"${rows}") -eq 1 && ${rows%%$'\t'*} == "TARGET" ]] \
  || fail "target-local-only index was rejected"

duplicate="${test_tmp}/duplicate.json"
jq '.producers[0].taskId = .target.taskId' "${index}" >"${duplicate}"
expect_failure campaign_decode_index_members "${duplicate}"

wrong_authority="${test_tmp}/wrong-authority.json"
jq '.selectionAuthority = "UNTRUSTED"' "${index}" >"${wrong_authority}"
expect_failure campaign_decode_index_members "${wrong_authority}"

multi_index="${test_tmp}/multi-index.json"
cp "${index}" "${multi_index}"
jq -c . "${index}" >>"${multi_index}"
expect_failure campaign_decode_index_members "${multi_index}"

one_json="${test_tmp}/one.json"
printf '{"ok":true}\n' >"${one_json}"
campaign_require_json "one" "${one_json}"
multi_json="${test_tmp}/multi.json"
printf '{"a":1}\n{"b":2}\n' >"${multi_json}"
expect_failure campaign_require_json "multi" "${multi_json}"
malformed_json="${test_tmp}/malformed.json"
printf '{bad}\n' >"${malformed_json}"
expect_failure campaign_require_json "malformed" "${malformed_json}"
scalar_json="${test_tmp}/scalar.json"
printf '7\n' >"${scalar_json}"
expect_failure campaign_require_json "scalar" "${scalar_json}"

empty_jsonl="${test_tmp}/empty.jsonl"
: >"${empty_jsonl}"
[[ $(campaign_jsonl_array "empty" "${empty_jsonl}") == "[]" ]] \
  || fail "empty JSONL did not become an empty array"
bad_jsonl="${test_tmp}/bad.jsonl"
printf '{"ok":true}\nnot-json\n' >"${bad_jsonl}"
expect_failure campaign_jsonl_array "bad" "${bad_jsonl}"
scalar_jsonl="${test_tmp}/scalar.jsonl"
printf '{"ok":true}\n7\n' >"${scalar_jsonl}"
expect_failure campaign_jsonl_array "scalar" "${scalar_jsonl}"
expect_failure campaign_jsonl_array "missing" "${test_tmp}/missing.jsonl"

worklist="${test_tmp}/worklist.jsonl"
: >"${worklist}"
[[ -z $(campaign_decode_worklist_keys "${worklist}" 8) ]] \
  || fail "an empty worklist was not preserved as an empty semantic result"
printf '{"queryKey":"b"}\n{"queryKey":"a"}\n' >"${worklist}"
[[ $(campaign_decode_worklist_keys "${worklist}" 1) == "a" ]] \
  || fail "worklist keys were not deterministically bounded"
printf '{"queryKey":"a"}\n{"queryKey":"a"}\n' >"${worklist}"
expect_failure campaign_decode_worklist_keys "${worklist}" 8
printf '{bad}\n' >"${worklist}"
expect_failure campaign_decode_worklist_keys "${worklist}" 8
expect_failure campaign_decode_worklist_keys "${test_tmp}/missing-worklist" 8

workers="${test_tmp}/workers"
mkdir -p "${workers}"
[[ $(campaign_path_closures_json "${workers}") == "[]" ]] \
  || fail "zero path closures did not become an empty array"
mkdir -p "${workers}/task"
printf '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n' \
  >"${workers}/task/path_closure.json"
[[ $(campaign_path_closures_json "${workers}" \
      | jq -r 'length') -eq 1 ]] || fail "one path closure was not collected"
jq '.kind = "WRONG"' "${workers}/task/path_closure.json" \
  >"${workers}/task/path_closure.json.bad"
mv "${workers}/task/path_closure.json.bad" \
  "${workers}/task/path_closure.json"
expect_failure campaign_path_closures_json "${workers}"
printf '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n' \
  >"${workers}/task/path_closure.json"
expect_failure campaign_path_closures_json "${workers}"

snapshot_workers="${test_tmp}/snapshot-workers"
mkdir -p "${snapshot_workers}/one" "${snapshot_workers}/two"
printf '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n' \
  >"${snapshot_workers}/one/path_closure.json"
printf '{bad}\n' >"${snapshot_workers}/two/path_closure.json"
snapshot="${test_tmp}/path-closures.json"
expect_failure campaign_materialize_path_closures "${snapshot_workers}" \
  "${snapshot}"
[[ ! -e "${snapshot}" ]] \
  || fail "failed path-closure snapshot published a partial final artifact"
printf '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n' \
  >"${snapshot_workers}/two/path_closure.json"
campaign_materialize_path_closures "${snapshot_workers}" "${snapshot}"
[[ $(jq -r 'length' "${snapshot}") -eq 2 ]] \
  || fail "checked path-closure snapshot lost a worker"
expect_failure campaign_materialize_path_closures "${snapshot_workers}" \
  "${snapshot}"

large_composition="${test_tmp}/large-composition.json"
{
  printf '{"schemaVersion":2,"kind":"CONCOLIC_COMPOSED_SMT",'
  printf '"finalStatusRefusals":[],"canonicalModel":{"gaps":[]},'
  printf '"padding":"'
  head -c 150000 /dev/zero | tr '\0' x
  printf '"}\n'
} >"${large_composition}"
large_reach="${test_tmp}/large-reach.json"
printf '%s\n' '{"schemaVersion":3,"kind":"BOOLEAN_REACH_CONDITION_REPORT","gaps":[]}' \
  >"${large_reach}"
large_diagnostics="${test_tmp}/large-diagnostics.jsonl"
: >"${large_diagnostics}"
large_delta="${test_tmp}/large-delta.jsonl"
{
  printf '{"deltaKind":"COVERAGE_GAP","source":"TEST","code":"BIG",'
  printf '"taskId":"large","reason":"'
  head -c 2200000 /dev/zero | tr '\0' y
  printf '"}\n'
} >"${large_delta}"
large_closures="${test_tmp}/large-closures.json"
printf '[]\n' >"${large_closures}"
large_gaps="${test_tmp}/large-gaps.json"
campaign_write_coverage_gaps "${large_composition}" "${large_reach}" \
  "${large_diagnostics}" "${large_delta}" "${large_closures}" \
  "${large_gaps}"
[[ $(jq -r '.gapCount' "${large_gaps}") -eq 1 ]] \
  || fail "file-backed coverage aggregation lost the large delta"
[[ $(jq -r '.gaps[0].code' "${large_gaps}") == "BIG" ]] \
  || fail "file-backed coverage aggregation changed the large delta"
malformed_composition="${test_tmp}/malformed-composition.json"
printf '{bad}\n' >"${malformed_composition}"
expect_failure campaign_write_coverage_gaps "${malformed_composition}" \
  "${large_reach}" "${large_diagnostics}" "${large_delta}" \
  "${large_closures}" "${test_tmp}/malformed-gaps.json"

campaign="${test_tmp}/campaign"
mkdir -p "${campaign}/iteration-0000"
manifest="${campaign}/iteration-0000/iteration_manifest.json"
jq -n '{schemaVersion: 1, kind: "CAMPAIGN_ITERATION_MANIFEST",
  iterationId: "iteration-0000", parentIterationId: "",
  externalWorkerCount: 8, topologyDelta: {rows: 0, divergences: 0},
  members: [{role: "TARGET", taskId: "task-target",
             obligationDigests: []}]}' >"${manifest}"
[[ $(campaign_iteration_manifests_json "${campaign}" \
      | jq -r '.[0].externalWorkerCount') -eq 8 ]] \
  || fail "iteration manifest was not collected"
mkdir -p "${campaign}/iteration-0001"
cp "${manifest}" "${campaign}/iteration-0001/iteration_manifest.json"
expect_failure campaign_iteration_manifests_json "${campaign}"
rm -r -- "${campaign}/iteration-0001"
jq '.kind = "WRONG"' "${manifest}" >"${manifest}.bad"
mv "${manifest}.bad" "${manifest}"
expect_failure campaign_iteration_manifests_json "${campaign}"

# A second campaign for the same root must lose before it can truncate the
# winner's metrics.  Stop the winner inside its first real campaign stage so
# both contenders remain live while the loser executes do_campaign's actual
# reservation path; all expensive semantic stages stay stubbed out.
reservation_root="${test_tmp}/reservation-campaign"
reservation_ready="${test_tmp}/reservation-winner-ready"
reservation_release="${test_tmp}/reservation-winner-release"
winner_status="${test_tmp}/reservation-winner-status"
loser_status="${test_tmp}/reservation-loser-status"
schedule_output_dir="${reservation_root}"
campaign_setup_command=""
campaign_max_iterations=1
campaign_validate() {
  printf 'winner-owned-metrics\n' >"${campaign_stage_metrics}"
  : >"${reservation_ready}"
  while [[ ! -e "${reservation_release}" ]]; do
    sleep 0.01
  done
  exit 0
}
(
  set +e
  (do_campaign)
  printf '%s\n' "$?" >"${winner_status}"
  exit 0
) &
winner_pid=$!
reservation_wait_attempts=0
while [[ ! -e "${reservation_ready}" ]]; do
  kill -0 "${winner_pid}" >/dev/null 2>&1 \
    || fail "the winning contender exited before its first campaign stage"
  reservation_wait_attempts=$((reservation_wait_attempts + 1))
  [[ "${reservation_wait_attempts}" -lt 500 ]] \
    || fail "the winning contender did not reach its first campaign stage"
  sleep 0.01
done
(
  set +e
  (do_campaign) >/dev/null 2>&1
  printf '%s\n' "$?" >"${loser_status}"
  exit 0
) &
loser_pid=$!
wait "${loser_pid}"
loser_pid=""
[[ $(<"${loser_status}") -ne 0 ]] \
  || fail "the second contender acquired an already reserved campaign root"
[[ $(<"${reservation_root}/stage_metrics.tsv") == "winner-owned-metrics" ]] \
  || fail "the losing contender truncated the winner's stage metrics"
: >"${reservation_release}"
wait "${winner_pid}"
winner_pid=""
[[ $(<"${winner_status}") -eq 0 ]] \
  || fail "the winning contender did not retain its campaign reservation"

# The private tool copy is the one identity observed by both adapter entry
# points.  Hash and mode checks keep this focused on the freeze contract rather
# than merely checking that an environment variable happened to be present.
freeze_root="${test_tmp}/freeze-campaign"
source_jar="${test_tmp}/GraphChecker-source.jar"
mkdir -p "${freeze_root}/frozen-inputs"
printf 'frozen GraphChecker test bytes\n' >"${source_jar}"
source_sha=$(campaign_digest "${source_jar}")
campaign_root="${freeze_root}"
graphchecker_jar="${source_jar}"
campaign_freeze_graphchecker_jar
private_jar="${freeze_root}/frozen-inputs/GraphChecker.jar"
[[ "${graphchecker_jar}" == "${private_jar}" ]] \
  || fail "freeze did not replace graphchecker_jar with the private path"
[[ $(campaign_digest "${private_jar}") == "${source_sha}" ]] \
  || fail "the private GraphChecker jar differs from its frozen source"
[[ $(stat -c '%A' "${private_jar}") != *w* ]] \
  || fail "the private GraphChecker jar remains writable"

workload_work_dir="${test_tmp}"
config_file="${test_tmp}/workflow.properties"
custom_jdk_home="${test_tmp}/jdk"
causynth_protocol_stubs=""
adapter_observed="${test_tmp}/adapter-graphchecker-jar"
workload_observed="${test_tmp}/workload-graphchecker-jar"
export RUN_ENGINE_TEST_ADAPTER_OUTPUT="${adapter_observed}"
export RUN_ENGINE_TEST_WORKLOAD_OUTPUT="${workload_observed}"
campaign_run_adapter freeze-test \
  'printf "%s\n" "$GRAPHCHECKER_JAR" >"$RUN_ENGINE_TEST_ADAPTER_OUTPUT"'
runtime_region_plan="${test_tmp}/runtime/concolic_region_plan.jsonl"
analysis_classes_dir="${test_tmp}/instrumented-classes"
workload_command='printf "%s\n" "$GRAPHCHECKER_JAR" >"$RUN_ENGINE_TEST_WORKLOAD_OUTPUT"'
run_configured_workload
[[ $(<"${adapter_observed}") == "${private_jar}" ]] \
  || fail "the setup/replay adapter did not observe the private jar"
[[ $(<"${workload_observed}") == "${private_jar}" ]] \
  || fail "the configured seed workload did not observe the private jar"

echo "run_engine campaign helper tests passed"
