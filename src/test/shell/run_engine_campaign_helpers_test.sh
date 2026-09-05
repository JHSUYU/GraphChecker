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

tree_one="${test_tmp}/tree-one"
tree_two="${test_tmp}/tree-two"
mkdir -p "${tree_one}/nested" "${tree_two}/nested"
printf 'same bytes\n' >"${tree_one}/nested/value"
printf 'same bytes\n' >"${tree_two}/nested/value"
[[ $(campaign_tree_digest "${tree_one}") \
    == $(campaign_tree_digest "${tree_two}") ]] \
  || fail "tree digest depends on its absolute root path"
printf 'changed bytes\n' >"${tree_two}/nested/value"
[[ $(campaign_tree_digest "${tree_one}") \
    != $(campaign_tree_digest "${tree_two}") ]] \
  || fail "tree digest ignored changed content"

# Import summaries are content-addressed by every semantic input.  A hit must
# reproduce all three importer artifacts without running the importer, a raw
# input change must miss, and a corrupt entry must fail closed.
import_cache_root="${test_tmp}/import-cache"
import_raw="${test_tmp}/import-raw.jsonl"
import_plan="${test_tmp}/import-plan.jsonl"
import_runtime_plan="${test_tmp}/import-runtime-plan.jsonl"
import_jar="${test_tmp}/import-GraphChecker.jar"
import_calls="${test_tmp}/import-calls"
printf '{"event":"CONCOLIC_REGION_RESULT"}\n' >"${import_raw}"
printf '{"taskId":"task"}\n' >"${import_plan}"
printf '{"kind":"RUNTIME_REGION_PLAN"}\n' >"${import_runtime_plan}"
printf 'jar\n' >"${import_jar}"
printf '0\n' >"${import_calls}"
causynth_cache_dir="${import_cache_root}"
graphchecker_jar="${import_jar}"
causynth_communication_mappings=""
raw_concolic_results="${import_raw}"
import_task_plan="${import_plan}"
runtime_region_plan="${import_runtime_plan}"
imported_summaries="${test_tmp}/import-out/summaries.jsonl"
import_diagnostics="${test_tmp}/import-out/diagnostics.jsonl"
import_topology_delta="${test_tmp}/import-out/delta.jsonl"
run_java_main() {
  local calls
  calls=$(( $(<"${import_calls}") + 1 ))
  printf '%s\n' "${calls}" >"${import_calls}"
  printf '{"call":%s,"raw":"%s"}\n' "${calls}" \
    "$(campaign_digest "${raw_concolic_results}")" \
    >"${imported_summaries}"
  : >"${import_diagnostics}"
  printf '{"call":%s}\n' "${calls}" >"${import_topology_delta}"
}
do_import iteration-0000
first_import_sha=$(campaign_digest "${imported_summaries}")
rm -- "${imported_summaries}" "${import_diagnostics}" \
  "${import_topology_delta}"
do_import iteration-0000
[[ $(<"${import_calls}") -eq 1 ]] \
  || fail "an exact importer cache hit reran the importer"
[[ $(campaign_digest "${imported_summaries}") == "${first_import_sha}" ]] \
  || fail "an importer cache hit changed the summary bytes"
printf '{"event":"CONCOLIC_REGION_RESULT","changed":true}\n' \
  >"${import_raw}"
rm -- "${imported_summaries}" "${import_diagnostics}" \
  "${import_topology_delta}"
do_import iteration-0000
[[ $(<"${import_calls}") -eq 2 ]] \
  || fail "changed raw replay content did not invalidate the import cache"
changed_import_key=$(campaign_import_cache_key iteration-0000)
printf 'corrupt\n' \
  >"${import_cache_root}/import/${changed_import_key}/summaries.jsonl"
if (do_import iteration-0000) >/dev/null 2>&1; then
  fail "a corrupt importer cache entry was treated as a cache miss"
fi

seed_cache_root="${test_tmp}/seed-cache"
seed_calls="${test_tmp}/seed-calls"
printf '0\n' >"${seed_calls}"
seed_config_base="${test_tmp}/seed-base.properties"
seed_config_proposal="${test_tmp}/seed-proposal.properties"
seed_config_changed="${test_tmp}/seed-changed.properties"
seed_config_similar="${test_tmp}/seed-similar.properties"
printf 'schedule_max_jobs=8\n' >"${seed_config_base}"
printf 'schedule_max_jobs=8\n  causynth_symbolic_root_proposal = "/tmp/proposal.json"\n' \
  >"${seed_config_proposal}"
printf 'schedule_max_jobs=9\n' >"${seed_config_changed}"
printf 'schedule_max_jobs=8\nx_causynth_symbolic_root_proposal=/tmp/p.json\n' \
  >"${seed_config_similar}"
[[ $(campaign_seed_config_digest "${seed_config_base}") \
    == $(campaign_seed_config_digest "${seed_config_proposal}") ]] \
  || fail "the plan-only proposal property changed the seed config digest"
[[ $(campaign_seed_config_digest "${seed_config_base}") \
    != $(campaign_seed_config_digest "${seed_config_changed}") ]] \
  || fail "a seed-relevant config change was ignored"
[[ $(campaign_seed_config_digest "${seed_config_base}") \
    != $(campaign_seed_config_digest "${seed_config_similar}") ]] \
  || fail "a similar config key was mistaken for the proposal property"
config_file="${seed_config_base}"
causynth_cache_dir="${seed_cache_root}"
causynth_analysis_scope=test-scope
causynth_process_dirs="${test_tmp}/classes"
workload_work_dir="${test_tmp}"
workload_command=test-workload
trace_test=test.Workload#run
unset HDFS11741_TRACE_JDK HDFS11741_MAX_EVENTS HDFS11741_EXTRA_JVM_ARGS
campaign_provenance=$(jq -n '
  {jar:{sha256:"jar"}, config:{sha256:"config"},
   targetSpec:{sha256:"target"}, communicationMappings:{sha256:"mappings"},
   loopBounds:{sha256:"bounds"}, symbolicInputs:{sha256:"symbols"},
   productionClasses:{sha256:"classes"},
   workload:{testClasses:{sha256:"tests"},classpathSha256:"classpath"},
   source:{graphchecker:{head:"g",worktreeDigest:"gd"},
           workload:{head:"h",worktreeDigest:"hd"}}}')
campaign_provenance=$(jq --arg sha "$(campaign_digest "${config_file}")" \
  '.config.sha256 = $sha' <<<"${campaign_provenance}")
configure_seed_outputs() {
  local root=$1
  causynth_output_dir="${root}"
  candidate_graph="${root}/candidate_dataflow_edges.jsonl.gz"
  runtime_region_plan="${root}/runtime/concolic_region_plan.jsonl"
  refined_graph="${root}/runtime/refined_dataflow_edges.jsonl.gz"
}
do_analyze() {
  local calls
  calls=$(( $(<"${seed_calls}") + 1 ))
  printf '%s\n' "${calls}" >"${seed_calls}"
  mkdir -p "${causynth_output_dir}"
  printf 'candidate-%s\n' "${calls}" >"${candidate_graph}"
  printf 'target-%s\n' "${calls}" \
    >"${causynth_output_dir}/target_resolved.json"
  printf 'skeleton-%s\n' "${calls}" \
    >"${causynth_output_dir}/region_skeletons.jsonl.gz"
  printf 'calls-%s\n' "${calls}" \
    >"${causynth_output_dir}/communication_call_sites.jsonl.gz"
  printf 'loops-%s\n' "${calls}" \
    >"${causynth_output_dir}/retained_loops.jsonl.gz"
  printf 'gaps-%s\n' "${calls}" \
    >"${causynth_output_dir}/communication_gaps.jsonl.gz"
}
do_workload() {
  local calls
  calls=$(<"${seed_calls}")
  mkdir -p "$(dirname "${runtime_region_plan}")/skeleton-pass"
  printf 'plan-%s\n' "${calls}" >"${runtime_region_plan}"
  printf 'refined-%s\n' "${calls}" >"${refined_graph}"
  printf 'selected-%s\n' "${calls}" \
    >"$(dirname "${runtime_region_plan}")/skeleton-pass/region_skeletons.jsonl"
}
configure_seed_outputs "${test_tmp}/seed-output-one"
campaign_root="${test_tmp}/seed-campaign-one"
mkdir -p "${campaign_root}"
baseline_seed_key=$(campaign_seed_cache_key)
campaign_seed
[[ $(<"${seed_calls}") -eq 1 ]] || fail "the seed stage did not run once"
configure_seed_outputs "${test_tmp}/seed-output-two"
campaign_root="${test_tmp}/seed-campaign-two"
mkdir -p "${campaign_root}"
campaign_seed
[[ $(<"${seed_calls}") -eq 1 ]] \
  || fail "an exact seed cache hit reran static analysis or trace indexing"
[[ $(jq -r '.cache.status' "${campaign_root}/seed-manifest.json") == HIT ]] \
  || fail "the seed manifest did not record its cache hit"
config_file="${seed_config_proposal}"
campaign_provenance=$(jq \
  --arg configSha "$(campaign_digest "${config_file}")" \
  '.config.sha256 = $configSha | .symbolicRootProposal =
  {path:"/tmp/proposal.json",sha256:"changed-proposal"}' \
  <<<"${campaign_provenance}")
[[ $(campaign_seed_cache_key) == "${baseline_seed_key}" ]] \
  || fail "the real proposal config path invalidated the seed cache key"
configure_seed_outputs "${test_tmp}/seed-output-proposal"
campaign_root="${test_tmp}/seed-campaign-proposal"
mkdir -p "${campaign_root}"
campaign_seed
[[ $(<"${seed_calls}") -eq 1 ]] \
  || fail "a changed root proposal invalidated reusable seed analysis"
campaign_provenance=$(jq \
  '.source.graphchecker.worktreeDigest = "changed-tool-source"' \
  <<<"${campaign_provenance}")
[[ $(campaign_seed_cache_key) != "${baseline_seed_key}" ]] \
  || fail "changed GraphChecker source did not invalidate the seed cache"
campaign_provenance=$(jq \
  '.source.graphchecker.worktreeDigest = "gd"' \
  <<<"${campaign_provenance}")
campaign_provenance=$(jq '.loopBounds.sha256 = "changed-bounds"' \
  <<<"${campaign_provenance}")
configure_seed_outputs "${test_tmp}/seed-output-three"
campaign_root="${test_tmp}/seed-campaign-three"
mkdir -p "${campaign_root}"
campaign_seed
[[ $(<"${seed_calls}") -eq 2 ]] \
  || fail "changed loop-bound content did not invalidate the seed cache"

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
[[ $(jq -r '.gapCount' "${large_gaps}") -eq 0 ]] \
  || fail "classifier telemetry became an acceptance blocker"
[[ $(jq -r '.telemetryCount' "${large_gaps}") -eq 1 ]] \
  || fail "file-backed coverage aggregation lost the large delta"
[[ $(jq -r '.telemetryGaps[0].code' "${large_gaps}") == "BIG" ]] \
  || fail "file-backed coverage aggregation changed the large delta"
# A coverage gap the worklist only forwarded from an imported summary names
# no region of its own; the recorded evidence identity is the only subject it
# has, and its free-text detail says more than the reason code alone.  A gap
# row that names neither is not actionable, so the projection reads both.
: >"${test_tmp}/empty-delta.jsonl"
forwarded_closures="${test_tmp}/forwarded-closures.json"
jq -n '[{schemaVersion: 1, kind: "REGION_PATH_WORKLIST",
  coverageGaps: [
    {kind: "RPC_HANDOFF_GAP", reason: "RPC_HANDOFF_UNKNOWN_HANDLE",
     stage: "ATTACH",
     detail: "required communication port carried no live VM handle: XCH.p",
     evidenceIdentity: {taskId: "task-consumer",
                        occurrenceId: "consumer#1#a1"}},
    {kind: "OUTPUT_VERSION_ALIGNMENT_GAP", reason: "BOUND_EXCEEDED",
     regionId: "REGION.own", pathKey: "", siteId: "s", occurrence: 9}]}]' \
  >"${forwarded_closures}"
forwarded_gaps="${test_tmp}/forwarded-gaps.json"
campaign_write_coverage_gaps "${large_composition}" "${large_reach}" \
  "${large_diagnostics}" "${test_tmp}/empty-delta.jsonl" \
  "${forwarded_closures}" "${forwarded_gaps}"
[[ $(jq -r '.gapCount' "${forwarded_gaps}") -eq 2 ]] \
  || fail "worklist coverage gaps stopped blocking incomplete claims"
[[ $(jq -r '.telemetryCount' "${forwarded_gaps}") -eq 0 ]] \
  || fail "forwarded coverage gaps were not both projected"
[[ $(jq -r '.gaps[] | select(.code == "RPC_HANDOFF_GAP") | .subject' \
      "${forwarded_gaps}") == "task-consumer" ]] \
  || fail "a forwarded gap was projected without its evidence subject"
[[ $(jq -r '.gaps[] | select(.code == "RPC_HANDOFF_GAP") | .detail' \
      "${forwarded_gaps}") \
    == "RPC_HANDOFF_UNKNOWN_HANDLE: required communication port carried no live VM handle: XCH.p" ]] \
  || fail "a forwarded gap lost its detail"
[[ $(jq -r '.gaps[] | select(.code == "OUTPUT_VERSION_ALIGNMENT_GAP") | .subject' \
      "${forwarded_gaps}") == "REGION.own" ]] \
  || fail "a worklist gap stopped naming its own region"
[[ $(jq -r '.gaps[] | select(.code == "OUTPUT_VERSION_ALIGNMENT_GAP") | .detail' \
      "${forwarded_gaps}") == "BOUND_EXCEEDED" ]] \
  || fail "a worklist gap stopped naming its reason"

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

# Seed replay is one fresh JVM per singleton member plan. They run in parallel,
# while the merged artifact remains a deterministic concatenation.
(
  replay_iteration="${test_tmp}/singleton-session"
  replay_calls="${replay_iteration}/calls"
  concolic_worker_count=8
  mkdir -p "${replay_iteration}/instrumented-classes" \
    "${replay_iteration}/workers/task-a" \
    "${replay_iteration}/workers/task-b"
  printf '{"taskId":"task-a"}\n{"taskId":"task-b"}\n' \
    >"${replay_iteration}/execution_task_plan.jsonl"
  printf '{"taskId":"task-a"}\n' \
    >"${replay_iteration}/workers/task-a/execution_task_plan.jsonl"
  printf '{"taskId":"task-b"}\n' \
    >"${replay_iteration}/workers/task-b/execution_task_plan.jsonl"
  : >"${replay_calls}"
  campaign_replay() {
    local role=$1 plan=$2 ids=$3 classes=$4 results=$5 worker=$6
    [[ "${role}" == worker && $(campaign_task_ids "${plan}") == "${ids}" \
      && $(wc -l <"${plan}") -eq 1 ]] \
      || fail "seed replay did not use a singleton member plan"
    mkdir -p "${worker}"
    printf '%s\n' "${ids}" >>"${replay_calls}"
    printf '{"event":"CONCOLIC_REGION_RESULT","taskId":"%s"}\n' \
      "${ids}" >"${results}"
  }
  campaign_session_replay "${replay_iteration}"
  [[ $(LC_ALL=C sort "${replay_calls}" | paste -sd, -) == "task-a,task-b" ]] \
    || fail "session members were not replayed independently"
  [[ $(jq -r '.taskId' \
      "${replay_iteration}/seed-result/concolic_region_results.jsonl" \
      | paste -sd, -) == "task-a,task-b" ]] \
    || fail "singleton replay results were not merged"
)

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
causynth_communication_mappings=""
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


# LOOP-1, shell half.  The per-loop K_L declarations are a required key rather
# than an optional one: an unset key and a campaign whose declarations never
# arrived are the same run -- every retained condition loop silently at the
# core default -- and nothing in the published artifacts distinguishes them.
loop_bounds_declared="${test_tmp}/loop-bounds.jsonl"
printf '# this workload retains no condition-controlled loop\n' \
  >"${loop_bounds_declared}"
configure_minimal_workflow() {
  project_repo="${test_tmp}"
  project_module_dir="${test_tmp}"
  project_classes_dir="${test_tmp}"
  project_classpath="${test_tmp}"
  causynth_output_dir="${test_tmp}/out"
  causynth_target_spec="${test_tmp}/target.yaml"
  causynth_communication_mappings=""
  causynth_symbolic_inputs=""
  causynth_loop_bounds="${loop_bounds_declared}"
  custom_jdk_home="${test_tmp}/jdk"
  z3_bin=z3
  workload_command=true
  trace_test="a.B#c"
  solver_timeout_ms=1000
  schedule_max_jobs=1
  reach_max_inputs=1
  reach_max_valuations=1
  concolic_worker_count=1
  campaign_max_iterations=1
  producer_max_paths_per_region=""
  producer_max_flips_per_path=""
  producer_max_path_tasks=""
}

configure_minimal_workflow
validate_config >/dev/null \
  || fail "a workflow that declares its loop bounds was rejected"

# A declarations file holding no row is a statement, not an omission: the
# fixtures that retain no condition loop still have to make it.
: >"${loop_bounds_declared}"
configure_minimal_workflow
validate_config >/dev/null \
  || fail "an empty loop bound declarations file was rejected"

# Both refusals exit rather than return, so each is observed from its own
# subshell with the rest of the workflow left valid.
if ( configure_minimal_workflow; causynth_loop_bounds=""; \
    validate_config ) >/dev/null 2>&1; then
  fail "a workflow that names no loop bound declarations was accepted"
fi
if ( configure_minimal_workflow; \
    causynth_loop_bounds="${test_tmp}/absent-loop-bounds.jsonl"; \
    validate_config ) >/dev/null 2>&1; then
  fail "a workflow naming absent loop bound declarations was accepted"
fi

# GATE-1, shell half.  Both properties under test are decisions campaign_emit
# makes about artifacts it has just written, so the stage is exercised whole:
# the frozen inputs are re-read before anything is published, the frozen
# provenance travels in result.json, and a claim reached with named gaps still
# open does not exit zero.
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
    "${emit_iteration}/seed-result" "${emit_iteration}/workers/task-target"
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

  printf 'STAGE\t7\n' >"${campaign_stage_metrics}"
  printf '(assert true)\n' >"${campaign_final}/candidate.smt2"
  jq -n '{schemaVersion: 2, kind: "CONCOLIC_COMPOSED_SMT",
    finalStatus: "FINAL_READY", finalStatusRefusals: [],
    canonicalModel: {counts: {exactBindings: 1, guardedBindings: 0,
      unknownArmBindings: 0, candidateBindings: 0, fieldVersions: 1,
      fieldReads: 1}, gaps: []}}' >"${composition_manifest}"
  jq -n '{schemaVersion: 3, kind: "BOOLEAN_REACH_CONDITION_REPORT",
    state: "sat", reachCondition: {reachability: "REACHABLE"},
    unsatClosureComplete: false, gaps: [], valuations: []}' >"${reach_report}"
  printf '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[]}\n' \
    >"${emit_iteration}/workers/task-target/path_closure.json"
  printf '{"taskId":"task-target","published":true}\n' \
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
  ( campaign_emit "${emit_iteration}" ) >"${emit_root}/emit.log" 2>&1 \
    || emit_status=$?
}

emit_fixture
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a gapless accepted candidate did not exit zero (${emit_status}); $(<"${emit_root}/emit.log")"
[[ $(jq -r '.claim' "${campaign_final}/result.json") == "SAT_CANDIDATE" ]] \
  || fail "the accepted claim was not published"
[[ $(jq -r '.provenance.loopBounds.sha256' "${campaign_final}/result.json") \
    == "$(campaign_digest "${emit_bounds}")" ]] \
  || fail "result.json does not carry the frozen provenance"
[[ $(jq -r '.provenance.config.path' "${campaign_final}/result.json") \
    == "${emit_config}" ]] \
  || fail "result.json provenance names a different frozen config"

# Importer diagnostics remain visible telemetry and do not re-score an
# accepted selected causal witness.
emit_fixture
printf '{"code":"UNRESOLVED","taskId":"task-target","detail":"open"}\n' \
  >"${emit_iteration}/import_diagnostics.jsonl"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "importer telemetry withheld an accepted candidate"
[[ $(jq -r '.gapCount' "${campaign_final}/result.json") -eq 0 ]] \
  || fail "importer telemetry became an acceptance blocker"
[[ $(jq -r '.telemetryCount' "${campaign_final}/result.json") -eq 1 ]] \
  || fail "the published result lost importer telemetry"
[[ $(jq -r '.claim' "${campaign_final}/result.json") == "SAT_CANDIDATE" ]] \
  || fail "the gap count re-scored the Composer's published claim"

# A frozen input that moved underneath the run is refused before anything is
# published: provenance that was current at FREEZE is not provenance now.
emit_fixture
printf 'schedule_max_jobs=1\n' >>"${emit_config}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "EMIT published a candidate whose frozen config had changed"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "EMIT published a result for a drifted generation"
grep -q 'changed after it was frozen' "${emit_root}/emit.log" \
  || fail "the drifted frozen input was not named"

emit_fixture
rm -r -- "${emit_classes}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "EMIT published a candidate whose production classes were removed"

echo "run_engine campaign helper tests passed"
