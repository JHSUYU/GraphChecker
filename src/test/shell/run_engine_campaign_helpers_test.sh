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
    '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[{"kind":"PATH_FLIP_NOT_ADMITTED","queryKey":"flip","reason":"UNEXPLORED"}]}' \
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

echo "run_engine campaign helper tests passed"
