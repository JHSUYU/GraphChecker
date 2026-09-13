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

# EMIT publishes the gap ledger beside the gaps it classed, and the ledger is
# the Java table -- there is no second copy of it to test against.  The built
# jar is therefore an input to these helper tests.
graphchecker_jar="${repo}/target/GraphChecker-1.0-SNAPSHOT-jar-with-dependencies.jar"
[[ -s "${graphchecker_jar}" ]] \
  || fail "these tests need the packaged jar: run mvn -o package -DskipTests"
java_bin=${JAVA_HOME:+${JAVA_HOME}/bin/}java
graphchecker_work_dir="${repo}"

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
  # The two gap sources EMIT reads outside the iteration directory: the
  # static catalog's own gaps and the planning gaps the runtime plan carries
  # in its catalog row.
  causynth_output_dir="${emit_root}/causynth"
  mkdir -p "${causynth_output_dir}"
  runtime_region_plan="${emit_root}/concolic_region_plan.jsonl"
  jq -n -c '{schemaVersion: 2, kind: "CONCOLIC_RUNTIME_MODEL_CATALOG",
    edges: [], regions: [], gaps: []}' >"${runtime_region_plan}"

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
    symbolicPropagationGaps: [],
    boundedLoopComposition: {gaps: []},
    guardedReadModelComplete: false,
    guardedReadModel: {
      schemaVersion: 1, kind: "DIRECT_GUARDED_READ_MODEL",
      authority: "VM_READ_TIME_CANDIDATE_SNAPSHOT_V1",
      complete: true, reads: []}, gaps: []}' \
    >"${composition_manifest}"
  # The reach report carries the ClaimPolicy decision the solver stage made
  # from it. EMIT publishes that decision; it does not re-derive one, so the
  # fixture states the claim exactly as ClaimPolicy states it.
  jq -n '{schemaVersion: 4, kind: "BOOLEAN_REACH_CONDITION_REPORT",
    state: "sat", reachCondition: {reachability: "REACHABLE",
      degeneracyCheck: "CONSTRAINED_ROOT_SPACE"},
    unsatClosureComplete: false, gaps: [],
    valuations: [{values: [false], status: "sat"},
                 {values: [true], status: "unsat"}],
    campaignClaim: {schemaVersion: 1, kind: "CAMPAIGN_CLAIM",
      claim: "SAT_CANDIDATE",
      claimReason: "a valuation satisfies the target predicate inside the recorded model and a symbolic root flips it",
      blockers: [], blockerCount: 0, whyNotAccepted: "",
      rootSpace: {consumerBoundaryFamilies: 1, consumerBoundaryArms: 2,
                  declaredWireFlows: 0, wireFlows: []}}}' \
    >"${reach_report}"
  printf '%s\n' \
    '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST","coverageGaps":[{"kind":"PATH_FLIP_REPLAY_NOT_ADMITTED","queryKey":"flip","reason":"UNEXPLORED"},{"kind":"PATH_FLIP_SOLVER_TIMEOUT","queryKey":"slow-flip","reason":"SOLVER_TIMEOUT"}]}' \
    >"${emit_iteration}/workers/task-target/path_closure.json"
  # DECIDE publishes this ledger and EMIT copies it into the result, so the
  # fixture states it exactly as TargetOccurrenceElection states it.
  campaign_target_ledger="${campaign_final}/target_occurrences.json"
  jq -n '{schemaVersion: 1, kind: "TARGET_OCCURRENCE_LEDGER",
    occurrenceCount: 2, composedCount: 2,
    chosenOccurrenceId: "REGION.T#1", chosenTaskId: "task-target",
    chosenSupport: "SAT_CANDIDATE_EXPLAINED_WITNESS",
    electionReason: "the campaign claim rests on REGION.T#1",
    occurrences: [
      {occurrenceId: "REGION.T#1", status: "COMPOSED",
       support: "SAT_CANDIDATE_EXPLAINED_WITNESS", claim: "SAT_CANDIDATE",
       blockerCount: 0, composeWallMillis: 51234, solveWallMillis: 9001,
       chosen: true},
      {occurrenceId: "REGION.T#2", status: "COMPOSED",
       support: "INCONCLUSIVE", claim: "INCONCLUSIVE_PARTIAL",
       blockerCount: 2, composeWallMillis: 48010, solveWallMillis: 7700,
       chosen: false}]}' \
    >"${campaign_target_ledger}"
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

# The same fixture as the solver stage published it for hdfs-17899-bug3: a
# REACHABLE formula whose degeneracy question ClaimPolicy could not decide,
# whose Boolean root never flips satisfiability, and whose experiment declares
# wire flows the composition never realized.
emit_fixture_undecided_roots() {
  emit_fixture
  jq -n '{schemaVersion: 4, kind: "BOOLEAN_REACH_CONDITION_REPORT",
    state: "CANDIDATE_READY", reachCondition: {reachability: "REACHABLE",
      degeneracyCheck: "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9"},
    unsatClosureComplete: false, gaps: [],
    valuations: [{values: [false], status: "sat"},
                 {values: [true], status: "sat"}],
    campaignClaim: {schemaVersion: 1, kind: "CAMPAIGN_CLAIM",
      claim: "INCONCLUSIVE_PARTIAL",
      claimReason: "3 blocker(s) withhold an accepted claim from a REACHABLE solver result: UNDECIDED_ROOT_SPACE,TARGET_UNCONSTRAINED_BY_ROOTS,DECLARED_WIRE_FLOWS_UNREALIZED",
      blockerCount: 3,
      blockers: [
        {code: "UNDECIDED_ROOT_SPACE",
         subject: "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9",
         detail: "the degeneracy question was not decided"},
        {code: "TARGET_UNCONSTRAINED_BY_ROOTS", subject: "",
         detail: "no symbolic root flips the target predicate"},
        {code: "DECLARED_WIRE_FLOWS_UNREALIZED", subject: "block-key-id",
         detail: "the composition realized neither side of 1 of 2 declared WIRE_FLOW(s): block-key-id"}],
      whyNotAccepted: ("claim=INCONCLUSIVE_PARTIAL: 3 blocker(s) withhold acceptance\n  UNDECIDED_ROOT_SPACE [UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:9]: the degeneracy question was not decided\n  TARGET_UNCONSTRAINED_BY_ROOTS: no symbolic root flips the target predicate\n  DECLARED_WIRE_FLOWS_UNREALIZED [block-key-id]: the composition realized neither side of 1 of 2 declared WIRE_FLOW(s): block-key-id"),
      rootSpace: {consumerBoundaryFamilies: 99, consumerBoundaryArms: 240,
                  declaredWireFlows: 2,
                  wireFlows: [
                    {flow: "block-key-id", realized: false,
                     mechanism: "EXCHANGE_PORT_PAIR",
                     consumerRealized: true, producerRealized: false},
                    {flow: "data-encryption-key-id", realized: true,
                     mechanism: "EXCHANGE_PORT_PAIR",
                     consumerRealized: true, producerRealized: true}]}}}' \
    >"${reach_report}"
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
  and .telemetryCount >= 2' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its propagation provenance"

# DECIDE-1: a verdict that rests on one of several observed executions of the
# annotated target says which one, in the result itself, with every other
# execution's verdict beside it. The harness reads one document.
jq -e '.targetOccurrence == "REGION.T#1"
  and (.targetOccurrences | length) == 2
  and ([.targetOccurrences[] | select(.chosen)] | length) == 1
  and ([.targetOccurrences[] | select(.chosen) | .support]
       == ["SAT_CANDIDATE_EXPLAINED_WITNESS"])
  and (.targetOccurrenceReason | test("REGION.T#1"))' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not name the elected target occurrence: \
$(jq -c '.targetOccurrence, .targetOccurrences' \
    "${campaign_final}/result.json")"
# Per-occurrence stage times are telemetry a reader needs to size the loop.
jq -e '[.targetOccurrences[] | .composeWallMillis] == [51234, 48010]
  and [.targetOccurrences[] | .solveWallMillis] == [9001, 7700]' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost the per-occurrence stage times"
# CLAIM-1: the whole policy decision, so no consumer has to open the solver
# report to find the claim this file was written from.
jq -e '.rootSpace.consumerBoundaryFamilies == 1
  and .rootSpace.consumerBoundaryArms == 2' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not carry the claim root space: \
$(jq -c '.rootSpace' "${campaign_final}/result.json")"

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
# An accepted claim has nothing to explain, and says so with an empty string
# rather than by omitting the field the owner reads.
jq -e '.blockers == [] and .blockerCount == 0 and .whyNotAccepted == ""' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an accepted claim published blockers"

# GAP-1: a gap raised by a stage the claim cannot see still withholds the
# candidate, because one ledger classes every code and an unregistered code
# is blocking.  BOUND_INSUFFICIENT is the finalizer truncation that used to
# build a refusal string and throw it away.
emit_fixture
jq -n -c '{schemaVersion: 2, kind: "CONCOLIC_RUNTIME_MODEL_CATALOG",
  edges: [], regions: [],
  gaps: [{schemaVersion: 1, kind: "RUNTIME_PLAN_GAP",
          code: "BOUND_INSUFFICIENT", subject: "port\nsite",
          detail: "static site demands more accesses than are retained"}]}' \
  >"${runtime_region_plan}"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "a plan gap did not withhold the candidate (exit ${emit_status}): \
$(<"${emit_root}/emit.log")"
jq -e '.gapCount == 1
  and (.gaps[0].stage == "PLAN")
  and (.gaps[0].code == "BOUND_INSUFFICIENT")
  and (.gaps[0].class == "BLOCKING")' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the plan gap was not published as blocking: \
$(jq -c '.gaps' "${campaign_final}/gaps.json")"
jq -e '.accepted == false and .gapCount == 1' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "result.json did not state that acceptance was withheld"

# GAP-3: a code nobody registered is blocking.  This fixture used to publish
# two invented composition gap reasons as accepted telemetry; under one
# ledger they withhold the candidate until somebody writes down why they
# cannot break a chain.
emit_fixture
jq '.symbolicPropagationGaps = [{reason: "UNRELATED_FAMILY_OPEN",
                                 subject: "CBF.fixture", detail: "invented"}]
    | .boundedLoopComposition.gaps = [{reason: "LOOP_BOUND_OPEN",
                                       subject: "loop.fixture",
                                       detail: "invented"}]' \
  "${composition_manifest}" >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "unregistered gap codes did not withhold the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '[.gaps[].code] | sort == ["LOOP_BOUND_OPEN", "UNRELATED_FAMILY_OPEN"]' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the unregistered codes were not both blocking: \
$(jq -c '[.gaps[].code]' "${campaign_final}/gaps.json")"

# GAP-4: the three region codes are decided against the replay slice, not by
# a blanket rule.  The static plan over-approximates; a region root
# dependence never selected is not a chain element.  With no schedule index
# in the fixture the slice is unknown, and an unknown slice blocks.
emit_fixture
printf '%s\n' '{"code":"REGION_CAUSAL_ANCHOR_NOT_OBSERVED","taskId":"TASK.REPLAY.kept","detail":"anchor never observed"}' \
  >"${emit_iteration}/import_diagnostics.jsonl"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "an unknown replay slice did not block a region code \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '[.gaps[] | select(.code == "REGION_CAUSAL_ANCHOR_NOT_OBSERVED")
        | .sliceVerdict] == ["SLICE_NOT_APPLIED"]' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the unknown slice was not named on the row: \
$(jq -c '.gaps' "${campaign_final}/gaps.json")"

# With a slice that kept one occurrence and pruned another, the same code
# blocks on the kept task and is diagnostic on the pruned one.
emit_fixture
printf '%s\n' \
  '{"code":"REGION_CAUSAL_ANCHOR_NOT_OBSERVED","taskId":"TASK.REPLAY.kept","detail":"anchor never observed"}' \
  '{"code":"REGION_CAUSAL_ANCHOR_NOT_OBSERVED","taskId":"TASK.REPLAY.pruned","detail":"anchor never observed"}' \
  >"${emit_iteration}/import_diagnostics.jsonl"
jq -n '{schemaVersion: 1, kind: "RUNTIME_REGION_PATH_SCHEDULE_INDEX",
  replayTaskSlice: {replayTaskSliceApplied: true, keptOccurrenceCount: 1},
  members: [{taskId: "TASK.REPLAY.kept", occurrenceId: "OCC.kept",
             regionId: "REGION.kept", role: "TARGET"}]}' \
  >"${emit_iteration}/runtime_workflow_schedule_index.json"
printf '%s\n' \
  '{"taskId":"TASK.REPLAY.kept","occurrenceId":"OCC.kept"}' \
  '{"taskId":"TASK.REPLAY.pruned","occurrenceId":"OCC.pruned"}' \
  >"${emit_iteration}/execution_task_plan.jsonl"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "a region code on the kept slice did not block \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 1
  and (.gaps[0].subject == "TASK.REPLAY.kept")
  and (.gaps[0].sliceVerdict == "ON_KEPT_SLICE:OCC.kept")
  and ([.telemetryGaps[] | select(.subject == "TASK.REPLAY.pruned")
        | .sliceVerdict] == ["SLICE_PRUNED:OCC.pruned"])' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the slice-aware split is wrong: \
$(jq -c '[(.gaps+.telemetryGaps)[]|{code,subject,class,sliceVerdict}]' \
    "${campaign_final}/gaps.json")"
# The rationale travels with the row, so a reader does not have to open the
# ledger to see why a gap was classed the way it was.
jq -e '[(.gaps + .telemetryGaps)[] | select((.classReason // "") == "")]
       | length == 0' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "a gap row carries no classification reason"

# GAP-2: the ledger is published beside the gaps it classed, and it names its
# own exceptions rather than leaving a reader to guess the default.
jq -e '.kind == "GAP_LEDGER" and .defaultClass == "BLOCKING"
  and (.diagnostic | index("SELECTED_PATH_SET_INCOMPLETE")) != null
  and (.entries | length) > 100' \
  "${campaign_final}/gap_ledger.json" >/dev/null \
  || fail "EMIT published no usable gap ledger"

# An undecided root space is no longer a witness. The claim ClaimPolicy
# decided is published with every named blocker and one readable summary, and
# the run exits 2 because it named no accepted candidate.
emit_fixture_undecided_roots
run_emit
[[ "${emit_status}" -eq 2 ]] \
  || fail "an undecided root space was accepted (exit ${emit_status}): \
$(<"${emit_root}/emit.log")"
[[ $(jq -r '.claim' "${campaign_final}/result.json") \
    == INCONCLUSIVE_PARTIAL ]] \
  || fail "the undecided root space did not publish INCONCLUSIVE_PARTIAL"
jq -e '[.blockers[].code] == ["UNDECIDED_ROOT_SPACE",
    "TARGET_UNCONSTRAINED_BY_ROOTS", "DECLARED_WIRE_FLOWS_UNREALIZED"]
  and .blockerCount == 3' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result did not publish the named blockers: \
$(jq -c '.blockers' "${campaign_final}/result.json")"
# The unrealized flow is named, not counted: an owner acts on the name.
jq -e '[.blockers[] | select(.code == "DECLARED_WIRE_FLOWS_UNREALIZED")
    | .subject] == ["block-key-id"]' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the wire-flow blocker did not name the unrealized flow"
# The per-flow realization rows are published with the claim, so the realized
# flow is visible next to the one that blocked it.
jq -e '.evidence.declaredWireFlows == 2
  and .evidence.consumerBoundaryFamilies == 99
  and ([.evidence.wireFlows[] | select(.realized)] | length) == 1' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its per-flow realization evidence: \
$(jq -c '.evidence' "${campaign_final}/result.json")"
# The one view: a header plus one line per blocker, printed and recorded.
[[ $(jq -r '.whyNotAccepted' "${campaign_final}/result.json" \
      | wc -l) -eq 4 ]] \
  || fail "whyNotAccepted does not name one blocker per line"
grep -q 'DECLARED_WIRE_FLOWS_UNREALIZED' "${emit_root}/emit.log" \
  || fail "EMIT did not print the blocker summary"
# A stage-local FINAL_READY with zero aggregate gaps is exactly the state the
# jq gate accepted. EMIT publishes the policy's claim over it.
jq -e '.finalStatus == "FINAL_READY" and .gapCount == 0' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the withheld fixture no longer reproduces the accepted state"

# The claim has one home. A reach report without the policy's decision is a
# report EMIT may not publish a result from.
emit_fixture
jq 'del(.campaignClaim)' "${reach_report}" >"${reach_report}.tmp"
mv "${reach_report}.tmp" "${reach_report}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a reach report with no ClaimPolicy decision was published"
grep -q 'no ClaimPolicy decision' "${emit_root}/emit.log" \
  || fail "the missing claim was not named: $(<"${emit_root}/emit.log")"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "a result was published without a claim"

# The elected occurrence has one home too. A run whose DECIDE stage published
# no ledger is a run EMIT may not publish a result from: the claim would then
# rest on an occurrence nothing named.
emit_fixture
rm -f "${campaign_target_ledger}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a result was published with no target occurrence ledger"
grep -q 'no target occurrence ledger' "${emit_root}/emit.log" \
  || fail "the missing ledger was not named: $(<"${emit_root}/emit.log")"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "a result was published without a target occurrence ledger"

# COMPOSE-1: one occurrence, one artifact directory, derived from the
# occurrence identity alone so the same occurrence always lands in the same
# place and two occurrences never share one.
[[ "$(campaign_occurrence_key \
      'hdfs-17897/dn0#epoch0/region/REGION.53092d3e#1')" \
    == 'hdfs-17897_dn0_epoch0_region_REGION.53092d3e_1' ]] \
  || fail "the occurrence key is not a filesystem name: \
$(campaign_occurrence_key 'hdfs-17897/dn0#epoch0/region/REGION.53092d3e#1')"
[[ "$(campaign_occurrence_key 'a#1')" \
    != "$(campaign_occurrence_key 'a#2')" ]] \
  || fail "two occurrences share one artifact directory"

# PLAN-1: the schedule index says which members carry a target-reach goal, so
# EXPLORE and COMPOSE can address every observed occurrence of the annotated
# site and not only the elected one.
index_root="${test_tmp}/schedule-index"
mkdir -p "${index_root}"
index_file="${index_root}/runtime_workflow_schedule_index.json"
jq -n '{schemaVersion: 2, kind: "RUNTIME_REGION_PATH_SCHEDULE_INDEX",
  members: [
    {campaignId: "CAMPAIGN.1", regionId: "REGION.T",
     relationKey: "rel/REGION.T", occurrenceId: "REGION.T#2",
     goalId: "GOAL.TARGET_REACH.2", taskId: "task-a", role: "TARGET",
     targetReachGoal: true},
    {campaignId: "CAMPAIGN.1", regionId: "REGION.T",
     relationKey: "rel/REGION.T", occurrenceId: "REGION.T#1",
     goalId: "GOAL.TARGET_REACH.1", taskId: "task-b", role: "DEPENDENCY",
     targetReachGoal: true},
    {campaignId: "CAMPAIGN.1", regionId: "REGION.D",
     relationKey: "rel/REGION.D", occurrenceId: "REGION.D#1",
     goalId: "GOAL.REGION_PATH.1", taskId: "task-c", role: "DEPENDENCY",
     targetReachGoal: false}]}' >"${index_file}"
index_rows=$(campaign_decode_index_members "${index_file}") \
  || fail "a complete schedule index was refused"
[[ "$(printf '%s\n' "${index_rows}" | cut -f7 | tr '\n' ' ')" \
    == "true true false " ]] \
  || fail "the decoded members do not name the target occurrences: \
$(printf '%s\n' "${index_rows}" | cut -f7 | tr '\n' ' ')"
# An index whose elected TARGET is not a target-reach member is an index this
# shell cannot dispatch on: every later stage composes from that flag.
jq '.members[0].targetReachGoal = false' "${index_file}" \
  >"${index_file}.broken"
( campaign_decode_index_members "${index_file}.broken" ) >/dev/null 2>&1 \
  && fail "a TARGET with no target-reach goal was accepted"
# An index from before the flag existed is not a silently narrowed index.
jq 'del(.members[].targetReachGoal)' "${index_file}" \
  >"${index_file}.old"
( campaign_decode_index_members "${index_file}.old" ) >/dev/null 2>&1 \
  && fail "a schedule index with no target-reach flag was accepted"

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
# 40 again: `replay_task_budget` joined the table in bef2db898 without this
# count being raised, and has now been deleted -- it capped nothing, no
# experiment set it, and its own test asserted it dropped no task.
[[ "$(print_normalized_config | wc -l)" -eq 40 ]] \
  || fail "config prints a different number of keys than it used to: \
$(print_normalized_config | wc -l)"

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

# EXPLORE-1: a forced closure stop is coverage telemetry on every pending
# worklist, and it publishes that worklist as the member's closure so the
# final gap report can read it.
stop_member="${test_tmp}/stop/workers/task-a"
stop_wave="${stop_member}/obligations-0003"
mkdir -p "${stop_wave}"
printf '%s\n' '{"schemaVersion":1,"kind":"REGION_PATH_WORKLIST",
  "state":"PENDING","coverageState":"PARTIAL","regionId":"REGION.A",
  "occurrenceId":"REGION.A#a1","gaps":[],"coverageGaps":[]}' \
  >"${stop_wave}/region_path_manifest.json"
campaign_explore_stop REGION_PATH_CLOSURE_NO_PROGRESS "stalled" \
  "${stop_wave}" >/dev/null \
  || fail "campaign_explore_stop did not record the closure stop"
jq -e '.coverageGaps | length == 1
  and .[0].kind == "REGION_PATH_CLOSURE_NO_PROGRESS"
  and .[0].reason == "stalled" and .[0].regionId == "REGION.A"' \
  "${stop_wave}/region_path_manifest.json" >/dev/null \
  || fail "the closure stop is not a coverage gap on the pending worklist: \
$(cat "${stop_wave}/region_path_manifest.json")"
# The member's closure is what campaign_path_closures_json collects, so the
# stop has to be visible there and has to stay non-CLOSED.
jq -e '.state == "PENDING" and (.coverageGaps | length) == 1' \
  "${stop_member}/path_closure.json" >/dev/null \
  || fail "the forced stop published no pending closure for the member"

echo "run_engine campaign helper tests passed"
