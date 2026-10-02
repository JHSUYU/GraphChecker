#!/usr/bin/env bash

set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
# shellcheck source=../../../run_engine.sh
source "${repo}/run_engine.sh"

test_tmp=$(mktemp -d)
# The per-host memory ledger is shared through the home directory in a
# campaign; a test keeps its own.
campaign_host_gate_root="${test_tmp}/hosts"
cleanup() {
  [[ "${test_tmp}" == /tmp/* ]] || return 1
  rm -r -- "${test_tmp}"
}
trap cleanup EXIT

fail() {
  echo "run_engine campaign helper test failed: $*" >&2
  exit 1
}

# CONFIRM's decision is ConfirmMain on the built jar, and the freeze and
# two-host tests digest that jar: it is an input to these helper tests, and
# so is a JVM to run it.
graphchecker_jar=${default_graphchecker_jar}
[[ -s "${graphchecker_jar}" ]] \
  || fail "these tests need the packaged jar: run mvn -o package -DskipTests"
# That JVM is resolved as initialize_config resolves java_bin: the
# GRAPH_CHECKER_JAVA override, else java on PATH.  JAVA_HOME is not read --
# run_engine.sh never reads it, and a shell started on a lift can carry a
# JAVA_HOME that host does not have.
test_java=$(workflow_path_base=project \
  resolve_executable "${GRAPH_CHECKER_JAVA:-java}")
"${test_java}" -version >/dev/null 2>&1 \
  || fail "no runnable JVM '${test_java}': set GRAPH_CHECKER_JAVA or put \
java on PATH"

emit_sequence=0
emit_fixture() {
  emit_sequence=$((emit_sequence + 1))
  emit_root="${test_tmp}/emit-${emit_sequence}"
  emit_iteration="${emit_root}/iteration-0000"
  emit_config="${emit_root}/workflow.properties"
  emit_bounds="${emit_root}/loop-bounds.jsonl"
  emit_classes="${emit_root}/classes"
  campaign_root="${emit_root}"
  # The production layout: the one iteration composes straight into
  # ${campaign_root}/final, which is the path every later reader opens.
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${emit_root}/stage_metrics.tsv"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"

  mkdir -p "${campaign_final}" "${emit_classes}" \
    "${emit_iteration}/seed-result" \
    "${emit_iteration}/sessions/SESSION.seed"
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
  # SOLVE publishes its valuations and the ClaimPolicy decision it made from
  # them into the manifest it solved, under "solver".  EMIT publishes that
  # decision; it does not re-derive one, so the fixture states the claim
  # exactly as ClaimPolicy states it.
  jq -n '{schemaVersion: 2, kind: "CONCOLIC_COMPOSED_SMT",
    finalStatus: "FINAL_READY", finalStatusRefusals: [],
    anchor: "REGION.T#1",
    pathSetComplete: false,
    symbolicPropagationComplete: false,
    symbolicPropagation: [{armCount: 2}],
    symbolicPropagationGaps: [],
    boundedLoopComposition: {gaps: []}, gaps: [],
    solver: {schemaVersion: 4, kind: "ROOT_VALUATION_REPORT",
      state: "sat", reachability: "REACHABLE",
      unsatClosureComplete: false, gaps: [],
      valuations: [{values: [false], status: "unsat"},
                   {values: [true], status: "sat"}],
      campaignClaim: {schemaVersion: 1, kind: "CAMPAIGN_CLAIM",
        claim: "SAT_CANDIDATE",
        claimReason: "a valuation satisfies the target predicate inside the recorded model and a symbolic root flips it",
        blockers: [], blockerCount: 0, whyNotAccepted: "",
        findingKind: "MARKER_FLIPPED", polarityDecides: true,
        valuationOrdinal: 1,
        movedRoots: {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"},
        witnessFindings: [{findingKind: "MARKER_FLIPPED",
          valuationOrdinal: 1, polarityDecides: true,
          movedRoots: {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"}}]}}}' \
    >"${composition_manifest}"
  # CONFIRM's answer for that SAT claim: the one replay agreed.  EMIT
  # requires it for every SAT_CANDIDATE and copies it into the result.
  jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: true,
    reason: "every edge the model chose was taken, and the anchor observed the fatal",
    sessionId: "CONFIRM-1"}' >"${campaign_final}/confirm.json"
  # One replay session, per kind, as the runtime publishes it.  IMPORT
  # counted these into the census EMIT requires; the fixture states both.
  for session_kind in activations decisions exports attaches writes reads \
      roots targets gaps; do
    : >"${emit_iteration}/sessions/SESSION.seed/${session_kind}.jsonl"
  done
  # Two rows the runtime classed DIAGNOSTIC itself: an arm whose producer ran
  # concretely, and an obligation the solver could not decide in its budget.
  # Neither can change the chain the claim rests on, and each says so on the
  # row rather than in a table a later stage consults.
  printf '%s\n' \
    '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"UNATTESTED_ARM","cls":"DIAGNOSTIC","subject":"IXN.7","detail":"the producer ran concretely"}' \
    '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"UNPRODUCIBLE_ANSWER","cls":"DIAGNOSTIC","subject":"OBL.slow","detail":"SOLVER_TIMEOUT"}' \
    >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
  printf '{}\n' >"${emit_iteration}/sessions/SESSION.seed/expressions.json"
  jq -n -c '{schemaVersion: 1, kind: "SESSION_CENSUS",
    topologyEpoch: "iteration-0000", sessionId: "SESSION.seed",
    rowKind: "targets", rows: 1}' \
    >"${emit_iteration}/session_census.jsonl"
  : >"${emit_iteration}/campaign_gaps.jsonl"
  jq -n '{schemaVersion: 1, kind: "CAMPAIGN_ITERATION_MANIFEST",
    iterationId: "iteration-0000",
    members: [{role: "TARGET", taskId: "task-target",
               obligationDigests: []}]}' \
    >"${emit_iteration}/iteration_manifest.json"
}

# The same fixture as the solver stage published it for hdfs-17899-bug3: a
# REACHABLE formula no root flip moves, so ClaimPolicy withholds it,
# whose Boolean root never flips satisfiability, and whose experiment declares
# wire flows the composition never realized.
emit_fixture_undecided_roots() {
  emit_fixture
  jq '.solver = {schemaVersion: 4, kind: "ROOT_VALUATION_REPORT",
    state: "CANDIDATE_READY", reachability: "REACHABLE",
    unsatClosureComplete: false, gaps: [],
    symbolicVariableModels: [],
    valuations: [{values: [false], status: "sat"},
                 {values: [true], status: "sat"}],
    campaignClaim: {schemaVersion: 1, kind: "CAMPAIGN_CLAIM",
      claim: "INCONCLUSIVE_PARTIAL",
      claimReason: "2 blocker(s) withhold an accepted claim from a REACHABLE solver result: TARGET_UNCONSTRAINED_BY_ROOTS,FINDING_MECHANISM_UNNAMED",
      blockerCount: 2,
      blockers: [
        {code: "TARGET_UNCONSTRAINED_BY_ROOTS", subject: "",
         detail: "no symbolic root flips the target predicate"},
        {code: "FINDING_MECHANISM_UNNAMED", subject: "NO_MECHANISM",
         detail: "no satisfying witness names a mechanism"}],
      whyNotAccepted: ("claim=INCONCLUSIVE_PARTIAL: 2 blocker(s) withhold acceptance\n  TARGET_UNCONSTRAINED_BY_ROOTS: no symbolic root flips the target predicate\n  FINDING_MECHANISM_UNNAMED [NO_MECHANISM]: no satisfying witness names a mechanism"),
      findingKind: "NO_SUPPORTED_WITNESS", polarityDecides: false,
      valuationOrdinal: 0, movedRoots: {}, witnessFindings: []}}' \
    "${composition_manifest}" >"${composition_manifest}.tmp"
  mv "${composition_manifest}.tmp" "${composition_manifest}"
}

run_emit() {
  emit_status=0
  ( campaign_emit "${emit_iteration}"; campaign_exit_verdict ) \
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
  and .gapCount == 0
  and .telemetryCount >= 2' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its propagation provenance"
# EMIT-1: the artifacts are published at ${campaign_root}/final, which is the
# one path every later reader and the harness open.
[[ -s "${campaign_root}/final/result.json" ]] \
  || fail "an accepted run published no ${campaign_root}/final"

# DECIDE-1: a campaign answers about one anchor -- the occurrence its case
# declares and the composer composed -- and the result names it.  Ranking
# several observed executions into a verdict is gone with the election.
jq -e '.targetOccurrence == "REGION.T#1"
  and (has("targetOccurrences") | not)' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not name the composed anchor: \
$(jq -c '.targetOccurrence' "${campaign_final}/result.json")"
# CLAIM-1: the policy decision, so no consumer has to open the solver
# report to find the claim this file was written from -- the mechanism, the
# valuation it rests on, the roots it moved, and the witness findings once.
jq -e '.findingKind == "MARKER_FLIPPED" and .polarityDecides == true
  and .valuationOrdinal == 1
  and .movedRoots["HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED"] == "true"
  and (.witnessFindings | length) == 1
  and .witnessFindings[0].findingKind == "MARKER_FLIPPED"
  and (has("rootSpace") | not)' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not carry the claim's decision: \
$(jq -c '{findingKind, polarityDecides, valuationOrdinal, movedRoots, witnessFindings}' "${campaign_final}/result.json")"

# An obligation the solver could not decide in its budget is an unexplored
# sibling path.  The runtime classes it DIAGNOSTIC on the row, so it leaves a
# SAT candidate accepted; only the closed UNSAT conclusion is withheld by it.
jq -e '[.telemetryGaps[]
        | select(.stage == "REPLAY" and .source == "SESSION.seed"
            and .code == "UNPRODUCIBLE_ANSWER"
            and .subject == "OBL.slow")] | length == 1' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the undecided obligation was not published as telemetry: \
$(jq -c '.telemetryGaps' "${campaign_final}/gaps.json")"
jq -e '[.gaps[] | select(.code == "PATH_FLIP_SOLVER_TIMEOUT")] | length == 0' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the solver-timeout path gap blocked an accepted SAT candidate"
# An accepted claim has nothing to explain, and says so with an empty string
# rather than by omitting the field the owner reads.
jq -e '.blockers == [] and .blockerCount == 0 and .whyNotAccepted == ""' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an accepted claim published blockers"
# WHICH mechanism, beside WHETHER accepted.  The acceptance harness gates
# on these four, so a result.json that publishes the claim without them
# reads as a refusal for a reason the run never had.
jq -e '.findingKind == "MARKER_FLIPPED" and .polarityDecides == true
  and .valuationOrdinal == 1
  and .movedRoots == {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"}' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "result.json does not carry the mechanism the claim rests on"

# GAP-1: a gap raised by a stage the claim cannot see still withholds the
# candidate, because the row states its own class and a row that states none
# is blocking.  BOUND_INSUFFICIENT is the finalizer truncation that used to
# build a refusal string and throw it away.
emit_fixture
jq -n -c '{schemaVersion: 2, kind: "CONCOLIC_RUNTIME_MODEL_CATALOG",
  edges: [], regions: [],
  gaps: [{schemaVersion: 1, kind: "BOUND_INSUFFICIENT", cls: "BLOCKING",
          subject: "port\nsite",
          detail: "static site demands more accesses than are retained"}]}' \
  >"${runtime_region_plan}"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "a plan gap did not withhold the candidate (exit ${emit_status}): \
$(<"${emit_root}/emit.log")"
jq -e '.gapCount == 1
  and (.gaps[0].stage == "PLAN")
  and (.gaps[0].code == "BOUND_INSUFFICIENT")
  and (.gaps[0].class == "BLOCKING")
  and (.gaps[0].classReason == "the row states its own class")' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the plan gap was not published as blocking: \
$(jq -c '.gaps' "${campaign_final}/gaps.json")"
jq -e '.accepted == false and .gapCount == 1' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "result.json did not state that acceptance was withheld"
# And a static-catalog row that states DIAGNOSTIC is telemetry, not a
# blocker: the loop catalog knows an inherited K_L is a prefix nobody stated,
# and it is the producer that says so.  This used to be decided by a second
# registry keyed on a code the shell read out of the wrong member, which
# classed all 74 of hdfs-17960's catalog rows BLOCKING by accident.
emit_fixture
printf '%s\n' \
  '{"schemaVersion":4,"kind":"BOUNDED_LOOP_BODY_BOUND_UNDECLARED","cls":"DIAGNOSTIC","reason":"INHERITED_K_L_8","method":"<C: void m()>","siteId":"<C: void m()>#u3","detail":"[<C: void m()>#u3]"}' \
  | gzip -c >"${causynth_output_dir}/communication_gaps.jsonl.gz"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a diagnostic catalog row withheld the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 0
  and ([.telemetryGaps[] | select(.stage == "PLAN")]
       == [{stage: "PLAN", source: "CATALOG",
            code: "BOUNDED_LOOP_BODY_BOUND_UNDECLARED",
            subject: "<C: void m()>#u3", detail: "[<C: void m()>#u3]",
            class: "DIAGNOSTIC",
            classReason: "the row states its own class"}])' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the diagnostic catalog row was not published as telemetry: \
$(jq -c '[(.gaps+.telemetryGaps)[]|{stage,code,class}]' \
    "${campaign_final}/gaps.json")"
# EMIT-2: and a WITHHELD run publishes too: campaign_emit leaves this shell
# with exit 3 on a blocking gap, after result.json and gaps.json are written.
[[ -s "${campaign_root}/final/result.json" ]] \
  || fail "a withheld run published no ${campaign_root}/final"
[[ -s "${campaign_root}/final/gaps.json" ]] \
  || fail "the published final lost the gaps that withheld it"

# EMIT-3: a corpus whose generated indexes exceed one command-line argument.
# Linux caps a single argument at MAX_ARG_STRLEN -- 32 pages, 128 KiB -- which
# no ARG_MAX headroom relaxes, and every document campaign_write_gaps
# builds is proportional to the corpus.  lane11741j reached DECIDE with
# SAT_CANDIDATE and 0 blockers and then died at EMIT with "Argument list too
# long" on a 134,436-byte generated index, publishing nothing.  The session
# gap file below is larger than that on its own.
emit_fixture
python3 - "${emit_iteration}/sessions/SESSION.seed/gaps.jsonl" <<'OVERSIZED'
import json, sys
with open(sys.argv[1], "w") as handle:
    for n in range(1600):
        handle.write(json.dumps({
            "schemaVersion": 1, 
            "sessionId": "SESSION.seed", "kind": "UNATTESTED_ARM",
            "cls": "DIAGNOSTIC", "subject": "IXN.%048d" % n,
            "detail": "the producer ran concretely at %048d" % n}) + "\n")
OVERSIZED
oversized=$(wc -c <"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl")
[[ "${oversized}" -gt 131072 ]] \
  || fail "the oversized fixture is only ${oversized} bytes; it must exceed \
one argument (131072) for this check to mean anything"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "an oversized index broke EMIT (exit ${emit_status}): \
$(<"${emit_root}/emit.log")"
[[ -s "${campaign_root}/final/gaps.json" ]] \
  || fail "an oversized index published no gaps.json"
[[ -s "${campaign_root}/final/run-manifest.json" ]] \
  || fail "an oversized index published no run manifest"

# GAP-3: a code nobody registered is blocking.  This fixture used to publish
# two invented composition gap reasons as accepted telemetry; under one
# ledger they withhold the candidate until somebody writes down why they
# cannot break a chain.
emit_fixture
jq '.gaps = [{reason: "UNRELATED_FAMILY_OPEN",
              subject: "CBF.fixture", detail: "invented"},
             {reason: "LOOP_BOUND_OPEN",
              subject: "loop.fixture", detail: "invented"}]' \
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

# GAP-4: a planned region that never ran blocks, full stop.  It used to be
# decided against the replay slice -- blocking on a task the slice kept,
# diagnostic on one it pruned -- and there is no slice any more: a replay
# focuses one occurrence and everything else runs concretely, so a planned
# region with no activation is a broken chain wherever it is raised.
emit_fixture
printf '%s\n' \
  '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"ADMISSION_GAP","cls":"BLOCKING","subject":"OCC.kept","detail":"anchor never observed"}' \
  '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"ADMISSION_GAP","cls":"BLOCKING","subject":"OCC.pruned","detail":"anchor never observed"}' \
  >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "a session gap row did not block \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 2
  and ([.gaps[].subject] | sort == ["OCC.kept", "OCC.pruned"])
  and ([.gaps[].code] | unique == ["ADMISSION_GAP"])
  and ([.gaps[].source] | unique == ["SESSION.seed"])
  and (.telemetryCount == 0)' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "a blocking session row was not blocking: \
$(jq -c '[(.gaps+.telemetryGaps)[]|{code,subject,class}]' \
    "${campaign_final}/gaps.json")"
# And a row that states DIAGNOSTIC is taken at its word: the runtime knows
# what it could not do, and no later stage is in a position to overrule it.
emit_fixture
printf '%s\n' \
  '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"UNATTESTED_ARM","cls":"DIAGNOSTIC","subject":"IXN.9","detail":"the producer ran concretely"}' \
  >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
: >"${emit_iteration}/campaign_gaps.jsonl"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a diagnostic session row withheld the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 0 and .telemetryCount == 1
  and .telemetryGaps[0].code == "UNATTESTED_ARM"' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the diagnostic row was not published as telemetry: \
$(jq -c '.telemetryGaps' "${campaign_final}/gaps.json")"
# The rationale travels with the row, so a reader does not have to open the
# ledger to see why a gap was classed the way it was.
jq -e '[(.gaps + .telemetryGaps)[] | select((.classReason // "") == "")]
       | length == 0' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "a gap row carries no classification reason"

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
jq -e '[.blockers[].code] == ["TARGET_UNCONSTRAINED_BY_ROOTS",
    "FINDING_MECHANISM_UNNAMED"]
  and .blockerCount == 2' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result did not publish the named blockers: \
$(jq -c '.blockers' "${campaign_final}/result.json")"
# A blocker is named, not counted: an owner acts on the name.
jq -e '[.blockers[] | select(.code == "FINDING_MECHANISM_UNNAMED")
    | .subject] == ["NO_MECHANISM"]' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the mechanism blocker did not name its subject"
# The one view: a header plus one line per blocker, printed and recorded.
[[ $(jq -r '.whyNotAccepted' "${campaign_final}/result.json" \
      | wc -l) -eq 3 ]] \
  || fail "whyNotAccepted does not name one blocker per line"
grep -q 'FINDING_MECHANISM_UNNAMED' "${emit_root}/emit.log" \
  || fail "EMIT did not print the blocker summary"
# A stage-local FINAL_READY with zero aggregate gaps is exactly the state the
# jq gate accepted. EMIT publishes the policy's claim over it.
jq -e '.finalStatus == "FINAL_READY" and .gapCount == 0' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the withheld fixture no longer reproduces the accepted state"

# The claim has one home. A solved manifest without the policy's decision is
# a manifest EMIT may not publish a result from.
emit_fixture
jq 'del(.solver.campaignClaim)' "${composition_manifest}" \
  >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a solved manifest with no ClaimPolicy decision was published"
grep -q 'no ClaimPolicy decision' "${emit_root}/emit.log" \
  || fail "the missing claim was not named: $(<"${emit_root}/emit.log")"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "a result was published without a claim"

# The sessions are the evidence, so a run whose IMPORT counted none is a run
# EMIT may not publish a result from: the claim would rest on nothing read.
emit_fixture
rm -f "${emit_iteration}/session_census.jsonl"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a result was published with no replay session census"
grep -q 'replay session census' "${emit_root}/emit.log" \
  || fail "the missing census was not named: $(<"${emit_root}/emit.log")"
[[ ! -e "${campaign_final}/result.json" ]] \
  || fail "a result was published without a replay session census"

# COMPOSE-1: one campaign, one anchor, one artifact directory.  The composer
# writes candidate.smt2 and its manifest straight into the epoch's final/;
# there is no per-occurrence fan-out to key, because which execution of the
# declared target site the campaign answers about is the case's declaration.
emit_fixture
[[ "$(jq -r '.anchor' "${composition_manifest}")" == "REGION.T#1" ]] \
  || fail "the composition does not name its anchor"
[[ -s "${campaign_final}/candidate.smt2" ]] \
  || fail "the anchor's formula is not in the epoch's final directory"
[[ ! -e "${campaign_final}/targets" ]] \
  || fail "the composition fanned out over occurrences"

# PLAN-1: the schedule index says which members carry a target-reach goal, so
# the plan can name every observed occurrence of the declared target site.
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
# The rows carry the six fields the consumers read, and nothing else: the
# target-reach flag is validated above and not emitted.
[[ "$(printf '%s\n' "${index_rows}" | awk -F'\t' '{print NF}' \
    | sort -u | tr '\n' ' ')" == "6 " ]] \
  || fail "the decoded members do not carry exactly six fields: \
$(printf '%s\n' "${index_rows}" | head -1)"
[[ "$(printf '%s\n' "${index_rows}" | cut -f1,6 | tr '\n' ' ')" \
    == "TARGET	task-a DEPENDENCY	task-b DEPENDENCY	task-c " ]] \
  || fail "the decoded members do not name the roles and tasks: \
$(printf '%s\n' "${index_rows}" | cut -f1,6 | tr '\n' ' ')"
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

# The laneBK shape: the anchor had no path to compose.  The composer states
# that as its own refusal, and a refusal withholds the claim by name rather
# than killing the run one stage earlier.
emit_fixture
jq '.finalStatus = "FINAL_REFUSED"
    | .finalStatusRefusals = [{kind: "TARGET_NOT_REACHED",
        subject: "REGION.T#1",
        detail: "no admitted path reaches the fatal arm"}]' \
  "${composition_manifest}" >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "a composition refusal did not withhold the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '[.gaps[] | select(.code == "TARGET_NOT_REACHED")] as $rows
  | ($rows | length) == 1
  and $rows[0].stage == "COMPOSE"
  and $rows[0].source == "ComposeMain"
  and $rows[0].class == "BLOCKING"
  and $rows[0].subject == "REGION.T#1"' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the composition refusal did not reach gaps.json as blocking: \
$(jq -c '.gaps' "${campaign_final}/gaps.json")"

# EXPLORE-1: a forced stop is coverage telemetry, and it is a gap row like
# any other -- the exploration loop writes it onto the campaign's gap file and
# goes on to publish what it did establish.  An unexplored sibling path blocks a
# closed UNSAT and says nothing about a SAT candidate.
emit_fixture
: >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
printf '%s\n' \
  '{"schemaVersion":1,"sessionId":"","kind":"ADMISSION_GAP","cls":"DIAGNOSTIC","subject":"REGION_PATH_WAVE_BUDGET_REACHED","detail":"round 7 is of wave 12 with 2 obligation(s) still open"}' \
  >"${emit_iteration}/campaign_gaps.jsonl"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a forced exploration stop withheld the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 0 and .telemetryCount == 1
  and .telemetryGaps[0].subject == "REGION_PATH_WAVE_BUDGET_REACHED"' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the exploration stop is not telemetry in gaps.json: \
$(jq -c '.telemetryGaps' "${campaign_final}/gaps.json")"

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
# 43: `replay_task_budget` joined the table in bef2db898 without this count
# being raised and has since been deleted -- it capped nothing, no experiment
# set it, and its own test asserted it dropped no task.  `composer` joined it
# when the composition became selectable, `declared_target_occurrence` joined
# it in 05d413cae -- again without this count being raised, which left the
# whole helper test red on staging until an audit found it -- and
# `causynth_root_domains` joined it in a6da088f1, where the case gained a way
# to say what a declared root may be.
# `composer` left with the stage reduction; `reach_max_inputs` and
# `reach_max_valuations` left with the separate solver process, because the
# composer runs z3 per valuation while it composes and SOLVE reads the verdict
# it wrote.  `compose_max_valuations` joined it in their place: the enumeration
# is still the campaign's to bound, it is just the composer that runs it.  `composer` left it with the
# stage reduction: there is one composition of the anchored target's paths,
# and a key naming which one selected nothing.
# 42: `campaign_stop_after` joined it when the IMPORT stop became a declared
# key, in place of the undeclared CAUSYNTH_CAMPAIGN_STOP_AFTER env switch
# b70e1c7eb deleted.  Where a run stopped is part of the configuration a
# campaign publishes, so `config` prints it whether or not it is set.
# 41: `clock_skew_ms` left.  A clock root is free above zero and has no
# window -- the composer and the flip query both assert `(>= clock 0)` and
# nothing else -- so no stage read the key, and both invocations that passed
# `--clock-skew-ms` handed it to a main that did not read it either.
# 42: `causynth_static_scope_map` joined it with SYMBOL-SCOPE §3's static scope
# map.  TWO stages read that file -- the workload JVM installs the guard sites
# it names and EXPLORE flips at them -- so which file it is belongs to the
# configuration a campaign publishes, and both readers take it from this one
# key rather than each deriving a path.
# 43: `causynth_region_skeletons` joined it with the one-identity round.  TWO
# weaves read that file -- the recording opens an execution-index region at
# every root it names and the concolic weave opens one at every root the
# campaign did not select -- so which file it is belongs to the configuration
# a campaign publishes, and a weave that read a different one would stand on
# a different frame stack and address a different occurrence for one event.
# 44: `causynth_loop_default_bound` joined it when the bound an unnarrowed
# retained loop inherits stopped being a constant in LoopBoundPolicy.  It was
# applied silently to 54 of hdfs-17960's retained loops; no retained
# condition loop may inherit a bound silently, so the case states it and the
# campaign publishes what it stated.
# 45: `replay_timeout_s` joined it when the focused replay got a wall clock.
# The solver had a budget and the replay had none, so one replay JVM that
# deadlocked on two class monitors held 11741 campaign #4's wave 1 open until
# the campaign's own outer timeout killed everything and discarded the
# verdicts the wave had already reached.  How long a replay may take is part
# of the configuration a campaign publishes: two runs of the same case that
# bounded their replays differently did not explore under the same rules.
# 46: `campaign_worker_hosts` joined it when a wave stopped being one
# machine's work.  WHICH machines a run's obligations were executed on is part
# of the configuration a campaign publishes -- it is the difference between a
# wave of 108 costing fourteen slowest-of-eight replays and costing three --
# and empty is the honest spelling of "this one", which is what every run
# before the key did.
# 47: `region_path_max_world_depth` joined it with the nesting bound: how deep
# a world a wave cuts from is a rule the exploration ran under, and two runs
# that nested to different depths did not explore the same space.
# 48: `obligation_memory_mb` joined it when the obligation pool started
# spanning every lift: what one obligation takes on the host that runs it is
# the case's measured need, and the gate that keeps every host's memory safe
# reads it (campaign_await_host_memory).
# 44: `campaign_max_iterations` left with the epoch loop (one iteration per
# campaign; growth happens inside EXPLORE's waves), `causynth_cache_dir` with
# the seed cache, and `causynth_process_dirs`, which no case ever set.
# 46: `causynth_lineage_roots` joined it with the lineage scope: which class
# roots the weave scanned for thread starts, handoffs and timed waits decides
# which threads a run attributes and which waits the schedule holds, so two
# runs that scanned different roots did not replay under the same rules.
# 45: `refined_graph` left with RuntimeRefinedGraphBuilder (R14/R48): the
# finalizer reads the candidate graph and the skeletons, and nothing else.
# 44: `causynth_symbolic_inputs` left: roots are recognized by category from
# the program text (causynth.RootCatalog) and stated by the static scope map.
# 45: `causynth_scope_growth_budget` joined it: how many classes SEED adds to
# the case's scope where the slice stops decides what the campaign analyses.
# 46: `engine_memory_mb` joined it: the heap the head's engine JVMs hold the
# corpus in, which decides whether a campaign's planner finishes at all.
# 47: `region_path_stop_at_fatal` joined it: whether a case stops exploring
# at its declared occurrence's first witness.
# 48: `seed_replay_time_factor` joined it when the seed replay got a wall
# clock: how long the seed may replay decides whether a slow one is a case.
# 50: `causynth_static_root` and `record_timeout_s` joined it with `record`,
# the pre-screen: which static slices it aggregates each target on, and how
# long its recording may run.
# 51: `reproduce_runs` joined it with REPRODUCE: how often a confirmed
# witness is run natively.
# 52: `causynth_system_doors` joined it with the library catalog: a system's
# own doors, which replace the catalog's where its hook follows the call.
# 53: `reproduce_time_factor` joined it: each native run's wall clock, as a
# multiple of the recording's own.
# 51: `concolic_worker_count` and `region_path_stop_at_fatal` left with the
# wave barrier: how many obligations run on a host is its memory, up to its
# cores, and every campaign ends at its first accepted witness.
# 52: `stream_max_in_flight` joined it: how many obligations the capped
# explorations running at once keep in flight together.
# 54: `campaign_budget_s` and `campaign_reserve_s` joined it: how long the
# campaign may take, and how much of it the stages after EXPLORE are kept.
[[ "$(print_normalized_config | wc -l)" -eq 54 ]] \
  || fail "config prints a different number of keys than it used to: \
$(print_normalized_config | wc -l)"
# CONFIG-4: the discovery artifacts are derived from causynth_output_dir and
# nothing else -- not loadable, not overridable -- so every stage of a run
# and every peer of a wave reads the same file.  `config` still prints them.
for derived_key in candidate_graph runtime_region_plan \
    schedule_output_dir analysis_classes_dir causynth_static_scope_map \
    causynth_region_skeletons; do
  [[ " ${config_table_keys[*]} " == *" ${derived_key} "* ]] \
    || fail "${derived_key} is not in the workflow-key table"
  ! known_config_key "${derived_key}" \
    || fail "${derived_key} is loadable from a workflow file: it is derived"
  print_normalized_config | grep "^${derived_key}=" >/dev/null \
    || fail "config does not print the derived ${derived_key}"
done
# CONFIG-3: the region skeletons are ONE path, and every weave takes them
# from that one key.
grep -qF 'causynth_region_skeletons="${causynth_output_dir}/region_skeletons.jsonl.gz"' \
    "${repo}/run_engine.sh" \
  || fail "the region skeletons are not derived beside the discovery artifacts"
grep -qF '"-Dcausynth.region.skeletons=${causynth_region_skeletons}"' \
    "${repo}/run_engine.sh" \
  || fail "the weaves are not given the region skeletons key"
[[ "$(grep -cF -- '-Dcausynth.region.skeletons=' "${repo}/run_engine.sh")" \
    -eq 1 ]] \
  || fail "the region skeletons reach the weave by more than one spelling"
# CONFIG-2: the static scope map is ONE path, and both of its readers take it
# from that one key.  The workload JVM installs the guard sites the map names
# and EXPLORE flips at them, so a second derivation of the path is two stages
# reading two files.
# CONFIG-1: a key workflow_config_keys does not carry is a refusal, not a
# comment.  It used to be skipped, so `reach_max_inputs`,
# `reach_max_valuations` and `causynth_analysis_scope` shipped in all four case
# configs and read as settings that did nothing.
unknown_config=$(mktemp "${test_tmp}/unknown-config.XXXXXX")
printf 'workflow_path_base=project\nreach_max_inputs=8\n' >"${unknown_config}"
if (load_config_file "${unknown_config}") 2>"${unknown_config}.err"; then
  fail "an unknown workflow config key was accepted"
fi
grep -qF 'unknown workflow config key' "${unknown_config}.err" \
  || fail "the refusal does not name the key: $(<"${unknown_config}.err")"
grep -qF 'reach_max_inputs' "${unknown_config}.err" \
  || fail "the refusal does not name the key: $(<"${unknown_config}.err")"

grep -qF 'causynth_static_scope_map="${causynth_output_dir}/static_scope_map.jsonl"' \
    "${repo}/run_engine.sh" \
  || fail "the static scope map is not derived beside the discovery artifacts"
grep -qF -- '--static-scope-map "${causynth_static_scope_map}"' \
    "${repo}/run_engine.sh" \
  || fail "EXPLORE does not read the static scope map key"
grep -qF 'CAUSYNTH_STATIC_SCOPE_MAP=${causynth_static_scope_map}' \
    "${repo}/run_engine.sh" \
  || fail "the workload JVM is not given the static scope map key"

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

# PLAN-2: what PLAN hands the scheduler.  One recording, one plan: there is
# no retained set to carry from an earlier epoch and no scope to re-derive
# from summaries, so neither option is passed.
plan2_dir="${test_tmp}/plan2"
mkdir -p "${plan2_dir}/out"
: >"${plan2_dir}/region_plan.jsonl"
: >"${plan2_dir}/candidate.jsonl.gz"
: >"${plan2_dir}/static_scope_map.jsonl"
scheduler_args=""
# The stub stands in for this test only: the real one is put back after.
real_run_java_main=$(declare -f run_java_main)
run_java_main() { scheduler_args="$*"; }
runtime_region_plan="${plan2_dir}/region_plan.jsonl"
candidate_graph="${plan2_dir}/candidate.jsonl.gz"
causynth_static_scope_map="${plan2_dir}/static_scope_map.jsonl"
schedule_output_dir="${plan2_dir}/out"
schedule_max_jobs=8
declared_target_occurrence=""
do_schedule
eval "${real_run_java_main}"
for retired_option in --retain-regions --summaries --refined-graph --closure-mode; do
  [[ "${scheduler_args}" != *"${retired_option}"* ]] \
    || fail "PLAN still passes ${retired_option}: ${scheduler_args}"
done
# GUARD-1: one guard authority.  The scheduler reads the fatal arm of the
# declared target branch off static_scope_map's TARGET_SITE row, so PLAN has
# to hand it the same file EXPLORE and the workload JVM are handed.
[[ "${scheduler_args}" == *"--static-scope-map ${plan2_dir}/static_scope_map.jsonl"* ]] \
  || fail "PLAN did not hand the scheduler the static scope map: \
${scheduler_args}"
# GRAPH-1: PLAN reads the STATIC candidate graph and no runtime-refined one.
[[ "${scheduler_args}" == *"--candidate-graph ${plan2_dir}/candidate.jsonl.gz"* ]] \
  || fail "PLAN did not hand the scheduler the candidate graph: \
${scheduler_args}"
for retired_function in campaign_seeding_results campaign_seeding_replay \
    campaign_retained_growth campaign_unplannable_regions \
    campaign_union_regions campaign_topology_divergences \
    campaign_publish_pending_refinement campaign_publish_epoch_final \
    campaign_restore_seed_cache campaign_store_seed_cache; do
  [[ "$(type -t "${retired_function}")" != function ]] \
    || fail "${retired_function} survived the epoch loop"
done

# STOP-1: `campaign_stop_after` is a declared workflow key, so it answers the
# four table questions, resolves from a config file, and resolves from
# CAUSYNTH_CAMPAIGN_STOP_AFTER through the one override mechanism every other
# key uses -- there is no second code path reading that variable.
grep -q 'CAUSYNTH_CAMPAIGN_STOP_AFTER' "${repo}/run_engine.sh" \
  || fail "the environment override for campaign_stop_after is not declared"
[[ "$(grep -c 'CAUSYNTH_CAMPAIGN_STOP_AFTER' "${repo}/run_engine.sh")" -eq 1 ]] \
  || fail "CAUSYNTH_CAMPAIGN_STOP_AFTER appears outside the key table: \
it is honoured through apply_environment_overrides only"
known_config_key campaign_stop_after \
  || fail "campaign_stop_after is not loadable from a workflow file"
stop_after_dir="${test_tmp}/stop-after"
mkdir -p "${stop_after_dir}"
printf 'campaign_stop_after=IMPORT\n' >"${stop_after_dir}/workflow.properties"
reset_config
[[ -z "${campaign_stop_after}" ]] \
  || fail "campaign_stop_after does not default to empty: \
${campaign_stop_after}"
load_config_file "${stop_after_dir}/workflow.properties"
[[ "${campaign_stop_after}" == IMPORT ]] \
  || fail "a workflow file cannot set campaign_stop_after"
reset_config
CAUSYNTH_CAMPAIGN_STOP_AFTER=IMPORT apply_environment_overrides
[[ "${campaign_stop_after}" == IMPORT ]] \
  || fail "CAUSYNTH_CAMPAIGN_STOP_AFTER does not override campaign_stop_after"

# STOP-2: only the two declared values exist.  A misspelling would otherwise
# match nothing in do_campaign, run the whole campaign, and be read back as a
# measurement run that never stopped, so validate_config names it -- which is
# what `validate` and the campaign's own PREFLIGHT stage both call.
stop_after_config() {
  project_repo="${stop_after_dir}"
  project_module_dir="${stop_after_dir}"
  project_classes_dir="${stop_after_dir}"
  project_classpath="${stop_after_dir}"
  causynth_output_dir="${stop_after_dir}/out"
  causynth_target_spec="${stop_after_dir}/target.yaml"
  custom_jdk_home="${stop_after_dir}/jdk"
  z3_bin=z3
  workload_command="true"
  trace_test=T
  causynth_loop_bounds="${stop_after_dir}/loop-bounds.jsonl"
  : >"${causynth_loop_bounds}"
  causynth_loop_default_bound=8
  causynth_communication_mappings=""
    causynth_root_domains=""
  solver_timeout_ms=1000
  replay_timeout_s=2400
  schedule_max_jobs=1
  region_path_max_waves=1
  compose_max_valuations=1
  obligation_memory_mb=2500
  region_path_max_paths_per_region=""
  region_path_max_flips_per_path=""
  region_path_max_tasks=""
  campaign_stop_after=$1
}
stop_after_config ""
validate_config >/dev/null \
  || fail "an empty campaign_stop_after is refused"
stop_after_config IMPORT
validate_config >/dev/null \
  || fail "campaign_stop_after=IMPORT is refused"
# A subshell body, because validate_config refuses by `die`, which exits.
stop_after_validate() (
  stop_after_config "$1"
  validate_config
)
run_capturing_status stop_after_validate EXPLORE \
  >/dev/null 2>"${stop_after_dir}/validate.err"
[[ "${status}" -ne 0 ]] \
  || fail "validate accepted an undeclared campaign_stop_after value"
grep -q 'campaign_stop_after must be empty or IMPORT: EXPLORE' \
    "${stop_after_dir}/validate.err" \
  || fail "the refusal does not name the key and the value it refused: \
$(cat "${stop_after_dir}/validate.err")"

# STOP-3: what the key does to the campaign.  IMPORT returns 0 right after
# the IMPORT stage -- EXPLORE and everything after it never run -- and an
# empty value proceeds to EXPLORE and on through EMIT, once: a campaign is
# one iteration, and every stage is named once in its metrics.  The stages
# are driven through a campaign_stage stub, so this pins the control flow of
# do_campaign itself rather than any stage's work.
stop_after_campaign() {
  local root=$1
  local labels=$2
  (
    campaign_stage() { printf '%s\n' "$1" >>"${labels}"; }
    campaign_publish_iteration_manifest() { :; }
    campaign_exit_verdict() { :; }
    schedule_output_dir="${root}"
    campaign_setup_command=""
    do_campaign >/dev/null
  )
}
stop_after_config IMPORT
: >"${stop_after_dir}/labels-import.tsv"
stop_after_campaign "${stop_after_dir}/campaign-import" \
  "${stop_after_dir}/labels-import.tsv" \
  || fail "a campaign stopping after IMPORT did not exit 0"
[[ "$(tail -n 1 "${stop_after_dir}/labels-import.tsv")" == "IMPORT" ]] \
  || fail "the last stage of a stopped campaign is not IMPORT: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-import.tsv")"
! grep -q 'EXPLORE' "${stop_after_dir}/labels-import.tsv" \
  || fail "a campaign stopping after IMPORT still ran EXPLORE"
stop_after_config ""
: >"${stop_after_dir}/labels-full.tsv"
stop_after_campaign "${stop_after_dir}/campaign-full" \
  "${stop_after_dir}/labels-full.tsv" \
  || fail "a campaign with campaign_stop_after unset did not exit 0"
[[ "$(tr '\n' ' ' <"${stop_after_dir}/labels-full.tsv")" == \
    "PREFLIGHT FREEZE_TOOL FREEZE SEED PLAN INSTRUMENT REPLAY IMPORT EXPLORE \
COMPOSE SOLVE DECIDE CONFIRM EMIT REPRODUCE " ]] \
  || fail "a full campaign is not the one iteration's stages, each once: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-full.tsv")"

# REPRODUCE-1: a confirmed witness's native runs, all at once, each a head
# step placed where there is room (here: the head's own host, which has it)
# and charged the recording's peak memory until it returns, naming the host
# it ran on, bounded by
# reproduce_time_factor times the recording's workload and answering for
# itself off its trace's plant rows; reproduce.json counts the answers and
# names the runs that stated none.  A plant CONFIRM refuses, or a
# recording that measured no peak memory, is no run and the reason.  Per row:
# ConfirmMain's exit, the recording's peak MB, and the reproduction.
repro_dir="${test_tmp}/reproduce"
while IFS='|' read -r repro_plant repro_rss repro_expected; do
  rm -rf -- "${repro_dir}"
  mkdir -p "${repro_dir}/final"
  jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE"}}}' \
    >"${repro_dir}/manifest.json"
  jq -n '{confirmed: true, reason: ""}' >"${repro_dir}/final/confirm.json"
  (
    campaign_final="${repro_dir}/final"
    composition_manifest="${repro_dir}/manifest.json"
    campaign_worker_hosts=""
    campaign_host_gate_root="${repro_dir}/hosts"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_host_available_mb() { echo 30000; }
    campaign_host_total_mb() { echo 30000; }
    campaign_host_max_used_pct=70
    campaign_host_poll_s=0
    campaign_head_charging=1
    reproduce_runs=4
    reproduce_time_factor=3
    campaign_recorded_workload_s=20
    campaign_recorded_workload_rss_mb=${repro_rss}
    run_java_main() {
      echo "CONFIRM refused: NATIVE_PLANT_UNSUPPORTED: a clock"
      return "${repro_plant}"
    }
    # Run n: 1 at the anchor, 2 fatal elsewhere, 3 planted only, 4 no trace.
    # Each states its bound and its charge, and the ledger's row for it.
    run_configured_workload() {
      local run=$1 n=${1##*-}
      echo "$2 $4 $(grep -c " $4 60 " "${campaign_host_gate_root}/gate-head/\
starts")" >>"${repro_dir}/bounds"
      (( n < 4 )) || return 1
      {
        echo '{"event":"BRANCH"}'
        echo '{"event":"PLANT_APPLIED"}'
        (( n > 2 )) \
          || jq -n -c --argjson at "$(( n == 1 ))" \
            '{event: "PLANT_FATAL", atAnchor: ($at == 1)}'
      } >"${run}/runtime_trace.jsonl"
    }
    campaign_reproduce "${repro_dir}/iteration"
  ) >"${repro_dir}/log" 2>&1 \
    || fail "REPRODUCE failed the campaign: $(cat "${repro_dir}/log")"
  [[ "$(jq -c 'del(.schemaVersion, .kind)' \
      "${repro_dir}/final/reproduce.json")" == "${repro_expected}" ]] \
    || fail "a reproduction (plant ${repro_plant}, ${repro_rss} MB) is \
$(cat "${repro_dir}/final/reproduce.json"): $(cat "${repro_dir}/log")"
  [[ "${repro_expected}" != *'"runs":4'* \
      || "$(cut -d' ' -f1,2 "${repro_dir}/bounds" | sort -u)" \
        == "60 ${repro_rss}" ]] \
    || fail "a native run was not bounded by 3 x the recording's 20 s and \
held to its ${repro_rss} MB charge: $(cat "${repro_dir}/bounds")"
  [[ "${repro_expected}" != *'"runs":4'* \
      || "$(awk '$3 < 1' "${repro_dir}/bounds")" == "" ]] \
    || fail "a native run ran uncharged: $(cat "${repro_dir}/bounds")"
  [[ "${repro_expected}" != *'"runs":4'* \
      || "$(cat "${repro_dir}"/final/reproduce/run-*/host.txt | sort -u)" \
        == gate-head ]] \
    || fail "a native run does not name the host it ran on"
  [[ -z "$(cat "${repro_dir}"/hosts/*/starts 2>/dev/null)" ]] \
    || fail "a native run's charge outlived it: \
$(cat "${repro_dir}"/hosts/*/starts)"
done <<'EOF'
0|2048|{"runs":4,"planted":3,"fatal":2,"atAnchor":1,"reason":""}
1|2048|{"runs":0,"planted":0,"fatal":0,"atAnchor":0,"reason":"no native run: NATIVE_PLANT_UNSUPPORTED: a clock"}
0||{"runs":0,"planted":0,"fatal":0,"atAnchor":0,"reason":"no native run: the recording measured no peak resident memory (workload_rss_mb) to charge one with"}
EOF

# REACHED-1: a replay reached its target when a session published a target
# row at a TARGET_SITE method of the scope map (any of them: a batch group's
# map names each target's); no session, or rows of another method, is "".
reached_dir="${test_tmp}/reached"
mkdir -p "${reached_dir}/sessions/s1"
jq -n -c '{role: "TARGET_SITE", siteId: "<A: void m()>#u20"},
  {role: "TARGET_SITE", siteId: "<B: void n()>#u3"},
  {role: "GUARD", siteId: "<C: void o()>#u1"}' >"${reached_dir}/map.jsonl"
while IFS='|' read -r reached_anchor reached_expected; do
  if [[ -n "${reached_anchor}" ]]; then
    jq -n -c --arg site "${reached_anchor}" '{anchorSiteId: $site}' \
      >"${reached_dir}/sessions/s1/targets.jsonl"
  else
    rm -f -- "${reached_dir}/sessions/s1/targets.jsonl"
  fi
  [[ "$(campaign_target_reached "${reached_dir}/sessions" \
      "${reached_dir}/map.jsonl")" == "${reached_expected}" ]] \
    || fail "a target row at '${reached_anchor}' is not reached as \
'${reached_expected}'"
done <<'EOF'
<A: void m()>#u8#1|<A: void m()>#u8#1
<B: void n()>#u1#2|<B: void n()>#u1#2
<A: void mm()>#u8#1|
<C: void o()>#u1#1|
|
EOF

# BATCH-1: a batch campaign (causynth_static_root) plans every target its
# recording activated, seed-replays each group of plans once, all groups at
# once, and runs the campaign of every target its group's seed reached, all
# at once, each logging to its own targets/<name>/campaign.log.  A target
# whose campaign reached EMIT (exit 0, 2 or 3) is its own verdict; one its
# group's seed did not reach or ended before, whose log then names that
# failure, or whose campaign ended before EMIT, fails the batch once every
# other has finished.  Per row: b's exit, the targets the seeds reached, the
# group whose seed fails, the batch's status, and the last line of b's log.
batch_out="${test_tmp}/batch"
while IFS='|' read -r batch_exit batch_served batch_broken batch_status \
    batch_last; do
  rm -rf -- "${batch_out}"
  mkdir -p "${batch_out}/runtime" "${batch_out}/targets/a" \
    "${batch_out}/targets/b" "${batch_out}/targets/c"
  jq -n '{exit: 0, wallSeconds: 1, timedOut: false,
    targets: {a: {state: "ACTIVATED"}, b: {state: "ACTIVATED"},
              c: {state: "NOT_IN_WINDOW", detail: "no activation"}}}' \
    >"${batch_out}/runtime/record-summary.json"
  status=0
  (
    causynth_output_dir="${batch_out}"
    campaign_root="${batch_out}/schedule"
    campaign_stage_metrics="${batch_out}/metrics.tsv"
    campaign_batch_seed() { :; }
    campaign_batch_plan() { echo "plan of $1"; }
    campaign_batch_union() {
      mkdir -p "$1"
      jq -n '[{group: 0, targets: ["a"]}, {group: 1, targets: ["b"]}]' \
        >"$1/groups.json"
    }
    campaign_batch_group() {
      local dir=$1 name
      shift
      mkdir -p "${dir}"
      [[ "$*" != "${batch_broken}" ]] \
        || campaign_fail REPLAY WORKLOAD "${dir}" "broken seed"
      for name in "$@"; do
        [[ " ${batch_served} " != *" ${name} "* ]] \
          || printf '%s\t%s\n' "${name}" "${dir}"
      done >"${dir}/served"
    }
    campaign_batch_target() {
      echo "campaign of $1 on $(basename "$2")"
      [[ "$1" == a ]] && exit 2
      exit "${batch_exit}"
    }
    campaign_batch
  ) </dev/null >"${batch_out}/batch.log" 2>&1 || status=$?
  [[ "${status}" -eq "${batch_status}" ]] \
    || fail "a batch (${batch_served}) exited ${status}: \
$(cat "${batch_out}/batch.log")"
  [[ "$(cat "${batch_out}/targets/a/campaign.log")" == \
      $'plan of a\ncampaign of a on group-0' \
      && "$(head -n 1 "${batch_out}/targets/b/campaign.log")" == "plan of b" \
      && "$(tail -n 1 "${batch_out}/targets/b/campaign.log")" \
        == "${batch_last}" \
      && ! -e "${batch_out}/targets/c/campaign.log" ]] \
    || fail "a batch (${batch_served}) ran other campaigns than its targets'"
done <<'EOF'
3|a b||0|campaign of b on group-1
1|a b||1|campaign of b on group-1
0|a||1|plan of b
0|a|b|1|  reason=broken seed
EOF

# IMPORT-GATE: the row contract stops the campaign at IMPORT, or records.
#
# The gate's own rules are checked in ContractTest; what is checked here is
# the control flow the stage wraps around them: a BLOCKING count fails the
# stage naming the first subject, a DIAGNOSTIC-only run goes on, and either
# way the gap file the gate appended is the artifact the failure names.
gate_dir="${test_tmp}/import-gate"
mkdir -p "${gate_dir}/sessions"
# Stands in for the gate JVM: prints the summary the stage reads and appends
# to the campaign gap file, exactly as ImportGateMain does.
gate_stub() {
  printf '{"violations":%s,"blocking":%s,"firstBlockingSubject":"%s"}\n' \
    "$1" "$2" "$3"
  printf '{"schemaVersion":1,"cls":"%s"}\n' "$4" \
    >>"${gate_dir}/campaign_gaps.jsonl"
}
(
  run_java_main() { gate_stub 3 0 "" DIAGNOSTIC; }
  campaign_import_gate "${gate_dir}" iteration-0000 >/dev/null
) || fail "a gate with no blocking violation failed the campaign"
[[ "$(wc -l <"${gate_dir}/campaign_gaps.jsonl")" -eq 1 ]] \
  || fail "the gate's diagnostic row was not appended"
(
  run_java_main() {
    gate_stub 4 2 "decisions.jsonl seq=88 field=outcome" BLOCKING
  }
  campaign_import_gate "${gate_dir}" iteration-0000 >/dev/null
) 2>"${gate_dir}/error.log" \
  && fail "a blocking row invariant did not fail the campaign"
grep -q 'stage=IMPORT' "${gate_dir}/error.log" \
  || fail "the gate's failure is not attributed to IMPORT: \
$(cat "${gate_dir}/error.log")"
grep -q 'component=ImportGate' "${gate_dir}/error.log" \
  || fail "the gate's failure names no component"
grep -q '2 row invariants violated: decisions.jsonl seq=88 field=outcome' \
  "${gate_dir}/error.log" \
  || fail "the gate's failure does not name the first blocking subject: \
$(cat "${gate_dir}/error.log")"
grep -q "artifact=${gate_dir}/campaign_gaps.jsonl" "${gate_dir}/error.log" \
  || fail "the gate's failure does not name the gap file it appended"
[[ "$(wc -l <"${gate_dir}/campaign_gaps.jsonl")" -eq 2 ]] \
  || fail "the gate's gap file is not append-only"

# The same gate over the sessions EXPLORE lands is STREAM-5's.
wave_gate="${test_tmp}/import-gate-outside"
mkdir -p "${wave_gate}/sessions" "${wave_gate}/obligations-0000"
# A session the gate is handed is a session of the iteration's corpus, or
# the gate refuses it by name: one outside would be judged against an epoch
# it is not part of.
(
  run_java_main() { fail "the gate ran over a session outside the corpus"; }
  campaign_import_gate "${wave_gate}" iteration-0000 \
    "${wave_gate}/elsewhere.json" "${wave_gate}/obligations-0000"
) 2>"${wave_gate}/outside.log" \
  && fail "the gate took a directory outside the corpus as a session"
grep -q "not a session directory of ${wave_gate}/sessions" \
  "${wave_gate}/outside.log" \
  || fail "the gate's refusal does not name the corpus: \
$(cat "${wave_gate}/outside.log")"

# INSTRUMENT-VERIFY: the woven classes are put to the JVM verifier in the
# stage that wrote them.  9d2761c17 asked it for the first time inside the
# seed replay, which died on woven FSNamesystem.allowSnapshot @142 before any
# region ran and was reported as a failed workload method.  VerifyWovenClasses
# itself is exercised offline against real woven trees; what is pinned here is
# the control flow around it -- INSTRUMENT calls it, a non-zero verifier exit
# fails the stage naming the class and the reason, the report it wrote is the
# named artifact, and a verifier that refuses nothing goes on.
declare -f campaign_instrument | grep -q campaign_verify_woven_classes \
  || fail "INSTRUMENT does not put its woven classes to the verifier"
verify_dir="${test_tmp}/instrument-verify"
mkdir -p "${verify_dir}/instrumented-classes"
project_classpath="${verify_dir}/classpath-entry"
(
  run_java_main() { echo "verified 18 woven class(es) under $2"; }
  campaign_verify_woven_classes "${verify_dir}/instrumented-classes" >/dev/null
) || fail "a verifier run that refused nothing failed the campaign"
grep -q 'verified 18 woven class' \
  "${verify_dir}/woven_class_verification.log" \
  || fail "the verifier's report was not written beside the classes"
(
  run_java_main() {
    echo "verified 3 of 18 woven class(es) under $2"
    echo "UNVERIFIABLE org.apache.hadoop.hdfs.server.namenode.FSNamesystem: \
java.lang.VerifyError at \
org/apache/hadoop/hdfs/server/namenode/FSNamesystem.allowSnapshot(Ljava/lang\
/String;)V @142: lload_2: Local index 2 is invalid"
    return 1
  }
  campaign_verify_woven_classes "${verify_dir}/instrumented-classes" >/dev/null
) 2>"${verify_dir}/error.log" \
  && fail "a woven class the JVM verifier refused did not fail the campaign"
grep -q 'stage=INSTRUMENT' "${verify_dir}/error.log" \
  || fail "the verifier's failure is not attributed to INSTRUMENT: \
$(cat "${verify_dir}/error.log")"
grep -q 'component=VerifyWovenClasses' "${verify_dir}/error.log" \
  || fail "the verifier's failure names no component"
grep -q "artifact=${verify_dir}/woven_class_verification.log" \
  "${verify_dir}/error.log" \
  || fail "the verifier's failure does not name the report it wrote"
grep -q 'allowSnapshot.*Local index 2 is invalid' "${verify_dir}/error.log" \
  || fail "the verifier's failure does not name the class, method and \
reason: $(cat "${verify_dir}/error.log")"
# A weave that throws fails its stage by name (campaign_analyze), its
# deepest cause the reason; under errexit it ended the campaign unnamed.
(
  do_analyze() {
    echo "java.lang.IllegalStateException: Could not instrument a root"
    echo "Caused by: java.lang.IllegalStateException: \
LOOP_BODY_ROOT_ENTRY_UNAVAILABLE: m#loop:u12 declares 2 controls" >&2
    return 1
  }
  campaign_analyze INSTRUMENT "${verify_dir}/instrument.log" >/dev/null
) 2>"${verify_dir}/weave-error.log" \
  && fail "a weave that threw did not fail the campaign"
grep -q 'stage=INSTRUMENT' "${verify_dir}/weave-error.log" \
  && grep -q "artifact=${verify_dir}/instrument.log" \
    "${verify_dir}/weave-error.log" \
  && grep -q 'reason=.*exit 1: java.lang.IllegalStateException: LOOP_BODY_ROOT_ENTRY_UNAVAILABLE' \
    "${verify_dir}/weave-error.log" \
  || fail "a weave's failure does not name its stage, log and refusal: \
$(cat "${verify_dir}/weave-error.log")"

# COUNT: a count the campaign decides on is a decision, and an unreadable
# count is a refusal.  `[[ "${n}" -eq 0 ]]` reads an empty string as zero, so
# the IMPORT gate passed whenever its summary could not be read at all --
# precisely when it should not.  Pinned here because the shape recurs: the
# gate, the solver's model count, the published gap count and the epoch
# loop's divergence count all decide on a number some other process printed.
count_dir="${test_tmp}/campaign-count"
mkdir -p "${count_dir}"
campaign_count IMPORT ImportGate "${count_dir}" label 0 \
  || fail "campaign_count refused a zero count"
campaign_count IMPORT ImportGate "${count_dir}" label 12 \
  || fail "campaign_count refused a count"
for bad in "" " " "x" "1+1" "-1" "0 -o 1" "null"; do
  (campaign_count IMPORT ImportGate "${count_dir}" \
      "the import gate's blocking count" "${bad}") \
    2>"${count_dir}/error.log" \
    && fail "campaign_count accepted '${bad}' as a count"
  grep -q 'stage=IMPORT' "${count_dir}/error.log" \
    || fail "an unreadable count is not attributed to its stage"
  grep -q "is not a count: '${bad}'" "${count_dir}/error.log" \
    || fail "an unreadable count does not name the value it read: \
$(cat "${count_dir}/error.log")"
done
# The gate itself, over a summary the gate JVM wrote nothing into: the old
# spelling logged "0 blocking" and carried on.
gate_empty="${test_tmp}/import-gate-unreadable"
mkdir -p "${gate_empty}/sessions"
(
  run_java_main() { printf '{}\n'; }
  campaign_import_gate "${gate_empty}" iteration-0000
) 2>"${gate_empty}/error.log" \
  && fail "an import gate summary with no counts did not fail the campaign"
grep -q 'stage=IMPORT' "${gate_empty}/error.log" \
  || fail "the unreadable gate summary is not attributed to IMPORT"
grep -q "is not a count: 'null'" "${gate_empty}/error.log" \
  || fail "the unreadable gate summary does not name the value it read: \
$(cat "${gate_empty}/error.log")"

# REPLAY-BOUND-1: `replay_timeout_s` is a declared workflow key, registered
# exactly like `solver_timeout_ms` -- it answers the four table questions, it
# resolves from a config file, it resolves from its one environment override,
# and validate_config refuses a value that is not a positive integer.  The
# solver had a budget and the replay had none, which is how one deadlocked
# replay JVM held 11741 campaign #4's wave 1 open until the campaign's own
# outer timeout killed everything.
grep -q 'CAUSYNTH_REPLAY_TIMEOUT_S' "${repo}/run_engine.sh" \
  || fail "the environment override for replay_timeout_s is not declared"
[[ "$(grep -c 'CAUSYNTH_REPLAY_TIMEOUT_S' "${repo}/run_engine.sh")" -eq 1 ]] \
  || fail "CAUSYNTH_REPLAY_TIMEOUT_S appears outside the key table: \
it is honoured through apply_environment_overrides only"
known_config_key replay_timeout_s \
  || fail "replay_timeout_s is not loadable from a workflow file"
bound_dir="${test_tmp}/replay-bound"
mkdir -p "${bound_dir}"
reset_config
[[ "${replay_timeout_s}" == 2400 ]] \
  || fail "replay_timeout_s does not default to 2400: ${replay_timeout_s}"
printf 'replay_timeout_s=60\n' >"${bound_dir}/workflow.properties"
load_config_file "${bound_dir}/workflow.properties"
[[ "${replay_timeout_s}" == 60 ]] \
  || fail "a workflow file cannot set replay_timeout_s"
reset_config
CAUSYNTH_REPLAY_TIMEOUT_S=90 apply_environment_overrides
[[ "${replay_timeout_s}" == 90 ]] \
  || fail "CAUSYNTH_REPLAY_TIMEOUT_S does not override replay_timeout_s"
reset_config
# The same gate every other bound answers to: a campaign that states a
# nonsense wall clock is refused by name before any work starts.
replay_bound_validate() (
  stop_after_config ""
  replay_timeout_s=$1
  validate_config
)
for bad in "" "0" "x" "-1"; do
  run_capturing_status replay_bound_validate "${bad}" \
    >/dev/null 2>"${bound_dir}/validate.err"
  [[ "${status}" -ne 0 ]] \
    || fail "validate accepted replay_timeout_s='${bad}'"
  grep -q 'replay_timeout_s must be' "${bound_dir}/validate.err" \
    || fail "the refusal does not name replay_timeout_s: \
$(cat "${bound_dir}/validate.err")"
done

# REPLAY-BOUND-2: the bound kills the adapter's whole PROCESS GROUP, not the
# shell it started.  The hung replay was a JVM two processes below the
# adapter's login shell, so a bound that signalled only the shell would have
# left it running and the worker still waiting on it.
mkdir -p "${bound_dir}/work"
workload_work_dir="${bound_dir}/work"
custom_jdk_home=""
# Ten seconds, not one: the adapter is a LOGIN shell, and the lifts' login
# profile runs a quota check on NFS, which right after `mvn package` took
# over five seconds, so a shorter bound sometimes fired before the payload
# wrote its pid.
campaign_adapter_timeout_s=10
run_capturing_status campaign_run_adapter "replay(test)" \
  "sleep 120 & echo \$! >'${bound_dir}/grandchild.pid'; wait" \
  >"${bound_dir}/adapter.log" 2>&1
[[ "${status}" -eq 124 ]] \
  || fail "a bounded adapter that outlived its bound did not report the \
timeout (exit ${status})"
grandchild=$(cat "${bound_dir}/grandchild.pid")
for _ in 1 2 3 4 5 6 7 8 9 10; do
  kill -0 "${grandchild}" 2>/dev/null || break
  sleep 0.3
done
if kill -0 "${grandchild}" 2>/dev/null; then
  kill -9 "${grandchild}" 2>/dev/null || true
  fail "the bound left the adapter's grandchild ${grandchild} running: the \
process group was not killed"
fi
# An empty bound is the unbounded call this was before: no `timeout` at all.
campaign_adapter_timeout_s=""
run_capturing_status campaign_run_adapter "replay(test)" "exit 3" \
  >"${bound_dir}/adapter-unbounded.log" 2>&1
[[ "${status}" -eq 3 ]] \
  || fail "an unbounded adapter no longer reports the workload's own exit \
code (${status})"
if grep -q 'adapter bound' "${bound_dir}/adapter-unbounded.log"; then
  fail "an unbounded adapter logs a bound it does not have"
fi
# Two setters beside the declaration: campaign_obligation_worker and
# campaign_session_replay (SEED-BOUND below), each with the rule it states.
[[ "$(grep -c 'campaign_adapter_timeout_s=' "${repo}/run_engine.sh")" -eq 3 ]] \
  || fail "the replay bound has a setter beyond the two replays: \
$(grep -n 'campaign_adapter_timeout_s=' "${repo}/run_engine.sh")"

# SEED-BOUND: the seed replay runs under seed_replay_time_factor times the
# recorded workload's wall time, never under one obligation's
# replay_timeout_s, and names that rule -- what campaign_replay fails the
# campaign with at REPLAY when the replay outlives it.  Unbounded, 11 of
# h4's cases spent their whole 5400 s budget in a seed replay and died
# unnamed.
known_config_key seed_replay_time_factor \
  || fail "seed_replay_time_factor is not loadable from a workflow file"
[[ "${seed_replay_time_factor}" == 40 ]] \
  || fail "seed_replay_time_factor does not default to 40"
seed_bound() (
  replay_timeout_s=$1 seed_replay_time_factor=$2
  campaign_recorded_workload_s=$3
  campaign_task_ids() { echo TASK.SEED; }
  campaign_replay() {
    printf '%s|%s\n' "${campaign_adapter_timeout_s}" \
      "${campaign_adapter_timeout_rule}"
  }
  campaign_session_replay "${bound_dir}/seed-iteration"
)
[[ "$(seed_bound 2400 40 100)" == "4000|4000s, seed_replay_time_factor=40 x \
the recording's 100s workload and at least replay_timeout_s=2400" ]] \
  || fail "the seed replay is not bound by the recording: $(seed_bound 2400 40 100)"
[[ "$(seed_bound 2400 40 10)" == 2400\|* ]] \
  || fail "a short recording bounds the seed replay under replay_timeout_s: \
$(seed_bound 2400 40 10)"
seed_factor_validate() (
  stop_after_config ""
  seed_replay_time_factor=$1
  validate_config
)
run_capturing_status seed_factor_validate 0 >/dev/null \
  2>"${bound_dir}/validate.err"
[[ "${status}" -ne 0 ]] && grep -q 'seed_replay_time_factor must be' \
  "${bound_dir}/validate.err" \
  || fail "validate accepted seed_replay_time_factor=0"

# REPLAY-NEED: the seed replay (and CONFIRM's) is charged the recording's
# measured peak times campaign_replay_memory_factor (7) when that is above
# one obligation's replay, else that (campaign_replay_need_mb), and its
# replay JVM is handed that charge
# (CAUSYNTH_CHARGED_MB, which execute.sh sizes and holds the JVM by).  Per
# row: obligation_memory_mb, the recording's peak (- none), the need.
while read -r need_obligation need_rss need_expected; do
  [[ "${need_rss}" != - ]] || need_rss=""
  need_said=$(
    obligation_memory_mb=${need_obligation}
    campaign_recorded_workload_rss_mb=${need_rss}
    replay_timeout_s=2400 seed_replay_time_factor=40
    campaign_recorded_workload_s=10
    campaign_task_ids() { echo TASK.SEED; }
    campaign_head_charged() { printf 'charged=%s ' "$1"; shift 2; "$@"; }
    campaign_replay() { printf 'jvm=%s' "$7"; }
    campaign_session_replay "${bound_dir}/seed-iteration"
  )
  [[ "${need_said}" == "charged=${need_expected} jvm=${need_expected}" ]] \
    || fail "a seed replay with ${need_obligation} MB per obligation and a \
'${need_rss}' MB recording is ${need_said}, not ${need_expected} MB"
done <<'EOF'
2500 300 2500
2500 442 3094
2500 - 2500
EOF
need_dir="${bound_dir}/need"
mkdir -p "${need_dir}"
printf '{"taskId":"TASK.1"}\n' >"${need_dir}/plan.jsonl"
(
  campaign_run_adapter() { printf '%s\n' "$@" >"${need_dir}/adapter.args"; }
  campaign_replay worker "${need_dir}/plan.jsonl" TASK.1 "${need_dir}/classes" \
    "${need_dir}/result/r.jsonl" "${need_dir}/worker" 3000 tolerated
) >/dev/null 2>&1 || fail "a tolerated replay failed"
grep -qx 'CAUSYNTH_CHARGED_MB=3000' "${need_dir}/adapter.args" \
  || fail "the replay JVM is not handed what its host was charged: \
$(cat "${need_dir}/adapter.args")"

# WATCH-1: a workload JVM that grows past its charge asks its host for the
# excess and holds what it was granted, charged on the ledger; it is ended
# only when the host's real use -- MemTotal less MemAvailable, 10000 MB and
# a 70% ceiling -- would pass the ceiling with it, never for what the
# ledger promised other starts (a foreign start still in its ramp), and
# what it was granted is released when it ends.  A recording (charged
# nothing) is only measured: its peak is the trace's workload_rss_mb.  Per
# row: the host's MemAvailable, the MB a foreign start in its ramp holds on
# the ledger (0: none), the charge, the JVM's resident memory at each read,
# whether it was ended, the most rows the ledger held for it, and what it
# says last.
watch_dir="${test_tmp}/watch"
while IFS='|' read -r watch_available watch_foreign watch_charged watch_rss \
    watch_ended watch_rows watch_said; do
  rm -rf -- "${watch_dir}"
  mkdir -p "${watch_dir}/trace" "${watch_dir}/hosts/gate-head"
  printf '%s\n' ${watch_rss//,/ } >"${watch_dir}/rss"
  : >"${watch_dir}/rows"
  watch_foreign_row=""
  if (( watch_foreign > 0 )); then
    watch_foreign_row="$(date +%s) ${watch_foreign} 3600 foreign"
    printf '%s\n' "${watch_foreign_row}" \
      >"${watch_dir}/hosts/gate-head/starts"
  fi
  (
    campaign_host_gate_root="${watch_dir}/hosts"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_host_available_mb() { echo "${watch_available}"; }
    campaign_host_total_mb() { echo 10000; }
    campaign_host_max_used_pct=70
    campaign_watch_interval_s=0.1
    # The JVM's resident memory, one read at a time, and the ledger's rows
    # at that read; after the last read it ends.
    campaign_process_rss_mb() {
      local mb
      mb=$(head -n 1 "${watch_dir}/rss")
      cat "${campaign_host_gate_root}/gate-head/starts" 2>/dev/null \
        | grep -vc ' foreign$' >>"${watch_dir}/rows"
      [[ -n "${mb}" ]] || { kill "$1"; return 1; }
      sed -i 1d "${watch_dir}/rss"
      echo "${mb}"
    }
    sleep 60 &
    watch_jvm=$!
    campaign_watch_workload "${watch_jvm}" "${watch_charged}" \
      "${watch_dir}/trace" 2>"${watch_dir}/said" &
    watch_pid=$!
    watch_exit=0
    wait "${watch_jvm}" 2>/dev/null || watch_exit=$?
    wait "${watch_pid}"
    echo "${watch_exit}" >"${watch_dir}/exit"
  ) || fail "a watch failed"
  [[ "$( (( $(cat "${watch_dir}/exit") == 137 )) && echo ended || echo ran)" \
      == "${watch_ended}" ]] \
    || fail "a JVM charged ${watch_charged} MB at ${watch_rss} MB on a host \
with ${watch_available} MB was not ${watch_ended} (exit \
$(cat "${watch_dir}/exit")): $(cat "${watch_dir}/said")"
  [[ "$(sort -n "${watch_dir}/rows" | tail -n 1)" == "${watch_rows}" ]] \
    || fail "the ledger held $(sort -n "${watch_dir}/rows" | tail -n 1) \
rows for a JVM at ${watch_rss} MB, not ${watch_rows}"
  [[ "$(cat "${watch_dir}/hosts/gate-head/starts" 2>/dev/null)" \
      == "${watch_foreign_row}" ]] \
    || fail "what a JVM was granted outlived it, or a foreign start's row \
went with it"
  [[ "$(cat "${watch_dir}/trace/workload_rss_mb")" \
      == "$(tr ',' '\n' <<<"${watch_rss}" | sort -n | tail -n 1)" ]] \
    || fail "the trace does not state the JVM's peak"
  [[ "$(tail -n 1 "${watch_dir}/said")" == "${watch_said}" ]] \
    || fail "a JVM at ${watch_rss} MB said: $(cat "${watch_dir}/said")"
  [[ "${watch_ended}" == ran ]] \
    || grep -q 'MB its host holds for it, and the host cannot take the [0-9]* MB more' \
      "${watch_dir}/said" \
    || fail "an ended JVM does not say why: $(cat "${watch_dir}/said")"
done <<'EOF'
28000|0|2500|1000,2541,2600|ran|2|causynth: the workload JVM's resident memory peaked at 2600 MB; its host was charged 2500 MB for it and took 2600 MB as it grew
5000|0|2500|2541,6000|ended|1|causynth: the workload JVM's resident memory peaked at 6000 MB; its host was charged 2500 MB for it and took 2541 MB as it grew
6000|5000|2500|2541,2600|ran|2|causynth: the workload JVM's resident memory peaked at 2600 MB; its host was charged 2500 MB for it and took 2600 MB as it grew
3000|0|2500|2541|ended|0|causynth: the workload JVM's resident memory peaked at 2541 MB; its host was charged 2500 MB for it
3000|0|2500|2400|ran|0|causynth: the workload JVM's resident memory peaked at 2400 MB; its host was charged 2500 MB for it
28000|0|0|400,486|ran|0|
EOF

# SOLVER-SERVICE: an obligation's question goes to ONE solver JVM of its host
# and corpus (ObligationSolverMain --serve), started by the first question
# and charged at the host's ledger what it holds as it grows; a question it
# could not answer is its worker's failure, by name; and it ends once idle,
# naming no solver, its charges given back as its JVM returns.  A host with
# no room to start one now answers 3 at once, starting nothing and holding
# no question behind a start that waits for memory.
# Two questions at once, over a corpus whose round holds neither obligation.
solver_test=${test_tmp}/solver-service
solver_wave=${solver_test}/iteration/obligations-0000
mkdir -p "${solver_test}/iteration/sessions" "${solver_wave}" \
  "${solver_test}/a" "${solver_test}/b"
: >"${solver_wave}/obligations.jsonl"
(
  java_bin=${test_java}
  graphchecker_jar=${default_graphchecker_jar}
  graphchecker_work_dir=${solver_test}
  causynth_loop_default_bound=1
  causynth_root_domains=""
  z3_bin=z3
  solver_timeout_ms=1000
  campaign_solver_idle_s=1
  # The test's host has room whatever else runs on it.
  campaign_host_max_used_pct=100
  campaign_host_gate_root=${solver_test}/hosts
  # Every solver started, counted.
  eval "$(declare -f campaign_start_solver \
    | sed '1s/campaign_start_solver/solver_started/')"
  campaign_start_solver() {
    echo "$1" >>"${solver_test}/solvers"
    solver_started "$@"
  }
  export TMPDIR=${solver_test}
  pids=()
  for question in a b; do
    campaign_solve_obligation "OB.${question}" "${solver_wave}/obligations.jsonl" \
      "${solver_test}/iteration/sessions" "${solver_test}/${question}" \
      >/dev/null 2>"${solver_test}/${question}.err" &
    pids+=("$!")
  done
  for pid in "${pids[@]}"; do
    wait "${pid}" && fail "a question its solver could not answer passed"
  done
  for question in a b; do
    grep -q "ObligationSolverMain: java.io.IOException: the round has no \
obligation OB.${question}" "${solver_test}/${question}.err" \
      || fail "the worker does not say why its question was not answered: \
$(cat "${solver_test}/${question}.err")"
  done
  [[ "$(wc -l <"${solver_test}/solvers")" -eq 1 ]] \
    || fail "the host's two questions did not go to one solver"
  solver_home=$(campaign_solver_dir "${solver_test}/iteration/sessions")
  for ((waited = 0; waited < 30; waited++)); do
    [[ -e "${solver_home}/server" ]] \
      || [[ -n "$(cat "${solver_test}/hosts/"*/starts)" ]] || break
    sleep 1
  done
  [[ ! -e "${solver_home}/server" ]] \
    || fail "an idle solver did not end: $(cat "${solver_home}/server")"
  [[ -z "$(cat "${solver_test}/hosts/"*/starts)" ]] \
    || fail "an ended solver is still charged: \
$(cat "${solver_test}/hosts/"*/starts)"
  # No room: 3 at once, no solver named, the question withdrawn.
  campaign_host_max_used_pct=1
  started=${SECONDS}
  status=0
  campaign_solve_obligation OB.c "${solver_wave}/obligations.jsonl" \
    "${solver_test}/iteration/sessions" "${solver_test}/c" \
    >/dev/null 2>&1 || status=$?
  [[ "${status}" -eq 3 && $(( SECONDS - started )) -lt 10 \
     && ! -e "${solver_home}/server" \
     && -z "$(ls "${solver_home}/requests")" ]] \
    || fail "a host with no room for a solver held its question (${status})"
)

# A question its host's solver could not answer (out of heap, died) is no
# answer: it is asked once more of a solver of its own, and a second failure
# fails the worker -- an unfinished obligation (campaign_obligation_unfinished)
# -- never a bare NOT_ADMITTED (hdfs-17960 fast1: 29 of 35 obligations
# "answered" by an OutOfMemoryError).  Neither settles its question.
# A question whose host had no room for its solver (3) is answered at once in
# a solver JVM of its own, under the obligation's charge (`now`).
retry_test=${test_tmp}/solver-retry
for alone in answers fails noroom; do
  mkdir -p "${retry_test}/${alone}"
  retry_status=0
  (
    campaign_solve_obligation() {
      [[ "${alone}" != noroom ]] || return 3
      : >"$4/question.asked"
      echo "ObligationSolverMain: java.lang.OutOfMemoryError: Java heap space" >&2
      return 1
    }
    campaign_solve_obligation_alone() {
      [[ "${alone}" != noroom || "${5:-}" == now ]] \
        || { echo "not asked at once" >&2; return 1; }
      [[ "${alone}" != fails ]] || { echo "the second one died" >&2; return 1; }
      printf '{"verdict":"UNSAT","obligationId":"OB.1"}\n' \
        >"$4/obligation_result.jsonl"
      printf '(assert false)\n' >"$4/obligation_query.smt2"
    }
    campaign_obligation_worker OB.1 obligations classes \
      "${retry_test}/${alone}" sessions plan
  ) >"${retry_test}/${alone}.log" 2>"${retry_test}/${alone}/stderr.log" \
    || retry_status=$?
  [[ ! -e "${retry_test}/${alone}/question.asked" ]] \
    || fail "a solver that failed settled a question"
  if [[ "${alone}" != fails ]]; then
    [[ "${retry_status}" -eq 0 && "$(jq -r .verdict \
        "${retry_test}/${alone}/obligation_result.jsonl")" == UNSAT ]] \
      || fail "the second solver's answer is not the obligation's"
  else
    [[ "${retry_status}" -ne 0 && ! -e \
        "${retry_test}/fails/obligation_result.jsonl" ]] \
      || fail "a question no solver answered was given an answer"
    grep -q 'Error: obligation OB.1: its solver failed twice.*the second one died' \
      "${retry_test}/fails/stderr.log" \
      || fail "the unfinished worker does not say why: \
$(cat "${retry_test}/fails/stderr.log")"
  fi
done

# REPLAY-BOUND-3: what one obligation whose replay never returns records.
# The same terminal NOT_ADMITTED row the worker writes for a solver that
# failed -- one obligation's own answer, never the wave's death -- naming the
# bound it exceeded.  The worker must also RETURN, which is the whole point:
# the wave barrier waited on the hung one forever.
worker_dir="${bound_dir}/obligation"
mkdir -p "${worker_dir}" "${bound_dir}/sessions" "${bound_dir}/classes"
printf '{"taskId":"TASK.1"}\n' >"${bound_dir}/seed_plan.jsonl"
: >"${bound_dir}/obligations.jsonl"
replay_timeout_s=1
concolic_replay_command="sleep 120"
causynth_root_domains=""
causynth_static_scope_map=""
z3_bin=z3
solver_timeout_ms=1000
schedule_max_jobs=1
trace_test=T
(
  # The solver settled it: a model is ready and the replay is what decides.
  campaign_solve_obligation() {
    jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
      obligationId: "OB.1", verdict: "SAT_MODEL_READY", sessionId: "",
      detail: ""}' >"${worker_dir}/obligation_result.jsonl"
    printf '{"taskId":"TASK.1"}\n' >"${worker_dir}/focused_task.jsonl"
    printf '(assert true)\n' >"${worker_dir}/obligation_query.smt2"
  }
  campaign_obligation_worker OB.1 "${bound_dir}/obligations.jsonl" \
    "${bound_dir}/classes" "${worker_dir}" "${bound_dir}/sessions" \
    "${bound_dir}/seed_plan.jsonl"
) >"${worker_dir}/worker.log" 2>&1 \
  || fail "the worker did not return when its replay outlived the bound: \
$(cat "${worker_dir}/worker.log")"
[[ "$(jq -r '.verdict' "${worker_dir}/obligation_result.jsonl")" \
    == NOT_ADMITTED ]] \
  || fail "a replay killed on its bound did not record NOT_ADMITTED: \
$(cat "${worker_dir}/obligation_result.jsonl")"
[[ "$(jq -r '.detail' "${worker_dir}/obligation_result.jsonl")" \
    == "replay exceeded replay_timeout_s=1" ]] \
  || fail "the recorded row does not name the bound it exceeded: \
$(cat "${worker_dir}/obligation_result.jsonl")"
[[ "$(jq -r '.kind' "${worker_dir}/obligation_result.jsonl")" \
    == OBLIGATION_RESULT ]] \
  || fail "the recorded row is not an obligation result: \
$(cat "${worker_dir}/obligation_result.jsonl")"
# This replay was killed before it opened a session, which is a case of its
# own: nothing to withdraw, and the worker says so rather than passing over
# it.
grep -q 'nothing withdrawn' "${worker_dir}/worker.log" \
  || fail "a replay killed before it opened a session does not say so: \
$(cat "${worker_dir}/worker.log")"
[[ ! -e "${worker_dir}/timed-out-sessions" ]] \
  || fail "the worker made a quarantine for a session that never existed"
# A replay SIGKILLed well inside its bound -- the kernel's memory killer --
# exits 137 like one killed on it, and is no timeout (hdfs-17960 v65-v67).
worker_dir="${bound_dir}/killed"
mkdir -p "${worker_dir}"
replay_timeout_s=60
concolic_replay_command='kill -KILL $$'
(
  campaign_solve_obligation() {
    jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
      obligationId: "OB.2", verdict: "SAT_MODEL_READY", sessionId: "",
      detail: ""}' >"${worker_dir}/obligation_result.jsonl"
    printf '{"taskId":"TASK.1"}\n' >"${worker_dir}/focused_task.jsonl"
    printf '(assert true)\n' >"${worker_dir}/obligation_query.smt2"
  }
  campaign_obligation_worker OB.2 "${bound_dir}/obligations.jsonl" \
    "${bound_dir}/classes" "${worker_dir}" "${bound_dir}/sessions" \
    "${bound_dir}/seed_plan.jsonl"
) >"${worker_dir}/worker.log" 2>&1 \
  || fail "the worker did not return when its replay was killed: \
$(cat "${worker_dir}/worker.log")"
[[ "$(jq -r '.verdict + " " + .detail' \
    "${worker_dir}/obligation_result.jsonl")" \
    == "NOT_ADMITTED replay was killed (exit 137) after "*"s, inside its 60s bound: by its memory reservation (the replay log says so), the kernel's memory killer or an operator" ]] \
  || fail "a replay killed inside its bound is recorded as something else: \
$(cat "${worker_dir}/obligation_result.jsonl")"

# REPLAY-BOUND-4: the session a killed replay left behind leaves the corpus.
# SessionPublisher writes manifest.json at the OPEN, so a replay killed at
# work has a session that NAMES its obligation and states no verdict for it
# -- which Composer.settled reads as UNSTATED_VALUE/BLOCKING.  The wave now
# closes on the NOT_ADMITTED row, so without this the campaign would trade a
# stopped wave for a withheld candidate: one hung JVM, no claim.  The
# directory is moved under the worker, never deleted, and the lookup is the
# manifest -- eight workers write into one sessions directory, so a session
# naming somebody else's obligation must not be touched.
withdraw_dir="${bound_dir}/withdraw"
withdraw_sessions="${withdraw_dir}/sessions"
withdraw_worker="${withdraw_dir}/obligation"
mkdir -p "${withdraw_worker}" "${withdraw_sessions}" "${withdraw_dir}/classes"
printf '{"taskId":"TASK.1"}\n' >"${withdraw_dir}/seed_plan.jsonl"
: >"${withdraw_dir}/obligations.jsonl"
# Another worker's session, open at the same moment and naming its own
# obligation: untouched, whatever happens to ours.
mkdir -p "${withdraw_sessions}/SESSION.other"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.other", role: "FOCUSED",
  obligationIds: ["OB.OTHER"]}' \
  >"${withdraw_sessions}/SESSION.other/manifest.json"
: >"${withdraw_sessions}/SESSION.other/activations.jsonl"
# The replay opens its session -- manifest first, as SessionPublisher does --
# and then hangs, exactly like the JVM that deadlocked on two class monitors.
cat >"${withdraw_dir}/replay.sh" <<EOF
#!/usr/bin/env bash
set -euo pipefail
mkdir -p "\${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.mine"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.mine", role: "FOCUSED", obligationIds: ["OB.1"]}' \\
  >"\${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.mine/manifest.json"
sleep 120
EOF
chmod +x "${withdraw_dir}/replay.sh"
# Five seconds: the replay must open its session before the bound fires, and
# it starts as a login shell (an NFS quota check alone can take a second).
replay_timeout_s=5
concolic_replay_command="${withdraw_dir}/replay.sh"
(
  campaign_solve_obligation() {
    jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
      obligationId: "OB.1", verdict: "SAT_MODEL_READY", sessionId: "",
      detail: ""}' >"${withdraw_worker}/obligation_result.jsonl"
    printf '{"taskId":"TASK.1"}\n' >"${withdraw_worker}/focused_task.jsonl"
    printf '(assert true)\n' >"${withdraw_worker}/obligation_query.smt2"
  }
  campaign_obligation_worker OB.1 "${withdraw_dir}/obligations.jsonl" \
    "${withdraw_dir}/classes" "${withdraw_worker}" "${withdraw_sessions}" \
    "${withdraw_dir}/seed_plan.jsonl"
) >"${withdraw_worker}/worker.log" 2>&1 \
  || fail "the worker did not return when its replay outlived the bound: \
$(cat "${withdraw_worker}/worker.log")"
[[ ! -e "${withdraw_sessions}/SESSION.mine" ]] \
  || fail "the timed-out replay's session is still in the corpus, where \
COMPOSE reads it and refuses the candidate BLOCKING: \
$(find "${withdraw_sessions}" -maxdepth 2 | LC_ALL=C sort)"
[[ -f "${withdraw_worker}/timed-out-sessions/SESSION.mine/manifest.json" ]] \
  || fail "the withdrawn session is not kept under the worker that owned it: \
$(find "${withdraw_worker}" -maxdepth 3 | LC_ALL=C sort)"
[[ "$(jq -r '.obligationIds[0]' \
    "${withdraw_worker}/timed-out-sessions/SESSION.mine/manifest.json")" \
    == OB.1 ]] \
  || fail "the withdrawn session is not the one that named this obligation"
# The other worker's session, and every row in it, exactly where it was.
[[ -f "${withdraw_sessions}/SESSION.other/manifest.json" ]] \
  || fail "another worker's session was withdrawn with ours"
[[ -f "${withdraw_sessions}/SESSION.other/activations.jsonl" ]] \
  || fail "another worker's session lost rows"
[[ ! -e "${withdraw_worker}/timed-out-sessions/SESSION.other" ]] \
  || fail "another worker's session was moved under our worker"
grep -q 'withdrew session SESSION.mine' "${withdraw_worker}/worker.log" \
  || fail "the withdrawal is not logged: $(cat "${withdraw_worker}/worker.log")"
# The verdict row is untouched by any of this: it is still the one terminal
# answer this obligation reached.
[[ "$(jq -r '.verdict' "${withdraw_worker}/obligation_result.jsonl")" \
    == NOT_ADMITTED ]] \
  || fail "withdrawing the session changed the verdict row: \
$(cat "${withdraw_worker}/obligation_result.jsonl")"
[[ "$(jq -r '.detail' "${withdraw_worker}/obligation_result.jsonl")" \
    == "replay exceeded replay_timeout_s=5" ]] \
  || fail "withdrawing the session changed the recorded detail: \
$(cat "${withdraw_worker}/obligation_result.jsonl")"

# REPLAY-BOUND-5: ONE WRITER, after the replay's process group is gone.
# solr-18406 ra1: a TERM on the bound ended the launcher at once while the
# JVM below it ran its shutdown hooks, which rewrote the verdict a second
# after the worker wrote its own, naming the session the worker had just
# withdrawn.  Here a group member outlives its launcher, shrugs off the TERM
# and writes the answer file late: the worker's row still stands, because
# the worker writes only once nothing of the group runs.
late_dir="${bound_dir}/late"
late_worker="${late_dir}/obligation"
mkdir -p "${late_worker}" "${late_dir}/sessions"
cat >"${late_dir}/replay.sh" <<EOF
#!/usr/bin/env bash
( trap '' TERM; sleep 3
  jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: "OB.L",
    verdict: "ADMITTED", sessionId: "SESSION.late", detail: "late"}' \\
    >"\${CAUSYNTH_CONCOLIC_WORKER_DIR}/obligation_result.jsonl" ) &
sleep 120
EOF
chmod +x "${late_dir}/replay.sh"
# Four seconds: the launcher must be running when the bound fires.
replay_timeout_s=4
concolic_replay_command="${late_dir}/replay.sh"
printf '{"taskId":"TASK.1"}\n' >"${late_worker}/focused_task.jsonl"
printf 'F:Q\n' >"${late_worker}/question.asked"
(
  campaign_adapter_kill_grace_s=10
  campaign_obligation_replay OB.L "${withdraw_dir}/classes" \
    "${late_worker}" "${late_dir}/sessions" "${withdraw_dir}/seed_plan.jsonl" \
    2500
) >"${late_worker}/worker.log" 2>&1 \
  || fail "REPLAY-BOUND-5: the worker failed: $(cat "${late_worker}/worker.log")"
[[ "$(jq -r '.verdict + " " + .detail' \
    "${late_worker}/obligation_result.jsonl")" \
    == "NOT_ADMITTED replay exceeded replay_timeout_s=4" ]] \
  || fail "REPLAY-BOUND-5: a member of the replay's group wrote after the \
worker: $(cat "${late_worker}/obligation_result.jsonl")"
[[ ! -e "${late_worker}/question.asked" && ! -e "${late_worker}/question.txt" ]] \
  || fail "REPLAY-BOUND-5: a killed replay's question stands settled"

# EARLY-END-1: a replay a refusal decided ended there, and its verdict names
# no session (RowRuntime.closeSession): the session it opened is a prefix of
# a run and is withdrawn on the host that ran it, under the worker; the
# verdict row stays the replay's own.  The head, reading a peer's result,
# waits until its own listing of the worker's staged sessions holds none
# naming the obligation, where it would land it.
refused_dir="${bound_dir}/refused"
refused_worker="${refused_dir}/obligation"
mkdir -p "${refused_worker}" "${refused_dir}/sessions"
cat >"${refused_dir}/replay.sh" <<EOF
#!/usr/bin/env bash
set -euo pipefail
mkdir -p "\${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.cut"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.cut", role: "FOCUSED", obligationIds: ["OB.R"]}' \\
  >"\${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.cut/manifest.json"
jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: "OB.R",
  verdict: "NOT_ADMITTED", sessionId: "", detail: "wrong decision; ended"}' \\
  >"\${CAUSYNTH_CONCOLIC_WORKER_DIR}/replay_verdict.jsonl"
EOF
chmod +x "${refused_dir}/replay.sh"
replay_timeout_s=60
concolic_replay_command="${refused_dir}/replay.sh"
printf '{"taskId":"TASK.1"}\n' >"${refused_worker}/focused_task.jsonl"
printf 'F:Q\n' >"${refused_worker}/question.asked"
(
  campaign_obligation_replay OB.R "${withdraw_dir}/classes" \
    "${refused_worker}" "${refused_dir}/sessions" \
    "${withdraw_dir}/seed_plan.jsonl" 2500
) >"${refused_worker}/worker.log" 2>&1 \
  || fail "EARLY-END-1: the worker failed on a replay that published no \
session: $(cat "${refused_worker}/worker.log")"
[[ ! -e "${refused_dir}/sessions/SESSION.cut" \
    && -f "${refused_worker}/refused-sessions/SESSION.cut/manifest.json" ]] \
  || fail "EARLY-END-1: the session of a replay whose verdict names none is \
not withdrawn under its worker: $(find "${refused_dir}" | LC_ALL=C sort)"
[[ "$(jq -r '.detail' "${refused_worker}/obligation_result.jsonl")" \
    == "wrong decision; ended" ]] \
  || fail "EARLY-END-1: the withdrawal changed the replay's verdict row"
[[ "$(cat "${refused_worker}/question.txt" 2>/dev/null)" == F:Q \
    && ! -e "${refused_worker}/question.asked" ]] \
  || fail "EARLY-END-1: the question a replay decided is not settled"
mkdir -p "${refused_worker}/sessions/SESSION.stale"
cp "${refused_worker}/refused-sessions/SESSION.cut/manifest.json" \
  "${refused_worker}/sessions/SESSION.stale/"
( sleep 2; rm -rf "${refused_worker}/sessions/SESSION.stale" ) &
campaign_remote_visibility_wait_s=30 campaign_await_remote_result \
  "${refused_worker}" peer OB.R \
  >"${refused_worker}/await.log" 2>&1 \
  || fail "EARLY-END-1: the head did not wait out a listing that still held \
the withdrawn session: $(cat "${refused_worker}/await.log")"
[[ ! -e "${refused_worker}/sessions/SESSION.stale" ]] \
  || fail "EARLY-END-1: the head returned while its listing held the session"
wait
reset_config

# ---- CHECKOUT-STATE-1: a clean tree hashes nothing -------------------------
#
# `printf '%s\n' ""` emits one empty line, awk prints an empty field for it,
# and "${repo}/" exists -- so before the guard a CLEAN checkout walked the
# whole repository, including the multi-GB agent git worktrees under .claude/,
# and digested files no commit of the repo contains.  hdfs-11741 campaign #6
# sat in FREEZE for over seven minutes on a tree that had just gone clean.
checkout_repo="${test_tmp}/checkout-state"
mkdir -p "${checkout_repo}/heavy"
git -C "${checkout_repo}" init -q
git -C "${checkout_repo}" config user.email t@t
git -C "${checkout_repo}" config user.name t
printf 'tracked\n' >"${checkout_repo}/tracked.txt"
git -C "${checkout_repo}" add tracked.txt
git -C "${checkout_repo}" -c commit.gpgsign=false commit -q -m seed
# An untrackable heap that no clean-tree digest may ever reach.
printf 'ignored\n' >"${checkout_repo}/.gitignore"
printf 'heavy/\n' >>"${checkout_repo}/.gitignore"
git -C "${checkout_repo}" add .gitignore
git -C "${checkout_repo}" -c commit.gpgsign=false commit -q -m ignore
for i in 1 2 3; do printf 'noise %s\n' "${i}" >"${checkout_repo}/heavy/f${i}"; done

clean_state=$(campaign_checkout_state "${checkout_repo}") \
  || fail "CHECKOUT-STATE-1: a clean checkout state failed"
[[ "$(printf '%s' "${clean_state}" | jq -r '.branch')" != "" ]] \
  || fail "CHECKOUT-STATE-1: the clean state states no branch"

# The digest of a clean tree is the digest of nothing but its one empty line,
# so it must NOT change when an ignored file underneath it changes.
printf 'noise changed\n' >"${checkout_repo}/heavy/f1"
clean_again=$(campaign_checkout_state "${checkout_repo}") \
  || fail "CHECKOUT-STATE-1: the second clean checkout state failed"
[[ "$(printf '%s' "${clean_state}" | jq -r '.worktreeDigest')" \
    == "$(printf '%s' "${clean_again}" | jq -r '.worktreeDigest')" ]] \
  || fail "CHECKOUT-STATE-1: a clean tree's digest followed a file the \
repository does not track, so the walk reached the repository root"

# And a tree that DOES state an entry still digests that entry's content.
printf 'untracked\n' >"${checkout_repo}/loose.txt"
dirty_state=$(campaign_checkout_state "${checkout_repo}") \
  || fail "CHECKOUT-STATE-1: a dirty checkout state failed"
[[ "$(printf '%s' "${dirty_state}" | jq -r '.worktreeDigest')" \
    != "$(printf '%s' "${clean_state}" | jq -r '.worktreeDigest')" ]] \
  || fail "CHECKOUT-STATE-1: an untracked file did not change the digest"
printf 'untracked, differently\n' >"${checkout_repo}/loose.txt"
[[ "$(campaign_checkout_state "${checkout_repo}" | jq -r '.worktreeDigest')" \
    != "$(printf '%s' "${dirty_state}" | jq -r '.worktreeDigest')" ]] \
  || fail "CHECKOUT-STATE-1: the content of a stated entry is not digested"
# STREAM: EXPLORE is one streaming loop (PIPELINE §7.7, §7.9).  The planner,
# the worker, the gate and COMPOSE are stubbed -- each stands where its JVM
# stands -- and everything between them is the production loop: the queue,
# the ledger's admission, landing, the head's steps, rounds and their
# in-flight rows, the stops.
#
# stream_fixture <name>: an iteration and a configuration of its own; a case
# then says what each round proposes (stream_round_plan <round> <out>: rows
# into <out>/obligations.jsonl, and stream_wave) and what each obligation does
# (campaign_obligation_worker).  The declared occurrence is {"node": "anchor"}.
stream_fixture() {
  stream_dir="${test_tmp}/$1/iteration-0000"
  mkdir -p "${stream_dir}/sessions" "${stream_dir}/seed-replay"
  printf '{"taskId":"TASK.seed"}\n' >"${stream_dir}/execution_task_plan.jsonl"
  ln -f "${stream_dir}/execution_task_plan.jsonl" \
    "${stream_dir}/seed-replay/execution_task_plan.jsonl"
  reset_config
  campaign_root="${test_tmp}/$1"
  campaign_host_gate_root="${test_tmp}/$1/hosts"
  campaign_worker_hosts=""
  obligation_memory_mb=1
  engine_memory_mb=1
  causynth_static_scope_map=""
  causynth_root_domains=""
  declared_target_occurrence=""
  campaign_host_poll_s=1
  campaign_adapter_kill_grace_s=1
}
# Where explore.ExploreMain stands: the files it states every round.
stream_planner() {
  local round="" out="" flying=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --round) round=$2; shift 2 ;;
      --output-dir) out=$2; shift 2 ;;
      --in-flight) flying=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  jq -r '.obligationId' "${flying}" | LC_ALL=C sort | paste -sd ' ' - \
    >"${out}/in-flight.txt"
  : >"${out}/obligations.jsonl"
  printf '{"kind":"FRONTIER","open":0}\n' >"${out}/growth.jsonl"
  stream_wave=0
  stream_round_plan "${round}" "${out}"
  jq -n --argjson wave "${stream_wave}" \
    --argjson truncated "${stream_truncated:-0}" \
    '{wave: $wave, witnesses: [], branchesStopped: 0, truncated: $truncated,
      anchorOccurrences: [{node: "anchor"}]}' \
    >"${out}/explore_manifest.json"
}
# One obligation row per id, as a round proposes it.
stream_propose() {
  local out=$1 id
  shift
  for id in "$@"; do
    printf '{"obligationId":"%s"}\n' "${id}" >>"${out}/obligations.jsonl"
  done
}
# What a worker leaves: its answer, and the session it staged when it names
# one -- with `fatal`, one whose target row at the declared occurrence
# observed the fatal, before a row of another occurrence that did not.
stream_answer() {
  local worker=$1 id=$2 verdict=$3 session=${4:-} fatal=${5:-}
  if [[ -n "${session}" ]]; then
    mkdir -p "${worker}/sessions/${session}"
    jq -n -c --arg session "${session}" --arg id "${id}" \
      '{schemaVersion: 1, kind: "SESSION_MANIFEST", sessionId: $session,
        role: "FOCUSED", obligationIds: [$id]}' \
      >"${worker}/sessions/${session}/manifest.json"
    jq -n -c --argjson fatal "$([[ -n "${fatal}" ]] && echo true \
        || echo false)" '{occurrence: {node: "anchor"}, observedFatal: $fatal},
        {occurrence: {node: "elsewhere"}, observedFatal: false}' \
      >"${worker}/sessions/${session}/targets.jsonl"
  fi
  jq -n -c --arg id "${id}" --arg verdict "${verdict}" \
    --arg session "${session}" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: $verdict, sessionId: $session, detail: ""}' \
    >"${worker}/obligation_result.jsonl"
}
# The stubs every STREAM case shares: a host with room, a gate that records
# what it gated, one line per call.
stream_stubs() {
  campaign_host_available_mb() { echo 30000; }
  campaign_host_total_mb() { echo 30000; }
  run_java_main() { stream_planner "$@"; }
  # Where CONFIRM stands: the attempt's claim confirmed, unless
  # stream_refute names the attempt.
  campaign_confirm_claim() {
    local confirmed=true refutes=false
    if [[ " ${stream_refute:-} " == *" $(basename "$2") "* ]]; then
      confirmed=false
      refutes=true
    fi
    campaign_confirm_verdict "${confirmed}" "stub" "" "${refutes}" \
      >"$2/confirm.json"
  }
  campaign_import_gate() {
    shift 3
    local gated
    for gated in "$@"; do basename "${gated}"; done | paste -sd ' ' - \
      >>"${stream_dir}/gated.txt"
  }
}

# STREAM-1: NO BARRIER.  A round is planned as soon as a session lands, while
# what else runs goes on, and what it proposes starts at once: NEXT, proposed
# once SHORT's session landed, starts while LONG -- proposed with SHORT in
# round 0 -- still runs, and that round is handed LONG as in flight.  An
# obligation whose worker did not finish is its own answer, and what it staged
# is withdrawn under it.  When nothing is queued or running, a last round over
# every answer proposes nothing: the fixed point.  An empty host list is this
# machine, with no ssh.
stream_fixture stream-1
(
  stream_stubs
  ssh() { printf '%s\n' "$*" >>"${stream_dir}/ssh-calls.txt"; return 99; }
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" LONG SHORT BROKEN ;;
      1) stream_propose "$2" NEXT ;;
    esac
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    date +%s.%N >"${worker}/started-at"
    case "${id}" in
      LONG) sleep 3; stream_answer "${worker}" "${id}" UNSAT ;;
      SHORT) stream_answer "${worker}" "${id}" ADMITTED SESSION.SHORT ;;
      BROKEN)
        mkdir -p "${worker}/sessions/SESSION.BROKEN"
        jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
          sessionId: "SESSION.BROKEN", role: "FOCUSED",
          obligationIds: ["BROKEN"]}' \
          >"${worker}/sessions/SESSION.BROKEN/manifest.json"
        return 7 ;;
      NEXT) stream_answer "${worker}" "${id}" UNSAT ;;
    esac
    date +%s.%N >"${worker}/ended-at"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the streaming loop did not finish: $(cat "${stream_dir}/explore.log")"
[[ -d "${stream_dir}/obligations-0002" && ! -e "${stream_dir}/obligations-0003" ]] \
  || fail "the loop did not end at its first round with nothing to ask: \
$(ls "${stream_dir}")"
[[ "$(cat "${stream_dir}/obligations-0001/in-flight.txt")" == *LONG* ]] \
  || fail "the round planned while LONG ran was not handed it as in flight: \
$(cat "${stream_dir}/obligations-0001/in-flight.txt")"
awk -v s="$(cat "${stream_dir}/obligations-0001/NEXT/started-at")" \
    -v e="$(cat "${stream_dir}/obligations-0000/LONG/ended-at")" \
    'BEGIN{exit !(s < e)}' \
  || fail "NEXT did not start until LONG ended: a barrier, not a stream"
[[ -z "$(cat "${stream_dir}/obligations-0002/in-flight.txt")" ]] \
  || fail "the last round was planned with work still in flight"
jq -e -s 'map(.obligationId) | sort == ["BROKEN","LONG","NEXT","SHORT"]' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the ledger is not every obligation's answer, once: \
$(cat "${stream_dir}/obligation_results.jsonl")"
jq -e -s '.[] | select(.obligationId == "BROKEN")
  | .verdict == "NOT_ADMITTED" and (.detail | test("exit 7"))' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the unfinished obligation is not answered as itself"
[[ -f "${stream_dir}/obligations-0000/BROKEN/unfinished-sessions/SESSION.BROKEN/manifest.json" \
    && ! -e "${stream_dir}/sessions/SESSION.BROKEN" ]] \
  || fail "what the unfinished obligation staged was not withdrawn under it"
[[ -f "${stream_dir}/sessions/SESSION.SHORT/manifest.json" \
    && ! -e "${stream_dir}/obligations-0000/SHORT/sessions/SESSION.SHORT" ]] \
  || fail "the staged session did not land in the corpus"
[[ "$(cat "${stream_dir}/gated.txt")" == SESSION.SHORT ]] \
  || fail "the gate did not judge exactly the landed session: \
$(cat "${stream_dir}/gated.txt")"
jq -e '.stop == "FIXED_POINT" and .rounds == 3 and .answered == 4
  and .cancelled == [] and .reaped == []' "${stream_dir}/exploration.json" \
  >/dev/null || fail "exploration.json does not state the fixed point: \
$(cat "${stream_dir}/exploration.json")"
[[ "$(jq -r '.subject' "${stream_dir}/campaign_gaps.jsonl")" \
    == OBLIGATION_UNFINISHED \
    && "$(campaign_unfinished_count "${stream_dir}")" -eq 1 ]] \
  || fail "the unfinished obligation is not its own counted gap row, or a \
loop that reached its fixed point wrote a stop row: \
$(cat "${stream_dir}/campaign_gaps.jsonl" 2>&1)"
[[ ! -e "${stream_dir}/ssh-calls.txt" ]] \
  || fail "an empty campaign_worker_hosts invoked ssh"
[[ "$(cat "${stream_dir}"/obligations-*/*/host.txt | LC_ALL=C sort -u)" \
    == localhost ]] || fail "a local obligation did not record its host"
[[ ! -s "${campaign_host_gate_root}/$(hostname -s)/starts" ]] \
  || fail "an obligation's ledger row outlived its return: \
$(cat "${campaign_host_gate_root}/$(hostname -s)/starts")"

# STREAM-2: THE END AT A WITNESS (PIPELINE §7.9).  An admitted replay whose
# target row at the declared occurrence observed the fatal is, once gated,
# attempted by the next head step: one COMPOSE over the corpus as it stands.
# Obligations keep starting while it runs (one core here: B, C and LONG
# start during A's attempt), nothing lands, and the witnesses that return
# meanwhile (B, C) are attempted together in the next attempt.  One that does
# not accept the claim lets the exploration go on; one that publishes
# SAT_CANDIDATE with its polarity deciding ends it at once: the queue
# cancelled, what runs reaped and moved out of the iteration, each named in
# exploration.json, and the end a DIAGNOSTIC row.
stream_fixture stream-2
mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
printf '1\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
(
  stream_stubs
  # Every round's closure truncated: an accepted witness asks nothing past
  # it, so that blocks nothing.
  stream_truncated=3
  stream_round_plan() {
    [[ "$1" != 0 ]] || stream_propose "$2" A B C LONG1 LONG2
  }
  # Where ComposeMain stands, two seconds long: the claim is accepted once
  # C's session is in.
  do_compose() {
    local claim=UNSAT_CLOSED
    date +%s.%N >>"${stream_dir}/attempt-started-at"
    sleep 2
    [[ ! -d "${compose_sessions_dir}/SESSION.C" ]] || claim=SAT_CANDIDATE
    jq -n --arg claim "${claim}" '{solver: {campaignClaim: {claim: $claim,
      findingKind: "CLOCK_SKEW", polarityDecides: true}}}' \
      >"${composition_manifest}"
    date +%s.%N >>"${stream_dir}/attempt-ended-at"
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    date +%s.%N >"${worker}/started-at"
    case "${id}" in
      A|B|C) stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}" fatal ;;
      *) sleep 60 & printf '%s\n' "$!" >"${worker}/sleep.pid"; wait ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the witnessed loop did not finish: $(cat "${stream_dir}/explore.log")"
jq -e '.stop == "WITNESSED" and .cancelled == ["LONG2"]
  and .reaped == ["LONG1"]
  and ([.witnessAttempts[].accepted] == [false, true])
  and ([.witnessAttempts[].witnesses]
       == [["SESSION.A"], ["SESSION.B", "SESSION.C"]])' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "exploration.json does not name the end, the coalesced attempts, \
the cancelled and the reaped: $(cat "${stream_dir}/exploration.json")"
stream_reaped="${campaign_root}/explore-reaped/obligations-0000/LONG1"
awk -v s="$(cat "${stream_reaped}/started-at")" \
    -v e="$(head -n 1 "${stream_dir}/attempt-ended-at")" \
    'BEGIN{exit !(s > 0 && s < e)}' \
  || fail "nothing started while the first attempt ran"
[[ -s "${stream_reaped}/sleep.pid" \
    && ! -e "${stream_dir}/obligations-0000/LONG1" \
    && ! -e "${stream_dir}/obligations-0000/LONG2" ]] \
  || fail "the reaped and the cancelled obligations are still in the \
iteration: $(ls "${stream_dir}/obligations-0000")"
! kill -0 "$(cat "${stream_reaped}/sleep.pid")" 2>/dev/null \
  || fail "the running obligation was not reaped"
jq -e -s 'map(.obligationId) | sort == ["A","B","C"]' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the ledger holds more than what landed before the end"
jq -e 'select(.subject == "WITNESSED" and .cls == "DIAGNOSTIC")' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "the end at a witness is not a DIAGNOSTIC row"
! jq -e 'select(.cls == "BLOCKING")' "${stream_dir}/campaign_gaps.jsonl" \
  >/dev/null \
  || fail "a truncated closure blocked a claim the accepted witness ended: \
$(cat "${stream_dir}/campaign_gaps.jsonl")"
[[ "$(jq -r '.solver.campaignClaim.claim' "${stream_dir}/witness-attempts/\
0001/candidate_composition_manifest.json")" == SAT_CANDIDATE ]] \
  || fail "the accepted attempt's composition is not kept"

# STREAM-2b: A REFUTED WITNESS.  An attempt whose claim CONFIRM refutes is
# not accepted: the exploration goes on, and the next witness's attempt,
# confirmed, ends it.
stream_fixture stream-2b
(
  stream_stubs
  stream_refute=0000
  stream_round_plan() {
    [[ "$1" != 0 ]] || stream_propose "$2" A B
  }
  do_compose() {
    jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE",
      findingKind: "CLOCK_SKEW", polarityDecides: true}}}' \
      >"${composition_manifest}"
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    [[ "${id}" == A ]] || sleep 3
    stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}" fatal
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the refuted-witness loop did not finish: \
$(cat "${stream_dir}/explore.log")"
jq -e '.stop == "WITNESSED"
  and ([.witnessAttempts[] | [.accepted, .confirmed]]
       == [[false, false], [true, true]])
  and ([.witnessAttempts[].witnesses] == [["SESSION.A"], ["SESSION.B"]])' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "a refuted witness ended the exploration, or the next was not \
attempted: $(cat "${stream_dir}/exploration.json")"

# STREAM-3: THE WAVE BUDGET.  A wave deepens only as sessions land: round 1,
# planned once A's session landed, is of wave 1.  A round of wave
# region_path_max_waves that still owes work is not dispatched, the queue is
# cancelled, what runs lands, and the stop is a DIAGNOSTIC row.
stream_fixture stream-3
region_path_max_waves=1
(
  stream_stubs
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" A SLOW ;;
      *) stream_wave=1; stream_propose "$2" NEVER ;;
    esac
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    case "${id}" in
      A) stream_answer "${worker}" A ADMITTED SESSION.A ;;
      SLOW) sleep 2; stream_answer "${worker}" SLOW UNSAT ;;
      *) fail "an obligation past the wave budget started" ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the bounded loop did not finish: $(cat "${stream_dir}/explore.log")"
jq -e 'select(.subject == "REGION_PATH_WAVE_BUDGET_REACHED")
  | .detail | test("region_path_max_waves=1") and test("1 obligation")' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "the wave budget is not stated as a gap row: \
$(cat "${stream_dir}/campaign_gaps.jsonl")"
jq -e -s 'map(.obligationId) | sort == ["A","SLOW"]' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "what ran when the budget stopped the exploration did not land"
jq -e '.stop == "REGION_PATH_WAVE_BUDGET_REACHED" and .rounds == 2
  and .cancelled == ["NEVER"]' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "exploration.json does not state the budget stop and name what \
it left unasked"
[[ ! -e "${stream_dir}/obligations-0001/NEVER" ]] \
  || fail "a round past the budget was dispatched"

# STREAM-3c: THE CAMPAIGN BUDGET.  Between two steps, once the campaign's
# budget has no room for the stages after the exploration (its reserve,
# campaign_reserve), the exploration ends as at a witness: the queue
# cancelled, what runs reaped, and the stop a DIAGNOSTIC row.
stream_fixture stream-3c
(
  stream_stubs
  campaign_budget_s=3
  campaign_reserve_s=1
  campaign_started_s=${SECONDS}
  stream_round_plan() {
    [[ "$1" != 0 ]] || stream_propose "$2" SLOW
  }
  campaign_obligation_worker() {
    local worker=$4
    sleep 60 & printf '%s\n' "$!" >"${worker}/sleep.pid"; wait
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the budgeted loop did not finish: $(cat "${stream_dir}/explore.log")"
jq -e '.stop == "CAMPAIGN_BUDGET_REACHED" and .reaped == ["SLOW"]' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "the campaign budget did not end the exploration: \
$(cat "${stream_dir}/exploration.json")"
jq -e 'select(.subject == "CAMPAIGN_BUDGET_REACHED" and .cls == "DIAGNOSTIC")
  | .detail | test("campaign_budget_s")' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "the budget stop is not a DIAGNOSTIC row: \
$(cat "${stream_dir}/campaign_gaps.jsonl")"

# STREAM-3b: A PLANNER OUT OF HEAP.  A round whose planner ran out of the most
# heap a head JVM is given (exit 3) is not planned: its directory goes, what
# runs lands, the exploration ends on the rounds before it, and the stop is
# a BLOCKING row naming the planner's error (sweep a40h2, DataStreamer-638).
stream_fixture stream-3b
(
  stream_stubs
  run_java_main() {
    if [[ " $* " == *" --round 1 "* ]]; then
      echo "Terminating due to java.lang.OutOfMemoryError: Java heap space" >&2
      return 3
    fi
    stream_planner "$@"
  }
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A SLOW; }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    case "${id}" in
      A) stream_answer "${worker}" A ADMITTED SESSION.A ;;
      SLOW) sleep 2; stream_answer "${worker}" SLOW UNSAT ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "a planner out of heap failed the exploration: \
$(cat "${stream_dir}/explore.log")"
jq -e 'select(.subject == "PLANNER_HEAP_EXCEEDED" and .cls == "BLOCKING")
  | .detail | test("obligations-0001 ran out") and test("OutOfMemoryError")' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  && jq -e '.stop == "PLANNER_HEAP_EXCEEDED" and .rounds == 1' \
    "${stream_dir}/exploration.json" >/dev/null \
  && jq -e -s 'map(.obligationId) | sort == ["A","SLOW"]' \
    "${stream_dir}/obligation_results.jsonl" >/dev/null \
  && [[ ! -e "${stream_dir}/obligations-0001" ]] \
  || fail "a planner out of heap did not end the exploration by name: \
$(cat "${stream_dir}/campaign_gaps.jsonl" "${stream_dir}/exploration.json")"

# STREAM-4: a planner that states no growth file did not run to completion:
# refused by name, never read as "nothing exposed".
stream_fixture stream-4
(
  stream_stubs
  run_java_main() { :; }
  campaign_explore "${stream_dir}" iteration-0000
) >/dev/null 2>"${stream_dir}/explore.err" \
  && fail "a round with no growth.jsonl was read as nothing exposed"
grep -q 'round growth rows' "${stream_dir}/explore.err" \
  || fail "the missing growth file is not named: \
$(cat "${stream_dir}/explore.err")"

# STREAM-7: THE CLOSURE IT ENDED ON.  An exploration that ends at its fixed
# point on a round whose closure was truncated at the task bound leaves a
# claim over that closure missing arms: one BLOCKING row, naming the round.
stream_fixture stream-7
(
  stream_stubs
  stream_truncated=2
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A; }
  campaign_obligation_worker() {
    stream_answer "$4" A UNSAT
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the truncated loop did not finish: $(cat "${stream_dir}/explore.log")"
jq -e -s 'map(select(.cls == "BLOCKING")) | length == 1
  and (.[0].subject == "REGION_PATH_CLOSURE_TRUNCATED")
  and (.[0].detail | test("FIXED_POINT") and test("obligations-0001")
       and test("2 occurrence"))' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "a fixed point on a truncated closure is not one BLOCKING row: \
$(cat "${stream_dir}/campaign_gaps.jsonl" 2>&1)"

# STREAM-5: THE GATE OVER WHAT LANDED (PIPELINE §6, §7.9).  A step gates the
# sessions landed since the step before, once each is in the corpus, in one
# call against the iteration's ledger, its list and summary in steps/NNNN/;
# a blocking row there fails the campaign at IMPORT, by name, and the head
# ends what it still runs.
stream_fixture stream-5
(
  campaign_host_available_mb() { echo 30000; }
  campaign_host_total_mb() { echo 30000; }
  run_java_main() {
    [[ "$1" == *.ImportGateMain ]] || { stream_planner "$@"; return; }
    shift
    [[ "$*" == "--sessions ${stream_dir}/sessions --gate SESSION.A \
--gated ${stream_dir}/import_gated.txt "* ]] \
      || fail "the step did not gate exactly what landed, against the \
iteration's ledger: $*"
    [[ -d "${stream_dir}/sessions/SESSION.A" ]] \
      || fail "a session was gated before it landed in the corpus"
    # It holds one session at a time: its heap (and charge) is what the
    # largest session takes, not the case's engine heap for a whole corpus.
    [[ "${engine_need_mb}" -ge 512 && "${engine_need_mb}" -lt 1024 ]] \
      || fail "the gate of one small session needs ${engine_need_mb} MB"
    printf '%s\n' '{"violations":1,"blocking":1,'\
'"firstBlockingSubject":"roots.jsonl seq=3 field=recordedValue"}'
  }
  engine_memory_mb=16384
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A LONG; }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    case "${id}" in
      A) sleep 1; stream_answer "${worker}" A ADMITTED SESSION.A ;;
      *) sleep 60 & printf '%s\n' "$!" >"${worker}/sleep.pid"; wait ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  && fail "a blocking row invariant in a landed session did not fail the \
campaign"
grep -q 'stage=IMPORT' "${stream_dir}/explore.log" \
  && grep -q 'roots.jsonl seq=3 field=recordedValue' "${stream_dir}/explore.log" \
  || fail "the gate's failure is not IMPORT's, naming the first blocking \
subject: $(cat "${stream_dir}/explore.log")"
[[ "$(cat "${stream_dir}/steps/0001/gate")" == SESSION.A \
    && -s "${stream_dir}/steps/0001/import_gate.json" ]] \
  || fail "the step wrote no summary beside the list it gated"
! kill -0 "$(cat "${stream_dir}/obligations-0000/LONG/sleep.pid")" \
    2>/dev/null \
  || fail "what ran when the head failed was not ended"

# STREAM-6: THE HEAD STEPS ASIDE.  A step runs in the background: while its
# gate waits (three seconds here), the pool goes on -- B and C start, one
# core at a time, and return -- and what returned meanwhile lands in the
# next step, through one gate.
stream_fixture stream-6
mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
printf '1\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
(
  stream_stubs
  campaign_import_gate() {
    shift 3
    local gated
    [[ -e "${stream_dir}/gate-ran" ]] \
      || { sleep 3; : >"${stream_dir}/gate-ran"; }
    date +%s.%N >>"${stream_dir}/gate-ended-at"
    for gated in "$@"; do basename "${gated}"; done | paste -sd ' ' - \
      >>"${stream_dir}/gated.txt"
  }
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A B C; }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    date +%s.%N >"${worker}/started-at"
    stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the stepping loop did not finish: $(cat "${stream_dir}/explore.log")"
awk -v s="$(cat "${stream_dir}/obligations-0000/C/started-at")" \
    -v e="$(head -n 1 "${stream_dir}/gate-ended-at")" \
    'BEGIN{exit !(s < e)}' \
  || fail "nothing started while the head's first gate ran: a head that \
blocks the pool"
[[ "$(cat "${stream_dir}/gated.txt")" == $'SESSION.A\nSESSION.B SESSION.C' ]] \
  || fail "what returned during a step did not land through one gate in the \
next: $(cat "${stream_dir}/gated.txt")"
jq -e '.stop == "FIXED_POINT" and .answered == 3' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "the stepping loop did not reach its fixed point: \
$(cat "${stream_dir}/exploration.json")"
reset_config

# STREAM-CAP: an exploration under stream_max_in_flight runs no more starts
# at once than its share of it -- the cap over the capped explorations whose
# ledger entry is fresh, its own among them, at least one -- says so once
# for the share it waits at, and takes its entry with it when it ends; with
# no cap it keeps no entry and waits for nothing but room (a40: one Solr
# case's pool held 27-32 replays on all ten lifts while the sweep's other
# cases waited).  Per row: the cap, the fresh and the stale entries of other
# explorations, the most of three one-second obligations that ran at once,
# and how many explorations the wait names (- for none).
while read -r cap_max cap_fresh cap_stale cap_peak cap_sharers; do
  stream_fixture "stream-cap-${cap_max}-${cap_fresh}-${cap_stale}"
  stream_max_in_flight=${cap_max}
  cap_entries="${campaign_host_gate_root}/explorations"
  mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
  printf '8\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
  for ((cap_index = 0; cap_index < cap_fresh + cap_stale; cap_index++)); do
    mkdir -p "${cap_entries}"
    : >"${cap_entries}/other.${cap_index}"
    (( cap_index < cap_fresh )) \
      || touch -d @1000 "${cap_entries}/other.${cap_index}"
  done
  (
    stream_stubs
    stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A B C; }
    campaign_obligation_worker() {
      local id=$1 worker=$4
      date +%s.%N >"${worker}/started-at"
      sleep 1
      date +%s.%N >"${worker}/ended-at"
      stream_answer "${worker}" "${id}" UNSAT
    }
    campaign_explore "${stream_dir}" iteration-0000
  ) >"${stream_dir}/explore.log" 2>&1 \
    || fail "a capped exploration did not finish: \
$(cat "${stream_dir}/explore.log")"
  cap_ran=$(for cap_worker in "${stream_dir}"/obligations-0000/*/; do
      echo "$(cat "${cap_worker}started-at") $(cat "${cap_worker}ended-at")"
    done | awk '{ s[NR] = $1; e[NR] = $2 }
      END { for (i = 1; i <= NR; i++) { n = 0
              for (j = 1; j <= NR; j++) if (s[j] <= s[i] && s[i] < e[j]) n++
              if (n > peak) peak = n }
            print peak }')
  [[ "${cap_ran}" == "${cap_peak}" ]] \
    || fail "cap ${cap_max} with ${cap_fresh} other exploration(s) ran \
${cap_ran} obligation(s) at once, not ${cap_peak}"
  cap_said=$(grep -c 'waiting for a slot' "${stream_dir}/explore.log" \
    || true)
  if [[ "${cap_sharers}" == - ]]; then
    [[ "${cap_said}" -eq 0 && ! -e "${cap_entries}" ]] \
      || fail "an exploration with no cap waited for a slot or kept an entry"
  else
    [[ "${cap_said}" -eq 1 ]] && grep -q "shared by ${cap_sharers} capped" \
      "${stream_dir}/explore.log" \
      || fail "the wait for a slot was not said once, naming \
${cap_sharers} exploration(s): $(grep 'slot' "${stream_dir}/explore.log")"
    [[ "$(ls "${cap_entries}" | wc -l)" -eq $((cap_fresh + cap_stale)) ]] \
      || fail "the exploration's entry outlived it: $(ls "${cap_entries}")"
  fi
done <<'EOF'
0 0 0 3 -
2 0 1 2 1
2 1 0 1 2
1 2 0 1 3
EOF
reset_config
# The cap is a declared workflow key, overridden only through the table, 0
# by default, and a non-negative integer or refused by name.
[[ "$(grep -c 'CAUSYNTH_STREAM_MAX_IN_FLIGHT' "${repo}/run_engine.sh")" \
    -eq 1 && "${stream_max_in_flight}" == 0 ]] && known_config_key \
    stream_max_in_flight \
  || fail "stream_max_in_flight is not a declared key defaulting to 0"
CAUSYNTH_STREAM_MAX_IN_FLIGHT=30 apply_environment_overrides
[[ "${stream_max_in_flight}" == 30 ]] \
  || fail "CAUSYNTH_STREAM_MAX_IN_FLIGHT does not override the key"
reset_config
cap_validate() (
  stop_after_config ""
  stream_max_in_flight=$1
  validate_config
)
for cap_value in "" -1 x 08 0 30; do
  run_capturing_status cap_validate "${cap_value}" >/dev/null \
    2>"${test_tmp}/cap-validate.err"
  case "${cap_value}" in
    0|30) [[ "${status}" -eq 0 ]] \
      || fail "validate refused stream_max_in_flight='${cap_value}'" ;;
    *) [[ "${status}" -ne 0 ]] && grep -q 'stream_max_in_flight must be' \
        "${test_tmp}/cap-validate.err" \
      || fail "validate did not refuse stream_max_in_flight='${cap_value}' \
by name" ;;
  esac
done
reset_config

# HOSTS-1: `campaign_worker_hosts` is a declared workflow key, registered
# exactly like `replay_timeout_s`.
grep -q 'CAUSYNTH_CAMPAIGN_WORKER_HOSTS' "${repo}/run_engine.sh" \
  || fail "the environment override for campaign_worker_hosts is not declared"
[[ "$(grep -c 'CAUSYNTH_CAMPAIGN_WORKER_HOSTS' "${repo}/run_engine.sh")" \
    -eq 1 ]] \
  || fail "CAUSYNTH_CAMPAIGN_WORKER_HOSTS appears outside the key table: \
it is honoured through apply_environment_overrides only"
known_config_key campaign_worker_hosts \
  || fail "campaign_worker_hosts is not loadable from a workflow file"
hosts_dir="${test_tmp}/worker-hosts"
mkdir -p "${hosts_dir}"
reset_config
[[ -z "${campaign_worker_hosts}" ]] \
  || fail "campaign_worker_hosts does not default to empty: \
'${campaign_worker_hosts}'"
printf 'campaign_worker_hosts=lift12 lift13\n' \
  >"${hosts_dir}/workflow.properties"
load_config_file "${hosts_dir}/workflow.properties"
[[ "${campaign_worker_hosts}" == "lift12 lift13" ]] \
  || fail "a workflow file cannot set campaign_worker_hosts: \
'${campaign_worker_hosts}'"
reset_config
CAUSYNTH_CAMPAIGN_WORKER_HOSTS="lift14 lift15" apply_environment_overrides
[[ "${campaign_worker_hosts}" == "lift14 lift15" ]] \
  || fail "CAUSYNTH_CAMPAIGN_WORKER_HOSTS does not override the key"
reset_config
# A host is a machine name.  Anything that could put a command where a
# machine belongs is refused by name before any work starts, because the
# value ends up inside `ssh <host> ...`.
hosts_validate() (
  stop_after_config ""
  campaign_worker_hosts=$1
  validate_config
)
for bad in 'lift12;rm -rf /' 'lift12$(id)' 'lift12|cat' '-oProxyCommand=x' \
    'a"b'; do
  run_capturing_status hosts_validate "${bad}" \
    >/dev/null 2>"${hosts_dir}/validate.err"
  [[ "${status}" -ne 0 ]] \
    || fail "validate accepted campaign_worker_hosts='${bad}'"
  grep -q 'campaign_worker_hosts must be' "${hosts_dir}/validate.err" \
    || fail "the refusal does not name campaign_worker_hosts: \
$(cat "${hosts_dir}/validate.err")"
done
run_capturing_status hosts_validate "localhost lift12 lift13.cs.virginia.edu" \
  >/dev/null 2>"${hosts_dir}/validate.err" \
  || fail "validate refused a plain host list: \
$(cat "${hosts_dir}/validate.err")"
[[ "${status}" -eq 0 ]] || fail "validate refused a plain host list"
reset_config

# HOSTS-2: the pool's hosts.  Empty is this machine; a list is its hosts.
# localhost, and this machine's own name, are local: no ssh for either.
campaign_worker_hosts=""
[[ "$(campaign_worker_host_list)" == localhost ]] \
  || fail "an empty host list is not this machine: $(campaign_worker_host_list)"
campaign_worker_hosts="lift12 lift13"
[[ "$(campaign_worker_host_list | tr '\n' ' ')" == "lift12 lift13 " ]] \
  || fail "a host list is not its hosts: $(campaign_worker_host_list)"
campaign_local_host_names=""
campaign_host_is_local localhost || fail "localhost is not local"
campaign_host_is_local "$(hostname)" \
  || fail "this machine's own hostname is not local"
campaign_host_is_local "$(hostname -s)" \
  || fail "this machine's own short hostname is not local"
campaign_host_is_local "" || fail "the empty host is not local"
! campaign_host_is_local somewhere-else \
  || fail "another machine reads as local"
reset_config

# HOSTS-4: the pool over two peers.  Starts go round-robin from the host
# after the last one chosen, an obligation first to a host where its
# campaign's solver still serves (so the four go where the first went), a
# peer's results and staged session come back and land, and a host whose
# ledger has no room is given nothing while the other runs everything (a10:
# one claim sat 30 min on a lift a planner had filled while eight lifts had
# room).
#
# The stub stands where the network stands and nowhere else: the pool, the
# host decision, the generated remote script and the bounded wait for what
# the peer wrote are the production code.  What the stub does is what a peer
# does -- run the script it was handed -- except that it publishes the
# payload's answer directly, because the payload is a second JVM-bearing
# campaign process and this is a shell test.
stream_two_hosts() {
  local name=$1
  stream_fixture "${name}"
  campaign_worker_hosts="lift12 lift13"
  campaign_local_host_names=" localhost this-machine "
  graphchecker_jar=${default_graphchecker_jar}
  replay_timeout_s=2400
  solver_timeout_ms=1800000
  campaign_init_local_scratch_root
  local host
  for host in lift12 lift13; do
    mkdir -p "${campaign_host_gate_root}/${host}"
    printf '48\n' >"${campaign_host_gate_root}/${host}/cores"
  done
  (
    stream_stubs
    campaign_host_available_mb() {
      [[ "$1" == lift13 && "${name}" == stream-room ]] && echo 0 || echo 30000
    }
    stream_round_plan() {
      [[ "$1" != 0 ]] || stream_propose "$2" A B C D
    }
    ssh() {
      local host="" script="" worker id
      # The production call is `ssh <options> -- <host> <command>`.
      while [[ $# -gt 0 ]]; do
        [[ "$1" == "--" ]] && { shift; break; }
        shift
      done
      host=${1:-}
      script=${2:-}
      script=${script#exec /bin/bash }
      script=${script%\'}
      script=${script#\'}
      printf '%s\t%s\n' "${host}" "${script}" >>"${stream_dir}/ssh-calls.txt"
      # The generated script is what a peer is asked to run, so it had
      # better be a script a peer can run.
      [[ -s "${script}" ]] || return 91
      bash -n "${script}" || return 92
      grep -q -- '--run-obligation' "${script}" || return 93
      grep -q -- "--graphchecker-jar-sha256 $(sha256sum "${graphchecker_jar}" \
        | awk '{print $1}')" "${script}" || return 94
      grep -q "CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root}" \
        "${script}" || return 95
      worker=$(awk '$1 == "--" {print $5; exit}' "${script}")
      id=$(basename "${worker}")
      stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}"
    }
    campaign_explore "${stream_dir}" iteration-0000
  ) >"${stream_dir}/explore.log" 2>&1 \
    || fail "a two-host exploration did not finish: \
$(cat "${stream_dir}/explore.log")"
}
stream_two_hosts stream-two
[[ "$(wc -l <"${stream_dir}/ssh-calls.txt")" -eq 4 ]] \
  || fail "four obligations did not become four remote invocations: \
$(cat "${stream_dir}/ssh-calls.txt")"
[[ "$(cut -f1 "${stream_dir}/ssh-calls.txt" | LC_ALL=C sort | uniq -c \
    | awk '{print $2 "=" $1}' | paste -sd ' ' -)" == "lift12=4" ]] \
  || fail "the obligations did not go where their solver serves: \
$(cut -f1 "${stream_dir}/ssh-calls.txt" | paste -sd ' ' -)"
for stream_id in A B C D; do
  [[ -f "${stream_dir}/sessions/SESSION.${stream_id}/manifest.json" ]] \
    || fail "${stream_id}'s staged session did not land from its peer"
  case "$(cat "${stream_dir}/obligations-0000/${stream_id}/host.txt")" in
    lift12|lift13) ;;
    *) fail "${stream_id} did not record which host ran it" ;;
  esac
done
jq -e -s 'length == 4 and all(.[]; .verdict == "ADMITTED")' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the peers' verdicts were not collected"
stream_two_hosts stream-room
[[ "$(cut -f1 "${stream_dir}/ssh-calls.txt" | LC_ALL=C sort -u)" == lift12 ]] \
  || fail "a host without room was given work: \
$(cut -f1 "${stream_dir}/ssh-calls.txt")"
reset_config

# The pool's choice over three hosts that all admit: a re-run goes
# round-robin; an obligation goes to a host where its campaign's solver
# still serves (one started there within the solver's idle time), else
# round-robin.  {kind, the host warm (- none), the hosts chosen in turn}.
while IFS='|' read -r admit_kind admit_warm admit_want; do
  (
    stream_hosts=(a b c)
    stream_next_host=0
    stream_waiting=""
    declare -A stream_solver_seen=() stream_host_unread=()
    [[ "${admit_warm}" == - ]] \
      || stream_solver_seen[${admit_warm}]=$(date +%s)
    campaign_stream_has_cores() { return 0; }
    campaign_host_try_charge() { status=0; campaign_host_charge_id=x; }
    chosen=()
    for _ in 1 2 3; do
      campaign_stream_admit_host "${admit_kind}" || exit 1
      chosen+=("${stream_admitted_host}")
    done
    [[ "${chosen[*]}" == "${admit_want}" ]] \
      || fail "${admit_kind} with ${admit_warm} warm chose ${chosen[*]}, \
not ${admit_want}"
  ) || fail "the pool admitted nothing for ${admit_kind}"
done <<'EOF'
RERUN|b|a b c
OBLIGATION|-|a b c
OBLIGATION|b|b b b
EOF

# POOL-JOB: a start of the pool runs on the host that admitted it -- an
# obligation's worker, or a GROW re-run's replay, which a peer runs as a
# placed step -- and gives its ledger row back as soon as its work
# returned, before the head waits to see what a peer wrote.  Per row: the
# kind, the host, and what ran, each with the rows the ledger still held for
# it then.
job_dir="${test_tmp}/pool-job"
while IFS='|' read -r job_kind job_host job_ran; do
  rm -rf -- "${job_dir}"
  mkdir -p "${job_dir}/worker"
  : >"${job_dir}/ran"
  (
    campaign_host_gate_root="${job_dir}/hosts"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_host_available_mb() { echo 30000; }
    campaign_host_total_mb() { echo 30000; }
    campaign_host_max_used_pct=70
    campaign_host_try_start "${job_host}" 2500 60 \
      || fail "the job's start was refused"
    job_charge=${campaign_host_charge_id}
    job_record() {
      printf '%s(%s) ' "$1" "$(cat "${campaign_host_gate_root}"/*/starts \
        | grep -c -- "${job_charge}")" >>"${job_dir}/ran"
    }
    campaign_obligation_worker() { job_record "worker:$1"; }
    campaign_obligation_replay() { job_record "replay:$1:$6"; }
    campaign_dispatch_remote() { job_record "$1:$4:$5"; }
    campaign_run_placed() { job_record "$1:$2:$3:$8"; }
    campaign_await_remote_result() { job_record "await:$3"; }
    campaign_stream_job "${job_kind}" "${job_host}" "${job_charge}" OB.1 \
      "${job_dir}/worker" OB.1 b c d e f
  ) || fail "a ${job_kind} on ${job_host} failed"
  [[ "$(cat "${job_dir}/ran")" == "${job_ran} " ]] \
    || fail "a ${job_kind} on ${job_host} ran $(cat "${job_dir}/ran")"
done <<'EOF'
OBLIGATION|localhost|worker:OB.1(1)
OBLIGATION|lift12|lift12:--run-obligation:OB.1(1) await:OB.1(0)
RERUN|localhost|replay:OB.1:f(1)
RERUN|lift12|lift12:campaign_obligation_replay:OB.1:f(1) await:OB.1(0)
EOF

# HOSTS-5: a remote worker whose head is gone kills its own process group.
#
# sshd does not do this.  Measured on lift12: an ssh client killed under a
# `sleep 500` three processes down left every one of them alive, which is
# forty orphan MiniDFSCluster JVMs across four machines for one interrupted
# campaign.  So the generated script watches the parent it was started
# under -- the sshd session process -- and a parent that is no longer that
# one means the connection is gone.
#
# Here the connection is stood in for by an intermediate shell that is
# killed: the wrapper is reparented exactly as it is when sshd dies, which is
# the condition the watchdog actually tests.  Everything else is the
# generated script, produced by the production function, including the
# `timeout` that makes the payload its own process group.
orphan_dir="${test_tmp}/remote-orphan"
mkdir -p "${orphan_dir}/worker"
# The payload, standing where run_engine.sh --run-obligation stands: a
# process with a grandchild under it, which is what a replay JVM is.
mkdir -p "${orphan_dir}/fake-repo"
cat >"${orphan_dir}/fake-repo/run_engine.sh" <<EOF
#!/usr/bin/env bash
sleep 600 &
echo "\$!" >"${orphan_dir}/grandchild.pid"
wait
EOF
chmod +x "${orphan_dir}/fake-repo/run_engine.sh"
(
  graphchecker_dir="${orphan_dir}/fake-repo"
  graphchecker_jar=${default_graphchecker_jar}
  config_file="${orphan_dir}/workflow.properties"
  campaign_local_scratch_root="${orphan_dir}/scratch"
  campaign_worker_hosts=""
  replay_timeout_s=600
  solver_timeout_ms=1000
  : >"${config_file}"
  campaign_write_remote_worker_script "${orphan_dir}/remote-worker.sh" \
    "${orphan_dir}/worker" 600 --run-obligation \
    OB.1 /dev/null /dev/null "${orphan_dir}/worker" /dev/null /dev/null
)
bash -n "${orphan_dir}/remote-worker.sh" \
  || fail "the generated remote worker script is not valid bash"
# The stand-in for sshd: a shell whose child is the wrapper.  Killing it is
# what a dropped connection does.
bash -c "exec /bin/bash '${orphan_dir}/remote-worker.sh'" \
  >"${orphan_dir}/wrapper.log" 2>&1 &
orphan_parent=$!
for _ in $(seq 1 40); do
  [[ -s "${orphan_dir}/grandchild.pid" ]] && break
  sleep 0.25
done
[[ -s "${orphan_dir}/grandchild.pid" ]] \
  || fail "the generated remote worker never started its payload"
orphan_grandchild=$(cat "${orphan_dir}/grandchild.pid")
kill -0 "${orphan_grandchild}" \
  || fail "the payload's grandchild was never running"
kill -KILL "${orphan_parent}" 2>/dev/null
wait "${orphan_parent}" 2>/dev/null || true
# The watchdog polls; it is allowed the poll interval plus slack, and no more.
for _ in $(seq 1 60); do
  kill -0 "${orphan_grandchild}" 2>/dev/null || break
  sleep 0.5
done
if kill -0 "${orphan_grandchild}" 2>/dev/null; then
  pkill -KILL -P "${orphan_grandchild}" 2>/dev/null || true
  kill -KILL "${orphan_grandchild}" 2>/dev/null || true
  fail "a killed head left the remote payload's grandchild \
${orphan_grandchild} running: this is the orphan MiniDFSCluster JVM on four \
machines that kill safety exists to prevent"
fi
# And it said so, naming the parent it lost, so an operator reading a peer's
# logs can tell a killed campaign from a crashed replay.
grep -q 'the campaign that started this is gone' "${orphan_dir}/wrapper.log" \
  || fail "the remote worker killed its payload without saying why: \
$(cat "${orphan_dir}/wrapper.log")"
reset_config

# HOSTS-6: what the peer is NOT allowed to work out for itself.
#
# FREEZE_TOOL rebinds graphchecker_jar to the campaign's private read-only
# copy.  A peer that resolved the key from the configuration would load
# whatever is in target/ at that instant instead -- and on this shared home
# that is a different build the moment anybody runs `mvn package`.  So the
# frozen path is passed, its digest is passed with it, and the worker checks
# the second against the first before it starts.
grep -q 'graphchecker_jar=${jar}' "${repo}/run_engine.sh" \
  || fail "--run-obligation does not take the frozen jar as given"
frozen_dir="${test_tmp}/frozen-jar"
mkdir -p "${frozen_dir}"
printf 'not the frozen jar\n' >"${frozen_dir}/live.jar"
run_capturing_status env -u CAUSYNTH_CAMPAIGN_WORKER_HOSTS \
  "${repo}/run_engine.sh" \
  --config "${repo}/experiments/hadoop/hdfs-11741/workflow.properties" \
  --run-obligation --graphchecker-jar "${frozen_dir}/live.jar" \
  --graphchecker-jar-sha256 \
  0000000000000000000000000000000000000000000000000000000000000000 \
  -- OB.1 a b c d e >/dev/null 2>"${frozen_dir}/err.log"
[[ "${status}" -ne 0 ]] \
  || fail "a worker handed a jar that is not the frozen one still ran"
grep -q 'is not the one the campaign froze' "${frozen_dir}/err.log" \
  || fail "the refusal does not say the jar is not the frozen one: \
$(cat "${frozen_dir}/err.log")"
run_capturing_status "${repo}/run_engine.sh" \
  --config "${repo}/experiments/hadoop/hdfs-11741/workflow.properties" \
  --run-obligation -- OB.1 a b c d e \
  >/dev/null 2>"${frozen_dir}/nojar.log"
[[ "${status}" -ne 0 ]] \
  || fail "--run-obligation ran without being told which jar to load"
grep -q 'requires --graphchecker-jar' "${frozen_dir}/nojar.log" \
  || fail "the refusal does not name the missing jar argument: \
$(cat "${frozen_dir}/nojar.log")"
# A placed head JVM (--run-placed) runs on the peer in the head's working
# directory, its standard output the command's alone: the peer's own words
# (campaign_peer_enter's, which checks the jar as above) go to stderr, since
# that output is often the JVM's artifact.
(
  campaign_peer_enter() {
    campaign_log "peer entered"
    campaign_peer_args=("$@")
  }
  do_run_placed "${frozen_dir}" -- bash -c 'printf "%s" "${PWD##*/}"'
) >"${frozen_dir}/placed.out" 2>"${frozen_dir}/placed.err"
[[ "$(cat "${frozen_dir}/placed.out")" == frozen-jar ]] \
  && grep -q 'peer entered' "${frozen_dir}/placed.err" \
  || fail "--run-placed did not run its command alone in the head's \
directory: $(cat "${frozen_dir}/placed.out" "${frozen_dir}/placed.err")"
# And every workflow key travels as its own environment override, so the
# peer's configuration is the head's rather than a second derivation of it.
reset_config
campaign_worker_hosts="lift12"
replay_timeout_s=1234
[[ "$(campaign_remote_env_assignments | grep -c '^CAUSYNTH_REPLAY_TIMEOUT_S=1234$')" \
    -eq 1 ]] \
  || fail "the peer is not handed the head's replay_timeout_s"
[[ "$(campaign_remote_env_assignments | wc -l)" \
    -eq "$(campaign_remote_env_assignments | cut -d= -f1 | sort -u | wc -l)" ]] \
  || fail "a workflow key is forwarded to the peer more than once"
reset_config

# SCRATCH-1: the replay's scratch root is per user, per RUN and per
# obligation, because two campaigns may share a cluster and a shared
# /localtmp/graphchecker would have them writing into each other.
scratch_probe="${test_tmp}/scratch-root"
mkdir -p "${scratch_probe}"
(
  unset CAUSYNTH_LOCAL_SCRATCH
  campaign_root="${scratch_probe}/run-one"
  campaign_init_local_scratch_root
  one=${campaign_local_scratch_root}
  campaign_root="${scratch_probe}/run-two"
  campaign_init_local_scratch_root
  two=${campaign_local_scratch_root}
  [[ "${one}" != "${two}" ]] \
    || fail "two campaigns share one local scratch root: ${one}"
  [[ "${one}" == /localtmp/* ]] \
    || fail "the replay scratch is not on a local disk: ${one}"
  [[ "${one}" == */"$(id -un)"/* ]] \
    || fail "the replay scratch root is not per user: ${one}"
) || exit 1
# An explicitly EMPTY CAUSYNTH_LOCAL_SCRATCH turns it off; that is what
# `${VAR+x}` is for and what `${VAR:-default}` would have got wrong.
(
  CAUSYNTH_LOCAL_SCRATCH=""
  campaign_root="${scratch_probe}/run-three"
  campaign_init_local_scratch_root
  [[ -z "${campaign_local_scratch_root}" ]] \
    || fail "an empty CAUSYNTH_LOCAL_SCRATCH did not turn local scratch off: \
${campaign_local_scratch_root}"
) || exit 1
# And a stated one is taken as the root, which is how the peer gets the
# head's.
(
  CAUSYNTH_LOCAL_SCRATCH=/localtmp/stated
  campaign_root="${scratch_probe}/run-four"
  campaign_init_local_scratch_root
  [[ "${campaign_local_scratch_root}" == /localtmp/stated ]] \
    || fail "a stated CAUSYNTH_LOCAL_SCRATCH was not taken as the root"
) || exit 1

# SCRATCH-2: the case adapter puts java.io.tmpdir and the system's data
# directory (system_jvm_properties) under it, in a directory of the worker's
# own, and REMOVES that directory when the replay exits -- including when it
# fails.  Only temporary bytes move: the session and the result rows are
# still written to the shared home.
execute_sh="${repo}/experiments/lib/execute.sh"
grep -qF -- '-Djava.io.tmpdir="${tmpdir}" "${jvm_properties[@]}"' \
  "${execute_sh}" \
  && grep -q -- 'system_jvm_properties "${tmpdir}" "${datadir}"' "${execute_sh}" \
  || fail "the adapter no longer takes its scratch paths from one place"
grep -q 'CAUSYNTH_LOCAL_SCRATCH' "${execute_sh}" \
  || fail "the adapter does not honour CAUSYNTH_LOCAL_SCRATCH"
grep -q 'rm -rf -- "${scratch_owned}"' "${execute_sh}" \
  || fail "the adapter does not remove its scratch subdirectory"
grep -q '^trap remove_local_scratch EXIT$\|trap remove_local_scratch EXIT' \
  "${execute_sh}" \
  || fail "the adapter's scratch removal is not on EXIT, so a failed replay \
would leave its MiniDFSCluster data behind on every host it ran on"
bash -n "${execute_sh}" || fail "the adapter is not valid bash"
# The campaign hands it one, per obligation, and hands the peers the same
# root so a remote replay's scratch is on the PEER's local disk.
grep -q 'CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root:+' \
  "${repo}/run_engine.sh" \
  || fail "the campaign does not hand the adapter a per-worker scratch path"
grep -q 'CAUSYNTH_LOCAL_SCRATCH=%q' "${repo}/run_engine.sh" \
  || fail "the peers are not handed the run's local scratch root"

# GROW-1: the growth step (PIPELINE §7.8), inside the stream.  Round 1 names
# a region OB.x's replay reached without its hooks; GROW plans it into a new
# generation of the plan -- the iteration's plan and the seed plan its links
# from then on, the generation before it untouched for whatever runs on it --
# weaves the generation's own tree, and re-runs OB.x's replay first, on the
# head, in a directory beside its worker; once it returns and no obligation
# runs, its session takes the exposing one's place in the corpus, its files
# the worker's and its verdict the ledger's.  The planner, the
# exposed-region planner and the weave are stubbed; the re-run is the
# production replay of a script that publishes a session, so everything
# between is the production code.
stream_fixture grow
stream_seed_plan_inode=$(stat -c %i "${stream_dir}/execution_task_plan.jsonl")
cat >"${stream_dir}/replay.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
grep -q '"REGION.grown"' "${CAUSYNTH_CONCOLIC_TASK_PLAN}" \
  || { echo "the re-run's plan carries no grown row" >&2; exit 9; }
[[ "${CAUSYNTH_CONCOLIC_TASK_ID}" == *TASK.grown* ]] \
  || { echo "the re-run's task ids omit the grown task" >&2; exit 8; }
[[ -f "${CAUSYNTH_CONCOLIC_CLASSES}/woven" ]] \
  || { echo "the re-run does not stand on the grown tree" >&2; exit 7; }
mkdir -p "${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.regrown"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.regrown", role: "FOCUSED", obligationIds: ["OB.x"]}' \
  >"${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.regrown/manifest.json"
jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: "OB.x",
  verdict: "NOT_ADMITTED", sessionId: "SESSION.regrown",
  detail: "the grown region refused the flip"}' \
  >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/replay_verdict.jsonl"
EOF
chmod +x "${stream_dir}/replay.sh"
concolic_replay_command="${stream_dir}/replay.sh"
replay_timeout_s=60
schedule_max_jobs=1
trace_test=T
custom_jdk_home=""
workload_work_dir="${stream_dir}"
(
  stream_stubs
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" OB.x ;;
      1) printf '%s\n' \
'{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
           >>"$2/growth.jsonl" ;;
    esac
  }
  run_java_main() {
    if [[ "$1" == edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain ]]
    then
      local args=" $* " output
      [[ "${args}" == *" --iteration ${stream_dir} "* \
          && "${args}" == *" --growth ${stream_dir}/obligations-0001/growth.jsonl "* ]] \
        || fail "the exposed-region planner was not handed the iteration and \
the round's growth rows: $*"
      output=${args##* --output }
      output=${output%% *}
      printf '{"taskId":"TASK.grown","regionId":"REGION.grown","admissionBasis":"EXPOSED_BY"}\n' \
        >"${output}"
      return 0
    fi
    stream_planner "$@"
  }
  campaign_instrument() {
    [[ "$1" == "${stream_dir}" \
        && "$2" == "${stream_dir}/generations/g1/instrumented-classes" ]] \
      || fail "the weave was given $*"
    grep -q TASK.grown "${stream_dir}/execution_task_plan.jsonl" \
      || fail "the weave ran before the grown rows reached the iteration plan"
    mkdir -p "$2"
    : >"$2/woven"
  }
  campaign_obligation_worker() {
    local worker=$4
    printf '{"taskId":"TASK.seed"}\n' >"${worker}/focused_task.jsonl"
    printf 'the exposing replay\n' >"${worker}/replay.log"
    stream_answer "${worker}" OB.x ADMITTED SESSION.exposing
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the growing exploration did not finish: \
$(cat "${stream_dir}/explore.log")"
stream_worker="${stream_dir}/obligations-0000/OB.x"
grep -q TASK.grown "${stream_dir}/seed-replay/execution_task_plan.jsonl" \
  || fail "the seed plan is not the grown generation's"
[[ "$(stat -c %i "${stream_dir}/generations/g0/execution_task_plan.jsonl")" \
    == "${stream_seed_plan_inode}" ]] \
  && ! grep -q TASK.grown "${stream_dir}/generations/g0/execution_task_plan.jsonl" \
  || fail "the generation before the growth was rewritten under what runs on it"
[[ -s "${stream_dir}/obligations-0001/exposed_region_plan.jsonl" ]] \
  || fail "the grown rows are not kept beside the round that grew them"
[[ ! -e "${stream_dir}/sessions/SESSION.exposing" \
    && -f "${stream_worker}/before-obligations-0001/sessions/SESSION.exposing/manifest.json" ]] \
  || fail "the exposing session is not out of the corpus and under its worker"
[[ -f "${stream_dir}/sessions/SESSION.regrown/manifest.json" ]] \
  || fail "the re-run's session did not reach the corpus"
[[ "$(cat "${stream_worker}/before-obligations-0001/replay.log")" \
    == "the exposing replay" ]] \
  || fail "the exposing replay's log was not kept aside"
[[ "$(jq -r '.verdict' "${stream_worker}/obligation_result.jsonl")" \
    == NOT_ADMITTED && "$(cat "${stream_worker}/host.txt")" == localhost ]] \
  || fail "the worker's answer is not the re-run's, on the head"
jq -e -s 'length == 1 and .[0].obligationId == "OB.x"
  and .[0].verdict == "NOT_ADMITTED" and .[0].sessionId == "SESSION.regrown"' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the re-run's verdict did not replace the exposing one, once: \
$(cat "${stream_dir}/obligation_results.jsonl")"
[[ -f "${stream_dir}/instrumented-classes/woven" \
    && ! -e "${stream_dir}/generations/g1/instrumented-classes" ]] \
  || fail "the last generation's tree is not the iteration's once nothing runs"
grep -q 'grown by REGION.grown' "${stream_dir}/explore.log" \
  && grep -q 'OB.x: re-run under the grown tree, verdict=NOT_ADMITTED' \
    "${stream_dir}/explore.log" \
  || fail "the step did not say what grew and what the re-run decided"
jq -e '.generations == 1 and .stop == "FIXED_POINT"' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "exploration.json does not count the generation"
# An exposure that names no obligation is the seed's, and the seed is not
# re-run: refused by name before any plan is touched.
printf '%s\n' \
  '{"kind":"EXPOSED_REGION","regionId":"REGION.seed","node":"nn0","occurrence":"REGION.seed#1","sessionId":"SESSION.seed","obligationId":""}' \
  >"${stream_dir}/obligations-0001/growth.jsonl"
(
  iteration_dir=${stream_dir}
  run_java_main() { fail "the planner ran on an exposure GROW must refuse"; }
  campaign_stream_grow "${stream_dir}/obligations-0001"
) >/dev/null 2>"${stream_dir}/refuse.log" \
  && fail "an exposure with no obligation was grown into"
grep -q 'names no obligation' "${stream_dir}/refuse.log" \
  || fail "the refusal does not say why: $(cat "${stream_dir}/refuse.log")"
reset_config


# CONFIRM-1: a SAT claim, checked by one replay (PIPELINE §10).  ConfirmMain's
# task and the replay are stubbed -- the first writes the focus row and the
# expected edges, the second publishes a session and its verdict -- and the
# decision is the production code, ConfirmMain --sessions on the built jar:
# the conditions of the rule in order, the first one failing named, and
# never a failed campaign.
confirm_root="${test_tmp}/confirm"
confirm_iteration="${confirm_root}/iteration-0000"
mkdir -p "${confirm_iteration}/instrumented-classes" \
  "${confirm_iteration}/seed-replay" "${confirm_root}/final"
: >"${confirm_iteration}/seed-replay/execution_task_plan.jsonl"
campaign_final="${confirm_root}/final"
composition_manifest="${campaign_final}/candidate_composition_manifest.json"
# What each run's stubs state: the replay's verdict, the session's gap rows
# (unset: no gap file published), whether its target row observed the fatal,
# and the occurrence that row is at -- the claim's anchor (iteration 0 of the
# handler) or another occurrence of the same site (iteration 1).
confirm_stub_verdict=ADMITTED
confirm_stub_gaps=""
confirm_stub_fatal=true
confirm_stub_target_iteration=0
confirm_stub_task_status=0
confirm_stub_realized=false
# The recording's measured peak resident memory, in MB (none: unmeasured).
confirm_recorded_rss=""
confirm_anchor='hdfs/dn0#epoch0/region/REGION.7c569c3f/ctx:Root:XCEIVER#1/idx:<a.Handler: void handle()>@0'
# The decision's JVM, on the built jar: reset_config clears java_bin and
# graphchecker_jar, which are workflow keys.
confirm_java=("${test_java}" -cp "${default_graphchecker_jar}")
confirm_stub_main() {
  local out=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --output) out=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  if [[ "${confirm_stub_task_status}" -ne 0 ]]; then
    echo "CONFIRM refused: the claim moves a cell nobody minted" >&2
    return "${confirm_stub_task_status}"
  fi
  if [[ "${confirm_stub_realized}" == true ]]; then
    printf '%s\n' '{"schemaVersion":1,"kind":"CONFIRMATION","confirmed":true,"reason":"the selected session S.sel is itself the run","sessionId":"S.sel"}' \
      >"${out}/realized.json"
    return 0
  fi
  printf '%s\n' '{"schemaVersion":1,"kind":"FOCUSED_TASK","taskId":"CONFIRM","obligationId":"CONFIRM","flip":null,"schedulePrefix":{"sessionId":"S.sel","events":10,"rest":3,"of":13,"cutAtFocus":true}}' \
    >"${out}/focused_task.jsonl"
  printf '%s\n' '{"kind":"ANCHOR","occurrence":"OCC.anchor","seq":40}' \
    >"${out}/expected_edges.jsonl"
}
confirm_stub_replay() {
  local worker=$3 sessions=$4
  # What the replay JVM is charged.
  printf '%s\n' "$6" >"${confirm_root}/replay-ran"
  mkdir -p "${sessions}/CONFIRM-1"
  jq -n -c --arg v "${confirm_stub_verdict}" '{schemaVersion: 1,
    kind: "OBLIGATION_RESULT", obligationId: "CONFIRM", verdict: $v,
    sessionId: "CONFIRM-1", detail: "stub"}' \
    >"${worker}/obligation_result.jsonl"
  [[ -z "${confirm_stub_gaps+set}" ]] \
    || printf '%s' "${confirm_stub_gaps}" >"${sessions}/CONFIRM-1/gaps.jsonl"
  # The occurrence as its four parts, exactly as RowCodec writes a target.
  jq -n -c --argjson fatal "${confirm_stub_fatal}" \
    --argjson iteration "${confirm_stub_target_iteration}" \
    '{sessionId: "CONFIRM-1", seq: 40,
      occurrence: {node: "hdfs/dn0#epoch0", regionId: "REGION.7c569c3f",
        context: {form: "ROOT", role: "XCEIVER", windowIndex: 1},
        index: [{callSite: "<a.Handler: void handle()>",
          iteration: $iteration}]},
      anchorSiteId: "T#u1#1", phiTerm: "EXPR.phi", observedFatal: $fatal,
      reachedAnchor: true}' >"${sessions}/CONFIRM-1/targets.jsonl"
}
run_confirm() {
  local claim=$1
  rm -rf -- "${campaign_final}/confirm" "${campaign_final}/confirm.json"
  jq -n --arg claim "${claim}" \
    '{solver: {campaignClaim: {claim: $claim}}}' >"${composition_manifest}"
  jq -n --arg anchor "${confirm_anchor}" '{anchor: $anchor,
    claim: {kind: "MARKER_FLIPPED", valuationOrdinal: 1,
      movedRoots: {"ROOT.M": "true"}},
    valuations: [{ordinal: 0, selectedPathId: "P.recorded"},
      {ordinal: 1, selectedPathId: "P.sel", selectedSessionId: "S.sel",
       selectedArms: [{selector: "message_arm__1__b2"},
         {selector: "message_arm__1__a1"}],
       assignment: {"ROOT.M": "true"}}]}' >"${campaign_final}/claim.json"
  (
    run_java_main() {
      case " $* " in
        *" --sessions "*) "${confirm_java[@]}" "$@" ;;
        *) confirm_stub_main "$@" ;;
      esac
    }
    campaign_obligation_replay() { confirm_stub_replay "$@"; }
    obligation_memory_mb=2500
    campaign_recorded_workload_rss_mb=${confirm_recorded_rss}
    campaign_confirm "${confirm_iteration}"
  ) >"${confirm_root}/confirm-stage.log" 2>&1 \
    || fail "the CONFIRM stage failed the campaign on claim=${claim}: \
$(cat "${confirm_root}/confirm-stage.log")"
}
confirm_says() {
  jq -e --argjson confirmed "$1" --arg reason "$2" \
    '.kind == "CONFIRMATION" and .confirmed == $confirmed
     and (.reason | contains($reason))' "${campaign_final}/confirm.json" \
    >/dev/null \
    || fail "$3: $(cat "${campaign_final}/confirm.json")"
}
reset_config
# Only a SAT_CANDIDATE is confirmed: any other claim has nothing to confirm.
run_confirm INCONCLUSIVE_PARTIAL
[[ ! -e "${campaign_final}/confirm.json" && ! -e "${campaign_final}/confirm" ]] \
  || fail "a claim that is not SAT_CANDIDATE was confirmed"
grep -q 'nothing to confirm' "${confirm_root}/confirm-stage.log" \
  || fail "the stage did not say why it ran nothing"
# The rule, both conditions holding.  The replay is charged as the seed's:
# the recording's measured peak times the replay factor, above one
# obligation's replay here.
confirm_recorded_rss=3000
run_confirm SAT_CANDIDATE
confirm_says true "the claim's anchor observed the fatal" \
  "a clean replay was not confirmed"
[[ "$(cat "${confirm_root}/replay-ran")" == 21000 ]] \
  || fail "the CONFIRM replay was charged $(cat "${confirm_root}/replay-ran") \
MB, not seven times the recording's 3000 MB peak"
confirm_recorded_rss=""
[[ $(jq -r '.sessionId' "${campaign_final}/confirm.json") == CONFIRM-1 ]] \
  || fail "the confirmation does not name the session that answered"
[[ -s "${campaign_final}/confirm/worker/focused_task.jsonl" \
    && -s "${campaign_final}/confirm/worker/expected_edges.jsonl" ]] \
  || fail "the confirmation replay was not handed the focus row and the edges"
# The order is how the replay reproduces the session, not what the claim
# says: a divergence before the anchor's cut (prefix of 10 events) or past it
# stays the diagnostic it is, and the edges and the fatal decide.
confirm_stub_gaps='{"sessionId":"CONFIRM-1","kind":"SCHEDULE_DIVERGED","cls":"DIAGNOSTIC","subject":"schedule#3","detail":"the run took RECV b, the prefix names SEND a"}'
run_confirm SAT_CANDIDATE
confirm_says true "every edge" \
  "a divergence of the order was held against a claim whose edges and fatal held"
confirm_stub_gaps='{"sessionId":"CONFIRM-1","kind":"SCHEDULE_DIVERGED","cls":"DIAGNOSTIC","subject":"schedule#12","detail":"past the cut"}
{"sessionId":"CONFIRM-1","kind":"SCHEDULE_DIVERGED","cls":"DIAGNOSTIC","subject":"schedule-rest#2","detail":"the rest gave up"}'
run_confirm SAT_CANDIDATE
confirm_says true "every edge" "a divergence past the anchor's cut was held against the claim"
# (a) An edge the model chose that the run did not take.
confirm_stub_gaps='{"sessionId":"CONFIRM-1","kind":"CONFIRM_MISMATCH","cls":"DIAGNOSTIC","subject":"WIRE e1","detail":"WIRE e1: the model chose producer p1, the run paired p2"}'
rm -f -- "${confirm_iteration}/refuted_claims.jsonl"
run_confirm SAT_CANDIDATE
confirm_says false "the model chose producer p1, the run paired p2" \
  "a mismatched edge was confirmed"
# A claim the replay ran and disagreed with is refuted: its model -- the
# finding kind, the path, the arms, the valuation, the moved roots -- and
# the reason, one row every later composition of the iteration excludes
# (compose.Refutations).
jq -e -s 'length == 1 and (.[0] | .kind == "REFUTED_CLAIM"
  and .model.pathId == "P.sel" and .model.arms == ["message_arm__1__a1",
    "message_arm__1__b2"] and .model.assignment == {"ROOT.M": "true"}
  and .model.moved == {"ROOT.M": "true"}
  and (.reason | contains("the run paired p2")))' \
  "${confirm_iteration}/refuted_claims.jsonl" >/dev/null \
  || fail "the refuted claim's model is not its row: \
$(cat "${confirm_iteration}/refuted_claims.jsonl" 2>&1)"
confirm_stub_gaps=""
# A session that published no gap file answers nothing about the edges --
# nor about the model, which is not refuted.
unset confirm_stub_gaps
run_confirm SAT_CANDIDATE
confirm_says false "published no readable" \
  "a session with no gap file was confirmed"
[[ "$(grep -c '' "${confirm_iteration}/refuted_claims.jsonl")" -eq 1 ]] \
  || fail "a confirmation that ran nothing refuted the model"
confirm_stub_gaps=""
# (b) The fatal not observed at the anchor.
confirm_stub_fatal=false
run_confirm SAT_CANDIDATE
confirm_says false "observed the fatal" "a healthy anchor was confirmed"
confirm_stub_fatal=true
# ... and observed at another occurrence of the target site is not the
# claim's anchor observing it.
confirm_stub_target_iteration=1
run_confirm SAT_CANDIDATE
confirm_says false "1 row(s) at other occurrences did" \
  "a fatal at another occurrence of the site confirmed the claim's anchor"
confirm_stub_target_iteration=0
# A replay whose roots were not planted, or whose prefix was abandoned,
# states NOT_ADMITTED, and that is the reason.
confirm_stub_verdict=NOT_ADMITTED
run_confirm SAT_CANDIDATE
confirm_says false "was NOT_ADMITTED: stub" "an unadmitted replay was confirmed"
confirm_stub_verdict=ADMITTED
# A selected session that already took every edge the model chose, with the
# moved roots at the model's values, and observed the fatal IS the run that
# confirms: published as ConfirmMain states it, and nothing is replayed.
confirm_stub_realized=true
rm -f -- "${confirm_root}/replay-ran"
run_confirm SAT_CANDIDATE
confirm_says true "is itself the run" "a realized claim was not confirmed"
[[ $(jq -r '.sessionId' "${campaign_final}/confirm.json") == S.sel ]] \
  || fail "the realized confirmation does not name the session that ran it"
[[ ! -e "${confirm_root}/replay-ran" ]] \
  || fail "a claim the selected session already realized was replayed"
confirm_stub_realized=false
# A confirmation nothing can run is refused by name, and the claim is
# unconfirmed for that reason -- the campaign goes on to EMIT.
confirm_stub_task_status=1
run_confirm SAT_CANDIDATE
confirm_says false "CONFIRM refused: the claim moves a cell nobody minted" \
  "a refused confirmation task did not name its reason"
confirm_stub_task_status=0
# The exploration's witness was confirmed as it was accepted: the same model,
# composed again, takes that confirmation and is not replayed.
campaign_witness_attempt="${confirm_root}/witness-attempt"
mkdir -p "${campaign_witness_attempt}"
cp -- "${campaign_final}/claim.json" "${campaign_witness_attempt}/claim.json"
jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: true,
  reason: "at the witness", sessionId: "W-1"}' \
  >"${campaign_witness_attempt}/confirm.json"
rm -f -- "${confirm_root}/replay-ran"
run_confirm SAT_CANDIDATE
confirm_says true "at the witness" "the witness's confirmation was not taken"
[[ ! -e "${confirm_root}/replay-ran" ]] \
  || fail "the model the exploration confirmed was replayed again"
campaign_witness_attempt=""
unset -f confirm_stub_main confirm_stub_replay run_confirm confirm_says
unset confirm_anchor confirm_stub_target_iteration confirm_java

# NEXT-CLAIM: a refuted SAT_CANDIDATE does not end the campaign while its
# budget has room for a composition and a confirmation (two
# replay_timeout_s): its artifacts move to final/refuted/NNNN/ and the next
# claim is composed.  Not when the claim was confirmed, not when the
# composition repeated a model already refuted, not past the budget.
next_root="${test_tmp}/next-claim"
next_iteration="${next_root}/iteration-0000"
campaign_final="${next_root}/final"
composition_manifest="${campaign_final}/candidate_composition_manifest.json"
next_claim() {
  mkdir -p "${campaign_final}/confirm" "${next_iteration}"
  jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE"}}}' \
    >"${composition_manifest}"
  : >"${campaign_final}/candidate.smt2"
  jq -n '{claim: {valuationOrdinal: 0}, valuations: [{ordinal: 0,
    selectedPathId: "P", selectedArms: [{selector: "m__0__a"}],
    assignment: {}}]}' >"${campaign_final}/claim.json"
  jq -n --argjson confirmed "$1" '{confirmed: $confirmed,
    refutes: ($confirmed | not), reason: "r"}' \
    >"${campaign_final}/confirm.json"
  campaign_claim_model "${campaign_final}/claim.json" \
    | jq -c '{model: .}' >"${next_iteration}/refuted_claims.jsonl"
}
reset_config
campaign_budget_s=100
campaign_reserve_s=20
campaign_started_s=${SECONDS}
next_claim true
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a confirmed claim was followed by another"
next_claim false
campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a refuted claim with room in the budget was not followed"
[[ -s "${campaign_final}/refuted/0000/claim.json" \
    && -d "${campaign_final}/refuted/0000/confirm" \
    && ! -e "${campaign_final}/candidate.smt2" ]] \
  || fail "the refuted claim's artifacts did not move out of final/"
next_claim false
campaign_claim_model "${campaign_final}/claim.json" | jq -c '{model: .}' \
  >>"${next_iteration}/refuted_claims.jsonl"
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a composition that repeated a refuted model was followed"
next_claim false
campaign_reserve_s=120
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a claim past the campaign budget was followed"
[[ -s "${campaign_final}/claim.json" \
    && ! -e "${campaign_final}/refuted/0001" ]] \
  || fail "a claim that ends the campaign left final/"
unset -f next_claim
reset_config

# BUDGET-1: a budget its reserve takes whole is refused by name.
budget_validate() (
  stop_after_config ""
  campaign_budget_s=600
  campaign_reserve_s=600
  validate_config
)
run_capturing_status budget_validate >/dev/null \
  2>"${test_tmp}/budget-validate.err"
[[ "${status}" -ne 0 ]] \
  && grep -q 'campaign_budget_s (600) must exceed its reserve' \
    "${test_tmp}/budget-validate.err" \
  || fail "a budget no larger than its reserve was accepted: \
$(cat "${test_tmp}/budget-validate.err")"
unset -f budget_validate

# EMIT-CONFIRM: an unconfirmed SAT claim is published as SAT_UNCONFIRMED,
# not accepted, with the confirmation and its reason in the result, and
# the campaign exits 2 as for any claim that is not an accepted candidate.
emit_fixture
jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: false,
  reason: "the run took an edge the model did not choose: WIRE e1",
  sessionId: "CONFIRM-2"}' >"${campaign_final}/confirm.json"
run_emit
[[ "${emit_status}" -eq 2 ]] \
  || fail "an unconfirmed SAT claim exited ${emit_status}, not 2: \
$(<"${emit_root}/emit.log")"
jq -e '.claim == "SAT_UNCONFIRMED" and .accepted == false
  and .confirmation.confirmed == false
  and .confirmation.sessionId == "CONFIRM-2"
  and (.claimReason | contains("WIRE e1"))
  and (.whyNotAccepted | startswith("SAT_UNCONFIRMED: "))
  and .findingKind == "MARKER_FLIPPED"' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the unconfirmed claim was not downgraded in the result: \
$(jq -c '{claim, accepted, confirmation, whyNotAccepted}' \
    "${campaign_final}/result.json")"
grep -q 'no accepted candidate: claim=SAT_UNCONFIRMED' "${emit_root}/emit.log" \
  || fail "EMIT did not name the unconfirmed claim: $(<"${emit_root}/emit.log")"
# A SAT claim with no confirmation at all is a malformed run, not a pass.
emit_fixture
rm -f -- "${campaign_final}/confirm.json"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a SAT claim with no confirmation was published as accepted"
# A claim that is not SAT_CANDIDATE needs none and carries null.
emit_fixture_undecided_roots
rm -f -- "${campaign_final}/confirm.json"
run_emit
jq -e '.claim == "INCONCLUSIVE_PARTIAL" and .confirmation == null' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "a claim that was never confirmed does not carry null: \
$(jq -c '{claim, confirmation}' "${campaign_final}/result.json")"

# MEMORY-1: `obligation_memory_mb` is a declared workflow key, and a
# campaign that states none -- or a nonsense one -- is refused by name.
[[ "$(grep -c 'CAUSYNTH_OBLIGATION_MEMORY_MB' "${repo}/run_engine.sh")" \
    -eq 1 ]] \
  || fail "CAUSYNTH_OBLIGATION_MEMORY_MB is not declared once, in the table"
known_config_key obligation_memory_mb \
  || fail "obligation_memory_mb is not loadable from a workflow file"
memory_dir="${test_tmp}/memory"
mkdir -p "${memory_dir}"
memory_validate() (
  stop_after_config ""
  obligation_memory_mb=$1
  validate_config
)
for bad in "" "0" "2g" "-1"; do
  run_capturing_status memory_validate "${bad}" \
    >/dev/null 2>"${memory_dir}/validate.err"
  [[ "${status}" -ne 0 ]] \
    || fail "validate accepted obligation_memory_mb='${bad}'"
  grep -q 'obligation_memory_mb must be' "${memory_dir}/validate.err" \
    || fail "the refusal does not name obligation_memory_mb: \
$(cat "${memory_dir}/validate.err")"
done
for case_config in "${repo}"/experiments/hadoop/hdfs-*/workflow.properties; do
  grep -q '^obligation_memory_mb=[1-9][0-9]*$' "${case_config}" \
    || fail "${case_config} states no obligation_memory_mb"
done

# MEMORY-2: the gate's decision.  A start is charged in full for the ramp
# window, whichever campaign made it; after it only MemAvailable counts; a
# local host and the same host named over ssh are one ledger; a lock a dead
# campaign left behind is broken.
reset_config
campaign_host_gate_root="${memory_dir}/hosts"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
memory_available=20000
campaign_host_available_mb() { echo "${memory_available}"; }
obligation_memory_mb=6000
campaign_host_total_mb() { echo 10000; }
campaign_host_max_used_pct=70
campaign_host_ramp_s=60
campaign_host_poll_s=0
# Every start states its need and its ramp: an obligation's, here.
memory_start=(6000 60)
campaign_host_try_start lift14 "${memory_start[@]}" \
  || fail "20000 MB free did not admit a 6000 MB obligation"
campaign_host_try_start lift14 "${memory_start[@]}" \
  || fail "20000 MB less one 6000 MB start did not admit a second"
run_capturing_status campaign_host_try_start lift14 "${memory_start[@]}"
[[ "${status}" -eq 1 ]] \
  || fail "two starts charged 12000 MB, and a third was admitted over the \
3000 MB reserve"
[[ "${campaign_host_wait_reason}" == *"12000 MB charged"* ]] \
  || fail "the wait does not say what is charged: ${campaign_host_wait_reason}"
# Another campaign, the same host: the same ledger refuses it too.
( run_capturing_status campaign_host_try_start lift14 "${memory_start[@]}"
  exit "${status}" ) \
  && fail "another campaign's start ignored the charges on the host"
# The window passes: the JVMs are in MemAvailable now, and the charge lapses.
sed -i 's/^[0-9]* /1 /' "${campaign_host_gate_root}/lift14/starts"
campaign_host_try_start lift14 "${memory_start[@]}" \
  || fail "starts older than the ramp window are still charged"
# The head is one ledger under both of its names.
campaign_host_try_start localhost "${memory_start[@]}" \
  || fail "the head's first start was refused"
[[ -s "${campaign_host_gate_root}/gate-head/starts" \
    && ! -e "${campaign_host_gate_root}/localhost" ]] \
  || fail "a local start is not charged to the head's own name"
# A stale lock: the next try breaks it and the one after starts.
mkdir "${campaign_host_gate_root}/lift15"
mkdir "${campaign_host_gate_root}/lift15/lock"
touch -d '10 minutes ago' "${campaign_host_gate_root}/lift15/lock"
run_capturing_status campaign_host_try_start lift15 "${memory_start[@]}"
[[ "${status}" -eq 3 && ! -e "${campaign_host_gate_root}/lift15/lock" ]] \
  || fail "a lock a dead campaign left was not broken"
campaign_host_try_start lift15 "${memory_start[@]}" \
  || fail "the host stayed locked"
# A lock held for the instant another start is charged is waited out, not
# answered as no room (campaign_host_try_charge).
mkdir "${campaign_host_gate_root}/lift15/lock"
( sleep 1; rmdir "${campaign_host_gate_root}/lift15/lock" ) &
campaign_host_try_charge lift15 "${memory_start[@]}"
wait
[[ "${status}" -eq 0 ]] || fail "a held lock was answered as ${status}"
# A host whose memory stays unreadable past the ssh patience is the
# waiter's named failure; within it the start waits (sshd refuses
# connections under a round's burst).
campaign_host_available_mb() { return 1; }
real_campaign_log=$(declare -f campaign_log)
campaign_log() { printf '%s\n' "$*" >>"${memory_dir}/gate.log"; }
campaign_host_poll_s=0
campaign_ssh_patience_s=1
run_capturing_status campaign_await_host_memory lift13 "${memory_start[@]}"
[[ "${status}" -eq 2 ]] \
  || fail "an unreadable host admitted an obligation"
grep -q 'the memory of host lift13 could not be read for 1s' \
    "${memory_dir}/gate.log" \
  || fail "the unreadable host is not named: $(cat "${memory_dir}/gate.log")"
unset -f hostname campaign_host_available_mb campaign_host_total_mb
eval "${real_campaign_log}"
reset_config

# MEMORY-3: a start states its need and its own ramp, and counts while that
# ramp lasts; a head's start is released when its command returns, so a
# head's JVMs, one after another, are never charged twice.
campaign_host_gate_root="${memory_dir}/ramps"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
campaign_host_available_mb() { echo 20000; }
campaign_host_total_mb() { echo 10000; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
mkdir -p "${campaign_host_gate_root}/lift14"
memory_now=$(date +%s)
printf '%s 8000 60 lapsed\n%s 8000 600 ramping\n' \
  "$((memory_now - 100))" "$((memory_now - 100))" \
  >"${campaign_host_gate_root}/lift14/starts"
campaign_host_try_start lift14 9000 300 \
  || fail "a row past its own 60 s ramp is still charged"
read -r _ memory_mb memory_ramp memory_id \
  < <(grep -v -e lapsed -e ramping "${campaign_host_gate_root}/lift14/starts")
[[ "${memory_mb} ${memory_ramp} ${memory_id}" \
    == "9000 300 ${campaign_host_charge_id}" ]] \
  || fail "a start's row does not state its need, its ramp and its id: \
$(cat "${campaign_host_gate_root}/lift14/starts")"
run_capturing_status campaign_host_try_start lift14 1 300
[[ "${status}" -eq 1 ]] \
  || fail "a row inside its own 600 s ramp is not charged"
campaign_host_release lift14 "${memory_id}"
! grep -q -- "${memory_id}" "${campaign_host_gate_root}/lift14/starts" \
  || fail "a released start is still charged"
campaign_head_charging=1
campaign_head_charged 7000 120 bash -c "grep -c ' 7000 120 ' \
  '${campaign_host_gate_root}/gate-head/starts' >'${memory_dir}/during'" \
  || fail "a head's charged command did not run"
[[ "$(cat "${memory_dir}/during")" -eq 1 \
    && ! -s "${campaign_host_gate_root}/gate-head/starts" ]] \
  || fail "a head's start was not charged while it ran and released after"
run_capturing_status campaign_head_charged 7000 120 false
[[ "${status}" -eq 1 ]] || fail "a charged command's exit status was lost"
# A head that waited for room says so on stderr, never in the stdout that is
# the charged command's artifact.
real_try_start=$(declare -f campaign_host_try_start)
campaign_host_try_start() {
  if [[ ! -e "${memory_dir}/tried" ]]; then
    : >"${memory_dir}/tried"
    campaign_host_wait_reason="no room"
    return 1
  fi
  campaign_host_charge_id=waited
}
campaign_host_poll_s=0
[[ "$(campaign_head_charged 7000 120 printf artifact 2>/dev/null)" \
    == artifact ]] || fail "a head's wait for memory reached its stdout"
eval "${real_try_start}"
campaign_head_charging=0
campaign_head_charged 999999 120 true \
  || fail "a start outside a head waited for the ledger"
unset -f hostname campaign_host_available_mb campaign_host_total_mb
reset_config

# MEMORY-4: HEAD ROOM.  A head's host keeps room for the head's next engine
# JVM against every other start -- what its planner or composer starts at
# (campaign_head_need_mb), not the case's engine heap: an obligation counts
# the largest idle, fresh reservation of the host as used, a head's own
# start counts none, one of its JVMs running (busy) or a reservation gone
# stale frees it, and the head gives it up when it exits.
campaign_host_gate_root="${memory_dir}/head-room"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
campaign_host_available_mb() { echo 16000; }
campaign_host_total_mb() { echo 10000; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
engine_memory_mb=12000
(
  campaign_head_charging=1
  campaign_head_reserve
  [[ "$(cat "${campaign_host_gate_root}/gate-head/heads/"*)" == 8192 ]] \
    || fail "the head reserved no room on its host, or the engine heap's: \
$(cat "${campaign_host_gate_root}/gate-head/heads/"*)"
  run_capturing_status campaign_host_try_start localhost 6000 60
  [[ "${status}" -eq 1 && "${campaign_host_wait_reason}" == *"8192 MB held \
for a head"* ]] || fail "an obligation took the room a head reserved: \
${campaign_host_wait_reason}"
  campaign_host_try_start lift14 6000 60 \
    || fail "a head's room was held on another host"
  campaign_head_charged 9000 120 bash -c "ls '${campaign_host_gate_root}/\
gate-head/heads/' >'${memory_dir}/head-busy'" \
    || fail "the head's own start waited for its own room"
  grep -q '\.busy\.' "${memory_dir}/head-busy" \
    || fail "the head's room is held while its own JVM runs"
  touch -d '20 minutes ago' "${campaign_host_gate_root}/gate-head/heads/"*
  campaign_host_try_start localhost 6000 60 \
    || fail "a stale reservation still holds room"
  campaign_head_heartbeat
  ( campaign_head_unreserve )
  [[ -n "$(ls "${campaign_host_gate_root}/gate-head/heads/")" ]] \
    || fail "a subshell of the head gave up the head's room"
) || exit 1
[[ -z "$(ls "${campaign_host_gate_root}/gate-head/heads/")" ]] \
  || fail "the head kept its room after it exited"
unset -f hostname campaign_host_available_mb campaign_host_total_mb

# HEAD-PLACE: every heavy step of a head -- an engine JVM of any stage, the
# seed or the CONFIRM replay, a native run of REPRODUCE -- goes wherever
# there is room: the head's own host when it fits, else the pool's host
# with the most room under the ceiling (MemAvailable less the 3000 MB
# reserve of a 10000 MB host), charged there while it runs and released
# after, and run there: --run-placed, in the head's working directory with
# the head's exported variables, a program or a run_engine.sh function with
# its arguments, its standard output passed on as its own.  Per row: the
# head's, lift14's and lift15's MemAvailable, the step's need, and where it
# runs.
place_dir="${memory_dir}/place"
! grep -q 'campaign_head_placing' "${repo}/run_engine.sh" \
  || fail "a head step is placed by a second rule"
while read -r place_own place_14 place_15 place_need place_expected; do
  rm -rf -- "${place_dir}"
  mkdir -p "${place_dir}"
  (
    campaign_host_gate_root="${place_dir}/hosts"
    campaign_root="${place_dir}"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_worker_hosts="gate-head lift14 lift15"
    campaign_host_total_mb() { echo 10000; }
    campaign_host_available_mb() {
      case "$1" in
        lift14) echo "${place_14}" ;;
        lift15) echo "${place_15}" ;;
        *) echo "${place_own}" ;;
      esac
    }
    campaign_host_max_used_pct=70
    campaign_host_poll_s=0
    campaign_head_charging=1
    # The peer: run_engine.sh --run-placed, as the remote worker script
    # runs it, with nothing of the head's environment but what it forwards.
    campaign_dispatch_remote() {
      local host=$1 dir=$2
      shift 3
      [[ "$1" == --run-placed ]] || fail "a head step was placed as $1"
      shift
      printf '%s\n' "${host}" >"${place_dir}/placed-on"
      (
        unset CAUSYNTH_PLACE_PROBE
        campaign_peer_enter() { campaign_peer_args=("$@"); }
        do_run_placed "$@"
      ) >"${dir}/stdout.log" 2>"${dir}/stderr.log"
    }
    # The step: where it runs from, its argument, the head's environment,
    # and how many starts of its need the ledger holds while it runs.
    place_probe() {
      printf '%s %s %s %s' "${PWD##*/}" "$1" "${CAUSYNTH_PLACE_PROBE:-}" \
        "$(cat "${campaign_host_gate_root}"/*/starts 2>/dev/null \
          | grep -c " ${place_need} 120 ")"
    }
    export CAUSYNTH_PLACE_PROBE=exported
    cd "${place_dir}"
    [[ "$(campaign_head_charged "${place_need}" 120 place_probe argument)" \
        == "place argument exported 1" ]] \
      || fail "a step of ${place_need} MB did not run from the head's \
directory with its arguments and the head's environment, charged once: \
$(campaign_head_charged "${place_need}" 120 place_probe argument)"
    [[ "$(campaign_head_charged "${place_need}" 120 \
        bash -c 'printf "%s" "${CAUSYNTH_PLACE_PROBE}"')" == exported ]] \
      || fail "a placed program did not see the head's environment"
    place_ran=gate-head
    [[ ! -e "${place_dir}/placed-on" ]] \
      || place_ran=$(cat "${place_dir}/placed-on")
    [[ "${place_ran}" == "${place_expected}" ]] \
      || fail "a step of ${place_need} MB with ${place_own}/${place_14}/\
${place_15} MB available ran on ${place_ran}, not ${place_expected}"
    [[ -z "$(cat "${campaign_host_gate_root}"/*/starts 2>/dev/null)" ]] \
      || fail "a placed step's charge outlived it"
  ) || exit 1
done <<'EOF'
4000 7000 9000 5000 lift15
20000 7000 9000 5000 gate-head
4000 9000 8500 5000 lift14
4000 7000 7000 2000 lift14
EOF

# ENGINE-HEAP: an engine JVM starts at what its main measurably needs, charged
# that, and only a run that outgrows it -- the JVM's exit 3 under
# -XX:+ExitOnOutOfMemoryError -- runs once more at the engine heap, saying
# so; the reader of its standard output sees the finished run's alone, and
# later starts of that main go straight to the engine heap.  A main with no
# measured need runs at the engine heap.  Every run, at the engine heap too,
# ends at its first out-of-heap error.
engine_test=${test_tmp}/engine-heap
mkdir -p "${engine_test}"
cat >"${engine_test}/java" <<'EOF'
#!/usr/bin/env bash
oom=n
[[ "$1" == -XX:+ExitOnOutOfMemoryError ]] && oom=y
echo "heap=${GRAPH_CHECKER_ENGINE_MEMORY_MB} oom=${oom}" >>"${ENGINE_TEST_LOG}"
if [[ "${oom}" == y && "${GRAPH_CHECKER_ENGINE_MEMORY_MB}" -lt 4000 ]]; then
  echo "half of an artifact"
  exit 3
fi
echo whole
EOF
chmod +x "${engine_test}/java"
(
  export ENGINE_TEST_LOG=${engine_test}/log
  java_bin=${engine_test}/java
  engine_memory_mb=8000
  campaign_head_charging=0
  campaign_engine_need_mb() { [[ "$1" != x.Grows ]] || echo 2000; }
  engine_java -Dk=v -cp jar x.Grows a b >"${engine_test}/out" 2>"${engine_test}/err" \
    || fail "an engine JVM that outgrew its need failed"
  [[ "$(cat "${engine_test}/out")" == whole ]] \
    || fail "the outgrown run's output reached its reader: $(cat "${engine_test}/out")"
  grep -q 'Grows ran out of its 2000 MB heap; run again at 8000 MB' \
    "${engine_test}/err" || fail "an engine JVM outgrew its need silently"
  engine_java -cp jar x.Grows >/dev/null
  engine_java -cp jar x.Other >/dev/null
  engine_need_mb=6000 engine_java -cp jar x.Other >/dev/null
  [[ "$(tr '\n' ' ' <"${engine_test}/log")" == "heap=2000 oom=y heap=8000 oom=y \
heap=8000 oom=y heap=8000 oom=y heap=6000 oom=y " ]] \
    || fail "engine JVMs did not start at their needs: \
$(tr '\n' ' ' <"${engine_test}/log")"
)
reset_config

# FANOUT-1: fanout.sh charges each job to the same ledger with the need its
# line states, releases it when the job returns, and a restart over the same
# log directory skips every job that returned.
fanout_dir="${test_tmp}/fanout"
mkdir -p "${fanout_dir}/logs"
printf '%s\n' "echo zero >${fanout_dir}/0.out" \
  "echo one >${fanout_dir}/1.out" \
  "NEED_MB=1 echo two >${fanout_dir}/2.out" >"${fanout_dir}/jobs"
echo 0 >"${fanout_dir}/logs/1.exit"
LIFTS=localhost CAUSYNTH_HOST_LEDGER="${fanout_dir}/ledger" JOB_MEMORY_MB=1 \
  bash "${repo}/tools/adhoc/fanout.sh" "${fanout_dir}/jobs" \
  "${fanout_dir}/logs" >"${fanout_dir}/fanout.out" 2>&1 \
  || fail "fanout failed: $(cat "${fanout_dir}/fanout.out")"
[[ -s "${fanout_dir}/0.out" && -s "${fanout_dir}/2.out" \
    && ! -e "${fanout_dir}/1.out" ]] \
  || fail "fanout did not resume: it ran $(ls "${fanout_dir}"/*.out)"
[[ "$(cat "${fanout_dir}/logs/0.exit" "${fanout_dir}/logs/2.exit")" \
    == $'0\n0' ]] \
  || fail "a returned job left no .exit"
grep -qE '^2 localhost exit=0 [0-9]+s$' "${fanout_dir}/fanout.out" \
  || fail "the finished-job line changed: $(cat "${fanout_dir}/fanout.out")"
! grep -q . "${fanout_dir}/ledger/$(command hostname -s)/starts" \
  || fail "a returned job is still charged: \
$(cat "${fanout_dir}/ledger/$(command hostname -s)/starts")"

# HEADS-1: a round's heads are chosen at launch from the hosts' room
# (tools/rounds/launch-round.sh, tools/lib/heads.sh heads_choose): the
# heaviest case first, each to the host with the most room among those that
# head the fewest cases, that host's room then less the case's need -- no
# host heads two before every host heads one, and a busy host is the last
# one chosen (round e1: two cases sat 30 min on a lift a stranger's JVM
# filled while three lifts had 28 GB free).  Per row: each host's room, each
# case's need, and the heads chosen in launch order.
# shellcheck source=../../../tools/lib/heads.sh
source "${repo}/tools/lib/heads.sh"
while IFS='|' read -r heads_rooms heads_needs heads_expected; do
  read -r -a heads_hosts <<<"${heads_rooms}"
  heads_chosen=$(tr ' :' '\n ' <<<"${heads_needs}" \
    | heads_choose "${heads_hosts[@]}" | paste -sd ' ' -)
  [[ "${heads_chosen}" == "${heads_expected}" ]] \
    || fail "rooms ${heads_rooms} and needs ${heads_needs} chose \
'${heads_chosen}', not '${heads_expected}'"
done <<'EOF'
lift06:20000 lift07:5000 lift08:18000|8192:a 16384:b 8192:c|b lift06 a lift08 c lift07
lift06:20000 lift07:9000|8192:a 8192:b 8192:c|a lift06 b lift07 c lift06
lift06:19000 lift07:-2000 lift08:20000 lift15:21000|16384:hdfs-11741 8192:hdfs-17960 8192:hdfs-17967-pathC|hdfs-11741 lift15 hdfs-17960 lift08 hdfs-17967-pathC lift06
EOF
[[ -z "$(heads_choose </dev/null)" ]] && ! heads_choose </dev/null \
  || fail "cases were headed with no host to head them"

# HEADS-2: launch-round.sh weighs a case's head by its engine heap; a sweep
# admits it for the room it reserves on its host, what its planner or
# composer starts at (campaign_head_need_mb), never more than that heap:
# a40's Solr heads asked fanout for 16 GB they never held and waited 90 min
# while one case's obligations filled the lifts.  Per row: the case's
# configuration, its weight and its head's room.
while IFS='|' read -r heads_config heads_heap heads_reserve; do
  [[ "$(case_engine_heap_mb "${heads_config}")" == "${heads_heap}" \
      && "$(case_head_reserve_mb "${heads_config}")" == "${heads_reserve}" ]] \
    || fail "${heads_config} weighs $(case_engine_heap_mb "${heads_config}") \
and reserves $(case_head_reserve_mb "${heads_config}")"
done <<'EOF'
engine_memory_mb=16384|16384|8192
engine_memory_mb=|8192|8192
engine_memory_mb=4096|4096|4096
EOF

# POOL-SLOTS: the obligation slots a sweep's cases share
# (campaign_pool_slots): on each host as many starts of the need as fit
# under its ceiling, at most its cores, summed; a host whose memory cannot
# be read adds none.  Per row: the need, and the slots of two 31583 MB,
# 48-core hosts and one unreadable.
(
  campaign_host_gate_root="${test_tmp}/pool-slots"
  campaign_host_max_used_pct=70
  campaign_host_total_mb() { return 1; }
  for host in lift12 lift13; do
    mkdir -p "${campaign_host_gate_root}/${host}"
    echo 31583 >"${campaign_host_gate_root}/${host}/total"
    echo 48 >"${campaign_host_gate_root}/${host}/cores"
  done
  while read -r slots_need slots_expected; do
    [[ "$(campaign_pool_slots "${slots_need}" lift12 lift13 lift14)" \
        == "${slots_expected}" ]] \
      || fail "a need of ${slots_need} MB found \
$(campaign_pool_slots "${slots_need}" lift12 lift13 lift14) slots"
  done <<'EOF'
6000 6
100 96
30000 0
EOF
)

# SWEEP-1: sweep.sh launches every case with its head's room as its need
# and the lifts' obligation slots for its obligation_memory_mb as its cap;
# a case whose configuration states no obligation_memory_mb launches no case.
sweep_dir="${test_tmp}/sweep"
mkdir -p "${sweep_dir}/snap/experiments/x/c" "${sweep_dir}/snap/experiments/lib" \
  "${sweep_dir}/snap/tools/rounds" "${sweep_dir}/out" \
  "${sweep_dir}/ledger/$(hostname -s)"
: >"${sweep_dir}/snap/experiments/x/c/case.sh"
printf '%s\n' '[[ "$3" == config ]] || exit 2' \
  'printf "obligation_memory_mb=6000\nengine_memory_mb=1\n"' \
  >"${sweep_dir}/snap/experiments/lib/run.sh"
printf 'echo "$2 ${CAUSYNTH_STREAM_MAX_IN_FLIGHT}" >%s/launched\n' \
  "${sweep_dir}" >"${sweep_dir}/snap/tools/rounds/launch-run.sh"
echo 31583 >"${sweep_dir}/ledger/$(hostname -s)/total"
echo 48 >"${sweep_dir}/ledger/$(hostname -s)/cores"
echo c-one >"${sweep_dir}/cases"
sweep_run() {
  LIFTS=localhost GC_OUT="${sweep_dir}/out" VM_IMAGE=vm \
    CAUSYNTH_HOST_LEDGER="${sweep_dir}/ledger" CAUSYNTH_HOST_MAX_USED_PCT=70 \
    bash "${repo}/tools/adhoc/sweep.sh" "${sweep_dir}/snap" "$1" \
    "${sweep_dir}/cases" >"${sweep_dir}/$1.out" 2>&1
}
sweep_run s1 || fail "the sweep failed: $(cat "${sweep_dir}/s1.out")"
[[ "$(cat "${sweep_dir}/launched")" == "c-one 3" ]] \
  && grep -q '^NEED_MB=1 .* CAUSYNTH_STREAM_MAX_IN_FLIGHT=3 ' \
    "${sweep_dir}/out/sweep-s1-jobs.txt" \
  || fail "the sweep's case did not launch with its head's room and the \
lifts' slots: $(cat "${sweep_dir}/launched" \
    "${sweep_dir}/out/sweep-s1-jobs.txt")"
echo nothing-here >"${sweep_dir}/cases"
! sweep_run s2 && grep -q 'nothing-here states no obligation_memory_mb' \
    "${sweep_dir}/s2.out" && [[ ! -s "${sweep_dir}/out/sweep-s2-jobs.txt" ]] \
  || fail "a case with no configuration was launched or not named: \
$(cat "${sweep_dir}/s2.out")"

# UNION-1: a batch's one recording weave (do_record) is woven with every
# target's skeletons merged by root -- one region per root, whichever
# authority each target rooted it under -- their lists united and the first
# target's words kept, and over every target's grown classes with one GROWN
# row per class.  Each target is aggregated on its view of it: its own
# selection at a root it plans, and another target's exception context as
# state.
union_dir="${test_tmp}/union"
causynth_static_root="${union_dir}/static"
causynth_output_dir="${union_dir}/out"
causynth_region_skeletons="${causynth_output_dir}/region_skeletons.jsonl.gz"
for target in a b; do
  mkdir -p "${causynth_static_root}/${target}/scope-classes/p"
  : >"${causynth_static_root}/${target}/scope-classes/p/${target^}.class"
  printf 'p.%s\tCALLEE\tm\t1\np.Shared\tFIELD\tf\t2\n' "${target^}" \
    >"${causynth_static_root}/${target}/scope-classes/GROWN"
done
printf '%s\n' \
  '{"regionId":"R1","rootMethod":"r1","selection":"EXCEPTION_CONTEXT","methods":["m1","m2"]}' \
  '{"regionId":"R2","rootMethod":"r2","selection":"STATE_CONTEXT","methods":["m3"]}' \
  '{"regionId":"R4","rootMethod":"r4","selection":"EXCEPTION_CONTEXT","methods":["m6"]}' \
  | gzip -c >"${causynth_static_root}/a/region_skeletons.jsonl.gz"
printf '%s\n' \
  '{"regionId":"R1","rootMethod":"r1","selection":"STATE_CONTEXT","methods":["m2","m4"]}' \
  '{"regionId":"R3","rootMethod":"r2","selection":"EXCEPTION_CONTEXT","methods":["m5"]}' \
  | gzip -c >"${causynth_static_root}/b/region_skeletons.jsonl.gz"
campaign_union_static a b
[[ "$(zcat "${causynth_region_skeletons}" | jq -c .)" == \
    '{"regionId":"R1","rootMethod":"r1","selection":"EXCEPTION_CONTEXT","methods":["m1","m2","m4"]}
{"regionId":"R2","rootMethod":"r2","selection":"STATE_CONTEXT","methods":["m3","m5"]}
{"regionId":"R4","rootMethod":"r4","selection":"EXCEPTION_CONTEXT","methods":["m6"]}' ]] \
  || fail "the union skeletons: $(zcat "${causynth_region_skeletons}")"
for target in a b; do
  campaign_region_view "${causynth_static_root}/${target}" | zcat \
    | jq -r .selection | paste -sd ' ' - >"${union_dir}/${target}.view"
done
[[ "$(cat "${union_dir}/a.view")" == \
    "EXCEPTION_CONTEXT STATE_CONTEXT EXCEPTION_CONTEXT" \
    && "$(cat "${union_dir}/b.view")" == \
    "STATE_CONTEXT EXCEPTION_CONTEXT STATE_CONTEXT" ]] \
  || fail "a target's view of the union: a $(cat "${union_dir}/a.view"), \
b $(cat "${union_dir}/b.view")"
[[ -e "${causynth_output_dir}/scope-classes/p/A.class" \
    && -e "${causynth_output_dir}/scope-classes/p/B.class" ]] \
  || fail "a target's grown classes are missing from the union"
[[ "$(cut -f1 "${causynth_output_dir}/scope-classes/GROWN")" == \
    $'p.A\np.Shared\np.B' ]] \
  || fail "the union GROWN: $(cat "${causynth_output_dir}/scope-classes/GROWN")"
reset_config

echo "run_engine campaign helper tests passed"
