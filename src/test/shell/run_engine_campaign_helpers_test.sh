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
  # The production layout: each epoch composes into its own final/ and the
  # campaign publishes the last one at ${campaign_root}/final.  The fixture
  # used to point campaign_final straight at the published directory, which
  # made the publish a no-op and hid the bug the checks below now pin.
  campaign_final="${emit_iteration}/final"
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
      symbolicVariableModels: [],
      valuations: [{values: [false], status: "unsat"},
                   {values: [true], status: "sat"}],
      campaignClaim: {schemaVersion: 1, kind: "CAMPAIGN_CLAIM",
        claim: "SAT_CANDIDATE",
        claimReason: "a valuation satisfies the target predicate inside the recorded model and a symbolic root flips it",
        blockers: [], blockerCount: 0, whyNotAccepted: "",
        findingKind: "MARKER_FLIPPED", polarityDecides: true,
        valuationOrdinal: 1,
        movedRoots: {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"},
        rootSpace: {reachability: "REACHABLE",
                    faultSensitive: true}}}}' \
    >"${composition_manifest}"
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
  printf '%s\n' \
    '{"taskId":"task-target","published":true}' \
    >"${emit_iteration}/seed-result/concolic_region_results.jsonl"
  : >"${emit_iteration}/campaign_gaps.jsonl"
  jq -n '{schemaVersion: 1, kind: "CAMPAIGN_ITERATION_MANIFEST",
    iterationId: "iteration-0000", parentIterationId: "",
    externalWorkerCount: 1, topologyDelta: {rows: 0, divergences: 0},
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
      valuationOrdinal: 0, movedRoots: {},
      rootSpace: {reachability: "REACHABLE",
                  faultSensitive: true}}}' \
    "${composition_manifest}" >"${composition_manifest}.tmp"
  mv "${composition_manifest}.tmp" "${composition_manifest}"
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
  and .gapCount == 0
  and .telemetryCount >= 2' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its propagation provenance"
# EMIT-1: the epoch's artifacts are published at ${campaign_root}/final, which
# is the one path every later reader and the harness open.
[[ -s "${campaign_root}/final/result.json" ]] \
  || fail "an accepted epoch published no ${campaign_root}/final"
cmp -s "${campaign_final}/result.json" "${campaign_root}/final/result.json" \
  || fail "the published final is not this epoch's final"

# DECIDE-1: a campaign answers about one anchor -- the occurrence its case
# declares and the composer composed -- and the result names it.  Ranking
# several observed executions into a verdict is gone with the election.
jq -e '.targetOccurrence == "REGION.T#1"
  and (has("targetOccurrences") | not)' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not name the composed anchor: \
$(jq -c '.targetOccurrence' "${campaign_final}/result.json")"
# CLAIM-1: the whole policy decision, so no consumer has to open the solver
# report to find the claim this file was written from.
jq -e '.rootSpace.reachability == "REACHABLE"
  and (.rootSpace | has("faultSensitive"))' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result does not carry the claim root space: \
$(jq -c '.rootSpace' "${campaign_final}/result.json")"

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
  and (.gaps[0].class == "BLOCKING")' \
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
# EMIT-2: and a WITHHELD epoch publishes too.  campaign_emit leaves this shell
# with exit 3 on a blocking gap, so the epoch loop's own publish call never
# ran: lane17897h composed, solved and decided, then published nothing at
# ${campaign_root}/final and the harness read claim=MISSING for it.
[[ -s "${campaign_root}/final/result.json" ]] \
  || fail "a withheld epoch published no ${campaign_root}/final"
[[ $(jq -r '.claim' "${campaign_root}/final/result.json") \
    == $(jq -r '.claim' "${campaign_final}/result.json") ]] \
  || fail "the published final does not carry the withheld epoch's claim"
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
# annotated site the campaign answers about is the case's declaration.
emit_fixture
[[ "$(jq -r '.anchor' "${composition_manifest}")" == "REGION.T#1" ]] \
  || fail "the composition does not name its anchor"
[[ -s "${campaign_final}/candidate.smt2" ]] \
  || fail "the anchor's formula is not in the epoch's final directory"
[[ ! -e "${campaign_final}/targets" ]] \
  || fail "the composition fanned out over occurrences"

# PLAN-1: the schedule index says which members carry a target-reach goal, so
# the plan can name every observed occurrence of the annotated site.
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

# EXPLORE-2: a wave collects every obligation's verdict once the wave has
# settled, in a deterministic order, so the next wave sees a complete frontier
# rather than a partial one.  An obligation the solver could not decide is one
# of those verdicts, not the wave's death.
wave_root="${test_tmp}/wave"
mkdir -p "${wave_root}/obligations-0000/OBL.slow" \
  "${wave_root}/obligations-0000/OBL.fast"
printf '%s\n' \
  '{"schemaVersion":1,"kind":"OBLIGATION_RESULT","obligationId":"OBL.slow","verdict":"NOT_ADMITTED","sessionId":"","detail":"SOLVER_TIMEOUT"}' \
  >"${wave_root}/obligations-0000/OBL.slow/obligation_result.jsonl"
printf '%s\n' \
  '{"schemaVersion":1,"kind":"OBLIGATION_RESULT","obligationId":"OBL.fast","verdict":"ADMITTED","sessionId":"SESSION.f","detail":""}' \
  >"${wave_root}/obligations-0000/OBL.fast/obligation_result.jsonl"
: >"${wave_root}/obligation_results.jsonl"
find "${wave_root}/obligations-0000" -mindepth 2 -maxdepth 2 \
  -name obligation_result.jsonl -print0 | LC_ALL=C sort -z \
  | xargs -0 -r cat >>"${wave_root}/obligation_results.jsonl"
[[ $(wc -l <"${wave_root}/obligation_results.jsonl") -eq 2 ]] \
  || fail "the wave did not collect every obligation verdict"
[[ "$(jq -r -s '[.[].obligationId] | join(",")' \
      "${wave_root}/obligation_results.jsonl")" == "OBL.fast,OBL.slow" ]] \
  || fail "the wave collected its verdicts in completion order: \
$(jq -r -s '[.[].obligationId] | join(",")' \
    "${wave_root}/obligation_results.jsonl")"
jq -e -s '[.[] | select(.obligationId == "OBL.slow"
    and .verdict == "NOT_ADMITTED")] | length == 1' \
  "${wave_root}/obligation_results.jsonl" >/dev/null \
  || fail "the undecided obligation's verdict was not recorded"

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
# any other -- the wave loop writes it onto the campaign's gap file and goes
# on to publish what it did establish.  An unexplored sibling path blocks a
# closed UNSAT and says nothing about a SAT candidate.
emit_fixture
: >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
printf '%s\n' \
  '{"schemaVersion":1,"sessionId":"","kind":"ADMISSION_GAP","cls":"DIAGNOSTIC","subject":"REGION_PATH_CLOSURE_NO_PROGRESS","detail":"wave 3 proposes the same 2 obligation(s) as the wave before it"}' \
  >"${emit_iteration}/campaign_gaps.jsonl"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a forced exploration stop withheld the candidate \
(exit ${emit_status}): $(<"${emit_root}/emit.log")"
jq -e '.gapCount == 0 and .telemetryCount == 1
  and .telemetryGaps[0].subject == "REGION_PATH_CLOSURE_NO_PROGRESS"' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the exploration stop is not telemetry in gaps.json: \
$(jq -c '.telemetryGaps' "${campaign_final}/gaps.json")"

# The iteration loop advances on a topology it has just learned, and stops
# when a wave exposes none.  A divergent bundle is held out of this epoch, so
# without this the campaign would compose an epoch whose evidence it refused.
div_dir="${test_tmp}/divergence"
mkdir -p "${div_dir}/sessions/SESSION.a"
[[ "$(campaign_topology_divergences "${div_dir}")" == "0" ]] \
  || fail "an iteration with no session gaps reported a divergence"
printf '%s\n' \
  '{"kind":"ADMISSION_GAP","subject":"t","detail":"x"}' \
  >"${div_dir}/sessions/SESSION.a/gaps.jsonl"
[[ "$(campaign_topology_divergences "${div_dir}")" == "0" ]] \
  || fail "an unrelated gap row was counted as a topology divergence"
printf '%s\n' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"IXN.1","detail":"unplanned producer"}' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"IXN.2","detail":"unplanned producer"}' \
  >>"${div_dir}/sessions/SESSION.a/gaps.jsonl"
[[ "$(campaign_topology_divergences "${div_dir}")" == "2" ]] \
  || fail "the topology divergence rows were not counted: \
$(campaign_topology_divergences "${div_dir}")"

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
# whole helper test red on staging until REPORT-GAPJOIN found it -- and
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
# 42: `causynth_static_scope_map` joined it with CLOSURE-V2's static scope
# map.  TWO stages read that file -- the workload JVM installs the guard sites
# it names and EXPLORE flips at them -- so which file it is belongs to the
# configuration a campaign publishes, and both readers take it from this one
# key rather than each deriving a path.
[[ "$(print_normalized_config | wc -l)" -eq 42 ]] \
  || fail "config prints a different number of keys than it used to: \
$(print_normalized_config | wc -l)"
# CONFIG-2: the static scope map is ONE path, and both of its readers take it
# from that one key.  The workload JVM installs the guard sites the map names
# and EXPLORE flips at them, so a second derivation of the path is two stages
# reading two files.
[[ " ${config_table_keys[*]} " == *" causynth_static_scope_map "* ]] \
  || fail "the static scope map is not a declared workflow key"
grep -qF 'causynth_static_scope_map=${causynth_static_scope_map:-${causynth_output_dir}/static_scope_map.jsonl}' \
    "${repo}/run_engine.sh" \
  || fail "the static scope map does not default beside the discovery artifacts"
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

# EPOCH-1: two divergence causes, two epochs (INTERACTION-ID section 8).
# A path that reached a region the workload never retained names that region,
# and the next epoch has to INSTRUMENT it before it replays or it diverges
# identically.  Every other divergence is a pairing or a context the catalog
# did not carry: a new epoch over the same retained set.
grow_dir="${test_tmp}/epoch-growth"
mkdir -p "${grow_dir}/sessions/SESSION.a"
printf '%s\n' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"IXN.1","detail":"a replaced pairing: the catalog names another producer"}' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"REGION.k","detail":"retained set must grow: REGION.k (entry hooks only)"}' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"REGION.k","detail":"retained set must grow: REGION.k (entry hooks only)"}' \
  '{"kind":"ADMISSION_GAP","subject":"x","detail":"retained set must grow: REGION.ignored"}' \
  >"${grow_dir}/sessions/SESSION.a/gaps.jsonl"
[[ "$(campaign_topology_divergences "${grow_dir}")" == "3" ]] \
  || fail "the divergence rows were not counted: \
$(campaign_topology_divergences "${grow_dir}")"
[[ "$(campaign_retained_growth "${grow_dir}")" == "REGION.k" ]] \
  || fail "the retained-set growth is not read off the divergence: \
$(campaign_retained_growth "${grow_dir}")"

# A divergence that names no growth grows nothing: the next epoch plans the
# same retained set.
pair_dir="${test_tmp}/epoch-pairing"
mkdir -p "${pair_dir}/sessions/SESSION.a"
printf '%s\n' \
  '{"kind":"TOPOLOGY_DIVERGENCE","subject":"IXN.9","detail":"a replaced pairing"}' \
  >"${pair_dir}/sessions/SESSION.a/gaps.jsonl"
[[ "$(campaign_topology_divergences "${pair_dir}")" == "1" ]] \
  || fail "a pairing divergence was not counted"
[[ -z "$(campaign_retained_growth "${pair_dir}")" ]] \
  || fail "a pairing divergence grew the retained set: \
$(campaign_retained_growth "${pair_dir}")"

# And an epoch that diverged not at all grows nothing either.
[[ -z "$(campaign_retained_growth "${test_tmp}/epoch-absent")" ]] \
  || fail "an iteration with no sessions grew the retained set"

# A divergent epoch names the replay the next one is seeded from, and the
# harness reads that name off the row rather than re-deriving which replay
# diverged.  Both helpers answer empty when the topology closed, which is what
# makes the loop return instead of planning an epoch from nothing.
seed_dir="${test_tmp}/seeding/iteration-0000"
mkdir -p "${seed_dir}/sessions/SESSION.diverged"
[[ -z "$(campaign_seeding_replay "${seed_dir}")" ]] \
  || fail "a closed topology seeds no epoch"
printf '%s\n' \
  '{"sessionId":"SESSION.diverged","kind":"TOPOLOGY_DIVERGENCE","cls":"DIAGNOSTIC","subject":"IXN.1","detail":"unplanned producer","seedsNextEpoch":true}' \
  '{"sessionId":"SESSION.diverged","kind":"ADMISSION_GAP","cls":"BLOCKING","subject":"OCC.x","detail":"never observed"}' \
  >"${seed_dir}/sessions/SESSION.diverged/gaps.jsonl"
[[ "$(campaign_seeding_replay "${seed_dir}")" == "SESSION.diverged" ]] \
  || fail "the seeding session is not read off the divergent row: \
$(campaign_seeding_replay "${seed_dir}")"

# EPOCH-2: the second epoch's PLAN reaches the scheduler.
#
# It used to die before it started.  campaign_seeding_results handed
# do_schedule a session DIRECTORY as --summaries, do_schedule ran require_file
# on it, and [[ -f <dir> ]] is false -- so every epoch after the first exited
# at that line.  The option it fed is gone with it: the scheduler's --summaries
# rows are keyed on summaryId, which has exactly one occurrence in src/main
# (the reader), and its only other consumer needs ClosureMode.ACTIVE_OBSERVED,
# which this script never sets.  What a second epoch actually varies is the
# retained set, through --retain-regions.
epoch2_dir="${test_tmp}/epoch2"
mkdir -p "${epoch2_dir}/out"
: >"${epoch2_dir}/region_plan.jsonl"
: >"${epoch2_dir}/refined.jsonl.gz"
scheduler_args=""
run_java_main() { scheduler_args="$*"; }
runtime_region_plan="${epoch2_dir}/region_plan.jsonl"
refined_graph="${epoch2_dir}/refined.jsonl.gz"
schedule_output_dir="${epoch2_dir}/out"
schedule_max_jobs=8
schedule_closure_mode=candidate
causynth_symbolic_inputs=""
declared_target_occurrence=""
schedule_retain_regions="REGION.grown"
do_schedule
unset -f run_java_main
[[ "${scheduler_args}" == *"--retain-regions REGION.grown"* ]] \
  || fail "the second epoch did not carry its grown retained set: \
${scheduler_args}"
[[ "${scheduler_args}" != *"--summaries"* ]] \
  || fail "PLAN still passes --summaries, which no stage in this pipeline \
writes: ${scheduler_args}"
[[ "$(type -t campaign_seeding_results)" != function ]] \
  || fail "campaign_seeding_results survived the option it fed"

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
  causynth_cache_dir="${stop_after_dir}/cache"
  causynth_target_spec="${stop_after_dir}/target.yaml"
  custom_jdk_home="${stop_after_dir}/jdk"
  z3_bin=z3
  workload_command="true"
  trace_test=T
  causynth_loop_bounds="${stop_after_dir}/loop-bounds.jsonl"
  : >"${causynth_loop_bounds}"
  causynth_communication_mappings=""
  causynth_symbolic_inputs=""
  causynth_root_domains=""
  solver_timeout_ms=1000
  schedule_max_jobs=1
  concolic_worker_count=1
  campaign_max_iterations=1
  region_path_max_waves=1
  compose_max_valuations=1
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

# STOP-3: what the key does to the campaign.  IMPORT returns 0 right after the
# IMPORT stage of epoch 0 -- EXPLORE and everything after it never run -- and
# an empty value proceeds to EXPLORE and on through EMIT.  The stages are
# driven through a campaign_stage stub, so this pins the control flow of
# do_campaign itself rather than any stage's work.
stop_after_epoch() {
  local root=$1
  local labels=$2
  (
    campaign_stage() { printf '%s\n' "$1" >>"${labels}"; }
    campaign_publish_iteration_manifest() { :; }
    campaign_publish_epoch_final() { :; }
    campaign_topology_divergences() { printf '0\n'; }
    campaign_retained_growth() { printf '\n'; }
    campaign_seeding_replay() { printf '\n'; }
    schedule_output_dir="${root}"
    campaign_setup_command=""
    campaign_max_iterations=1
    do_campaign >/dev/null
  )
}
stop_after_config IMPORT
: >"${stop_after_dir}/labels-import.tsv"
stop_after_epoch "${stop_after_dir}/campaign-import" \
  "${stop_after_dir}/labels-import.tsv" \
  || fail "a campaign stopping after IMPORT did not exit 0"
[[ "$(tail -n 1 "${stop_after_dir}/labels-import.tsv")" == "IMPORT[0]" ]] \
  || fail "the last stage of a stopped campaign is not IMPORT[0]: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-import.tsv")"
! grep -q 'EXPLORE' "${stop_after_dir}/labels-import.tsv" \
  || fail "a campaign stopping after IMPORT still ran EXPLORE"
stop_after_config ""
: >"${stop_after_dir}/labels-full.tsv"
stop_after_epoch "${stop_after_dir}/campaign-full" \
  "${stop_after_dir}/labels-full.tsv" \
  || fail "a campaign with campaign_stop_after unset did not exit 0"
grep -q 'EXPLORE\[0\]' "${stop_after_dir}/labels-full.tsv" \
  || fail "an unset campaign_stop_after did not proceed to EXPLORE: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-full.tsv")"
[[ "$(tail -n 1 "${stop_after_dir}/labels-full.tsv")" == "EMIT[0]" ]] \
  || fail "an unset campaign_stop_after did not run through EMIT: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-full.tsv")"

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

echo "run_engine campaign helper tests passed"
