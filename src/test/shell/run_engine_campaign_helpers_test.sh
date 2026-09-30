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
  # REPRODUCE's answer for that confirmed claim, which EMIT copies beside it.
  jq -n '{schemaVersion: 1, kind: "REPRODUCTION", runs: 10, planted: 10,
    fatal: 7, atAnchor: 6, reason: ""}' >"${campaign_final}/reproduce.json"
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
    iterationId: "iteration-0000", externalWorkerCount: 1,
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
[[ $(jq -r '.reproduction.atAnchor' "${campaign_final}/result.json") == 6 ]] \
  || fail "the result lost the native reproduction"
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
[[ "$(print_normalized_config | wc -l)" -eq 51 ]] \
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
run_java_main() { scheduler_args="$*"; }
runtime_region_plan="${plan2_dir}/region_plan.jsonl"
candidate_graph="${plan2_dir}/candidate.jsonl.gz"
causynth_static_scope_map="${plan2_dir}/static_scope_map.jsonl"
schedule_output_dir="${plan2_dir}/out"
schedule_max_jobs=8
declared_target_occurrence=""
do_schedule
unset -f run_java_main
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
  concolic_worker_count=1
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
COMPOSE SOLVE DECIDE CONFIRM REPRODUCE EMIT " ]] \
  || fail "a full campaign is not the one iteration's stages, each once: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-full.tsv")"

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
# at once, each
# logging to its own targets/<name>/campaign.log.  A target whose campaign
# reached EMIT (exit 0, 2 or 3) is its own verdict; one its group's seed did
# not reach, or whose campaign ended before EMIT, fails the batch once every
# other has finished.
batch_out="${test_tmp}/batch"
for batch_case in "3 a b" "1 a b" "0 a"; do
  read -r batch_exit batch_served <<<"${batch_case}"
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
  ) >"${batch_out}/batch.log" 2>&1 || status=$?
  [[ "${status}" -eq $(( batch_exit == 1 || ${#batch_served} < 3 )) ]] \
    || fail "a batch (${batch_case}) exited ${status}: \
$(cat "${batch_out}/batch.log")"
  [[ "$(cat "${batch_out}/targets/a/campaign.log")" == \
      $'plan of a\ncampaign of a on group-0' \
      && "$(head -n 1 "${batch_out}/targets/b/campaign.log")" == "plan of b" \
      && ( "${batch_served}" == a || "$(tail -n 1 \
        "${batch_out}/targets/b/campaign.log")" == "campaign of b on group-1" ) \
      && ! -e "${batch_out}/targets/c/campaign.log" ]] \
    || fail "a batch (${batch_case}) ran other campaigns than its targets'"
done

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

# The same gate over one wave's own sessions: EXPLORE calls it after the
# wave's replays land, and a blocking violation there fails the campaign at
# that wave.  What the wave ADDED decides whether the gate runs; what it READS
# is the epoch's whole roster, seed included, because invariant 1 is a
# set-level rule (exactly one session states role SEED) and a set cut down to
# one wave never holds the seed.
declare -f campaign_explore | grep -q campaign_import_wave_gate \
  || fail "EXPLORE does not put its wave's sessions to the import gate"
wave_gate="${test_tmp}/import-gate-wave"
mkdir -p "${wave_gate}/sessions/seed-result-0" \
         "${wave_gate}/obligations-0000/OBL.a"
printf '{"sessionId":"focus-a"}\n' \
  >"${wave_gate}/obligations-0000/OBL.a/obligation_result.jsonl"
campaign_session_roster "${wave_gate}/sessions" \
  >"${wave_gate}/obligations-0000/sessions-before.txt"
# The wave's own replay lands after the roster is taken.
mkdir -p "${wave_gate}/sessions/focus-a"
[[ "$(campaign_wave_sessions "${wave_gate}/sessions" \
        "${wave_gate}/obligations-0000/sessions-before.txt")" == "focus-a" ]] \
  || fail "the wave gate does not count exactly the sessions the wave added"
(
  run_java_main() {
    # The gate is handed a session directory of its own, holding the
    # epoch's whole roster, and the wave itself as the one wave of
    # obligation workers behind it.  It is built BESIDE the waves, never
    # inside one: a gate under its own wave links its own ancestor.
    [[ "$3" == "${wave_gate}/import-gates/obligations-0000/sessions" ]] \
      || fail "the wave gate did not name its own session set: $3"
    [[ -d "$3/focus-a" ]] \
      || fail "the wave gate did not gate the session its wave published"
    [[ -d "$3/seed-result-0" ]] \
      || fail "the wave gate left the epoch's seed out of the set it gated, \
so invariant 1 has no SEED to find"
    [[ -f "${wave_gate}/import-gates/obligations-0000/obligations-0000/\
OBL.a/obligation_result.jsonl" ]] \
      || fail "the wave gate hid its own obligation workers"
    [[ ! -e "${wave_gate}/obligations-0000/import-gate" ]] \
      || fail "the wave gate was built inside the wave it links"
    printf '%s\n' '{"violations":1,"blocking":1,'\
'"firstBlockingSubject":"roots.jsonl seq=3 field=recordedValue"}'
    printf '{"schemaVersion":1,"cls":"BLOCKING"}\n' \
      >>"${wave_gate}/campaign_gaps.jsonl"
  }
  campaign_import_wave_gate "${wave_gate}" iteration-0000 \
    "${wave_gate}/obligations-0000" "${wave_gate}/sessions" >/dev/null
) 2>"${wave_gate}/error.log" \
  && fail "a blocking row invariant in a wave's session did not fail the \
campaign"
grep -q 'stage=IMPORT' "${wave_gate}/error.log" \
  || fail "the wave gate's failure is not attributed to IMPORT: \
$(cat "${wave_gate}/error.log")"
grep -q 'roots.jsonl seq=3 field=recordedValue' "${wave_gate}/error.log" \
  || fail "the wave gate's failure does not name the first blocking subject"
[[ -s "${wave_gate}/obligations-0000/import_gate.json" ]] \
  || fail "the wave gate wrote no summary of its own"

# And EVERY wave of the epoch is behind the set it gates, not just the one
# being gated.  Invariant 6 asks of each FOCUSED session which world it ran
# in, and its worker's focus row is the only thing that says so; a gate that
# links this wave alone hides every earlier wave's focus rows, so each session
# an earlier wave focused reads as "no focus row this epoch".  hdfs-11741
# campaign #3: wave 1 was the first wave of any campaign to publish a session,
# and its gate refused with 13 BLOCKING invariant-6 rows, one per session that
# wave 0 had focused.
mkdir -p "${wave_gate}/obligations-0001/OBL.b"
printf '{"sessionId":"focus-b"}\n' \
  >"${wave_gate}/obligations-0001/OBL.b/obligation_result.jsonl"
campaign_session_roster "${wave_gate}/sessions" \
  >"${wave_gate}/obligations-0001/sessions-before.txt"
mkdir -p "${wave_gate}/sessions/focus-b"
(
  run_java_main() {
    [[ -f "${wave_gate}/import-gates/obligations-0001/obligations-0000/\
OBL.a/obligation_result.jsonl" ]] \
      || fail "the wave gate hid an EARLIER wave's obligation workers, so \
every session that wave focused reads as having no focus row"
    [[ -f "${wave_gate}/import-gates/obligations-0001/obligations-0001/\
OBL.b/obligation_result.jsonl" ]] \
      || fail "the wave gate hid its own obligation workers"
    printf '%s\n' '{"violations":0,"blocking":0,"firstBlockingSubject":""}'
  }
  campaign_import_wave_gate "${wave_gate}" iteration-0000 \
    "${wave_gate}/obligations-0001" "${wave_gate}/sessions" >/dev/null
) || fail "a wave gate over two waves did not link both waves"
[[ -s "${wave_gate}/obligations-0001/import_gate.json" ]] \
  || fail "the wave gate's summary does not stay with its wave"
# NO LINK INTO ITS OWN ANCESTOR: the gate is beside the waves, so nothing
# under it resolves to a directory that contains it -- a walker that
# recurses cannot loop.
for gate_link in "${wave_gate}"/import-gates/*/*; do
  [[ -L "${gate_link}" ]] || continue
  gate_target=$(readlink -f "${gate_link}")
  gate_holder=$(readlink -f "$(dirname "${gate_link}")")
  [[ "${gate_holder}" != "${gate_target}"/* \
     && "${gate_holder}" != "${gate_target}" ]] \
    || fail "the wave gate links its own ancestor: ${gate_link}"
done

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
  campaign_verify_woven_classes "${verify_dir}" >/dev/null
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
  campaign_verify_woven_classes "${verify_dir}" >/dev/null
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
# Five seconds, not one: the adapter is a LOGIN shell, and the lifts' login
# profile runs a quota check on NFS that alone takes up to a second, so a
# one-second bound sometimes fired before the payload wrote its pid.
campaign_adapter_timeout_s=5
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

# REPLAY-BOUND-3: what one obligation whose replay never returns records.
# The same terminal NOT_ADMITTED row the worker writes for a solver that
# failed -- one obligation's own answer, never the wave's death -- naming the
# bound it exceeded.  The worker must also RETURN, which is the whole point:
# campaign_wait_workers waited on the hung one forever.
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
  run_java_main() {
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
  run_java_main() {
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
  run_java_main() {
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
# POOL-1: a slot that frees takes the next obligation IMMEDIATELY.
#
# What this replaces was a batch barrier: fill ${concolic_worker_count}
# background pids, wait for ALL of them, start the next array.  One slow
# obligation then idled every other slot for its whole duration -- and on
# 11741 every wave has one, because a replay that reaches its target runs a
# MiniDFSCluster and one that refuses at the solver does not.
#
# One long job and five short ones over two slots.  The barrier pairs the
# long one with a short one and nothing else may start until the long one
# ends; the pool runs all five short ones on the other slot WHILE the long
# one is still going.  Both claims are checked, because either alone is weak:
# the wall clock alone is a race on a loaded machine, and the start times
# alone do not say the wave was actually faster.
pool_dir="${test_tmp}/pool"
mkdir -p "${pool_dir}/wave"
reset_config
concolic_worker_count=2
campaign_worker_hosts=""
obligation_memory_mb=1
pool_jobs=(LONG F1 F2 F3 F4 F5)
for pool_job in "${pool_jobs[@]}"; do
  mkdir -p "${pool_dir}/wave/${pool_job}"
done
# The stub stands where campaign_obligation_worker stands, so everything
# between the pool and it -- the claim, the slot, the local branch of
# campaign_run_obligation_on_host, the log redirection -- is the real thing.
campaign_obligation_worker() {
  local id=$1 worker=$4
  date +%s.%N >"${worker}/started-at"
  if [[ "${id}" == LONG ]]; then sleep 4; else sleep 0.3; fi
  date +%s.%N >"${worker}/ended-at"
  jq -n -c --arg id "${id}" '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
    obligationId: $id, verdict: "UNSAT", sessionId: "", detail: ""}' \
    >"${worker}/obligation_result.jsonl"
}
pool_started=$(date +%s.%N)
campaign_dispatch_wave "${pool_dir}/wave" /dev/null /dev/null /dev/null \
  /dev/null "${pool_jobs[@]}" >"${pool_dir}/dispatch.log" 2>&1 \
  || fail "the pool did not finish a wave of six: $(cat "${pool_dir}/dispatch.log")"
pool_elapsed=$(awk -v a="$(date +%s.%N)" -v b="${pool_started}" \
  'BEGIN{printf "%.2f", a - b}')
for pool_job in "${pool_jobs[@]}"; do
  [[ -s "${pool_dir}/wave/${pool_job}/obligation_result.jsonl" ]] \
    || fail "the pool did not run ${pool_job}"
done
# NOT THE SUM.  Six jobs end to end is 5.5s; the barrier is 4.6s; the pool is
# the long job plus change.  5 is below the sum with room to spare and the
# claim the brief makes.
awk -v e="${pool_elapsed}" 'BEGIN{exit !(e < 5)}' \
  || fail "the pool took ${pool_elapsed}s for one 4s job and five 0.3s ones: \
that is the sum of the work, not the length of its longest piece"
# NOT THE BARRIER.  Every short job started before the long one finished,
# which is exactly what a barrier cannot do: under it, four of the five would
# start only once the long job's batch had been waited on.
pool_long_end=$(cat "${pool_dir}/wave/LONG/ended-at")
for pool_job in F1 F2 F3 F4 F5; do
  pool_start=$(cat "${pool_dir}/wave/${pool_job}/started-at")
  awk -v s="${pool_start}" -v e="${pool_long_end}" 'BEGIN{exit !(s < e)}' \
    || fail "${pool_job} did not start until the long obligation had \
finished: the slot was idle behind a barrier, not pulling work"
done
# And the pool laid the work out over both slots rather than serialising it.
[[ "$(wc -l <"${pool_dir}/wave/work-queue.txt")" -eq 6 ]] \
  || fail "the wave's job list is not the six obligations it was given"
[[ "$(find "${pool_dir}/wave/work-queue" -mindepth 1 -maxdepth 1 -type d \
    | wc -l)" -eq 6 ]] \
  || fail "the work queue does not hold one claim per obligation"
unset -f campaign_obligation_worker

# POOL-2: a failed obligation still fails the WAVE, and still lets the wave
# finish.  campaign_wait_workers' semantics are what the barrier had: the
# remaining obligations ran after one of them failed, and the wave failed at
# the end.  A pool that stopped its slot on the first failure would discard
# verdicts the wave had already paid for -- the same loss REPLAY-BOUND-1
# exists to prevent.
pool_fail_dir="${test_tmp}/pool-fail"
mkdir -p "${pool_fail_dir}/wave"
for pool_job in A B C D; do mkdir -p "${pool_fail_dir}/wave/${pool_job}"; done
campaign_obligation_worker() {
  local id=$1 worker=$4
  : >"${worker}/ran"
  [[ "${id}" != B ]] || return 7
  jq -n -c --arg id "${id}" '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
    obligationId: $id, verdict: "UNSAT", sessionId: "", detail: ""}' \
    >"${worker}/obligation_result.jsonl"
}
concolic_worker_count=2
campaign_dispatch_wave "${pool_fail_dir}/wave" /dev/null /dev/null /dev/null \
  /dev/null A B C D >"${pool_fail_dir}/dispatch.log" 2>&1 \
  && fail "one failed obligation did not fail the wave"
for pool_job in A B C D; do
  [[ -f "${pool_fail_dir}/wave/${pool_job}/ran" ]] \
    || fail "obligation ${pool_job} never ran: one failure stopped its slot"
done
grep -q 'DID NOT FINISH' "${pool_fail_dir}/dispatch.log" \
  || fail "the failed obligation is not named in the wave's log: \
$(cat "${pool_fail_dir}/dispatch.log")"
unset -f campaign_obligation_worker
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

# HOSTS-2: the slot layout.  Empty is one host's worth of slots; a list is
# ${concolic_worker_count} slots PER HOST, laid out so the wave's opening
# fill -- every slot claiming at once -- lands round-robin across the hosts
# instead of filling the first host before the second sees any work.
concolic_worker_count=3
campaign_worker_hosts=""
[[ "$(campaign_worker_slot_hosts | tr '\n' ' ')" \
    == "localhost localhost localhost " ]] \
  || fail "an empty host list is not this machine's slots: \
$(campaign_worker_slot_hosts | tr '\n' ' ')"
campaign_worker_hosts="lift12 lift13"
[[ "$(campaign_worker_slot_hosts | tr '\n' ' ')" \
    == "lift12 lift13 lift12 lift13 lift12 lift13 " ]] \
  || fail "two hosts do not round-robin: \
$(campaign_worker_slot_hosts | tr '\n' ' ')"
[[ "$(campaign_worker_slot_hosts | wc -l)" -eq 6 ]] \
  || fail "the pool is not hosts x concolic_worker_count wide"
# localhost, and this machine's own name, are local: no ssh for either.
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

# HOSTS-3: EMPTY MEANS NO SSH.  The default is not "ssh to localhost", it is
# the plain background subshell this shell always used -- so a run that
# states no hosts cannot fail for a reason ssh invented.
nossh_dir="${test_tmp}/no-ssh"
mkdir -p "${nossh_dir}/wave"
for pool_job in A B C; do mkdir -p "${nossh_dir}/wave/${pool_job}"; done
ssh() { printf '%s\n' "$*" >>"${nossh_dir}/ssh-calls.txt"; return 99; }
campaign_obligation_worker() {
  local id=$1 worker=$4
  jq -n -c --arg id "${id}" '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
    obligationId: $id, verdict: "UNSAT", sessionId: "", detail: ""}' \
    >"${worker}/obligation_result.jsonl"
}
concolic_worker_count=2
campaign_worker_hosts=""
obligation_memory_mb=1
campaign_dispatch_wave "${nossh_dir}/wave" /dev/null /dev/null /dev/null \
  /dev/null A B C >"${nossh_dir}/dispatch.log" 2>&1 \
  || fail "the local default did not finish its wave: \
$(cat "${nossh_dir}/dispatch.log")"
[[ ! -e "${nossh_dir}/ssh-calls.txt" ]] \
  || fail "an empty campaign_worker_hosts still invoked ssh $(wc -l \
<"${nossh_dir}/ssh-calls.txt") time(s): $(cat "${nossh_dir}/ssh-calls.txt")"
for pool_job in A B C; do
  [[ "$(cat "${nossh_dir}/wave/${pool_job}/host.txt")" == localhost ]] \
    || fail "${pool_job} did not record the local host"
  [[ -s "${nossh_dir}/wave/${pool_job}/obligation_result.jsonl" ]] \
    || fail "${pool_job} produced no result locally"
done

# HOSTS-4: two hosts round-robin, and BOTH hosts' results are collected.
#
# The stub stands where the network stands and nowhere else: the wave, the
# pool, the slot, the host decision, the generated remote script and the
# bounded wait for what the peer wrote are all the production code.  What the
# stub does is what a peer does -- run the script it was handed -- except
# that it runs the payload's job directly, because the payload is a second
# JVM-bearing campaign process and this is a shell test.
twohost_dir="${test_tmp}/two-hosts"
mkdir -p "${twohost_dir}/wave" "${twohost_dir}/sessions"
for pool_job in A B C D; do mkdir -p "${twohost_dir}/wave/${pool_job}"; done
campaign_root="${twohost_dir}"
graphchecker_jar=${default_graphchecker_jar}
replay_timeout_s=2400
solver_timeout_ms=1800000
campaign_init_local_scratch_root
ssh() {
  local host="" script=""
  # The production call is `ssh <options> -- <host> <command>`, so `--` is
  # where the options stop, exactly as it is for the real client.
  while [[ $# -gt 0 ]]; do
    [[ "$1" == "--" ]] && { shift; break; }
    shift
  done
  host=${1:-}
  script=${2:-}
  script=${script#exec /bin/bash }
  script=${script%\'}
  script=${script#\'}
  printf '%s\t%s\n' "${host}" "${script}" >>"${twohost_dir}/ssh-calls.txt"
  # The generated script is what a peer is asked to run, so it had better be
  # a script a peer can run.
  [[ -s "${script}" ]] || return 91
  bash -n "${script}" || return 92
  grep -q -- '--run-obligation' "${script}" || return 93
  grep -q -- "--graphchecker-jar-sha256 $(sha256sum "${graphchecker_jar}" \
    | awk '{print $1}')" "${script}" || return 94
  grep -q "CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root}" \
    "${script}" || return 95
  # What the peer's payload would have published, published.
  local worker
  worker=$(awk '$1 == "--" {print $5; exit}' "${script}")
  jq -n -c --arg id "$(basename "${worker}")" --arg host "${host}" \
    '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: $id,
      verdict: "ADMITTED", sessionId: ("SESSION." + $id), detail: $host}' \
    >"${worker}/obligation_result.jsonl"
  mkdir -p "${twohost_dir}/sessions/SESSION.$(basename "${worker}")"
  return 0
}
concolic_worker_count=2
campaign_worker_hosts="lift12 lift13"
campaign_local_host_names=" localhost this-machine "
obligation_memory_mb=1
campaign_host_available_mb() { echo 30000; }
campaign_host_total_mb() { echo 30000; }
campaign_dispatch_wave "${twohost_dir}/wave" "${twohost_dir}/obligations.jsonl" \
  "${twohost_dir}/classes" "${twohost_dir}/sessions" \
  "${twohost_dir}/seed.jsonl" A B C D \
  >"${twohost_dir}/dispatch.log" 2>&1 \
  || fail "a two-host wave did not finish: $(cat "${twohost_dir}/dispatch.log")"
[[ "$(wc -l <"${twohost_dir}/ssh-calls.txt")" -eq 4 ]] \
  || fail "four obligations did not become four remote invocations: \
$(cat "${twohost_dir}/ssh-calls.txt")"
for twohost_host in lift12 lift13; do
  [[ "$(cut -f1 <"${twohost_dir}/ssh-calls.txt" | grep -c "^${twohost_host}$")" \
      -ge 1 ]] \
    || fail "${twohost_host} was given no work: the pool did not round-robin: \
$(cut -f1 <"${twohost_dir}/ssh-calls.txt" | LC_ALL=C sort | uniq -c)"
done
# Both hosts' results are here, and they are the peers' own rows.
for pool_job in A B C D; do
  [[ -s "${twohost_dir}/wave/${pool_job}/obligation_result.jsonl" ]] \
    || fail "${pool_job}'s remote result was not collected"
  [[ "$(jq -r '.verdict' \
      "${twohost_dir}/wave/${pool_job}/obligation_result.jsonl")" \
      == ADMITTED ]] \
    || fail "${pool_job}'s collected row is not the peer's verdict"
  case "$(cat "${twohost_dir}/wave/${pool_job}/host.txt")" in
    lift12|lift13) ;;
    *) fail "${pool_job} did not record which host ran it: \
$(cat "${twohost_dir}/wave/${pool_job}/host.txt")" ;;
  esac
done
[[ "$(cat "${twohost_dir}/wave"/*/host.txt | LC_ALL=C sort -u | wc -l)" \
    -eq 2 ]] \
  || fail "the wave's obligations all landed on one host"
campaign_log_wave_hosts "${twohost_dir}/wave" 0 \
  >"${twohost_dir}/hosts.log" 2>&1
grep -q 'lift12=' "${twohost_dir}/hosts.log" \
  || fail "the wave summary does not say how many ran on lift12: \
$(cat "${twohost_dir}/hosts.log")"
grep -q 'lift13=' "${twohost_dir}/hosts.log" \
  || fail "the wave summary does not say how many ran on lift13"
# POOL-ROOM: a slot waits for room BEFORE it claims, so a host that has none
# holds no obligation while the other runs them all, and its slots end with
# the wave (a10: one claim waited 30 min on a lift a planner had filled).
room_wave="${twohost_dir}/wave-room"
for pool_job in E F G; do mkdir -p "${room_wave}/${pool_job}"; done
campaign_host_poll_s=0
campaign_host_available_mb() { [[ "$1" == lift13 ]] && echo 0 || echo 30000; }
campaign_host_total_mb() { echo 30000; }
campaign_dispatch_wave "${room_wave}" "${twohost_dir}/obligations.jsonl" \
  "${twohost_dir}/classes" "${twohost_dir}/sessions" \
  "${twohost_dir}/seed.jsonl" E F G \
  >"${twohost_dir}/dispatch-room.log" 2>&1 \
  || fail "a wave with one full host did not finish: \
$(cat "${twohost_dir}/dispatch-room.log")"
[[ "$(cat "${room_wave}"/*/host.txt | LC_ALL=C sort -u)" == lift12 ]] \
  || fail "a host without room held work: $(cat "${room_wave}"/*/host.txt)"
unset -f ssh
unset -f campaign_obligation_worker
reset_config

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
# And every workflow key travels as its own environment override, so the
# peer's configuration is the head's rather than a second derivation of it.
reset_config
concolic_worker_count=8
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

# GROW-1: the growth step (PIPELINE §7.8).  ExploreMain named a region an
# obligation's replay reached without its hooks; the step plans it, weaves
# it and re-runs that obligation's replay in its own worker directory, and
# the corpus ends up holding the re-run's session in place of the exposing
# one.  The planner JVM and the weave are stubbed (run_java_main and
# campaign_instrument); the replay is a script that publishes a session, so
# everything between -- the plan appends reaching the workers through their
# hard links, the withdrawal, the re-run and the verdict rewrite -- is the
# production code.
grow_dir="${test_tmp}/grow/iteration-0000"
grow_wave0="${grow_dir}/obligations-0000"
grow_wave1="${grow_dir}/obligations-0001"
grow_sessions="${grow_dir}/sessions"
grow_plan="${grow_dir}/execution_task_plan.jsonl"
grow_seed_plan="${grow_dir}/seed-replay/execution_task_plan.jsonl"
grow_results="${grow_dir}/obligation_results.jsonl"
mkdir -p "${grow_wave0}/OB.x" "${grow_wave1}" "${grow_dir}/seed-replay" \
  "${grow_dir}/workers/task-a" "${grow_sessions}/SESSION.exposing" \
  "${grow_sessions}/SESSION.other"
printf '{"taskId":"TASK.1","regionId":"REGION.a"}\n' >"${grow_plan}"
ln -f "${grow_plan}" "${grow_seed_plan}"
# The links PLAN and the obligation worker make: a member's plan is the
# iteration plan, an obligation worker's is the seed plan.
ln -f "${grow_plan}" "${grow_dir}/workers/task-a/execution_task_plan.jsonl"
ln -f "${grow_seed_plan}" "${grow_wave0}/OB.x/execution_task_plan.jsonl"
# What the exposing replay left in its worker and in the corpus.
printf '{"taskId":"TASK.1"}\n' >"${grow_wave0}/OB.x/focused_task.jsonl"
printf 'the exposing replay\n' >"${grow_wave0}/OB.x/replay.log"
printf 'lift12\n' >"${grow_wave0}/OB.x/host.txt"
jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: "OB.x",
  verdict: "ADMITTED", sessionId: "SESSION.exposing", detail: ""}' \
  >"${grow_wave0}/OB.x/obligation_result.jsonl"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.exposing", role: "FOCUSED", obligationIds: ["OB.x"]}' \
  >"${grow_sessions}/SESSION.exposing/manifest.json"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.other", role: "FOCUSED", obligationIds: ["OB.y"]}' \
  >"${grow_sessions}/SESSION.other/manifest.json"
printf '%s\n' \
  '{"schemaVersion":1,"kind":"OBLIGATION_RESULT","obligationId":"OB.y","verdict":"ADMITTED","sessionId":"SESSION.other","detail":""}' \
  '{"schemaVersion":1,"kind":"OBLIGATION_RESULT","obligationId":"OB.x","verdict":"ADMITTED","sessionId":"SESSION.exposing","detail":""}' \
  >"${grow_results}"
# The wave planner's statement: one exposure, and the frontier summary that
# is always there.
printf '%s\n' \
  '{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
  '{"kind":"FRONTIER","open":0}' \
  >"${grow_wave1}/growth.jsonl"
[[ "$(campaign_exposures "${grow_wave1}/growth.jsonl")" \
    == "OB.x	REGION.grown	SESSION.exposing" ]] \
  || fail "the exposures are not read off growth.jsonl: \
$(campaign_exposures "${grow_wave1}/growth.jsonl")"
# The re-run: it must be handed the grown plan and task, and it publishes a
# session naming OB.x and the verdict row RowRuntime writes.
cat >"${grow_dir}/replay.sh" <<'EOF'
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
  >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/obligation_result.jsonl"
EOF
chmod +x "${grow_dir}/replay.sh"
reset_config
concolic_replay_command="${grow_dir}/replay.sh"
obligation_memory_mb=1
replay_timeout_s=60
schedule_max_jobs=1
trace_test=T
causynth_static_scope_map=""
custom_jdk_home=""
workload_work_dir="${grow_dir}"
(
  run_java_main() {
    [[ "$1" == edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain ]] \
      || fail "GROW ran a JVM other than the exposed-region planner: $*"
    local args=" $* " output
    [[ "${args}" == *" --iteration ${grow_dir} "* \
        && "${args}" == *" --growth ${grow_wave1}/growth.jsonl "* ]] \
      || fail "the exposed-region planner was not handed the iteration and \
the wave's growth rows: $*"
    output=${args##* --output }
    output=${output%% *}
    printf '{"taskId":"TASK.grown","regionId":"REGION.grown","admissionBasis":"EXPOSED_BY"}\n' \
      >"${output}"
  }
  campaign_instrument() {
    [[ "$1" == "${grow_dir}" ]] || fail "the weave was given $1"
    grep -q TASK.grown "${grow_plan}" \
      || fail "the weave ran before the grown rows reached the iteration plan"
    mkdir -p "${grow_dir}/instrumented-classes"
    : >"${grow_dir}/instrumented-classes/woven"
  }
  campaign_grow "${grow_dir}" "${grow_wave1}" \
    "${grow_dir}/instrumented-classes" "${grow_sessions}" "${grow_seed_plan}" \
    "${grow_results}"
) >"${grow_dir}/grow.log" 2>&1 \
  || fail "the growth step did not finish: $(cat "${grow_dir}/grow.log")"
# Both plans carry the row, and so does every worker's link of them.
grep -q TASK.grown "${grow_dir}/workers/task-a/execution_task_plan.jsonl" \
  || fail "the member worker's plan did not see the grown row"
grep -q TASK.grown "${grow_wave0}/OB.x/execution_task_plan.jsonl" \
  || fail "the obligation worker's plan did not see the grown row"
[[ -s "${grow_wave1}/exposed_region_plan.jsonl" ]] \
  || fail "the grown rows are not kept beside the wave that grew them"
# The exposing session left the corpus and is kept under its worker; the
# re-run's session is in the corpus; another obligation's session is where
# it was.
[[ ! -e "${grow_sessions}/SESSION.exposing" ]] \
  || fail "the exposing session is still in the corpus"
[[ -f "${grow_wave0}/OB.x/before-obligations-0001/sessions/SESSION.exposing/manifest.json" ]] \
  || fail "the exposing session is not kept under the worker: \
$(find "${grow_wave0}" | LC_ALL=C sort)"
[[ -f "${grow_sessions}/SESSION.regrown/manifest.json" ]] \
  || fail "the re-run's session did not reach the corpus"
[[ -f "${grow_sessions}/SESSION.other/manifest.json" ]] \
  || fail "another obligation's session was withdrawn with the exposing one"
# The exposing replay's log and verdict are aside; the re-run's are the
# worker's, and the re-run ran on the head.
[[ "$(cat "${grow_wave0}/OB.x/before-obligations-0001/replay.log")" \
    == "the exposing replay" ]] \
  || fail "the exposing replay's log was not kept aside"
[[ "$(jq -r '.verdict' "${grow_wave0}/OB.x/obligation_result.jsonl")" \
    == NOT_ADMITTED ]] \
  || fail "the worker's verdict row is not the re-run's: \
$(cat "${grow_wave0}/OB.x/obligation_result.jsonl")"
[[ "$(cat "${grow_wave0}/OB.x/host.txt")" == localhost ]] \
  || fail "the re-run did not record that it ran on the head"
# The results file: OB.y untouched, OB.x replaced, each once.
jq -e -s 'length == 2
  and ([.[] | select(.obligationId == "OB.x")] | length == 1
       and .[0].verdict == "NOT_ADMITTED"
       and .[0].sessionId == "SESSION.regrown")
  and ([.[] | select(.obligationId == "OB.y")] | length == 1)' \
  "${grow_results}" >/dev/null \
  || fail "the re-run's verdict did not replace the exposing one, once: \
$(cat "${grow_results}")"
grep -q 'grown by REGION.grown' "${grow_dir}/grow.log" \
  || fail "the step did not say what grew: $(cat "${grow_dir}/grow.log")"
grep -q 'OB.x: re-run under the grown tree, verdict=NOT_ADMITTED' \
    "${grow_dir}/grow.log" \
  || fail "the step did not say what the re-run decided"
# An exposure that names no obligation is the seed's, and the seed is not
# re-run: refused by name before any plan is touched.
printf '%s\n' \
  '{"kind":"EXPOSED_REGION","regionId":"REGION.seed","node":"nn0","occurrence":"REGION.seed#1","sessionId":"SESSION.seed","obligationId":""}' \
  >"${grow_wave1}/growth.jsonl"
(
  run_java_main() { fail "the planner ran on an exposure GROW must refuse"; }
  campaign_grow "${grow_dir}" "${grow_wave1}" \
    "${grow_dir}/instrumented-classes" "${grow_sessions}" "${grow_seed_plan}" \
    "${grow_results}"
) >/dev/null 2>"${grow_dir}/refuse.log" \
  && fail "an exposure with no obligation was grown into"
grep -q 'names no obligation' "${grow_dir}/refuse.log" \
  || fail "the refusal does not say why: $(cat "${grow_dir}/refuse.log")"
reset_config

# EXPLORE-3: the wave loop around the step.  The planner is stubbed to say
# what each wave proposes and exposes, the pool to answer each obligation,
# and the step and the gate to record that they ran; the loop's own order
# and its fixed point are the production code.  Wave 0 proposes one
# obligation and exposes nothing; wave 1 proposes nothing and exposes one
# region; wave 2 proposes and exposes nothing, which is the fixed point.
loop_dir="${test_tmp}/explore-loop/iteration-0000"
mkdir -p "${loop_dir}/sessions" "${loop_dir}/seed-replay"
: >"${loop_dir}/seed-replay/execution_task_plan.jsonl"
explore_loop_planner() {
  local wave="" out=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --wave) wave=$2; shift 2 ;;
      --output-dir) out=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  : >"${out}/obligations.jsonl"
  printf '{"kind":"FRONTIER","open":0}\n' >"${out}/growth.jsonl"
  case "${wave}" in
    0) printf '{"obligationId":"OB.a"}\n' >"${out}/obligations.jsonl" ;;
    1) printf '%s\n' \
        '{"kind":"EXPOSED_REGION","regionId":"REGION.g","node":"nn0","occurrence":"REGION.g#1","sessionId":"SESSION.a","obligationId":"OB.a"}' \
        >>"${out}/growth.jsonl" ;;
  esac
}
reset_config
concolic_worker_count=1
region_path_max_waves=12
causynth_static_scope_map=""
causynth_root_domains=""
declared_target_occurrence=""
(
  run_java_main() { explore_loop_planner "$@"; }
  campaign_dispatch_wave() {
    local wave_dir=$1
    shift 5
    printf '%s\n' "$*" >>"${loop_dir}/dispatched.txt"
    local job
    for job in "$@"; do
      jq -n -c --arg id "${job}" '{schemaVersion: 1,
        kind: "OBLIGATION_RESULT", obligationId: $id, verdict: "ADMITTED",
        sessionId: "SESSION.a", detail: ""}' \
        >"${wave_dir}/${job}/obligation_result.jsonl"
    done
  }
  campaign_grow() { printf '%s\n' "$(basename "$2")" >>"${loop_dir}/grown.txt"; }
  campaign_import_wave_gate() {
    printf '%s\n' "$(basename "$3")" >>"${loop_dir}/gated.txt"
  }
  campaign_explore "${loop_dir}" iteration-0000
) >"${loop_dir}/explore.log" 2>&1 \
  || fail "the wave loop did not finish: $(cat "${loop_dir}/explore.log")"
[[ "$(cat "${loop_dir}/dispatched.txt")" == "OB.a" ]] \
  || fail "the pool did not run exactly wave 0's obligation: \
$(cat "${loop_dir}/dispatched.txt")"
[[ "$(cat "${loop_dir}/grown.txt")" == "obligations-0001" ]] \
  || fail "the growth step did not run exactly once, on wave 1: \
$(cat "${loop_dir}/grown.txt")"
[[ "$(tr '\n' ' ' <"${loop_dir}/gated.txt")" \
    == "obligations-0000 obligations-0001 " ]] \
  || fail "the gate did not run once per wave that did work: \
$(tr '\n' ' ' <"${loop_dir}/gated.txt")"
[[ -d "${loop_dir}/obligations-0002" && ! -e "${loop_dir}/obligations-0003" ]] \
  || fail "the loop did not stop at the first wave with nothing open and \
nothing exposed"
grep -q 'wave 2: no obligation open and no region exposed' \
    "${loop_dir}/explore.log" \
  || fail "the fixed point is not stated: $(cat "${loop_dir}/explore.log")"
[[ "$(jq -r '.obligationId' "${loop_dir}/obligation_results.jsonl")" == OB.a ]] \
  || fail "the wave's verdict was not collected"
[[ ! -e "${loop_dir}/campaign_gaps.jsonl" ]] \
  || fail "a loop that reached its fixed point wrote a stop row"
# The wave bound: an exposure still owed when region_path_max_waves is
# reached is stated, as a gap row and in the log, and the loop stops.
bound_loop="${test_tmp}/explore-bound/iteration-0000"
mkdir -p "${bound_loop}/sessions" "${bound_loop}/seed-replay"
: >"${bound_loop}/seed-replay/execution_task_plan.jsonl"
region_path_max_waves=1
(
  run_java_main() { explore_loop_planner "$@"; }
  campaign_dispatch_wave() {
    local wave_dir=$1
    shift 5
    local job
    for job in "$@"; do
      jq -n -c --arg id "${job}" '{schemaVersion: 1,
        kind: "OBLIGATION_RESULT", obligationId: $id, verdict: "ADMITTED",
        sessionId: "SESSION.a", detail: ""}' \
        >"${wave_dir}/${job}/obligation_result.jsonl"
    done
  }
  campaign_grow() { fail "the growth step ran past the wave bound"; }
  campaign_import_wave_gate() { :; }
  campaign_explore "${bound_loop}" iteration-0000
) >"${bound_loop}/explore.log" 2>&1 \
  || fail "the bounded wave loop did not finish: \
$(cat "${bound_loop}/explore.log")"
jq -e 'select(.subject == "REGION_PATH_WAVE_BUDGET_REACHED")
  | .detail | test("region_path_max_waves=1") and test("1 region exposure")' \
  "${bound_loop}/campaign_gaps.jsonl" >/dev/null \
  || fail "the wave bound is not stated as a gap row naming the exposure: \
$(cat "${bound_loop}/campaign_gaps.jsonl")"
grep -q 'region_path_max_waves=1' "${bound_loop}/explore.log" \
  || fail "the wave bound is not stated in the campaign log"
# And a planner that states no growth file is a planner that did not run
# to completion: refused by name, never read as "nothing exposed".
nogrowth_loop="${test_tmp}/explore-nogrowth/iteration-0000"
mkdir -p "${nogrowth_loop}/sessions" "${nogrowth_loop}/seed-replay"
: >"${nogrowth_loop}/seed-replay/execution_task_plan.jsonl"
region_path_max_waves=12
(
  run_java_main() { :; }
  campaign_explore "${nogrowth_loop}" iteration-0000
) >/dev/null 2>"${nogrowth_loop}/explore.err" \
  && fail "a wave with no growth.jsonl was read as nothing exposed"
grep -q 'wave growth rows' "${nogrowth_loop}/explore.err" \
  || fail "the missing growth file is not named: \
$(cat "${nogrowth_loop}/explore.err")"
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
  : >"${confirm_root}/replay-ran"
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
  jq -n --arg anchor "${confirm_anchor}" '{anchor: $anchor}' \
    >"${campaign_final}/claim.json"
  (
    run_java_main() {
      case " $* " in
        *" --sessions "*) "${confirm_java[@]}" "$@" ;;
        *) confirm_stub_main "$@" ;;
      esac
    }
    campaign_obligation_replay() { confirm_stub_replay "$@"; }
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
# The rule, both conditions holding.
run_confirm SAT_CANDIDATE
confirm_says true "the claim's anchor observed the fatal" \
  "a clean replay was not confirmed"
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
run_confirm SAT_CANDIDATE
confirm_says false "the model chose producer p1, the run paired p2" \
  "a mismatched edge was confirmed"
confirm_stub_gaps=""
# A session that published no gap file answers nothing about the edges.
unset confirm_stub_gaps
run_confirm SAT_CANDIDATE
confirm_says false "published no readable" \
  "a session with no gap file was confirmed"
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
unset -f confirm_stub_main confirm_stub_replay run_confirm confirm_says
unset confirm_anchor confirm_stub_target_iteration confirm_java

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
campaign_host_try_start lift14 \
  || fail "20000 MB free did not admit a 6000 MB obligation"
campaign_host_try_start lift14 \
  || fail "20000 MB less one 6000 MB start did not admit a second"
run_capturing_status campaign_host_try_start lift14
[[ "${status}" -eq 1 ]] \
  || fail "two starts charged 12000 MB, and a third was admitted over the \
3000 MB reserve"
[[ "${campaign_host_wait_reason}" == *"12000 MB charged"* ]] \
  || fail "the wait does not say what is charged: ${campaign_host_wait_reason}"
# Another campaign, the same host: the same ledger refuses it too.
( run_capturing_status campaign_host_try_start lift14; exit "${status}" ) \
  && fail "another campaign's start ignored the charges on the host"
# The window passes: the JVMs are in MemAvailable now, and the charge lapses.
sed -i 's/^[0-9]* /1 /' "${campaign_host_gate_root}/lift14/starts"
campaign_host_try_start lift14 \
  || fail "starts older than the ramp window are still charged"
# The head is one ledger under both of its names.
campaign_host_try_start localhost \
  || fail "the head's first start was refused"
[[ -s "${campaign_host_gate_root}/gate-head/starts" \
    && ! -e "${campaign_host_gate_root}/localhost" ]] \
  || fail "a local start is not charged to the head's own name"
# A stale lock: the next try breaks it and the one after starts.
mkdir "${campaign_host_gate_root}/lift15"
mkdir "${campaign_host_gate_root}/lift15/lock"
touch -d '10 minutes ago' "${campaign_host_gate_root}/lift15/lock"
run_capturing_status campaign_host_try_start lift15
[[ "${status}" -eq 3 && ! -e "${campaign_host_gate_root}/lift15/lock" ]] \
  || fail "a lock a dead campaign left was not broken"
campaign_host_try_start lift15 || fail "the host stayed locked"
# A host whose memory stays unreadable past the ssh patience is the
# obligation's named failure; within it the slot waits (sshd refuses
# connections under a round's burst).
campaign_host_available_mb() { return 1; }
campaign_log() { printf '%s\n' "$*" >>"${memory_dir}/gate.log"; }
campaign_host_poll_s=0
campaign_ssh_patience_s=1
mkdir -p "${memory_dir}/queue"
run_capturing_status campaign_await_host_memory lift13 "${memory_dir}/queue" 1
[[ "${status}" -eq 2 ]] \
  || fail "an unreadable host admitted an obligation"
grep -q 'the memory of host lift13 could not be read for 1s' \
    "${memory_dir}/gate.log" \
  || fail "the unreadable host is not named: $(cat "${memory_dir}/gate.log")"
# Once every obligation of the wave is claimed there is nothing to wait for.
mkdir "${memory_dir}/queue/000000"
run_capturing_status campaign_await_host_memory lift13 "${memory_dir}/queue" 1
[[ "${status}" -eq 1 ]] \
  || fail "a slot kept waiting for room after the wave was all claimed"
unset -f hostname campaign_host_available_mb campaign_host_total_mb campaign_log
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

# HOSTS-7: a wave rotates the slot list, so the one-obligation waves of a
# campaign do not all start on the first host.
concolic_worker_count=2
campaign_worker_hosts="lift06 lift07 lift08"
[[ "$(campaign_worker_slot_hosts 4 | tr '\n' ' ')" \
    == "lift07 lift08 lift06 lift07 lift08 lift06 " ]] \
  || fail "the slot list does not start at its offset: \
$(campaign_worker_slot_hosts 4 | tr '\n' ' ')"
campaign_wave_slot() { printf '%s\n' "$1" >>"${memory_dir}/first-hosts"; }
campaign_wait_workers() { wait; }
for wave in 0 1 2 3 4 5; do
  campaign_dispatch_wave "${memory_dir}/campaign/obligations-000${wave}" \
    /dev/null /dev/null /dev/null /dev/null A
done
[[ "$(LC_ALL=C sort -u "${memory_dir}/first-hosts" | wc -l)" -ge 2 ]] \
  || fail "six one-obligation waves all started on one host: \
$(cat "${memory_dir}/first-hosts")"
unset -f campaign_wave_slot campaign_wait_workers
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
