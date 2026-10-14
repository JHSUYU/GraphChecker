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

# The charges standing in the ledger <root>, one name per line.
live_charges() {
  find "$1" -path '*/charges/*' -type f -printf '%f\n' 2>/dev/null
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
  # The one declared bound EMIT reads from the configuration (campaign_bounds).
  campaign_max_claims=8

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
        movedRootCategories:
          {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "HOOK"},
        witnessFindings: [{findingKind: "MARKER_FLIPPED",
          valuationOrdinal: 1, polarityDecides: true,
          movedRoots: {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"}}]}}}' \
    >"${composition_manifest}"
  # CONFIRM's answer for that SAT claim: the one replay agreed.  EMIT
  # requires it for every SAT_CANDIDATE and copies it into the result.
  jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: true,
    refutes: false,
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
      claim: "RUN_DEFECT",
      claimReason: "2 blocker(s) withhold an accepted claim from a REACHABLE solver result: TARGET_UNCONSTRAINED_BY_ROOTS,FINDING_MECHANISM_UNNAMED",
      blockerCount: 2,
      blockers: [
        {code: "TARGET_UNCONSTRAINED_BY_ROOTS", subject: "",
         detail: "no symbolic root flips the target predicate"},
        {code: "FINDING_MECHANISM_UNNAMED", subject: "NO_MECHANISM",
         detail: "no satisfying witness names a mechanism"}],
      whyNotAccepted: ("claim=RUN_DEFECT: 2 blocker(s) withhold acceptance\n  TARGET_UNCONSTRAINED_BY_ROOTS: no symbolic root flips the target predicate\n  FINDING_MECHANISM_UNNAMED [NO_MECHANISM]: no satisfying witness names a mechanism"),
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
  and .telemetryCount >= 2
  and .bounded == null
  and .confinedWriters == null' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the result lost its propagation provenance"

# CONFINED-1: the writers PLAN dropped as confined are DIAGNOSTIC rows of the
# region plan's gaps, which EMIT carries into gaps.json, and result.json
# counts them by owner class with the first rows (CHECKING trap 22).
emit_fixture
jq -n -c '{schemaVersion: 2, kind: "CONCOLIC_RUNTIME_MODEL_CATALOG",
  edges: [], regions: [],
  gaps: [{schemaVersion: 1, kind: "CLOSURE_CONFINED", cls: "DIAGNOSTIC",
          subject: "CONTEXT <a.B: int x> @ r1", detail: "3 writer(s)",
          scope: "CONTEXT", ownerClass: "a.B", field: "<a.B: int x>",
          reader: "r1", writers: 3, first: ["w1", "w2", "w3"]},
         {schemaVersion: 1, kind: "CLOSURE_CONFINED", cls: "DIAGNOSTIC",
          subject: "CONTEXT <a.C: int y> @ r1", detail: "2 writer(s)",
          scope: "CONTEXT", ownerClass: "a.C", field: "<a.C: int y>",
          reader: "r1", writers: 2, first: ["w4", "w5"]}]}' \
  >"${runtime_region_plan}"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a confined drop withheld the candidate: $(<"${emit_root}/emit.log")"
jq -e '.confinedWriters.writers == 5 and .confinedWriters.rows == 2
  and .confinedWriters.byOwnerClass == {"a.B": 3, "a.C": 2}
  and (.confinedWriters.first | length) == 2
  and .confinedWriters.first[0].first == ["w1", "w2", "w3"]
  and .gapCount == 0' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the confined drops were not published: \
$(jq -c '.confinedWriters' "${campaign_final}/result.json" 2>&1)"
jq -e '[.telemetryGaps[] | select(.code == "CLOSURE_CONFINED")] | length == 2' \
  "${campaign_final}/gaps.json" >/dev/null \
  || fail "the confined drops are not DIAGNOSTIC rows of gaps.json"

# BOUND-1: every declared bound that cut the search is named in result.json
# by its configuration key (campaign_bounds), whatever the claim -- a loop
# bound that cut the anchor's occurrence on the way to the throw too
# (COMPOSE's loop-body-bound row, RestsOn#decided), a store content leaf
# held past the daemon tick bound (COMPOSE's daemon-tick-bound row,
# Composer#arrival), a pairing hold that gave way past VIEW_HOLD_MAX (a
# replay's view-hold-max row, Confirmation#gaveWay -- a CONFIRM replay's
# too, witness or final), the invocations of one marker past those GROW plans
# inputs for (unplanned-input-max), the task bound by the static candidates it
# cut, the closure ceiling by the occurrences the rows connect cut past it; a round's
# max-flips-per-path, asked again by the next round, is none, nor is a
# closure an earlier round truncated and the last planned whole, nor paths an
# earlier round deferred (the path bound counts the last round's); and the flips,
# and the FORCE run (named FORCE), whose replays were killed past replay_timeout_s
# twice, the last round's boundedFlips (an earlier round's list is in the
# last's, which holds every one).
emit_fixture
mkdir -p "${campaign_final}/refuted/0000" "${campaign_final}/refuted/0001" \
  "${emit_iteration}/obligations-0000" "${emit_iteration}/obligations-0001"
campaign_max_claims=2
jq '.confirmed = false | .refutes = true' "${campaign_final}/confirm.json" \
  >"${campaign_final}/confirm.json.tmp"
mv "${campaign_final}/confirm.json.tmp" "${campaign_final}/confirm.json"
jq -n '{stop: "REGION_PATH_WAVE_BUDGET_REACHED", detail: "wave 3"}' \
  >"${emit_iteration}/exploration.json"
jq -n '{closureCut: {occurrences: 5, keptDepth: 1}}' \
  >"${emit_iteration}/runtime_workflow_schedule_index.json"
echo '{"truncated": 4, "boundedFlips": [{"siteId": "S#u9", "ordinal": 0, "outcome": false}]}' \
  >"${emit_iteration}/obligations-0000/explore_manifest.json"
echo '{"truncated": 3, "ceilingCut": 1, "boundedFlips": [{"siteId": "S#u9", "ordinal": 0, "outcome": false}, {"siteId": "S#u4", "ordinal": 1, "outcome": true}, {"siteId": "", "ordinal": 0, "outcome": false, "force": true}]}' \
  >"${emit_iteration}/obligations-0001/explore_manifest.json"
for subject in 'T max-paths-per-region=32' 'T max-world-depth=4' \
    'T max-flips-per-path=4' 'T pairing-bound=8' 'REGION.T#1 loop-body-bound=8' \
    'REGION.P#2 daemon-tick-bound=5'; do
  jq -n -c --arg subject "${subject}" '{schemaVersion: 1,
    sessionId: "SESSION.seed", kind: "ADMISSION_GAP", cls: "DIAGNOSTIC",
    subject: $subject, detail: "cut"}'
done >>"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
for round in 0000:U 0001:T; do
  jq -n -c --arg subject "${round#*:} max-paths-per-region=32" \
    '{schemaVersion: 1, sessionId: "exploration", kind: "ADMISSION_GAP",
      cls: "DIAGNOSTIC", subject: $subject, detail: "deferred"}' \
    >"${emit_iteration}/obligations-${round%:*}/gaps.jsonl"
done
# A pairing hold that gave way in a CONFIRM replay of the final stages.
mkdir -p "${campaign_final}/confirm/sessions/worker-1"
jq -n -c '{schemaVersion: 1, sessionId: "worker-1",
  kind: "BOUND_INSUFFICIENT", cls: "DIAGNOSTIC",
  subject: "VIEW/SOLR_ZK@n0#/a.json view-hold-max=3000", detail: "gave way"}' \
  >"${campaign_final}/confirm/sessions/worker-1/gaps.jsonl"
# A marker invocation past the ones GROW plans inputs for, in the last round.
jq -n -c '{schemaVersion: 1, sessionId: "exploration",
  kind: "UNPLANNED_INPUT", cls: "DIAGNOSTIC",
  subject: "TASK.T SYM.marker#5 unplanned-input-max=4", detail: "concrete"}' \
  >>"${emit_iteration}/obligations-0001/gaps.jsonl"
run_emit
jq -e '.bounded.by == ["region_path_max_waves",
    "region_path_max_paths_per_region", "region_path_max_world_depth",
    "pairing_flip_per_read", "loop_body_bound", "daemon_tick_bound",
    "view_hold_max", "unplanned_input_max",
    "region_path_max_tasks", "region_path_closure_ceiling", "replay_timeout_s",
    "schedule_max_jobs", "campaign_max_claims"]
  and (.bounded.detail | test("wave 3; the last round deferred 1 task.*without 2 static.*without 1 occ"))
  and (.bounded.detail | test("3 flip[(]s[)] whose replays were killed twice .* answered nothing, held open: FORCE, S#u4#1=true, S#u9#0=false"))
  and (.bounded.detail | test("1 pairing hold.*VIEW_HOLD_MAX [(]3000 ms"))' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "the declared bounds the search touched were not named: \
$(jq -c '.bounded' "${campaign_final}/result.json" 2>&1) $(<"${emit_root}/emit.log")"
# The fixture's claim confirmed again, its result the one the rows below
# read; a confirmed claim needs no claim bound.
rm -rf -- "${campaign_final}/refuted"
jq '.confirmed = true | .refutes = false' "${campaign_final}/confirm.json" \
  >"${campaign_final}/confirm.json.tmp"
mv "${campaign_final}/confirm.json.tmp" "${campaign_final}/confirm.json"
run_emit
# VIEW-HOLD-1: a pairing hold's bound in a replay is VIEW_HOLD_MAX times the
# VM's slowdown S -- the seed replay's window over the recording's, rounded
# up (campaign_view_hold_max) --, written to view_hold_max.tsv beside the
# iteration, where every replay below it finds it
# (campaign_view_hold_wall_ms).  A window its run ended inside (marked cut)
# is named in the file and the log; one that stated no duration fails the
# campaign by name: no bound is guessed.
view_hold_root="${test_tmp}/view-hold"
view_hold_iteration="${view_hold_root}/schedule/iteration-0000"
for missing in none cut recording seed; do
  rm -rf "${view_hold_root}"
  mkdir -p "${view_hold_root}/causynth/runtime" \
    "${view_hold_iteration}/seed-result/focused"
  [[ "${missing}" == recording ]] \
    || echo 1000 >"${view_hold_root}/causynth/runtime/window_ms"
  [[ "${missing}" == seed ]] \
    || printf '2500%s\n' "$([[ "${missing}" != cut ]] || printf '\tcut')" \
      >"${view_hold_iteration}/seed-result/focused/window_ms"
  view_hold_status=0
  ( causynth_output_dir="${view_hold_root}/causynth" view_hold_max_ms=3000
    campaign_view_hold_max "${view_hold_iteration}" ) \
    2>"${view_hold_root}/err.log" || view_hold_status=$?
  if [[ "${missing}" == cut ]]; then
    (( view_hold_status == 0 )) \
      && [[ "$(<"${view_hold_root}/schedule/view_hold_max.tsv")" \
        == $'3\t9000\tseed-replay' ]] \
      && grep -q 'the seed-replay window was cut' "${view_hold_root}/err.log" \
      || fail "a cut seed replay window was not named: \
$(cat "${view_hold_root}/schedule/view_hold_max.tsv" "${view_hold_root}/err.log" 2>&1)"
  elif [[ "${missing}" == none ]]; then
    (( view_hold_status == 0 )) \
      && [[ "$(<"${view_hold_root}/schedule/view_hold_max.tsv")" \
        == $'3\t9000\t' ]] \
      && [[ "$(campaign_view_hold_wall_ms \
        "${view_hold_iteration}/obligations-0000/worker")" == 9000 ]] \
      || fail "the view hold's bound was not VIEW_HOLD_MAX times S: \
$(cat "${view_hold_root}/schedule/view_hold_max.tsv" 2>&1)"
  else
    (( view_hold_status != 0 )) \
      && grep -q 'component=VIEW_HOLD_MAX' "${view_hold_root}/err.log" \
      && [[ ! -e "${view_hold_root}/schedule/view_hold_max.tsv" ]] \
      || fail "a ${missing} window with no duration did not fail by name: \
$(<"${view_hold_root}/err.log")"
  fi
done

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
  and .movedRoots == {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "true"}
  and .movedRootCategories
      == {"HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED": "HOOK"}' \
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

# An undecided root space is no witness and no verdict: the claim ClaimPolicy
# decided is published (RUN_DEFECT) with every named blocker and one readable
# summary, and the run exits 3 because it named defects.
emit_fixture_undecided_roots
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "an undecided root space was accepted (exit ${emit_status}): \
$(<"${emit_root}/emit.log")"
[[ $(jq -r '.claim' "${campaign_final}/result.json") == RUN_DEFECT ]] \
  || fail "the undecided root space did not publish RUN_DEFECT"
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

# DECISIVE-1: the formula decides, SAT or UNSAT.  An UNSAT formula is the
# verdict only where no stage named a defect: beside a BLOCKING row it
# publishes RUN_DEFECT, the formula's own claim and every defect named, and
# exits 3.  What the last EXPLORE round found decided on no symbol travels as
# information (concrete[]), never as a gap.
emit_unsat_fixture() {
  emit_fixture
  jq '.solver.campaignClaim += {claim: "UNSAT_CLOSED",
        claimReason: "every enumerated valuation is decided and unsat",
        findingKind: "NO_SUPPORTED_WITNESS", polarityDecides: false,
        valuationOrdinal: 0, movedRoots: {}, movedRootCategories: {},
        witnessFindings: []}' \
    "${composition_manifest}" >"${composition_manifest}.tmp"
  mv "${composition_manifest}.tmp" "${composition_manifest}"
  mkdir -p "${emit_iteration}/obligations-0000"
  jq -n '{concreteAnchors: [{anchor: "REGION.T#1", paths: 1, decided: 1,
    reads: 2, locations: ["INSTANCE/1#2"], offCone: 3}]}' \
    >"${emit_iteration}/obligations-0000/explore_manifest.json"
}
emit_unsat_fixture
jq -n -c '{schemaVersion: 1, sessionId: "SESSION.seed",
  kind: "ADMISSION_GAP", cls: "BLOCKING", subject: "REGION.T#1",
  detail: "only the seed replay ran this occurrence"}' \
  >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl"
run_emit
[[ "${emit_status}" -eq 3 ]] \
  || fail "an UNSAT formula beside a defect exited ${emit_status}: \
$(<"${emit_root}/emit.log")"
jq -e '.claim == "RUN_DEFECT" and .formulaClaim == "UNSAT_CLOSED"
  and .accepted == false
  and [.defects[].code] == ["ADMISSION_GAP"]
  and (.whyNotAccepted | startswith("RUN_DEFECT: the run named 1 defect"))
  and [.concrete[] | {kind, decided, reads, offCone}]
      == [{kind: "ANCHOR", decided: 1, reads: 2, offCone: 3}]' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an UNSAT formula beside a defect was not RUN_DEFECT: \
$(jq -c '{claim, formulaClaim, accepted, defects, concrete, whyNotAccepted}' \
    "${campaign_final}/result.json")"
grep -q 'no accepted verdict: claim=RUN_DEFECT (the formula UNSAT_CLOSED)' \
  "${emit_root}/emit.log" \
  || fail "EMIT did not name the defect run: $(<"${emit_root}/emit.log")"
# The same formula with no defect is the verdict, concrete anchor and all,
# and what COMPOSE held beside it (Composer.Concrete) travels too, with the
# refuted claims its unsat core names (restsOnRefutations).
emit_unsat_fixture
jq '.concrete = [{kind: "HELD", subject: "vh", value: "7",
      reason: "producer unstated: the attach names no producer",
      movesWith: [], pathId: "P1"}]
  | .solver.campaignClaim.restsOnRefutations = [{name: "refuted_claim__0",
      pathId: "P1", moved: {"ROOT.M": "true"}, reason: "WIRE e1"}]' \
  "${composition_manifest}" >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a defect-free UNSAT was not accepted: $(<"${emit_root}/emit.log")"
jq -e --arg formula "$(realpath --relative-to="${causynth_output_dir}" \
    "${campaign_final}/candidate.smt2")" \
  '.claim == "UNSAT_CLOSED" and .accepted == true and .defects == []
  and [.concrete[].kind] == ["ANCHOR", "HELD"]
  and .concrete[1].pathId == "P1"
  and [.restsOnRefutations[].name] == ["refuted_claim__0"]
  and .formula.path == $formula and ($formula | startswith("/") | not)
  and (.formula.sha256 | length) == 64' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "a defect-free UNSAT was not published as the verdict: \
$(jq -c '{claim, accepted, defects, concrete}' "${campaign_final}/result.json")"
# Every SAT excluded -- one a replay refuted, one no replay decided (CONFIRM
# refused it: PAIRING_UNHELD) -- and COMPOSE then answers UNSAT: the verdict
# is UNSAT_CLOSED with both exclusions listed (COMPOSE SAT -> CONFIRM
# <outcome> -> excluded -> UNSAT_CLOSED), never RUN_DEFECT for a refusal.
emit_unsat_fixture
printf '%s\n' \
  '{"kind":"REFUTED_CLAIM","model":{"pathId":"P1"},"outcome":"refuted","reason":"the run took an edge the model did not choose: WIRE e1"}' \
  '{"kind":"REFUTED_CLAIM","model":{"pathId":"P2"},"outcome":"undecided","reason":"CONFIRM refused: PAIRING_UNHELD: a view no publication hook publishes"}' \
  >"${emit_iteration}/refuted_claims.jsonl"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "an UNSAT after excluded claims was not accepted: \
$(<"${emit_root}/emit.log")"
jq -e '.claim == "UNSAT_CLOSED" and .accepted == true and .defects == []
  and [.refutedClaims[] | .outcome] == ["refuted", "undecided"]
  and (.refutedClaims[1].reason | contains("PAIRING_UNHELD"))' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an UNSAT after every SAT was excluded was not UNSAT_CLOSED with \
its exclusions: $(jq -c '{claim, defects, refutedClaims}' \
    "${campaign_final}/result.json")"
rm -f -- "${emit_iteration}/refuted_claims.jsonl"

# OPEN-ARM: an open decider arm no run took (ExploreMain#openArms) is named in
# concrete[]; only an UNSAT flip closes over it, and one whose flip came to no
# verdict leaves the UNSAT none (OPEN_ARM_UNANSWERED, campaign_open_arms).
for state in UNSAT UNANSWERED; do
  emit_unsat_fixture
  jq '.solver.unsatClosureComplete = true' "${composition_manifest}" \
    >"${composition_manifest}.tmp"
  mv "${composition_manifest}.tmp" "${composition_manifest}"
  jq --arg state "${state}" '.openArms = [{anchor: "REGION.T#1",
      siteId: "H#u2", outcome: true, state: $state, paths: {($state): 1},
      asked: ["H#u2@1"]}]' \
    "${emit_iteration}/obligations-0000/explore_manifest.json" \
    >"${emit_root}/manifest.tmp"
  mv "${emit_root}/manifest.tmp" \
    "${emit_iteration}/obligations-0000/explore_manifest.json"
  run_emit
  jq -e --arg state "${state}" '
    [.concrete[] | select(.kind == "OPEN_ARM") | .state] == [$state]
    and .evidence.unsatClosureComplete == ($state == "UNSAT")
    and .claim == (if $state == "UNSAT" then "UNSAT_CLOSED"
                   else "RUN_DEFECT" end)
    and ([.defects[].subject] | index("OPEN_ARM_UNANSWERED") != null)
        == ($state != "UNSAT")' \
    "${campaign_final}/result.json" >/dev/null \
    || fail "an open arm ${state} was not judged: \
$(jq -c '{claim, concrete, evidence, defects}' "${campaign_final}/result.json")"
done
# An open arm whose query was refused at the arm (ARM_REFUSED) is still open,
# by name, with the refusal on its defect.
emit_unsat_fixture
jq '.solver.unsatClosureComplete = true' "${composition_manifest}" \
  >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
jq '.openArms = [{anchor: "REGION.T#1", siteId: "H#u2", outcome: true,
    state: "UNANSWERED", paths: {UNANSWERED: 1}, asked: ["H#u2@1"],
    refused: ["the query was refused: ADMISSION_GAP:H#u2#1"]}]' \
  "${emit_iteration}/obligations-0000/explore_manifest.json" \
  >"${emit_root}/manifest.tmp"
mv "${emit_root}/manifest.tmp" \
  "${emit_iteration}/obligations-0000/explore_manifest.json"
run_emit
jq -e '.claim == "RUN_DEFECT"
  and ([.defects[] | select(.subject == "OPEN_ARM_UNANSWERED") | .detail]
       | any(contains("refused at the arm: the query was refused: ADMISSION_GAP:H#u2#1")))' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an arm refused at the arm closed silently: \
$(jq -c '{claim, defects}' "${campaign_final}/result.json")"

# SOLVER-TIMEOUT: an obligation the hard lane left undecided at the full
# budget (solver_timeouts.jsonl) is a SOLVER_TIMEOUT defect
# (campaign_solver_timeouts): no UNSAT closes over its arm.
emit_unsat_fixture
jq '.solver.unsatClosureComplete = true' "${composition_manifest}" \
  >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
jq -n -c '{obligationId: "OB.H", detail: "SOLVER_TIMEOUT after 1800000ms",
  host: "lift12"}' >"${emit_iteration}/solver_timeouts.jsonl"
run_emit
jq -e '.claim == "RUN_DEFECT"
  and ([.defects[] | select(.subject == "SOLVER_TIMEOUT")] | length == 1)' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an undecided hard ask was not a named defect: \
$(jq -c '{claim, defects}' "${campaign_final}/result.json")"
rm -f -- "${emit_iteration}/solver_timeouts.jsonl"

# A satisfiable formula no mechanism names (FORMULA_SAT) is a claim like any
# other: published as CONFIRM left it.
emit_fixture
jq '.solver.campaignClaim.findingKind = "FORMULA_SAT"' "${composition_manifest}" \
  >"${composition_manifest}.tmp"
mv "${composition_manifest}.tmp" "${composition_manifest}"
run_emit
[[ "${emit_status}" -eq 0 ]] \
  || fail "a confirmed FORMULA_SAT was not published: $(<"${emit_root}/emit.log")"
jq -e '.claim == "SAT_CANDIDATE" and .findingKind == "FORMULA_SAT"
  and .accepted == true' "${campaign_final}/result.json" >/dev/null \
  || fail "a confirmed FORMULA_SAT is not the verdict: \
$(jq -c '{claim, findingKind, accepted}' "${campaign_final}/result.json")"

# DECISIVE-2: triage reads the verdict: UNSAT (the concrete anchor as its
# reason), RUN_DEFECT (the first defect), CONFIRMED, REFUTED only where the
# confirmation refutes; no NO_ROOT or NO_WITNESS class is left.
triage_out="${test_tmp}/triage"
mkdir -p "${triage_out}"
printf '1\tcase-unsat\n2\tcase-defect\n3\tcase-sat\n4\tcase-refuted\n' \
  >"${triage_out}/sweep-T1-cases.tsv"
triage_case() {
  local dir="${triage_out}/accept-T1-$1/out/$2/schedule/final"
  mkdir -p "${dir}"
  printf 'case\texit\telapsed\tclaim\nx\t0\t9\t-\n' \
    >"${triage_out}/accept-T1-$1/summary.tsv"
  printf '%s\n' "$3" >"${dir}/result.json"
}
triage_case 1 case-unsat '{"claim": "UNSAT_CLOSED", "concrete": [{"kind":
  "ANCHOR", "decided": 1, "paths": 1, "reads": 2}],
  "restsOnRefutations": [{"name": "refuted_claim__0", "pathId": "P1"}],
  "bounded": {"by": ["region_path_max_waves", "schedule_max_jobs"],
    "detail": "wave 3"}}'
triage_case 2 case-defect '{"claim": "RUN_DEFECT", "defects": [{"code":
  "ADMISSION_GAP", "detail": "no session reached the declared occurrence"}]}'
triage_case 3 case-sat '{"claim": "SAT_CANDIDATE",
  "confirmation": {"confirmed": true}, "findingKind": "MARKER_FLIPPED"}'
triage_case 4 case-refuted '{"claim": "SAT_UNCONFIRMED",
  "confirmation": {"confirmed": false, "refutes": true, "reason": "WIRE e1"}}'
triage_rows=$(python3 "${repo}/tools/adhoc/triage.py" T1 "${triage_out}" \
  2>"${triage_out}/counts" | tr -d '\r' \
  | awk -F'\t' 'NR > 1 {print $2 "=" $3 "|" $8 "|" $NF}')
[[ "${triage_rows}" == "case-unsat=UNSAT|region_path_max_waves,schedule_max_jobs|rests on 1 refuted claim(s) P1; the anchor was decided on no symbol: 1 of 1 path(s) decided it, 2 read(s) demanded
case-defect=RUN_DEFECT||ADMISSION_GAP no session reached the declared occurrence
case-sat=CONFIRMED||
case-refuted=REFUTED||WIRE e1" ]] \
  && grep -q ' BOUNDED=1$' "${triage_out}/counts" \
  || fail "triage did not class the verdicts: ${triage_rows} \
$(<"${triage_out}/counts")"

# DECISIVE-3: report.py names a defect run's claim and its defects, and the
# concrete anchor beside an UNSAT, and passes neither.
report_case="${test_tmp}/report-case"
report_work="${test_tmp}/report-work"
mkdir -p "${report_case}/schedule/final" "${report_work}"
printf '%s\n' '{"claim": "RUN_DEFECT", "finalStatus": "FINAL_READY",
  "findingKind": "NO_SUPPORTED_WITNESS", "accepted": false,
  "concrete": [{"kind": "ANCHOR", "anchor": "REGION.T#1", "paths": 1,
    "decided": 1, "reads": 2, "locations": ["INSTANCE/1#2"], "offCone": 0}],
  "bounded": {"by": ["region_path_max_waves"], "detail": "wave 3"}}' \
  >"${report_case}/schedule/final/result.json"
printf '%s\n' '{"gaps": [{"stage": "EXPLORE", "code": "ADMISSION_GAP",
  "class": "BLOCKING", "subject": "REGION.T#1",
  "detail": "only the seed replay ran this occurrence"}]}' \
  >"${report_case}/schedule/final/gaps.json"
python3 "${repo}/experiments/accept/report.py" case-x "${report_case}" \
  "${report_work}" >/dev/null
awk -F'\t' '{exit !($4 == "RUN_DEFECT" && $6 == "1 BLOCKING" &&
  $11 == "FAIL" && index($12, "claim=RUN_DEFECT") > 0 &&
  index($13, "BOUNDED by region_path_max_waves") > 0)}' \
  "${report_work}/row.tsv" \
  || fail "report.py did not fail the defect run by name: \
$(<"${report_work}/row.tsv")"
grep -q '^## Defects' "${report_work}/report.md" \
  && grep -q '^\* `region_path_max_waves` -- wave 3$' \
    "${report_work}/report.md" \
  && grep -q 'anchor `REGION.T#1` decided on no symbol: 1 of 1 path(s)' \
    "${report_work}/report.md" \
  || fail "report.md did not name the defects and the concrete anchor: \
$(<"${report_work}/report.md")"
# The witness path's rows come first and are never cut; a FREE row is free
# (over-approximated), a HELD one held at its recorded value; the other
# paths' rows are cut at 20, their count stated.
jq -n '{claim: "SAT_CANDIDATE", valuationOrdinal: 1,
  valuations: [{ordinal: 1, selectedPathId: "P.w"}],
  concrete: ([range(25) | {kind: "HELD", subject: "r\(.)", value: "0",
      reason: "producer unstated: x", movesWith: [], pathId: "P.o"}]
    + [{kind: "FREE", subject: "w", value: "", reason: "moves",
      movesWith: ["ROOT.M"], pathId: "P.w"}])}' \
  >"${report_case}/schedule/final/result.json"
python3 "${repo}/experiments/accept/report.py" case-x "${report_case}" \
  "${report_work}" >/dev/null
awk '/^## Concrete/ {on = 1; next} on && /^\* / {print; exit}' \
    "${report_work}/report.md" \
  | grep -q '^\* free (over-approximated) `w` (moves with ROOT.M)' \
  && grep -q '^\* held at its recorded value `r0` = `0`' \
    "${report_work}/report.md" \
  && grep -q '^\* \.\.\. and 5 more' "${report_work}/report.md" \
  || fail "report.md did not put the witness path's rows first, or cut \
the others: $(<"${report_work}/report.md")"

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
# reads it (the host ledger).
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
# 52: `causynth_static_root` and `record_timeout_s` left with the batch
# campaign and the pre-screen: every campaign slices and records its own.
# 53: `recording_max_trace_mb` joined it: the most trace a recording may
# write before SEED ends it, RECORDING_BOUND.
# 54: `campaign_max_claims` joined it: how many times the final stages decide
# a claim again after CONFIRM refuted one.
# 53: `obligation_memory_mb` left: every replay after the seed's is charged
# the campaign's measured need (campaign_replay_need_mb); and
# `stream_max_in_flight` became `stream_shared_pool`: a sweep asks for a
# shared pool, and each exploration sizes its share from its measured need.
# 54: `reproduce_min_s` joined it: the least wall clock a native run is
# given, since a short recording says little of ten runs at once.
# 55: `view_hold_max_ms`, a pairing hold's realism bound in recorded time
# (runtime.Confirmation#publishing, campaign_view_hold_max).
# 56: `reproduce_charge_pct` joined it: a native run's memory charge, in
# percent of the recording's peak (110 native runs peaked at most 1.27x it).
[[ "$(print_normalized_config | wc -l)" -eq 56 ]] \
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
stop_after_config SEED
validate_config >/dev/null \
  || fail "campaign_stop_after=SEED is refused"
# A subshell body, because validate_config refuses by `die`, which exits.
stop_after_validate() (
  stop_after_config "$1"
  validate_config
)
run_capturing_status stop_after_validate EXPLORE \
  >/dev/null 2>"${stop_after_dir}/validate.err"
[[ "${status}" -ne 0 ]] \
  || fail "validate accepted an undeclared campaign_stop_after value"
grep -q 'campaign_stop_after must be empty, SEED or IMPORT: EXPLORE' \
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
stop_after_config SEED
: >"${stop_after_dir}/labels-seed.tsv"
stop_after_campaign "${stop_after_dir}/campaign-seed" \
  "${stop_after_dir}/labels-seed.tsv" \
  || fail "a campaign stopping after SEED did not exit 0"
[[ "$(tr '\n' ' ' <"${stop_after_dir}/labels-seed.tsv")" == \
    "PREFLIGHT FREEZE_TOOL FREEZE SEED " ]] \
  || fail "a campaign stopping after SEED ran past it: \
$(tr '\n' ' ' <"${stop_after_dir}/labels-seed.tsv")"
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
# and charged reproduce_charge_pct of the recording's peak memory -- in its
# placement and in the charge its watcher holds it to -- until it returns,
# naming the host it ran on, bounded by
# reproduce_time_factor times the recording's workload, at least
# reproduce_min_s, and answering for
# itself, per row of the plant, off its trace's plant rows; reproduce.json
# counts the answers (whole plant applied, fatal, at the anchor, reproduced:
# at the anchor with every root planted and every order held, an order
# unheld -- what it waited for came late, or never came --, an order still
# holding) and names the runs that stated none.  The plant holds the order
# of the session CONFIRM saw (final/confirm.json's sessionId).  A plant
# CONFIRM refuses, or a recording that measured no peak memory, is no run
# and the reason.  Per row: ConfirmMain's exit, the recording's peak MB, and
# the reproduction.
repro_dir="${test_tmp}/reproduce"
while IFS='|' read -r repro_plant repro_rss repro_expected; do
  rm -rf -- "${repro_dir}"
  mkdir -p "${repro_dir}/final"
  jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE"}}}' \
    >"${repro_dir}/manifest.json"
  jq -n '{confirmed: true, reason: "", sessionId: "sel"}' \
    >"${repro_dir}/final/confirm.json"
  mkdir -p "${repro_dir}/iteration/sessions/sel"
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
    reproduce_runs=5
    reproduce_time_factor=3
    reproduce_min_s=75
    reproduce_charge_pct=130
    campaign_recorded_workload_s=20
    campaign_recorded_workload_rss_mb=${repro_rss}
    # ConfirmMain --plant, holding the confirmed session's order: a root,
    # the model's order, an answer, a clock reading (a context row, applied
    # by nobody), the target's arm and the realized order's one edge, else
    # refused.
    run_java_main() {
      (( repro_plant == 0 )) || {
        echo "CONFIRM refused: NATIVE_PLANT_UNSUPPORTED: a clock"
        return "${repro_plant}"
      }
      local plant="" confirmed="" prev="" arg
      for arg; do
        [[ "${prev}" != --plant ]] || plant=${arg}
        [[ "${prev}" != --confirmed-session ]] || confirmed=${arg}
        prev=${arg}
      done
      [[ "${confirmed}" == "${repro_dir}/iteration/sessions/sel" ]] \
        || { echo "CONFIRM refused: not the session CONFIRM saw: \
${confirmed}"; return 1; }
      {
        echo '{"kind":"ROOT","category":"HOOK","rootId":"R","row":0}'
        echo '{"kind":"ORDER","before":"b|","after":"a|","row":1}'
        echo '{"kind":"ANSWER","endpoint":"e","row":2}'
        echo '{"kind":"CLOCK_SITE","row":3}'
        echo '{"kind":"TARGET","row":4}'
        jq -n -c '{kind: "ORDER", scope: "EVENT",
          before: {kind: "WAKE", context: "c", site: "s", k: 0},
          after: {kind: "RECV", context: "d", site: "r", k: 1}, row: 5}'
      } >"${plant}"
    }
    # Run n: 1 every row applied and the fatal at the anchor; 2 the model's
    # order unheld, what it waited for never came, and the fatal elsewhere;
    # 3 its root unwritten, its order still holding, its answer and the
    # realized order not reached, and the fatal at the anchor all the same
    # -- the program's own race, no reproduction; 4 every root planted and
    # the fatal at the anchor, but the realized order unheld, what it waited
    # for came late: another world than CONFIRM's, no reproduction; 5 no
    # trace.  Each states its bound, its order timeout and its charge, and
    # the ledger's row for it.
    run_configured_workload() {
      local run=$1 n=${1##*-}
      echo "$2 $4 $6 $(ls "${campaign_host_gate_root}/gate-head/charges" \
        | grep -c "^$4\\.")" >>"${repro_dir}/bounds"
      (( n < 5 )) || return 1
      {
        echo '{"event":"BRANCH"}'
        case ${n} in
          1) echo '{"event":"PLANT_APPLIED","row":0}'
             echo '{"event":"PLANT_APPLIED","row":1}'
             echo '{"event":"PLANT_APPLIED","row":2}'
             echo '{"event":"PLANT_APPLIED","row":5}' ;;
          2) echo '{"event":"PLANT_APPLIED","row":0}'
             echo '{"event":"PLANT_APPLIED","row":2}'
             echo '{"event":"PLANT_APPLIED","row":5}'
             echo '{"event":"PLANT_HOLDING","row":1}'
             echo '{"event":"PLANT_UNHELD","row":1}' ;;
          3) echo '{"event":"PLANT_UNWRITTEN","row":0}'
             echo '{"event":"PLANT_HOLDING","row":1}' ;;
          4) echo '{"event":"PLANT_APPLIED","row":0}'
             echo '{"event":"PLANT_APPLIED","row":1}'
             echo '{"event":"PLANT_APPLIED","row":2}'
             echo '{"event":"PLANT_HOLDING","row":5}'
             echo '{"event":"PLANT_UNHELD","row":5}'
             echo '{"event":"PLANT_LATE","row":5}' ;;
        esac
        jq -n -c --argjson at "$(( n != 2 ))" \
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
  [[ "${repro_expected}" != *'"runs":5'* \
      || "$(cut -d' ' -f1-3 "${repro_dir}/bounds" | sort -u)" \
        == "75 $(( repro_rss * 130 / 100 )) 37500" ]] \
    || fail "a native run was not bounded by reproduce_min_s=75 over 3 x the \
recording's 20 s, its orders held at most half of it, and held to its \
charge, 130 % of the recording's ${repro_rss} MB: $(cat "${repro_dir}/bounds")"
  [[ "${repro_expected}" != *'"runs":5'* \
      || "$(jq -c '[.unapplied[].why]' \
        "${repro_dir}/final/reproduce/run-3/answer.json")" \
        == '["UNWRITTEN","HOLDING","NOT_REACHED","NOT_REACHED"]' ]] \
    || fail "a run does not say why it did not apply a row: \
$(cat "${repro_dir}/final/reproduce/run-3/answer.json")"
  [[ "${repro_expected}" != *'"runs":5'* \
      || "$(jq -c '[.unapplied[] | [.planted, .why]] + [.ordersHeld,
          .rootsPlanted, .reproduced]' \
        "${repro_dir}/final/reproduce/run-4/answer.json")" \
        == '[["WAKE s @ c #0 -> RECV r @ d #1","LATE"],false,true,false]' ]] \
    || fail "a run that broke the confirmed order reproduced, or does not \
name the order: $(cat "${repro_dir}/final/reproduce/run-4/answer.json")"
  [[ "${repro_expected}" != *'"runs":5'* \
      || "$(awk '$4 < 1' "${repro_dir}/bounds")" == "" ]] \
    || fail "a native run ran uncharged: $(cat "${repro_dir}/bounds")"
  [[ "${repro_expected}" != *'"runs":5'* \
      || "$(cat "${repro_dir}"/final/reproduce/run-*/host.txt | sort -u)" \
        == gate-head ]] \
    || fail "a native run does not name the host it ran on"
  [[ -z "$(live_charges "${repro_dir}/hosts")" ]] \
    || fail "a native run's charge outlived it: \
$(live_charges "${repro_dir}/hosts")"
done <<'EOF'
0|2048|{"runs":5,"planted":1,"fatal":4,"atAnchor":3,"reproduced":1,"unheld":2,"unheldLate":1,"unheldMissing":1,"holding":1,"reason":""}
1|2048|{"runs":0,"planted":0,"fatal":0,"atAnchor":0,"reproduced":0,"unheld":0,"unheldLate":0,"unheldMissing":0,"holding":0,"reason":"no native run: NATIVE_PLANT_UNSUPPORTED: a clock"}
0||{"runs":0,"planted":0,"fatal":0,"atAnchor":0,"reproduced":0,"unheld":0,"unheldLate":0,"unheldMissing":0,"holding":0,"reason":"no native run: the recording measured no peak resident memory (workload_rss_mb) to charge one with"}
EOF

# REACHED-1: a replay reached its target when a session published a target
# row at a TARGET_SITE method of the scope map (any of them); no session, or
# rows of another method, is "".
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
# The recording's window, which the seed replay's scales the view hold's
# bound by (campaign_view_hold_max): every stub replay below states its own.
mkdir -p "${bound_dir}/causynth/runtime"
echo 1000 >"${bound_dir}/causynth/runtime/window_ms"
seed_bound() (
  causynth_output_dir="${bound_dir}/causynth"
  replay_timeout_s=$1 seed_replay_time_factor=$2
  campaign_recorded_workload_s=$3
  campaign_recorded_workload_rss_mb=100
  campaign_task_ids() { echo TASK.SEED; }
  campaign_log() { :; }
  campaign_replay() {
    printf '%s|%s\n' "${campaign_adapter_timeout_s}" \
      "${campaign_adapter_timeout_rule}"
    mkdir -p "$6"
    echo 300 >"$6/workload_rss_mb"
    echo 1500 >"$6/window_ms"
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

# REPLAY-NEED: the seed replay, before any replay of the campaign was
# measured, needs the recording's measured peak times
# campaign_replay_memory_factor (7); it is charged the recording's peak times
# campaign_seed_charge_factor (2), at least 512 MB, never more
# than half a host's ceiling (cap: CAUSYNTH_HOST_MAX_USED_PCT of this host's
# MemTotal, halved; campaign_replay_charge_mb), its replay JVM is held to
# that charge (CAUSYNTH_CHARGED_MB) and sized by the whole need
# (CAUSYNTH_HEAP_BASIS_MB, campaign_replay_heap_basis_mb), and its own peak
# is the campaign's first measured need (campaign_replay_need_mb).  A
# recording that measured no peak, or a seed replay that states none, fails
# REPLAY by name: there is no static charge to fall back to.  Per row: the
# recording's peak and the seed replay's (- none), the charge, the need, and
# the measured need after it (- refused).
need_cap=$(( $(awk '/^MemTotal:/ {print int($2 / 1024)}' /proc/meminfo) \
  * campaign_host_max_used_pct / 200 ))
while read -r need_rss need_peak need_expected need_whole need_after; do
  [[ "${need_rss}" != - ]] || need_rss=""
  [[ "${need_expected}" != cap ]] || need_expected=${need_cap}
  need_said=$(
    causynth_output_dir="${bound_dir}/causynth"
    campaign_recorded_workload_rss_mb=${need_rss}
    campaign_replay_peak_mb=0
    replay_timeout_s=2400 seed_replay_time_factor=40
    campaign_recorded_workload_s=10
    campaign_task_ids() { echo TASK.SEED; }
    campaign_log() { :; }
    campaign_head_charged() { printf 'charged=%s ' "$1"; shift; "$@"; }
    campaign_replay() {
      printf 'jvm=%s heap=%s' "$7" "${campaign_replay_heap_basis_mb}"
      mkdir -p "$6"
      rm -f -- "$6/workload_rss_mb"
      [[ "${need_peak}" == - ]] || echo "${need_peak}" >"$6/workload_rss_mb"
      echo 1500 >"$6/window_ms"
    }
    campaign_session_replay "${bound_dir}/seed-iteration" \
      2>"${bound_dir}/need.err"
    printf ' need=%s' "$(campaign_replay_need_mb)"
  ) || true
  if [[ "${need_after}" == - ]]; then
    grep -q "stage=REPLAY" "${bound_dir}/need.err" \
      && grep -q "reason=the \(recording\|seed replay\).* no peak" \
        "${bound_dir}/need.err" && [[ "${need_said}" != *need=* ]] \
      || fail "a seed replay with a '${need_rss}' MB recording and a \
'${need_peak}' MB peak was not refused by name: ${need_said} \
$(cat "${bound_dir}/need.err")"
    continue
  fi
  [[ "${need_said}" == "charged=${need_expected} jvm=${need_expected} \
heap=${need_whole} need=${need_after}" ]] \
    || fail "a seed replay of a '${need_rss}' MB recording peaking at \
${need_peak} MB is ${need_said}, not ${need_expected} MB sized by \
${need_whole} MB, then ${need_after} MB"
done <<'EOF'
300 400 600 2100 640
442 674 884 3094 1024
200 100 512 1400 512
99999 2003 cap 699993 3072
- 400 - - -
300 - 2100 2100 -
EOF

# MEASURED-NEED: every replay that returns -- an obligation's, a GROW
# re-run's, a CONFIRM's -- states its peak in its worker directory
# (workload_rss_mb, experiments/lib/execute.sh), and the campaign's need is
# the largest so far times 1.5, rounded up to 128 MB, at least 512 MB: it
# never falls, a worker that states none (its solver answered) leaves it,
# and it is said when it is first measured and whenever it moves.  Per row:
# the peaks in turn (- a worker that states none), the need after each, and
# how many times it was said.
measured_dir="${test_tmp}/measured"
while IFS='|' read -r measured_peaks measured_needs measured_said; do
  rm -rf -- "${measured_dir}"
  mkdir -p "${measured_dir}"
  measured_got=$(
    campaign_replay_peak_mb=0
    measured_n=0
    for measured_peak in ${measured_peaks}; do
      measured_n=$((measured_n + 1))
      mkdir -p "${measured_dir}/${measured_n}"
      [[ "${measured_peak}" == - ]] \
        || echo "${measured_peak}" >"${measured_dir}/${measured_n}/workload_rss_mb"
      campaign_replay_measured "${measured_dir}/${measured_n}" \
        >>"${measured_dir}/said"
      printf '%s ' "$(campaign_replay_need_mb)"
    done
  )
  [[ "${measured_got% }" == "${measured_needs}" \
     && "$(grep -c 'every replay from now on needs' "${measured_dir}/said")" \
       == "${measured_said}" ]] \
    || fail "peaks ${measured_peaks} gave the needs ${measured_got}, not \
${measured_needs}, said: $(cat "${measured_dir}/said")"
done <<'EOF'
674 662 715 2003 500|1024 1024 1152 3072 3072|3
171 - 300 400|512 512 512 640|2
- 238|512 512|1
EOF
# MEASURED-TYPICAL: once eight replays after the seed's returned, a replay of
# the stream is charged their 90th percentile times 1.25 (rounded up to 128
# MB, at least 512, at most the need), its heap still the need; before that,
# the need.  Per row: the seed's peak, the later peaks, the need and the
# stream's replay charge after them.
while IFS='|' read -r typical_seed typical_peaks typical_need typical_charge; do
  rm -rf -- "${measured_dir}"
  mkdir -p "${measured_dir}"
  typical_got=$(
    campaign_replay_peak_mb=0
    campaign_replay_peaks=()
    campaign_replay_typical_mb=0
    typical_n=0
    for typical_peak in ${typical_seed} ${typical_peaks}; do
      typical_n=$((typical_n + 1))
      mkdir -p "${measured_dir}/${typical_n}"
      echo "${typical_peak}" >"${measured_dir}/${typical_n}/workload_rss_mb"
      campaign_replay_measured "${measured_dir}/${typical_n}" >/dev/null 2>&1
    done
    printf '%s|%s' "$(campaign_replay_need_mb)" \
      "$(campaign_stream_charge_mb REPLAY)"
  )
  [[ "${typical_got}" == "${typical_need}|${typical_charge}" ]] \
    || fail "seed ${typical_seed} and peaks ${typical_peaks} gave \
${typical_got}, not ${typical_need}|${typical_charge}"
done <<'EOF'
2234|918 900 950 1000 880 1242 920 910|3456|1664
3454|1583 1600 1500|5248|5248
2234|300 310 320 330 340 350 360 370|3456|512
1000|900 950 1000 1100 1200 1300 1400 3000|4608|3840
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
# ledger promised other starts (a foreign live charge), and what it was
# granted is released when it ends.  A recording (charged nothing) is only
# measured: its peak is the trace's workload_rss_mb.  Per row: the host's
# MemAvailable, the MB a foreign live charge holds on the ledger (0: none),
# the charge, the JVM's resident memory at each read,
# whether it was ended, the most rows the ledger held for it, and what it
# says last.
watch_dir="${test_tmp}/watch"
while IFS='|' read -r watch_available watch_foreign watch_charged watch_rss \
    watch_ended watch_rows watch_said; do
  rm -rf -- "${watch_dir}"
  mkdir -p "${watch_dir}/trace" "${watch_dir}/hosts/gate-head/charges"
  printf '%s\n' ${watch_rss//,/ } >"${watch_dir}/rss"
  : >"${watch_dir}/rows"
  watch_foreign_row=""
  if (( watch_foreign > 0 )); then
    watch_foreign_row="${watch_foreign}.foreign"
    : >"${watch_dir}/hosts/gate-head/charges/${watch_foreign_row}"
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
      ls "${campaign_host_gate_root}/gate-head/charges" \
        | grep -vc '\.foreign$' >>"${watch_dir}/rows"
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
  [[ "$(ls "${watch_dir}/hosts/gate-head/charges")" \
      == "${watch_foreign_row}" ]] \
    || fail "what a JVM was granted outlived it, or a foreign charge went \
with it"
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

# RECORDING-END: a JVM with a trace directory (a recording; a native run,
# bound 0) is ended by its watcher, which says why beside the trace, the
# reason first (what SEED fails by): once its trace passes
# recording_max_trace_mb (RECORDING_BOUND), or once it wrote nothing there
# or on its output for campaign_unbounded_stall_s (RECORDING_STALLED); one
# that stays under its bound and keeps writing runs to its end and leaves no
# marker.  Per row: the bound in MB, the MB the "recording" writes, the
# seconds it then stays alive writing nothing, the stall bound, and the
# reason it is ended for (- for none).
while IFS='|' read -r bound_mb bound_writes bound_quiet bound_stall bound_ended; do
  bound_dir="${test_tmp}/bound"
  rm -rf -- "${bound_dir}"
  mkdir -p "${bound_dir}/trace"
  (
    campaign_watch_interval_s=0.1
    campaign_unbounded_stall_s=${bound_stall}
    ( for (( mb = 0; mb < bound_writes; mb++ )); do
        head -c 1048576 /dev/zero >>"${bound_dir}/trace/runtime_trace.jsonl"
        sleep 0.05
      done
      sleep "${bound_quiet}" ) &
    bound_jvm=$!
    campaign_watch_workload "${bound_jvm}" 0 "${bound_dir}/trace" \
      "${bound_mb}" 2>"${bound_dir}/said" &
    bound_watch=$!
    bound_exit=0
    wait "${bound_jvm}" 2>/dev/null || bound_exit=$?
    wait "${bound_watch}"
    echo "${bound_exit}" >"${bound_dir}/exit"
  ) || fail "a traced JVM's watch failed"
  if [[ "${bound_ended}" != - ]]; then
    [[ "$(cat "${bound_dir}/exit")" == 137 ]] \
      || fail "a traced JVM to be ended ${bound_ended} was not ended"
    grep -q "^${bound_ended}: " \
      "${bound_dir}/trace/${campaign_recording_end_marker}" \
      || fail "a traced JVM ended ${bound_ended} does not say so beside its \
trace: $(cat "${bound_dir}/trace/${campaign_recording_end_marker}" 2>&1)"
    grep -q "^causynth: ${bound_ended}: " "${bound_dir}/said" \
      || fail "a traced JVM ended ${bound_ended} does not say so on stderr"
  else
    [[ "$(cat "${bound_dir}/exit")" == 0 \
        && ! -e "${bound_dir}/trace/${campaign_recording_end_marker}" ]] \
      || fail "a traced JVM under its ${bound_mb} MB bound, quiet for \
${bound_quiet}s, was ended or marked"
  fi
done <<'EOF2'
2|40|1|600|RECORDING_BOUND
50|3|1|600|-
0|5|1|600|-
50|0|5|1|RECORDING_STALLED
0|1|5|1|RECORDING_STALLED
EOF2

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
      || [[ -n "$(live_charges "${solver_test}/hosts")" ]] || break
    sleep 1
  done
  [[ ! -e "${solver_home}/server" ]] \
    || fail "an idle solver did not end: $(cat "${solver_home}/server")"
  [[ -z "$(live_charges "${solver_test}/hosts")" ]] \
    || fail "an ended solver is still charged: \
$(live_charges "${solver_test}/hosts")"
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
  # Busy: a live solver that has not taken the question within
  # campaign_solver_busy_patience_s gives it up, 5, withdrawn from its queue.
  campaign_host_max_used_pct=100
  campaign_solver_busy_patience_s=1
  mkdir -p "${solver_test}/d"
  sleep 30 &
  busy_pid=$!
  printf '%s\n' "${busy_pid}" >"${solver_home}/server"
  started=${SECONDS}
  status=0
  campaign_solve_obligation OB.d "${solver_wave}/obligations.jsonl" \
    "${solver_test}/iteration/sessions" "${solver_test}/d" \
    >/dev/null 2>&1 || status=$?
  kill "${busy_pid}"
  rm -f -- "${solver_home}/server"
  [[ "${status}" -eq 5 && $(( SECONDS - started )) -lt 10 \
     && -z "$(ls "${solver_home}/requests")" ]] \
    || fail "a question behind a busy solver was not withdrawn (${status})"
)

# A question its host's solver could not answer (out of heap, died, ended at
# what its host could hold) is no answer: it is asked once more of a solver
# of its own at its corpus's solver heap, placed by that JVM's footprint and
# a question's z3 room (campaign_solver_need_mb: 2048 MB -> 2560 + 1152 MB),
# or by what the first held -- its watched peak with the usual margin, and the
# z3 room its peak does not count -- where that is more (killed: 1788 MB ->
# 2688 + 1152); a JVM that ran out of heap (3) doubles the corpus's solver
# heap first (4096 MB -> 4736 + 1152 MB); what other solvers of the corpus
# held places nothing (measured:
# 6000 MB in solver-lift12.log beside the corpus);
# a second failure, or no host with the room, fails the worker by name -- an
# unfinished obligation (campaign_obligation_unfinished) -- never a bare
# NOT_ADMITTED (hdfs-17960 fast1: 29 of 35 obligations "answered" by an
# OutOfMemoryError).  Neither settles its question.  A question whose host
# had no room for its solver (3) is answered at once in a solver JVM of its
# own under the obligation's charge when that covers the JVM's need, else
# placed by it (warm: a question's 1152 MB).  Per row: the case, and the need
# the second ask is placed by.
retry_test=${test_tmp}/solver-retry
while read -r alone retry_need; do
  mkdir -p "${retry_test}/${alone}"
  [[ "${alone}" != measured ]] || printf 'causynth: the workload JVM'"'"'s \
resident memory peaked at 6000 MB; its host was charged 1024 MB\n' \
    >"${retry_test}/${alone}/solver-lift12.log"
  retry_status=0
  retry_charged=${campaign_solver_start_mb}
  [[ "${alone}" != warm ]] || retry_charged=${campaign_question_mb}
  (
    campaign_solve_obligation() {
      [[ "${alone}" != noroom && "${alone}" != killed && "${alone}" != heap \
         && "${alone}" != warm ]] || return 3
      : >"$4/question.asked"
      echo "ObligationSolverMain: java.lang.OutOfMemoryError: Java heap space" >&2
      return 1
    }
    campaign_solve_obligation_alone() {
      [[ "$5" == "${campaign_solver_start_mb}" ]] \
        || { echo "not asked at once" >&2; return 1; }
      [[ "${alone}" != killed ]] || { campaign_watch_peak_mb=1788; return 1; }
      if [[ "${alone}" == heap ]]; then
        campaign_solver_outgrown "$3" "$(campaign_solver_heap_mb "$3")"
        return 3
      fi
      printf '{"verdict":"UNSAT","obligationId":"OB.1"}\n' \
        >"$4/obligation_result.jsonl"
      printf '(assert false)\n' >"$4/obligation_query.smt2"
    }
    campaign_solve_obligation_placed() {
      if [[ "${alone}" == ladder ]]; then
        printf '%s ' "$5" >>"${retry_test}/ladder/needs"
        if [[ "$(campaign_solver_heap_mb "$3")" -lt 8192 ]]; then
          campaign_solver_outgrown "$3" "$(campaign_solver_heap_mb "$3")"
          return 3
        fi
        set -- "$1" "$2" "$3" "$4" "${retry_need}"
      fi
      [[ "$5" == "${retry_need}" ]] \
        || { echo "placed at $5 MB, not ${retry_need}" >&2; return 1; }
      [[ "${alone}" != nohost ]] \
        || { campaign_host_wait_reason="no host of the pool has $5 MB"; return 4; }
      [[ "${alone}" != fails ]] || { echo "the second one died" >&2; return 1; }
      printf '{"verdict":"UNSAT","obligationId":"OB.1"}\n' \
        >"$4/obligation_result.jsonl"
      printf '(assert false)\n' >"$4/obligation_query.smt2"
    }
    campaign_obligation_worker OB.1 obligations \
      "${retry_test}/${alone}/sessions" "${retry_test}/${alone}" \
      "${retry_charged}"
  ) >"${retry_test}/${alone}.log" 2>"${retry_test}/${alone}/stderr.log" \
    || retry_status=$?
  [[ "${alone}" != ladder \
     || "$(cat "${retry_test}/ladder/needs")" == "3712 5888 10240 " ]] \
    || fail "a retry out of heap did not climb 2, 4 and 8 GB: \
$(cat "${retry_test}/ladder/needs")"
  [[ "${alone}" != heap \
     || "$(cat "${retry_test}/heap/solver_heap_mb" 2>/dev/null)" == 4096 ]] \
    || fail "a solver out of its 2048 MB heap did not double its corpus's \
(${retry_test}/heap/solver_heap_mb)"
  [[ ! -e "${retry_test}/${alone}/question.asked" ]] \
    || fail "a solver that failed settled a question"
  case "${alone}" in
    fails|nohost)
      [[ "${retry_status}" -ne 0 && ! -e \
          "${retry_test}/${alone}/obligation_result.jsonl" ]] \
        || fail "a question no solver answered was given an answer" ;;
    *)
      [[ "${retry_status}" -eq 0 && "$(jq -r .verdict \
          "${retry_test}/${alone}/obligation_result.jsonl")" == UNSAT ]] \
        || fail "the second solver's answer is not the obligation's \
(${alone}): $(cat "${retry_test}/${alone}/stderr.log")" ;;
  esac
  case "${alone}" in
    fails) grep -q 'Error: obligation OB.1: its solver failed twice.*the second one died' \
        "${retry_test}/fails/stderr.log" \
      || fail "the unfinished worker does not say why: \
$(cat "${retry_test}/fails/stderr.log")" ;;
    nohost) grep -q "Error: obligation OB.1: its solver did not answer, and no \
host has room for a solver of its own of 3712 MB (the first ran in its host's \
solver, unwatched).*no \
host of the pool has 3712 MB" "${retry_test}/nohost/stderr.log" \
      || fail "a second ask no host could hold does not fail by name: \
$(cat "${retry_test}/nohost/stderr.log")" ;;
  esac
done <<'EOF_RETRY'
answers 3712
fails 3712
noroom 3712
killed 3840
nohost 3712
measured 3712
heap 5888
warm 3712
ladder 10240
EOF_RETRY

# SOLVER-HEAP: a corpus's solvers start at campaign_solver_start_heap_mb, and
# each out-of-heap exit doubles the next one's heap, up to the engine heap,
# never below what another solver of the corpus already outgrew; a solver JVM
# is charged its heap's footprint and a question's z3 room (1152 MB).  Per
# row: the engine heap, the heaps the
# corpus's solvers ran out of, in order, and the heap and charge after.
solver_heap_dir=${test_tmp}/solver-heap
while IFS='|' read -r sh_engine sh_outgrown sh_heap sh_need; do
  rm -rf -- "${solver_heap_dir}"
  mkdir -p "${solver_heap_dir}/sessions"
  sh_said=$(
    engine_memory_mb=${sh_engine}
    for sh_out in ${sh_outgrown}; do
      campaign_solver_outgrown "${solver_heap_dir}/sessions" "${sh_out}"
    done
    printf '%s %s' "$(campaign_solver_heap_mb "${solver_heap_dir}/sessions")" \
      "$(campaign_solver_need_mb "${solver_heap_dir}/sessions")"
  )
  [[ "${sh_said}" == "${sh_heap} ${sh_need}" ]] \
    || fail "engine ${sh_engine}, outgrown [${sh_outgrown}]: ${sh_said}, not \
${sh_heap} ${sh_need}"
done <<'EOF_HEAP'
16384||2048|3712
16384|2048|4096|5888
16384|2048 4096 8192|16384|18944
6144|2048 4096|6144|8064
1024||1024|2624
16384|4096 2048|8192|10240
EOF_HEAP

# SOLVE-LANES-WORKER: a first ask goes to its host's solver (at the first
# budget, campaign_solver_first_ms); one its host had no room for (3) or whose
# solver stayed busy past its patience (5) is asked alone at that budget; a
# HARD ask never goes to the host's solver: alone, at the full budget and the
# hard lane's z3 room, under its start's charge (campaign_stream_charge_mb
# HARD).  Per row: the lane, what the host's solver returns, and every ask
# made: its charge, budget and z3 room.
lanes_worker=${test_tmp}/lanes-worker
while IFS='|' read -r wl_lane wl_service wl_asks; do
  wl_dir="${lanes_worker}/${wl_lane:-first}${wl_service}"
  mkdir -p "${wl_dir}"
  wl_said=$(
    solver_timeout_ms=1800000
    campaign_solver_first_tier_ms=60000
    campaign_log() { :; }
    lanes_answer() {
      printf '{"verdict":"UNSAT","obligationId":"OB.1"}\n' \
        >"$1/obligation_result.jsonl"
      printf '(assert false)\n' >"$1/obligation_query.smt2"
    }
    campaign_solve_obligation() {
      printf 'service,' >>"$4/asked"
      [[ "${wl_service}" != 0 ]] || lanes_answer "$4"
      return "${wl_service}"
    }
    campaign_solve_obligation_alone() {
      printf 'alone %s at %s in %s,' "$5" "$6" "$7" >>"$4/asked"
      lanes_answer "$4"
    }
    sessions="${wl_dir}/sessions"
    campaign_obligation_worker OB.1 obligations "${wl_dir}/sessions" \
      "${wl_dir}" "$(campaign_stream_charge_mb \
        "$([[ -n "${wl_lane}" ]] && echo "${wl_lane}" || echo OBLIGATION)" \
        cold)" ${wl_lane} >/dev/null 2>&1 \
      || echo "failed,"
    cat "${wl_dir}/asked"
  )
  [[ "${wl_said}" == "${wl_asks}" ]] \
    || fail "lane '${wl_lane}', service ${wl_service}: ${wl_said}, not ${wl_asks}"
done <<'EOF_LANES'
|0|service,
|3|service,alone 3712 at 60000 in 1152,
|5|service,alone 3712 at 60000 in 1152,
HARD|0|alone 6656 at 1800000 in 4096,
EOF_LANES

# SOLVER-PLACED: a solver asked again goes to the pool's host with the most
# room for its need (MemAvailable less the 30000 MB reserve of a 100000 MB
# host), charged there while it runs and released after: here, or a peer
# (--run-placed, from a directory under the worker).  No host with the room
# within campaign_solver_place_patience_s: 4, at once, nothing started.  Per
# row: the head's, lift14's and lift15's MemAvailable, the need, and where it
# runs (none: 4).
placed_dir=${test_tmp}/solver-placed
while read -r placed_own placed_14 placed_15 placed_need placed_expected; do
  rm -rf -- "${placed_dir}"
  mkdir -p "${placed_dir}/worker"
  (
    campaign_host_gate_root="${placed_dir}/hosts"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_worker_hosts="gate-head lift14 lift15"
    campaign_host_total_mb() { echo 100000; }
    campaign_host_available_mb() {
      case "$1" in
        lift14) echo "${placed_14}" ;;
        lift15) echo "${placed_15}" ;;
        *) echo "${placed_own}" ;;
      esac
    }
    campaign_host_max_used_pct=70
    campaign_host_poll_s=0
    campaign_solver_place_patience_s=0
    campaign_solve_obligation_alone() {
      printf 'gate-head %s %s\n' "$5" "$(live_charges "${campaign_host_gate_root}" \
        | grep -c "^$5\\.")" >"${placed_dir}/ran"
    }
    campaign_run_placed() {
      [[ "${campaign_root}" == "${placed_dir}/worker" ]] \
        || fail "a peer's placed directory is not under its worker"
      printf '%s %s %s\n' "$1" "$7" "$(live_charges "${campaign_host_gate_root}" \
        | grep -c "^$7\\.")" >"${placed_dir}/ran"
    }
    run_capturing_status campaign_solve_obligation_placed OB.1 obligations \
      sessions "${placed_dir}/worker" "${placed_need}" 60000 1152
    if [[ "${placed_expected}" == none ]]; then
      [[ "${status}" -eq 4 && ! -e "${placed_dir}/ran" ]] \
        || fail "a need no host holds was placed (${status})"
    else
      [[ "${status}" -eq 0 && "$(cat "${placed_dir}/ran")" \
          == "${placed_expected} ${placed_need} 1" ]] \
        || fail "a solver of ${placed_need} MB with ${placed_own}/${placed_14}/\
${placed_15} MB available ran as $(cat "${placed_dir}/ran" 2>/dev/null), not on \
${placed_expected} charged once"
    fi
    [[ -z "$(live_charges "${campaign_host_gate_root}")" ]] \
      || fail "a placed solver's charge outlived it"
  ) || exit 1
done <<'EOF_PLACED'
31000 34000 36000 2688 lift15
47000 34000 36000 2688 gate-head
31000 36000 35500 2688 lift14
31000 31000 31000 2688 none
EOF_PLACED

# REPLAY-BOUND-3: what one obligation whose replay never returns records.
# The same terminal NOT_ADMITTED row the worker writes for a solver that
# failed -- one obligation's own answer, never the wave's death -- naming the
# bound it exceeded.  The REPLAY must also RETURN, which is the whole point:
# the wave barrier waited on the hung one forever.  Each replay below runs
# as the pool's REPLAY start does (campaign_stream_start), on what its
# solver left in its worker (bound_solved): the SAT_MODEL_READY row, the
# focus row and the query.
bound_solved() {
  jq -n -c --arg id "$2" '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
    obligationId: $id, verdict: "SAT_MODEL_READY", sessionId: "",
    detail: ""}' >"$1/obligation_result.jsonl"
  printf '{"taskId":"TASK.1"}\n' >"$1/focused_task.jsonl"
  printf '(assert true)\n' >"$1/obligation_query.smt2"
}
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
bound_solved "${worker_dir}" OB.1
bound_inode=$(stat -c %i "${worker_dir}/obligation_result.jsonl")
(
  campaign_obligation_replay OB.1 "${bound_dir}/classes" "${worker_dir}" \
    "${worker_dir}/sessions" "${bound_dir}/seed_plan.jsonl" 1024 1024
) >"${worker_dir}/worker.log" 2>&1 \
  || fail "the worker did not return when its replay outlived the bound: \
$(cat "${worker_dir}/worker.log")"
# The answer replaces the solver's row as a new inode, never in place: the
# REPLAY runs on another host than the solve, whose NFS client may hold the
# old row (campaign_write_whole).
[[ "$(stat -c %i "${worker_dir}/obligation_result.jsonl")" != "${bound_inode}" \
   && ! -e "${worker_dir}/obligation_result.jsonl.part" ]] \
  || fail "the replay's answer was written over the solver's row in place"
[[ "$(jq -r '.verdict' "${worker_dir}/obligation_result.jsonl")" \
    == NOT_ADMITTED ]] \
  || fail "a replay killed on its bound did not record NOT_ADMITTED: \
$(cat "${worker_dir}/obligation_result.jsonl")"
[[ "$(jq -r '.detail' "${worker_dir}/obligation_result.jsonl")" \
    == "REPLAY_BOUNDED: replay exceeded replay_timeout_s=1" ]] \
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
bound_solved "${worker_dir}" OB.2
(
  campaign_obligation_replay OB.2 "${bound_dir}/classes" "${worker_dir}" \
    "${worker_dir}/sessions" "${bound_dir}/seed_plan.jsonl" 1024 1024
) >"${worker_dir}/worker.log" 2>&1 \
  || fail "the worker did not return when its replay was killed: \
$(cat "${worker_dir}/worker.log")"
[[ "$(jq -r '.verdict + " " + .detail' \
    "${worker_dir}/obligation_result.jsonl")" \
    == "NOT_ADMITTED REPLAY_BOUNDED: replay was killed (exit 137) after "*"s, inside its 60s bound: by its memory reservation (the replay log says so), the kernel's memory killer or an operator" ]] \
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
bound_solved "${withdraw_worker}" OB.1
(
  campaign_obligation_replay OB.1 "${withdraw_dir}/classes" \
    "${withdraw_worker}" "${withdraw_worker}/sessions" \
    "${withdraw_dir}/seed_plan.jsonl" 1024 1024
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
    == "REPLAY_BOUNDED: replay exceeded replay_timeout_s=5" ]] \
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
    == "NOT_ADMITTED REPLAY_BOUNDED: replay exceeded replay_timeout_s=4" ]] \
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
  "${refused_worker}" peer OB.R "${refused_worker}/sessions" \
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
# A file gone between the walk and its hash (a JVM attach's .attach_pid<pid>)
# is no part of the state; one still there that cannot be read fails it.
printf 'transient\n' >"${checkout_repo}/.attach_pid1"
sha256sum() {
  [[ "${2:-}" != *.attach_pid1 ]] || rm -f -- "$2"
  command sha256sum "$@"
}
campaign_checkout_state "${checkout_repo}" >/dev/null \
  || fail "CHECKOUT-STATE-2: a file gone before its hash failed the digest"
unset -f sha256sum
printf 'locked\n' >"${checkout_repo}/locked.txt"
chmod 000 "${checkout_repo}/locked.txt"
! campaign_checkout_state "${checkout_repo}" >/dev/null 2>&1 \
  || fail "CHECKOUT-STATE-2: an unreadable file was left out of the digest"
rm -f -- "${checkout_repo}/locked.txt"
# STREAM: EXPLORE is one streaming loop (PIPELINE §7.7, §7.9).  The planner,
# the worker, the gate and COMPOSE are stubbed -- each stands where its JVM
# stands (the planner's: its service's loop, stream_planner_serve) -- and
# everything between them is the production loop: the queue, the ledger's
# admission, landing, the head's steps, the planner service's start, its
# questions and its ends, rounds and their in-flight rows, the stops.
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
  engine_memory_mb=1
  causynth_static_scope_map=""
  causynth_root_domains=""
  declared_target_occurrence=""
  campaign_host_poll_s=1
  campaign_adapter_kill_grace_s=1
  # Where the planner's questions wait (campaign_planner_dir).
  TMPDIR=${test_tmp}
}
# Where explore.ExploreMain --serve stands (campaign_planner_serve <heap>
# <id> <peak> <log> <jvm_file> <args...>): it names itself where its rounds
# are asked and answers each with stream_planner, over the corpus and the
# answers the question names, until it is ended -- or until
# stream_planner_dies <round> <heap> says it ends there with that status
# (3: out of heap, its JVM's last words in its log).
stream_planner_serve() {
  local heap=$1 id=$2 log=$4 sessions="" dir request name round status
  printf '%s\n' "${BASHPID}" >"$5"
  shift 5
  while [[ $# -gt 0 ]]; do
    [[ "$1" != --sessions ]] || sessions=$2
    shift
  done
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  mkdir -p "${dir}/requests" "${dir}/answers"
  printf '%s\n' "${heap}" >>"${stream_dir}/planner-heaps.txt"
  printf '%s\n' "${BASHPID}" >"${dir}/server"
  while true; do
    for request in "${dir}"/requests/*.json; do
      [[ -e "${request}" ]] || continue
      name=$(basename "${request}" .json)
      mv -- "${request}" "${dir}/requests/${name}.taken"
      round=$(jq -r '.round' "${dir}/requests/${name}.taken")
      status=$(stream_planner_dies "${round}" "${heap}")
      if [[ -n "${status}" ]]; then
        echo "Terminating due to java.lang.OutOfMemoryError: Java heap \
space" >>"${log}"
        rm -rf -- "${dir}/requests" "${dir}/answers"
        return "${status}"
      fi
      stream_planner --round "${round}" --output-dir "$(jq -r '.outputDir' \
        "${dir}/requests/${name}.taken")" --in-flight "$(jq -r '.inFlight' \
        "${dir}/requests/${name}.taken")" --corpus "$(jq -r '.corpus // ""' \
        "${dir}/requests/${name}.taken")" --results "$(jq -r \
        '.results // ""' "${dir}/requests/${name}.taken")"
      printf '{"exit":0,"error":""}\n' >"${dir}/answers/${name}.part"
      mv -- "${dir}/answers/${name}.part" "${dir}/answers/${name}.json"
      rm -f -- "${dir}/requests/${name}.taken"
    done
    sleep 0.1
  done
}
stream_planner_dies() { :; }

# The planner's JVM is stopped by the pid it stated, on its host, whatever
# still holds it (SG2: peers' planners outlived their campaigns by 75-105
# minutes); a pid the host gave another process since is left alone.
(
  iteration_dir="${test_tmp}/planner-stop"
  mkdir -p "${iteration_dir}/planner"
  printf 'localhost\n' >"${iteration_dir}/planner/host"
  printf '1791\n' >"${iteration_dir}/planner/id"
  bash -c 'exec -a "ExploreMain --serve x.1791" sleep 600' &
  served=$!
  printf '%s\n' "${served}" >"${iteration_dir}/planner/jvm"
  sleep 600 &
  stranger=$!
  campaign_planner_stop
  sleep 0.2
  ! kill -0 "${served}" 2>/dev/null \
    || fail "campaign_planner_stop left the planner JVM it stated running"
  [[ ! -e "${iteration_dir}/planner/jvm" ]] \
    || fail "campaign_planner_stop kept the planner JVM's pid"
  printf '%s\n' "${stranger}" >"${iteration_dir}/planner/jvm"
  campaign_planner_stop
  kill -0 "${stranger}" 2>/dev/null \
    || fail "campaign_planner_stop ended a process not named by its id"
  kill "${stranger}"
)
# Where explore.ExploreMain stands: the files it states every round, and
# what it read -- the sessions its corpus names, the answers it was handed.
stream_planner() {
  local round="" out="" flying="" corpus="" answers=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --round) round=$2; shift 2 ;;
      --output-dir) out=$2; shift 2 ;;
      --in-flight) flying=$2; shift 2 ;;
      --corpus) corpus=$2; shift 2 ;;
      --results) answers=$2; shift 2 ;;
      *) shift ;;
    esac
  done
  jq -r '.obligationId' "${flying}" | LC_ALL=C sort | paste -sd ' ' - \
    >"${out}/in-flight.txt"
  [[ ! -f "${corpus}" ]] || paste -sd ' ' - <"${corpus}" >"${out}/read.txt"
  [[ ! -f "${answers}" ]] || jq -r '.obligationId' "${answers}" \
    | LC_ALL=C sort | paste -sd ' ' - >"${out}/answers-read.txt"
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
# What ComposeMain publishes beside <manifest>: the claim <claim>
# (CLOCK_SKEW, its polarity deciding) and a model selecting the path of
# <path> -- by default the attempt's first witness, so attempts at other
# witnesses claim other models.
stream_compose() {
  local manifest=$1 claim=$2 path=${3:-}
  jq -n --arg claim "${claim}" '{solver: {campaignClaim: {claim: $claim,
    findingKind: "CLOCK_SKEW", polarityDecides: true}}}' >"${manifest}"
  [[ -n "${path}" ]] || path=$(head -n 1 "${stream_dir}/steps/$(ls \
    "${stream_dir}/steps" | LC_ALL=C sort | tail -n 1)/witnesses")
  jq -n --arg path "${path}" '{claim: {kind: "CLOCK_SKEW",
    valuationOrdinal: 0, movedRoots: {}},
    valuations: [{ordinal: 0, selectedPathId: $path}]}' \
    >"$(dirname "${manifest}")/claim.json"
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
  campaign_planner_serve() { stream_planner_serve "$@"; }
  # Where CONFIRM stands.  Its task planned: a verdict now where
  # stream_realize names the attempt (its selected session is the run),
  # else the replay owed.  The replay, a job of the pool: what it was handed,
  # stream_confirm_sleep seconds long.  Its verdict: confirmed, unless
  # stream_refute names the attempt.
  campaign_confirm_plan() {
    mkdir -p "$3/worker" "$3/sessions"
    [[ " ${stream_realize:-} " != *" $(basename "$2") "* ]] \
      || campaign_confirm_verdict true "realized" "" false >"$2/confirm.json"
  }
  campaign_confirm_replay() {
    printf '%s\n' "$2" >"$1/classes.txt"
    date +%s.%N >"$1/replay-started-at"
    sleep "${stream_confirm_sleep:-0}"
    date +%s.%N >"$1/replay-ended-at"
    jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
      obligationId: "CONFIRM", verdict: "ADMITTED", sessionId: "",
      detail: "stub"}' >"$1/worker/obligation_result.jsonl"
  }
  campaign_confirm_decide() {
    local confirmed=true refutes=false
    if [[ " ${stream_refute:-} " == *" $(basename "$1") "* ]]; then
      confirmed=false
      refutes=true
    fi
    campaign_confirm_verdict "${confirmed}" "stub" "" "${refutes}" \
      >"$1/confirm.json"
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
[[ "$(cat "${stream_dir}/obligations-0001/read.txt")" == SESSION.SHORT \
    && "$(cat "${stream_dir}/obligations-0001/corpus.txt")" == SESSION.SHORT \
    && "$(cat "${stream_dir}/obligations-0001/answers-read.txt")" \
       == *SHORT* ]] \
  || fail "round 1 did not read the corpus and the answers landed as it \
started: $(cat "${stream_dir}/obligations-0001/read.txt" \
"${stream_dir}/obligations-0001/answers-read.txt")"
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
[[ -z "$(live_charges "${campaign_host_gate_root}/$(hostname -s)")" ]] \
  || fail "an obligation's charge outlived its return: \
$(live_charges "${campaign_host_gate_root}/$(hostname -s)")"

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
  # The accepted claim's selected session is the run: decided in its step.
  stream_realize=0001
  do_compose() {
    local claim=UNSAT_CLOSED
    date +%s.%N >>"${stream_dir}/attempt-started-at"
    sleep 2
    [[ ! -d "${compose_sessions_dir}/SESSION.C" ]] || claim=SAT_CANDIDATE
    stream_compose "${composition_manifest}" "${claim}"
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
    stream_compose "${composition_manifest}" SAT_CANDIDATE
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

# STREAM-2c: THE CONFIRMATION IS A JOB OF THE POOL.  An accepted attempt's
# replay runs outside the head's steps: while it runs, what returns lands and
# the round it owes is planned (N's session, round 1).  Its verdict, landed,
# ends the exploration, and the corpus COMPOSE reads next is the one the
# attempt composed: N's session, landed after it, leaves for
# explore-reaped/after-witness/.  The replay stands on the generation's tree.
stream_fixture stream-2c
(
  stream_stubs
  stream_confirm_sleep=4
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" A N ;;
      *) date +%s.%N >>"${stream_dir}/round-planned-at" ;;
    esac
  }
  do_compose() {
    stream_compose "${composition_manifest}" SAT_CANDIDATE
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    case "${id}" in
      A) stream_answer "${worker}" A ADMITTED SESSION.A fatal ;;
      N) sleep 1; stream_answer "${worker}" N ADMITTED SESSION.N ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the confirming loop did not finish: \
$(cat "${stream_dir}/explore.log")"
stream_confirm="${campaign_root}/witness-confirm/0000"
jq -e '.stop == "WITNESSED" and .afterWitness == ["SESSION.N"]
  and ([.witnessAttempts[] | [.attempt, .accepted, .confirmed]]
       == [["0000", true, true]])
  and .witnessAttempts[0].confirmMillis >= 3000' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "the pool's confirmation did not end the exploration on the \
attempt's corpus: $(cat "${stream_dir}/exploration.json")"
awk -v p="$(head -n 1 "${stream_dir}/round-planned-at")" \
    -v e="$(cat "${stream_confirm}/replay-ended-at")" \
    'BEGIN{exit !(p > 0 && p < e)}' \
  || fail "nothing landed and no round was planned while the confirmation ran"
[[ -d "${stream_dir}/sessions/SESSION.A" \
    && ! -e "${stream_dir}/sessions/SESSION.N" \
    && -d "${campaign_root}/explore-reaped/after-witness/SESSION.N" ]] \
  || fail "the corpus is not the accepted attempt's: \
$(ls "${stream_dir}/sessions")"
[[ "$(cat "${stream_confirm}/classes.txt")" \
    == "${stream_dir}/instrumented-classes" ]] \
  || fail "the confirmation did not stand on the generation's tree: \
$(cat "${stream_confirm}/classes.txt")"
jq -e -s 'map(.obligationId) | sort == ["A","N"]' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "what returned during the confirmation did not land"

# STREAM-2d: A CONFIRMATION OWED GOES FIRST.  B lands while A's confirmation
# runs: no attempt starts until A's verdict lands -- refuted -- and then B is
# attempted once, confirmed (campaign_stream_confirm_owed).
stream_fixture stream-2d
(
  stream_stubs
  stream_confirm_sleep=3
  stream_refute=0000
  stream_round_plan() {
    [[ "$1" != 0 ]] || stream_propose "$2" A B
  }
  do_compose() {
    stream_compose "${composition_manifest}" SAT_CANDIDATE P.same
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    [[ "${id}" == A ]] || sleep 1
    stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}" fatal
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the deferring loop did not finish: \
$(cat "${stream_dir}/explore.log")"
jq -e '.stop == "WITNESSED"
  and ([.witnessAttempts[] | [.attempt, .accepted, .confirmed]]
       == [["0000", false, false], ["0001", true, true]])
  and ([.witnessAttempts[].witnesses]
       == [["SESSION.A"], ["SESSION.B"]])' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "an attempt started while a confirmation was owed, or B was not \
attempted after A's refutation: $(cat "${stream_dir}/exploration.json")"

# STREAM-WITFIRST: A WITNESS WAITS FOR NO ROUND (PIPELINE §7.9).  A round
# plans in its own lane, over inputs frozen as it started, so a witness that
# returns while a round plans lands, is gated and is attempted at once: W
# returns while round 1 -- its planner thirty seconds long -- plans over the
# corpus landed before it (A's session, not W's); W's attempt starts while
# round 1 plans, and, accepted, ends the exploration: round 1, never taken,
# leaves the iteration for explore-reaped/ (roundDropped, roundDue), its
# planner stopped, no charge left (Z3S-18413: a witness waited 69 minutes,
# 57 of them behind one round, for its attempt).
stream_fixture stream-witfirst
(
  stream_stubs
  # The accepted claim's selected session is the run: decided in its step.
  stream_realize=0000
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" A W ;;
      1)
        date +%s.%N >"${stream_dir}/round-1-started-at"
        sleep 30
        date +%s.%N >"${stream_dir}/round-1-ended-at" ;;
    esac
  }
  do_compose() {
    date +%s.%N >>"${stream_dir}/attempt-started-at"
    stream_compose "${composition_manifest}" SAT_CANDIDATE
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    case "${id}" in
      A) stream_answer "${worker}" A ADMITTED SESSION.A ;;
      W) sleep 2; stream_answer "${worker}" W ADMITTED SESSION.W fatal ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "STREAM-WITFIRST: the loop did not finish: \
$(cat "${stream_dir}/explore.log")"
[[ -s "${stream_dir}/round-1-started-at" \
    && -s "${stream_dir}/attempt-started-at" ]] \
  && awk -v r="$(cat "${stream_dir}/round-1-started-at")" \
    -v a="$(head -n 1 "${stream_dir}/attempt-started-at")" \
    'BEGIN{exit !(a > r && a < r + 30)}' \
  && [[ ! -e "${stream_dir}/round-1-ended-at" ]] \
  || fail "STREAM-WITFIRST: the witness's attempt waited for the round: \
$(cat "${stream_dir}/round-1-started-at" "${stream_dir}/attempt-started-at" \
"${stream_dir}/round-1-ended-at" 2>&1)"
jq -e '.stop == "WITNESSED" and .rounds == 1
  and .roundDropped == "planning-0001" and .roundDue == true
  and ([.witnessAttempts[] | [.witnesses, .accepted]]
       == [[["SESSION.W"], true]])' \
  "${stream_dir}/exploration.json" >/dev/null \
  || fail "STREAM-WITFIRST: the witness did not end the exploration with the \
round still planning dropped: $(cat "${stream_dir}/exploration.json")"
stream_dropped="${campaign_root}/explore-reaped/planning-0001"
[[ "$(cat "${stream_dropped}/corpus.txt")" == SESSION.A \
    && "$(cat "${stream_dropped}/read.txt" 2>/dev/null)" != *SESSION.W* \
    && ! -e "${stream_dir}/planning-0001" \
    && ! -e "${stream_dir}/obligations-0001" \
    && -d "${stream_dir}/sessions/SESSION.W" ]] \
  || fail "STREAM-WITFIRST: the round's corpus was not frozen as it started, \
or the round dropped is still in the iteration: $(ls "${stream_dir}" \
"${stream_dropped}" 2>&1)"
[[ ! -e "${stream_dir}/planner/pid" \
   && -z "$(live_charges "${campaign_host_gate_root}")" ]] \
  || fail "STREAM-WITFIRST: the dropped round's planner, or a charge, \
outlived the exploration: $(live_charges "${campaign_host_gate_root}")"

# STREAM-2e: THE WITNESS BY ATTEMPT ORDER.  Of the confirmations that land
# together, the earliest attempt confirmed is the witness, whatever their
# order of return; a later one confirmed says which attempt is.
for row in "true true 0000" "false true 0001" "true false 0000"; do
  read -r first second chosen <<<"${row}"
  decide_dir="${test_tmp}/decide-${first}-${second}"
  mkdir -p "${decide_dir}/iteration/witness-attempts" "${decide_dir}/step"
  (
    iteration_dir="${decide_dir}/iteration"
    campaign_root="${decide_dir}"
    attempts="${decide_dir}/attempts.jsonl"
    for attempt in 0000 0001; do
      mkdir -p "${iteration_dir}/witness-attempts/${attempt}" \
        "${campaign_root}/witness-confirm/${attempt}"
      date +%s%3N >"${campaign_root}/witness-confirm/${attempt}/started-at"
      jq -n -c --arg a "${attempt}" --arg d "${iteration_dir}/witness-attempts/${attempt}" \
        '{attempt: $a, step: "0009", witnesses: ["S.\($a)"], dir: $d,
          composeExit: 0, claim: "SAT_CANDIDATE", findingKind: "CLOCK_SKEW",
          polarityDecides: true, composeMillis: 1}' \
        >"${iteration_dir}/witness-attempts/${attempt}/attempt.json"
    done
    campaign_confirm_decide() {
      local verdict=${first}
      [[ "$(basename "$1")" == 0000 ]] || verdict=${second}
      campaign_confirm_verdict "${verdict}" "stub" "" false >"$1/confirm.json"
    }
    printf '0001 0\n0000 0\n' >"${decide_dir}/step/confirms"
    campaign_stream_decide "${decide_dir}/step"
  ) >"${decide_dir}/decide.log" 2>&1 \
    || fail "the decision of ${row} failed: $(cat "${decide_dir}/decide.log")"
  [[ "$(basename "$(cat "${decide_dir}/step/attempt")")" == "${chosen}" ]] \
    || fail "the confirmations ${row} did not take attempt ${chosen}"
  jq -e -s --arg chosen "${chosen}" --argjson both \
      "$([[ "${first}${second}" == truetrue ]] && echo true || echo false)" \
    '(map(select(.accepted)) | map(.attempt)) == [$chosen]
     and ((map(select(.supersededBy == "0000")) | length == 1) == $both)' \
    "${decide_dir}/attempts.jsonl" >/dev/null \
    || fail "the rows of ${row} do not state the witness: \
$(cat "${decide_dir}/attempts.jsonl")"
done

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
  && jq -e -s 'map(select(.cls == "BLOCKING")) | length == 0' \
    "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "the wave budget is not stated as a gap row, or the declared \
nesting bound cut the exploration: $(cat "${stream_dir}/campaign_gaps.jsonl")"
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

# STREAM-3c: THE CAMPAIGN BUDGET.  Between two head steps, whatever a round
# plans, once the campaign's budget has no room for the stages after the
# exploration (its reserve,
# campaign_reserve), the exploration ends as at a witness: the queue
# cancelled, what runs reaped, the stop a DIAGNOSTIC row, and
# exploration.json states what it left owed.  It still owed an arm (SLOW,
# reaped), so EMIT's one judge (campaign_exploration_cut) makes it one
# BLOCKING EXPLORATION_CUT row under an UNSAT claim, a DIAGNOSTIC one under
# a SAT_CANDIDATE, which CONFIRM validates.  The declared wave bound
# (STREAM-3) cuts nothing.
stream_fixture stream-3c
(
  stream_stubs
  # Room for round 0 (its planner's start among it) and SLOW's start, and
  # none past the planner round's wall the reserve stands COMPOSE for.
  campaign_budget_s=10
  campaign_reserve_s=1
  reproduce_min_s=1
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
jq -e -s 'map(select(.cls == "BLOCKING")) | length == 0' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  && jq -e 'select(.subject == "CAMPAIGN_BUDGET_REACHED"
    and .cls == "DIAGNOSTIC") | .detail | test("campaign_budget_s")' \
    "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  || fail "the budget stop is not one DIAGNOSTIC row: \
$(cat "${stream_dir}/campaign_gaps.jsonl")"
cp "${stream_dir}/campaign_gaps.jsonl" "${stream_dir}/explore-gaps.jsonl"
for claim in UNSAT_CLOSED SAT_CANDIDATE; do
  cp "${stream_dir}/explore-gaps.jsonl" "${stream_dir}/campaign_gaps.jsonl"
  jq -n --arg claim "${claim}" '{solver: {campaignClaim: {claim: $claim}}}' \
    >"${stream_dir}/cut-manifest.json"
  ( composition_manifest="${stream_dir}/cut-manifest.json"
    campaign_exploration_cut "${stream_dir}" )
  cls=$([[ "${claim}" == UNSAT_CLOSED ]] && echo BLOCKING || echo DIAGNOSTIC)
  jq -e -s --arg cls "${cls}" 'map(select(.subject == "EXPLORATION_CUT"))
    | length == 1 and .[0].cls == $cls
    and (.[0].detail | test("ended CAMPAIGN_BUDGET_REACHED")
         and test("1 unlanded job"))' \
    "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
    || fail "under ${claim}, a budget stop that owed arms is not one ${cls} \
EXPLORATION_CUT row: $(cat "${stream_dir}/campaign_gaps.jsonl")"
done
# A WITNESSED end owes what it dropped (a refuted witness's next claim is
# composed over the trimmed corpus); FIXED_POINT owes nothing.
for end in '{"stop": "WITNESSED", "cancelled": ["A"]}' \
    '{"stop": "FIXED_POINT", "cancelled": ["A"]}'; do
  printf '%s\n' "${end}" >"${stream_dir}/exploration.json"
  : >"${stream_dir}/campaign_gaps.jsonl"
  jq -n '{solver: {campaignClaim: {claim: "UNSAT_CLOSED"}}}' \
    >"${stream_dir}/cut-manifest.json"
  ( composition_manifest="${stream_dir}/cut-manifest.json"
    campaign_exploration_cut "${stream_dir}" )
  want=$([[ "${end}" == *WITNESSED* ]] && echo 1 || echo 0)
  [[ "$(grep -c EXPLORATION_CUT "${stream_dir}/campaign_gaps.jsonl")" \
      == "${want}" ]] \
    || fail "${end} under an UNSAT is not ${want} cut row(s): \
$(cat "${stream_dir}/campaign_gaps.jsonl")"
done

# STREAM-3d: THE BUDGET ENDS A ROUND STILL PLANNING.  The campaign's budget is
# judged between two head steps, not when a round returns: round 1 -- its
# planner a minute long -- still plans when the budget has no room left, so
# the exploration ends as at a witness and the round, never taken, is dropped:
# its planner stopped, its directory out of the iteration for explore-reaped/,
# exploration.json naming it (roundDropped) as a round owed (roundDue).
stream_fixture stream-3d
(
  stream_stubs
  campaign_budget_s=15
  campaign_reserve_s=1
  reproduce_min_s=1
  campaign_started_s=${SECONDS}
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" A ;;
      1) date +%s.%N >"${stream_dir}/round-1-started-at"; sleep 60 ;;
    esac
  }
  campaign_obligation_worker() { stream_answer "$4" A ADMITTED SESSION.A; }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "STREAM-3d: the budgeted loop did not finish: \
$(cat "${stream_dir}/explore.log")"
jq -e '.stop == "CAMPAIGN_BUDGET_REACHED" and .rounds == 1
  and .roundDropped == "planning-0001" and .roundDue == true' \
  "${stream_dir}/exploration.json" >/dev/null \
  && [[ -s "${stream_dir}/round-1-started-at" \
        && -s "${campaign_root}/explore-reaped/planning-0001/corpus.txt" \
        && ! -e "${stream_dir}/planning-0001" \
        && ! -e "${stream_dir}/obligations-0001" \
        && ! -e "${stream_dir}/planner/pid" ]] \
  || fail "STREAM-3d: the budget did not drop the round still planning: \
$(cat "${stream_dir}/exploration.json"; ls "${stream_dir}")"

# STREAM-3b: A PLANNER OUT OF HEAP.  A round whose planner ran out of the most
# heap a head JVM is given (exit 3) is not planned: its directory leaves the
# iteration with its logs (explore-reaped/planning-NNNN, roundDropped), what
# runs lands, the exploration ends on the rounds before it, and the stop is
# a row naming the planner's error (sweep a40h2, DataStreamer-638) -- rounds
# were owed, so EMIT's judge cuts any UNSAT over it.
stream_fixture stream-3b
(
  stream_stubs
  stream_planner_dies() { [[ "$1" != 1 ]] || echo 3; }
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
jq -e 'select(.subject == "PLANNER_HEAP_EXCEEDED")
  | .detail | test("obligations-0001 ran out") and test("OutOfMemoryError")' \
  "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  && jq -n '{solver: {campaignClaim: {claim: "UNSAT_CLOSED"}}}' \
    >"${stream_dir}/cut-manifest.json" \
  && ( composition_manifest="${stream_dir}/cut-manifest.json"
    campaign_exploration_cut "${stream_dir}" ) \
  && jq -e 'select(.subject == "EXPLORATION_CUT" and .cls == "BLOCKING")
    | .detail | test("ended PLANNER_HEAP_EXCEEDED")' \
    "${stream_dir}/campaign_gaps.jsonl" >/dev/null \
  && jq -e '.stop == "PLANNER_HEAP_EXCEEDED" and .rounds == 1
    and .roundDropped == "planning-0001"' \
    "${stream_dir}/exploration.json" >/dev/null \
  && [[ -s "${campaign_root}/explore-reaped/planning-0001/stderr.log" \
        && ! -e "${stream_dir}/planning-0001" ]] \
  && jq -e -s 'map(.obligationId) | sort == ["A","SLOW"]' \
    "${stream_dir}/obligation_results.jsonl" >/dev/null \
  && [[ ! -e "${stream_dir}/obligations-0001" ]] \
  || fail "a planner out of heap did not end the exploration by name: \
$(cat "${stream_dir}/campaign_gaps.jsonl" "${stream_dir}/exploration.json")"

# STREAM-SERVE: ONE PLANNER SERVES THE ROUNDS (PIPELINE §7.1, §7.9).  It is
# started once, at what the planner starts at, every round asked of it, and
# it is ended with the exploration, its charge given back.  One that runs out
# of a heap below the engine heap is started again at twice it and the round
# asked again; any other end fails EXPLORE with its deepest throwable, never
# a silent start of another.
stream_fixture stream-serve
(
  stream_stubs
  engine_memory_mb=16384
  stream_planner_dies() {
    [[ "$1" != 1 || "$2" != 8192 ]] || echo 3
  }
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" A ;;
      1) stream_propose "$2" B ;;
    esac
  }
  campaign_obligation_worker() {
    case "$1" in
      A) stream_answer "$4" A ADMITTED SESSION.A ;;
      B) stream_answer "$4" B UNSAT ;;
    esac
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "STREAM-SERVE: the served exploration failed: \
$(cat "${stream_dir}/explore.log")"
[[ "$(paste -sd ' ' - <"${stream_dir}/planner-heaps.txt")" == "8192 16384" ]] \
  && grep -q 'ExploreMain ran out of its 8192 MB heap; run again at 16384 MB' \
    "${stream_dir}/obligations-0001/stderr.log" \
  && jq -e '.stop == "FIXED_POINT" and .rounds == 3' \
    "${stream_dir}/exploration.json" >/dev/null \
  || fail "STREAM-SERVE: one planner did not serve the rounds, again at twice \
its heap once out of it: $(cat "${stream_dir}/planner-heaps.txt" \
"${stream_dir}/exploration.json")"
[[ ! -e "${stream_dir}/planner/pid" \
   && -z "$(ls "${campaign_host_gate_root}"/*/charges 2>/dev/null)" ]] \
  || fail "STREAM-SERVE: the planner outlived its exploration, or its charge"
stream_fixture stream-serve-dies
(
  stream_stubs
  engine_memory_mb=16384
  stream_planner_dies() { [[ "$1" != 1 ]] || echo 1; }
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A; }
  campaign_obligation_worker() { stream_answer "$4" A ADMITTED SESSION.A; }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  && fail "STREAM-SERVE: a planner that died was started again"
grep -q 'the planner service on localhost ended with exit 1' \
    "${stream_dir}/planning-0001/stderr.log" \
  && grep -q 'reason=the planner of obligations-0001 failed with exit 1' \
    "${stream_dir}/explore.log" \
  && grep -q 'exit 1: java.lang.OutOfMemoryError' "${stream_dir}/explore.log" \
  && [[ "$(grep -c . "${stream_dir}/planner-heaps.txt")" == 1 ]] \
  || fail "STREAM-SERVE: a planner's other end did not fail EXPLORE by name: \
$(cat "${stream_dir}/explore.log")"

# STREAM-REAP-HOLDS: the exploration's end ends a lane that waits for room
# (campaign_stream_reap: a round whose planner waits to be placed): the room
# it holds on a host (campaign_head_hold_room, named by the pid of the
# process that waits) is the hosts' again at once, never left to lapse; a
# hold another process keeps stays.
(
  campaign_host_gate_root=${test_tmp}/reap-holds/hosts
  mkdir -p "${campaign_host_gate_root}/lift12/heads"
  sleep 60 &
  stream_round_pid=$!
  sleep 60 &
  reap_other=$!
  reap_held="${campaign_host_gate_root}/lift12/heads/$(hostname -s).\
${stream_round_pid}.1791900000.hold"
  reap_kept="${campaign_host_gate_root}/lift12/heads/$(hostname -s).\
${reap_other}.1791900000.hold"
  printf '17792\n' >"${reap_held}"
  printf '4096\n' >"${reap_kept}"
  declare -A stream_jobs=() stream_job_charge=()
  stream_step_pid=""
  stream_ticker=""
  campaign_adapter_kill_grace_s=0
  campaign_reap_remote_workers() { :; }
  campaign_stream_reap
  ! kill -0 "${reap_other}" 2>/dev/null || kill "${reap_other}"
  [[ ! -e "${reap_held}" && -s "${reap_kept}" && -z "${stream_round_pid}" ]] \
    || fail "STREAM-REAP-HOLDS: the ended lane's hold was not given back, or \
another's was: $(ls "${campaign_host_gate_root}/lift12/heads")"
)

# STREAM-4: a planner that states no growth file did not run to completion:
# refused by name, never read as "nothing exposed".
stream_fixture stream-4
(
  stream_stubs
  stream_planner() { :; }
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

# STREAM-5: THE GATE OVER WHAT LANDED (PIPELINE §6, §7.9).  A head step
# gates the sessions landed since the step before, once each is in the
# corpus, in one call against the iteration's ledger, its list and summary in
# steps/NNNN/ (round 0, planned in its own lane, is no head step);
# a blocking row there fails the campaign at IMPORT, by name, and the head
# ends what it still runs.
stream_fixture stream-5
(
  campaign_host_available_mb() { echo 30000; }
  campaign_host_total_mb() { echo 30000; }
  campaign_planner_serve() { stream_planner_serve "$@"; }
  run_java_main() {
    [[ "$1" == *.ImportGateMain ]] \
      || fail "the step ran an engine main past the gate: $1"
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
[[ "$(cat "${stream_dir}/steps/0000/gate")" == SESSION.A \
    && -s "${stream_dir}/steps/0000/import_gate.json" ]] \
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

# STREAM-CAP: an exploration in a shared pool runs no more starts at once
# than its share -- the slots its hosts hold at its measured replay charge
# (campaign_pool_slots: here one host of 30000 MB at 70 %, 8 cores) over the
# sharing explorations whose ledger entry is fresh, its own among them, at
# least one -- a solve charged what a solver starts at; it says so once for
# each share it waits at, and takes its entry with it when it ends; outside
# a shared pool it keeps no entry and waits for nothing but room (a40: one
# Solr case's pool held 27-32 replays on all ten lifts while the sweep's
# other cases waited).  Outside a shared pool the one host still holds no
# more than campaign_stream_solves_per_host (2) of its solves.  Per row: the
# campaign's measured peak (- outside a shared pool), the fresh and the stale
# entries of other explorations, the most of three one-second solves that ran
# at once, and how many explorations the wait names (- for none).
while read -r cap_peak cap_fresh cap_stale cap_ran_most cap_sharers; do
  stream_fixture "stream-cap-${cap_peak}-${cap_fresh}-${cap_stale}"
  campaign_replay_peak_mb=0
  if [[ "${cap_peak}" != - ]]; then
    stream_shared_pool=true
    campaign_replay_peak_mb=${cap_peak}
  fi
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
      printf '%s\n' "$5" >"${worker}/charged"
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
  [[ "${cap_ran}" == "${cap_ran_most}" ]] \
    || fail "a pool at a ${cap_peak} MB peak with ${cap_fresh} other \
exploration(s) ran ${cap_ran} obligation(s) at once, not ${cap_ran_most}"
  # One host: its first solve is cold, charged what a solver starts at; the
  # others find its solver serving and are charged a question's z3 run.
  [[ "$(cat "${stream_dir}"/obligations-0000/{A,B,C}/charged | sort -n \
      | paste -sd ' ' -)" == "$(printf '%s\n' "${campaign_question_mb}" \
      "${campaign_question_mb}" "$(campaign_solver_need_mb)" | sort -n \
      | paste -sd ' ' -)" ]] \
    || fail "the pool's solves were charged $(cat \
      "${stream_dir}"/obligations-0000/{A,B,C}/charged | paste -sd ' ' -), \
not a solver's start ($(campaign_solver_need_mb) MB) for the cold one and \
a question's (${campaign_question_mb} MB) for the warm ones"
  cap_said=$(grep -c 'waiting for a slot' "${stream_dir}/explore.log" \
    || true)
  if [[ "${cap_sharers}" == - ]]; then
    [[ "${cap_said}" -eq 0 && ! -e "${cap_entries}" ]] \
      || fail "an exploration outside a shared pool waited for a slot or \
kept an entry"
  else
    [[ "${cap_said}" -ge 1 && "${cap_said}" -eq "$(grep -o \
        "waiting for a slot.*share [0-9]*" "${stream_dir}/explore.log" \
        | sort -u | wc -l)" ]] && grep -q "shared by ${cap_sharers} \
exploration" "${stream_dir}/explore.log" \
      || fail "the wait for a slot was not said once for each share, \
naming ${cap_sharers} exploration(s): $(grep 'slot' \
        "${stream_dir}/explore.log")"
    [[ "$(ls "${cap_entries}" | wc -l)" -eq $((cap_fresh + cap_stale)) ]] \
      || fail "the exploration's entry outlived it: $(ls "${cap_entries}")"
  fi
done <<'EOF'
- 0 0 2 -
5000 0 1 2 1
5000 1 0 1 2
8000 2 0 1 3
EOF
campaign_replay_peak_mb=0
reset_config
# Sharing is a declared workflow key, overridden only through the table,
# false by default, and true or false or refused by name.
[[ "$(grep -c 'CAUSYNTH_STREAM_SHARED_POOL' "${repo}/run_engine.sh")" \
    -eq 1 && "${stream_shared_pool}" == false ]] && known_config_key \
    stream_shared_pool \
  || fail "stream_shared_pool is not a declared key defaulting to false"
CAUSYNTH_STREAM_SHARED_POOL=true apply_environment_overrides
[[ "${stream_shared_pool}" == true ]] \
  || fail "CAUSYNTH_STREAM_SHARED_POOL does not override the key"
reset_config
cap_validate() (
  stop_after_config ""
  stream_shared_pool=$1
  validate_config
)
for cap_value in "" 0 1 30 TRUE true false; do
  run_capturing_status cap_validate "${cap_value}" >/dev/null \
    2>"${test_tmp}/cap-validate.err"
  case "${cap_value}" in
    true|false) [[ "${status}" -eq 0 ]] \
      || fail "validate refused stream_shared_pool='${cap_value}'" ;;
    *) [[ "${status}" -ne 0 ]] && grep -q 'stream_shared_pool must be' \
        "${test_tmp}/cap-validate.err" \
      || fail "validate did not refuse stream_shared_pool='${cap_value}' \
by name" ;;
  esac
done
reset_config

# STREAM-SPLIT: an obligation's solve and its replay are two starts.  The
# solve is charged what a solver starts at; one its solver answers
# SAT_MODEL_READY queues its REPLAY first, at once, charged the measured
# replay need then -- C's replay, after A's stated its peak, from that peak
# -- on the class tree and plan its solve started on.  Until its REPLAY
# lands the obligation is in flight: round 1, planned when B's session
# landed while A replayed, is handed A and C (C still solving), and round 2
# C.  Only the replays' answers land (no SAT_MODEL_READY row), each where
# its replay staged it.
stream_fixture stream-split
(
  stream_stubs
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A B C; }
  campaign_obligation_worker() {
    local id=$1 worker=$4
    printf '%s\n' "$5" >"${worker}/solve-charged"
    case "${id}" in
      A) sleep 1; stream_answer "${worker}" A SAT_MODEL_READY ;;
      B) sleep 2; stream_answer "${worker}" B ADMITTED SESSION.B ;;
      C) sleep 6; stream_answer "${worker}" C SAT_MODEL_READY ;;
    esac
  }
  campaign_obligation_replay() {
    local id=$1 classes=$2 worker=$3 plan=$5 charged=$6
    printf '%s %s %s\n' "${charged}" "${classes#"${stream_dir}"/}" \
      "${plan#"${stream_dir}"/}" >"${worker}/replay-args"
    if [[ "${id}" == A ]]; then
      sleep 3
      echo 3000 >"${worker}/workload_rss_mb"
    fi
    stream_answer "${worker}" "${id}" ADMITTED "SESSION.${id}"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "a split exploration did not finish: $(cat "${stream_dir}/explore.log")"
split_round0="${stream_dir}/obligations-0000"
[[ "$(cat "${split_round0}"/{A,B,C}/solve-charged | sort -n \
    | paste -sd ' ' -)" == "$(printf '%s\n' "${campaign_question_mb}" \
    "${campaign_question_mb}" "$(campaign_solver_need_mb)" | sort -n \
    | paste -sd ' ' -)" ]] \
  || fail "the solves were not charged a solver's start for the cold one and \
a question's for the warm ones: $(cat \
    "${split_round0}"/{A,B,C}/solve-charged | paste -sd ' ' -)"
split_plan="instrumented-classes generations/g0/execution_task_plan.jsonl"
[[ "$(cat "${split_round0}/A/replay-args")" \
    == "$(campaign_stream_charge_mb REPLAY) ${split_plan}" \
   && "$(cat "${split_round0}/C/replay-args")" \
    == "$(campaign_replay_peak_mb=3000 campaign_stream_charge_mb REPLAY) \
${split_plan}" && ! -e "${split_round0}/B/replay-args" ]] \
  || fail "the REPLAYs were not charged the measured need on their solve's \
tree: A $(cat "${split_round0}/A/replay-args"), C $(cat \
    "${split_round0}/C/replay-args")"
[[ "$(cat "${stream_dir}/obligations-0001/in-flight.txt")" == "A C" \
   && "$(cat "${stream_dir}/obligations-0002/in-flight.txt")" == C ]] \
  || fail "an obligation whose REPLAY had not landed was not in flight: \
round 1 $(cat "${stream_dir}/obligations-0001/in-flight.txt"), round 2 \
$(cat "${stream_dir}/obligations-0002/in-flight.txt")"
jq -e -s 'length == 3 and all(.[]; .verdict == "ADMITTED")' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  && [[ -d "${stream_dir}/sessions/SESSION.A" \
     && -d "${stream_dir}/sessions/SESSION.C" \
     && -s "${split_round0}/A/replay-host.txt" \
     && -e "${split_round0}/A/replay-stderr.log" \
     && -e "${split_round0}/A/stderr.log" \
     && ! -e "${split_round0}/B/replay-host.txt" ]] \
  && grep -q 'obligation A: solved on .*, its replay queued' \
    "${stream_dir}/explore.log" \
  || fail "the replays' answers did not land as the obligations' own: \
$(cat "${stream_dir}/obligation_results.jsonl")"
reset_config

# STREAM-SPLIT-QUEUE: what a solve's return does to the queue.  An answer
# SAT_MODEL_READY of a solve that finished queues its REPLAY behind the
# solves (here last), carrying
# the class tree and plan the solve started on even when a GROW wove a newer
# generation since (g1 here), and the REPLAY starts on them, charged the
# replay's charge; any other answer, or a solve that did not finish, waits
# to land.  Per row: the solve's verdict, its exit, the queue's last entry
# after it, and what waits to land (- nothing).
split_dir="${test_tmp}/split-queue"
while IFS='|' read -r split_verdict split_status split_first split_pending; do
  rm -rf -- "${split_dir}"
  mkdir -p "${split_dir}/it/obligations-0000/A"
  : >"${split_dir}/jobs"
  split_said=$(
    iteration_dir="${split_dir}/it"
    sessions="${split_dir}/it/sessions"
    stream_classes=g0/classes
    stream_plan=g0/plan.jsonl
    stream_admitted_mb=${campaign_solver_start_mb}
    declare -A stream_jobs=() stream_job_charge=() stream_job_worker=() \
      stream_job_tree=() stream_host_jobs=() stream_solver_seen=() \
      stream_host_solves=()
    declare -A stream_queued_at=()
    stream_queue=("OBLIGATION obligations-0000 B")
    stream_pending=()
    stream_ticker=""
    stream_step_pid=""
    stream_round_pid=""
    campaign_host_release() { :; }
    campaign_log() { :; }
    campaign_stream_job() {
      printf '%s\n' "$*" >>"${split_dir}/jobs"
      [[ "$1" != OBLIGATION ]] || jq -n -c --arg v "${split_verdict}" \
        '{verdict: $v}' >"$5/obligation_result.jsonl"
      return "${split_status}"
    }
    campaign_stream_start "OBLIGATION obligations-0000 A" lift12
    split_pid=$!
    split_rc=0
    wait "${split_pid}" || split_rc=$?
    stream_classes=g1/classes
    stream_plan=g1/plan.jsonl
    campaign_stream_ended "${split_pid}" "${split_rc}"
    if [[ "${stream_queue[-1]}" == REPLAY\ * ]]; then
      stream_admitted_mb=2048
      campaign_stream_start "${stream_queue[-1]}" lift13
      wait "$!" || true
    fi
    printf '%s|%s' "${stream_queue[-1]}" "${stream_pending[*]:--}"
  )
  [[ "${split_said% }" == "${split_first}|${split_pending}" ]] \
    || fail "a ${split_verdict} solve that exited ${split_status} left \
${split_said}, not ${split_first}|${split_pending}"
  if [[ "${split_first}" == REPLAY\ * ]]; then
    grep -q "^REPLAY lift13 .* A ${split_dir}/it/obligations-0000/A A \
g0/classes ${split_dir}/it/obligations-0000/A \
${split_dir}/it/obligations-0000/A/sessions g0/plan.jsonl 2048 " \
      "${split_dir}/jobs" \
      || fail "the REPLAY did not start on its solve's tree in its worker: \
$(cat "${split_dir}/jobs")"
  fi
done <<'EOF'
SAT_MODEL_READY|0|REPLAY obligations-0000 A g0/classes g0/plan.jsonl|-
UNSAT|0|OBLIGATION obligations-0000 B|OBLIGATION obligations-0000 A lift12 0
SAT_MODEL_READY|1|OBLIGATION obligations-0000 B|OBLIGATION obligations-0000 A lift12 1
EOF

# SOLVE-LANES: what a solve's return does with the lanes.  A first ask
# undecided at the first budget (SOLVER_TIMEOUT) leaves for the hard lane,
# landing nothing, its first answer kept aside; with no shorter first budget
# it lands as any answer, and so does any other refusal; one at its z3s' cap
# (SOLVER_MEMOUT) leaves for the hard lane whatever the budgets, its larger
# z3 room; a HARD ask's SOLVER_TIMEOUT or SOLVER_MEMOUT lands, named in
# solver_timeouts.jsonl.  Per row: the full
# budget, the ending job's kind, its answer's detail, the hard lane after,
# what waits to land, the first answer kept aside, and the named timeout.
lanes_dir="${test_tmp}/solve-lanes"
while IFS='|' read -r ln_budget ln_kind ln_detail ln_hard ln_pending ln_aside \
    ln_named; do
  rm -rf -- "${lanes_dir}"
  ln_worker="${lanes_dir}/it/obligations-0000/A"
  mkdir -p "${ln_worker}"
  ln_said=$(
    iteration_dir="${lanes_dir}/it"
    results="${lanes_dir}/results.jsonl"
    solver_timeout_ms=${ln_budget}
    campaign_solver_first_tier_ms=60000
    declare -A stream_jobs=() stream_job_charge=() stream_job_worker=() \
      stream_job_tree=() stream_host_jobs=() stream_host_solves=() \
      stream_host_hard=() stream_flying=()
    stream_queue=()
    stream_pending=()
    stream_hard=()
    stream_staged=()
    stream_ticker=""
    stream_step_pid=""
    stream_round_pid=""
    campaign_log() { :; }
    campaign_replay_measured() { :; }
    jq -n -c --arg d "${ln_detail}" \
      '{obligationId: "A", verdict: "NOT_ADMITTED", detail: $d}' \
      >"${ln_worker}/obligation_result.jsonl"
    sleep 0 &
    ln_pid=$!
    wait "${ln_pid}"
    stream_jobs[${ln_pid}]="${ln_kind} obligations-0000 A lift12 "
    stream_job_worker[${ln_pid}]=${ln_worker}
    stream_host_jobs[lift12]=1
    stream_host_solves[lift12]=1
    stream_host_hard[lift12]=1
    campaign_stream_ended "${ln_pid}" 0
    ln_waiting="${stream_pending[*]:--}"
    campaign_stream_land
    printf '%s|%s|%s|%s' "${stream_hard[*]:--}" "${ln_waiting% }" \
      "$([[ -e "${ln_worker}/obligation_result.first.jsonl" ]] && echo aside \
        || echo -)" "$(jq -r .obligationId \
        "${lanes_dir}/it/solver_timeouts.jsonl" 2>/dev/null || echo -)"
  )
  [[ "${ln_said}" == "${ln_hard}|${ln_pending}|${ln_aside}|${ln_named}" ]] \
    || fail "a ${ln_kind} answer '${ln_detail}' under ${ln_budget} ms left \
${ln_said}, not ${ln_hard}|${ln_pending}|${ln_aside}|${ln_named}"
done <<'EOF'
1800000|OBLIGATION|SOLVER_TIMEOUT after 60000ms|HARD obligations-0000 A|-|aside|-
60000|OBLIGATION|SOLVER_TIMEOUT after 60000ms|-|OBLIGATION obligations-0000 A lift12 0|-|-
1800000|OBLIGATION|the query was refused: no root|-|OBLIGATION obligations-0000 A lift12 0|-|-
1800000|HARD|SOLVER_TIMEOUT after 1800000ms|-|HARD obligations-0000 A lift12 0|-|A
60000|OBLIGATION|SOLVER_MEMOUT at 512 MB|HARD obligations-0000 A|-|aside|-
1800000|HARD|SOLVER_MEMOUT at 1984 MB|-|HARD obligations-0000 A lift12 0|-|A
EOF

# SOLVE-LANES-DISPATCH: the hard lane starts once no other start waits, and
# like any solve not while GROW holds the solves.  Per row: GROW's hold and
# the starts made, in order.
while IFS='|' read -r ld_hold ld_started; do
  ld_said=$(
    declare -A stream_queued_at=()
    stream_queue=("OBLIGATION obligations-0001 B"
      "REPLAY obligations-0000 C g0/c g0/p")
    [[ "${ld_hold}" -eq 0 ]] || stream_queue=()
    stream_hard=("HARD obligations-0000 A")
    stream_hold=${ld_hold}
    campaign_stream_collect_jobs() { :; }
    campaign_stream_has_slot() { return 0; }
    campaign_stream_admit_host() { stream_admitted_host=lift12; }
    campaign_stream_start() { printf '%s;' "$1"; }
    campaign_stream_dispatch
  )
  [[ "${ld_said}" == "${ld_started}" ]] \
    || fail "hold ${ld_hold}: started '${ld_said}', not '${ld_started}'"
done <<'EOF'
0|OBLIGATION obligations-0001 B;REPLAY obligations-0000 C g0/c g0/p;HARD obligations-0000 A;
1|
EOF

# STREAM-CONFIRM-FIRST: a confirmation queued, running or returned is owed
# its verdict, and no witness attempt starts meanwhile
# (campaign_stream_confirm_owed); obligations and replays owe none.  Per
# row: a running job, the queue, what returned, and whether one is owed.
while IFS='|' read -r owed_job owed_queue owed_pending owed_expect; do
  owed_said=$(
    declare -A stream_jobs=()
    [[ "${owed_job}" == - ]] || stream_jobs[4242]=${owed_job}
    stream_queue=()
    [[ "${owed_queue}" == - ]] || stream_queue=("${owed_queue}")
    stream_pending=()
    [[ "${owed_pending}" == - ]] || stream_pending=("${owed_pending}")
    if campaign_stream_confirm_owed; then echo owed; else echo none; fi
  )
  [[ "${owed_said}" == "${owed_expect}" ]] \
    || fail "job '${owed_job}', queue '${owed_queue}', returned \
'${owed_pending}': ${owed_said}, not ${owed_expect}"
done <<'EOF'
-|-|-|none
OBLIGATION obligations-0003 A lift12 s|REPLAY obligations-0003 B|OBLIGATION obligations-0002 C lift13 0|none
CONFIRM - 0000 lift09 s|-|-|owed
-|CONFIRM - 0000|-|owed
-|-|CONFIRM - 0000 lift09 0|owed
EOF

# STREAM-CHAIN: a witness attempt whose COMPOSE names an open chain (its
# path's fatal condition resting on a value no attested producer made) is not
# confirmed; the head grows the producers its arrivals name -- each once,
# from the rounds' exposures of them only, every other obligation cancelled
# -- and attempts the witnesses again once the GROW swaps in.
chain_dir="${test_tmp}/chain"
mkdir -p "${chain_dir}/step" "${chain_dir}/attempt" "${chain_dir}/sessions/W1" \
  "${chain_dir}/round"
chain_said=$(
  attempts="${chain_dir}/attempts.jsonl"
  campaign_log() { printf '%s\n' "$*" >>"${chain_dir}/log"; }
  jq -n -c '{witnesses: ["W1", "W2"]}' >"${chain_dir}/attempt/attempt.json"
  manifest="${chain_dir}/attempt/candidate_composition_manifest.json"
  jq -n -c '{solver: {campaignClaim: {openChain: []}}}' >"${manifest}"
  ! campaign_stream_open_chain "${chain_dir}/step" "${chain_dir}/attempt" \
    W1 W2 || echo "a closed chain opened"
  jq -n -c '{solver: {campaignClaim: {openChain: [
      {symbol: "M_J_field_HOFF.a", producer: "nn0/region/R.P1"},
      {symbol: "M_J_field_HOFF.b", producer: ""},
      {symbol: "M_J_field_HOFF.c", producer: "nn0/region/R.P1"}]}}}' \
    >"${manifest}"
  campaign_stream_open_chain "${chain_dir}/step" "${chain_dir}/attempt" W1 W2 \
    || echo "an open chain read closed"
  printf 'chain=%s witnesses=%s row=%s\n' \
    "$(paste -sd, "${chain_dir}/step/chain")" \
    "$(paste -sd, "${chain_dir}/step/chain-witnesses")" \
    "$(jq -r '[.confirmed, .accepted, (.confirmReason | test("chain is open"))]
      | map(tostring) | join(",")' "${attempts}")"
  # The head takes it: queued obligations cancelled, a REPLAY kept.
  declare -A stream_chain=() stream_chain_grown=()
  stream_chain_witnesses=()
  stream_cancelled=()
  iteration_dir="${chain_dir}"
  mkdir -p "${chain_dir}/obligations-0003/O1"
  stream_queue=("REPLAY obligations-0002 R1 g0/c g0/p" \
    "OBLIGATION obligations-0003 O1")
  declare -A stream_flying=([O1]=row)
  campaign_stream_open "${chain_dir}/step"
  printf 'producers=%s queue=%s cancelled=%s\n' "${!stream_chain[*]}" \
    "${stream_queue[*]%% *}" "${stream_cancelled[*]}"
  # A round: only the chain's producer exposed grows; obligations wait.
  jq -n -c '{kind: "EXPOSED_REGION", occurrence: "nn0/region/R.P1",
      obligationId: "O7", sessionId: "S7"},
    {kind: "EXPOSED_REGION", occurrence: "nn0/region/R.P9",
      obligationId: "O8", sessionId: "S8"}' >"${chain_dir}/round/growth.jsonl"
  campaign_stream_grow() { printf 'grew %s\n' "$(jq -r .occurrence "$2")"; }
  stream_cancelled=()
  campaign_stream_chain_round "${chain_dir}/round" O5 O6
  printf 'cancelled=%s grown=%s\n' "${stream_cancelled[*]}" \
    "${!stream_chain_grown[*]}"
  # The same chain again: its producer was grown, so it cannot close.
  campaign_stream_open "${chain_dir}/step"
  printf 'reopened=%s\n' "${#stream_chain[@]}"
  # After the swap: the witnesses still in the corpus are attempted again.
  sessions="${chain_dir}/sessions"
  stream_chain=([nn0/region/R.P1]=1)
  stream_chain_witnesses=(W1 W2)
  stream_witnesses=()
  campaign_stream_chain_reattempt
  printf 'again=%s open=%s\n' "${stream_witnesses[*]}" "${#stream_chain[@]}"
)
[[ "${chain_said}" == "chain=nn0/region/R.P1 witnesses=W1,W2 row=null,false,true
producers=nn0/region/R.P1 queue=REPLAY cancelled=O1
grew nn0/region/R.P1
cancelled=O5 O6 grown=nn0/region/R.P1
reopened=0
again=W1 open=0" ]] || fail "the open witness chain was handled as: \
${chain_said}"

# STREAM-QUEUE-ORDER: the queue by kind (campaign_stream_enqueue): the
# witness's confirmation and GROW's re-runs lead it (hdfs-11741 AR1: 473
# later replays started ahead of the confirmation), the solves follow in
# their rounds' order, the replays last, the newest first (solr-adhoc-21
# RX4: solves starved behind replays).  Per row: the queue's kinds before,
# the entry queued, and the kinds after.
while IFS='|' read -r confirm_before confirm_kind confirm_after; do
  confirm_said=$(
    declare -A stream_queued_at=()
    stream_queue=()
    for kind in ${confirm_before}; do
      stream_queue+=("${kind} r q")
    done
    campaign_stream_enqueue "${confirm_kind} obligations-0004 A g0/c g0/p"
    printf '%s,' "${stream_queue[@]%% *}"
    [[ -n "${stream_queued_at[${confirm_kind} obligations-0004 A g0/c \
g0/p]:-}" ]] || printf 'unstamped'
  )
  [[ "${confirm_said}" == "${confirm_after}" ]] \
    || fail "a ${confirm_kind} queued over [${confirm_before}] gave \
${confirm_said}, not ${confirm_after}"
done <<'ROWS'
CONFIRM RERUN OBLIGATION|REPLAY|CONFIRM,RERUN,OBLIGATION,REPLAY,
OBLIGATION REPLAY|REPLAY|OBLIGATION,REPLAY,REPLAY,
CONFIRM|REPLAY|CONFIRM,REPLAY,
|REPLAY|REPLAY,
RERUN OBLIGATION REPLAY|OBLIGATION|RERUN,OBLIGATION,OBLIGATION,REPLAY,
OBLIGATION REPLAY|CONFIRM|CONFIRM,OBLIGATION,REPLAY,
ROWS

# STREAM-DISPATCH: the first entry a host admits starts, a kind no host
# admits holding nothing behind it; an entry queued past the wait bound goes
# first and alone; no solve starts while GROW owes re-runs.  Per row: the
# queue (kind:age in s), the kinds hosts admit, GROW's hold, and the entries
# started, in order.
while IFS='|' read -r dispatch_queue dispatch_admits dispatch_hold \
    dispatch_expect; do
  dispatch_said=$(
    declare -A stream_queued_at=()
    stream_queue=()
    stream_hard=()
    now=$(date +%s)
    index=0
    for item in ${dispatch_queue}; do
      index=$((index + 1))
      stream_queue+=("${item%%:*} r q${index}")
      stream_queued_at["${item%%:*} r q${index}"]=$((now - ${item##*:}))
    done
    stream_hold=${dispatch_hold}
    campaign_stream_collect_jobs() { :; }
    campaign_stream_has_slot() { return 0; }
    campaign_stream_admit_host() {
      [[ " ${dispatch_admits} " == *" $1 "* ]] || return 1
      stream_admitted_host=lift06
    }
    campaign_stream_start() { printf '%s,' "${1%% *}:${1##* }"; }
    campaign_stream_dispatch
  )
  [[ "${dispatch_said}" == "${dispatch_expect}" ]] \
    || fail "dispatching [${dispatch_queue}] with hosts admitting \
[${dispatch_admits}], hold ${dispatch_hold}, started ${dispatch_said}, not \
${dispatch_expect}"
done <<'ROWS'
OBLIGATION:5 OBLIGATION:5 REPLAY:5|OBLIGATION REPLAY|0|OBLIGATION:q1,OBLIGATION:q2,REPLAY:q3,
REPLAY:5 OBLIGATION:5|OBLIGATION|0|OBLIGATION:q2,
OBLIGATION:5 REPLAY:5|REPLAY|0|REPLAY:q2,
OBLIGATION:5 REPLAY:900 OBLIGATION:5|OBLIGATION|0|
OBLIGATION:5 REPLAY:900 OBLIGATION:5|OBLIGATION REPLAY|0|REPLAY:q2,OBLIGATION:q1,OBLIGATION:q3,
OBLIGATION:900 REPLAY:5|REPLAY|1|REPLAY:q2,
CONFIRM:5 OBLIGATION:5|CONFIRM OBLIGATION|0|CONFIRM:q1,OBLIGATION:q2,
ROWS

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
    # Where a solver serves, not how many it holds (the admission table).
    campaign_stream_solves_per_host=4
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

# STREAM-SPLIT-REMOTE: both starts of an obligation on peers (the remote
# CONFIRM of HG4 lost every result and no test ran it).  A's solve runs on
# lift12 as --run-obligation, charged what a solver starts at; its
# SAT_MODEL_READY comes back through the shared home, and its REPLAY runs as
# a placed step on lift13 -- not its solve's host -- in A's worker, where it
# must find the model its solve left (the focus row), on the solve's tree,
# charged the replay's need; the session it staged lands from there.  B's
# solve answers UNSAT and replays nothing.  The stub stands where the
# network stands, as in HOSTS-4: it reads the generated script's arguments
# as a peer's shell would.
stream_fixture stream-split-remote
campaign_worker_hosts="lift12 lift13"
campaign_local_host_names=" localhost this-machine "
graphchecker_jar=${default_graphchecker_jar}
replay_timeout_s=2400
solver_timeout_ms=1800000
campaign_init_local_scratch_root
for split_host in lift12 lift13; do
  mkdir -p "${campaign_host_gate_root}/${split_host}"
  printf '48\n' >"${campaign_host_gate_root}/${split_host}/cores"
done
(
  stream_stubs
  stream_round_plan() { [[ "$1" != 0 ]] || stream_propose "$2" A B; }
  ssh() {
    local host="" script="" line at
    local -a words=() cmd=()
    while [[ $# -gt 0 ]]; do
      [[ "$1" == "--" ]] && { shift; break; }
      shift
    done
    host=${1:-}
    script=${2:-}
    script=${script#exec /bin/bash }
    script=${script%\'}
    script=${script#\'}
    [[ -s "${script}" ]] && bash -n "${script}" || return 91
    line=$(awk '$1 == "--"' "${script}")
    eval "words=(${line% \\})"
    if grep -q -- '--run-obligation' "${script}"; then
      # -- id obligations sessions worker charged
      printf '%s SOLVE %s %s\n' "${host}" "${words[1]}" "${words[5]}" \
        >>"${stream_dir}/ssh-calls.txt"
      if [[ "${words[1]}" == A ]]; then
        printf '{"taskId":"TASK.A"}\n' >"${words[4]}/focused_task.jsonl"
        stream_answer "${words[4]}" A SAT_MODEL_READY
      else
        stream_answer "${words[4]}" "${words[1]}" UNSAT
      fi
      return 0
    fi
    grep -q -- '--run-placed' "${script}" || return 93
    # -- <workdir> <assignments...> -- <command...>
    for ((at = 1; at < ${#words[@]}; at++)); do
      [[ "${words[${at}]}" != -- ]] || break
    done
    cmd=("${words[@]:$((at + 1))}")
    [[ "${cmd[0]}" == campaign_obligation_replay ]] || return 94
    # id classes worker sessions plan charged need
    [[ -s "${cmd[3]}/focused_task.jsonl" \
       && "${cmd[4]}" == "${cmd[3]}/sessions" ]] || return 96
    printf '%s REPLAY %s %s %s %s\n' "${host}" "${cmd[1]}" "${cmd[6]}" \
      "${cmd[2]#"${stream_dir}"/}" "${cmd[5]#"${stream_dir}"/}" \
      >>"${stream_dir}/ssh-calls.txt"
    stream_answer "${cmd[3]}" "${cmd[1]}" ADMITTED "SESSION.${cmd[1]}"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "a remote split exploration did not finish: \
$(cat "${stream_dir}/explore.log")"
[[ "$(LC_ALL=C sort "${stream_dir}/ssh-calls.txt")" == "lift12 SOLVE A \
$(campaign_solver_need_mb)
lift12 SOLVE B ${campaign_question_mb}
lift13 REPLAY A $(campaign_stream_charge_mb REPLAY) instrumented-classes \
generations/g0/execution_task_plan.jsonl" ]] \
  || fail "the remote solves and REPLAY did not run where and as they \
should: $(cat "${stream_dir}/ssh-calls.txt")"
jq -e -s 'length == 2 and (map({(.obligationId): .verdict}) | add)
    == {"A": "ADMITTED", "B": "UNSAT"}' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  && [[ -f "${stream_dir}/sessions/SESSION.A/manifest.json" \
     && "$(cat "${stream_dir}/obligations-0000/A/host.txt")" == lift12 \
     && "$(cat "${stream_dir}/obligations-0000/A/replay-host.txt")" \
       == lift13 ]] \
  || fail "the remote REPLAY's answer did not land as A's: \
$(cat "${stream_dir}/obligation_results.jsonl")"
reset_config

# The pool's choice over three hosts that all admit: a replay (a REPLAY, a
# re-run) goes round-robin; an obligation's solve goes to a host where its
# campaign's solver still serves (one started there within the solver's idle
# time), else round-robin; a host already holding
# campaign_stream_solves_per_host of its solves takes no more (b:2).  {kind,
# the host warm (- none), the hosts chosen in turn}.
while IFS='|' read -r admit_kind admit_warm admit_want; do
  (
    stream_hosts=(a b c)
    stream_next_host=0
    stream_waiting=""
    declare -A stream_solver_seen=() stream_host_unread=()
    declare -A stream_host_solves=()
    [[ "${admit_warm}" != *:* ]] \
      || stream_host_solves[${admit_warm%%:*}]=${admit_warm#*:}
    admit_warm=${admit_warm%%:*}
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
REPLAY|b|a b c
OBLIGATION|-|a b c
OBLIGATION|b|b b b
OBLIGATION|b:2|a c a
REPLAY|b:2|a b c
EOF

# POOL-JOB: a start of the pool runs on the host that admitted it -- an
# obligation's solve, or an obligation's REPLAY, a GROW re-run's or a
# CONFIRM's replay, which a peer runs as a placed step -- and gives its
# ledger row back as soon as its work returned, before the head waits to see
# what a peer wrote, in the directory the job staged its sessions to (a
# CONFIRM's beside its worker: HG4 lost hdfs-11741's confirmed witness
# waiting under the worker); a REPLAY's logs go beside its solve's, never
# over them.  Per row: the kind, the host, what ran, each with the rows the
# ledger still held for it then, and the job's logs in its worker.
job_dir="${test_tmp}/pool-job"
while IFS='|' read -r job_kind job_host job_ran job_logs; do
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
    campaign_host_try_start "${job_host}" 2500 \
      || fail "the job's start was refused"
    job_charge=${campaign_host_charge_id}
    job_record() {
      printf '%s(%s) ' "$1" "$(live_charges "${campaign_host_gate_root}" \
        | grep -cF -- "${job_charge}")" >>"${job_dir}/ran"
    }
    campaign_obligation_worker() { job_record "worker:$1"; }
    campaign_obligation_replay() { job_record "replay:$1:$6"; }
    campaign_dispatch_remote() { job_record "$1:$4:$5"; }
    campaign_run_placed() { job_record "$1:$2:$3:$8"; }
    campaign_await_remote_result() { job_record "await:$3:${4#"${job_dir}"/}"; }
    campaign_stream_job "${job_kind}" "${job_host}" "${job_charge}" OB.1 \
      "${job_dir}/worker" OB.1 b c d e f
  ) || fail "a ${job_kind} on ${job_host} failed"
  [[ "$(cat "${job_dir}/ran")" == "${job_ran} " ]] \
    || fail "a ${job_kind} on ${job_host} ran $(cat "${job_dir}/ran")"
  [[ "$(ls "${job_dir}/worker" | grep 'stdout\|stderr' | paste -sd ' ' -)" \
      == "${job_logs}" ]] \
    || fail "a ${job_kind} on ${job_host} logged into $(ls "${job_dir}/worker")"
done <<'EOF'
OBLIGATION|localhost|worker:OB.1(1)|stderr.log stdout.log
OBLIGATION|lift12|lift12:--run-obligation:OB.1(1) await:OB.1:worker/sessions(0)|
REPLAY|localhost|replay:OB.1:f(1)|replay-stderr.log replay-stdout.log
REPLAY|lift12|lift12:campaign_obligation_replay:OB.1:f(1) await:OB.1:worker/sessions(0)|replay-stderr.log replay-stdout.log
RERUN|localhost|replay:OB.1:f(1)|stderr.log stdout.log
RERUN|lift12|lift12:campaign_obligation_replay:OB.1:f(1) await:OB.1:worker/sessions(0)|stderr.log stdout.log
CONFIRM|lift12|lift12:campaign_confirm_replay:OB.1:f(1) await:OB.1:OB.1/sessions(0)|stderr.log stdout.log
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
# A stated one is taken as the root, which is how the peer gets the head's.
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
grep -q 'CAUSYNTH_LOCAL_SCRATCH=${campaign_local_scratch_root}/$(basename' \
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
# the worker's and its verdict the ledger's.  What was queued stays first:
# Q2, queued through the growth, is in flight for the round after it, which
# proposes Q3 behind it; G1, which the growing round itself proposed, is
# queued behind the re-run as well and answered once.  The same replay also
# made a marker invocation its task planned no input for (UNPLANNED_INPUT):
# one exposure more, one re-run still.  The planner, GROW's planner (which
# writes the generation's whole plan) and the weave are stubbed; the re-run
# is the production replay of a script that publishes a session, so
# everything between is the production code.
stream_fixture grow
mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
printf '1\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
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
      0) stream_propose "$2" OB.x Q1 Q2 ;;
      1) printf '%s\n' \
'{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
'{"kind":"UNPLANNED_INPUT","taskId":"TASK.seed","symbol":"SYM.marker","k":2,"sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
           >>"$2/growth.jsonl"
         stream_propose "$2" G1 ;;
      2) stream_propose "$2" Q3 ;;
    esac
  }
  run_java_main() {
    if [[ "$1" == edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain ]]
    then
      local args=" $* " output plan
      [[ "${args}" == *" --iteration ${stream_dir} "* \
          && "${args}" == *" --growth ${stream_dir}/obligations-0001/growth.jsonl "* \
          && "${args}" == *" --output ${stream_dir}/generations/g1/execution_task_plan.jsonl "* ]] \
        || fail "GROW's planner was not handed the iteration, the round's \
growth rows and the next generation's plan: $*"
      plan=${args##* --plan }
      plan=${plan%% *}
      output=${args##* --output }
      output=${output%% *}
      { cat "${plan}"
        printf '{"taskId":"TASK.grown","regionId":"REGION.grown","admissionBasis":"EXPOSED_BY"}\n'
      } >"${output}"
      return 0
    fi
    fail "the step ran an engine main GROW does not: $1"
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
    local id=$1 worker=$4
    date +%s.%N >"${worker}/started-at"
    if [[ "${id}" != OB.x ]]; then
      [[ "${id}" != Q1 ]] || sleep 2
      stream_answer "${worker}" "${id}" UNSAT
      return 0
    fi
    printf '{"taskId":"TASK.seed"}\n' >"${worker}/focused_task.jsonl"
    printf 'the exposing replay\n' >"${worker}/replay.log"
    printf 'Q.exposing\n' >"${worker}/question.txt"
    stream_answer "${worker}" OB.x ADMITTED SESSION.exposing
  }
  # The worker's inodes as the swap takes them, and after it, theirs and
  # the aside's.
  eval "grow_swap_production() $(declare -f campaign_stream_swap \
    | tail -n +2)"
  campaign_stream_swap() {
    local held="${stream_dir}/obligations-0000/OB.x"
    stat -c %i "${held}/obligation_result.jsonl" "${held}/replay.log" \
      "${held}/question.txt" >"${stream_dir}/exposing-inodes"
    grow_swap_production
    stat -c %i "${held}/before-obligations-0001/obligation_result.jsonl" \
      "${held}/before-obligations-0001/replay.log" \
      "${held}/before-obligations-0001/question.txt" \
      "${held}/obligation_result.jsonl" "${held}/replay.log" \
      >"${stream_dir}/swapped-inodes"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "the growing exploration did not finish: \
$(cat "${stream_dir}/explore.log")"
stream_worker="${stream_dir}/obligations-0000/OB.x"
# The swap set the exposing replay's files aside as copies and renamed the
# re-run's over them, or removed one it lacks: none of the inodes a peer's
# NFS client may have looked up under the worker's names is kept aside or
# under them (Z2M).  A copy is made while its original lives, and the
# re-run's files before the swap, so each differs from its own original's
# inode unless it is that inode.
[[ "$(paste -d ' ' <(cat "${stream_dir}/exposing-inodes" \
      "${stream_dir}/exposing-inodes") "${stream_dir}/swapped-inodes" \
    | awk 'NF == 2 && $1 != $2' | grep -c '')" -eq 5 ]] \
  || fail "an exposing file was moved aside or kept, not copied and replaced: \
$(paste -d ' ' "${stream_dir}/exposing-inodes" "${stream_dir}/swapped-inodes")"
[[ ! -e "${stream_worker}/question.txt" \
    && "$(cat "${stream_worker}/before-obligations-0001/question.txt")" \
      == Q.exposing \
    && "$(jq -r '.sessionId' \
      "${stream_worker}/before-obligations-0001/obligation_result.jsonl")" \
      == SESSION.exposing ]] \
  || fail "the exposing answer is not aside, or a file the re-run lacks is \
still the worker's"
grep -q TASK.grown "${stream_dir}/seed-replay/execution_task_plan.jsonl" \
  || fail "the seed plan is not the grown generation's"
[[ "$(stat -c %i "${stream_dir}/generations/g0/execution_task_plan.jsonl")" \
    == "${stream_seed_plan_inode}" ]] \
  && ! grep -q TASK.grown "${stream_dir}/generations/g0/execution_task_plan.jsonl" \
  || fail "the generation before the growth was rewritten under what runs on it"
[[ "$(stat -c %i "${stream_dir}/obligations-0001/grown_plan.jsonl")" \
    == "$(stat -c %i "${stream_dir}/generations/g1/execution_task_plan.jsonl")" ]] \
  || fail "the grown plan is not kept beside the round that grew it"
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
jq -e -s 'map(select(.obligationId == "OB.x")) | length == 1
  and .[0].verdict == "NOT_ADMITTED" and .[0].sessionId == "SESSION.regrown"' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "the re-run's verdict did not replace the exposing one, once: \
$(cat "${stream_dir}/obligation_results.jsonl")"
jq -e -s 'map(.obligationId) | sort == ["G1","OB.x","Q1","Q2","Q3"]' \
  "${stream_dir}/obligation_results.jsonl" >/dev/null \
  || fail "an obligation queued through the growth, or one the growing \
round proposed, was asked again or dropped: \
$(cat "${stream_dir}/obligation_results.jsonl")"
[[ -s "${stream_dir}/obligations-0001/G1/started-at" ]] \
  || fail "the growing round's own proposal was not queued behind its growth"
[[ "$(cat "${stream_dir}/obligations-0002/in-flight.txt")" == *Q2* \
    && -s "${stream_dir}/obligations-0000/Q2/started-at" \
    && ! -e "${stream_dir}/obligations-0002/Q2" ]] \
  || fail "the obligation queued through the growth was not in flight for \
the round after it: $(cat "${stream_dir}/obligations-0002/in-flight.txt")"
awk -v q="$(cat "${stream_dir}/obligations-0000/Q2/started-at")" \
    -v n="$(cat "${stream_dir}/obligations-0002/Q3/started-at")" \
    'BEGIN{exit !(q < n)}' \
  || fail "a newly planned obligation started before the one queued \
through the growth"
[[ -f "${stream_dir}/instrumented-classes/woven" \
    && ! -e "${stream_dir}/generations/g1/instrumented-classes" ]] \
  || fail "the last generation's tree is not the iteration's once nothing runs"
grep -q 'grown by REGION.grown,TASK.seed SYM.marker#2 (2 exposure(s))' \
    "${stream_dir}/explore.log" \
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
# A growth of grown inputs only weaves nothing new: the generation's plan,
# the tree it stood on.
printf '%s\n' \
  '{"kind":"UNPLANNED_INPUT","taskId":"TASK.seed","symbol":"SYM.marker","k":3,"sessionId":"SESSION.regrown","obligationId":"OB.x"}' \
  >"${stream_dir}/obligations-0002/growth.jsonl"
(
  iteration_dir=${stream_dir}
  stream_generation=1
  stream_plan="${stream_dir}/generations/g1/execution_task_plan.jsonl"
  stream_classes="${stream_dir}/instrumented-classes"
  stream_queue=()
  declare -A stream_queued_at=()
  stream_hold=0
  run_java_main() {
    local args=" $* " output
    output=${args##* --output }
    output=${output%% *}
    cp "${stream_plan}" "${output}"
  }
  campaign_instrument() { fail "grown inputs only were woven again: $*"; }
  campaign_stream_grow "${stream_dir}/obligations-0002"
  [[ "${stream_classes}" == "${stream_dir}/instrumented-classes" \
      && "${stream_plan}" == "${stream_dir}/generations/g2/execution_task_plan.jsonl" \
      && -s "${stream_plan}" ]] \
    || fail "grown inputs only did not keep the tree under the new plan: \
${stream_classes} ${stream_plan}"
) >"${stream_dir}/inputs-only.log" 2>&1 \
  || fail "grown inputs only: $(cat "${stream_dir}/inputs-only.log")"
reset_config

# GROW-2: a doors-only occurrence a value demand reached that no focused
# replay ran (ClosurePlanner#plan): its generation drops the task row's mark,
# plans and weaves nothing, re-runs nothing and owes a round; promoting it
# keeps the iteration's own tree.
grow2="${test_tmp}/grow2"
mkdir -p "${grow2}/obligations-0003" "${grow2}/instrumented-classes" \
  "${grow2}/seed-replay"
: >"${grow2}/instrumented-classes/woven"
printf '%s\n' '{"occurrenceId":"W#1","taskId":"T.W","doorsOnly":true}' \
  '{"occurrenceId":"X#1","taskId":"T.X","doorsOnly":true}' \
  >"${grow2}/execution_task_plan.jsonl"
printf '%s\n' \
  '{"kind":"DOORS_ONLY_UNPAUSED","regionId":"R","node":"nn0","occurrence":"W#1","sessionId":"","obligationId":""}' \
  >"${grow2}/obligations-0003/growth.jsonl"
(
  iteration_dir=${grow2}
  stream_plan=${grow2}/execution_task_plan.jsonl
  stream_classes=${grow2}/instrumented-classes
  stream_generation=0
  stream_dirty=0
  stream_hold=0
  stream_queue=()
  declare -A stream_queued_at=()
  run_java_main() { fail "the exposed-region planner ran with no exposure"; }
  campaign_instrument() { fail "a generation that only dropped a mark wove"; }
  campaign_stream_grow "${grow2}/obligations-0003" >/dev/null
  jq -e -s 'length == 2 and (.[0].doorsOnly == null)
    and .[1].doorsOnly == true' \
    "${grow2}/generations/g1/execution_task_plan.jsonl" >/dev/null \
    || fail "the generation did not drop the reached occurrence's mark alone"
  [[ "${stream_classes}" == "${grow2}/instrumented-classes" \
      && ${#stream_queue[@]} -eq 0 && "${stream_dirty}" == 1 ]] \
    || fail "a dropped mark wove, queued a re-run, or owed no round"
  campaign_stream_promote_generation
  [[ -f "${grow2}/instrumented-classes/woven" ]] \
    || fail "promoting a generation that wove nothing removed the tree"
) || fail "GROW-2 failed"
reset_config


# GROW-CONFIRM: a witness's confirmation holds GROW's swap (Z2M).  OB.x's
# session observed the fatal and exposed a region: its attempt claims and
# queues its confirmation while GROW re-runs OB.x, and the re-run returns
# before the verdict.  The swap waits for it: confirmed, the exploration
# ends on the corpus the attempt composed -- the witness in it, the re-run
# dropped and counted; refuted, the re-run swaps in after it.
for grow_verdict in confirmed refuted; do
  stream_fixture "grow-confirm-${grow_verdict}"
  mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
  printf '2\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
  cat >"${stream_dir}/replay.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
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
  (
    stream_stubs
    concolic_replay_command="${stream_dir}/replay.sh"
    replay_timeout_s=60
    schedule_max_jobs=1
    trace_test=T
    custom_jdk_home=""
    workload_work_dir="${stream_dir}"
    stream_confirm_sleep=4
    [[ "${grow_verdict}" == confirmed ]] || stream_refute=0000
    stream_round_plan() {
      case "$1" in
        0) stream_propose "$2" OB.x ;;
        1) printf '%s\n' \
'{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
             >>"$2/growth.jsonl" ;;
      esac
    }
    do_compose() {
      stream_compose "${composition_manifest}" SAT_CANDIDATE
    }
    run_java_main() {
      [[ "$1" == edu.uva.liftlab.graphchecker.plan.ExposedRegionPlanMain ]] \
        || fail "the step ran an engine main GROW does not: $1"
      local args=" $* " output plan
      plan=${args##* --plan }
      plan=${plan%% *}
      output=${args##* --output }
      output=${output%% *}
      { cat "${plan}"
        printf '{"taskId":"TASK.grown","regionId":"REGION.grown","admissionBasis":"EXPOSED_BY"}\n'
      } >"${output}"
    }
    campaign_instrument() {
      mkdir -p "$2"
      : >"$2/woven"
    }
    campaign_obligation_worker() {
      local worker=$4
      printf '{"taskId":"TASK.seed"}\n' >"${worker}/focused_task.jsonl"
      stream_answer "${worker}" OB.x ADMITTED SESSION.exposing fatal
    }
    campaign_explore "${stream_dir}" iteration-0000
  ) >"${stream_dir}/explore.log" 2>&1 \
    || fail "the ${grow_verdict} witness beside a growth did not finish: \
$(cat "${stream_dir}/explore.log")"
  grow_worker="${stream_dir}/obligations-0000/OB.x"
  grow_ended=$(cut -d. -f1 \
    "${campaign_root}/witness-confirm/0000/replay-ended-at")
  [[ -n "$(find "${campaign_root}" -path '*/SESSION.regrown/manifest.json')" ]] \
    || fail "the ${grow_verdict} case's re-run never returned"
  if [[ "${grow_verdict}" == confirmed ]]; then
    # The confirmed witness with a swap pending at the end: the corpus is
    # exactly the one its attempt composed, and the re-run is dropped,
    # counted, its directory out of the worker.
    jq -e '.stop == "WITNESSED" and .rerunsDropped == ["OB.x"]
      and .reaped == []' "${stream_dir}/exploration.json" >/dev/null \
      && [[ "$(ls "${stream_dir}/sessions")" \
          == "$(cat "${stream_dir}/witness-attempts/0000/corpus.txt")" \
        && -d "${stream_dir}/sessions/SESSION.exposing" \
        && ! -e "${grow_worker}/before-obligations-0001" \
        && ! -e "${grow_worker}/grow-obligations-0001/OB.x" \
        && -s "${campaign_root}/explore-reaped/obligations-0001/OB.x/sessions/SESSION.regrown/manifest.json" ]] \
      || fail "a confirmed witness's session was swapped out, or its \
re-run not dropped and counted: $(ls "${stream_dir}/sessions") \
$(cat "${stream_dir}/exploration.json")"
  else
    jq -e '.stop == "FIXED_POINT" and .rerunsDropped == []
      and ([.witnessAttempts[] | [.attempt, .confirmed]]
           == [["0000", false]])' \
      "${stream_dir}/exploration.json" >/dev/null \
      && [[ -d "${stream_dir}/sessions/SESSION.regrown" \
        && -d "${grow_worker}/before-obligations-0001/sessions/SESSION.exposing" \
        && "$(stat -c %Y "${grow_worker}/before-obligations-0001")" \
          -ge "${grow_ended}" ]] \
      || fail "the re-run did not swap in after the refutation: \
$(cat "${stream_dir}/exploration.json")"
  fi
done

# GROW-REASK: an obligation asked again under its id has a worker in each
# round that asked it; GROW re-runs, and swaps, the one whose replay landed
# the exposing session, whichever round it is in (SGF3-adhoc-21: the first
# ask's worker found no host for its solver, the re-ask exposed a region,
# and GROW failed on "no one worker").  The other ask's worker, its ledger
# row and its session, where it landed one, stay as they were
# (SGF3-bugs-snapshot-no-active: the first ask's NOT_ADMITTED session and
# the re-ask's ADMITTED one both in the corpus).
while IFS='|' read -r reask_case reask_exposing reask_other reask_first; do
  reask_dir="${test_tmp}/grow-reask-${reask_case}"
  reask_iteration="${reask_dir}/iteration-0000"
  reask_sessions="${reask_iteration}/sessions"
  reask_results="${reask_iteration}/obligation_results.jsonl"
  reask_worker="${reask_iteration}/${reask_exposing}/OB.r"
  reask_rerun="${reask_worker}/grow-obligations-0009/OB.r"
  mkdir -p "${reask_iteration}/${reask_other}/OB.r" "${reask_rerun}" \
    "${reask_sessions}/SESSION.exposing" "${reask_rerun}/sessions/SESSION.regrown"
  # The other ask: a world-only answer (its focus row stated, as a solved
  # ask's is), with the session it landed, if any.
  printf '{"taskId":"TASK.seed"}\n' \
    >"${reask_iteration}/${reask_other}/OB.r/focused_task.jsonl"
  jq -n -c --arg session "${reask_first}" '{schemaVersion: 1,
    kind: "OBLIGATION_RESULT", obligationId: "OB.r", verdict: "NOT_ADMITTED",
    sessionId: $session, detail: "world only"}' \
    | tee "${reask_iteration}/${reask_other}/OB.r/obligation_result.jsonl" \
    >"${reask_results}"
  if [[ -n "${reask_first}" ]]; then
    mkdir -p "${reask_sessions}/${reask_first}"
    jq -n -c --arg session "${reask_first}" \
      '{sessionId: $session, obligationIds: ["OB.r"]}' \
      >"${reask_sessions}/${reask_first}/manifest.json"
  fi
  printf '{"taskId":"TASK.seed"}\n' >"${reask_worker}/focused_task.jsonl"
  jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId:
    "OB.r", verdict: "ADMITTED", sessionId: "SESSION.exposing",
    detail: "took the arm"}' \
    | tee "${reask_worker}/obligation_result.jsonl" >>"${reask_results}"
  jq -n -c '{sessionId: "SESSION.exposing", obligationIds: ["OB.r"]}' \
    >"${reask_sessions}/SESSION.exposing/manifest.json"
  jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId:
    "OB.r", verdict: "UNSAT", sessionId: "SESSION.regrown",
    detail: "re-run"}' >"${reask_rerun}/obligation_result.jsonl"
  (
    iteration_dir=${reask_iteration}
    sessions=${reask_sessions}
    results=${reask_results}
    [[ "$(campaign_stream_rerun_dir obligations-0009 OB.r SESSION.exposing)" \
        == "${reask_rerun}" ]] \
      || fail "GROW-REASK ${reask_case}: the re-run is not the exposing \
ask's"
    stream_swaps=("obligations-0009 OB.r SESSION.exposing 0")
    stream_staged=()
    stream_hold=1
    campaign_stream_swap
    printf '%s\n' "${stream_staged[@]}" >"${reask_dir}/staged.txt"
  ) </dev/null >"${reask_dir}/swap.log" 2>&1 \
    || fail "GROW-REASK ${reask_case}: the swap failed: \
$(cat "${reask_dir}/swap.log")"
  [[ "$(jq -r .sessionId "${reask_worker}/obligation_result.jsonl")" \
        == SESSION.regrown \
      && -s "${reask_worker}/before-obligations-0009/sessions/SESSION.exposing/manifest.json" \
      && ! -e "${reask_sessions}/SESSION.exposing" \
      && "$(cat "${reask_dir}/staged.txt")" \
        == "${reask_worker} ${reask_rerun}/sessions SESSION.regrown" \
      && "$(jq -r .detail \
        "${reask_iteration}/${reask_other}/OB.r/obligation_result.jsonl")" \
        == "world only" \
      && ( -z "${reask_first}" \
        || -s "${reask_sessions}/${reask_first}/manifest.json" ) \
      && "$(ls "${reask_worker}/before-obligations-0009/sessions")" \
        == SESSION.exposing \
      && "$(jq -s -c 'map([.verdict, .sessionId])' "${reask_results}")" \
        == "[[\"NOT_ADMITTED\",\"${reask_first}\"],[\"UNSAT\",\"SESSION.regrown\"]]" ]] \
    || fail "GROW-REASK ${reask_case}: the exposing ask was not the one \
swapped: $(cat "${reask_results}") $(cat "${reask_dir}/swap.log")"
done <<'EOF'
later|obligations-0004|obligations-0000|
earlier|obligations-0000|obligations-0004|
both-landed|obligations-0004|obligations-0000|SESSION.first
EOF
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
confirm_stub_task_line="CONFIRM refused: the claim moves a cell nobody minted"
confirm_stub_realized=false
# The campaign's largest measured replay peak, in MB (none: unmeasured).
confirm_peak=""
# The value the replay minted the moved root ROOT.M at ("": no root row).
confirm_stub_planted=true
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
    echo "${confirm_stub_task_line}" >&2
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
  # The moved root as the run minted it: the model's plant, or not.
  [[ -z "${confirm_stub_planted}" ]] \
    || jq -n -c --arg v "${confirm_stub_planted}" '{sessionId: "CONFIRM-1",
      seq: 3, occurrence: {node: "hdfs/dn0#epoch0", regionId: "REGION.m",
        context: {form: "ROOT", role: "XCEIVER", windowIndex: 1}, index: []},
      rootId: "ROOT.M", symbol: "M_Z_m", kind: "MARKER", category: "FAULT",
      recordedValue: $v, declared: true}' \
      >"${sessions}/CONFIRM-1/roots.jsonl"
}
run_confirm() {
  local claim=$1
  rm -rf -- "${campaign_final}/confirm" "${campaign_final}/confirm.json"
  jq -n --arg claim "${claim}" \
    '{solver: {campaignClaim: {claim: $claim}}}' >"${composition_manifest}"
  # The arms at the path ordinal this composition gave the path.
  jq -n --arg anchor "${confirm_anchor}" --arg at "${confirm_path_ordinal:-1}" \
    '{anchor: $anchor,
    claim: {kind: "MARKER_FLIPPED", valuationOrdinal: 1,
      movedRoots: {"ROOT.M": "true"}},
    valuations: [{ordinal: 0, selectedPathId: "P.recorded"},
      {ordinal: 1, selectedPathId: "P.sel", selectedSessionId: "S.sel",
       selectedArms: [{selector: "message_arm__\($at)__b2"},
         {selector: "message_arm__\($at)__a1"}],
       assignment: {"ROOT.M": "true"}}]}' >"${campaign_final}/claim.json"
  (
    run_java_main() {
      case " $* " in
        *" --sessions "*) "${confirm_java[@]}" "$@" ;;
        *) confirm_stub_main "$@" ;;
      esac
    }
    campaign_obligation_replay() { confirm_stub_replay "$@"; }
    campaign_replay_peak_mb=${confirm_peak:-0}
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
run_confirm RUN_DEFECT
[[ ! -e "${campaign_final}/confirm.json" && ! -e "${campaign_final}/confirm" ]] \
  || fail "a claim that is not SAT_CANDIDATE was confirmed"
grep -q 'nothing to confirm' "${confirm_root}/confirm-stage.log" \
  || fail "the stage did not say why it ran nothing"
# The rule, both conditions holding.  The replay is charged the campaign's
# measured replay need: its largest replay peak so far, 1000 MB, times 1.5.
confirm_peak=1000
run_confirm SAT_CANDIDATE
confirm_says true "the claim's anchor observed the fatal" \
  "a clean replay was not confirmed"
[[ "$(cat "${confirm_root}/replay-ran")" == 1536 ]] \
  || fail "the CONFIRM replay was charged $(cat "${confirm_root}/replay-ran") \
MB, not 1.5 times the campaign's 1000 MB peak"
confirm_peak=""
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
# Every replay that does not reach the fatal at the anchor refutes the model,
# a false positive (owner 2026-10-08), one row of refuted_claims.jsonl whose
# reason names how: (a) an edge the model chose that the run did not take, a
# plant it did not make, a session with no gap file, an unadmitted replay;
# (b) no fatal at the anchor (a fatal at another occurrence of the site is not
# the anchor's).  The row is the claim's model (the finding kind, the path,
# the arms, the valuation, the moved roots) and the reason, which every later
# composition of the iteration excludes (compose.Refutations).
# confirm_refutes <reason> <what> [<setup>]: one run, refuted for <reason>.
confirm_refutes() {
  rm -f -- "${confirm_iteration}/refuted_claims.jsonl"
  run_confirm SAT_CANDIDATE
  confirm_says false "$1" "$2"
  [[ "$(jq -r '.refutes' "${campaign_final}/confirm.json")" == true ]] \
    && jq -e -s --arg why "$1" 'length == 1 and (.[0] | .kind == "REFUTED_CLAIM"
      and .model.pathId == "P.sel" and .model.arms == ["message_arm__1__a1",
        "message_arm__1__b2"] and .model.assignment == {"ROOT.M": "true"}
      and .model.moved == {"ROOT.M": "true"} and .outcome == "refuted"
      and (.reason | contains($why)))' \
      "${confirm_iteration}/refuted_claims.jsonl" >/dev/null \
    || fail "$2, and was not refuted as its model: \
$(cat "${campaign_final}/confirm.json" \
  "${confirm_iteration}/refuted_claims.jsonl" 2>&1)"
}
confirm_stub_gaps='{"sessionId":"CONFIRM-1","kind":"CONFIRM_MISMATCH","cls":"DIAGNOSTIC","subject":"WIRE e1","detail":"WIRE e1: the model chose producer p1, the run paired p2"}'
confirm_refutes "the model chose producer p1, the run paired p2" \
  "a mismatched edge was confirmed"
confirm_stub_gaps=""
confirm_stub_fatal=false
confirm_refutes "observed the fatal" "a healthy anchor was confirmed"
for planted in false ""; do
  confirm_stub_planted=${planted}
  confirm_refutes "observed the fatal" \
    "an unplanted healthy run (planted '${planted}') was confirmed"
done
confirm_stub_planted=true
confirm_stub_fatal=true
unset confirm_stub_gaps
confirm_refutes "published no readable" "a session with no gap file was \
confirmed"
confirm_stub_gaps=""
confirm_stub_target_iteration=1
confirm_refutes "1 row(s) at other occurrences did" \
  "a fatal at another occurrence of the site confirmed the claim's anchor"
confirm_stub_target_iteration=0
confirm_stub_verdict=NOT_ADMITTED
confirm_refutes "was NOT_ADMITTED: stub" "an unadmitted replay was confirmed"
confirm_stub_verdict=ADMITTED
unset -f confirm_refutes
rm -f -- "${confirm_iteration}/refuted_claims.jsonl"
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
# A confirmation nothing can run is refused by name, which no replay ran:
# the claim is unconfirmed for that reason, not refuted (refutes false), and
# its model is excluded all the same, its outcome undecided -- a false
# positive, the next claim composed past it (owner 2026-10-08, no refused
# split).  A claim ConfirmMain refutes by name (the run as recorded) is
# refuted without a replay.
confirm_stub_task_status=1
refuted_before=0
run_confirm SAT_CANDIDATE
confirm_says false "CONFIRM refused: the claim moves a cell nobody minted" \
  "a refused confirmation task did not name its reason"
[[ "$(jq -r '.refutes' "${campaign_final}/confirm.json")" == false \
    && "$(grep -c "" "${confirm_iteration}/refuted_claims.jsonl" 2>/dev/null)" \
      -eq $((refuted_before + 1)) \
    && "$(tail -n 1 "${confirm_iteration}/refuted_claims.jsonl" \
      | jq -r '.outcome + " " + .reason')" \
      == "undecided CONFIRM refused: the claim moves a cell nobody minted" ]] \
  || fail "a refused confirmation did not exclude its model, undecided: \
$(cat "${campaign_final}/confirm.json" \
  "${confirm_iteration}/refuted_claims.jsonl" 2>&1)"
refuted_before=$((refuted_before + 1))
confirm_stub_task_line="CONFIRM refutes: the claim moves nothing: its \
witness is the run as recorded"
run_confirm SAT_CANDIDATE
confirm_says false "CONFIRM refutes: the claim moves nothing" \
  "a refuted confirmation task did not name its reason"
[[ "$(jq -r '.refutes' "${campaign_final}/confirm.json")" == true \
    && "$(grep -c "" "${confirm_iteration}/refuted_claims.jsonl" 2>/dev/null)" \
      -eq $((refuted_before + 1)) \
    && "$(tail -n 1 "${confirm_iteration}/refuted_claims.jsonl" \
      | jq -r '.outcome')" == refuted ]] \
  || fail "the run as recorded was not refuted: \
$(cat "${campaign_final}/confirm.json")"
confirm_stub_task_status=0
confirm_stub_task_line="CONFIRM refused: the claim moves a cell nobody minted"
# The exploration's witness was confirmed as it was accepted: the same model,
# composed again, takes that confirmation and is not replayed.
campaign_witness_attempt="${confirm_root}/witness-attempt"
mkdir -p "${campaign_witness_attempt}"
cp -- "${campaign_final}/claim.json" "${campaign_witness_attempt}/claim.json"
jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: true,
  refutes: false, reason: "at the witness", sessionId: "W-1"}' \
  >"${campaign_witness_attempt}/confirm.json"
rm -f -- "${confirm_root}/replay-ran"
run_confirm SAT_CANDIDATE
confirm_says true "at the witness" "the witness's confirmation was not taken"
[[ ! -e "${confirm_root}/replay-ran" ]] \
  || fail "the model the exploration confirmed was replayed again"
campaign_witness_attempt=""
unset -f confirm_stub_main confirm_stub_replay run_confirm confirm_says
unset confirm_anchor confirm_stub_target_iteration confirm_java

# NEXT-CLAIM: a SAT_CANDIDATE CONFIRM refuted (a false positive) does not
# end the campaign while its budget has room: its
# artifacts move to final/refuted/NNNN/ and the next claim is composed.  Not
# when the claim was confirmed, not when the composition repeated a model it
# was told to exclude (matched by its arms' digests, whatever path ordinal
# a composition spelled them with), not past the budget.
next_root="${test_tmp}/next-claim"
next_iteration="${next_root}/iteration-0000"
campaign_final="${next_root}/final"
composition_manifest="${campaign_final}/candidate_composition_manifest.json"
# next_claim <confirmed> <file CONFIRM's verdict recorded the model in>
#   [<refutes>; default: whether that file is refuted_claims]
next_claim() {
  mkdir -p "${campaign_final}/confirm" "${next_iteration}"
  jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE"}}}' \
    >"${composition_manifest}"
  : >"${campaign_final}/candidate.smt2"
  jq -n '{claim: {valuationOrdinal: 0}, valuations: [{ordinal: 0,
    selectedPathId: "P", selectedArms: [{selector: "m__0__a"}],
    assignment: {}}]}' >"${campaign_final}/claim.json"
  jq -n --argjson confirmed "$1" --arg file "$2" \
    --arg refutes "${3:-}" '{confirmed: $confirmed,
    refutes: (if $refutes == "" then $file == "refuted_claims"
              else $refutes == "true" end), reason: "r"}' \
    >"${campaign_final}/confirm.json"
  rm -f -- "${next_iteration}/refuted_claims.jsonl"
  campaign_claim_model "${campaign_final}/claim.json" \
    | jq -c '{model: .}' >"${next_iteration}/$2.jsonl"
}
reset_config
campaign_budget_s=100
campaign_reserve_s=20
reproduce_min_s=1
campaign_started_s=${SECONDS}
next_claim true refuted_claims
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a confirmed claim was followed by another"
# Each refuted claim in turn: its artifacts move to final/refuted/NNNN/.
for next_index in 0 1; do
  next_claim false refuted_claims
  next_out=$(campaign_next_claim "${next_iteration}" 2>&1) \
    || fail "a refuted claim with room in the budget was not followed"
  [[ "${next_out}" == *"was excluded ("* ]] \
    || fail "the next claim after a refuted one did not say why: ${next_out}"
  [[ -s "${campaign_final}/refuted/000${next_index}/claim.json" \
      && -d "${campaign_final}/refuted/000${next_index}/confirm" \
      && ! -e "${campaign_final}/candidate.smt2" ]] \
    || fail "the artifacts of refuted claim ${next_index} did not move out of \
final/"
done
# A claim no replay decided (CONFIRM refused it: refutes false), its model
# excluded all the same, is followed too.
next_claim false refuted_claims false
next_out=$(campaign_next_claim "${next_iteration}" 2>&1) \
  || fail "an undecided claim with room in the budget was not followed: \
${next_out}"
[[ -s "${campaign_final}/refuted/0002/claim.json" ]] \
  || fail "the artifacts of the undecided claim did not move out of final/"
next_claim false refuted_claims
campaign_claim_model "${campaign_final}/claim.json" \
  | jq -c '{model: (.arms = ["m__3__a"])}' \
  >>"${next_iteration}/refuted_claims.jsonl"
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a composition that repeated an excluded model, its arm at another \
path ordinal, was followed"
next_claim false refuted_claims
campaign_reserve_s=120
! campaign_next_claim "${next_iteration}" >/dev/null \
  || fail "a claim past the campaign budget was followed"
[[ -s "${campaign_final}/claim.json" \
    && ! -e "${campaign_final}/refuted/0003" ]] \
  || fail "a claim that ends the campaign left final/"
# Re-decision has a named bound: past campaign_max_claims claims decided
# again, the last claim is published, budget or not.
campaign_reserve_s=20
campaign_max_claims=3
next_claim false refuted_claims
next_out=$(campaign_next_claim "${next_iteration}" 2>&1) \
  && fail "a claim past campaign_max_claims was decided again"
[[ "${next_out}" == *'campaign_max_claims=3'* \
    && ! -e "${campaign_final}/refuted/0003" ]] \
  || fail "the re-decision bound was not named: ${next_out}"
unset -f next_claim
reset_config

# RESERVE-1: the reserve owes COMPOSE and EMIT as long as the longest COMPOSE
# (the last planner round, which reads the same corpus, standing for one not
# yet run), CONFIRM as long as the longest CONFIRM (the seed's REPLAY
# standing for one), REPRODUCE its bound (reproduce_time_factor times the
# recorded workload, at least reproduce_min_s), never less than
# campaign_reserve_s.  HG4's hdfs-11741 lost its
# EMIT to the case timeout when it owed COMPOSE and CONFIRM alone; HR1's
# hdfs-adhoc-07 had the floor's 600 s for its first COMPOSE; SL1's
# hdfs-adhoc-37 owed its 23-min seed replay twice and explored one round.
# Rows: name | stage metrics | planner rounds, each its start and end second
# (- : still planning) | campaign_reserve_s | recorded workload s | the
# reserve.
reserve_case() {
  local root=${test_tmp}/reserve-$1 round=0 span dir got
  mkdir -p "${root}/iteration-0000"
  printf "$2" >"${root}/stage_metrics.tsv"
  for span in $3; do
    dir=$(printf '%s/iteration-0000/obligations-%04d' "${root}" "${round}")
    round=$((round + 1))
    mkdir -p "${dir}"
    touch -d "@$((1000000 + ${span%:*}))" "${dir}/in_flight.jsonl"
    [[ "${span#*:}" == - ]] || touch -d "@$((1000000 + ${span#*:}))" \
      "${dir}/explore_manifest.json"
  done
  got=$(campaign_reserve_s=$4 campaign_recorded_workload_s=$5 \
    reproduce_time_factor=3 reproduce_min_s=30 \
    campaign_stage_metrics="${root}/stage_metrics.tsv" \
    campaign_root="${root}" campaign_reserve)
  [[ "${got}" == "$6" ]] \
    || fail "RESERVE-1 $1: the reserve is ${got} s, not $6 s"
}
reserve_case composed 'COMPOSE\t100000\nREPLAY\t30000\nCONFIRM\t50000\n' \
  '0:400' 20 10 280
reserve_case planned 'REPLAY\t30000\n' '0:5 10:130 140:-' 20 10 300
reserve_case floor 'REPLAY\t30000\n' '' 100 0 100
reserve_case slow-seed 'REPLAY\t1409000\n' '0:60' 20 30 1619
reserve_case native-floor 'REPLAY\t30000\n' '' 20 5 60
unset -f reserve_case

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
  refutes: true,
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
# The last claim, unconfirmed where the claim bound or the budget ran out,
# decided by no replay (CONFIRM refused it, or its decision failed): a false
# positive all the same (owner 2026-10-08, no refused split) --
# SAT_UNCONFIRMED, exit 2 -- never RUN_DEFECT for it; the confirmation that
# no replay decided is still named, a CONFIRM_NO_VERDICT defect.
emit_fixture
jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: false,
  refutes: false, sessionId: "",
  reason: "CONFIRM refused: PAIRING_UNHELD: a view no publication hook publishes"}' \
  >"${campaign_final}/confirm.json"
run_emit
[[ "${emit_status}" -eq 2 ]] \
  || fail "an undecided last claim exited ${emit_status}, not 2: \
$(<"${emit_root}/emit.log")"
jq -e '.claim == "SAT_UNCONFIRMED" and .formulaClaim == "SAT_CANDIDATE"
  and .accepted == false and (.claimReason | contains("PAIRING_UNHELD"))
  and (.claimReason | startswith("no confirmation replay decided the model"))
  and (.whyNotAccepted | startswith("SAT_UNCONFIRMED: CONFIRM refused"))
  and ([.defects[] | select(.stage == "CONFIRM"
        and .code == "CONFIRM_NO_VERDICT")] | length) == 1' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "an undecided last claim was not SAT_UNCONFIRMED: \
$(jq -c '{claim, formulaClaim, claimReason, defects}' \
    "${campaign_final}/result.json")"
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
jq -e '.claim == "RUN_DEFECT" and .confirmation == null' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "a claim that was never confirmed does not carry null: \
$(jq -c '{claim, confirmation}' "${campaign_final}/result.json")"

memory_dir="${test_tmp}/memory"
mkdir -p "${memory_dir}"

# MEMORY-2: the gate's decision.  A start goes only where both the host's
# live charges and its real use, each with the start, stay within the
# ceiling -- 70% of a 31 GB host, 22221 MB -- whichever campaign charged
# them: three 6000 MB obligations fit, and the fourth waits with the host's
# real use still low, since the three may yet grow into what they were
# charged (SB13: lift06 at 29 of 30 GB).  A charge lives while the shell
# that took it renews its lease; one whose holder is gone lapses.  A local
# host and the same host named over ssh are one ledger; a lock a dead
# campaign left behind is broken.
reset_config
campaign_host_gate_root="${memory_dir}/hosts"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
memory_available=30000
campaign_host_available_mb() { echo "${memory_available}"; }
campaign_host_total_mb() { echo 31744; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
memory_charges=()
for memory_start in 1 2 3; do
  campaign_host_try_start lift14 6000 \
    || fail "start ${memory_start} of 6000 MB was refused: \
${campaign_host_wait_reason}"
  memory_charges+=("${campaign_host_charge_id}")
done
run_capturing_status campaign_host_try_start lift14 6000
[[ "${status}" -eq 1 ]] \
  || fail "three starts charged 18000 MB, and a fourth was admitted over \
the 22221 MB ceiling while the host used 1744 MB"
[[ "${campaign_host_wait_reason}" == *"18000 MB charged"*"1744 MB in use"* ]] \
  || fail "the wait does not say what is charged and used: \
${campaign_host_wait_reason}"
# Another campaign, the same host: the same ledger refuses it too.
( run_capturing_status campaign_host_try_start lift14 6000
  exit "${status}" ) \
  && fail "another campaign's start ignored the charges on the host"
[[ "$(campaign_host_room lift14)" -eq 4221 ]] \
  || fail "the room is not what the charges leave: \
$(campaign_host_room lift14)"
# The real use alone refuses too: no charge, 21744 MB in use.
for memory_charge in "${memory_charges[@]}"; do
  campaign_host_release lift14 "${memory_charge}"
done
memory_available=10000
run_capturing_status campaign_host_try_start lift14 6000
[[ "${status}" -eq 1 \
    && "${campaign_host_wait_reason}" == *"0 MB charged"*"21744 MB in use"* ]] \
  || fail "a host using 21744 MB admitted 6000 MB more: \
${campaign_host_wait_reason}"
memory_available=30000
# A charge whose shell is gone lapses with its lease; one whose shell lives
# is renewed past it; one gone ten leases is removed.
memory_lease=("${campaign_host_lease_s}" "${campaign_host_renew_s}")
campaign_host_lease_s=5
campaign_host_renew_s=1
( campaign_host_try_start lift14 6000 ) || fail "a subshell's start failed"
memory_gone=$(live_charges "${campaign_host_gate_root}/lift14")
campaign_host_try_start lift14 6000 || fail "a held start failed"
memory_held=${campaign_host_charge_id}
memory_files="${campaign_host_gate_root}/lift14/charges"
touch -d '1 minute ago' "${memory_files}/${memory_gone}" \
  "${memory_files}/${memory_held}"
sleep 2
[[ "$(campaign_host_charged "${campaign_host_gate_root}/lift14" \
    "$(date +%s)")" -eq 6000 \
    && -e "${memory_files}/${memory_held}" ]] \
  || fail "a held charge lapsed, or one whose shell is gone still counts: \
$(ls -l --time-style=+%s "${memory_files}")"
touch -d '1 hour ago' "${memory_files}/${memory_gone}"
campaign_host_charged "${campaign_host_gate_root}/lift14" "$(date +%s)" \
  >/dev/null
[[ ! -e "${memory_files}/${memory_gone}" ]] \
  || fail "a charge ten leases old was not removed"
campaign_host_release lift14 "${memory_held}"
campaign_host_lease_s=${memory_lease[0]}
campaign_host_renew_s=${memory_lease[1]}
# The head is one ledger under both of its names.
campaign_host_try_start localhost 6000 \
  || fail "the head's first start was refused"
[[ -n "$(live_charges "${campaign_host_gate_root}/gate-head")" \
    && ! -e "${campaign_host_gate_root}/localhost" ]] \
  || fail "a local start is not charged to the head's own name"
# A stale lock: the next try breaks it and the one after starts.
mkdir "${campaign_host_gate_root}/lift15"
mkdir "${campaign_host_gate_root}/lift15/lock"
touch -d '10 minutes ago' "${campaign_host_gate_root}/lift15/lock"
run_capturing_status campaign_host_try_start lift15 6000
[[ "${status}" -eq 3 && ! -e "${campaign_host_gate_root}/lift15/lock" ]] \
  || fail "a lock a dead campaign left was not broken"
campaign_host_try_start lift15 6000 \
  || fail "the host stayed locked"
# A lock held for the instant another start is charged is waited out, not
# answered as no room (campaign_host_try_charge).
mkdir "${campaign_host_gate_root}/lift15/lock"
( sleep 1; rmdir "${campaign_host_gate_root}/lift15/lock" ) &
campaign_host_try_charge lift15 6000
wait
[[ "${status}" -eq 0 ]] || fail "a held lock was answered as ${status}"
unset -f hostname campaign_host_available_mb campaign_host_total_mb
reset_config

# MEMORY-READ: one shell refreshes a host's reading.  While another holds the
# refresh, a reading younger than campaign_host_reading_keep_s is kept and
# the host is not read; an older one is read but not published; a refresh a
# dead shell left is broken and the reading published.
reading_dir="${memory_dir}/reading/lift14"
mkdir -p "${reading_dir}/refresh"
reading_calls="${memory_dir}/reading-calls"
: >"${reading_calls}"
campaign_host_available_mb() { echo read >>"${reading_calls}"; echo 12000; }
campaign_host_poll_s=5
reading_now=$(date +%s)
printf '%s 9000\n' "$(( reading_now - 10 ))" >"${reading_dir}/available"
[[ "$(campaign_host_memory_reading lift14 "${reading_dir}" "${reading_now}")" \
    -eq 9000 && ! -s "${reading_calls}" ]] \
  || fail "a waiter read the host while another refreshed a 10 s reading"
printf '%s 9000\n' "$(( reading_now - 40 ))" >"${reading_dir}/available"
[[ "$(campaign_host_memory_reading lift14 "${reading_dir}" "${reading_now}")" \
    -eq 12000 && "$(cat "${reading_dir}/available")" \
    == "$(( reading_now - 40 )) 9000" ]] \
  || fail "a 40 s reading was kept, or published by a shell not refreshing it"
touch -d '10 minutes ago' "${reading_dir}/refresh"
[[ "$(campaign_host_memory_reading lift14 "${reading_dir}" "${reading_now}")" \
    -eq 12000 && "$(cat "${reading_dir}/available")" \
    == "${reading_now} 12000" && ! -e "${reading_dir}/refresh" ]] \
  || fail "a refresh a dead shell left was not broken: \
$(cat "${reading_dir}/available"), $(ls "${reading_dir}")"
unset -f campaign_host_available_mb
reset_config

# MEMORY-3: a charge is named by its need and released by its id; a head's
# start is charged while its command runs and released when it returns, so
# a head's JVMs, one after another, are never charged twice.
campaign_host_gate_root="${memory_dir}/released"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
campaign_host_available_mb() { echo 20000; }
campaign_host_total_mb() { echo 10000; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
campaign_host_try_start lift14 4000 || fail "a 4000 MB start was refused"
memory_id=${campaign_host_charge_id}
[[ "$(live_charges "${campaign_host_gate_root}/lift14")" == "${memory_id}" \
    && "${memory_id}" == 4000.gate-head.* ]] \
  || fail "a start's charge does not state its need and its id: \
$(live_charges "${campaign_host_gate_root}/lift14")"
campaign_host_release lift14 "${memory_id}"
[[ -z "$(live_charges "${campaign_host_gate_root}/lift14")" ]] \
  || fail "a released start is still charged"
campaign_head_charging=1
campaign_head_charged 7000 bash -c "ls '${campaign_host_gate_root}/\
gate-head/charges' | grep -c '^7000\\.' >'${memory_dir}/during'" \
  || fail "a head's charged command did not run"
[[ "$(cat "${memory_dir}/during")" -eq 1 \
    && -z "$(live_charges "${campaign_host_gate_root}/gate-head")" ]] \
  || fail "a head's start was not charged while it ran and released after"
run_capturing_status campaign_head_charged 7000 false
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
[[ "$(campaign_head_charged 7000 printf artifact 2>/dev/null)" \
    == artifact ]] || fail "a head's wait for memory reached its stdout"
eval "${real_try_start}"
campaign_head_charging=0
campaign_head_charged 999999 true \
  || fail "a start outside a head waited for the ledger"
unset -f hostname campaign_host_available_mb campaign_host_total_mb
reset_config

# MEMORY-4: HEAD ROOM.  A head's host keeps room for the head's next engine
# JVM against every other start -- what its planner or composer starts at
# (campaign_head_need_mb: that JVM's footprint, the composer's with its z3
# room), not the case's engine heap: an obligation counts
# the largest idle, fresh reservation of the host as used, a head's own
# start counts none, one of its JVMs running (busy) or a reservation gone
# stale frees it, and the head gives it up when it exits.  The hosts are
# 100000 MB, so the 70% ceiling leaves 70000 MB to charge and real use
# alone decides here.
campaign_host_gate_root="${memory_dir}/head-room"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
campaign_host_available_mb() { echo 43000; }
campaign_host_total_mb() { echo 100000; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
engine_memory_mb=12000
(
  campaign_head_charging=1
  campaign_head_reserve
  head_room=$(campaign_jvm_charge_mb \
    edu.uva.liftlab.graphchecker.compose.ComposeMain 8192)
  [[ "$(cat "${campaign_host_gate_root}/gate-head/heads/"*)" == "${head_room}" ]] \
    || fail "the head reserved no room on its host, or the engine heap's: \
$(cat "${campaign_host_gate_root}/gate-head/heads/"*)"
  run_capturing_status campaign_host_try_start localhost 6000
  [[ "${status}" -eq 1 && "${campaign_host_wait_reason}" == *"${head_room} MB held \
for a head"* ]] || fail "an obligation took the room a head reserved: \
${campaign_host_wait_reason}"
  campaign_host_try_start lift14 6000 \
    || fail "a head's room was held on another host"
  campaign_head_charged 9000 bash -c "ls '${campaign_host_gate_root}/\
gate-head/heads/' >'${memory_dir}/head-busy'" \
    || fail "the head's own start waited for its own room"
  grep -q '\.busy\.' "${memory_dir}/head-busy" \
    || fail "the head's room is held while its own JVM runs"
  touch -d '20 minutes ago' "${campaign_host_gate_root}/gate-head/heads/"*
  campaign_host_try_start localhost 6000 \
    || fail "a stale reservation still holds room"
  campaign_head_heartbeat
  ( campaign_head_unreserve )
  [[ -n "$(ls "${campaign_host_gate_root}/gate-head/heads/")" ]] \
    || fail "a subshell of the head gave up the head's room"
  # A head step no host has room for holds its need on the host with the
  # most room (lift14's 39400 MB less the 30000 MB reserve, against the
  # head's 39300 less its own room held, an 8192 MB composer's charge): an obligation lift14 would admit
  # is refused while the 9500 MB step waits, the step takes lift14 once it
  # has room, its own hold not held against it, and gives the hold up.
  campaign_worker_hosts="gate-head lift14"
  echo 39400 >"${memory_dir}/lift14-available"
  campaign_host_available_mb() {
    if [[ "$1" == lift14 ]]; then cat "${memory_dir}/lift14-available"
    else echo 39300; fi
  }
  sleep() {
    # Another campaign's start: it holds no hold of its own.
    campaign_head_hold="" run_capturing_status campaign_host_try_start \
      lift14 1000
    echo "${status} ${campaign_host_wait_reason}" >"${memory_dir}/head-held"
    echo 40000 >"${memory_dir}/lift14-available"
  }
  rm -f -- "${campaign_host_gate_root}"/*/charges/*
  campaign_host_try_start lift14 1000 \
    || fail "lift14 refused a start it has room for"
  rm -f -- "${campaign_host_gate_root}"/*/charges/*
  campaign_head_place 9500 >"${memory_dir}/head-place.log"
  unset -f sleep
  [[ "$(cat "${memory_dir}/head-held")" == "1 "*"9500 MB held for a head"* \
     && "${campaign_placed_host}" == lift14 ]] \
    || fail "a waiting head step held no room where it then ran \
(${campaign_placed_host}): $(cat "${memory_dir}/head-held")"
  grep -q 'held on lift14' "${memory_dir}/head-place.log" \
    || fail "a waiting head step did not say where it held its need"
  [[ -z "$(ls "${campaign_host_gate_root}/lift14/heads/")" \
     && "$(cat "${campaign_host_gate_root}/gate-head/heads/"*)" == "${head_room}" ]] \
    || fail "a placed head step kept its hold: \
$(ls "${campaign_host_gate_root}"/*/heads/)"
) || exit 1
[[ -z "$(ls "${campaign_host_gate_root}/gate-head/heads/")" ]] \
  || fail "the head kept its room after it exited"
unset -f hostname campaign_host_available_mb campaign_host_total_mb

# HEAD-PLACE: every heavy step of a head -- an engine JVM of any stage, the
# seed or the CONFIRM replay, a native run of REPRODUCE -- goes wherever
# there is room: the head's own host when it fits, else the pool's host
# with the most room under the ceiling (MemAvailable less the 30000 MB
# reserve of a 100000 MB host), charged there while it runs and released
# after, and run there: --run-placed, in the head's working directory with
# the head's exported variables, a program or a run_engine.sh function with
# its arguments, its standard output passed on as its own.  Per row: the
# head's, lift14's and lift15's MemAvailable, the step's need, and where it
# runs.
place_dir="${memory_dir}/place"
while read -r place_own place_14 place_15 place_need place_expected; do
  rm -rf -- "${place_dir}"
  mkdir -p "${place_dir}"
  (
    campaign_host_gate_root="${place_dir}/hosts"
    campaign_root="${place_dir}"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_worker_hosts="gate-head lift14 lift15"
    campaign_host_total_mb() { echo 100000; }
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
        "$(live_charges "${campaign_host_gate_root}" \
          | grep -c "^${place_need}\\.")"
    }
    export CAUSYNTH_PLACE_PROBE=exported
    cd "${place_dir}"
    [[ "$(campaign_head_charged "${place_need}" place_probe argument)" \
        == "place argument exported 1" ]] \
      || fail "a step of ${place_need} MB did not run from the head's \
directory with its arguments and the head's environment, charged once: \
$(campaign_head_charged "${place_need}" place_probe argument)"
    [[ "$(campaign_head_charged "${place_need}" \
        bash -c 'printf "%s" "${CAUSYNTH_PLACE_PROBE}"')" == exported ]] \
      || fail "a placed program did not see the head's environment"
    place_ran=gate-head
    [[ ! -e "${place_dir}/placed-on" ]] \
      || place_ran=$(cat "${place_dir}/placed-on")
    [[ "${place_ran}" == "${place_expected}" ]] \
      || fail "a step of ${place_need} MB with ${place_own}/${place_14}/\
${place_15} MB available ran on ${place_ran}, not ${place_expected}"
    [[ -z "$(live_charges "${campaign_host_gate_root}")" ]] \
      || fail "a placed step's charge outlived it"
  ) || exit 1
done <<'EOF'
31000 34000 36000 5000 lift15
47000 34000 36000 5000 gate-head
31000 36000 35500 5000 lift14
31000 34000 34000 2000 lift14
EOF

# ENGINE-HEAP: an engine JVM starts at what its main measurably needs, charged
# that, and only a run that outgrows it -- the JVM's exit 3 under
# -XX:+ExitOnOutOfMemoryError -- runs again at twice its heap, up to the
# engine heap, saying so each time; the reader of its standard output sees
# the finished run's alone, and later starts of that main begin at the heap
# it last grew to.  A main with no measured need runs at the engine heap.
# Every run, at the engine heap too, ends at its first out-of-heap error.
engine_test=${test_tmp}/engine-heap
mkdir -p "${engine_test}"
cat >"${engine_test}/java" <<'EOF'
#!/usr/bin/env bash
oom=n
[[ "$1" == -XX:+ExitOnOutOfMemoryError ]] && oom=y
echo "$2" >>"${ENGINE_TEST_LOG}.stack"
echo "heap=${GRAPH_CHECKER_ENGINE_MEMORY_MB} oom=${oom}" >>"${ENGINE_TEST_LOG}"
if [[ "${oom}" == y && "${GRAPH_CHECKER_ENGINE_MEMORY_MB}" -lt 5000 ]]; then
  echo "half of an artifact"
  exit 3
fi
echo whole
EOF
chmod +x "${engine_test}/java"
(
  export ENGINE_TEST_LOG=${engine_test}/log
  java_bin=${engine_test}/java
  engine_memory_mb=16000
  campaign_head_charging=0
  campaign_engine_need_mb() { [[ "$1" != x.Grows ]] || echo 2000; }
  engine_java -Dk=v -cp jar x.Grows a b >"${engine_test}/out" 2>"${engine_test}/err" \
    || fail "an engine JVM that outgrew its need failed"
  [[ "$(cat "${engine_test}/out")" == whole ]] \
    || fail "the outgrown run's output reached its reader: $(cat "${engine_test}/out")"
  [[ "$(grep -c 'Grows ran out of its 2000 MB heap; run again at 4000 MB\|Grows ran out of its 4000 MB heap; run again at 8000 MB' \
      "${engine_test}/err")" == 2 ]] \
    || fail "an engine JVM did not grow one step at a time, saying so: \
$(cat "${engine_test}/err")"
  engine_java -cp jar x.Grows >/dev/null
  engine_java -cp jar x.Other >/dev/null
  engine_need_mb=6000 engine_java -cp jar x.Other >/dev/null
  [[ "$(tr '\n' ' ' <"${engine_test}/log")" == "heap=2000 oom=y heap=4000 oom=y \
heap=8000 oom=y heap=8000 oom=y heap=16000 oom=y heap=6000 oom=y " ]] \
    || fail "engine JVMs did not start at their needs: \
$(tr '\n' ' ' <"${engine_test}/log")"
  engine_memory_mb=6000 engine_java -cp jar x.Grows >/dev/null
  [[ "$(tail -n 1 "${engine_test}/log")" == "heap=6000 oom=y" ]] \
    || fail "an engine JVM started above the engine heap: \
$(tail -n 1 "${engine_test}/log")"
  [[ "$(sort -u "${engine_test}/log.stack")" == -Xss512m ]] \
    || fail "an engine JVM ran at another stack: \
$(sort -u "${engine_test}/log.stack" | tr '\n' ' ')"
)
reset_config

# ENGINE-STACK: every engine JVM -- a head's (engine_java), the served
# planner, a solver, offline A/B's -- runs at campaign_engine_stack: a term
# ~750 binary operations deep overflowed the default stack in an arm's key
# (solr-adhoc-19 SC7).  Each java_bin start names it.
for engine_file in "${repo}/run_engine.sh" \
    "${repo}/tools/regress/offline-ab.sh"; do
  starts=$(grep -c 'env "GRAPH_CHECKER_ENGINE_MEMORY_MB=' "${engine_file}")
  staged=$(grep -A3 --group-separator=@ \
      'env "GRAPH_CHECKER_ENGINE_MEMORY_MB=' "${engine_file}" \
    | awk '/^@$/ {n += hit; hit = 0; next}
           /campaign_engine_stack/ {hit = 1}
           END {print n + hit}')
  (( starts > 0 && starts == staged )) \
    || fail "${engine_file##*/}: ${staged} of ${starts} engine JVM starts \
name campaign_engine_stack"
done

# Z3-ROOM: a JVM that starts z3 is charged its footprint and its z3 room, and
# told the room (--z3-room-mb), so the ledger sees every z3 it may run at once
# (SGF3-adhoc-13: a composer charged its footprint alone ran a z3 to 10.9
# GB): a composer 6144 MB, less where its footprint, the room and a 2048 MB
# margin would not fit under the host's ceiling (70 % of 30000 MB here), the
# least room (256 MB) where nothing is left; a solver a question's room, its
# hard lane 4096 MB; a main that starts no z3 none.  Per row: the main (or a
# solver lane), the heap, the room, the charge.  A composer at 8 and at 16 GB
# is admitted on an idle 31583 MB lift (a charge at the ceiling never was:
# head steps waited for room forever).
(
  campaign_host_total_mb() { echo 30000; }
  while IFS='|' read -r z3_main z3_heap z3_room z3_charge; do
    case "${z3_main}" in
      solver|HARD)
        z3_said="$(campaign_solver_z3_room_mb \
          "$([[ "${z3_main}" != HARD ]] || echo HARD)")|$(\
          campaign_solver_need_mb "" "$([[ "${z3_main}" != HARD ]] \
            || echo HARD)")" ;;
      *)
        z3_said="$(campaign_z3_room_mb "edu.uva.liftlab.graphchecker.${z3_main}" \
          "${z3_heap}")|$(campaign_jvm_charge_mb \
          "edu.uva.liftlab.graphchecker.${z3_main}" "${z3_heap}")" ;;
    esac
    [[ "${z3_said}" == "${z3_room}|${z3_charge}" ]] \
      || fail "Z3-ROOM: ${z3_main} at ${z3_heap} MB: ${z3_said}, not \
${z3_room}|${z3_charge}"
  done <<'EOF'
compose.ComposeMain|8192|6144|15232
compose.ComposeMain|16384|1160|18952
compose.ComposeMain|18000|256|19765
explore.ExploreMain|8192|0|9088
explore.ObligationSolverMain|2048|1152|3712
solver|2048|1152|3712
HARD|2048|4096|6656
EOF
  [[ "$(campaign_z3_room_args edu.uva.liftlab.graphchecker.compose.ComposeMain \
      8192)" == "--z3-room-mb 6144" \
     && -z "$(campaign_z3_room_args edu.uva.liftlab.graphchecker.explore.ExploreMain \
      8192)" ]] \
    || fail "Z3-ROOM: a composer is not told its room, or a planner is"
  campaign_host_gate_root=${test_tmp}/z3-room-idle/hosts
  campaign_host_total_mb() { echo 31583; }
  campaign_host_available_mb() { echo 31583; }
  for z3_heap in 8192 16384; do
    z3_status=0
    campaign_host_try_start localhost "$(campaign_jvm_charge_mb \
      edu.uva.liftlab.graphchecker.compose.ComposeMain "${z3_heap}")" \
      || z3_status=$?
    [[ "${z3_status}" -eq 0 ]] \
      || fail "Z3-ROOM: a composer at ${z3_heap} MB is not admitted on an \
idle host (${z3_status}): ${campaign_host_wait_reason}"
    campaign_host_release localhost "${campaign_host_charge_id}"
  done
)

# HEAD-NEED: every engine JVM is watched where its step runs
# (campaign_engine_jvm) and its peak joins the campaign's engine_peak_mb,
# never lowering it; its status is the JVM's.  The head's held room is that
# peak times 1.25, rounded up to 128 MB, at least 1024 and at most the engine
# heap's JVM footprint (heap + heap/16 + 384); before any was measured, the
# footprint of what its planner or composer starts at; and on top, the z3 room
# its composer is charged (6144 MB: its z3s are children its peak does not
# count).
# Per row: the peaks of the JVMs run in turn (each JVM's exit), the peak
# file after them, and the held room (engine heap 12000).
need_dir=${test_tmp}/head-need
while IFS='|' read -r need_peaks need_file need_room; do
  rm -rf -- "${need_dir}"
  mkdir -p "${need_dir}"
  need_said=$(
    campaign_root=${need_dir}
    engine_memory_mb=12000
    campaign_watch_interval_s=0.1
    campaign_host_total_mb() { echo 30000; }
    for need_run in ${need_peaks}; do
      need_peak=${need_run%:*}
      need_exit=${need_run#*:}
      campaign_process_rss_mb() { echo "${need_peak}"; }
      need_status=0
      campaign_engine_jvm "${campaign_root}/engine_peak_mb" \
        bash -c "sleep 0.3; exit ${need_exit}" || need_status=$?
      [[ "${need_status}" == "${need_exit}" ]] \
        || fail "an engine JVM's exit ${need_exit} came back as ${need_status}"
    done
    printf '%s|%s' "$(cat "${campaign_root}/engine_peak_mb" 2>/dev/null \
      || echo -)" "$(campaign_head_need_mb)"
  )
  [[ "${need_said}" == "${need_file}|${need_room}" ]] \
    || fail "engine peaks ${need_peaks} left ${need_said}, not \
${need_file}|${need_room}"
done <<'EOF'
|-|15232
700:0|700|7168
2949:0 1200:3|2949|9856
9000:0|9000|17408
20000:0 300:0|20000|19278
EOF
campaign_root=""
# HEAD-NEED-LANES: a round's planner and a head step fold their peaks at once
# (campaign_engine_peak, under its lock): of twenty folds racing, the largest
# stands and the lock is gone; a lock a folder left when it was ended (older
# than 10 s) is broken, not waited on.
need_dir=${test_tmp}/head-need-lanes
mkdir -p "${need_dir}"
for need_peak in $(seq 100 100 2000); do
  campaign_engine_peak "${need_dir}/engine_peak_mb" "${need_peak}" &
done
wait
[[ "$(cat "${need_dir}/engine_peak_mb")" == 2000 \
    && ! -e "${need_dir}/engine_peak_mb.lock" ]] \
  || fail "HEAD-NEED-LANES: racing folds left $(cat \
"${need_dir}/engine_peak_mb"), not the largest"
mkdir "${need_dir}/engine_peak_mb.lock"
touch -d '-1 minute' "${need_dir}/engine_peak_mb.lock"
campaign_engine_peak "${need_dir}/engine_peak_mb" 2500 &
need_pid=$!
for need_try in 1 2 3 4 5 6 7 8 9 10; do
  kill -0 "${need_pid}" 2>/dev/null || break
  sleep 0.5
done
! kill "${need_pid}" 2>/dev/null \
  || fail "HEAD-NEED-LANES: a lock left by an ended folder was waited on"
wait "${need_pid}" || true
[[ "$(cat "${need_dir}/engine_peak_mb")" == 2500 ]] \
  || fail "HEAD-NEED-LANES: the fold past a stale lock was lost"

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
[[ -z "$(live_charges "${fanout_dir}/ledger")" ]] \
  || fail "a returned job is still charged: \
$(live_charges "${fanout_dir}/ledger")"
# Resumed once every job returned, it has nothing to run and ends cleanly.
LIFTS=localhost CAUSYNTH_HOST_LEDGER="${fanout_dir}/ledger" JOB_MEMORY_MB=1 \
  bash "${repo}/tools/adhoc/fanout.sh" "${fanout_dir}/jobs" \
  "${fanout_dir}/logs" >"${fanout_dir}/fanout-again.out" 2>&1 \
  || fail "a fanout resumed with every job returned failed: \
$(cat "${fanout_dir}/fanout-again.out")"

# FANOUT-2: an ADMIT_MB job starts only where the ledger has its room and
# holds no charge while it runs (a campaign head reserves its own room).
admit_dir="${test_tmp}/fanout-admit"
mkdir -p "${admit_dir}/logs"
printf '%s\n' "ADMIT_MB=1 find ${admit_dir}/ledger -path '*/charges/*' -type f | wc -l >${admit_dir}/0.out" \
  >"${admit_dir}/jobs"
LIFTS=localhost CAUSYNTH_HOST_LEDGER="${admit_dir}/ledger" \
  bash "${repo}/tools/adhoc/fanout.sh" "${admit_dir}/jobs" \
  "${admit_dir}/logs" >"${admit_dir}/fanout.out" 2>&1 \
  || fail "fanout failed an ADMIT_MB job: $(cat "${admit_dir}/fanout.out")"
[[ "$(tr -d ' ' <"${admit_dir}/0.out")" == 0 ]] \
  || fail "an ADMIT_MB job held a charge while it ran: $(cat "${admit_dir}/0.out")"

# FANOUT-3: a job no host has room for holds its need on the host with the
# most room while it waits (a heads/ hold every other start counts), and the
# hold goes once a job starts: a running campaign's pool no longer takes each
# freed slot ahead of the queued campaigns (round HI3).
hold_dir="${test_tmp}/fanout-hold"
mkdir -p "${hold_dir}/logs"
hold_host=$(campaign_host_key localhost)
mkdir -p "${hold_dir}/ledger/${hold_host}/charges"
hold_block="${hold_dir}/ledger/${hold_host}/charges/99999999.${hold_host}.1.1.1"
: >"${hold_block}"
printf '%s\n' "ADMIT_MB=1234 echo held >${hold_dir}/0.out" >"${hold_dir}/jobs"
( LIFTS=localhost CAUSYNTH_HOST_LEDGER="${hold_dir}/ledger" \
    bash "${repo}/tools/adhoc/fanout.sh" \
    "${hold_dir}/jobs" "${hold_dir}/logs" >"${hold_dir}/fanout.out" 2>&1 ) &
hold_fanout=$!
for _ in $(seq 1 60); do
  compgen -G "${hold_dir}/ledger/*/heads/fanout.*.hold" >/dev/null && break
  sleep 0.5
done
hold_file=$(compgen -G "${hold_dir}/ledger/*/heads/fanout.*.hold" | head -n 1)
[[ -n "${hold_file}" && "$(cat "${hold_file}")" == 1234 \
    && ! -e "${hold_dir}/0.out" ]] \
  || fail "a job with no room held nothing while it waited: \
$(ls -R "${hold_dir}/ledger") $(cat "${hold_dir}/fanout.out")"
# A host another sweep's waiting job holds is not held again.
( LIFTS=localhost CAUSYNTH_HOST_LEDGER="${hold_dir}/ledger" \
    bash "${repo}/tools/adhoc/fanout.sh" "${hold_dir}/jobs" \
    "${hold_dir}/logs2" >"${hold_dir}/fanout2.out" 2>&1 ) &
hold_second=$!
sleep 12
[[ "$(compgen -G "${hold_dir}/ledger/*/heads/fanout.*.hold" | wc -l)" -eq 1 ]] \
  || fail "two waiting sweeps both held one host: \
$(compgen -G "${hold_dir}/ledger/*/heads/fanout.*.hold")"
rm -f -- "${hold_block}"
wait "${hold_fanout}" || fail "fanout failed a held job: $(cat "${hold_dir}/fanout.out")"
wait "${hold_second}" || fail "the second fanout failed: $(cat "${hold_dir}/fanout2.out")"
[[ -s "${hold_dir}/0.out" ]] \
  && ! compgen -G "${hold_dir}/ledger/*/heads/fanout.*.hold" >/dev/null \
  || fail "the held job did not start, or its hold outlived it"

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
# composer starts at with the JVM's own memory beside its heap
# (campaign_head_need_mb, campaign_jvm_footprint_mb), never more than that
# heap's footprint, and the z3 room its composer is charged (6144 MB on a
# 30000 MB host):
# a40's Solr heads asked fanout for 16 GB they never held and waited 90 min
# while one case's obligations filled the lifts.  Per row: the case's
# configuration, its weight and its head's room.
(
  campaign_host_total_mb() { echo 30000; }
  while IFS='|' read -r heads_config heads_heap heads_reserve; do
    [[ "$(case_engine_heap_mb "${heads_config}")" == "${heads_heap}" \
        && "$(case_head_reserve_mb "${heads_config}")" == "${heads_reserve}" ]] \
      || fail "${heads_config} weighs $(case_engine_heap_mb "${heads_config}") \
and reserves $(case_head_reserve_mb "${heads_config}")"
  done <<'EOF'
engine_memory_mb=16384|16384|15232
engine_memory_mb=|8192|15232
engine_memory_mb=4096|4096|10880
EOF
)

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

# SWEEP-1: sweep.sh launches every case with its head's room as its need (an
# engine heap of 1 MB: its JVM footprint, 385 MB, and its composer's z3 room,
# 6144 MB on any lift),
# in the shared pool, and a measurement sweep's stop stage and pruning on the
# job's command line (ssh carries no environment); a case id that names no
# case launches no case.
sweep_dir="${test_tmp}/sweep"
mkdir -p "${sweep_dir}/snap/experiments/x/c" "${sweep_dir}/snap/experiments/lib" \
  "${sweep_dir}/snap/tools/rounds" "${sweep_dir}/out" "${sweep_dir}/ledger"
: >"${sweep_dir}/snap/experiments/x/c/case.sh"
printf '%s\n' '[[ "$3" == config ]] || exit 2' \
  'printf "engine_memory_mb=1\n"' \
  >"${sweep_dir}/snap/experiments/lib/run.sh"
printf 'echo "$2 ${CAUSYNTH_STREAM_SHARED_POOL} ${CAUSYNTH_CAMPAIGN_STOP_AFTER-}" >%s/launched\n' \
  "${sweep_dir}" >"${sweep_dir}/snap/tools/rounds/launch-run.sh"
echo c-one >"${sweep_dir}/cases"
sweep_run() {
  LIFTS=localhost GC_OUT="${sweep_dir}/out" VM_IMAGE=vm \
    CAUSYNTH_CAMPAIGN_STOP_AFTER=SEED PRUNE=0 \
    CAUSYNTH_HOST_LEDGER="${sweep_dir}/ledger" CAUSYNTH_HOST_MAX_USED_PCT=70 \
    bash "${repo}/tools/adhoc/sweep.sh" "${sweep_dir}/snap" "$1" \
    "${sweep_dir}/cases" >"${sweep_dir}/$1.out" 2>&1
}
sweep_run s1 || fail "the sweep failed: $(cat "${sweep_dir}/s1.out")"
[[ "$(cat "${sweep_dir}/launched")" == "c-one true SEED" ]] \
  && grep -q "^ADMIT_MB=6529 PRUNE=0 .* CAUSYNTH_STREAM_SHARED_POOL=true .*\
 CAUSYNTH_CAMPAIGN_STOP_AFTER='SEED' " "${sweep_dir}/out/sweep-s1-jobs.txt" \
  || fail "the sweep's case did not launch with its head's room in the \
shared pool: $(cat "${sweep_dir}/launched" \
    "${sweep_dir}/out/sweep-s1-jobs.txt")"
echo nothing-here >"${sweep_dir}/cases"
! sweep_run s2 && grep -q 'nothing-here names no case' \
    "${sweep_dir}/s2.out" && [[ ! -s "${sweep_dir}/out/sweep-s2-jobs.txt" ]] \
  || fail "a case with no configuration was launched or not named: \
$(cat "${sweep_dir}/s2.out")"

# AB-FRESH: the offline gate's SEED chain (tools/regress/offline-ab.sh
# ab_seed) feeds both sides' trace chains the recording's static artifacts,
# and with AB_FRESH_SLICE=1 each side its own fresh slice.
ab_dir="${test_tmp}/offline-ab"
mkdir -p "${ab_dir}"
ab_reads() {
  : >"${ab_dir}/read"
  (
    # shellcheck source=../../../tools/regress/offline-ab.sh
    source "${repo}/tools/regress/offline-ab.sh"
    ab_side_env() {
      ab_acc=/recorded
      ab_case_dir="$1/$2/$3"
      ab_side_now=$2
      mkdir -p "${ab_case_dir}"
    }
    ab_stage_seed_static() { :; }
    ab_stage_seed_trace() {
      echo "${ab_side_now} ${ab_static}" >>"${ab_dir}/read"
      mkdir -p "${ab_case_dir}/SEED.trace"
      echo exit=0 >"${ab_case_dir}/SEED.trace/status"
    }
    ab_trace_rest() { :; }
    AB_FRESH_SLICE=$1 ab_seed "${ab_dir}" c
  )
  sort "${ab_dir}/read" | tr '\n' ';'
}
[[ "$(ab_reads 0)" == "baseline /recorded;candidate /recorded;" ]] \
  || fail "the gate's trace chains do not share the recording's slice: \
$(ab_reads 0)"
[[ "$(ab_reads 1)" == "baseline ${ab_dir}/baseline/c/SEED.static/out;\
candidate ${ab_dir}/candidate/c/SEED.static/out;" ]] \
  || fail "AB_FRESH_SLICE=1 does not give each side its own slice: \
$(ab_reads 1)"

echo "run_engine campaign helper tests passed"
