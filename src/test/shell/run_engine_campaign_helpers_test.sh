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
  # EMIT's gap ledger is an engine main (contract.GapLedgerMain), run as
  # every main is, at a fixture's heap.
  java_bin=${test_java}
  graphchecker_jar=${default_graphchecker_jar}
  graphchecker_work_dir=${emit_root}
  causynth_loop_default_bound=8
  causynth_system_doors=""
  causynth_doors_only_roots=""
  engine_memory_mb=1024

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
  # The static pass always writes its catalog's gaps, none here.
  gzip -c </dev/null >"${causynth_output_dir}/communication_gaps.jsonl.gz"
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
    : >"${emit_iteration}/sessions/SESSION.seed/${session_kind}.jsonl.gz"
  done
  # Two rows the runtime classed DIAGNOSTIC itself: an arm whose producer ran
  # concretely, and an obligation the solver could not decide in its budget.
  # Neither can change the chain the claim rests on, and each says so on the
  # row rather than in a table a later stage consults.
  printf '%s\n' \
    '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"UNATTESTED_ARM","cls":"DIAGNOSTIC","subject":"IXN.7","detail":"the producer ran concretely"}' \
    '{"schemaVersion":1,"sessionId":"SESSION.seed","kind":"UNPRODUCIBLE_ANSWER","cls":"DIAGNOSTIC","subject":"OBL.slow","detail":"SOLVER_TIMEOUT"}' \
    | gzip -c >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl.gz"
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
# The run manifest names the ledger by the digest its writer took as it wrote
# it (GapLedgerMain): the digest of the file as it is.
[[ "$(jq -r '.artifacts[] | select(.name == "gaps.json") | .sha256' \
      "${campaign_final}/run-manifest.json")" \
    == "$(campaign_digest "${campaign_final}/gaps.json")" ]] \
  || fail "the run manifest names gaps.json by a digest not its own"

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
  | gzip -c >"${emit_iteration}/sessions/SESSION.seed/gaps.jsonl.gz"
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

# IMPORT-GATE: the row contract stops the campaign at IMPORT, or records.
#
# The gate's own rules are checked in ContractTest; what is checked here is
# the control flow the stage wraps around them: a BLOCKING count fails the
# stage naming the first subject, a DIAGNOSTIC-only run goes on, and either
# way the gap file the gate appended is the artifact the failure names.
gate_dir="${test_tmp}/import-gate"
mkdir -p "${gate_dir}/sessions/s1"
printf '%s\n' "${gate_dir}/sessions/s1" >"${gate_dir}/gate.list"
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
  campaign_import_gate "${gate_dir}" iteration-0000 \
    "${gate_dir}/import_gate.json" "${gate_dir}/gate.list" >/dev/null
) || fail "a gate with no blocking violation failed the campaign"
[[ "$(wc -l <"${gate_dir}/campaign_gaps.jsonl")" -eq 1 ]] \
  || fail "the gate's diagnostic row was not appended"
(
  run_java_main() {
    gate_stub 4 2 "decisions.jsonl seq=88 field=outcome" BLOCKING
  }
  campaign_import_gate "${gate_dir}" iteration-0000 \
    "${gate_dir}/import_gate.json" "${gate_dir}/gate.list" >/dev/null
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

# The same gate over the sessions EXPLORE gates before they land is
# STREAM-5's.

# The replays below run under a bound of their own, in a directory of their own;
# the recording's window is what the seed replay's scales the view hold by.
reset_config
bound_dir="${test_tmp}/replay-bound"
mkdir -p "${bound_dir}/causynth/runtime"
echo 1000 >"${bound_dir}/causynth/runtime/window_ms"

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
# the largest so far times 1.5, rounded up to 128 MB, at least 512 MB, until
# eight replays after the seed's returned (MEASURED-TYPICAL: then their
# peaks' 90th percentile); a worker that states none (its solver answered)
# leaves it, and it is said when it is first measured and whenever it moves.  Per row:
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
# MEASURED-TYPICAL: once eight replays after the seed's returned, the need is
# their peaks' 90th percentile times 1.5, and a replay of
# the stream is charged the 90th percentile of their lives' mean resident
# memory (rounded up to 128 MB, at least 512, at most the need; a replay that
# stated no mean counts its peak), its heap still the need, and a host keeps
# room for four ends of their peaks' 90th percentile less that charge;
# before that, a quarter more than the seed's life mean (at most the need),
# and room for ends that reach the largest peak so far.  Per row: the seed's
# peak[/mean], the later replays' peak[/mean], the need, the stream's replay
# charge after them and an end's growth.
while IFS='|' read -r typical_seed typical_peaks typical_need typical_charge \
    typical_spike; do
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
      echo "${typical_peak%/*}" \
        >"${measured_dir}/${typical_n}/workload_rss_mb"
      [[ "${typical_peak}" != */* ]] || echo "${typical_peak#*/}" \
        >"${measured_dir}/${typical_n}/workload_rss_mean_mb"
      campaign_replay_measured "${measured_dir}/${typical_n}" >/dev/null 2>&1
    done
    printf '%s|%s|%s' "$(campaign_replay_need_mb)" \
      "$(campaign_stream_charge_mb REPLAY)" "${campaign_replay_spike_mb}"
  )
  [[ "${typical_got}" == \
      "${typical_need}|${typical_charge}|${typical_spike}" ]] \
    || fail "seed ${typical_seed} and peaks ${typical_peaks} gave \
${typical_got}, not ${typical_need}|${typical_charge}|${typical_spike}"
done <<'EOF'
2234|918 900 950 1000 880 1242 920 910|1920|1280|0
3454|1583 1600 1500|5248|4352|0
1600/867|1991/1040 2088/1000|3200|1152|936
2234|300 310 320 330 340 350 360 370|640|512|0
1000|900 950 1000 1100 1200 1300 1400 3000|4608|3072|0
2234|1557/718 1497/696 1478/834 1304/705 1081/413 955/576 940/664 859/587|2432|896|661
1000|900 950 1000 1100 1200 1300 1400 1500 1450 1350 6476|2304|1536|0
EOF
# PLANNER-START: the planner runs at the engine heap (campaign_stream_plan):
# one is started there when none lives, charged its need for the round
# (campaign_planner_need_mb), a living one is asked as it is once its host
# holds the round's need (campaign_planner_hold), and a round it answers it
# cannot hold (exit 3) is PLANNER_HEAP_EXCEEDED.  A round planned leaves the
# planner's measure and the sessions it read for the next round's need; a
# planner started anew has neither.  Per row: whether a planner lives (its
# heap), the live set it measured last round (- none), whether it read the
# round's one session S1 (100 MB of text), what the ask returns, the status,
# what was done.
plan_dir="${test_tmp}/planner-start"
while IFS='|' read -r plan_heap plan_live plan_read plan_asked plan_status \
    plan_done; do
  rm -rf -- "${plan_dir}"
  mkdir -p "${plan_dir}/planning-0003" "${plan_dir}/planner"
  echo S1 >"${plan_dir}/planning-0003/corpus.txt"
  echo 4321 >"${plan_dir}/planning-0003/planner_live_mb"
  [[ "${plan_live}" == - ]] || echo "${plan_live}" >"${plan_dir}/planner/live_mb"
  [[ "${plan_read}" == - ]] || echo S1 >"${plan_dir}/planner/read.txt"
  plan_got=$(
    iteration_dir=${plan_dir}
    engine_memory_mb=16384
    sessions=${plan_dir}/sessions
    campaign_engine_outgrown=""
    plan_alive=0
    if [[ "${plan_heap}" != - ]]; then
      plan_alive=1
      echo "${plan_heap}" >"${plan_dir}/planner/heap"
      echo 1 >"${plan_dir}/planner/id"
    fi
    campaign_session_bytes() { echo "S1 104857600"; }
    campaign_planner_alive() { (( plan_alive )); }
    campaign_planner_start() { plan_alive=1; echo "start $1 $2" >>"${plan_dir}/done"; }
    campaign_planner_hold() { echo "hold $1" >>"${plan_dir}/done"; }
    campaign_planner_round() { echo ask >>"${plan_dir}/done"; return "${plan_asked}"; }
    status=0
    campaign_stream_plan "${plan_dir}/planning-0003" 2>/dev/null || status=$?
    printf '%s|%s' "${status}" "$(paste -sd ' ' "${plan_dir}/done" \
      2>/dev/null)"
  )
  [[ "${plan_got}" == "${plan_status}|${plan_done}" ]] \
    || fail "PLANNER-START: a planner of ${plan_heap} asked ${plan_asked} \
gave ${plan_got}, not ${plan_status}|${plan_done}"
  if (( plan_status == 0 )); then
    [[ "$(cat "${plan_dir}/planner/live_mb")|$(cat \
        "${plan_dir}/planner/read.txt")" == "4321|S1" ]] \
      || fail "PLANNER-START: a planned round left no measure for the next"
  fi
done <<'EOF'
16384|-|-|0|0|hold 3910 ask
-|2000|S1|0|0|start 16384 3910 hold 3910 ask
16384|2000|S1|0|0|hold 6521 ask
16384|2000|-|3|3|hold 6566 ask
EOF

# PLANNER-NEED: what the planner's host holds for a round
# (campaign_planner_need_mb): its young generation whole (a fifth of the
# heap) and 1.25 times its old generation's need -- the live set it measured
# at its highest last round and 0.35 of the text of the round's sessions it
# has not read -- at most the heap, as a JVM's footprint.  Per row: the
# heap, the live set (MB), the sessions read, the round's sessions with
# their MB, the need.
need_dir="${test_tmp}/planner-need"
while IFS='|' read -r need_heap need_live need_read need_round need_want; do
  rm -rf -- "${need_dir}"
  mkdir -p "${need_dir}/planner" "${need_dir}/planning-0001"
  echo "${need_live}" >"${need_dir}/planner/live_mb"
  tr ' ' '\n' <<<"${need_read}" >"${need_dir}/planner/read.txt"
  : >"${need_dir}/planning-0001/corpus.txt"
  : >"${need_dir}/bytes"
  for need_session in ${need_round}; do
    echo "${need_session%=*}" >>"${need_dir}/planning-0001/corpus.txt"
    echo "${need_session%=*} $(( ${need_session#*=} * 1048576 ))" \
      >>"${need_dir}/bytes"
  done
  # A session landed after the round was planned is no session of it.
  echo "S.late 99999999999" >>"${need_dir}/bytes"
  need_got=$(
    iteration_dir=${need_dir}
    sessions=${need_dir}/sessions
    campaign_session_bytes() { cat "${need_dir}/bytes"; }
    campaign_planner_need_mb "${need_dir}/planning-0001" "${need_heap}"
  )
  [[ "${need_got}" == "${need_want}" ]] \
    || fail "PLANNER-NEED: a planner of ${need_heap} MB, ${need_live} MB \
live, having read ${need_read}, needs ${need_got} for ${need_round}, not \
${need_want}"
done <<'EOF'
24576|0||S1=0|5606
24576|8000|S1|S1=900 S2=4000|18090
24576|20000|S1 S2|S1=900 S2=4000|26496
16384|2000|S1|S1=100|6521
EOF

# PLANNER-HOLD: a round is asked once the planner's host holds its need
# (campaign_planner_hold): the reserve is asked of the planner's watcher,
# and while the watcher holds less the shortfall is held among the head
# reservations of the planner's host, given up once it holds enough; a host
# still short past campaign_planner_hold_max_s (here 2 s) fails the round
# by name, its hold given up -- never a wait without end.  Per row: what the
# watcher holds, what it holds a moment later, the need, whether the round
# waited (failed: past the bound).
hold_dir="${test_tmp}/planner-hold"
while IFS='|' read -r hold_first hold_later hold_need hold_waited; do
  rm -rf -- "${hold_dir}"
  mkdir -p "${hold_dir}/planner" "${hold_dir}/hosts/lift12/heads"
  echo lift12 >"${hold_dir}/planner/host"
  echo "${hold_first}" >"${hold_dir}/planner/reserve_mb.held"
  hold_status=0
  (
    iteration_dir=${hold_dir}
    campaign_host_gate_root=${hold_dir}/hosts
    campaign_host_poll_s=0.1
    campaign_planner_hold_max_s() { echo 2; }
    campaign_planner_alive() { true; }
    ( sleep 0.5; echo "${hold_later}" >"${hold_dir}/planner/reserve_mb.held"
    ) &
    hold_seen=""
    campaign_head_heartbeat() {
      [[ -n "${hold_seen}" ]] || hold_seen=$(cat \
        "${hold_dir}"/hosts/lift12/heads/*.hold 2>/dev/null || true)
      [[ -z "${hold_seen}" ]] || echo "${hold_seen}" >"${hold_dir}/seen"
    }
    held_status=0
    campaign_planner_hold "${hold_need}" 2>"${hold_dir}/said" \
      || held_status=$?
    wait
    exit "${held_status}"
  ) || hold_status=$?
  [[ "${hold_status}" == "$([[ "${hold_waited}" == failed ]] && echo 1 \
      || echo 0)" ]] \
    || fail "PLANNER-HOLD: a hold of ${hold_need} MB (${hold_first} then \
${hold_later} held) ended ${hold_status}: $(cat "${hold_dir}/said")"
  [[ "$(cat "${hold_dir}/planner/reserve_mb")" == "${hold_need}" ]] \
    || fail "PLANNER-HOLD: the watcher was not asked ${hold_need} MB"
  [[ -z "$(ls "${hold_dir}/hosts/lift12/heads")" ]] \
    || fail "PLANNER-HOLD: the shortfall's hold outlived the wait"
  # A short host holds the shortfall while the round waits; one holding
  # enough holds none.
  [[ "$(cat "${hold_dir}/seen" 2>/dev/null || echo 0)" == "$( \
      [[ "${hold_waited}" == no ]] && echo 0 \
      || echo "$(( hold_need - hold_first ))")" ]] \
    || fail "PLANNER-HOLD: a hold of ${hold_need} MB with ${hold_first} \
held held $(cat "${hold_dir}/seen" 2>/dev/null) of the shortfall"
done <<'EOF'
6000|6000|5000|no
2000|6000|5000|yes
2000|3000|5000|failed
EOF
# PLANNER-LIVE: a served planner's answer that it cannot hold the round (its
# live set and the round's new sessions past its old generation's room,
# explore.ExploreMain --serve, exit 3) is the ask's 3, the planner's words
# in the round's heap-predicted, which names the stop.
(
  plan_dir="${test_tmp}/planner-live"
  mkdir -p "${plan_dir}/planning-0006"
  live_dir=$(campaign_planner_dir "${plan_dir}/sessions" 7)
  mkdir -p "${live_dir}/requests" "${live_dir}/answers"
  printf '%s\n' "${BASHPID}" >"${live_dir}/server"
  (
    for (( waited = 0; waited < 100; waited++ )); do
      for request in "${live_dir}"/requests/*.json; do
        [[ -e "${request}" ]] || continue
        name=$(basename "${request}" .json)
        jq -n -c '{exit: 3, error: "the planner needs ~16900 MB of its 17203 MB old generation: 14500 MB live at its highest last round and 0.35 of the 6857 MB of session files it reads now, past 90 % of it"}' \
          >"${live_dir}/answers/${name}.json"
        exit 0
      done
      sleep 0.1
    done
  ) &
  status=0
  campaign_planner_ask "${plan_dir}/sessions" 7 6 \
    "${plan_dir}/planning-0006/in_flight.jsonl" "${plan_dir}/planning-0006" \
    "${plan_dir}/answers.jsonl" "${plan_dir}/corpus.txt" 2>/dev/null \
    || status=$?
  wait
  (( status == campaign_jvm_out_of_heap_status )) \
    || fail "PLANNER-LIVE: a planner's out-of-heap answer asked ${status}"
  grep -q "14500 MB live at its highest last round" \
    "${plan_dir}/planning-0006/heap-predicted" \
    || fail "PLANNER-LIVE: the predicted stop does not carry the planner's \
measure"
)


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

# KEEPER-FDS: a process that outlives the call that started it -- a
# charge's keeper (campaign_host_hold), and as it a host's reader and a host's
# solver (campaign_close_inherited_fds) -- holds none of the call's
# descriptors: a charged call inside $(...), its output redirected as an
# engine JVM's is, returns as its work does, not when its charge's keeper
# ends (the charge stands 3 s here, renewed every 30).
(
  kf_dir=${test_tmp}/keeper-fds
  mkdir -p "${kf_dir}"
  campaign_host_renew_s=30
  : >"${kf_dir}/charge"
  ( command sleep 3; rm -f -- "${kf_dir}/charge" ) &
  kf_call() {
    campaign_host_hold "${kf_dir}/charge" >"${kf_dir}/out"
    echo returned
  }
  kf_start=${SECONDS}
  kf_said=$(kf_call)
  [[ "${kf_said}" == returned ]] && (( SECONDS - kf_start < 2 )) \
    || fail "KEEPER-FDS: a charged call inside \$(...) returned \
'${kf_said}' after $(( SECONDS - kf_start )) s"
  wait
) || fail "KEEPER-FDS failed"

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

# WATCH-RESERVE: a watched JVM given a reserve file (the served planner's,
# campaign_planner_hold) is held at what the file asks ahead of its growth,
# and states what it holds; the reserve refused ends nothing -- the JVM has
# not grown -- and the JVM's own growth past what it holds is still granted
# alone, or ends it, as any watched JVM's.  On a host of 10000 MB at a 70%
# ceiling.  Per row: its MemAvailable, the charge, the reserve asked, the
# JVM's resident memory at each read, whether it was ended, what it held.
reserve_dir="${test_tmp}/watch-reserve"
while IFS='|' read -r reserve_available reserve_charged reserve_asked \
    reserve_rss reserve_ended reserve_held; do
  rm -rf -- "${reserve_dir}"
  mkdir -p "${reserve_dir}/trace" "${reserve_dir}/hosts/gate-head/charges"
  tr ',' '\n' <<<"${reserve_rss}" >"${reserve_dir}/rss"
  echo "${reserve_asked}" >"${reserve_dir}/reserve"
  (
    campaign_host_gate_root="${reserve_dir}/hosts"
    campaign_local_host_names=" localhost gate-head "
    hostname() { echo gate-head; }
    campaign_host_available_mb() { echo "${reserve_available}"; }
    campaign_host_total_mb() { echo 10000; }
    campaign_host_max_used_pct=70
    campaign_watch_interval_s=0.1
    campaign_process_rss_mb() {
      local mb
      mb=$(head -n 1 "${reserve_dir}/rss")
      [[ -n "${mb}" ]] || { kill "$1"; return 1; }
      sed -i 1d "${reserve_dir}/rss"
      echo "${mb}"
    }
    sleep 60 &
    reserve_jvm=$!
    campaign_watch_workload "${reserve_jvm}" "${reserve_charged}" \
      "${reserve_dir}/trace" "" "${reserve_dir}/reserve" \
      2>"${reserve_dir}/said" &
    reserve_pid=$!
    reserve_exit=0
    wait "${reserve_jvm}" 2>/dev/null || reserve_exit=$?
    wait "${reserve_pid}"
    echo "${reserve_exit}" >"${reserve_dir}/exit"
  ) || fail "WATCH-RESERVE: a watch failed"
  reserve_got="$( (( $(cat "${reserve_dir}/exit") == 137 )) && echo ended \
    || echo ran)|$(cat "${reserve_dir}/reserve.held")"
  [[ "${reserve_got}" == "${reserve_ended}|${reserve_held}" ]] \
    || fail "WATCH-RESERVE: a JVM charged ${reserve_charged} MB, reserve \
${reserve_asked}, at ${reserve_rss} MB on a host with ${reserve_available} MB \
was ${reserve_got}, not ${reserve_ended}|${reserve_held}: $(cat \
"${reserve_dir}/said")"
  [[ -z "$(ls "${reserve_dir}/hosts/gate-head/charges")" ]] \
    || fail "WATCH-RESERVE: what the JVM was granted outlived it"
done <<'EOF'
28000|2000|5000|1000,1000,1000|ran|5000
5000|2000|5000|1000,1000,1000|ran|2000
5000|2000|5000|1000,2600,2600|ran|2600
3000|2000|5000|1000,2600|ended|2000
28000|2000|1500|1000,1800|ran|2000
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
  # Cold: a question charged a solver's need (a cold host's start) hands that
  # charge to the solver it starts -- one charge on the host, the solver's,
  # never a second (SGF7-adhoc-39: no cold host had room for two).
  campaign_host_max_used_pct=100
  mkdir -p "${solver_test}/d"
  status=0
  campaign_host_try_charge localhost "$(campaign_solver_need_mb \
    "${solver_test}/iteration/sessions")"
  cold_charge=${campaign_host_charge_id}
  campaign_solve_obligation OB.d "${solver_wave}/obligations.jsonl" \
    "${solver_test}/iteration/sessions" "${solver_test}/d" "${cold_charge}" \
    >/dev/null 2>&1 || status=$?
  [[ "${status}" -eq 1 && "$(live_charges "${solver_test}/hosts")" \
       == *"${cold_charge}.solver"* \
     && "$(live_charges "${solver_test}/hosts" | wc -w)" -eq 1 ]] \
    || fail "a cold question's solver did not take its charge over \
(${status}): $(live_charges "${solver_test}/hosts")"
  for ((waited = 0; waited < 30; waited++)); do
    [[ -e "${solver_home}/server" ]] || break
    sleep 1
  done
  # Retired: the solver its asker started gave its corpus up
  # (Service#retireOutgrown: <dir>/retired names it, the question untaken), so
  # that asker starts the next one, sized anew, which answers it -- never
  # "the solver ended before it answered".
  mkdir -p "${solver_test}/e"
  : >"${solver_test}/solvers"
  campaign_start_solver() {
    echo "$1" >>"${solver_test}/solvers"
    if [[ "$(wc -l <"${solver_test}/solvers")" -gt 1 ]]; then
      solver_started "$@"
      return
    fi
    ( sleep 1
      until mkdir "$1/lock" 2>/dev/null; do sleep 0.1; done
      cat "$1/server" >"$1/retired"
      rm -f -- "$1/server"
      rmdir "$1/lock" ) &
    printf '%s\n' "$!" >"$1/server"
  }
  status=0
  campaign_solve_obligation OB.e "${solver_wave}/obligations.jsonl" \
    "${solver_test}/iteration/sessions" "${solver_test}/e" \
    >/dev/null 2>"${solver_test}/e.err" || status=$?
  [[ "${status}" -eq 1 && "$(wc -l <"${solver_test}/solvers")" -eq 2 ]] \
    && grep -q "the round has no obligation OB.e" "${solver_test}/e.err" \
    || fail "a retired solver's question was not asked of the next one \
(${status}, $(wc -l <"${solver_test}/solvers") starts): \
$(cat "${solver_test}/e.err")"
)

# SOLVE-WORKER: NO QUESTION IS ANSWERED IN A CORPUS JVM OF ITS OWN.  A first
# ask goes to its host's solver under its start's charge (a cold host's, the
# solver's to take over); one whose host had no room to start its solver (3)
# is asked again of a host's solver, uncharged in the pool's queue
# (solve_again); one its solver ended on or failed (1) is asked again once,
# then fails the worker by name -- but a solver that ended for memory (4)
# fails none of its questions: asked again uncounted, at most
# campaign_solver_memory_asks times (memory: those spent), then counted.
# A HARD ask is z3 alone over its first ask's
# query (campaign_obligation_decide: ObligationSolverMain --decide, its
# charge, the full budget, the hard lane's z3 room); its answer is the
# obligation's, a model is asked again of a host's solver to finish the flip,
# and a JVM that failed fails the worker by name.  Per row: the lane, what
# the host's solver or the hard lane's JVM returns (model: a model and no
# answer), whether it was asked again before, and what it ends in: its
# answer, its ask again, or why it fails; every ask made.
worker_test=${test_tmp}/solve-worker
while IFS='|' read -r sw_lane sw_returns sw_before sw_end sw_asks; do
  sw_dir="${worker_test}/${sw_lane}${sw_returns}${sw_before}"
  mkdir -p "${sw_dir}"
  [[ "${sw_before}" != before ]] || : >"${sw_dir}/asked_again"
  [[ "${sw_before}" != memory ]] \
    || printf '\n%.0s' $(seq "${campaign_solver_memory_asks}") \
      >"${sw_dir}/asked_again_memory"
  sw_log="$(campaign_stream_logs "${sw_lane}" "${sw_dir}")stderr.log"
  sw_status=0
  (
    solver_timeout_ms=1800000
    campaign_log() { echo "[campaign] $*" >&2; }
    sw_answer() {
      printf '{"verdict":"UNSAT","obligationId":"OB.1"}\n' \
        >"$1/obligation_result.jsonl"
      printf '(assert false)\n' | gzip -c >"$1/obligation_query.smt2.gz"
    }
    campaign_solve_obligation() {
      printf 'service %s,' "$5" >>"$4/asked"
      case "${sw_returns}" in
        0) sw_answer "$4" ;;
        1) echo "ObligationSolverMain: the solver of lift12 ended" >&2 ;;
      esac
      return "${sw_returns}"
    }
    campaign_solver_jvm() {
      printf 'decide %s at %s in %s,' "$2" "$3" "$4" >>"${sw_dir}/asked"
      case "${sw_returns}" in
        0) sw_answer "${sw_dir}" ;;
        model) printf '{}\n' >"${sw_dir}/obligation_model.json" ;;
        1) echo "java.lang.IllegalStateException: the record" >&2
           return 1 ;;
      esac
    }
    campaign_obligation_worker OB.1 obligations "${sw_dir}/sessions" \
      "${sw_dir}" 5024 "$([[ "${sw_lane}" == HARD ]] && echo HARD \
        || echo charge.1)"
  ) >"${sw_dir}/stdout.log" 2>"${sw_log}" || sw_status=$?
  [[ "$(cat "${sw_dir}/asked")" == "${sw_asks}" ]] \
    || fail "SOLVE-WORKER ${sw_lane} ${sw_returns}: asked \
$(cat "${sw_dir}/asked"), not ${sw_asks}"
  [[ "${sw_end}" != UNSAT && "${sw_end}" != again:no* \
     || ! -e "${sw_dir}/asked_again" ]] \
    || fail "SOLVE-WORKER ${sw_lane} ${sw_returns}: its earlier ask again \
outlived an answer or a new reason"
  case "${sw_end}" in
    UNSAT)
      [[ "${sw_status}" -eq 0 && ! -e "${sw_dir}/solve_again" \
         && "$(jq -r .verdict "${sw_dir}/obligation_result.jsonl")" \
           == UNSAT ]] \
        || fail "SOLVE-WORKER ${sw_lane} ${sw_returns}: not answered \
(${sw_status}): $(cat "${sw_log}")" ;;
    again:*)
      [[ "${sw_status}" -eq 0 \
         && ! -e "${sw_dir}/obligation_result.jsonl" \
         && "$(jq -r .why "${sw_dir}/solve_again" 2>/dev/null)" \
           == "${sw_end#again:}"* ]] \
        || fail "SOLVE-WORKER ${sw_lane} ${sw_returns}: \
$(cat "${sw_dir}/solve_again" 2>/dev/null) (${sw_status}), not ${sw_end}" ;;
    *)
      [[ "${sw_status}" -ne 0 && ! -e "${sw_dir}/solve_again" \
         && ! -e "${sw_dir}/obligation_result.jsonl" ]] \
        && grep -qF "Error: obligation OB.1: ${sw_end}" "${sw_log}" \
        || fail "SOLVE-WORKER ${sw_lane} ${sw_returns}: did not fail by \
name (${sw_status}): $(cat "${sw_log}")" ;;
  esac
done <<'EOF_WORKER'
OBLIGATION|0||UNSAT|service charge.1,
OBLIGATION|0|before|UNSAT|service charge.1,
OBLIGATION|3|before|again:no room on |service charge.1,
OBLIGATION|1||again:its host's solver did not answer (ObligationSolverMain: the solver of lift12 ended)|service charge.1,
OBLIGATION|1|before|its host's solver did not answer it, asked twice: ObligationSolverMain: the solver of lift12 ended|service charge.1,
OBLIGATION|4|before|again:its host's solver ended for memory|service charge.1,
OBLIGATION|4|memory|again:its host's solver did not answer|service charge.1,
HARD|0||UNSAT|decide 5024 at 1800000 in 4096,
HARD|model||again:the hard lane found a model|decide 5024 at 1800000 in 4096,
HARD|1||its hard-lane ask failed (exit 1): java.lang.IllegalStateException: the record|decide 5024 at 1800000 in 4096,
EOF_WORKER

# SOLVER-MEMORY-END: a host solver's end is one for memory -- none of its
# questions' failure (campaign_solver_ended_for_memory) -- when it ran out
# of heap below the most heap a solver is given (a larger one follows), or
# its watcher ended it for its host's room (137); not at the most heap, nor
# for any other end, nor when it stated none.  Per row: its status and heap
# (- none stated), whether it is a memory end (engine heap 16384).
sme_dir=${test_tmp}/solver-memory-end
mkdir -p "${sme_dir}"
while IFS='|' read -r sme_status sme_heap sme_want; do
  rm -f -- "${sme_dir}/ended.77"
  [[ "${sme_status}" == - ]] \
    || echo "${sme_status} ${sme_heap}" >"${sme_dir}/ended.77"
  sme_said=$(
    engine_memory_mb=16384
    campaign_solver_ended_for_memory "${sme_dir}" 77 && echo yes || echo no
  )
  [[ "${sme_said}" == "${sme_want}" ]] \
    || fail "SOLVER-MEMORY-END: ${sme_status} at ${sme_heap}: ${sme_said}"
done <<'EOF'
3|8192|yes
3|16384|no
137|16384|yes
1|8192|no
-|-|no
EOF

# SOLVER-HEAP: a corpus's solver is sized by its session files
# (campaign_corpus_mb, stated beside the corpus): the heap its live set needs
# now (50 % of them, at 150 % for the collector, at least 2048 MB, never less
# than a heap a solver of it ran out of), room to grow to twice that, up to
# the engine heap; charged that need's footprint and the z3 room its seats
# share (two questions' rooms, 2304 MB); and a host's solver gives its corpus up past what its heap holds
# (0 at the engine heap).  Per row: the engine heap, the corpus's MB, the
# heaps its solvers ran out of, in order, and the heap, charge and retire
# point after.
solver_heap_dir=${test_tmp}/solver-heap
while IFS='|' read -r sh_engine sh_corpus sh_outgrown sh_heap sh_need \
    sh_retire; do
  rm -rf -- "${solver_heap_dir}"
  mkdir -p "${solver_heap_dir}/sessions"
  printf '%s %s\n' "$(date +%s)" "${sh_corpus}" \
    >"${solver_heap_dir}/corpus_mb"
  sh_said=$(
    engine_memory_mb=${sh_engine}
    for sh_out in ${sh_outgrown}; do
      campaign_solver_outgrown "${solver_heap_dir}/sessions" "${sh_out}"
    done
    sh_at=$(campaign_solver_heap_mb "${solver_heap_dir}/sessions")
    printf '%s %s %s' "${sh_at}" \
      "$(campaign_solver_need_mb "${solver_heap_dir}/sessions")" \
      "$(campaign_solver_retire_mb "${sh_at}")"
  )
  [[ "${sh_said}" == "${sh_heap} ${sh_need} ${sh_retire}" ]] \
    || fail "engine ${sh_engine}, corpus ${sh_corpus} MB, outgrown \
[${sh_outgrown}]: ${sh_said}, not ${sh_heap} ${sh_need} ${sh_retire}"
done <<'EOF_HEAP'
16384|0||4096|4864|5461
16384|3000||4500|5078|6000
16384|9974||14960|10635|19946
16384|20000||16384|18625|0
16384|0|2048|4096|4864|5461
16384|0|2048 4096 8192|16384|11392|0
6144|0|2048 4096|6144|7040|0
1024|0||1024|3776|0
16384|0|4096 2048|8192|7040|10922
EOF_HEAP

# SOLVER-MEASURED: once a corpus's solvers stated their live set after a read
# (<iteration>/solver_live/: "<live MB> <corpus MB>", ObligationSolverMain),
# a solver is sized by the share the read of the largest corpus measured,
# rounded up, not campaign_solver_live_pct; a composer keeps that rule.  Per
# row: the statements, the corpus's MB, the share, a solver's heap, charge
# and retire point, and a composer's heap (engine heap 16384).
while IFS='|' read -r sm_stated sm_corpus sm_pct sm_heap sm_need sm_retire \
    sm_compose; do
  rm -rf -- "${solver_heap_dir}"
  mkdir -p "${solver_heap_dir}/sessions" "${solver_heap_dir}/solver_live"
  printf '%s %s\n' "$(date +%s)" "${sm_corpus}" >"${solver_heap_dir}/corpus_mb"
  sm_at=0
  for sm_one in ${sm_stated}; do
    sm_at=$((sm_at + 1))
    echo "${sm_one/:/ }" >"${solver_heap_dir}/solver_live/host.${sm_at}"
  done
  sm_said=$(
    engine_memory_mb=16384
    sm_got=$(campaign_solver_measured_pct "${solver_heap_dir}/sessions")
    sm_h=$(campaign_solver_heap_mb "${solver_heap_dir}/sessions")
    printf '%s %s %s %s %s' "${sm_got}" "${sm_h}" \
      "$(campaign_solver_need_mb "${solver_heap_dir}/sessions")" \
      "$(campaign_solver_retire_mb "${sm_h}" "${sm_got}")" \
      "$(campaign_solver_heap_mb "${solver_heap_dir}/sessions" \
        "${campaign_solver_live_pct}")"
  )
  [[ "${sm_said}" == "${sm_pct} ${sm_heap} ${sm_need} ${sm_retire} \
${sm_compose}" ]] \
    || fail "SOLVER-MEASURED: [${sm_stated}] over ${sm_corpus} MB: \
${sm_said}"
done <<'EOF_MEASURED'
|20000|50|16384|18625|0|16384
3000:20000 900:300|20000|15|9000|7469|40000|16384
3001:20000|20000|16|9600|7788|40000|16384
600:300|3000|200|16384|12250|0|4500
EOF_MEASURED

# COMPOSE-HEAP: a composer starts at its corpus's heap, as a solver's
# (do_compose: campaign_solver_heap_mb of the sessions it reads).  Per row:
# the corpus's MB, the heap its composer starts at.
while read -r ch_corpus ch_heap; do
  rm -rf -- "${solver_heap_dir}"
  mkdir -p "${solver_heap_dir}/sessions"
  printf '%s %s\n' "$(date +%s)" "${ch_corpus}" \
    >"${solver_heap_dir}/corpus_mb"
  ch_said=$(
    engine_memory_mb=16384
    compose_sessions_dir="${solver_heap_dir}/sessions"
    composed_smt="${solver_heap_dir}/final/candidate.smt2"
    campaign_declared_target_occurrence() { :; }
    run_java_main() { printf '%s' "${engine_need_mb}"; }
    do_compose
  )
  [[ "${ch_said}" == "${ch_heap}" ]] \
    || fail "a composer of ${ch_corpus} MB of sessions started at \
${ch_said} MB, not ${ch_heap}"
done <<'EOF_HEAP'
0 4096
3200 4800
10969 16384
EOF_HEAP

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
  printf '(assert true)\n' | gzip -c >"$1/obligation_query.smt2.gz"
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

# REPLAY-ENDED-MEMORY: a replay its watcher ended because its host could not
# take its growth (campaign_watch_workload states what it reached,
# workload_refused_mb) decided nothing and is no answer: its run -- log,
# measures, the session it opened -- goes aside under its worker, the
# solver's row and its question stay, and replay_again tells the head what it
# reached, what it was charged and where it went (campaign_replay_set_aside),
# for the head to ask it again at its full need.
worker_dir="${bound_dir}/ended"
mkdir -p "${worker_dir}/sessions/SESSION.E"
printf '{"obligationIds":["OB.E"]}\n' \
  >"${worker_dir}/sessions/SESSION.E/manifest.json"
replay_timeout_s=60
concolic_replay_command='printf "%s\n" 2900 >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/\
workload_refused_mb"; echo 2900 >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/\
workload_rss_mb"; kill -KILL $$'
bound_solved "${worker_dir}" OB.E
: >"${worker_dir}/question.asked"
(
  campaign_obligation_replay OB.E "${bound_dir}/classes" "${worker_dir}" \
    "${worker_dir}/sessions" "${bound_dir}/seed_plan.jsonl" 1024 1536
) >"${bound_dir}/ended.log" 2>&1 \
  || fail "the worker did not return when its replay was ended for memory: \
$(cat "${bound_dir}/ended.log")"
read -r ended_mb ended_charged ended_aside ended_heap \
  <"${worker_dir}/replay_again" || ended_mb=""
[[ "${ended_mb} ${ended_charged} ${ended_aside} ${ended_heap}" \
    == "2900 1024 ${worker_dir}/ended-1 -" \
   && "$(jq -r '.verdict' "${worker_dir}/obligation_result.jsonl")" \
    == SAT_MODEL_READY && -e "${worker_dir}/question.asked" \
   && -s "${worker_dir}/ended-1/replay.log" \
   && -s "${worker_dir}/ended-1/workload_refused_mb" \
   && -s "${worker_dir}/ended-1/workload_rss_mb" \
   && -d "${worker_dir}/ended-1/sessions/SESSION.E" \
   && ! -e "${worker_dir}/replay.log" && ! -e "${worker_dir}/workload_rss_mb" \
   && ! -e "${worker_dir}/sessions/SESSION.E" ]] \
  || fail "a replay ended for memory was not set aside to be asked again: \
$(cat "${worker_dir}/replay_again" 2>&1) $(ls -R "${worker_dir}") \
$(cat "${bound_dir}/ended.log")"
# Its worker is as before the run: the next run of it starts there.
rm -f -- "${worker_dir}/replay_again"
concolic_replay_command='kill -KILL $$'
(
  campaign_obligation_replay OB.E "${bound_dir}/classes" "${worker_dir}" \
    "${worker_dir}/sessions" "${bound_dir}/seed_plan.jsonl" 4352 4352
) >"${bound_dir}/ended2.log" 2>&1 \
  || fail "a replay asked again in its worker did not run there: \
$(cat "${bound_dir}/ended2.log")"
[[ ! -e "${worker_dir}/replay_again" \
   && "$(jq -r '.detail' "${worker_dir}/obligation_result.jsonl")" \
    == "REPLAY_BOUNDED: replay was killed (exit 137) after "*"s, inside its \
60s bound: by its memory reservation (the replay log says so), the kernel's \
memory killer or an operator" ]] \
  || fail "a replay killed, not for memory, after a memory end was not \
answered REPLAY_BOUNDED: $(cat "${worker_dir}/obligation_result.jsonl")"
# A replay out of heap (exit 3: -XX:+ExitOnOutOfMemoryError or HeapWatch) is
# set aside the same way, replay_again naming the heap it ran out of.
worker_dir="${bound_dir}/heap"
mkdir -p "${worker_dir}"
concolic_replay_command='echo 900 >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/\
workload_rss_mb"; exit 3'
bound_solved "${worker_dir}" OB.H
(
  campaign_obligation_replay OB.H "${bound_dir}/classes" "${worker_dir}" \
    "${worker_dir}/sessions" "${bound_dir}/seed_plan.jsonl" 1024 9216
) >"${bound_dir}/heap.log" 2>&1 \
  || fail "the worker did not return when its replay ran out of heap: \
$(cat "${bound_dir}/heap.log")"
read -r ended_mb ended_charged ended_aside ended_heap \
  <"${worker_dir}/replay_again" || ended_mb=""
[[ "${ended_charged} ${ended_aside} ${ended_heap}" \
    == "1024 ${worker_dir}/ended-1 4608" \
   && "$(cat "${worker_dir}/ended-1/workload_out_of_heap_mb")" == 4608 \
   && "$(jq -r '.verdict' "${worker_dir}/obligation_result.jsonl")" \
    == SAT_MODEL_READY ]] \
  || fail "a replay out of heap was not set aside to be asked again: \
$(cat "${worker_dir}/replay_again" 2>&1) $(cat "${bound_dir}/heap.log")"

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
: >"${withdraw_sessions}/SESSION.other/activations.jsonl.gz"
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
[[ -f "${withdraw_sessions}/SESSION.other/activations.jsonl.gz" ]] \
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
# The weave key a fixture's plan stands for where a test stubs
# campaign_weave_key (WEAVE-KEY runs the JVM, over task rows whole): its
# task ids, the one weave input these fixtures' growths change.
test_weave_key() {
  jq -r '.taskId' "$1" | LC_ALL=C sort -u | sha256sum | cut -c1-64
}

stream_fixture() {
  stream_dir="${test_tmp}/$1/iteration-0000"
  mkdir -p "${stream_dir}/sessions" "${stream_dir}/seed-replay"
  printf '{"taskId":"TASK.seed"}\n' >"${stream_dir}/execution_task_plan.jsonl"
  ln -f "${stream_dir}/execution_task_plan.jsonl" \
    "${stream_dir}/seed-replay/execution_task_plan.jsonl"
  # What INSTRUMENT left beside the iteration's tree.
  test_weave_key "${stream_dir}/execution_task_plan.jsonl" \
    >"${stream_dir}/weave_key"
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
# <id> <peak> <log> <jvm_file> <charged> <reserve> <args...>): it names
# itself where its rounds are asked and answers each with stream_planner,
# over the corpus and the answers the question names, until it is ended --
# or until stream_planner_dies <round> <heap> says it ends there with that
# status (3: out of heap, its JVM's last words in its log).  Its watcher
# holds what its reserve asks (campaign_watch_workload), on a host with room.
stream_planner_serve() {
  local heap=$1 id=$2 log=$4 reserve=$7 sessions="" dir request name round
  local status refused
  printf '%s\n' "${BASHPID}" >"$5"
  shift 7
  while [[ $# -gt 0 ]]; do
    [[ "$1" != --sessions ]] || sessions=$2
    shift
  done
  dir=$(campaign_planner_dir "${sessions}" "${id}")
  mkdir -p "${dir}/requests" "${dir}/answers"
  printf '%s\n' "${heap}" >>"${stream_dir}/planner-heaps.txt"
  printf '%s\n' "${BASHPID}" >"${dir}/server"
  while true; do
    [[ ! -s "${reserve}" ]] || cp -f -- "${reserve}" "${reserve}.held"
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
      refused=$(stream_planner_refuses "${round}")
      if [[ -n "${refused}" ]]; then
        jq -n -c --arg why "${refused}" '{exit: 3, error: $why}' \
          >"${dir}/answers/${name}.part"
        mv -- "${dir}/answers/${name}.part" "${dir}/answers/${name}.json"
        rm -f -- "${dir}/requests/${name}.taken"
        continue
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
# stream_planner_refuses <round> says why the served planner answers that it
# cannot hold that round (ExploreMain --serve's out-of-heap answer), or
# nothing.
stream_planner_refuses() { :; }

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
  # Its sessions read (ExploreMain#CORPUS_READ): a swap may withdraw one.
  : >"${out}/corpus_read"
  [[ ! -f "${answers}" ]] || jq -r '.obligationId' "${answers}" \
    | LC_ALL=C sort | paste -sd ' ' - >"${out}/answers-read.txt"
  : >"${out}/obligations.jsonl"
  printf '{"kind":"FRONTIER","open":0}\n' >"${out}/growth.jsonl"
  stream_wave=0
  stream_round_plan "${round}" "${out}"
  # Every round states the world depth its paths were cut by: unbounded
  # (ObligationFactory.Bounds), unless a case sets the owner's cap.
  jq -n --argjson wave "${stream_wave}" \
    --argjson truncated "${stream_truncated:-0}" \
    --argjson depth "${stream_test_world_depth:-2147483647}" \
    '{wave: $wave, witnesses: [], branchesStopped: 0, truncated: $truncated,
      anchorOccurrences: [{node: "anchor"}], maxWorldDepth: $depth}' \
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
      | gzip -c >"${worker}/sessions/${session}/targets.jsonl.gz"
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
  campaign_weave_key() { test_weave_key "$1"; }
  campaign_planner_serve() { stream_planner_serve "$@"; }
  # Where CONFIRM stands.  Its task planned: a verdict now where
  # stream_realize names the attempt (its selected session is the run),
  # else the replay owed.  The replay, a job of the pool: what it was
  # handed.  Its verdict: confirmed, unless stream_refute names the attempt.
  campaign_confirm_plan() {
    mkdir -p "$3/worker" "$3/sessions"
    [[ " ${stream_realize:-} " != *" $(basename "$2") "* ]] \
      || campaign_confirm_verdict true "realized" "" false >"$2/confirm.json"
  }
  campaign_confirm_replay() {
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
    cut -f1 "$4" | xargs -r -n1 basename | paste -sd ' ' - \
      >>"${stream_dir}/gated.txt"
    test_gated "$1" $(cut -f1 "$4" | xargs -r -n1 basename)
  }
}
# test_gated <iteration> <session>...: the import gate's ledger holds each
# (ImportGateMain's record), as the gate leaves it.
test_gated() {
  local iteration=$1 session
  shift
  mkdir -p "${iteration}/import_gated"
  for session in "$@"; do
    printf '{}\n' >"${iteration}/import_gated/${session}.json"
  done
}

# The exploration loop's state, as campaign_explore declares it, for a case
# that calls one of its helpers alone.
stream_loop_state() {
  declare -gA stream_reruns=() stream_growing=() stream_withdrawn=() \
    stream_rests=() stream_queued_at=() stream_flying=() stream_chain=() \
    stream_confirming=() stream_entry_need=() stream_rerun_offpath=() \
    stream_rerun_composed=()
  stream_uncaptured=()
  stream_world_depth=2147483647
  stream_queue=()
  stream_pending=()
  stream_gate_owed=()
  stream_gate_running=()
  stream_grow_pid=""
  stream_grow_round=""
  stream_grow_growth=""
  stream_grow_returned=""
  stream_swaps=()
  stream_staged=()
  stream_reaped=()
  stream_witnesses=()
  stream_deferred=()
  stream_hold=0
  stream_dirty=0
  stream_round_dir=""
}

# STREAM-1: NO BARRIER.  A round is planned as soon as a session lands, while
# what else runs goes on, and what it proposes starts at once: NEXT, proposed
# once SHORT's session landed, starts while LONG -- proposed with SHORT in
# round 0 -- still runs, and that round is handed LONG as in flight.  An
# obligation whose worker did not finish is its own answer, and what it staged
# is withdrawn under it.  When nothing is queued or running, a last round over
# every answer proposes nothing: the fixed point.  An empty host list is this
# machine, with no ssh; SHORT, its first solve, runs alone there (it starts
# the host's solver, campaign_stream_has_seat), the others at once on the
# solver's seats (four here).
stream_fixture stream-1
(
  stream_stubs
  campaign_solver_seats() { printf '4\n'; }
  ssh() { printf '%s\n' "$*" >>"${stream_dir}/ssh-calls.txt"; return 99; }
  stream_round_plan() {
    case "$1" in
      0) stream_propose "$2" SHORT LONG BROKEN ;;
      1) stream_propose "$2" NEXT ;;
    esac
  }
  campaign_obligation_worker() {
    local id=$1 worker=$4
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
  stream_grow_pid=""
  stream_grow_round=""
  stream_grow_returned=""
  stream_gate_owed=()
  stream_gate_running=()
  campaign_adapter_kill_grace_s=0
  campaign_reap_remote_workers() { :; }
  campaign_stream_reap
  ! kill -0 "${reap_other}" 2>/dev/null || kill "${reap_other}"
  [[ ! -e "${reap_held}" && -s "${reap_kept}" && -z "${stream_round_pid}" ]] \
    || fail "STREAM-REAP-HOLDS: the ended lane's hold was not given back, or \
another's was: $(ls "${campaign_host_gate_root}/lift12/heads")"
)

# STREAM-IDLE: the exploration ends -- its fixed point, or a stop already
# stated -- only with nothing left to start, run, plan or take: an ask waiting
# in the hard lane is in flight, never lost to a fixed point, and so is a
# returned re-run whose swap a reader holds, a return owed its gate, and a
# GROW building or built and not taken.  Per row: a job running, an entry
# queued, an ask in the hard lane, a re-run awaiting its swap, a head step, a
# round planning, a round returned, a return owed its gate, GROW's build (b)
# or its take (t) owed, and whether that is the end.
while IFS='|' read -r si_job si_queue si_hard si_swap si_step si_round \
    si_returned si_gate si_grow si_want; do
  si_said=$(
    declare -A stream_jobs=()
    stream_queue=()
    stream_hard=()
    stream_swaps=()
    stream_gate_owed=()
    stream_grow_pid=""
    stream_grow_returned=""
    [[ "${si_gate}" == 0 ]] || stream_gate_owed=("REPLAY r D lift12 0"$'\t'"s"$'\t'"w")
    [[ "${si_grow}" != b ]] || stream_grow_pid=79
    [[ "${si_grow}" != t ]] || stream_grow_returned=1
    [[ "${si_job}" == 0 ]] || stream_jobs[4242]="HARD r A lift12 "
    [[ "${si_queue}" == 0 ]] || stream_queue=("OBLIGATION r B again")
    [[ "${si_hard}" == 0 ]] || stream_hard=("HARD r C")
    [[ "${si_swap}" == 0 ]] || stream_swaps=("obligations-0002 R S 0")
    stream_step_pid=${si_step}
    stream_round_pid=${si_round}
    stream_round_returned=${si_returned}
    if campaign_stream_idle; then echo end; else echo on; fi
  )
  [[ "${si_said}" == "${si_want}" ]] \
    || fail "STREAM-IDLE: job ${si_job}, queue ${si_queue}, hard ${si_hard}, \
swap ${si_swap}, step '${si_step}', round '${si_round}', returned \
'${si_returned}': ${si_said}, not ${si_want}"
done <<'EOF'
0|0|0|0||||0||end
0|0|1|0||||0||on
0|1|0|0||||0||on
1|0|0|0||||0||on
0|0|0|1||||0||on
0|0|0|0|77|||0||on
0|0|0|0||78||0||on
0|0|0|0|||obligations-0001|0||on
0|0|0|0||||1||on
0|0|0|0||||0|b|on
0|0|0|0||||0|t|on
EOF

# STREAM-OFFPATH: a GROW re-run is off EXPLORE's critical path exactly when
# its world -- its focus row's own flip and the flips it inherited, counted
# as explore.ExploreCodec#readWorld counts them -- holds more flips than the
# rounds' maxWorldDepth (campaign_stream_offpath): no path of its session is
# ever cut.  At the unbounded depth (Integer.MAX_VALUE) none is.  Per row:
# whether the row flips (- a pairing flip: none), the flips it inherited,
# the depth, whether it is off the path.
offpath_focus="${test_tmp}/offpath-focus.jsonl"
while IFS='|' read -r op_flip op_inherited op_depth op_want; do
  jq -n -c --arg flip "${op_flip}" --argjson inherited "${op_inherited}" \
    '{taskId: "TASK.seed",
      flip: (if $flip == "yes" then {siteId: "S#u1", ordinal: 0,
        outcome: true} else null end),
      inheritedFlips: [range($inherited) | {siteId: "S#u\(.)", ordinal: 0,
        outcome: false}]}' >"${offpath_focus}"
  op_said=$(
    stream_world_depth=${op_depth}
    if campaign_stream_offpath "${offpath_focus}"; then echo off; else
      echo on; fi
  )
  [[ "${op_said}" == "${op_want}" ]] \
    || fail "STREAM-OFFPATH: flip ${op_flip}, ${op_inherited} inherited, \
depth ${op_depth}: ${op_said}, not ${op_want}"
done <<'EOF'
yes|0|0|off
-|0|0|on
yes|0|1|on
yes|1|1|off
-|2|1|off
yes|2|3|on
yes|0|2147483647|on
yes|40|2147483647|on
EOF

# STREAM-IDLE-BESIDE: the exploration's idleness but for GROW's re-runs
# (campaign_stream_idle offpath|composed): under offpath, a re-run no
# obligation can come from (stream_rerun_offpath) -- running, queued,
# returned unswapped or owed its gate -- is no work; under composed, only
# such a re-run COMPOSE does not wait for (stream_rerun_composed) is none.
# Any other work is work under both.  Per row: where the re-run is, whether
# it is off the path, whether COMPOSE waits for it, the filter, and the
# answer.
while IFS='|' read -r ib_where ib_off ib_composed ib_filter ib_want; do
  ib_said=$(
    declare -A stream_jobs=() stream_rerun_offpath=() \
      stream_rerun_composed=()
    stream_queue=()
    stream_hard=()
    stream_swaps=()
    stream_gate_owed=()
    stream_step_pid=""
    stream_round_pid=""
    stream_round_returned=""
    stream_grow_pid=""
    stream_grow_returned=""
    case "${ib_where}" in
      job) stream_jobs[4242]="RERUN obligations-0001 OB.r lift12 S.x" ;;
      queue) stream_queue=("RERUN obligations-0001 OB.r S.x") ;;
      swap) stream_swaps=("obligations-0001 OB.r S.x 0") ;;
      gate) stream_gate_owed=("RERUN obligations-0001 OB.r lift12 0 S.x"$'\t'"s"$'\t'"w") ;;
      solve) stream_queue=("OBLIGATION obligations-0001 OB.r") ;;
    esac
    [[ "${ib_off}" == no ]] || stream_rerun_offpath["OB.r S.x"]=1
    [[ "${ib_composed}" == no ]] || stream_rerun_composed["OB.r S.x"]=1
    if campaign_stream_idle ${ib_filter/-/}; then echo end; else echo on; fi
  )
  [[ "${ib_said}" == "${ib_want}" ]] \
    || fail "STREAM-IDLE-BESIDE: a re-run (${ib_where}, off the path \
${ib_off}, composed ${ib_composed}) under '${ib_filter}': ${ib_said}, not \
${ib_want}"
done <<'EOF'
job|yes|no|-|on
job|yes|no|offpath|end
job|no|no|offpath|on
job|yes|no|composed|end
job|yes|yes|composed|on
job|yes|yes|offpath|end
queue|yes|no|offpath|end
queue|no|no|offpath|on
queue|yes|yes|composed|on
swap|yes|no|composed|end
swap|no|no|offpath|on
swap|yes|yes|composed|on
gate|yes|no|offpath|end
gate|yes|yes|composed|on
solve|no|no|offpath|on
EOF

# FIXED-BESIDE: nothing owed but re-runs no obligation can come from is the
# fixed point beside them (campaign_stream_fixed_beside): COMPOSE waits for
# the re-runs of sessions whose paths it composes -- a target row at the
# declared occurrence (campaign_stream_composes) -- running, queued or
# returned; a queued one of any other session is dropped now, its session
# uncaptured, and one running is left to the end.  S.a (running) and S.c
# (queued) compose; S.b (queued) and S.d (running) do not.
(
  beside="${test_tmp}/fixed-beside"
  iteration_dir="${beside}/iteration-0000"
  sessions="${iteration_dir}/sessions"
  campaign_root=${beside}
  stream_loop_state
  stream_world_depth=0
  stream_anchors='[{"node":"anchor"}]'
  stream_round=3
  stream_step_pid=""
  stream_round_pid=""
  stream_round_returned=""
  stream_hard=()
  stream_reruns_dropped=()
  declare -A stream_jobs=()
  stream_stop=""
  stream_stop_detail=""
  for fb_session in S.a S.b S.c S.d; do
    mkdir -p "${sessions}/${fb_session}" \
      "${iteration_dir}/obligations-0001/OB.${fb_session#S.}/grow-obligations-0002/OB.${fb_session#S.}"
    stream_reruns["OB.${fb_session#S.} ${fb_session}"]="${iteration_dir}/obligations-0001/OB.${fb_session#S.}/grow-obligations-0002/OB.${fb_session#S.}"
    stream_rerun_offpath["OB.${fb_session#S.} ${fb_session}"]=1
    jq -n -c --arg at "$([[ "${fb_session}" == S.[ac] ]] && echo anchor \
        || echo elsewhere)" '{occurrence: {node: $at}}' \
      | gzip -c >"${sessions}/${fb_session}/targets.jsonl.gz"
  done
  stream_hold=4
  stream_jobs[4242]="RERUN obligations-0002 OB.a lift12 S.a"
  stream_jobs[4243]="RERUN obligations-0002 OB.d lift12 S.d"
  stream_queue=("RERUN obligations-0002 OB.b S.b" \
    "RERUN obligations-0002 OB.c S.c")
  campaign_stream_fixed_beside 2>"${beside}/said"
  [[ "${stream_stop}" == FIXED_POINT \
      && "${!stream_rerun_composed[*]}" == *"OB.a S.a"* \
      && "${!stream_rerun_composed[*]}" == *"OB.c S.c"* \
      && ${#stream_rerun_composed[@]} -eq 2 \
      && "${stream_queue[*]}" == "RERUN obligations-0002 OB.c S.c" \
      && "${stream_reruns_dropped[*]}" == OB.b \
      && "${stream_uncaptured[*]}" == S.b \
      && -d "${beside}/explore-reaped/obligations-0002/OB.b" \
      && ${#stream_jobs[@]} -eq 2 && "${stream_hold}" == 3 ]] \
    || fail "FIXED-BESIDE: stop ${stream_stop}, composed \
[${!stream_rerun_composed[*]}], queue [${stream_queue[*]}], dropped \
[${stream_reruns_dropped[*]}], uncaptured [${stream_uncaptured[*]}], hold \
${stream_hold}"
  # Nothing owed but those COMPOSE does not wait for is the end; the two it
  # waits for hold it.
  ! campaign_stream_idle composed \
    || fail "FIXED-BESIDE: the end came with COMPOSE's re-runs owed"
  unset 'stream_jobs[4242]'
  stream_queue=()
  campaign_stream_idle composed \
    || fail "FIXED-BESIDE: a re-run COMPOSE does not wait for held the end"
) || fail "FIXED-BESIDE failed"

# STREAM-UNCAPTURED: at the exploration's end, the exposing sessions still
# in the corpus whose re-runs did not land are named in
# uncaptured_sessions.txt (campaign_stream_uncaptured, SessionDir#UNCAPTURED:
# COMPOSE frees what their reads saw that no write states), once each,
# sorted; a session swapped out since is none, and none are named after a
# witness (its claim is the accepted attempt's).  Per row: the stop, the
# sessions named uncaptured (in order), those in the corpus, the file.
while IFS='|' read -r un_stop un_named un_corpus un_want; do
  un_dir="${test_tmp}/stream-uncaptured"
  rm -rf -- "${un_dir}"
  mkdir -p "${un_dir}/sessions"
  for un_session in ${un_corpus}; do
    mkdir -p "${un_dir}/sessions/${un_session}"
  done
  (
    iteration_dir=${un_dir}
    sessions=${un_dir}/sessions
    stream_stop=${un_stop}
    read -r -a stream_uncaptured <<<"${un_named}"
    campaign_stream_uncaptured 2>/dev/null
  )
  un_got=$(paste -sd ' ' "${un_dir}/uncaptured_sessions.txt" 2>/dev/null \
    || echo -)
  [[ "${un_got:--}" == "${un_want}" ]] \
    || fail "STREAM-UNCAPTURED: ${un_stop} with [${un_named}] uncaptured \
over [${un_corpus}]: ${un_got}, not ${un_want}"
done <<'EOF'
FIXED_POINT|S.b S.a S.b|S.a S.b S.c|S.a S.b
FIXED_POINT|S.gone S.a|S.a|S.a
FIXED_POINT||S.a|-
CAMPAIGN_BUDGET_REACHED|S.c|S.c|S.c
WITNESSED|S.a|S.a|-
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

# REMOTE-AWAIT: what a job on another host left is collected only once it
# is an answer or an ask again (campaign_await_remote_result): a replay set
# aside for memory (replay_again) of any kind -- RERUN and CONFIRM have no
# other row -- or a solve's ask again (solve_again) is handed on (0), never
# waited out as unseen and dropped; a REPLAY's worker holding only its
# solve's SAT_MODEL_READY has no answer of the replay yet (1 past the
# visibility bound, here 1 s).  Per row: the kind, the files its worker shows
# (result:<verdict>, replay_again, solve_again), the status.
ra_dir=${test_tmp}/remote-await
while IFS='|' read -r ra_kind ra_files ra_want; do
  rm -rf -- "${ra_dir}"
  mkdir -p "${ra_dir}/worker"
  for ra_file in ${ra_files}; do
    case "${ra_file}" in
      result:*) printf '{"verdict":"%s","sessionId":""}\n' \
        "${ra_file#result:}" >"${ra_dir}/worker/obligation_result.jsonl" ;;
      *) echo "1024 512 ${ra_dir}/aside" >"${ra_dir}/worker/${ra_file}" ;;
    esac
  done
  ra_status=0
  (
    campaign_remote_visibility_wait_s=1
    campaign_log() { :; }
    campaign_await_remote_result "${ra_dir}/worker" lift12 OB.1 \
      "${ra_dir}/staged" "${ra_kind}"
  ) || ra_status=$?
  [[ "${ra_status}" == "${ra_want}" ]] \
    || fail "REMOTE-AWAIT: a ${ra_kind} showing [${ra_files}] ended \
${ra_status}, not ${ra_want}"
done <<'EOF'
RERUN|replay_again|0
CONFIRM|replay_again|0
REPLAY|result:SAT_MODEL_READY replay_again|0
REPLAY|result:SAT_MODEL_READY|1
REPLAY|result:NOT_ADMITTED|0
OBLIGATION|result:SAT_MODEL_READY|0
OBLIGATION|solve_again|0
RERUN||1
EOF

# STREAM-REAP: nothing a job started outlives the exploration's end
# (campaign_stream_reap): its tree is frozen as it is listed (each process
# stopped, listed again until no new one appears), so a process it starts
# while the reap lists it is ended with it, never left reparented to init.
# The job here starts a process every 10 ms.
(
  reap_dir=${test_tmp}/stream-reap
  mkdir -p "${reap_dir}"
  campaign_adapter_kill_grace_s=1
  campaign_reap_remote_workers() { :; }
  campaign_stream_release() { :; }
  declare -A stream_jobs=()
  stream_step_pid="" stream_round_pid="" stream_grow_pid="" stream_ticker=""
  ( set +e
    while :; do
      command sleep 600 &
      echo "$!" >>"${reap_dir}/started"
      command sleep 0.01
    done ) &
  stream_jobs[$!]="RERUN obligations-0001 OB.r lift12 S.r"
  command sleep 0.3
  campaign_stream_reap
  reap_left=""
  while read -r reap_pid; do
    ! kill -0 "${reap_pid}" 2>/dev/null || reap_left+=" ${reap_pid}"
  done <"${reap_dir}/started"
  [[ -z "${reap_left}" ]] \
    || { kill ${reap_left} 2>/dev/null
         fail "STREAM-REAP: what the job started outlived the end:${reap_left}"; }
) || fail "STREAM-REAP failed"

# KILL-REQUEUE: a replay of the pool its watcher ended for memory returns
# with its run set aside (replay_again: what it reached, what it was
# charged, where it went; campaign_replay_set_aside) and is no answer:
# nothing lands, its peak raises the measured need, and its entry is queued
# again unchanged -- a REPLAY on the tree its solve started on, a RERUN, a
# CONFIRM -- at its full need (stream_entry_need: 1.5 times the largest
# peak, rounded up to 128 MB, at most half a host's ceiling, 8192 here),
# charged whole (campaign_stream_try_host).  One whose full need is no more
# than it reached would end again: answered REPLAY_BOUNDED, it lands as any
# answer, as it is collected.  A replay out of heap (its runs out of heap so
# far, the last one's heap) is queued again once, its own need unset, and
# every replay from then on starts at twice that heap (the heap basis, twice
# the heap); out of heap twice, REPLAY_BOUNDED.  {kind, the MB it reached,
# the heap it ran out of (- for a memory end; n*heap: its n runs out of
# heap), queued at <MB>, rerun at <basis> or bounded: twice, or once at the
# most a replay's heap is, half a host's ceiling (8192 here)}.
while IFS='|' read -r rq_kind rq_mb rq_heap rq_want; do
  rq_dir="${test_tmp}/kill-requeue"
  rm -rf -- "${rq_dir}"
  rq_worker="${rq_dir}/it/obligations-0000/A"
  [[ "${rq_kind}" != CONFIRM ]] || rq_worker="${rq_dir}/witness-confirm/0001/worker"
  mkdir -p "${rq_worker}/ended-1" "${rq_dir}/it/sessions"
  rq_runs=0
  [[ "${rq_heap}" == - ]] || rq_runs=${rq_heap%%\**}
  for (( rq_n = 1; rq_n <= rq_runs; rq_n++ )); do
    mkdir -p "${rq_worker}/ended-${rq_n}"
    echo "${rq_heap#*\*}" >"${rq_worker}/ended-${rq_n}/workload_out_of_heap_mb"
  done
  printf '%s 1024 %s %s\n' "${rq_mb}" "${rq_worker}/ended-$(( \
    rq_runs > 1 ? rq_runs : 1 ))" "${rq_heap#*\*}" >"${rq_worker}/replay_again"
  rq_logs=$(campaign_stream_logs "${rq_kind}" "${rq_worker}")
  echo out >"${rq_logs}stdout.log"
  echo lift12 >"${rq_logs}host.txt"
  rq_said=$(
    iteration_dir="${rq_dir}/it"
    sessions="${iteration_dir}/sessions"
    results="${rq_dir}/results.jsonl"
    campaign_root=${rq_dir}
    campaign_log() { :; }
    campaign_replay_charge_mb() { echo "$(( $1 < 8192 ? $1 : 8192 ))"; }
    campaign_replay_peak_mb=1000
    rq_id=A
    [[ "${rq_kind}" != CONFIRM ]] || rq_id=0001
    rq_round=obligations-0000
    [[ "${rq_kind}" != CONFIRM ]] || rq_round=-
    stream_queue=("OBLIGATION obligations-0000 B")
    stream_pending=()
    stream_ticker=""
    stream_grow_pid=""
    stream_grow_round=""
    stream_grow_returned=""
    stream_gate_owed=()
    stream_gate_running=()
    stream_step_pid=""
    stream_round_pid=""
    rq_session=""
    [[ "${rq_kind}" != RERUN ]] || rq_session=EXPOSING
    declare -A stream_jobs=([4242]="${rq_kind} ${rq_round} ${rq_id} lift12 \
${rq_session}") stream_job_worker=([4242]=${rq_worker}) \
      stream_job_tree=([4242]="g0/classes g0/plan.jsonl") \
      stream_job_charge=() stream_job_since=() stream_job_cores=() \
      stream_host_busy=([lift12]=1) stream_host_solves=() \
      stream_entry_need=() stream_queued_at=() stream_solver_seen=() \
      stream_withdrawn=() stream_rests=()
    campaign_stream_ended 4242 0
    for rq_entry in "${stream_queue[@]}"; do
      printf 'queued %s %s\n' "${rq_entry}" \
        "${stream_entry_need[${rq_entry}]:-}"
    done
    printf 'pending %s\n' "${stream_pending[@]}"
    printf 'landed %s\n' "$(jq -r -s 'map(.obligationId) | join(" ")' \
      "${results}" 2>/dev/null)"
    printf 'need %s\n' "$(campaign_replay_need_mb)"
    printf 'basis %s\n' "$(campaign_replay_basis_mb)"
  )
  case "${rq_want}" in
    rerun\ *)
      rq_entry="REPLAY obligations-0000 A g0/classes g0/plan.jsonl"
      [[ "${rq_kind}" != CONFIRM ]] || rq_entry="CONFIRM - 0001"
      [[ "${rq_said}" == *"queued ${rq_entry} "$'\n'* \
         && "${rq_said}" == *"basis ${rq_want#rerun }"* \
         && ! -e "${rq_worker}/obligation_result.jsonl" ]] \
        || fail "KILL-REQUEUE: a ${rq_kind} out of its ${rq_heap} MB heap was \
not run again at twice it: ${rq_said}" ;;
    twice)
      [[ "${rq_said}" == *"landed A"* \
         && "${rq_said}" != *"queued ${rq_kind}"* \
         && "$(jq -r '.detail' "${rq_worker}/obligation_result.jsonl")" \
           == REPLAY_BOUNDED:* ]] \
        || fail "KILL-REQUEUE: a ${rq_kind} out of heap twice was not \
answered REPLAY_BOUNDED: ${rq_said}" ;;
    queued\ *)
      rq_entry="REPLAY obligations-0000 A g0/classes g0/plan.jsonl"
      [[ "${rq_kind}" != RERUN ]] \
        || rq_entry="RERUN obligations-0000 A EXPOSING"
      [[ "${rq_kind}" != CONFIRM ]] || rq_entry="CONFIRM - 0001"
      [[ "${rq_said}" == *"queued ${rq_entry} ${rq_want#queued }"* \
         && "${rq_said}" == *"pending "$'\n'* \
         && "${rq_said}" == *"queued OBLIGATION obligations-0000 B "* \
         && ! -e "${rq_worker}/replay_again" \
         && -s "${rq_worker}/ended-1/${rq_logs#"${rq_worker}"/}stdout.log" \
         && ! -e "${rq_worker}/obligation_result.jsonl" ]] \
        || fail "KILL-REQUEUE: a ${rq_kind} ended at ${rq_mb} MB was not \
queued again at its full need ${rq_want#queued }: ${rq_said}" ;;
    bounded)
      [[ "${rq_said}" == *"landed A"* \
         && "${rq_said}" != *"queued ${rq_kind}"* \
         && "$(jq -r '.verdict + " " + .detail' \
           "${rq_worker}/obligation_result.jsonl")" == "NOT_ADMITTED \
REPLAY_BOUNDED: replay was ended at ${rq_mb} MB as its host could not take \
its growth, and its full need, 8192 MB, is the most a replay is charged" ]] \
        || fail "KILL-REQUEUE: a ${rq_kind} ended at ${rq_mb} MB past every \
charge was not answered REPLAY_BOUNDED: ${rq_said} \
$(cat "${rq_worker}/obligation_result.jsonl" 2>&1)" ;;
  esac
done <<'EOF'
REPLAY|2900|-|queued 4352
RERUN|2900|-|queued 4352
CONFIRM|2900|-|queued 4352
REPLAY|5000|-|queued 7552
REPLAY|5400|-|queued 8192
REPLAY|9000|-|bounded
REPLAY|0|1*4096|rerun 16384
CONFIRM|0|1*4096|rerun 16384
REPLAY|0|2*4096|twice
REPLAY|0|1*8192|twice
EOF

# CONFIRM-IN-PLACE: the final CONFIRM runs its replay in place: a replay
# ended for memory runs once more at its full need, one out of heap once more
# at twice its heap; a second end is REPLAY_BOUNDED by name, never a
# confirmation decided over no replay.  {how the runs end, the runs, the
# confirmation's worker result}.
while IFS='|' read -r cp_ends cp_runs cp_result; do
  cp_dir="${test_tmp}/confirm-in-place"
  rm -rf -- "${cp_dir}"
  mkdir -p "${cp_dir}/claims" "${cp_dir}/c/worker" "${cp_dir}/c/sessions"
  cp_got=$(
    campaign_log() { :; }
    campaign_confirm_plan() { :; }
    campaign_confirm_settle() { :; }
    campaign_replay_charge_mb() { echo "$(( $1 < 8192 ? $1 : 8192 ))"; }
    campaign_replay_peak_mb=1000
    cp_n=0
    campaign_head_charged() {
      cp_n=$((cp_n + 1))
      echo "$1 $7" >>"${cp_dir}/charged"
      read -r -a cp_end <<<"${cp_ends}"
      case "${cp_end[cp_n - 1]:-ok}" in
        heap) mkdir -p "${cp_dir}/c/worker/ended-${cp_n}"
          echo 4096 >"${cp_dir}/c/worker/ended-${cp_n}/workload_out_of_heap_mb"
          printf '0 %s %s 4096\n' "$1" "${cp_dir}/c/worker/ended-${cp_n}" \
            >"${cp_dir}/c/worker/replay_again" ;;
        memory) printf '2900 %s %s -\n' "$1" \
            "${cp_dir}/c/worker/ended-${cp_n}" >"${cp_dir}/c/worker/replay_again" ;;
        ok) jq -n -c '{verdict: "ADMITTED", sessionId: "S"}' \
            >"${cp_dir}/c/worker/obligation_result.jsonl" ;;
      esac
    }
    campaign_confirm_decide() {
      jq -r '.verdict + " " + (.detail // "")' \
        "${cp_dir}/c/worker/obligation_result.jsonl"
    }
    campaign_confirm_claim "${cp_dir}" "${cp_dir}/claims" "${cp_dir}/c"
    echo "runs $(wc -l <"${cp_dir}/charged")"
  )
  [[ "${cp_got}" == *"runs ${cp_runs}"* \
     && "${cp_got}" == *"${cp_result}"* ]] \
    || fail "CONFIRM-IN-PLACE: ends ${cp_ends} gave ${cp_got}, not ${cp_runs} \
run(s) and ${cp_result}: $(cat "${cp_dir}/charged")"
done <<'EOF'
ok|1|ADMITTED
heap ok|2|ADMITTED
memory ok|2|ADMITTED
heap heap|2|NOT_ADMITTED REPLAY_BOUNDED: the confirmation replay ran out of its 4096 MB heap
memory memory|2|NOT_ADMITTED REPLAY_BOUNDED: the confirmation replay was ended at 2900 MB
EOF

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
    [[ "${grow_verdict}" == confirmed ]] || stream_refute=0000
    # The re-run returns before the verdict: the confirmation's replay
    # answers only once the re-run's session is written and a poll later.
    campaign_confirm_replay() {
      local waited
      for (( waited = 0; waited < 600; waited++ )); do
        [[ -z "$(find "${campaign_root}" \
          -path '*/SESSION.regrown/manifest.json')" ]] || break
        sleep 0.1
      done
      sleep 2
      date +%s.%N >"$1/replay-ended-at"
      jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT",
        obligationId: "CONFIRM", verdict: "ADMITTED", sessionId: "",
        detail: "stub"}' >"$1/worker/obligation_result.jsonl"
    }
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
      printf '%s\n' "$3" >"$(dirname "$2")/weave_key"
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

# GROW-BESIDE: a GROW re-run no obligation can come from (its world past the
# owner's cap, campaign_stream_offpath) holds no fixed point: once nothing
# else is owed the exploration is at its fixed point beside it, and COMPOSE
# waits for it only where it composes the exposing session's path (a target
# row at the declared occurrence): composed, the re-run swaps in before the
# end; free, it is reaped at the end and its session named uncaptured
# (uncaptured_sessions.txt: COMPOSE frees what its reads saw that no write
# states).  Uncapped (Integer.MAX_VALUE) no re-run is off the path: it holds
# the fixed point and swaps in, as before.  OB.x flips once and exposes a
# region; its re-run runs <sleep> seconds (the free one past any end, so it
# can only be reaped).  Per row: the case, the depth (- unbounded), where the
# exposing session's target stands, the re-run's sleep, the session the
# corpus ends with, the sessions named uncaptured, the obligations reaped.
while IFS='|' read -r gb_case gb_depth gb_target gb_sleep gb_session \
    gb_free_want gb_reaped_want; do
  gb_named="${gb_free_want}|${gb_reaped_want}"
  stream_fixture "grow-beside-${gb_case}"
  mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
  printf '2\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
  {
    printf '#!/usr/bin/env bash\nset -euo pipefail\nsleep %s\n' "${gb_sleep}"
    cat <<'EOF'
mkdir -p "${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.regrown"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.regrown", role: "FOCUSED", obligationIds: ["OB.x"]}' \
  >"${CAUSYNTH_CONCOLIC_SESSIONS}/SESSION.regrown/manifest.json"
jq -n -c '{schemaVersion: 1, kind: "OBLIGATION_RESULT", obligationId: "OB.x",
  verdict: "NOT_ADMITTED", sessionId: "SESSION.regrown",
  detail: "the grown region refused the flip"}' \
  >"${CAUSYNTH_CONCOLIC_WORKER_DIR}/replay_verdict.jsonl"
EOF
  } >"${stream_dir}/replay.sh"
  chmod +x "${stream_dir}/replay.sh"
  (
    stream_stubs
    [[ "${gb_depth}" == - ]] || stream_test_world_depth=${gb_depth}
    concolic_replay_command="${stream_dir}/replay.sh"
    replay_timeout_s=900
    schedule_max_jobs=1
    trace_test=T
    custom_jdk_home=""
    workload_work_dir="${stream_dir}"
    stream_round_plan() {
      case "$1" in
        0) stream_propose "$2" OB.x ;;
        1) printf '%s\n' \
'{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.exposing","obligationId":"OB.x"}' \
             >>"$2/growth.jsonl" ;;
      esac
    }
    do_compose() { fail "GROW-BESIDE ${gb_case}: a witness was attempted"; }
    run_java_main() {
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
      printf '%s\n' "$3" >"$(dirname "$2")/weave_key"
    }
    campaign_obligation_worker() {
      local worker=$4
      printf '%s\n' '{"taskId":"TASK.seed","flip":{"siteId":"S#u1","ordinal":0,"outcome":true},"inheritedFlips":[]}' \
        >"${worker}/focused_task.jsonl"
      stream_answer "${worker}" OB.x ADMITTED SESSION.exposing
      jq -n -c --arg at "${gb_target}" \
        '{occurrence: {node: $at}, observedFatal: false}' | gzip -c \
        >"${worker}/sessions/SESSION.exposing/targets.jsonl.gz"
    }
    campaign_explore "${stream_dir}" iteration-0000
  ) >"${stream_dir}/explore.log" 2>&1 \
    || fail "GROW-BESIDE ${gb_case} did not finish: \
$(cat "${stream_dir}/explore.log")"
  gb_ended=$(jq -r '.stop' "${stream_dir}/exploration.json")
  gb_landed=$(ls "${stream_dir}/sessions" | paste -sd ' ' -)
  gb_free=$(cat "${stream_dir}/uncaptured_sessions.txt" 2>/dev/null \
    || echo -)
  [[ "${gb_ended}|${gb_landed}" == "FIXED_POINT|${gb_session}" ]] \
    || fail "GROW-BESIDE ${gb_case}: ended ${gb_ended} with [${gb_landed}], \
not FIXED_POINT with ${gb_session}: $(cat "${stream_dir}/explore.log")"
  # Free: the re-run, which never returns by itself, is reaped at the end
  # beside it, and its session is named; otherwise it lands before the end.
  gb_reaped=$(jq -r '.reaped | join(" ")' "${stream_dir}/exploration.json")
  [[ "${gb_free}|${gb_reaped}" == "${gb_named}" ]] \
    || fail "GROW-BESIDE ${gb_case}: uncaptured ${gb_free}, reaped \
[${gb_reaped}], not ${gb_named}: $(cat "${stream_dir}/exploration.json")"
done <<'EOF_BESIDE'
composed|0|anchor|2|SESSION.regrown|-|
free|0|elsewhere|600|SESSION.exposing|SESSION.exposing|OB.x
uncapped|-|anchor|2|SESSION.regrown|-|
EOF_BESIDE

# STREAM-SWAP-DUE: a returned re-run swaps in once no reader of the session
# it withdraws runs: a witness's confirmation owed whose attempt composed it
# (an attempt stating no corpus holds every swap); a witness owed an attempt,
# gated and not attempted (a confirmation owed holds the attempt) or
# deferred until a confirmation's verdict (Z2M's class); or the round
# planning while its corpus names it and its planner has not read it.  A
# solve running holds none (a solver reads the corpus without what GROW
# withdrew, ObligationSolverMain#standing).  Per row: the attempts under
# confirmation (<attempt>:<its corpus, +-joined>, <attempt>:! where it states
# none; - none), the witnesses waiting for an attempt and the deferred ones
# (+-joined; - none), the planning round's corpus (+-joined; - no round),
# whether its planner read it, the jobs running, and whether the swap of
# session A is due.
swap_due_n=0
while IFS='|' read -r sd_confirming sd_witnesses sd_deferred sd_round \
    sd_read sd_jobs sd_want; do
  swap_due_n=$((swap_due_n + 1))
  sd_said=$(
    iteration_dir="${test_tmp}/swap-due-${swap_due_n}"
    mkdir -p "${iteration_dir}"
    stream_loop_state
    declare -A stream_jobs=()
    for sd_attempt in ${sd_confirming//,/ }; do
      [[ "${sd_attempt}" != - ]] || continue
      stream_confirming[${sd_attempt%%:*}]=model
      mkdir -p "${iteration_dir}/witness-attempts/${sd_attempt%%:*}"
      [[ "${sd_attempt#*:}" == '!' ]] || tr '+' '\n' <<<"${sd_attempt#*:}" \
        >"${iteration_dir}/witness-attempts/${sd_attempt%%:*}/corpus.txt"
    done
    [[ "${sd_witnesses}" == - ]] || read -r -a stream_witnesses \
      <<<"${sd_witnesses//+/ }"
    [[ "${sd_deferred}" == - ]] || read -r -a stream_deferred \
      <<<"${sd_deferred//+/ }"
    if [[ "${sd_round}" != - ]]; then
      stream_round_dir="${iteration_dir}/planning-0003"
      mkdir -p "${stream_round_dir}"
      tr '+' '\n' <<<"${sd_round}" >"${stream_round_dir}/corpus.txt"
      [[ "${sd_read}" != yes ]] || : >"${stream_round_dir}/corpus_read"
    fi
    for sd_kind in ${sd_jobs//,/ }; do
      [[ "${sd_kind}" == - ]] || stream_jobs[$((100 + ${#stream_jobs[@]}))]="\
${sd_kind} obligations-0002 X lift12 "
    done
    if campaign_stream_swap_due A; then echo due; else echo held; fi
  )
  [[ "${sd_said}" == "${sd_want}" ]] \
    || fail "STREAM-SWAP-DUE: confirming ${sd_confirming}, witnesses \
${sd_witnesses}, deferred ${sd_deferred}, round ${sd_round} (read ${sd_read}), \
running ${sd_jobs}: ${sd_said}, not ${sd_want}"
done <<'EOF'
-|-|-|-|-|-|due
-|-|-|-|-|OBLIGATION,HARD,REPLAY,RERUN|due
0000:A+B|-|-|-|-|-|held
0000:B|-|-|-|-|-|due
0000:B,0001:C+A|-|-|-|-|-|held
0000:!|-|-|-|-|-|held
0000:B|A|-|-|-|-|held
0000:B|C+A|-|-|-|-|held
-|-|A|-|-|-|held
0000:B|B+C|D|-|-|OBLIGATION|due
-|-|-|A+B|no|-|held
-|-|-|A+B|yes|OBLIGATION|due
-|-|-|B+C|no|OBLIGATION|due
0000:B|-|-|A|yes|OBLIGATION|due
EOF

# GROW-INFLIGHT: a round planned while GROW's re-runs run, or taken after one
# swapped in, saw the sessions they stand in for, and the occurrences they
# capture uncaptured still: a growth row is not grown again when its
# exposing (obligation, session) has a re-run owed or its session was
# withdrawn by one, or when its subject was grown with the re-run of a
# session the round's corpus names (planned before that re-run's session
# landed); every other row grows, rows of other kinds kept, and a round
# whose growth is all in flight grows nothing and queues its proposals as
# any round.  Per case: the round's corpus, and the rows GROW was handed.
while IFS='|' read -r inflight_case inflight_corpus inflight_grown; do
  (
    inflight_dir="${test_tmp}/grow-inflight-${inflight_case}"
    round_dir="${inflight_dir}/obligations-0004"
    iteration_dir=${inflight_dir}
    mkdir -p "${round_dir}"
    stream_loop_state
    # OB.a's re-run is owed; OB.s's swapped in (S.s withdrawn, R.s landed);
    # OB.w's exposing session S.w was withdrawn by its swap.
    stream_reruns["OB.a S.a"]="${inflight_dir}/rerun"
    stream_growing["X.owed"]="OB.a S.a"
    stream_growing["T.u S.u#2"]="OB.a S.a"
    stream_growing["X.swapped"]="OB.s S.s"
    stream_withdrawn[S.s]=1
    stream_withdrawn[S.w]=1
    region_path_max_waves=99
    campaign_log() { :; }
    campaign_stream_grow() {
      jq -r '.kind + " " + (.occurrence // .taskId // "")' "$2" \
        | paste -sd ',' >"${inflight_dir}/grown.txt"
    }
    tr '+' '\n' <<<"${inflight_corpus}" >"${round_dir}/corpus.txt"
    {
      printf '%s\n' \
        '{"kind":"EXPOSED_REGION","occurrence":"X.other","sessionId":"S.a","obligationId":"OB.a"}' \
        '{"kind":"EXPOSED_REGION","occurrence":"X.owed","sessionId":"S.b","obligationId":"OB.b"}' \
        '{"kind":"UNPLANNED_INPUT","taskId":"T.u","symbol":"S.u","k":2,"sessionId":"S.c","obligationId":"OB.c"}' \
        '{"kind":"ZK_EDGE","occurrence":"Z.w","sessionId":"S.w","obligationId":"OB.w"}' \
        '{"kind":"EXPOSED_REGION","occurrence":"X.swapped","sessionId":"S.e","obligationId":"OB.e"}' \
        '{"kind":"FRONTIER","open":0}'
      [[ "${inflight_case}" == all ]] || printf '%s\n' \
        '{"kind":"EXPOSED_REGION","occurrence":"X.new","sessionId":"S.d","obligationId":"OB.d"}' \
        '{"kind":"DOORS_ONLY_UNPAUSED","occurrence":"D.1","sessionId":"","obligationId":""}'
    } >"${round_dir}/growth.jsonl"
    printf '{"obligationId":"P1"}\n' >"${round_dir}/obligations.jsonl"
    : >"${round_dir}/in_flight.jsonl"
    jq -n '{wave: 0, branchesStopped: 0, anchorOccurrences: [],
      maxWorldDepth: 2147483647}' >"${round_dir}/explore_manifest.json"
    campaign_stream_take_round "${round_dir}"
    [[ "$(cat "${inflight_dir}/grown.txt" 2>/dev/null || echo -)" \
        == "${inflight_grown}" ]] \
      || fail "GROW-INFLIGHT ${inflight_case}: GROW was handed \
$(cat "${inflight_dir}/grown.txt" 2>/dev/null || echo nothing)"
    [[ "${stream_queue[*]}" == "OBLIGATION obligations-0004 P1" ]] \
      || fail "GROW-INFLIGHT ${inflight_case}: the round's proposals were \
not queued: ${stream_queue[*]}"
  ) || fail "GROW-INFLIGHT ${inflight_case} failed"
done <<'EOF'
before|S.a+S.b+S.s|FRONTIER ,EXPOSED_REGION X.new,DOORS_ONLY_UNPAUSED D.1
after|S.a+S.b+R.s|EXPOSED_REGION X.swapped,FRONTIER ,EXPOSED_REGION X.new,DOORS_ONLY_UNPAUSED D.1
all|S.a+S.s|-
EOF
reset_config

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
# A start that leaves room beside it (a replay's ends) fits only with that
# room free, and is charged its need alone.
run_capturing_status campaign_host_try_start lift14 2000 3000
[[ "${status}" -eq 1 && "${campaign_host_wait_reason}" \
    == *"2000 MB and 3000 MB room beside it"* ]] \
  || fail "a start of 2000 MB leaving 3000 MB was admitted beside 18000 MB \
under a 22221 MB ceiling, or not said so: ${campaign_host_wait_reason}"
campaign_host_try_start lift14 2000 2000 \
  || fail "a start of 2000 MB leaving 2000 MB was refused: \
${campaign_host_wait_reason}"
[[ "$(campaign_host_room lift14)" -eq 2221 ]] \
  || fail "the room left beside a start was charged: \
$(campaign_host_room lift14)"
campaign_host_release lift14 "${campaign_host_charge_id}"
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

# ENGINE-HEAP: an engine JVM starts at what its main measurably needs, charged
# that, and only a run that outgrows it -- the JVM's exit 3 under
# -XX:+ExitOnOutOfMemoryError -- runs again at twice its heap, up to the
# engine heap, saying so each time; the reader of its standard output sees
# the finished run's alone, and later starts of that main begin at the heap
# it last grew to.  A main with no measured need runs at the engine heap.
# Every run, at the engine heap too, ends at its first out-of-heap error, and
# so does one that only collects (the GC overhead limit at 70 %/5 %).
engine_test=${test_tmp}/engine-heap
mkdir -p "${engine_test}"
cat >"${engine_test}/java" <<'EOF'
#!/usr/bin/env bash
oom=n
# Out of heap at its first error, and at a collector that only collects.
[[ " $* " == *" -XX:+ExitOnOutOfMemoryError -XX:GCTimeLimit=70 -XX:GCHeapFreeLimit=5 "* ]] && oom=y
for arg; do [[ "${arg}" != -Xss* ]] || echo "${arg}" >>"${ENGINE_TEST_LOG}.stack"; done
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

# HEAD-NEVER: a head step no host of the pool can ever hold -- its charge past
# every host's ceiling less what the host uses beside the ledger's charges
# (campaign_head_most_mb) -- never waits (SGF8-adhoc-40: 23 and 107 min): an
# engine JVM whose heap is only a bound (its main has no measured need) runs
# at the most a host can hold; one whose measured need no host can hold, and
# any other step, fails at once, named.  Per row: the engine heap, the
# main's need (- none), the most the pool's best host holds, and the heap it
# ran at, or "fails".
never_dir=${test_tmp}/head-never
mkdir -p "${never_dir}"
printf '#!/usr/bin/env bash\necho "heap=${GRAPH_CHECKER_ENGINE_MEMORY_MB}"\n' \
  >"${never_dir}/java"
chmod +x "${never_dir}/java"
while IFS='|' read -r nv_engine nv_need nv_most nv_want; do
  nv_got=$(
    engine_memory_mb=${nv_engine}
    campaign_head_charging=1
    campaign_head_most_mb() { echo "${nv_most}"; }
    campaign_engine_need_mb() { [[ "${nv_need}" == - ]] || echo "${nv_need}"; }
    campaign_head_charged() { shift; "$@"; }
    campaign_engine_jvm() { shift; "$@"; }
    java_bin=${never_dir}/java
    engine_java -cp jar x.Main 2>/dev/null | sed -n 's/^heap=//p' || true
  )
  [[ "${nv_got:-fails}" == "${nv_want}" ]] \
    || fail "HEAD-NEVER: engine heap ${nv_engine}, need ${nv_need}, a host \
holding ${nv_most} MB at most: ${nv_got:-fails}, not ${nv_want}"
done <<'EOF'
24576|-|30000|24576
24576|-|26000|23552
24576|4096|26000|4096
24576|24000|20000|fails
EOF
(
  campaign_host_gate_root=${never_dir}/hosts
  campaign_worker_hosts="lift12"
  campaign_head_most_mb() { echo 20000; }
  campaign_host_try_charge() { status=1; }
  campaign_host_room() { echo 100; }
  sleep() { echo waited >"${never_dir}/waited"; exit 0; }
  campaign_head_place 26496 2>/dev/null
  echo placed >"${never_dir}/waited"
) || true
[[ ! -e "${never_dir}/waited" ]] \
  || fail "HEAD-NEVER: a step no host can ever hold was $(cat \
"${never_dir}/waited")"

# TREE-DIGEST: FREEZE's tree digest (campaign_tree_digest, its files hashed
# side by side) is the digest of the tree's sorted listing.
digest_root="${test_tmp}/tree-digest"
for digest_n in $(seq 1 600); do
  mkdir -p "${digest_root}/tree/d$(( digest_n % 7 ))"
  printf '%s\n' "${digest_n}" \
    >"${digest_root}/tree/d$(( digest_n % 7 ))/f${digest_n}.class"
done
[[ "$(campaign_tree_digest "${digest_root}/tree")" \
    == "$( (cd "${digest_root}/tree" && find . -type f -print0 \
      | LC_ALL=C sort -z | xargs -0 -r sha256sum) | sha256sum \
      | awk '{print $1}')" ]] \
  || fail "the tree digest is not the sorted listing's"

echo "run_engine campaign helper tests passed"
