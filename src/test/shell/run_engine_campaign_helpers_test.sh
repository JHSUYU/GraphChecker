#!/usr/bin/env bash

set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
# shellcheck source=../../../run_engine.sh
source "${repo}/run_engine.sh"

test_tmp=$(mktemp -d)
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

live_charges() {
  find "$1" -path '*/charges/*' -type f -printf '%f\n' 2>/dev/null
}

graphchecker_jar=${default_graphchecker_jar}
[[ -s "${graphchecker_jar}" ]] \
  || fail "these tests need the packaged jar: run mvn -o package -DskipTests"
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
  campaign_final="${campaign_root}/final"
  campaign_stage_metrics="${emit_root}/stage_metrics.tsv"
  composition_manifest="${campaign_final}/candidate_composition_manifest.json"
  campaign_max_claims=8
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
  causynth_output_dir="${emit_root}/causynth"
  mkdir -p "${causynth_output_dir}"
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
  jq -n '{schemaVersion: 1, kind: "CONFIRMATION", confirmed: true,
    refutes: false,
    reason: "every edge the model chose was taken, and the anchor observed the fatal",
    sessionId: "CONFIRM-1"}' >"${campaign_final}/confirm.json"
  for session_kind in activations decisions exports attaches writes reads \
      roots targets gaps; do
    : >"${emit_iteration}/sessions/SESSION.seed/${session_kind}.jsonl.gz"
  done
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
[[ "$(jq -r '.artifacts[] | select(.name == "gaps.json") | .sha256' \
      "${campaign_final}/run-manifest.json")" \
    == "$(campaign_digest "${campaign_final}/gaps.json")" ]] \
  || fail "the run manifest names gaps.json by a digest not its own"

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
[[ -s "${campaign_root}/final/result.json" ]] \
  || fail "a withheld run published no ${campaign_root}/final"
[[ -s "${campaign_root}/final/gaps.json" ]] \
  || fail "the published final lost the gaps that withheld it"

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

gate_dir="${test_tmp}/import-gate"
mkdir -p "${gate_dir}/sessions/s1"
printf '%s\n' "${gate_dir}/sessions/s1" >"${gate_dir}/gate.list"
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


reset_config
bound_dir="${test_tmp}/replay-bound"
mkdir -p "${bound_dir}/causynth/runtime"
echo 1000 >"${bound_dir}/causynth/runtime/window_ms"

mkdir -p "${bound_dir}/work"
workload_work_dir="${bound_dir}/work"
custom_jdk_home=""
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
campaign_adapter_timeout_s=""
run_capturing_status campaign_run_adapter "replay(test)" "exit 3" \
  >"${bound_dir}/adapter-unbounded.log" 2>&1
[[ "${status}" -eq 3 ]] \
  || fail "an unbounded adapter no longer reports the workload's own exit \
code (${status})"

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
    campaign_head_charged() { printf 'charged=%s ' "$1"; shift 2; "$@"; }
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
plan_dir="${test_tmp}/planner-start"
while IFS='|' read -r plan_heap plan_asked plan_status plan_done; do
  rm -rf -- "${plan_dir}"
  mkdir -p "${plan_dir}/planning-0003" "${plan_dir}/planner"
  plan_got=$(
    iteration_dir=${plan_dir}
    engine_memory_mb=16384
    plan_alive=0
    if [[ "${plan_heap}" != - ]]; then
      plan_alive=1
      echo "${plan_heap}" >"${plan_dir}/planner/heap"
      echo 1 >"${plan_dir}/planner/id"
    fi
    campaign_planner_alive() { (( plan_alive )); }
    campaign_planner_start() { plan_alive=1; echo "start $1 $2" >>"${plan_dir}/done"; }
    campaign_planner_round() { echo ask >>"${plan_dir}/done"; return "${plan_asked}"; }
    status=0
    campaign_stream_plan "${plan_dir}/planning-0003" 2>/dev/null || status=$?
    printf '%s|%s' "${status}" "$(paste -sd ' ' "${plan_dir}/done" \
      2>/dev/null)"
  )
  [[ "${plan_got}" == "${plan_status}|${plan_done}" ]] \
    || fail "PLANNER-START: a planner of ${plan_heap} asked ${plan_asked} \
gave ${plan_got}, not ${plan_status}|${plan_done}"
done <<'EOF'
16384|0|0|ask
-|0|0|start 16384 17792 ask
16384|3|3|ask
EOF
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

watch_dir="${test_tmp}/watch"
while IFS='|' read -r watch_available watch_foreign watch_charged watch_rss \
    watch_ended watch_rows watch_said watch_ending; do
  rm -rf -- "${watch_dir}"
  mkdir -p "${watch_dir}/trace" "${watch_dir}/hosts/gate-head/charges"
  [[ "${watch_ending}" != ending ]] || : >"${watch_dir}/trace/workload_ending"
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
3000|0|2500|2541|ran|1|causynth: the workload JVM's resident memory peaked at 2541 MB; its host was charged 2500 MB for it and took 2541 MB as it grew|ending
1400|0|2500|2541|ended|0|causynth: the workload JVM's resident memory peaked at 2541 MB; its host was charged 2500 MB for it|ending
3000|0|2500|2400|ran|0|causynth: the workload JVM's resident memory peaked at 2400 MB; its host was charged 2500 MB for it
28000|0|0|400,486|ran|0|
EOF

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
  campaign_host_max_used_pct=100
  campaign_host_gate_root=${solver_test}/hosts
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
  campaign_host_max_used_pct=100
  mkdir -p "${solver_test}/d"
  status=0
  campaign_host_try_charge localhost "$(campaign_solver_need_mb \
    "${solver_test}/iteration/sessions")" "${campaign_solve_cores}"
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
grep -q 'nothing withdrawn' "${worker_dir}/worker.log" \
  || fail "a replay killed before it opened a session does not say so: \
$(cat "${worker_dir}/worker.log")"
[[ ! -e "${worker_dir}/timed-out-sessions" ]] \
  || fail "the worker made a quarantine for a session that never existed"
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

withdraw_dir="${bound_dir}/withdraw"
withdraw_sessions="${withdraw_dir}/sessions"
withdraw_worker="${withdraw_dir}/obligation"
mkdir -p "${withdraw_worker}" "${withdraw_sessions}" "${withdraw_dir}/classes"
printf '{"taskId":"TASK.1"}\n' >"${withdraw_dir}/seed_plan.jsonl"
: >"${withdraw_dir}/obligations.jsonl"
mkdir -p "${withdraw_sessions}/SESSION.other"
jq -n -c '{schemaVersion: 1, kind: "SESSION_MANIFEST",
  sessionId: "SESSION.other", role: "FOCUSED",
  obligationIds: ["OB.OTHER"]}' \
  >"${withdraw_sessions}/SESSION.other/manifest.json"
: >"${withdraw_sessions}/SESSION.other/activations.jsonl.gz"
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
[[ -f "${withdraw_sessions}/SESSION.other/manifest.json" ]] \
  || fail "another worker's session was withdrawn with ours"
[[ -f "${withdraw_sessions}/SESSION.other/activations.jsonl.gz" ]] \
  || fail "another worker's session lost rows"
[[ ! -e "${withdraw_worker}/timed-out-sessions/SESSION.other" ]] \
  || fail "another worker's session was moved under our worker"
grep -q 'withdrew session SESSION.mine' "${withdraw_worker}/worker.log" \
  || fail "the withdrawal is not logged: $(cat "${withdraw_worker}/worker.log")"
[[ "$(jq -r '.verdict' "${withdraw_worker}/obligation_result.jsonl")" \
    == NOT_ADMITTED ]] \
  || fail "withdrawing the session changed the verdict row: \
$(cat "${withdraw_worker}/obligation_result.jsonl")"
[[ "$(jq -r '.detail' "${withdraw_worker}/obligation_result.jsonl")" \
    == "REPLAY_BOUNDED: replay exceeded replay_timeout_s=5" ]] \
  || fail "withdrawing the session changed the recorded detail: \
$(cat "${withdraw_worker}/obligation_result.jsonl")"

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

test_weave_key() {
  jq -r '.taskId' "$1" | LC_ALL=C sort -u | sha256sum | cut -c1-64
}

stream_fixture() {
  stream_dir="${test_tmp}/$1/iteration-0000"
  mkdir -p "${stream_dir}/sessions" "${stream_dir}/seed-replay"
  printf '{"taskId":"TASK.seed"}\n' >"${stream_dir}/execution_task_plan.jsonl"
  ln -f "${stream_dir}/execution_task_plan.jsonl" \
    "${stream_dir}/seed-replay/execution_task_plan.jsonl"
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
  TMPDIR=${test_tmp}
}
stream_planner_serve() {
  local heap=$1 id=$2 log=$4 sessions="" dir request name round
  local status refused
  printf '%s\n' "${BASHPID}" >"$5"
  shift 6
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
stream_planner_refuses() { :; }

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
  : >"${out}/corpus_read"
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
stream_propose() {
  local out=$1 id
  shift
  for id in "$@"; do
    printf '{"obligationId":"%s"}\n' "${id}" >>"${out}/obligations.jsonl"
  done
}
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
stream_stubs() {
  campaign_host_available_mb() { echo 30000; }
  campaign_host_total_mb() { echo 30000; }
  campaign_weave_key() { test_weave_key "$1"; }
  campaign_planner_serve() { stream_planner_serve "$@"; }
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
test_gated() {
  local iteration=$1 session
  shift
  mkdir -p "${iteration}/import_gated"
  for session in "$@"; do
    printf '{}\n' >"${iteration}/import_gated/${session}.json"
  done
}

stream_loop_state() {
  declare -gA stream_reruns=() stream_growing=() stream_withdrawn=() \
    stream_rests=() stream_queued_at=() stream_flying=() stream_chain=() \
    stream_confirming=() stream_entry_need=()
  stream_uncaptured=()
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

ka_dir=${test_tmp}/killed-again
while IFS='|' read -r ka_kind ka_host ka_status ka_result ka_prior ka_want; do
  rm -rf -- "${ka_dir}"
  mkdir -p "${ka_dir}/worker/sessions/OB.k-s1"
  echo '{"pathSessionId":""}' >"${ka_dir}/worker/focused_task.jsonl"
  echo replay >"${ka_dir}/worker/replay.log"
  [[ "${ka_result}" == - ]] || echo '{"verdict":"ADMITTED"}' \
    >"${ka_dir}/worker/obligation_result.jsonl"
  for (( ka_at = 1; ka_at <= ka_prior; ka_at++ )); do
    mkdir -p "${ka_dir}/worker/killed-${ka_at}"
  done
  ka_said=$(
    declare -A stream_withdrawn=()
    campaign_log() { :; }
    campaign_reap_on_host() { :; }
    campaign_sessions_naming() { find "$2" -mindepth 1 -maxdepth 1 -type d; }
    campaign_stream_enqueue() { echo "queued $*"; }
    if campaign_stream_killed_again "${ka_kind}" obligations-0001 OB.k \
        "${ka_host}" "${ka_status}" "${ka_dir}/worker" "C P"; then
      echo again
    else
      echo verdict
    fi
  )
  [[ "${ka_said}" == *"${ka_want}" ]] \
    || fail "KILLED-AGAIN: a ${ka_kind} on ${ka_host} ending ${ka_status} \
(result ${ka_result}, ${ka_prior} earlier) said '${ka_said}', not ${ka_want}"
  if [[ "${ka_want}" == again ]]; then
    [[ "${ka_said}" == "queued REPLAY obligations-0001 OB.k C P"* \
        && -s "${ka_dir}/worker/killed-$((ka_prior + 1))/replay.log" \
        && -d "${ka_dir}/worker/killed-$((ka_prior + 1))/sessions/OB.k-s1" \
        && ! -e "${ka_dir}/worker/replay.log" ]] \
      || fail "KILLED-AGAIN: the killed replay was not set aside and queued \
again: ${ka_said}"
  fi
done <<'EOF'
REPLAY|lift12|255|-|0|again
REPLAY|lift12|143|-|1|again
REPLAY|lift12|255|-|2|verdict
REPLAY|lift12|1|-|0|verdict
REPLAY|lift12|255|ADMITTED|0|verdict
REPLAY|localhost|255|-|0|verdict
OBLIGATION|lift12|255|-|0|verdict
EOF

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

(
  ss_dir=${test_tmp}/stop-solvers
  mkdir -p "${ss_dir}"
  campaign_adapter_kill_grace_s=2
  campaign_worker_host_list() { echo localhost; }
  bash -c "exec -a 'java -Xmx4096m edu.uva.liftlab.graphchecker.explore.ObligationSolverMain --serve d --sessions ${ss_dir}/a/sessions --seats 8' sleep 600" &
  ss_ours=$!
  bash -c "exec -a 'java -Xmx4096m edu.uva.liftlab.graphchecker.explore.ObligationSolverMain --serve d --sessions ${ss_dir}/b/sessions --seats 8' sleep 600" &
  ss_theirs=$!
  command sleep 0.3
  sessions=${ss_dir}/a/sessions campaign_stream_stop_solvers
  command sleep 0.3
  ss_left=$(kill -0 "${ss_ours}" 2>/dev/null && echo ours || true)
  ss_kept=$(kill -0 "${ss_theirs}" 2>/dev/null && echo theirs || true)
  kill "${ss_ours}" "${ss_theirs}" 2>/dev/null || true
  [[ -z "${ss_left}" && "${ss_kept}" == theirs ]] \
    || fail "STOP-SOLVERS: an exploration's end left its host solver \
(${ss_left:-ended}) or ended another's (${ss_kept:-ended})"
) || fail "STOP-SOLVERS failed"

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
      stream_job_charge=() stream_job_since=() stream_host_solves=() \
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
      echo "$1 $8" >>"${cp_dir}/charged"
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

for grow_verdict in confirmed refuted; do
  stream_fixture "grow-confirm-${grow_verdict}"
  mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
  printf '3\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
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

stream_fixture grow-lands
mkdir -p "${campaign_host_gate_root}/$(hostname -s)"
printf '3\n' >"${campaign_host_gate_root}/$(hostname -s)/cores"
cat >"${stream_dir}/replay.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
sleep 2
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
  do_compose() { fail "GROW-LANDS: a witness was attempted"; }
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
    jq -n -c '{occurrence: {node: "elsewhere"}, observedFatal: false}' \
      | gzip -c >"${worker}/sessions/SESSION.exposing/targets.jsonl.gz"
  }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "GROW-LANDS did not finish: $(cat "${stream_dir}/explore.log")"
gl_said="$(jq -r '[.stop, (.reaped | length), (.rerunsDropped | length)]
  | join(" ")' "${stream_dir}/exploration.json") \
$(ls "${stream_dir}/sessions" | paste -sd ' ' -) \
$(cd "${stream_dir}" && ls -d obligations-* | paste -sd ' ' -) \
$(paste -sd ' ' - <"${stream_dir}/obligations-0002/corpus.txt" || echo -) \
$(cat "${stream_dir}/uncaptured_sessions.txt" 2>/dev/null || echo -)"
[[ "${gl_said}" == "FIXED_POINT 0 0 SESSION.regrown obligations-0000 \
obligations-0001 obligations-0002 SESSION.regrown -" ]] \
  || fail "GROW-LANDS: a re-run one flip deep did not hold the fixed point \
until it landed and a round planned over it: ${gl_said}: \
$(cat "${stream_dir}/explore.log")"

stream_fixture grow-plan-only
(
  stream_stubs
  schedule_max_jobs=1
  stream_round_plan() {
    case "$1" in
      0) printf '%s\n' \
'{"kind":"EXPOSED_REGION","regionId":"REGION.grown","node":"nn0","occurrence":"REGION.grown#1","sessionId":"SESSION.seed","obligationId":""}' \
           >>"$2/growth.jsonl" ;;
    esac
  }
  do_compose() { fail "GROW-PLAN-ONLY: a witness was attempted"; }
  run_java_main() {
    local args=" $* " output plan
    plan=${args##* --plan }
    plan=${plan%% *}
    output=${args##* --output }
    output=${output%% *}
    { cat "${plan}"
      printf '{"taskId":"TASK.grown","regionId":"REGION.grown","admissionBasis":"EXPOSED_BY:SESSION.seed"}\n'
    } >"${output}"
  }
  campaign_instrument() {
    mkdir -p "$2"
    : >"$2/woven"
    printf '%s\n' "$3" >"$(dirname "$2")/weave_key"
  }
  campaign_obligation_worker() { fail "GROW-PLAN-ONLY: a replay was run"; }
  campaign_explore "${stream_dir}" iteration-0000
) >"${stream_dir}/explore.log" 2>&1 \
  || fail "GROW-PLAN-ONLY did not finish: $(cat "${stream_dir}/explore.log")"
gp_said="$(jq -r '.stop' "${stream_dir}/exploration.json") \
$(jq -r 'select(.taskId == "TASK.grown") | .taskId' \
  "${stream_dir}/execution_task_plan.jsonl") \
$(find "${stream_dir}" -name 'grow-obligations-*' | grep -c '' || true) \
$(grep -c 'grow the plan alone' "${stream_dir}/explore.log" || true)"
[[ "${gp_said}" == "FIXED_POINT TASK.grown 0 1" ]] \
  || fail "GROW-PLAN-ONLY: an exposure only the seed ran did not grow the plan \
alone, without a re-run, to a fixed point: ${gp_said}: \
$(cat "${stream_dir}/explore.log")"

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

while IFS='|' read -r inflight_case inflight_corpus inflight_grown; do
  (
    inflight_dir="${test_tmp}/grow-inflight-${inflight_case}"
    round_dir="${inflight_dir}/obligations-0004"
    iteration_dir=${inflight_dir}
    mkdir -p "${round_dir}"
    stream_loop_state
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
    jq -n '{wave: 0, branchesStopped: 0, anchorOccurrences: []}' \
      >"${round_dir}/explore_manifest.json"
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
campaign_reserve_s=20
campaign_max_claims=3
next_claim false refuted_claims
next_out=$(campaign_next_claim "${next_iteration}" 2>&1) \
  && fail "a claim past campaign_max_claims was decided again"
[[ "${next_out}" == *'campaign_max_claims=3'* \
    && ! -e "${campaign_final}/refuted/0003" ]] \
  || fail "the re-decision bound was not named: ${next_out}"
jq -n '{solver: {campaignClaim: {claim: "SAT_CANDIDATE"}},
  paths: [{pathId: "P", selector: "path_selector__4__p"}]}' \
  >"${composition_manifest}"
jq -n '{claim: {valuationOrdinal: 0}, valuations: [{ordinal: 0,
  selectedPathId: "P", selectedArms: [{selector: "m__4__a"},
  {selector: "m__3__seed"}], assignment: {}}]}' >"${campaign_final}/claim.json"
[[ "$(campaign_claim_model "${campaign_final}/claim.json" | jq -c '.arms')" \
    == '["m__4__a"]' ]] \
  || fail "a refuted model kept an arm of another path than the one it \
selected, which no refutation of that path can compose"
reset_config
campaign_budget_s=100
campaign_reserve_s=20
reproduce_min_s=1
campaign_started_s=${SECONDS}
rm -rf -- "${campaign_final}"
reproduced_claim() {
  next_claim true refuted_claims
  jq -n --argjson runs "$1" --argjson reproduced "$2" \
    '{runs: $runs, reproduced: $reproduced}' >"${campaign_final}/reproduce.json"
  mkdir -p "${campaign_final}/reproduce"
}
while IFS='|' read -r unrep_case unrep_runs unrep_reproduced unrep_next; do
  rm -rf -- "${campaign_final}"
  reproduced_claim "${unrep_runs}" "${unrep_reproduced}"
  if [[ "${unrep_next}" == next ]]; then
    unrep_out=$(campaign_unreproduced "${next_iteration}" 2>&1) \
      || fail "UNREPRODUCED ${unrep_case}: no next claim: ${unrep_out}"
    [[ -s "${campaign_final}/unreproduced/0000/reproduce.json" \
        && -s "${campaign_final}/unreproduced/0000/claim.json" \
        && ! -e "${campaign_final}/claim.json" ]] \
      || fail "UNREPRODUCED ${unrep_case}: the claim did not move aside"
    [[ "$(jq -r 'select(.outcome == "unreproduced") | .model.pathId' \
        "${next_iteration}/refuted_claims.jsonl")" == P ]] \
      || fail "UNREPRODUCED ${unrep_case}: the claim was not excluded"
    [[ "${unrep_out}" == *"kept as the fallback verdict"* ]] \
      || fail "UNREPRODUCED ${unrep_case}: not named: ${unrep_out}"
  else
    ! campaign_unreproduced "${next_iteration}" >/dev/null \
      || fail "UNREPRODUCED ${unrep_case}: the loop went on"
    [[ -s "${campaign_final}/claim.json" \
        && ! -e "${campaign_final}/unreproduced" ]] \
      || fail "UNREPRODUCED ${unrep_case}: the claim left final/"
  fi
done <<'EOF'
reproduced 0 of 10|10|0|next
reproduced 3 of 10|10|3|stop
no native run|0|0|stop
EOF
rm -rf -- "${campaign_final}"
reproduced_claim 10 0
campaign_unreproduced "${next_iteration}" >/dev/null \
  || fail "FALLBACK: the first unreproduced claim did not go aside"
next_claim false refuted_claims
campaign_fallback >/dev/null
[[ "$(jq -r '.stood' "${campaign_final}/fallback.json")" == true \
    && "$(jq -r '.confirmed' "${campaign_final}/confirm.json")" == true \
    && "$(jq -r '.reproduced' "${campaign_final}/reproduce.json")" == 0 \
    && "$(jq -r '.confirmed' "${campaign_final}/superseded/confirm.json")" \
      == false ]] \
  || fail "FALLBACK: with no later reproduction the fallback did not stand"
rm -rf -- "${campaign_final}"
reproduced_claim 10 0
campaign_unreproduced "${next_iteration}" >/dev/null \
  || fail "FALLBACK: the first unreproduced claim did not go aside"
reproduced_claim 10 2
campaign_fallback >/dev/null
[[ "$(jq -r '.stood' "${campaign_final}/fallback.json")" == false \
    && "$(jq -r '.reproduced' "${campaign_final}/reproduce.json")" == 2 \
    && ! -e "${campaign_final}/superseded" ]] \
  || fail "FALLBACK: a later reproduced claim did not stay the verdict"
rm -rf -- "${campaign_final}"
unset -f reproduced_claim
unset -f next_claim
reset_config

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
emit_fixture
rm -f -- "${campaign_final}/confirm.json"
run_emit
[[ "${emit_status}" -ne 0 ]] \
  || fail "a SAT claim with no confirmation was published as accepted"
emit_fixture_undecided_roots
rm -f -- "${campaign_final}/confirm.json"
run_emit
jq -e '.claim == "RUN_DEFECT" and .confirmation == null' \
  "${campaign_final}/result.json" >/dev/null \
  || fail "a claim that was never confirmed does not carry null: \
$(jq -c '{claim, confirmation}' "${campaign_final}/result.json")"

memory_dir="${test_tmp}/memory"
mkdir -p "${memory_dir}"

reset_config
campaign_host_gate_root="${memory_dir}/hosts"
campaign_local_host_names=" localhost gate-head "
hostname() { echo gate-head; }
memory_available=30000
campaign_host_available_mb() { echo "${memory_available}"; }
campaign_host_total_mb() { echo 31744; }
campaign_host_cores() { echo 8; }
campaign_host_max_used_pct=70
campaign_host_poll_s=0
memory_charges=()
for memory_start in 1 2 3; do
  campaign_host_try_start lift14 6000 100 \
    || fail "start ${memory_start} of 6000 MB was refused: \
${campaign_host_wait_reason}"
  memory_charges+=("${campaign_host_charge_id}")
done
run_capturing_status campaign_host_try_start lift14 6000 100
[[ "${status}" -eq 1 ]] \
  || fail "three starts charged 18000 MB, and a fourth was admitted over \
the 22221 MB ceiling while the host used 1744 MB"
[[ "${campaign_host_wait_reason}" == *"18000 MB charged"*"1744 MB in use"* ]] \
  || fail "the wait does not say what is charged and used: \
${campaign_host_wait_reason}"
( run_capturing_status campaign_host_try_start lift14 6000 100
  exit "${status}" ) \
  && fail "another campaign's start ignored the charges on the host"
[[ "$(campaign_host_room lift14)" == "4221 500" ]] \
  || fail "the room is not what the charges leave: \
$(campaign_host_room lift14)"
run_capturing_status campaign_host_try_start lift14 2000 100 3000
[[ "${status}" -eq 1 && "${campaign_host_wait_reason}" \
    == *"2000 MB and 3000 MB room beside it"* ]] \
  || fail "a start of 2000 MB leaving 3000 MB was admitted beside 18000 MB \
under a 22221 MB ceiling, or not said so: ${campaign_host_wait_reason}"
campaign_host_try_start lift14 2000 100 2000 \
  || fail "a start of 2000 MB leaving 2000 MB was refused: \
${campaign_host_wait_reason}"
[[ "$(campaign_host_room lift14)" == "2221 400" ]] \
  || fail "the room left beside a start was charged: \
$(campaign_host_room lift14)"
campaign_host_release lift14 "${campaign_host_charge_id}"
for memory_charge in "${memory_charges[@]}"; do
  campaign_host_release lift14 "${memory_charge}"
done
memory_available=10000
run_capturing_status campaign_host_try_start lift14 6000 100
[[ "${status}" -eq 1 \
    && "${campaign_host_wait_reason}" == *"0 MB charged"*"21744 MB in use"* ]] \
  || fail "a host using 21744 MB admitted 6000 MB more: \
${campaign_host_wait_reason}"
memory_available=30000
memory_lease=("${campaign_host_lease_s}" "${campaign_host_renew_s}")
campaign_host_lease_s=5
campaign_host_renew_s=1
( campaign_host_try_start lift14 6000 100 ) || fail "a subshell's start failed"
memory_gone=$(live_charges "${campaign_host_gate_root}/lift14")
campaign_host_try_start lift14 6000 100 || fail "a held start failed"
memory_held=${campaign_host_charge_id}
memory_files="${campaign_host_gate_root}/lift14/charges"
touch -d '1 minute ago' "${memory_files}/${memory_gone}" \
  "${memory_files}/${memory_held}"
sleep 2
[[ "$(campaign_host_charged "${campaign_host_gate_root}/lift14" \
    "$(date +%s)")" == "6000 100" \
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
campaign_host_try_start localhost 6000 1 \
  || fail "the head's first start was refused"
[[ -n "$(live_charges "${campaign_host_gate_root}/gate-head")" \
    && ! -e "${campaign_host_gate_root}/localhost" ]] \
  || fail "a local start is not charged to the head's own name"
mkdir "${campaign_host_gate_root}/lift15"
mkdir "${campaign_host_gate_root}/lift15/lock"
touch -d '10 minutes ago' "${campaign_host_gate_root}/lift15/lock"
run_capturing_status campaign_host_try_start lift15 6000 100
[[ "${status}" -eq 3 && ! -e "${campaign_host_gate_root}/lift15/lock" ]] \
  || fail "a lock a dead campaign left was not broken"
campaign_host_try_start lift15 6000 100 \
  || fail "the host stayed locked"
mkdir "${campaign_host_gate_root}/lift15/lock"
( sleep 1; rmdir "${campaign_host_gate_root}/lift15/lock" ) &
campaign_host_try_charge lift15 6000 100
wait
[[ "${status}" -eq 0 ]] || fail "a held lock was answered as ${status}"
cores_dir="${campaign_host_gate_root}/lift16/charges"
while IFS='|' read -r cores_rows cores_pct cores_start cores_sum cores_want; do
  rm -rf -- "${cores_dir}"
  mkdir -p "${cores_dir}"
  for cores_row in ${cores_rows//,/ }; do
    touch -d "@$(( $(date +%s) - ${cores_row#*@} ))" \
      "${cores_dir}/${cores_row%@*}"
  done
  campaign_host_max_cores_pct=${cores_pct}
  cores_got=$(campaign_host_charged "${cores_dir%/charges}" "$(date +%s)")
  [[ "${cores_got}" == "${cores_sum}" ]] \
    || fail "CORES: ${cores_rows} are charged ${cores_got}, not ${cores_sum}"
  run_capturing_status campaign_host_try_start lift16 100 "${cores_start}"
  if [[ "${cores_want}" == admit ]]; then
    [[ "${status}" -eq 0 && "${campaign_host_charge_id}" \
        == "100.${cores_start}.gate-head."* \
        && -e "${cores_dir}/${campaign_host_charge_id}" ]] \
      || fail "CORES: a start of ${cores_start} cores beside ${cores_rows} \
was not admitted and charged (${status}): ${campaign_host_wait_reason}"
    campaign_host_release lift16 "${campaign_host_charge_id}"
  else
    [[ "${status}" -eq 1 && "${campaign_host_wait_reason}" \
        == "${cores_want}" ]] \
      || fail "CORES: a start of ${cores_start} cores beside ${cores_rows} \
was not refused by its cores (${status}): ${campaign_host_wait_reason}"
  fi
done <<'EOF'
512.200.n.1.1.1@0,0.0.n.2.1.1@0,1024.300.n.3.1.1.solver@0,700.foreign@0|100|300|2236 500|admit
512.600.n.1.1.1@0|100|300|512 600|lift16 has 6.00 cores charged to what it runs; one needs 3.00 and at most 8.00 (100% of its cores) may be charged
512.550.n.1.1.1@0|100|250|512 550|admit
900.0.n.1.1.1@0|100|1200|900 0|admit
512.600.n.1.1.1@200,256.400.n.2.1.1@0|100|400|256 400|admit
256.200.n.1.1.1@0|50|250|256 200|lift16 has 2.00 cores charged to what it runs; one needs 2.50 and at most 4.00 (50% of its cores) may be charged
EOF
rm -rf -- "${cores_dir}"
while IFS='|' read -r order_need order_rows order_want; do
  rm -rf -- "${campaign_host_gate_root}"/lift2[123]
  for order_row in ${order_rows//,/ }; do
    mkdir -p "${campaign_host_gate_root}/${order_row%%:*}/charges"
    : >"${campaign_host_gate_root}/${order_row%%:*}/charges/${order_row#*:}"
  done
  order_got=$(campaign_hosts_by_room "${order_need}" lift21 lift22 lift23 \
    | paste -sd ' ' -)
  [[ "${order_got}" == "${order_want}" ]] \
    || fail "ORDER: hosts charged ${order_rows} (need ${order_need:-none}) \
were ordered ${order_got}, not ${order_want}"
done <<'EOF'
|lift21:100.6.n.1.1.1,lift22:8000.2.n.1.1.1,lift23:100.2.n.1.1.1|lift23 lift22 lift21
20000|lift21:100.6.n.1.1.1,lift22:8000.2.n.1.1.1,lift23:100.2.n.1.1.1|lift23 lift21
|lift21:9000.0.n.1.1.1,lift22:3000.0.n.1.1.1|lift23 lift22 lift21
|lift21:100.1.n.1.1.1,lift22:100.3.n.1.1.1,lift23:100.2.n.1.1.1|lift21 lift23 lift22
EOF
rm -rf -- "${campaign_host_gate_root}"/lift2[123]
while IFS='|' read -r view_rows view_want; do
  view_got=$(
    declare -A stream_host_ledger=() stream_host_view=()
    declare -a stream_hosts=() order=()
    campaign_host_poll_s=60
    for view_row in ${view_rows//,/ }; do
      IFS=: read -r view_host view_busy view_charged view_used <<<"${view_row}"
      stream_hosts+=("${view_host}")
      stream_host_ledger[${view_host}]="${test_tmp}/${view_host} 31744 22221 8"
      stream_host_view[${view_host}]="${EPOCHSECONDS} ${view_charged} 0 \
${view_used} 0 ${view_busy}"
    done
    campaign_stream_by_room REPLAY cold
    printf '%s\n' "${order[*]}"
  )
  [[ "${view_got}" == "${view_want}" ]] \
    || fail "VIEW-ORDER: hosts ${view_rows} were ordered ${view_got}, not \
${view_want}"
done <<'EOF'
a:6:100:1744,b:2:8000:1744,c:2:100:1744|c b a
a:0:9000:1744,b:0:3000:1744,c:0:100:1744|c b a
a:1:100:1744,b:3:100:1744,c:2:100:1744|a c b
EOF
(
  declare -A stream_host_ledger=() stream_host_view=() stream_jobs=() \
    stream_job_charge=()
  campaign_host_max_cores_pct=50
  campaign_host_poll_s=60
  cores_said=""
  for cores_step in start foreign start release start; do
    case "${cores_step}" in
      start)
        campaign_stream_try_charge lift16 100 200
        cores_said+="${status} "
        cores_n=${#stream_jobs[@]}
        (( status != 0 )) || stream_jobs[${cores_n}]="REPLAY r A lift16 -"
        (( status != 0 )) \
          || stream_job_charge[${cores_n}]=${campaign_host_charge_id} ;;
      foreign) : >"${cores_dir}/0.200.other.1.1.1" ;;
      release) campaign_stream_release 0 ;;
    esac
    read -r _ _ _ _ _ cores_busy <<<"${stream_host_view[lift16]}"
    cores_said+="${cores_busy} "
  done
  [[ "${cores_said}" == "0 200 200 1 400 200 0 400 " \
     && "${campaign_host_wait_reason}" == "lift16 has 4.00 cores charged"* ]] \
    || fail "STREAM-CORES: the head's view took, refused and gave back cores \
as ${cores_said}(${campaign_host_wait_reason})"
) || fail "STREAM-CORES failed"
cores_measure=${test_tmp}/cores-measured
mkdir -p "${cores_measure}"
(
  campaign_log() { :; }
  printf '180\n' >"${cores_measure}/workload_cores_x100"
  campaign_replay_cores_measured "${cores_measure}" 1
  cores_seen=${campaign_replay_cores}
  for cores_x100 in 90 80 100 60 70 95 85 5; do
    printf '%s\n' "${cores_x100}" >"${cores_measure}/workload_cores_x100"
    campaign_replay_cores_measured "${cores_measure}" 0
    cores_seen+=" ${campaign_replay_cores}"
  done
  [[ "${cores_seen}" == "200 200 200 200 200 200 200 200 100" ]] \
    || fail "REPLAY-CORES: the seed's 1.80 cores rounded up to 2.00, then once \
eight replays returned their own p90 of 1.00 rounded up, never the seed's, \
were charged ${cores_seen}"
) || fail "REPLAY-CORES failed"
unset -f hostname campaign_host_available_mb campaign_host_total_mb \
  campaign_host_cores
reset_config

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
    campaign_head_charged() { shift 2; "$@"; }
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
  campaign_host_room() { echo 100 8; }
  sleep() { echo waited >"${never_dir}/waited"; exit 0; }
  campaign_head_place 26496 1 2>/dev/null
  echo placed >"${never_dir}/waited"
) || true
[[ ! -e "${never_dir}/waited" ]] \
  || fail "HEAD-NEVER: a step no host can ever hold was $(cat \
"${never_dir}/waited")"

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

fq_iteration="${test_tmp}/fault-queue"
for fq_id in G1 F1 G2 F2; do
  mkdir -p "${fq_iteration}/obligations-0003/${fq_id}"
  fq_flag=false
  [[ "${fq_id}" != F* ]] || fq_flag=true
  echo "{\"faultFlip\":${fq_flag}}" \
    >"${fq_iteration}/obligations-0003/${fq_id}/focused_task.jsonl"
done
fq_said=$(
  iteration_dir=${fq_iteration}
  stream_queue=()
  declare -A stream_queued_at=()
  for fq_entry in "REPLAY obligations-0003 F1 T" "REPLAY obligations-0003 G1 T" \
      "REPLAY obligations-0003 F2 T" "OBLIGATION obligations-0004 O1" \
      "REPLAY obligations-0003 G2 T" "CONFIRM - C1"; do
    campaign_stream_enqueue "${fq_entry}"
  done
  printf '%s\n' "${stream_queue[@]}" | awk '{print $1 ":" $3}' | paste -sd' '
)
[[ "${fq_said}" == "CONFIRM:C1 OBLIGATION:O1 REPLAY:G2 REPLAY:G1 REPLAY:F1 REPLAY:F2" ]] \
  || fail "FAULT-QUEUE: a fault flip's replay waits behind every other entry, \
the others in their old order; the queue was '${fq_said}'"

pb_iteration=${test_tmp}/plan-blocker
mkdir -p "${pb_iteration}"
pb_said=$(campaign_plan_blocker "${pb_iteration}")
[[ -z "${pb_said}" ]] || fail "PLAN-BLOCKER: no region plan names no blocker, \
said '${pb_said}'"
for pb_cls in DIAGNOSTIC BLOCKING; do
  printf '%s\n%s\n' "{\"kind\":\"PLAN\",\"gaps\":[{\"cls\":\"BLOCKING\",\
\"kind\":\"AMBIGUOUS_FATAL_ARM\",\"subject\":\"x\"},{\"cls\":\"${pb_cls}\",\
\"kind\":\"TARGET_FATAL_IN_RECORDING\",\"subject\":\"auto0/m#epoch0/region/R#1\"}]}" \
    '{"regionId":"R"}' >"${pb_iteration}/concolic_region_plan.jsonl"
  pb_said=$(campaign_plan_blocker "${pb_iteration}")
  pb_want=""
  [[ "${pb_cls}" == DIAGNOSTIC ]] || pb_want=auto0/m#epoch0/region/R#1
  [[ "${pb_said}" == "${pb_want}" ]] || fail "PLAN-BLOCKER: a ${pb_cls} \
TARGET_FATAL_IN_RECORDING in the region plan's header names '${pb_want}', \
said '${pb_said}'"
done

dw_iteration=${test_tmp}/duplicate-world
mkdir -p "${dw_iteration}/obligations-0003/OB.d" \
  "${dw_iteration}/obligations-0002/OB.a" "${dw_iteration}/obligations-0002/OB.b" \
  "${dw_iteration}/obligations-0002/OB.c"
echo "flip:question" >"${dw_iteration}/obligations-0003/OB.d/question.asked"
echo '{"obligationId":"OB.a","verdict":"NOT_ADMITTED","sessionId":""}' \
  >"${dw_iteration}/obligations-0002/OB.a/obligation_result.jsonl"
echo '{"obligationId":"OB.b","verdict":"ADMITTED","sessionId":"OB.b-s1"}' \
  >"${dw_iteration}/obligations-0002/OB.b/obligation_result.jsonl"
echo '{"obligationId":"OB.c","verdict":"NOT_ADMITTED","sessionId":"OB.c-s1"}' \
  >"${dw_iteration}/obligations-0002/OB.c/obligation_result.jsonl"
dw_said=$(
  iteration_dir=${dw_iteration}
  results=${dw_iteration}/results.jsonl
  : >"${results}"
  stream_dirty=0
  stream_duplicates=()
  declare -A stream_flying=() stream_worlds=([w1]=OB.a [w2]=OB.b [w3]=OB.c) \
    stream_world_of=([OB.a]=w1 [OB.b]=w2 [OB.c]=w3)
  campaign_log() { :; }
  campaign_stream_duplicate "OBLIGATION obligations-0003 OB.d lift12 0" w1 \
    OB.a
  campaign_stream_land "REPLAY obligations-0002 OB.a lift12 0 -"
  campaign_stream_land "REPLAY obligations-0002 OB.b lift12 0 -"
  campaign_stream_land "REPLAY obligations-0002 OB.c lift12 0 -"
  echo "worlds=${!stream_worlds[*]} duplicates=${stream_duplicates[*]}"
  jq -r '.verdict' "${results}" | paste -sd' '
)
[[ "${dw_said}" == $'worlds=w2 duplicates=OB.d:OB.a\nDUPLICATE_WORLD NOT_ADMITTED ADMITTED NOT_ADMITTED' ]] \
  || fail "DUPLICATE-WORLD: a model of a world already replayed is settled \
DUPLICATE_WORLD with no replay, and a replay that lands anything but ADMITTED \
gives its world back; the head said '${dw_said}'"
jq -e '.verdict == "DUPLICATE_WORLD" and (.detail | contains("obligation OB.a"))' \
  "${dw_iteration}/obligations-0003/OB.d/obligation_result.jsonl" >/dev/null \
  && [[ -s "${dw_iteration}/obligations-0003/OB.d/question.txt" ]] \
  || fail "DUPLICATE-WORLD: the duplicate's row names the replay that answers \
it and its question is answered"

echo "run_engine campaign helper tests passed"
