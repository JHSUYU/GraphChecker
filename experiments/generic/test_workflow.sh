#!/usr/bin/env bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${script_dir}/../.." && pwd -P)
runner="${graphchecker_dir}/run_engine.sh"
fixture_root=$(mktemp -d "${TMPDIR:-/tmp}/graphchecker-workflow.XXXXXX")
trap 'rm -rf "${fixture_root}"' EXIT

fail() {
  echo "workflow shell test failed: $*" >&2
  exit 1
}

assert_contains() {
  local text=$1
  local expected=$2
  [[ "${text}" == *"${expected}"* ]] \
    || fail "expected output to contain: ${expected}"
}

assert_not_contains() {
  local text=$1
  local unexpected=$2
  [[ "${text}" != *"${unexpected}"* ]] \
    || fail "expected output not to contain: ${unexpected}"
}

mkdir -p \
  "${fixture_root}/repo/module/classes" \
  "${fixture_root}/repo/module/test-classes" \
  "${fixture_root}/tool" \
  "${fixture_root}/artifacts/runtime" \
  "${fixture_root}/artifacts/schedule" \
  "${fixture_root}/custom-jdk" \
  "${fixture_root}/bin"

for file in \
  tool/fake.jar tool/env.jar tool/pom.xml target.yaml bin/z3 bin/java \
  artifacts/symbolic_regions.jsonl artifacts/static_dataflow_edges.jsonl \
  artifacts/symbolic_region_edges.jsonl \
  artifacts/runtime/concolic_region_plan.jsonl \
  artifacts/runtime/runtime_region_edge_validation.jsonl \
  artifacts/schedule/concolic_region_results.jsonl \
  artifacts/schedule/execution_task_plan.jsonl \
  artifacts/schedule/concolic_region_summaries.jsonl \
  artifacts/schedule/merged_region_summaries.jsonl \
  artifacts/schedule/branch_queries.jsonl \
  artifacts/schedule/composed_fatal.smt2 \
  artifacts/schedule/composed_smt_manifest.json \
  artifacts/schedule/symbolic_relationship_candidates.json; do
  : > "${fixture_root}/${file}"
done

printf '%s\n' '#!/usr/bin/env bash' 'exit 0' > "${fixture_root}/bin/java"
chmod +x "${fixture_root}/bin/java"
printf '%s\n' \
  '{"id":"DF.Z","kind":"z-static","fromCell":"z-cell","toCell":"sink","method":"m","siteId":"z"}' \
  '{"id":"DF.A","kind":"a-static","fromCell":"a-cell","toCell":"sink","method":"m","siteId":"a"}' \
  > "${fixture_root}/artifacts/static_dataflow_edges.jsonl"
printf '%s\n' \
  '{"regionId":"REGION.0","anchorMethod":"m","symbolicInputs":[{"portId":"in.0"}],"outputs":[{"portId":"out.0"}],"truncated":false}' \
  > "${fixture_root}/artifacts/symbolic_regions.jsonl"
printf '%s\n' \
  '{"edgeId":"REGION_EDGE.0","kind":"RPC_RETURN","fromRegion":"REGION.1","fromPort":"out.0","toRegion":"REGION.0","toPort":"in.0"}' \
  > "${fixture_root}/artifacts/symbolic_region_edges.jsonl"
printf '%s\n' \
  '{"schemaVersion":2,"kind":"RUNTIME_REGION_EDGE_EVIDENCE","edgeId":"REGION_EDGE.0","fromRegion":"REGION.1","toRegion":"REGION.0","transportKind":"RPC_RETURN","fromPort":"out.0","toPort":"in.0","requiresOrder":true,"requiresObjectIdentity":false,"state":"UNOBSERVED","bindings":[]}' \
  > "${fixture_root}/artifacts/runtime/runtime_region_edge_validation.jsonl"
printf '%s\n' \
  '{"regionInstanceId":"REGION_INSTANCE.0","regionId":"REGION.0","rootSelector":{"kind":"GLOBAL_INVOCATION","method":"m","ordinal":1},"closureGoals":[]}' \
  > "${fixture_root}/artifacts/runtime/concolic_region_plan.jsonl"
printf '%s\n' \
  '{"regionId":"REGION.0","relationallyComplete":true,"outputClosure":{"schemaVersion":1,"kind":"OUTPUT_CLOSURE_CONTRACT","producer":{"regionId":"REGION.0","regionInstanceId":"REGION_INSTANCE.0","rootCallId":1},"members":[{"output":{"portId":"out.0","cell":"out-cell","kind":"RETURN","javaTypeDescriptor":"I","selectionAuthority":"TEST_FIXTURE"},"slice":{"inputPorts":[],"sites":[],"staticSites":[],"methods":["m"],"causalEdgeIds":[],"captureBindingsRequired":false,"captureBindingsComplete":true,"captureBindings":[]}}]},"regionRelation":{"kind":"GUARDED_PATH_MERGE","cases":[{"caseId":"CASE.0","guard":{"kind":"PATH_CONDITION","conditions":[{"op":"="}]},"outputExpressions":{"out.0":{"exp":"x"}},"heapEffects":[],"normalExit":true}]}}' \
  > "${fixture_root}/artifacts/schedule/merged_region_summaries.jsonl"
printf '%s\n' \
  '{"schemaVersion":2,"kind":"CONCOLIC_COMPOSED_SMT","state":"CANDIDATE_READY","trustState":"CANDIDATE_ONLY","fatalRegion":"REGION.0","fatalSite":"m#u0","gaps":[],"includedSummaries":[],"resolvedEdgeBindings":[],"caseProjectionCatalog":[],"composedSmtArtifact":{"path":"artifacts/schedule/composed_fatal.smt2","sha256":"test"}}' \
  > "${fixture_root}/artifacts/schedule/composed_smt_manifest.json"
printf '%s\n' '(set-logic ALL)' '(assert true)' '(check-sat)' \
  > "${fixture_root}/artifacts/schedule/composed_fatal.smt2"

config="${fixture_root}/workflow.properties"
printf '%s\n' \
  'workflow_path_base=config' \
  'graphchecker_jar=tool/fake.jar' \
  'graphchecker_pom=tool/pom.xml' \
  'graphchecker_work_dir=repo' \
  'java_bin=bin/java' \
  'maven_bin=mvn' \
  'project_repo=repo' \
  'project_module_dir=@repo/module' \
  'project_classes_dir=@repo/module/classes' \
  'project_test_classes_dir=@repo/module/test-classes' \
  'project_classpath=@repo/module/classes:@repo/module/test-classes' \
  'analysis_classes_dir=artifacts/instrumented' \
  'causynth_output_dir=artifacts' \
  'causynth_target_spec=target.yaml' \
  'custom_jdk_home=custom-jdk' \
  'z3_bin=bin/z3' \
  'workload_work_dir=@repo/module' \
  'workload_command=echo workflow' \
  'trace_test=workflow-shell-test' \
  'runtime_region_plan=artifacts/runtime/concolic_region_plan.jsonl' \
  'runtime_edge_validations=artifacts/runtime/runtime_region_edge_validation.jsonl' \
  'schedule_output_dir=artifacts/schedule' \
  'reach_report=artifacts/reports/reach-condition.json' \
  'reach_max_inputs=7' \
  'reach_max_valuations=128' \
  > "${config}"

bash -n "${runner}"
bash -n "${BASH_SOURCE[0]}"

help_text=$("${runner}" help)
assert_contains "${help_text}" \
  'reach       Project the composed bug path onto finite Boolean root inputs'
assert_not_contains "${help_text}" \
  'merge       Merge imported output paths into guarded region relations'

normalized=$("${runner}" --config "${config}" config)
assert_contains "${normalized}" "project_repo=${fixture_root}/repo"
assert_contains "${normalized}" "project_module_dir=${fixture_root}/repo/module"
assert_contains "${normalized}" "z3_bin=${fixture_root}/bin/z3"
assert_contains "${normalized}" \
  "reach_report=${fixture_root}/artifacts/reports/reach-condition.json"
assert_contains "${normalized}" 'reach_max_inputs=7'
assert_contains "${normalized}" 'reach_max_valuations=128'

overridden=$(CAUSYNTH_OUTPUT_DIR=@config/env-output \
  GRAPH_CHECKER_JAR=@config/tool/env.jar \
  "${runner}" --config "${config}" config)
assert_contains "${overridden}" "causynth_output_dir=${fixture_root}/env-output"
assert_contains "${overridden}" "graphchecker_jar=${fixture_root}/tool/env.jar"

validation=$("${runner}" --config "${config}" validate)
assert_contains "${validation}" 'Workflow configuration is valid.'

invalid_log="${fixture_root}/invalid-reach-limit.log"
if CAUSYNTH_REACH_MAX_VALUATIONS=0 \
    "${runner}" --config "${config}" validate \
    >"${invalid_log}" 2>&1; then
  fail 'reach_max_valuations=0 unexpectedly passed validation'
fi
assert_contains "$(<"${invalid_log}")" \
  'reach_max_valuations must be greater than zero'

build=$("${runner}" --config "${config}" --dry-run build)
assert_contains "${build}" 'mvn'
assert_contains "${build}" "${fixture_root}/tool/pom.xml"

analyze=$("${runner}" --config "${config}" --dry-run analyze)
assert_contains "${analyze}" 'edu.uva.liftlab.graphchecker.GraphCheckerMain'
assert_contains "${analyze}" "-Dcausynth.target.spec=${fixture_root}/target.yaml"

quiet_stdout="${fixture_root}/quiet.stdout"
quiet_stderr="${fixture_root}/quiet.stderr"
"${runner}" --config "${config}" analyze \
  >"${quiet_stdout}" 2>"${quiet_stderr}"
[[ ! -s "${quiet_stderr}" ]] || fail 'debug output was enabled by default'

debug_stdout="${fixture_root}/debug.stdout"
debug_stderr="${fixture_root}/debug.stderr"
GRAPH_CHECKER_DEBUG_MAX_ITEMS=1 \
  "${runner}" --config "${config}" --debug analyze \
  >"${debug_stdout}" 2>"${debug_stderr}"
[[ ! -s "${debug_stdout}" ]] || fail 'analyze debug output leaked to stdout'
debug_text=$(<"${debug_stderr}")
assert_contains "${debug_text}" 'artifact=static_graph'
assert_contains "${debug_text}" 'total=2 shown=1 truncated=true'
assert_contains "${debug_text}" 'a-static'
assert_not_contains "${debug_text}" 'z-static'

"${runner}" --config "${config}" --debug workload \
  >"${debug_stdout}" 2>"${debug_stderr}"
assert_contains "$(<"${debug_stdout}")" 'workflow'
debug_text=$(<"${debug_stderr}")
assert_contains "${debug_text}" 'artifact=runtime_region_edge_validation'
assert_contains "${debug_text}" 'artifact=concolic_region_instance_plan'
assert_contains "${debug_text}" 'total=1 shown=1 truncated=false'
assert_contains "${debug_text}" '"regionInstanceId":"REGION_INSTANCE.0"'
assert_contains "${debug_text}" '"goalCount":0'
assert_not_contains "${debug_text}" 'status=invalid-json'

"${runner}" --config "${config}" debug-stage merge \
  >"${debug_stdout}" 2>"${debug_stderr}"
assert_contains "$(<"${debug_stderr}")" 'artifact=guarded_merge'
assert_contains "$(<"${debug_stderr}")" 'GUARDED_PATH_MERGE'
assert_contains "$(<"${debug_stderr}")" '"relationallyComplete":true'

"${runner}" --config "${config}" --debug compose \
  >"${debug_stdout}" 2>"${debug_stderr}"
debug_text=$(<"${debug_stderr}")
assert_contains "${debug_text}" 'artifact=composition_manifest'
assert_contains "${debug_text}" 'artifact=candidate_smt'
assert_contains "${debug_text}" '"state":"CANDIDATE_READY"'
assert_contains "${debug_text}" '(check-sat)'

schedule=$("${runner}" --config "${config}" --dry-run schedule)
assert_contains "${schedule}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler'
assert_not_contains "${schedule}" '--runtime-region-instances'

imported=$("${runner}" --config "${config}" --dry-run import)
assert_contains "${imported}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter'

composed=$("${runner}" --config "${config}" --dry-run compose)
assert_contains "${composed}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer'

reached=$("${runner}" --config "${config}" --dry-run reach)
assert_contains "${reached}" \
  'edu.uva.liftlab.graphchecker.concolic.BooleanReachConditionExtractor'
assert_contains "${reached}" \
  "--smt ${fixture_root}/artifacts/schedule/composed_fatal.smt2"
assert_contains "${reached}" \
  "--manifest ${fixture_root}/artifacts/schedule/composed_smt_manifest.json"
assert_contains "${reached}" \
  "--regions ${fixture_root}/artifacts/symbolic_regions.jsonl"
assert_contains "${reached}" \
  "--relationships ${fixture_root}/artifacts/schedule/symbolic_relationship_candidates.json"
assert_contains "${reached}" \
  "--output ${fixture_root}/artifacts/reports/reach-condition.json"
assert_contains "${reached}" "--z3 ${fixture_root}/bin/z3"
assert_contains "${reached}" '--timeout-ms 20000'
assert_contains "${reached}" '--max-inputs 7'
assert_contains "${reached}" '--max-valuations 128'

reach_overridden=$(CAUSYNTH_REACH_REPORT=@config/artifacts/env-reach.json \
  CAUSYNTH_REACH_MAX_INPUTS=5 CAUSYNTH_REACH_MAX_VALUATIONS=32 \
  "${runner}" --config "${config}" config)
assert_contains "${reach_overridden}" \
  "reach_report=${fixture_root}/artifacts/env-reach.json"
assert_contains "${reach_overridden}" 'reach_max_inputs=5'
assert_contains "${reach_overridden}" 'reach_max_valuations=32'

echo 'generic workflow shell test passed'
