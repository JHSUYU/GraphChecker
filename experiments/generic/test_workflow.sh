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

mkdir -p \
  "${fixture_root}/repo/module/classes" \
  "${fixture_root}/repo/module/test-classes" \
  "${fixture_root}/tool" \
  "${fixture_root}/artifacts/runtime" \
  "${fixture_root}/artifacts/schedule" \
  "${fixture_root}/custom-jdk" \
  "${fixture_root}/bin"

for file in \
  tool/fake.jar tool/env.jar tool/pom.xml target.yaml rpc.jsonl bin/z3 \
  artifacts/symbolic_regions.jsonl artifacts/static_dataflow_edges.jsonl \
  artifacts/runtime/concolic_activation_plan.jsonl \
  artifacts/runtime/runtime_region_instances.jsonl \
  artifacts/runtime/runtime_region_edge_validation.jsonl \
  artifacts/schedule/concolic_region_results.jsonl \
  artifacts/schedule/scheduled_activation_plan.jsonl \
  artifacts/schedule/concolic_region_summaries.jsonl \
  artifacts/schedule/region_path_manifest.json \
  artifacts/schedule/merged_region_summaries.jsonl \
  artifacts/schedule/branch_queries.jsonl \
  artifacts/schedule/symbolic_merge_plan.json \
  artifacts/schedule/composed_fatal.smt2 \
  artifacts/schedule/composed_smt_manifest.json \
  artifacts/schedule/symbolic_relationship_candidates.json; do
  : > "${fixture_root}/${file}"
done

config="${fixture_root}/workflow.properties"
printf '%s\n' \
  'workflow_path_base=config' \
  'graphchecker_jar=tool/fake.jar' \
  'graphchecker_pom=tool/pom.xml' \
  'graphchecker_work_dir=repo' \
  'java_bin=java' \
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
  'rpc_mapping_file=rpc.jsonl' \
  'workload_work_dir=@repo/module' \
  'workload_command=echo workflow' \
  'runtime_activation_plan=artifacts/runtime/concolic_activation_plan.jsonl' \
  'runtime_region_instances=artifacts/runtime/runtime_region_instances.jsonl' \
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
assert_contains "${analyze}" "-Dcausynth.repo=${fixture_root}/repo"

schedule=$("${runner}" --config "${config}" --dry-run schedule)
assert_contains "${schedule}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicScheduler'
assert_contains "${schedule}" \
  "--runtime-region-instances ${fixture_root}/artifacts/runtime/runtime_region_instances.jsonl"

imported=$("${runner}" --config "${config}" --dry-run import)
assert_contains "${imported}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter'

merged=$("${runner}" --config "${config}" --dry-run merge)
assert_contains "${merged}" 'edu.uva.liftlab.graphchecker.concolic.RegionSummaryMerger'

composed=$("${runner}" --config "${config}" --dry-run compose)
assert_contains "${composed}" 'edu.uva.liftlab.graphchecker.concolic.ConcolicSmtComposer'

solved=$("${runner}" --config "${config}" --dry-run solve)
assert_contains "${solved}" 'edu.uva.liftlab.graphchecker.concolic.SymbolicRelationshipVerifier'
assert_contains "${solved}" "--z3 ${fixture_root}/bin/z3"

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

legacy_config="${fixture_root}/legacy.properties"
printf '%s\n' \
  "system_classes_path=${fixture_root}/repo/module/classes" \
  "java_class_path=${fixture_root}/repo/module/classes" \
  > "${legacy_config}"
legacy=$(GRAPH_CHECKER_JAR="${fixture_root}/tool/env.jar" \
  GRAPH_CHECKER_JAVA=java \
  GRAPH_CHECKER_WORK_DIR="${fixture_root}/repo" \
  "${runner}" --dry-run process "${legacy_config}")
assert_contains "${legacy}" "${fixture_root}/tool/env.jar"
assert_contains "${legacy}" "WORK_DIR=${fixture_root}/repo"

echo 'generic workflow shell test passed'
