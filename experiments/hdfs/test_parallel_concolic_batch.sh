#!/bin/bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
gc_dir=$(realpath "${script_dir}/../..")
runner="${script_dir}/run_hdfs.sh"
fixture=$(mktemp -d "${gc_dir}/target/hdfs-concolic-batch-fixture.XXXXXX")
trap 'rm -rf -- "${fixture}"' EXIT

worker="${fixture}/fixture-worker.sh"
java_stub="${fixture}/fixture-java.sh"
activity="${fixture}/activity"
mkdir -p "${activity}"
printf '%s\n' \
    '#!/bin/bash' \
    'set -euo pipefail' \
    'spec=$1' \
    'output=$(jq -r .outputDir "${spec}")' \
    'activation=$(jq -r .activationId "${spec}")' \
    '[[ -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS:-}" ]]' \
    '[[ -z "${CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES:-}" ]]' \
    '[[ -z "${CAUSYNTH_SUREFIRE_TEST_SELECTOR:-}" ]]' \
    '[[ -z "${CAUSYNTH_TEST_CLASSES_OVERLAY:-}" ]]' \
    'if [[ "${activation}" == "FAIL" ]]; then exit 42; fi' \
    'mkdir -p "${output}"' \
    'exec 9>"${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/lock"' \
    'flock 9' \
    'active=$(cat "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/active" 2>/dev/null || printf 0)' \
    'active=$((active + 1))' \
    'maximum=$(cat "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/maximum" 2>/dev/null || printf 0)' \
    'if [[ "${active}" -gt "${maximum}" ]]; then maximum=${active}; fi' \
    'printf "%s\n" "${active}" > "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/active"' \
    'printf "%s\n" "${maximum}" > "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/maximum"' \
    'flock -u 9' \
    'sleep 0.15' \
    'jq -nc --arg activation "${activation}" '\''{activationId:$activation}'\'' > "${output}/concolic_region_results.jsonl"' \
    'flock 9' \
    'active=$(cat "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/active")' \
    'printf "%s\n" "$((active - 1))" > "${CAUSYNTH_FIXTURE_ACTIVITY_DIR}/active"' \
    'flock -u 9' \
    > "${worker}"
chmod +x "${worker}"

printf '%s\n' \
    '#!/bin/bash' \
    'set -euo pipefail' \
    'output=""; diagnostics=""; cache=""; results=""; regions=""' \
    'while [[ $# -gt 0 ]]; do' \
    '  case "$1" in' \
    '    --results) results=$2; shift 2 ;;' \
    '    --output) output=$2; shift 2 ;;' \
    '    --diagnostics) diagnostics=$2; shift 2 ;;' \
    '    --cache-dir) cache=$2; shift 2 ;;' \
    '    --regions) regions=$2; shift 2 ;;' \
    '    *) shift ;;' \
    '  esac' \
    'done' \
    '[[ -s "${regions}" ]]' \
    'printf "%s\n" "${regions}" >> "${CAUSYNTH_FIXTURE_IMPORT_LOG}"' \
    'if [[ -n "${CAUSYNTH_FIXTURE_IMPORT_FAIL_ACTIVATION:-}" ]] && jq -e --arg id "${CAUSYNTH_FIXTURE_IMPORT_FAIL_ACTIVATION}" ".activationId == \$id" "${results}" >/dev/null; then exit 43; fi' \
    'mkdir -p "$(dirname "${output}")" "${cache}"' \
    'printf "{}\n" > "${output}"' \
    'printf "{}\n" > "${diagnostics}"' \
    > "${java_stub}"
chmod +x "${java_stub}"

workload=org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer#testEncryptedBalancer1
catalog="${fixture}/static-catalog/symbolic_regions.jsonl"
mkdir -p "$(dirname "${catalog}")"
printf '{}\n' > "${catalog}"
catalog_sha=$(shasum -a 256 "${catalog}" | awk '{print $1}')

write_schedule_provenance() {
    local output=$1 plan=$2 plan_sha
    plan_sha=$(shasum -a 256 "${plan}" | awk '{print $1}')
    jq -n --arg plan "${plan}" --arg planSha256 "${plan_sha}" \
        --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
        '{complete:true, scheduledActivationPlan:$plan,
          scheduledActivationPlanSha256:$planSha256, regions:$regions,
          regionsSha256:$regionsSha256}' \
        > "${output}/schedule_input_provenance.json"
}

success_manifest="${fixture}/success.jsonl"
for index in 0 1 2; do
    output="${fixture}/job-${index}"
    mkdir -p "${output}"
    printf '{}\n' > "${output}/plan.jsonl"
    write_schedule_provenance "${output}" "${output}/plan.jsonl"
    jq -nc --arg id "job-${index}" --arg plan "${output}/plan.jsonl" \
        --arg activation "ACT.${index}" --arg output "${output}" \
        --arg classes "${output}/classes" --arg static "${output}/static" \
        --arg test "${workload}" --arg regions "${catalog}" \
        --arg regionsSha256 "${catalog_sha}" \
        '{schemaVersion:2,jobId:$id,plan:$plan,activationId:$activation,
          outputDir:$output,classesDir:$classes,staticOutputDir:$static,
          test:$test,regions:$regions,
          regionsSha256:$regionsSha256}' >> "${success_manifest}"
done

export CAUSYNTH_HDFS_CONCOLIC_BATCH_FIXTURE_MODE=true
export CAUSYNTH_HDFS_CONCOLIC_BATCH_FIXTURE_WORKER="${worker}"
export CAUSYNTH_HDFS_CONCOLIC_PARALLELISM=2
export CAUSYNTH_HDFS_CONCOLIC_BATCH_STATUS_DIR="${fixture}/status"
export CAUSYNTH_FIXTURE_ACTIVITY_DIR="${activity}"
export CAUSYNTH_FIXTURE_IMPORT_LOG="${fixture}/imports.log"
export GRAPH_CHECKER_JAVA="${java_stub}"
export CAUSYNTH_OUTPUT_DIR="${fixture}/static-catalog"
export CAUSYNTH_CAMPAIGN_DISCOVERED_ACTIVATIONS="${fixture}/poison-activations.jsonl"
export CAUSYNTH_CAMPAIGN_DISCOVERED_EDGES="${fixture}/poison-edges.jsonl"
export CAUSYNTH_SUREFIRE_TEST_SELECTOR=NotTheConfiguredWorkload
export CAUSYNTH_TEST_CLASSES_OVERLAY="${fixture}/poison-overlay"

"${runner}" replay-concolic-batch "${success_manifest}" >/dev/null
summary=$(find "${fixture}/status" -name batch_summary.json -type f | sort | tail -1)
jq -e '.complete == true and .parallelism == 2 and (.jobs | length) == 3
       and all(.jobs[]; .workerStatus == 0 and .importStatus == 0)' \
    "${summary}" >/dev/null
[[ "$(cat "${activity}/maximum")" -eq 2 ]]
[[ "$(wc -l < "${fixture}/imports.log")" -eq 3 ]]

# A failed retry must not leave stale results that a later import could mistake
# for this attempt.  The ownership marker from the successful first run grants
# cleanup only for the same normalized job paths.
rerun_output="${fixture}/job-0"
mkdir -p "${rerun_output}/classes" "${rerun_output}/static" \
    "${rerun_output}/hadoop-target-snapshot" \
    "${rerun_output}/replay-work" \
    "${rerun_output}/concolic-summary-cache"
for stale_path in \
        "${rerun_output}/classes/stale" \
        "${rerun_output}/static/stale" \
        "${rerun_output}/hadoop-target-snapshot/stale" \
        "${rerun_output}/replay-work/stale" \
        "${rerun_output}/concolic-summary-cache/stale"; do
    printf 'stale\n' > "${stale_path}"
done
for stale_path in \
        "${rerun_output}/concolic_region_results.jsonl" \
        "${rerun_output}/concolic_region_summaries.jsonl" \
        "${rerun_output}/concolic_import_diagnostics.jsonl" \
        "${rerun_output}/concolic_runtime_provenance.json"; do
    printf 'stale\n' > "${stale_path}"
done
rerun_failure_manifest="${fixture}/rerun-failure.jsonl"
head -1 "${success_manifest}" \
    | jq -c '.activationId="FAIL"' > "${rerun_failure_manifest}"
if "${runner}" replay-concolic-batch \
        "${rerun_failure_manifest}" >/dev/null 2>&1; then
    echo "failed retry unexpectedly succeeded" >&2
    exit 1
fi
[[ ! -e "${rerun_output}/classes" ]]
[[ ! -e "${rerun_output}/static" ]]
[[ ! -e "${rerun_output}/hadoop-target-snapshot" ]]
[[ -d "${rerun_output}/replay-work" ]]
[[ ! -e "${rerun_output}/replay-work/stale" ]]
[[ ! -e "${rerun_output}/concolic_region_results.jsonl" ]]
[[ ! -e "${rerun_output}/concolic_region_summaries.jsonl" ]]
[[ ! -e "${rerun_output}/concolic_import_diagnostics.jsonl" ]]
[[ ! -e "${rerun_output}/concolic_runtime_provenance.json" ]]
[[ ! -e "${rerun_output}/concolic-summary-cache" ]]
[[ -f "${rerun_output}/.causynth-hdfs-concolic-batch-owner.json" ]]
[[ ! -L "${rerun_output}/.causynth-hdfs-concolic-batch-owner.json" ]]
[[ "$(wc -l < "${fixture}/imports.log")" -eq 3 ]]

# A matching JSON document behind a symlink must not grant ownership.  With the
# old -f-only check this forged marker was followed and the sentinel was erased.
symlink_output="${fixture}/symlink-job"
symlink_manifest="${fixture}/symlink.jsonl"
mkdir -p "${symlink_output}/classes"
printf '{}\n' > "${symlink_output}/plan.jsonl"
write_schedule_provenance "${symlink_output}" \
    "${symlink_output}/plan.jsonl"
jq -nc --arg plan "${symlink_output}/plan.jsonl" \
    --arg output "${symlink_output}" --arg test "${workload}" \
    --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
    '{schemaVersion:2,jobId:"symlink",plan:$plan,activationId:"SYMLINK",
      outputDir:$output,classesDir:($output+"/classes"),
      staticOutputDir:($output+"/static"),test:$test,regions:$regions,
      regionsSha256:$regionsSha256}' > "${symlink_manifest}"
forged_marker="${fixture}/forged-owner.json"
jq -n --arg output "${symlink_output}" \
    '{schemaVersion:1,kind:"HDFS_CONCOLIC_BATCH_OWNERSHIP",
      job:{jobId:"symlink",outputDir:$output,
        classesDir:($output+"/classes"),
        staticOutputDir:($output+"/static"),
        hadoopTargetDir:($output+"/hadoop-target-snapshot"),
        workDir:($output+"/replay-work")}}' > "${forged_marker}"
ln -s "${forged_marker}" \
    "${symlink_output}/.causynth-hdfs-concolic-batch-owner.json"
printf 'preserve\n' > "${symlink_output}/classes/sentinel"
if "${runner}" replay-concolic-batch \
        "${symlink_manifest}" >/dev/null 2>&1; then
    echo "batch accepted a symbolic-link ownership marker" >&2
    exit 1
fi
[[ -L "${symlink_output}/.causynth-hdfs-concolic-batch-owner.json" ]]
[[ -f "${symlink_output}/classes/sentinel" ]]
[[ "$(wc -l < "${fixture}/imports.log")" -eq 3 ]]

failure_manifest="${fixture}/failure.jsonl"
failure_output="${fixture}/failure-job"
mkdir -p "${failure_output}"
printf '{}\n' > "${failure_output}/plan.jsonl"
write_schedule_provenance "${failure_output}" \
    "${failure_output}/plan.jsonl"
jq -nc --arg plan "${failure_output}/plan.jsonl" \
    --arg output "${failure_output}" --arg test "${workload}" \
    --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
    '{schemaVersion:2,jobId:"failure",plan:$plan,activationId:"FAIL",
      outputDir:$output,classesDir:($output+"/classes"),
      staticOutputDir:($output+"/static"),test:$test,regions:$regions,
      regionsSha256:$regionsSha256}' \
    > "${failure_manifest}"
if "${runner}" replay-concolic-batch "${failure_manifest}" >/dev/null 2>&1; then
    echo "failure batch unexpectedly succeeded" >&2
    exit 1
fi
[[ "$(wc -l < "${fixture}/imports.log")" -eq 3 ]]
failure_summary=""
while IFS= read -r candidate; do
    if jq -e '.jobs | length == 1
              and .[0].job.jobId == "failure"' \
            "${candidate}" >/dev/null; then
        failure_summary="${candidate}"
        break
    fi
done < <(find "${fixture}/status" -name batch_summary.json -type f | sort)
[[ -n "${failure_summary}" ]]
jq -e '.complete == false and .workerFailureCount == 1
       and all(.jobs[]; .importStatus == null)' "${failure_summary}" >/dev/null

import_failure_manifest="${fixture}/import-failure.jsonl"
import_failure_output="${fixture}/import-failure-job"
mkdir -p "${import_failure_output}"
printf '{}\n' > "${import_failure_output}/plan.jsonl"
write_schedule_provenance "${import_failure_output}" \
    "${import_failure_output}/plan.jsonl"
jq -nc --arg plan "${import_failure_output}/plan.jsonl" \
    --arg output "${import_failure_output}" --arg test "${workload}" \
    --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
    '{schemaVersion:2,jobId:"import-failure",plan:$plan,
      activationId:"IMPORT_FAIL",outputDir:$output,
      classesDir:($output+"/classes"),staticOutputDir:($output+"/static"),
      test:$test,regions:$regions,
      regionsSha256:$regionsSha256}' > "${import_failure_manifest}"
export CAUSYNTH_FIXTURE_IMPORT_FAIL_ACTIVATION=IMPORT_FAIL
if "${runner}" replay-concolic-batch \
        "${import_failure_manifest}" >/dev/null 2>&1; then
    echo "import-failure batch unexpectedly succeeded" >&2
    exit 1
fi
unset CAUSYNTH_FIXTURE_IMPORT_FAIL_ACTIVATION
[[ "$(wc -l < "${fixture}/imports.log")" -eq 4 ]]
import_failure_summary=""
while IFS= read -r candidate; do
    if jq -e '.jobs | length == 1
              and .[0].job.jobId == "import-failure"' \
            "${candidate}" >/dev/null; then
        import_failure_summary="${candidate}"
        break
    fi
done < <(find "${fixture}/status" -name batch_summary.json -type f | sort)
[[ -n "${import_failure_summary}" ]]
jq -e '.complete == false and .workerFailureCount == 0
       and .importFailureCount == 1
       and .jobs[0].workerStatus == 0
       and .jobs[0].importStatus != 0' \
    "${import_failure_summary}" >/dev/null

duplicate_manifest="${fixture}/duplicate.jsonl"
head -1 "${success_manifest}" > "${duplicate_manifest}"
tail -1 "${success_manifest}" \
    | jq -c --arg output "${fixture}/job-0" \
        '.jobId="duplicate" | .outputDir=$output
         | .plan=($output+"/plan.jsonl")
         | .classesDir=($output+"/other-classes")
         | .staticOutputDir=($output+"/other-static")' \
    >> "${duplicate_manifest}"
if "${runner}" replay-concolic-batch "${duplicate_manifest}" >/dev/null 2>&1; then
    echo "batch accepted a shared writable output directory" >&2
    exit 1
fi

bad_hash_manifest="${fixture}/bad-hash.jsonl"
head -1 "${success_manifest}" \
    | jq -c '.jobId="bad-hash"
             | .regionsSha256="0000000000000000000000000000000000000000000000000000000000000000"' \
    > "${bad_hash_manifest}"
if "${runner}" replay-concolic-batch "${bad_hash_manifest}" >/dev/null 2>&1; then
    echo "batch accepted a mismatched region catalog hash" >&2
    exit 1
fi

# A self-consistent replacement catalog/hash is still invalid when the
# scheduler provenance bound this plan to the original static catalog.
alternate_catalog="${fixture}/alternate-catalog/symbolic_regions.jsonl"
mkdir -p "$(dirname "${alternate_catalog}")"
printf '{"alternate":true}\n' > "${alternate_catalog}"
alternate_catalog_sha=$(shasum -a 256 "${alternate_catalog}" \
    | awk '{print $1}')
wrong_catalog_manifest="${fixture}/wrong-catalog.jsonl"
head -1 "${success_manifest}" \
    | jq -c --arg regions "${alternate_catalog}" \
        --arg regionsSha256 "${alternate_catalog_sha}" \
        '.jobId="wrong-catalog" | .regions=$regions
         | .regionsSha256=$regionsSha256' \
    > "${wrong_catalog_manifest}"
if "${runner}" replay-concolic-batch \
        "${wrong_catalog_manifest}" >/dev/null 2>&1; then
    echo "batch accepted a catalog not bound by schedule provenance" >&2
    exit 1
fi

nested_manifest="${fixture}/nested.jsonl"
nested_parent="${fixture}/nested-parent"
nested_child="${nested_parent}/target/child-job"
mkdir -p "${nested_parent}" "${nested_child}"
printf '{}\n' > "${nested_parent}/plan.jsonl"
printf '{}\n' > "${nested_child}/plan.jsonl"
write_schedule_provenance "${nested_parent}" \
    "${nested_parent}/plan.jsonl"
write_schedule_provenance "${nested_child}" \
    "${nested_child}/plan.jsonl"
jq -nc --arg output "${nested_parent}" --arg plan "${nested_parent}/plan.jsonl" \
    --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
    --arg test "${workload}" \
    '{schemaVersion:2,jobId:"parent",plan:$plan,activationId:"PARENT",
      outputDir:$output,classesDir:($output+"/classes"),
      staticOutputDir:($output+"/static"),
      hadoopTargetDir:($output+"/target"),workDir:($output+"/work"),
      test:$test,regions:$regions,regionsSha256:$regionsSha256}' \
    > "${nested_manifest}"
jq -nc --arg output "${nested_child}" --arg plan "${nested_child}/plan.jsonl" \
    --arg regions "${catalog}" --arg regionsSha256 "${catalog_sha}" \
    --arg test "${workload}" \
    '{schemaVersion:2,jobId:"child",plan:$plan,activationId:"CHILD",
      outputDir:$output,classesDir:($output+"/classes"),
      staticOutputDir:($output+"/static"),
      hadoopTargetDir:($output+"/target"),workDir:($output+"/work"),
      test:$test,regions:$regions,regionsSha256:$regionsSha256}' \
    >> "${nested_manifest}"
if "${runner}" replay-concolic-batch "${nested_manifest}" >/dev/null 2>&1; then
    echo "batch accepted nested cross-job writable paths" >&2
    exit 1
fi

echo "parallel HDFS concolic batch fixture passed"
