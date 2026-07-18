#!/bin/bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
gc_dir=$(realpath "${script_dir}/../..")
runner="${script_dir}/run_hdfs.sh"
mkdir -p "${gc_dir}/target"
fixture=$(mktemp -d "${gc_dir}/target/causynth-handoff-fixture.XXXXXX")
trap 'chmod -R u+w "${fixture}" 2>/dev/null || true; rm -rf "${fixture}"' EXIT

sha() {
    shasum -a 256 "$1" | awk '{print $1}'
}

lines() {
    jq -s 'length' "$1"
}

state_entry() {
    local role=$1 path=$2
    jq -nc --arg role "${role}" --arg file "$(basename "${path}")" \
        --arg sha "$(sha "${path}")" --argjson count "$(lines "${path}")" \
        '{role:$role,file:$file,sha256:$sha,lineCount:$count}'
}

generation="GEN.FIXTURE"
activation="ACT.FRESH"
region="REGION.FRESH"
instance="REGION.FRESH@INSTANCE.1"
summary_id="SUMMARY.FRESH"
campaign_dir="${fixture}/campaign"
generation_dir="${campaign_dir}/state-generations/${generation}"
mkdir -p "${generation_dir}"

regions="${generation_dir}/campaign_regions.jsonl"
activations="${generation_dir}/campaign_activations.jsonl"
edges="${generation_dir}/campaign_edge_validations.jsonl"
roots="${generation_dir}/campaign_roots.jsonl"
summaries="${generation_dir}/campaign_summaries.jsonl"
records="${generation_dir}/region_path_records.jsonl"
static_graph="${generation_dir}/campaign_static_graph.jsonl"
runtime_instances="${fixture}/runtime_region_instances.jsonl"
complete="${generation_dir}/campaign_complete_manifest.json"
generation_manifest="${generation_dir}/state_manifest.json"
pointer="${campaign_dir}/campaign_state_manifest.json"
jar="${fixture}/GraphChecker-fixture.jar"

printf '%s\n' '{"regionId":"REGION.FRESH"}' \
    '{"regionId":"REGION.UPSTREAM"}' > "${regions}"
jq -nc --arg activation "${activation}" --arg region "${region}" \
    --arg instance "${instance}" \
    '{activationId:$activation,regionId:$region,regionInstanceId:$instance}' \
    > "${activations}"
printf '%s\n' '{"edgeId":"EDGE.FIXTURE"}' > "${edges}"
printf '%s\n' '{"pathId":"PATH.FIXTURE"}' > "${records}"
printf '%s\n' '{"edgeId":"STATIC.FIXTURE"}' > "${static_graph}"
jq -nc --arg region "${region}" --arg instance "${instance}" \
    '{regionId:$region,regionInstanceId:$instance}' > "${runtime_instances}"
printf '%s\n' 'fixture-jar' > "${jar}"

jq -nc --arg activation "${activation}" --arg region "${region}" \
    --arg instance "${instance}" --arg summary "${summary_id}" '
    {activationId:$activation,regionId:$region,regionInstanceId:$instance,
     validatedSummaryId:$summary,readyForSolver:true,
     replayAlreadyValidated:true,targetReplayValidated:true,
     replayValidationAuthority:
       "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY",
     siteId:"SITE.FRESH",occurrence:1,desiredOutcome:true,conditionIndex:0,
     constraints:[{op:"bool",value:true}],
     freshObservedTargetCondition:{op:"bool",value:true},
     negatedTargetCondition:{op:"bool",value:true},
     engineArrayInputBindings:[],
     symbolicContext:{regionId:$region,regionInstanceId:$instance},
     formulaAuthority:
       "FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_PLUS_OBSERVED_TARGET",
     targetPolicy:"KEEP_FRESH_OBSERVED_DESIRED_TARGET_CONDITION",
     freshQueryRebuildProvenance:{freshSummaryId:$summary,
       activationId:$activation,regionInstanceId:$instance,
       transitionExecutionId:"EXEC.1",
       authority:"FRESH_SUMMARY_PATH_AND_CURRENT_RUNTIME_EDGE_LEDGER"},
     targetRebaseProvenance:{activationId:$activation,
       regionInstanceId:$instance,downstreamInjectionUsed:false,
       branchOverrideUsed:false,
       authority:
         "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"}}' \
    > "${roots}"
jq -nc --arg activation "${activation}" --arg region "${region}" \
    --arg instance "${instance}" --arg summary "${summary_id}" '
    {summaryId:$summary,activationId:$activation,regionId:$region,
     regionInstanceId:$instance,valid:true,targetReplayValidated:true,
     branchOverrideUsed:false,captureGoal:{kind:"TARGET_BRANCH"},
     executionAdmission:{required:true,valid:true,
       branchOverrideAccepted:false,
       authority:
         "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION"}}' \
    > "${summaries}"
jq -nc '
    {summaryId:"SUMMARY.UPSTREAM",activationId:"ACT.UPSTREAM",
     regionId:"REGION.UPSTREAM",regionInstanceId:"UPSTREAM@INSTANCE.1",
     valid:true,branchOverrideUsed:false,
     captureGoal:{kind:"OUTPUT_CLOSURE"},
     requestedOutput:{portId:"REGION.UPSTREAM.out.0"},
     outputExpressions:{"REGION.UPSTREAM.out.0":{op:"int",value:1}},
     executionAdmission:{required:false,valid:true,
       branchOverrideAccepted:false,authority:"OBSERVED_TARGET_SEED_PATH_ONLY"}}' \
    >> "${summaries}"
jq -nc '
    {summaryId:"SUMMARY.QUARANTINED",activationId:"ACT.QUARANTINED",
     regionId:"REGION.UPSTREAM",regionInstanceId:"UPSTREAM@INSTANCE.OLD",
     valid:true,discoveryOnly:true,summaryCacheAdmission:"QUARANTINED",
     captureGoal:{kind:"OUTPUT_CLOSURE"},
     requestedOutput:{portId:"REGION.UPSTREAM.out.0"},
     executionAdmission:{required:false,valid:true,
       branchOverrideAccepted:false,authority:"OBSERVED_TARGET_SEED_PATH_ONLY"}}' \
    >> "${summaries}"

write_complete() {
    local complete_value=$1
    jq -n --arg activation "${activation}" --arg region "${region}" \
        --arg instance "${instance}" --argjson completeValue "${complete_value}" '
        {schemaVersion:1,kind:"CONCOLIC_REGION_CAMPAIGN",
         complete:$completeValue,status:"COMPLETE_FOCUSED_TRANSITION_DISCOVERY",
         transitionFocusOnly:true,focusedTargetComplete:true,
         transitionDiscovery:{complete:true},gapCount:0,gaps:[],
         postDiscoveryTargetRebaseCompleted:true,
         postDiscoveryTargetRebaseRequired:false,
         postDiscoveryTargetRebaseReady:true,targetRootAdmissionComplete:true,
         branchOverrideAccepted:false,
         postDiscoveryTargetRebaseActivationId:$activation,
         postDiscoveryTargetRebaseRegionInstanceId:$instance,
         postDiscoveryTargetRebase:{activationId:$activation,regionId:$region,
           regionInstanceId:$instance,
           authority:
             "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_TARGET_REPLAY"}}' \
        > "${complete}"
}

rebuild_authority() {
    local state_files
    state_files=$({
        state_entry REGIONS "${regions}"
        state_entry ACTIVATIONS "${activations}"
        state_entry EDGES "${edges}"
        state_entry ROOTS "${roots}"
        state_entry SUMMARIES "${summaries}"
        state_entry PATH_RECORDS "${records}"
        state_entry STATIC_GRAPH "${static_graph}"
    } | jq -s '.')
    jq -n --arg generation "${generation}" \
        --arg completion "$(basename "${complete}")" \
        --arg completionSha "$(sha "${complete}")" \
        --argjson files "${state_files}" '
        {schemaVersion:2,kind:"CONCOLIC_CAMPAIGN_STATE_GENERATION",
         generation:$generation,complete:true,
         campaignCompleteManifest:$completion,
         campaignCompleteManifestSha256:$completionSha,stateFiles:$files}' \
        > "${generation_manifest}"
    jq -n --arg generation "${generation}" \
        --arg manifest "state-generations/${generation}/state_manifest.json" \
        --arg manifestSha "$(sha "${generation_manifest}")" \
        --arg completion \
            "state-generations/${generation}/campaign_complete_manifest.json" \
        --arg completionSha "$(sha "${complete}")" '
        {schemaVersion:2,kind:"CONCOLIC_CAMPAIGN_STATE_POINTER",
         generation:$generation,complete:true,manifest:$manifest,
         manifestSha256:$manifestSha,campaignCompleteManifest:$completion,
         campaignCompleteManifestSha256:$completionSha}' > "${pointer}"
}

publish() {
    CAUSYNTH_GC_JAR="${jar}" \
    CAUSYNTH_FRESH_HANDOFF_TEST_MODE=true \
    CAUSYNTH_FRESH_HANDOFF_SCHEDULER_FIXTURE=true \
    CAUSYNTH_SCHEDULE_RUNTIME_REGION_INSTANCES="${runtime_instances}" \
        "${runner}" publish-campaign-handoff \
            "fixture.Test#freshHandoff" "${campaign_dir}"
}

# An incomplete authoritative completion snapshot must fail before publication.
write_complete false
rebuild_authority
if publish >/dev/null 2>&1; then
    echo "[FAIL] Incomplete campaign was published" >&2
    exit 1
fi

# Canonical containment must reject a symlinked fresh-handoffs parent.
write_complete true
rebuild_authority
mkdir -p "${fixture}/escape"
ln -s "${fixture}/escape" "${campaign_dir}/fresh-handoffs"
if publish >/dev/null 2>&1; then
    echo "[FAIL] Symlinked handoff output escaped canonical containment" >&2
    exit 1
fi
if [[ -n "$(find "${fixture}/escape" -mindepth 1 -print -quit)" ]]; then
    echo "[FAIL] Publisher wrote through the rejected symlink" >&2
    exit 1
fi
rm "${campaign_dir}/fresh-handoffs"

# Execute the real publisher, then execute it again to exercise immutable reuse.
publish
manifest=$(find "${campaign_dir}/fresh-handoffs" -type f \
    -name campaign_handoff_manifest.json -print -quit)
if [[ -z "${manifest}" ]]; then
    echo "[FAIL] Publisher emitted no handoff manifest" >&2
    exit 1
fi
reuse_output=$(publish)
if [[ "${reuse_output}" != *"reusing immutable fresh handoff"* ]]; then
    echo "[FAIL] Second publication did not take the verified reuse path" >&2
    exit 1
fi
CAUSYNTH_GC_JAR="${jar}" "${runner}" verify-campaign-handoff "${manifest}"

upstream=$(jq -r '[.artifacts[] | select(.role == "UPSTREAM_SUMMARIES")][0].path' \
    "${manifest}")
if jq -e 'select(.discoveryOnly == true
        or ((.summaryCacheAdmission // "") | contains("QUARANTINED")))' \
        "${upstream}" >/dev/null; then
    echo "[FAIL] Quarantined discovery summary entered the handoff" >&2
    exit 1
fi
if [[ "$(lines "${upstream}")" -ne 1 ]]; then
    echo "[FAIL] Admitted upstream projection has the wrong cardinality" >&2
    exit 1
fi

# Recompute the artifact hash after a semantically wrong derived projection;
# verification must reject it by ledger equality, not merely by stale hash.
cp "${upstream}" "${fixture}/upstream.original"
cp "${manifest}" "${fixture}/manifest.original"
chmod u+w "${upstream}" "${manifest}"
cp "${roots}" "${upstream}"
bad_sha=$(sha "${upstream}")
jq --arg sha "${bad_sha}" '
    (.artifacts[] | select(.role == "UPSTREAM_SUMMARIES")).sha256 = $sha' \
    "${manifest}" > "${fixture}/manifest.bad"
mv "${fixture}/manifest.bad" "${manifest}"
if CAUSYNTH_GC_JAR="${jar}" "${runner}" verify-campaign-handoff \
        "${manifest}" >/dev/null 2>&1; then
    echo "[FAIL] Semantically tampered derived upstream projection was accepted" >&2
    exit 1
fi
mv "${fixture}/upstream.original" "${upstream}"
mv "${fixture}/manifest.original" "${manifest}"
CAUSYNTH_GC_JAR="${jar}" "${runner}" verify-campaign-handoff "${manifest}"

echo "[PASS] fresh handoff publish/reuse, authority, quarantine, tamper, and symlink fixture"
