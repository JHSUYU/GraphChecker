#!/usr/bin/env bash

set -euo pipefail

fixture_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
graphchecker_dir=$(cd "${fixture_dir}/../../.." && pwd -P)
fixture_runner="${fixture_dir}/run.sh"
engine_runner="${graphchecker_dir}/run_engine.sh"

die() {
  echo "[three-thread-rpc-matrix] $*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: experiments/generic/three-thread-rpc/run_robustness_matrix.sh [MODE]

  core  Run baseline, cross-method-fields, and multitype (default).
  all   Also run dependent-scalar, containers, and unreachable-parity.
  baseline | cross-method-fields | multitype | dependent-scalar | containers |
  unreachable-parity
        Run one named workload. This is useful for an exact post-fix gate.

Each entry runs the fixture runner's clean and candidate commands, invokes Z3
on the emitted SMT, and validates the exact candidate reach profile. Natural
replay promotion is intentionally outside this gate and remains a TODO.
EOF
}

require_command() {
  command -v "$1" >/dev/null 2>&1 \
    || die "required command not found: $1"
}

require_file() {
  [[ -f "$2" ]] || die "$1 not found: $2"
}

configured_value() {
  local normalized=$1
  local key=$2
  local value
  value=$(awk -v requested="${key}" '
    index($0, requested "=") == 1 {
      print substr($0, length(requested) + 2)
      found = 1
    }
    END { if (!found) exit 1 }
  ' <<< "${normalized}") \
    || die "normalized workflow configuration has no ${key}"
  [[ -n "${value}" ]] \
    || die "normalized workflow configuration has empty ${key}"
  printf '%s\n' "${value}"
}

resolve_executable() {
  local configured=$1
  if [[ "${configured}" == */* ]]; then
    [[ -x "${configured}" ]] \
      || die "configured executable is not runnable: ${configured}"
    realpath -m -- "${configured}"
    return
  fi
  command -v "${configured}" \
    || die "configured command not found: ${configured}"
}

sha256_file() {
  sha256sum "$1" | awk '{print $1}'
}

validate_json_object() {
  local role=$1
  local path=$2
  require_file "${role}" "${path}"
  jq -e 'type == "object"' "${path}" >/dev/null \
    || die "${role} is not one JSON object: ${path}"
}

validate_artifact_binding() {
  local manifest=$1
  local field=$2
  local expected=$3
  local declared_path declared_hash declared_size
  local expected_path actual_hash actual_size
  declared_path=$(jq -er --arg field "${field}" '
    .[$field].path | select(type == "string" and length > 0)
  ' "${manifest}") \
    || die "${manifest} has no ${field}.path"
  declared_hash=$(jq -er --arg field "${field}" '
    .[$field].sha256
    | select(type == "string" and test("^[0-9a-f]{64}$"))
  ' "${manifest}") \
    || die "${manifest} has no valid ${field}.sha256"
  declared_size=$(jq -er --arg field "${field}" '
    .[$field].sizeBytes | select(type == "number" and . >= 0)
  ' "${manifest}") \
    || die "${manifest} has no valid ${field}.sizeBytes"
  require_file "${field} artifact" "${expected}"
  expected_path=$(realpath -m -- "${expected}")
  [[ "$(realpath -m -- "${declared_path}")" == "${expected_path}" ]] \
    || die "${field} path does not bind ${expected_path}"
  actual_hash=$(sha256_file "${expected}")
  [[ "${actual_hash}" == "${declared_hash}" ]] \
    || die "${field} hash does not match ${expected}"
  actual_size=$(stat -c '%s' "${expected}")
  [[ "${actual_size}" == "${declared_size}" ]] \
    || die "${field} size does not match ${expected}"
}

validate_composition_common() {
  local manifest=$1
  jq -e '
    .schemaVersion == 1
    and .kind == "CONCOLIC_COMPOSED_SMT"
    and .structurallyComplete == true
    and ((.unsupportedExpressions // []) | length) == 0
    and ((.unboundPorts // []) | length) == 0
    and (.fatalConditionCount // 0) > 0
    and (.resolvedProducerCount // 0) > 0
  ' "${manifest}" >/dev/null \
    || die "composition manifest is incomplete: ${manifest}"
}

validate_multitype_producer_artifacts() {
  local work_root=$1
  local campaign_root="${work_root}/producer-campaign"
  local -a path_closures merged_summaries

  [[ -d "${campaign_root}" ]] \
    || die "multitype producer campaign not found: ${campaign_root}"
  mapfile -t path_closures < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name region_path_closure.json | sort)
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)
  [[ ${#path_closures[@]} -eq 2 ]] \
    || die "multitype expected two producer path closures"
  [[ ${#merged_summaries[@]} -eq 2 ]] \
    || die "multitype expected two producer guarded merges"

  jq -e -s '
    length == 2
    and all(.[];
      .schemaVersion == 1
      and .kind == "REGION_PATH_WORKLIST"
      and .status == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .complete == true
      and .wallClockBoundReached == false
      and .gapCount == 0
      and ((.gaps // []) | length) == 0
      and .pendingTaskCount == 0
      and .observedPathCount > 1
      and .candidateFlipCount > 0
      and ([.pathCountByRegion[]] | add) == .observedPathCount)
  ' "${path_closures[@]}" >/dev/null \
    || die "multitype producer path closure is incomplete or single-path"

  jq -e -s '
    length == 2
    and all(.[];
      .valid == true
      and .relationallyComplete == true
      and .regionRelation.kind == "GUARDED_PATH_MERGE"
      and .regionRelation.complete == true
      and .regionRelation.pathClosureStatus
        == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .regionRelation.guardSemantics
        == "EXACT_NORMALIZED_PATH_CONDITION"
      and .regionRelation.caseCount > 1
      and .regionRelation.caseCount == (.regionRelation.cases | length)
      and all(.regionRelation.cases[];
        .guard.kind == "PATH_CONDITION"
        and ((.guard.conditions // []) | length) > 0))
    # Java double comparison is captured as dcmpl, long comparison as lcmp,
    # and String.contains remains a first-class string AST node.
    and ([.[] | .regionRelation.cases[].guard.conditions[]
      | .. | objects | select(._op? == "--l")] | length) > 0
    and ([.[] | .regionRelation.cases[].guard.conditions[]
      | .. | objects | select(._op? == "--")] | length) > 0
    and ([.[] | .regionRelation.cases[].guard.conditions[]
      | .. | objects
      | select(._type? == "OpStrExpression"
        and ._name? == "contains")] | length) > 0
    # A completed bounded loop path visits the same guard PC more than once.
    # This checks semantic occurrences, not a fixture-specific unit index.
    and any(.[] | .regionRelation.cases[];
      ([.guard.conditions[]._code_position? | select(. != null)]
        | length)
      > ([.guard.conditions[]._code_position? | select(. != null)]
        | unique | length))
  ' "${merged_summaries[@]}" >/dev/null \
    || die "multitype guarded merge lost double/long/string/loop semantics"
}

validate_dependent_scalar_artifacts() {
  local work_root=$1
  local target_resolution="${work_root}/analysis/target_resolved.json"
  local activation_plan="${work_root}/runtime/concolic_activation_plan.jsonl"
  local campaign_root="${work_root}/producer-campaign"
  local fixture_class="edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload"
  local target_method="<${fixture_class}\$ConsumerThread: void executeWorker()>"
  local target_exception="${fixture_class}\$DependentScalarBugReachedException"
  local arithmetic_cell="<${fixture_class}\$RpcBus: int arithmeticValue>"
  local text_cell="<${fixture_class}\$RpcBus: int textValue>"
  local -a path_closures merged_summaries

  require_file "dependent-scalar annotation target" "${target_resolution}"
  require_file "dependent-scalar runtime activation plan" "${activation_plan}"
  [[ -d "${campaign_root}" ]] \
    || die "dependent-scalar producer campaign not found: ${campaign_root}"

  # The target is the one class-file annotation, not a rediscovered exception
  # type or a fixture-provided branch formula.  Bytecode offsets and source
  # lines are deliberately excluded because they are not semantic identity.
  jq -e --arg method "${target_method}" \
    --arg exception "${target_exception}" '
    .seedMode == "EXCEPTION_ANNOTATION"
    and .seedException == $exception
    and .exceptionTarget.id == "dependent-scalar"
    and .exceptionTarget.method == $method
    and .exceptionTarget.exception == $exception
    and .exceptionTarget.authority
      == "CLASSFILE_CAUSYNTH_EXCEPTION_TARGET_TYPE_USE_V1"
    and .discoveredSeedCount == 1
    and .discoveredSeedMethods == [$method]
  ' "${target_resolution}" >/dev/null \
    || die "dependent-scalar lost its exact annotated target root"

  # Runtime discovery must expose both scalar publishers as distinct producer
  # roots converging on one TARGET_BRANCH instance.  Region numbers and event
  # sequence values are intentionally not pinned.
  jq -e -s --arg arithmetic "${arithmetic_cell}" \
    --arg text "${text_cell}" '
    [.[] | select(
      .captureGoal.kind == "OUTPUT_CLOSURE"
      and .captureGoal.scope == "BOUNDED_OUTPUT_RELEVANT_PATHS"
      and .replayable == true
      and .symbolicReady == true
      and (.requestedOutput.cell == $arithmetic
        or .requestedOutput.cell == $text))] as $producers
    | ([$producers[].edgeBindings[]?
        | select(.relation == "READ_FROM"
          and .selectionAuthority == "RUNTIME_CONFIRMED_READ_FROM"
          and .fromOutputCell == .toInputCell)] as $edges
      | ($producers | length) == 2
      and ([$producers[].requestedOutput.cell] | sort)
        == ([$arithmetic, $text] | sort)
      and ([$producers[].regionId] | unique | length) == 2
      and ($edges | length) == 2
      and ([$edges[].fromOutputCell] | sort)
        == ([$arithmetic, $text] | sort)
      and ([$edges[].toRegionInstance] | unique | length) == 1
      and all($edges[];
        .fromRegion != .toRegion
        and .objectIdentityConfirmed == true
        and .orderConfirmed == true
        and .canonicalOutputAliasUsed == false
        and .canonicalInputResolutionUsed == true)
      and ([.[] | select(
          .captureGoal.kind == "TARGET_BRANCH"
          and .replayable == true
          and .regionId == $edges[0].toRegion
          and .regionInstanceId == $edges[0].toRegionInstance)]
        | length) == 1)
  ' "${activation_plan}" >/dev/null \
    || die "dependent-scalar runtime roots are not two exact producers and one target"

  mapfile -t path_closures < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name region_path_closure.json | sort)
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)
  [[ ${#path_closures[@]} -eq 2 ]] \
    || die "dependent-scalar expected two producer path closures"
  [[ ${#merged_summaries[@]} -eq 2 ]] \
    || die "dependent-scalar expected two producer guarded merges"

  jq -e -s '
    length == 2
    and all(.[];
      .schemaVersion == 1
      and .kind == "REGION_PATH_WORKLIST"
      and .status == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .complete == true
      and .wallClockBoundReached == false
      and .gapCount == 0
      and ((.gaps // []) | length) == 0
      and .pendingTaskCount == 0
      and .observedPathCount > 1
      and .candidateFlipCount > 0
      and ([.pathCountByRegion[]] | add) == .observedPathCount)
    and ([.[].observedPathCount] | sort) == [2, 6]
  ' "${path_closures[@]}" >/dev/null \
    || die "dependent-scalar producer path closure is incomplete"

  # The string producer has exactly the two semantic outputs 5 and 9.  The
  # arithmetic producer has six feasible clamp/add path partitions.  These
  # are source-level domains, unlike region IDs, unit indexes, or symbols.
  jq -e -s --arg arithmetic "${arithmetic_cell}" \
    --arg text "${text_cell}" '
    length == 2
    and ([.[].requestedOutputSlice.outputCell] | sort)
      == ([$arithmetic, $text] | sort)
    and all(.[];
      .valid == true
      and .relationallyComplete == true
      and .regionRelation.kind == "GUARDED_PATH_MERGE"
      and .regionRelation.complete == true
      and .regionRelation.pathClosureStatus
        == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .regionRelation.guardSemantics
        == "EXACT_NORMALIZED_PATH_CONDITION"
      and .regionRelation.caseCount == (.regionRelation.cases | length)
      and .regionRelation.caseCount > 1
      and all(.regionRelation.cases[];
        .relationallyComplete == true
        and (.guard.conditions | length) > 0
        and (.outputExpressions | length) == 1))
    and any(.[];
      .requestedOutputSlice.outputCell == $arithmetic
      and .regionRelation.caseCount == 6)
    and any(.[];
      .requestedOutputSlice.outputCell == $text
      and .regionRelation.caseCount == 2
      and ([.regionRelation.cases[].outputExpressions[]?._exp] | sort)
        == ["Y_I_5", "Y_I_9"]
      and ([.regionRelation.cases[].guard.conditions[]
        | .. | objects
        | select(._type? == "OpStrExpression"
          and ._name? == "contains")] | length) > 0)
  ' "${merged_summaries[@]}" >/dev/null \
    || die "dependent-scalar lost its arithmetic/text producer domains"
}

validate_container_producer_artifacts() {
  local work_root=$1
  local campaign_root="${work_root}/producer-campaign"
  local array_summary="${campaign_root}/arrayvalue/merged_region_summaries.jsonl"
  local map_summary="${campaign_root}/mapvalue/merged_region_summaries.jsonl"
  local -a path_closures exploration_records raw_results

  [[ -d "${campaign_root}" ]] \
    || die "container producer campaign not found: ${campaign_root}"
  mapfile -t path_closures < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name region_path_closure.json | sort)
  mapfile -t exploration_records < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name path_exploration_records.jsonl | sort)
  mapfile -t raw_results < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name raw_results.jsonl | sort)
  [[ ${#path_closures[@]} -eq 2 ]] \
    || die "containers expected two producer path closures"
  [[ ${#exploration_records[@]} -eq 2 ]] \
    || die "containers expected two producer exploration ledgers"
  [[ ${#raw_results[@]} -eq 2 ]] \
    || die "containers expected two producer raw-result ledgers"
  require_file "array guarded merge" "${array_summary}"
  require_file "map guarded merge" "${map_summary}"

  jq -e -s '
    length == 2
    and all(.[];
      .schemaVersion == 1
      and .kind == "REGION_PATH_WORKLIST"
      and .status == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .complete == true
      and .wallClockBoundReached == false
      and .gapCount == 0
      and ((.gaps // []) | length) == 0
      and .pendingTaskCount == 0
      and .observedPathCount >= 2
      and .candidateFlipCount > 0
      and ([.pathCountByRegion[]] | add) == .observedPathCount)
    and ([.[].observedPathCount] | sort) == [2, 10]
  ' "${path_closures[@]}" >/dev/null \
    || die "container producer path closure is incomplete"

  # Successful per-iteration files are intentionally transient. The retained
  # ledger records one terminal status per query; the canonical raw results
  # preserve the custom-JDK observation without duplicating replay manifests.
  jq -e -s '
    ([.[] | select(
        .status == "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY")]
      | length) == 10
    and all(.[];
      .schemaVersion == 1
      and .kind == "PATH_EXPLORATION_RECORD"
      and (.queryKey | test("^[0-9a-f]{64}$"))
      and (.status == "UNSAT"
        or (.status == "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
          and (.observedPathKey | test("^[0-9a-f]{64}$"))
          and (.summaryId | type == "string" and length > 0))))
    and ([.[].queryKey] | unique | length) == length
  ' "${exploration_records[@]}" >/dev/null \
    || die "container retained exploration ledger is incomplete"

  jq -e -s '
    ([.[] | select((.pathQueryKey // "") != "")] as $replays
      | ($replays | length) == 10
      and all($replays[];
        .branchOverrideUsed == false
        and .allModelAssignmentsApplied == true
        and .branchReplayValidation.kind == "BRANCH_REPLAY_OBSERVATION"
        and .branchReplayValidation.requested == true
        and .branchReplayValidation.valid == true)
      and ([$replays[].modelAssignmentsApplied[]?
        | select((.dynamicReplayRebindingAuthority // "") != "")]
        | length) > 0)
  ' "${raw_results[@]}" >/dev/null \
    || die "container custom-JDK replay evidence is incomplete"

  jq -e '
    .valid == true
    and .relationallyComplete == true
    and .regionRelation.kind == "GUARDED_PATH_MERGE"
    and .regionRelation.complete == true
    and .regionRelation.pathClosureStatus
      == "COMPLETE_BOUNDED_PATH_CLOSURE"
    and .regionRelation.guardSemantics
      == "EXACT_NORMALIZED_PATH_CONDITION"
    and .regionRelation.caseCount == 2
    and (.requestedOutputSlice.containerElementFieldBindings | length) == 1
    and .requestedOutputSlice.containerElementFieldBindings[0] as $static
    | ($static.schemaVersion == 2
      and $static.kind == "ARRAY_ELEMENT_FIELD"
      and $static.materializationMode == "CONTAINER_SNAPSHOT"
      and $static.selectorAuthority == "EXACT_ARRAY_INDEX"
      and $static.elementIndex == 1
      and $static.elementOccurrence == 1
      and $static.fieldPath == ["state", "guard", "enabled"]
      and $static.complete == true
      and $static.proofAuthority
        == "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_CHAIN_V1"
      and ($static.proofCausalEdgeIds | length)
        > ($static.fieldPath | length)
      and (.requestedOutputSlice.inputPorts
        | index($static.baseInputSymbol)) != null
      and (.requestedOutputSlice.inputPorts
        | index($static.containerInputPort)) != null
      and ([.regionRelation.cases[].guard.conditions[]._op] | sort)
        == ["!=", "=="]
      and ([.regionRelation.cases[].outputExpressions[]?._exp] | sort)
        == ["Y_I_-1", "Y_I_1"]
      and all(.regionRelation.cases[];
        .relationallyComplete == true
        and (.dynamicFieldBindings | length) == 1
        and .dynamicFieldBindings[0] as $dynamic
        | ($dynamic.schemaVersion == 2
          and $dynamic.kind
            == "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING"
          and $dynamic.complete == true
          and $dynamic.containerBindingId == $static.bindingId
          and $dynamic.baseInputSymbol == $static.baseInputSymbol
          and $dynamic.containerInputPort == $static.containerInputPort
          and $dynamic.selectorAuthority == "EXACT_ARRAY_INDEX"
          and $dynamic.elementIndex == 1
          and $dynamic.elementOccurrence == 1
          and $dynamic.fieldPath == $static.fieldPath
          and $dynamic.containerSelector.complete == true
          and $dynamic.containerSelector.elementIndex == 1
          and $dynamic.fieldExpression._type == "SymbolExpression"
          and $dynamic.fieldExpression._java_type == "Z"
          and ($dynamic.fieldExpression._exp
            | contains($dynamic.dynamicFieldSymbol)))))
  ' "${array_summary}" >/dev/null \
    || die "array producer lost exact index-1 nested field semantics"

  jq -e '
    .valid == true
    and .relationallyComplete == true
    and .regionRelation.kind == "GUARDED_PATH_MERGE"
    and .regionRelation.complete == true
    and .regionRelation.pathClosureStatus
      == "COMPLETE_BOUNDED_PATH_CLOSURE"
    and .regionRelation.guardSemantics
      == "EXACT_NORMALIZED_PATH_CONDITION"
    and .regionRelation.caseCount == 10
    and (.requestedOutputSlice.inputAliasCanonicalizations | length) == 2
    and all(.requestedOutputSlice.inputAliasCanonicalizations[];
      .schemaVersion == 1
      and .kind == "CANONICAL_PRIMITIVE_INPUT_ALIAS"
      and .staticAuthority
        == "PROJECTED_FRONTIER_TO_EXACT_PRIMITIVE_FIELD_V1"
      and .runtimeIdentityAuthority
        == "BASE_FIELD_VALUE_EQUALS_EXACT_LEAF_RECEIVER_V1"
      and .intermediateOwnerObjectId == .canonicalLeafReceiverObjectId
      and .aliasBindingCount == 1
      and .aliasBindingAuthorities
        == ["UNIQUE_EXACT_PROJECTED_ALIAS_CHAIN"]
      and .runtimeCutAuthority
        == "BASE_READ_BEFORE_LEAF_READ_WITH_NO_INTERVENING_LEAF_WRITE_V1"
      and .baseFieldEventSeq > 0
      and .baseFieldCallId > 0
      and .canonicalLeafFieldEventSeq > 0
      and .canonicalLeafFieldCallId > 0
      and .baseFieldEventSeq < .canonicalLeafFieldEventSeq
      and .complete == true)
    and ([.requestedOutputSlice.inputAliasCanonicalizations[]
      | .canonicalInputCell] | sort) == [
        "<edu.uva.liftlab.graphchecker.fixtures.ContainerThreeThreadRpcWorkload$MapProducer: int input1>",
        "<edu.uva.liftlab.graphchecker.fixtures.ContainerThreeThreadRpcWorkload$MapProducer: int input2>"
      ]
    and ([.requestedOutputSlice.inputBindings[].dependencyCell] | tostring
      | contains("MapProducer: int input1"))
    and ([.requestedOutputSlice.inputBindings[].dependencyCell] | tostring
      | contains("MapProducer: int input2"))
    and (any(.regionRelation.cases[].outputExpressions[]?;
      ._type == "ConstExpr" and ._exp == "Y_I_10"))
    and (any(.regionRelation.cases[].outputExpressions[]?;
      ._type == "BinaryExpression" and ._op == "+"))
    and all(.regionRelation.cases[];
      .relationallyComplete == true
      and (.dynamicFieldBindings | length) == 1
      and (.heapObservations | length) == 1
      and .dynamicFieldBindings[0] as $dynamic
      | .heapObservations[0] as $observation
      | ($dynamic.schemaVersion == 1
        and $dynamic.kind == "DYNAMIC_MAP_ENTRY_FIELD_BINDING"
        and $dynamic.complete == true
        and $dynamic.fieldPath == ["state", "guard", "enabled"]
        and $dynamic.keyExpression._type == "ConstExpr"
        and $dynamic.keyExpression._java_type == "I"
        and $dynamic.keyExpression._exp == "Y_I_7"
        and $dynamic.entryValueRefWitnessJoinCertified == true
        and $observation.schemaVersion == 1
        and $observation.kind == "MAP_ENTRY_READ"
        and $observation.complete == true
        and $observation.stateBaseComplete == true
        and $observation.stateBindingAuthority
          == "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1"
        and $observation.entryValueFieldBindingComplete == true
        and ($observation.entryFieldBindings | length) == 1
        and $observation.entryFieldBindings[0].dynamicBindingId
          == $dynamic.dynamicBindingId
        and $observation.entryFieldBindings[0].fieldPath
          == $dynamic.fieldPath
        and $observation.entryFieldBindings[0].keyExpression
          == $dynamic.keyExpression))
  ' "${map_summary}" >/dev/null \
    || die "map producer lost exact key-7 nested entry field semantics"

}

validate_unreachable_parity_producer_artifacts() {
  local work_root=$1
  local campaign_root="${work_root}/producer-campaign"
  local -a path_closures merged_summaries

  [[ -d "${campaign_root}" ]] \
    || die "unreachable-parity producer campaign not found: ${campaign_root}"
  mapfile -t path_closures < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name region_path_closure.json | sort)
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)
  [[ ${#path_closures[@]} -eq 2 ]] \
    || die "unreachable-parity expected two producer path closures"
  [[ ${#merged_summaries[@]} -eq 2 ]] \
    || die "unreachable-parity expected two producer guarded merges"

  jq -e -s '
    length == 2
    and all(.[];
      .schemaVersion == 1
      and .kind == "REGION_PATH_WORKLIST"
      and .status == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .complete == true
      and .wallClockBoundReached == false
      and .gapCount == 0
      and ((.gaps // []) | length) == 0
      and .pendingTaskCount == 0
      and .observedPathCount == 2
      and .candidateFlipCount > 0
      and ([.pathCountByRegion[]] | add) == 2)
  ' "${path_closures[@]}" >/dev/null \
    || die "unreachable-parity producer path closure is incomplete"

  jq -e -s '
    length == 2
    and all(.[];
      .valid == true
      and .relationallyComplete == true
      and .regionRelation.kind == "GUARDED_PATH_MERGE"
      and .regionRelation.complete == true
      and .regionRelation.pathClosureStatus
        == "COMPLETE_BOUNDED_PATH_CLOSURE"
      and .regionRelation.guardSemantics
        == "EXACT_NORMALIZED_PATH_CONDITION"
      and .regionRelation.caseCount == 2
      and all(.regionRelation.cases[];
        .relationallyComplete == true
        and (.guard.conditions | length) > 0))
    # The complete producer image is {-1, 3} union {0, 4}.  No target-side
    # constant says UNSAT; equality becomes impossible only after both
    # guarded relations are composed.
    and ([.[] | .regionRelation.cases[].outputExpressions[]?._exp]
      | sort) == ["Y_I_-1", "Y_I_0", "Y_I_3", "Y_I_4"]
    and ([.[]
      | .requestedOutputSlice.containerElementFieldBindings[]?
      | select(.kind == "ARRAY_ELEMENT_FIELD"
        and .selectorAuthority == "EXACT_ARRAY_INDEX"
        and .elementIndex == 1
        and .fieldPath == ["state", "guard", "enabled"]
        and .complete == true)] | length) == 1
    and ([.[] | .regionRelation.cases[].dynamicFieldBindings[]?
      | select(.kind == "DYNAMIC_MAP_ENTRY_FIELD_BINDING"
        and .keyExpression._java_type == "I"
        and .keyExpression._exp == "Y_I_7"
        and .fieldPath == ["state", "guard", "enabled"]
        and .complete == true)] | length) == 2
  ' "${merged_summaries[@]}" >/dev/null \
    || die "unreachable-parity lost its exact odd/even container relations"
}

validate_semantic_profile() {
  local label=$1
  local smt=$2
  local reach_report=$3
  local work_root=$4
  case "${label}" in
    baseline)
      jq -e '
        .rootBooleanInputCount == 2
        and .existentialNonBooleanRootInputCount == 1
        and .valuationCount == 4
        and .satisfyingValuationCount == 2
        and .unsatisfyingValuationCount == 2
        and ([.truthTable[] | select(.reachesBug) | .valuationKey]
          == ["00", "10"])
        and (.existentialNonBooleanRootInputs[0].javaTypeDescriptor == "I")
        and (.existentialNonBooleanRootInputs[0].cell
          | contains("ThreeThreadRpcWorkload$ProducerBThread: int var"))
      ' "${reach_report}" >/dev/null \
        || die "baseline lost its Boolean/int overflow reach profile"
      grep -Fq '(define-fun java_int_wrap' "${smt}" \
        || die "baseline SMT has no Java int wrap semantics"
      grep -Eq '\(java_int_wrap \(\+ 10 [^)]+\)\)' "${smt}" \
        || die "baseline SMT omitted wrapped 10 + var"
      ;;
    cross-method-fields)
      jq -e '
        .rootBooleanInputCount == 2
        and .existentialNonBooleanRootInputCount == 4
        and .valuationCount == 4
        and .satisfyingValuationCount == 1
        and .unsatisfyingValuationCount == 3
        and ([.truthTable[] | select(.reachesBug) | .valuationKey]
          == ["10"])
        and ([.existentialNonBooleanRootInputs[].javaTypeDescriptor]
          | sort) == ["I", "I", "I", "Ljava/lang/String;"]
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("baseInput"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("instanceWeight"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("processWeight"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("routeInput"))
        and (all(.existentialNonBooleanRootInputs[];
          (.cell | contains("boundedWeight.return") | not)
          and (.cell | contains("ThirdHop.return") | not)
          and (.cell | contains("thirdHop.return") | not)))
      ' "${reach_report}" >/dev/null \
        || die "cross-method-fields lost an external root or exact truth row"
      grep -Fq 'str.contains' "${smt}" \
        || die "cross-method-fields SMT omitted String.contains"
      grep -Fq '"ready"' "${smt}" \
        || die "cross-method-fields SMT omitted the ready needle"
      ;;
    multitype)
      jq -e '
        .rootBooleanInputCount == 2
        and .existentialNonBooleanRootInputCount == 4
        and .valuationCount == 4
        and .satisfyingValuationCount == 2
        and .unsatisfyingValuationCount == 2
        and ([.truthTable[] | select(.reachesBug) | .valuationKey]
          == ["10", "11"])
        and ([.existentialNonBooleanRootInputs[].javaTypeDescriptor]
          | sort) == ["D", "I", "J", "Ljava/lang/String;"]
      ' "${reach_report}" >/dev/null \
        || die "multitype lost its Boolean/I/J/D/String reach profile"
      grep -Fq 'str.contains' "${smt}" \
        || die "multitype SMT omitted String.contains"
      grep -Fq '"needle"' "${smt}" \
        || die "multitype SMT omitted the needle literal"
      grep -Fq '#x3ff8000000000000' "${smt}" \
        || die "multitype SMT omitted the exact double 1.5 value"
      grep -Fq 'fp.isNaN' "${smt}" \
        || die "multitype SMT omitted Java dcmpl NaN semantics"
      grep -Fq 'fp.lt' "${smt}" \
        || die "multitype SMT omitted Java dcmpl less-than semantics"
      grep -Fq 'fp.gt' "${smt}" \
        || die "multitype SMT omitted Java dcmpl greater-than semantics"
      validate_multitype_producer_artifacts "${work_root}"
      ;;
    dependent-scalar)
      jq -e '
        .status == "COMPLETE_CANDIDATE_MODEL"
        and .reachabilityStatus == "REACHABLE"
        and .candidateModelAvailable == true
        and .rootBooleanInputCount == 1
        and .existentialNonBooleanRootInputCount == 2
        and .valuationCount == 2
        and .satisfyingValuationCount == 1
        and .unsatisfyingValuationCount == 1
        and ([.truthTable[] | select(.reachesBug) | .valuationKey]
          == ["1"])
        and ([.truthTable[]
          | select((.valuationKey == "1" and .solverStatus == "sat")
            or (.valuationKey == "0" and .solverStatus == "unsat"))]
          | length) == 2
        and ([.existentialNonBooleanRootInputs[].javaTypeDescriptor]
          | sort) == ["I", "Ljava/lang/String;"]
        and .nullableJavaStringModeled == true
        and .nullableJavaStringInputCount == 1
        and ([.rootBooleanInputs[].cell] | tostring
          | contains("<java.lang.Boolean: boolean booleanValue()>.return"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("DependentScalarThreeThreadWorkload$ArithmeticThread: int input"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("DependentScalarThreeThreadWorkload$TextThread: java.lang.String text"))
        and ([.rootBooleanInputs[],
          .existentialNonBooleanRootInputs[]] | map(.regionId)
          | unique | length) == 2
        and .rootBooleanInputs[0].regionId
          == ([.existentialNonBooleanRootInputs[]
            | select(.javaTypeDescriptor == "I")][0].regionId)
      ' "${reach_report}" >/dev/null \
        || die "dependent-scalar lost its exact existential reach profile"
      jq -e '
        .fatalSite
          | startswith("<edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload$ConsumerThread: void executeWorker()>#")
      ' "${work_root}/candidate/candidate_composition_manifest.json" >/dev/null \
        || die "dependent-scalar composition moved away from the annotated target"
      jq -e '
        . as $root
        | .resolvedProducerCount == 2
        and .resolvedDemandedOutputCount == 2
        and .includedBoundedRelationCount == 2
        and .guardedRegionRelationCount == 2
        and .guardedPathCaseCount == 8
        and .caseProjectionCatalogComplete == true
        and .caseProjectionCatalogCount == 8
        and ([.resolvedEdgeBindings[].binding.fromOutputCell] | sort)
          == [
            "<edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload$RpcBus: int arithmeticValue>",
            "<edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload$RpcBus: int textValue>"
          ]
        and all(.resolvedEdgeBindings[];
          .targetRegion == .binding.toRegion
          and .targetRegion == $root.fatalRegion
          and .targetRegionInstance == $root.fatalRegionInstanceId
          and .binding.fromOutputCell == .binding.toInputCell
          and .selectionAuthority == "RUNTIME_CONFIRMED_READ_FROM"
          and .binding.objectIdentityConfirmed == true
          and .binding.orderConfirmed == true)
      ' "${work_root}/candidate/candidate_composition_manifest.json" >/dev/null \
        || die "dependent-scalar lost either producer relation"
      grep -Fq 'str.contains' "${smt}" \
        || die "dependent-scalar SMT omitted String.contains"
      grep -Fq '"ready"' "${smt}" \
        || die "dependent-scalar SMT omitted the ready needle"
      grep -Fq '(define-fun java_int_wrap' "${smt}" \
        || die "dependent-scalar SMT omitted Java int arithmetic semantics"
      validate_dependent_scalar_artifacts "${work_root}"
      ;;
    containers)
      jq -e '
        .rootBooleanInputCount == 2
        and .existentialNonBooleanRootInputCount == 2
        and ([.existentialNonBooleanRootInputs[].javaTypeDescriptor]
          | sort) == ["I", "I"]
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("MapProducer: int input1"))
        and ([.existentialNonBooleanRootInputs[].cell] | tostring
          | contains("MapProducer: int input2"))
        and .valuationCount == 4
        and .satisfyingValuationCount == 4
        and .unsatisfyingValuationCount == 0
        and all(.truthTable[];
          .solverStatus == "sat" and .reachesBug == true)
      ' "${reach_report}" >/dev/null \
        || die "containers lost its Boolean/int existential reach profile"
      jq -e '
        .resolvedProducerCount == 2
        and .guardedRegionRelationCount == 2
        and .guardedPathCaseCount == 12
        and .caseProjectionCatalogComplete == true
        and .caseProjectionCatalogCount == 12
        and .heapObservationCount == 10
        and .heapObservationFieldBindingCount == 10
      ' "${work_root}/candidate/candidate_composition_manifest.json" >/dev/null \
        || die "containers lost guarded array/map composition evidence"
      grep -Fq '(define-fun java_int_wrap' "${smt}" \
        || die "containers SMT omitted Java int wrap semantics"
      validate_container_producer_artifacts "${work_root}"
      ;;
    unreachable-parity)
      jq -e '
        .status == "COMPLETE_CANDIDATE_UNREACHABLE"
        and .reachabilityStatus == "UNREACHABLE"
        and .candidateModelAvailable == false
        and .rootBooleanInputCount == 2
        and .existentialNonBooleanRootInputCount == 0
        and .valuationCount == 4
        and .satisfyingValuationCount == 0
        and .unsatisfyingValuationCount == 4
        and .reachConditionSmtLib == "false"
        and all(.truthTable[]; .reachesBug == false)
      ' "${reach_report}" >/dev/null \
        || die "unreachable-parity was not proved unreachable for all roots"
      jq -e '
        .resolvedProducerCount == 2
        and .guardedRegionRelationCount == 2
        and .guardedPathCaseCount == 4
        and .caseProjectionCatalogComplete == true
        and .caseProjectionCatalogCount == 4
        and .heapObservationCount == 2
        and .heapObservationFieldBindingCount == 2
      ' "${work_root}/candidate/candidate_composition_manifest.json" >/dev/null \
        || die "unreachable-parity lost guarded container composition evidence"
      validate_unreachable_parity_producer_artifacts "${work_root}"
      ;;
    *) die "no semantic profile for matrix label: ${label}" ;;
  esac
}

validate_candidate_outputs() {
  local label=$1
  local work_root=$2
  local z3=$3
  local candidate_root="${work_root}/candidate"
  local smt="${candidate_root}/candidate.smt2"
  local composition="${candidate_root}/candidate_composition_manifest.json"
  local reach_report="${candidate_root}/candidate_boolean_model.json"
  local relationships="${candidate_root}/symbolic_relationship_candidates.json"
  local candidate_manifest="${candidate_root}/candidate_result_manifest.json"
  local reachability solver_output solver_status expected_status

  require_file "candidate SMT" "${smt}"
  [[ -s "${smt}" ]] || die "candidate SMT is empty: ${smt}"
  grep -Eq '^[[:space:]]*\(check-sat\)' "${smt}" \
    || die "candidate SMT has no check-sat command: ${smt}"
  validate_json_object "candidate composition manifest" "${composition}"
  validate_json_object "candidate reach model" "${reach_report}"
  validate_json_object "candidate result manifest" "${candidate_manifest}"
  validate_json_object "candidate relationships" "${relationships}"
  validate_composition_common "${composition}"

  jq -e '
    .compositionStage == "CANDIDATE"
    and .boundedComposition == true
    and .structurallyComplete == true
    and .eligibleForCandidateModel == true
    and .fatalReplayValidated == false
    and .complete == false
    and .eligibleToReportAutomaticRelationship == false
    and .caseProjectionCatalogComplete == true
  ' "${composition}" >/dev/null \
    || die "candidate composition escaped CANDIDATE trust state"
  jq -e '
    .schemaVersion == 1
    and .kind == "BOOLEAN_REACH_CONDITION_REPORT"
    and .complete == true
    and .extractionMode == "CANDIDATE_MODEL"
    and .candidateOnly == true
    and ((.status == "COMPLETE_CANDIDATE_MODEL"
        and .reachabilityStatus == "REACHABLE"
        and .candidateModelAvailable == true)
      or (.status == "COMPLETE_CANDIDATE_UNREACHABLE"
        and .reachabilityStatus == "UNREACHABLE"
        and .candidateModelAvailable == false))
    and .reportableFinalReachCondition == false
    and .fatalReplayValidated == false
    and .truthTableComplete == true
    and .exactFiniteProjection == true
    and .solverErrorCount == 0
    and ((.discoveryGaps // []) | length) == 0
    and (.satisfyingValuationCount + .unsatisfyingValuationCount
      == .valuationCount)
    and .rootBooleanInputCount == ((.rootBooleanInputs // []) | length)
    and (.existentialNonBooleanRootInputCount // 0)
      == ((.existentialNonBooleanRootInputs // []) | length)
  ' "${reach_report}" >/dev/null \
    || die "candidate Boolean reach model is incomplete"
  jq -e '
    .schemaVersion == 1
    and .kind == "CONCOLIC_CANDIDATE_RESULT"
    and .status == "COMPLETE_Z3_CHECKED_CANDIDATE"
    and .complete == true
    and .trustState == "CANDIDATE_ONLY"
    and .z3Checked == true
    and .naturalReplayPromotionImplemented == false
  ' "${candidate_manifest}" >/dev/null \
    || die "candidate result incorrectly claims trusted promotion"
  jq -e '
    .schemaVersion == 1
    and .kind == "SYMBOLIC_RELATIONSHIP_CANDIDATES"
    and .eligibleForAutomaticVerification == false
    and (.relationships | type == "array")
    and (keys | sort) == (["eligibleForAutomaticVerification", "kind",
      "relationships", "schemaVersion"] | sort)
  ' "${relationships}" >/dev/null \
    || die "candidate relationships claim final eligibility"

  validate_artifact_binding "${candidate_manifest}" \
    candidateSmtArtifact "${smt}"
  validate_artifact_binding "${candidate_manifest}" \
    compositionManifestArtifact "${composition}"
  validate_artifact_binding "${candidate_manifest}" \
    candidateReachModelArtifact "${reach_report}"
  validate_artifact_binding "${candidate_manifest}" \
    relationshipCandidatesArtifact "${relationships}"

  reachability=$(jq -er '
    .reachabilityStatus
    | select(. == "REACHABLE" or . == "UNREACHABLE")
  ' "${reach_report}") \
    || die "candidate reach model has no reachability status"
  expected_status=$([[ "${reachability}" == "REACHABLE" ]] \
    && printf sat || printf unsat)
  solver_output=$("${z3}" "${smt}") \
    || die "z3 failed for ${label} candidate"
  printf '%s\n' "${solver_output}" | grep -Fq '(error' \
    && die "z3 reported an SMT error for ${label} candidate"
  solver_status=$(awk 'NF { print $1; exit }' <<< "${solver_output}")
  [[ "${solver_status}" == "${expected_status}" ]] \
    || die "${label} candidate expected z3 ${expected_status}, got ${solver_status}"
  validate_semantic_profile "${label}" "${smt}" "${reach_report}" \
    "${work_root}"
  echo "[three-thread-rpc-matrix] ${label}: candidate ${reachability}, z3=${solver_status}"
}

run_case() {
  local label=$1
  local relative_config=$2
  local config="${fixture_dir}/${relative_config}"
  local normalized analysis_dir work_root configured_z3 z3

  require_file "${label} workflow configuration" "${config}"
  normalized=$("${engine_runner}" --config "${config}" config)
  analysis_dir=$(configured_value "${normalized}" causynth_output_dir)
  work_root=$(dirname "${analysis_dir}")
  configured_z3=$(configured_value "${normalized}" z3_bin)
  z3=$(resolve_executable "${configured_z3}")

  echo "[three-thread-rpc-matrix] ${label}: clean"
  CAUSYNTH_WORKFLOW_CONFIG="${config}" "${fixture_runner}" clean
  echo "[three-thread-rpc-matrix] ${label}: candidate"
  CAUSYNTH_WORKFLOW_CONFIG="${config}" "${fixture_runner}" candidate
  validate_candidate_outputs "${label}" "${work_root}" "${z3}"
}

mode=${1:-core}
[[ $# -le 1 ]] || die "expected at most one mode argument"
case "${mode}" in
  core|all|baseline|cross-method-fields|multitype|dependent-scalar|containers|unreachable-parity) ;;
  help|-h|--help) usage; exit 0 ;;
  *) usage >&2; die "unknown matrix mode: ${mode}" ;;
esac

require_command awk
require_command find
require_command grep
require_command jq
require_command realpath
require_command sha256sum
require_command stat
[[ -x "${fixture_runner}" ]] \
  || die "fixture runner is not executable: ${fixture_runner}"
[[ -x "${engine_runner}" ]] \
  || die "engine runner is not executable: ${engine_runner}"

case "${mode}" in
  core)
    labels=(baseline cross-method-fields multitype)
    configs=(workflow.properties cross-method-fields/workflow.properties \
      multitype/workflow.properties)
    ;;
  all)
    labels=(baseline cross-method-fields multitype dependent-scalar containers \
      unreachable-parity)
    configs=(workflow.properties cross-method-fields/workflow.properties \
      multitype/workflow.properties dependent-scalar/workflow.properties \
      containers/workflow.properties unreachable-parity/workflow.properties)
    ;;
  baseline)
    labels=(baseline)
    configs=(workflow.properties)
    ;;
  cross-method-fields)
    labels=(cross-method-fields)
    configs=(cross-method-fields/workflow.properties)
    ;;
  multitype)
    labels=(multitype)
    configs=(multitype/workflow.properties)
    ;;
  dependent-scalar)
    labels=(dependent-scalar)
    configs=(dependent-scalar/workflow.properties)
    ;;
  containers)
    labels=(containers)
    configs=(containers/workflow.properties)
    ;;
  unreachable-parity)
    labels=(unreachable-parity)
    configs=(unreachable-parity/workflow.properties)
    ;;
esac

for matrix_position in "${!labels[@]}"; do
  run_case "${labels[${matrix_position}]}" \
    "${configs[${matrix_position}]}"
done

echo "[three-thread-rpc-matrix] validated ${#labels[@]} workflows"
