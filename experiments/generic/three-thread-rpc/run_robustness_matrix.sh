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
  all   Also run dependent-scalar, containers, and all UNSAT workloads.
  baseline | cross-method-fields | multitype | dependent-scalar | containers |
  unreachable-parity | unreachable-correlated-fields |
  unreachable-nested-object | unreachable-inherited-alias |
  unreachable-mutated-object | unreachable-long-fields |
  compound-target | unreachable-compound-target | container-tricky |
  tricky-nested-array-map-key | tricky-divergent-object-fields |
  tricky-array-element-frame | tricky-map-key-value |
  tricky-compound-container-guard
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
  local declared_path declared_hash
  local expected_path actual_hash
  declared_path=$(jq -er --arg field "${field}" '
    .[$field].path | select(type == "string" and length > 0)
  ' "${manifest}") \
    || die "${manifest} has no ${field}.path"
  declared_hash=$(jq -er --arg field "${field}" '
    .[$field].sha256
    | select(type == "string" and test("^[0-9a-f]{64}$"))
  ' "${manifest}") \
    || die "${manifest} has no valid ${field}.sha256"
  require_file "${field} artifact" "${expected}"
  expected_path=$(realpath -m -- "${expected}")
  [[ "$(realpath -m -- "${declared_path}")" == "${expected_path}" ]] \
    || die "${field} path does not bind ${expected_path}"
  actual_hash=$(sha256_file "${expected}")
  [[ "${actual_hash}" == "${declared_hash}" ]] \
    || die "${field} hash does not match ${expected}"
}

output_closure_helpers='
def region_goals:
  .[] as $plan
  | $plan.closureGoals[]
  | . + {
      regionId: $plan.regionId,
      regionInstanceId: $plan.regionInstanceId
    };
def output_members:
  if has("outputClosure") then
    if (.outputClosure | type) == "object"
      and .outputClosure.schemaVersion == 2
      and .outputClosure.kind == "OUTPUT_CLOSURE_CONTRACT"
      and (.outputClosure.members | type) == "array"
      and (.outputClosure.members | length) > 0
      and all(.outputClosure.members[];
        (type == "object")
        and (.output | type) == "object"
        and (.slice | type) == "object")
    then .outputClosure.members
    else error("malformed explicit outputClosure")
    end
  else error("missing output closure")
  end;
def read_from_evidence:
  (.evidenceKind == "FIELD_ASSIGNMENT_READ_FROM_V1"
    or .evidenceKind == "CONTAINER_MUTATION_READ_FROM_V1")
  and (.writerEventSeq | type) == "number"
  and (.readerEventSeq | type) == "number"
  and .writerEventSeq < .readerEventSeq
  and (.receiverObjectId | type) == "number"
  and .receiverObjectId != 0;
'

validate_composition_common() {
  local manifest=$1
  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_COMPOSED_SMT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.gaps | type == "array" and length == 0)
    and ((.resolvedEdgeBindings // []) | length) > 0
    and ((.suppliedInputs // []) | type) == "array"
  ' "${manifest}" >/dev/null \
    || die "composition manifest is incomplete: ${manifest}"
}

validate_producer_contracts() {
  local label=$1
  local work_root=$2
  local composition="${work_root}/candidate/candidate_composition_manifest.json"
  local summary closure declared_hash actual_hash
  local -a summaries

  mapfile -t summaries < <(jq -er '
    .summaryInputArtifacts[]
    | [.path, .sha256]
    | @tsv
  ' "${composition}")
  [[ ${#summaries[@]} -gt 0 ]] \
    || die "${label} composition references no producer summaries"

  for entry in "${summaries[@]}"; do
    IFS=$'\t' read -r summary declared_hash <<< "${entry}"
    require_file "${label} producer summary" "${summary}"
    actual_hash=$(sha256_file "${summary}")
    [[ "${actual_hash}" == "${declared_hash}" ]] \
      || die "${label} producer summary hash mismatch: ${summary}"
    closure="$(dirname "${summary}")/region_path_closure.json"
    require_file "${label} producer closure" "${closure}"
    jq -e '
      .schemaVersion == 1
      and .kind == "REGION_PATH_WORKLIST"
      and .state == "CLOSED"
      and (.gaps | length) == 0
      and .outputClosure.schemaVersion == 2
      and .outputClosure.kind == "OUTPUT_CLOSURE_CONTRACT"
    ' "${closure}" >/dev/null \
      || die "${label} producer closure is incomplete: ${closure}"
    jq -e '
      .relationallyComplete == true
      and .regionRelation.kind == "GUARDED_PATH_MERGE"
      and (.outputClosure.members | length) > 0
      and (.outputClosure.members | map(.output.portId) | sort) as $ports
      | (.regionRelation.cases | length) > 0
        and all(.regionRelation.cases[];
          (.outputExpressions | keys | sort) == $ports)
    ' "${summary}" >/dev/null \
      || die "${label} producer relation is incomplete: ${summary}"
  done
}

validate_cross_method_joint_output_artifacts() {
  local work_root=$1
  local smt=$2
  local region_plan="${work_root}/runtime/concolic_region_plan.jsonl"
  local merged="${work_root}/producer-campaign/a/merged_region_summaries.jsonl"
  local producer_cell='<edu.uva.liftlab.graphchecker.fixtures.CrossMethodExternalFieldThreeThreadWorkload$RpcBus: int a>'
  local witness_cell='<edu.uva.liftlab.graphchecker.fixtures.CrossMethodExternalFieldThreeThreadWorkload$RpcBus: int aWitness>'

  require_file "cross-method region plan" "${region_plan}"
  require_file "cross-method Producer A merged relation" "${merged}"

  jq -e -s --arg producer "${producer_cell}" --arg witness "${witness_cell}" \
    "${output_closure_helpers}"'
    [region_goals | select(
      .kind == "OUTPUT_RELATION_CLOSURE"
      and ([.outputClosure.members[].output.cell] | sort)
        == ([$producer, $witness] | sort))] as $joint
    | ($joint | length) == 1
    and ($joint[0].outputClosure.members | length) == 2
    and ([$joint[0].edgeBindings[]
      | select(read_from_evidence
        and (.fromOutputCell == $producer
          or .fromOutputCell == $witness))] as $edges
      | ($edges | length) == 2
      and ([$edges[].fromOutputCell] | sort)
        == ([$producer, $witness] | sort)
      and ([$edges[].toRegionInstance] | unique | length) == 1)
  ' "${region_plan}" >/dev/null \
    || die "cross-method Producer A is not one two-output runtime demand"

  jq -e --arg producer "${producer_cell}" --arg witness "${witness_cell}" '
    . as $summary
    | ($summary.outputClosure.members
      | map(.output.portId) | sort) as $ports
    | ([ $summary.outputClosure.members[].output.cell ] | sort)
        == ([$producer, $witness] | sort)
      and all($summary.regionRelation.cases[];
        (.outputExpressions | keys | sort) == $ports)
  ' "${merged}" >/dev/null \
    || die "cross-method merged cases do not carry both Producer A outputs"

  grep -Fq 'region_case_selector_partition_' "${smt}" \
    || die "cross-method joint relation has no case partition"
}

validate_multitype_producer_artifacts() {
  local work_root=$1
  local campaign_root="${work_root}/producer-campaign"
  local -a merged_summaries

  [[ -d "${campaign_root}" ]] \
    || die "multitype producer campaign not found: ${campaign_root}"
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)

  jq -e -s '
    # Java double comparison is captured as dcmpl, long comparison as lcmp,
    # and String.contains remains a first-class string AST node.
    ([.[] | .regionRelation.cases[].guard.conditions[]
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
  local region_plan="${work_root}/runtime/concolic_region_plan.jsonl"
  local campaign_root="${work_root}/producer-campaign"
  local fixture_class="edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload"
  local target_method="<${fixture_class}\$ConsumerThread: void executeWorker()>"
  local target_exception="${fixture_class}\$DependentScalarBugReachedException"
  local arithmetic_cell="<${fixture_class}\$RpcBus: int arithmeticValue>"
  local text_cell="<${fixture_class}\$RpcBus: int textValue>"
  local -a merged_summaries

  require_file "dependent-scalar annotation target" "${target_resolution}"
  require_file "dependent-scalar region plan" "${region_plan}"
  [[ -d "${campaign_root}" ]] \
    || die "dependent-scalar producer campaign not found: ${campaign_root}"

  # The target is the one class-file annotation, not a rediscovered exception
  # type or a fixture-provided branch formula.  Bytecode offsets and source
  # lines are deliberately excluded because they are not semantic identity.
  jq -e --arg method "${target_method}" \
    --arg exception "${target_exception}" '
    .schemaVersion == 2
    and .kind == "TARGET_ATTESTATION"
    and .targetId == "dependent-scalar"
    and .method == $method
    and .exception == $exception
    and .constructionOrdinal == 0
  ' "${target_resolution}" >/dev/null \
    || die "dependent-scalar lost its exact annotated target root"

  # Runtime discovery must expose both scalar publishers as distinct producer
  # roots converging on one TARGET_BRANCH instance.  Region numbers and event
  # sequence values are intentionally not pinned.
  jq -e -s --arg arithmetic "${arithmetic_cell}" \
    --arg text "${text_cell}" "${output_closure_helpers}"'
    [region_goals | select(
      .kind == "OUTPUT_RELATION_CLOSURE"
      and .admission.state == "READY")
      | select(
        ([output_members | .[].output.cell] | index($arithmetic)) != null
        or ([output_members | .[].output.cell] | index($text)) != null)
    ] as $producers
    | ([$producers[].edgeBindings[]?
        | select(read_from_evidence
          and .fromOutputCell == .toInputCell)] as $edges
      | ($producers | length) == 2
      and all($producers[]; (output_members | length) == 1)
      and ([$producers[] | output_members | .[].output.cell] | sort)
        == ([$arithmetic, $text] | sort)
      and ([$producers[].regionId] | unique | length) == 2
      and ($edges | length) == 2
      and ([$edges[].fromOutputCell] | sort)
        == ([$arithmetic, $text] | sort)
      and ([$edges[].toRegionInstance] | unique | length) == 1
      and all($edges[];
        .fromRegion != .toRegion)
      and ([region_goals | select(
          .kind == "TARGET_REACH_CLOSURE"
          and (.admission.state == "READY"
            or .admission.state == "DISCOVERED")
          and .regionId == $edges[0].toRegion
          and .regionInstanceId == $edges[0].toRegionInstance)]
        | length) == 1)
  ' "${region_plan}" >/dev/null \
    || die "dependent-scalar runtime roots are not two exact producers and one target"

  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)

  # Preserve the source-level output domains without pinning the number of
  # internal producer relations or path partitions.
  jq -e -s --arg arithmetic "${arithmetic_cell}" \
    --arg text "${text_cell}" "${output_closure_helpers}"'
    [.[] | select(any(output_members[];
      .slice.outputCell == $arithmetic
      or .slice.outputCell == $text))] as $terminal
    | ($terminal | length) == 2
    and ([ $terminal[] | output_members[].slice.outputCell ] | sort)
      == ([$arithmetic, $text] | sort)
    and any($terminal[];
      any(output_members[]; .slice.outputCell == $arithmetic)
      and any(.regionRelation.cases[].outputExpressions[]?;
        ._type == "BinaryExpression"))
    and any($terminal[];
      any(output_members[]; .slice.outputCell == $text)
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
  local -a exploration_records

  [[ -d "${campaign_root}" ]] \
    || die "container producer campaign not found: ${campaign_root}"
  mapfile -t exploration_records < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name path_exploration_records.jsonl | sort)
  [[ ${#exploration_records[@]} -gt 0 ]] \
    || die "containers produced no exploration ledger"
  require_file "array guarded merge" "${array_summary}"
  require_file "map guarded merge" "${map_summary}"

  # Successful per-iteration files are intentionally transient. The retained
  # ledger is the canonical terminal status for each query.
  jq -e -s '
    all(.[];
      .schemaVersion == 1
      and .kind == "PATH_EXPLORATION_RECORD"
      and (.queryKey | test("^[0-9a-f]{64}$"))
      and (.status == "UNSAT"
        or (.status == "VALIDATED_FRESH_OUTPUT_PATH_FLIP_REPLAY"
          and (.regionId | type == "string" and length > 0)
          and (.taskId | type == "string" and length > 0)
          and (.regionInstanceId | type == "string" and length > 0)
          and (.goalId | type == "string" and length > 0))))
    and ([.[].queryKey] | unique | length) == length
  ' "${exploration_records[@]}" >/dev/null \
    || die "container retained exploration ledger is incomplete"

  jq -e "${output_closure_helpers}"'
    .relationallyComplete == true
    and .regionRelation.kind == "GUARDED_PATH_MERGE"
    and ([.regionRelation.cases[].outputExpressions[]?._exp] | sort)
      == ["Y_I_-1", "Y_I_1"]
    and all(.regionRelation.cases[];
      any(.. | objects;
        ._type? == "ContainerRelation"
        and (.operation == "STATE" or .operation == "READ")))
  ' "${array_summary}" >/dev/null \
    || die "array producer lost canonical container relation"

  jq -e "${output_closure_helpers}"'
    .relationallyComplete == true
    and .regionRelation.kind == "GUARDED_PATH_MERGE"
    and (any(.regionRelation.cases[].outputExpressions[]?;
      ._type == "ConstExpr" and ._exp == "Y_I_10"))
    and (any(.regionRelation.cases[].outputExpressions[]?;
      ._type == "BinaryExpression"))
  ' "${map_summary}" >/dev/null \
    || die "map producer lost its complete output relation"

}

validate_unreachable_parity_producer_artifacts() {
  local work_root=$1
  local campaign_root="${work_root}/producer-campaign"
  local fixture_class="edu.uva.liftlab.graphchecker.fixtures.UnreachableParityContainerThreeThreadWorkload"
  local odd_cell="<${fixture_class}\$RpcBus: int odd>"
  local even_cell="<${fixture_class}\$RpcBus: int even>"
  local -a merged_summaries

  [[ -d "${campaign_root}" ]] \
    || die "unreachable-parity producer campaign not found: ${campaign_root}"
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)

  jq -e -s --arg odd "${odd_cell}" --arg even "${even_cell}" \
    "${output_closure_helpers}"'
    [.[] | select(any(output_members[];
      .slice.outputCell == $odd or .slice.outputCell == $even))] as $terminal
    | ($terminal | length) == 2
    and ([$terminal[] | output_members[].slice.outputCell] | sort)
      == ([$odd, $even] | sort)
    # The two complete producer images remain disjoint by parity.  No
    # target-side constant says UNSAT; composition must prove the mismatch.
    and ([$terminal[] | .regionRelation.cases[]
      .outputExpressions[]?._exp]
      | unique | sort)
        == ["Y_I_-1", "Y_I_0", "Y_I_1", "Y_I_2", "Y_I_3", "Y_I_4"]
  ' "${merged_summaries[@]}" >/dev/null \
    || die "unreachable-parity lost complete producer relations"
}

validate_two_boolean_unsat_report() {
  local label=$1
  local reach_report=$2
  local descriptor=$3
  local root_mode=${4:-present}

  jq -e --arg descriptor "${descriptor}" --arg rootMode "${root_mode}" '
    .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and .reachCondition.reachability == "UNREACHABLE"
    and (.roots.booleanInputs | length) == 2
    and all(.roots.booleanInputs[]; .javaTypeDescriptor == "Z")
    and (if $rootMode == "none"
      then (.roots.existentialInputs | length) == 0
      else (.roots.existentialInputs | length) > 0
        and all(.roots.existentialInputs[];
          .javaTypeDescriptor == $descriptor)
      end)
    and (.valuations | length) == 4
    and all(.valuations[];
      .status == "unsat")
    and .reachCondition.formula == "false"
  ' "${reach_report}" >/dev/null \
    || die "${label} was not proved unreachable for all Boolean roots"
}

validate_scalar_unsat_producer_artifacts() {
  local label=$1
  local work_root=$2
  local campaign_root="${work_root}/producer-campaign"
  local region_plan="${work_root}/runtime/concolic_region_plan.jsonl"
  local composition="${work_root}/candidate/candidate_composition_manifest.json"
  local -a merged_summaries

  [[ -d "${campaign_root}" ]] \
    || die "${label} producer campaign not found: ${campaign_root}"
  require_file "${label} activation plan" "${region_plan}"
  require_file "${label} composition manifest" "${composition}"
  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)

  jq -e -s "${output_closure_helpers}"'
    length > 0
    and all(.[];
      .relationallyComplete == true
      and .regionRelation.kind == "GUARDED_PATH_MERGE"
      and (output_members | map(.output.portId) | sort) as $ports
      | all(.regionRelation.cases[];
          (.outputExpressions | keys | sort) == $ports))
  ' "${merged_summaries[@]}" >/dev/null \
    || die "${label} producer relations are not complete guarded merges"

  jq -e '
    (.resolvedEdgeBindings | length) > 0
    and ([.resolvedEdgeBindings[]] | unique | length)
      == (.resolvedEdgeBindings | length)
    and all(.resolvedEdgeBindings[];
      type == "string" and length > 0)
  ' "${composition}" >/dev/null \
    || die "${label} lost its one-write shared-field producer bindings"

  if [[ "${label}" == "unreachable-correlated-fields" ]]; then
    jq -e -s "${output_closure_helpers}"'
      any(region_goals | select(
        .kind == "OUTPUT_RELATION_CLOSURE"
        and .admission.state == "READY");
        ([output_members[].output.cell] | sort)
          == ([
            "<edu.uva.liftlab.graphchecker.fixtures.CorrelatedFieldsUnreachableThreeThreadWorkload$RpcBus: int left>",
            "<edu.uva.liftlab.graphchecker.fixtures.CorrelatedFieldsUnreachableThreeThreadWorkload$RpcBus: int right>"
          ] | sort))
    ' "${region_plan}" >/dev/null \
      || die "${label} did not preserve the joint left/right output demand"
  fi
}

validate_compound_target_artifacts() {
  local label=$1
  local work_root=$2
  local region_plan="${work_root}/runtime/concolic_region_plan.jsonl"
  local target_closure="${work_root}/target-campaign/region_path_closure.json"
  local target_query="${work_root}/schedule/branch_queries.jsonl"
  local composition="${work_root}/candidate/candidate_composition_manifest.json"
  local campaign_root="${work_root}/producer-campaign"
  local expected_reached consumer_name
  local -a merged_summaries

  expected_reached=positive
  consumer_name='$ReachableConsumerThread: void executeWorker()>'
  [[ "${label}" == "unreachable-compound-target" ]] \
    && {
      expected_reached=zero
      consumer_name='$UnreachableConsumerThread: void executeWorker()>'
    }
  require_file "${label} activation plan" "${region_plan}"
  require_file "${label} target closure" "${target_closure}"
  require_file "${label} target path query" "${target_query}"
  require_file "${label} composition manifest" "${composition}"
  [[ -d "${campaign_root}" ]] \
    || die "${label} producer campaign not found: ${campaign_root}"

  jq -e '
    .kind == "REGION_PATH_WORKLIST"
    and .state == "CLOSED"
    and .goalKind == "TARGET_REACH_CLOSURE"
    and (.gaps | length) == 0
  ' "${target_closure}" >/dev/null \
    || die "${label} target-function path worklist is incomplete"

  jq -e --arg expectation "${expected_reached}" '
    .kind == "TARGET_REACH_PATH_SET_QUERY"
    and .constraintAuthority
      == "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1"
    and (if $expectation == "positive"
      then (.paths | length) > 1
        and all(.paths[];
          (.constraints | length) >= 3)
        and any(.paths[]; (.constraints | length) >= 4)
      else (.paths | length) == 0
      end)
  ' "${target_query}" >/dev/null \
    || die "${label} target reach-path query is incomplete"

  jq -e -s --arg consumer "${consumer_name}" \
    --arg target_region "$(jq -r '.regionId' "${target_closure}")" \
    "${output_closure_helpers}"'
    [region_goals | select(.kind == "OUTPUT_RELATION_CLOSURE"
      and .admission.state == "READY"
      and (output_members | length) == 3)] as $producers
    | [region_goals | select(.kind == "TARGET_REACH_CLOSURE"
      and (.admission.state == "READY"
        or .admission.state == "DISCOVERED")
      and .regionId == $target_region
      and any(.branches[]?;
        .policy == "EXPLORE" and (.siteId | contains($consumer))))] as $targets
    | ($producers | length) == 2
    and all($producers[];
      (.outputClosure.members | length) == 3
      and all(.outputClosure.members[]; .slice.complete == true))
    and ([$producers[].edgeBindings[]?
      | select(read_from_evidence)]
      | length) == 6
    and ($targets | length) == 1
    and ([$targets[0].branches[]
      | select(.policy == "EXPLORE"
        and (.siteId | contains($consumer)))] | length) >= 5
  ' "${region_plan}" >/dev/null \
    || die "${label} lost its two joint three-output producer demands"

  mapfile -t merged_summaries < <(find "${campaign_root}" -mindepth 2 \
    -maxdepth 2 -type f -name merged_region_summaries.jsonl | sort)
  jq -e -s "${output_closure_helpers}"'
    [.[] | select(output_members | length == 3)] as $joint
    | ($joint | length) == 2
    and all($joint[];
      (output_members | length) == 3
      and .relationallyComplete == true
      and all(.regionRelation.cases[];
        (.outputExpressions | length) == 3))
  ' "${merged_summaries[@]}" >/dev/null \
    || die "${label} joint producer summaries lost output correlation"

  jq -e --arg expectation "${expected_reached}" \
    '
    .fatalConstraintAuthority
      == "CLOSED_IMPORTED_TARGET_REACH_PATH_SET_V1"
    and (.resolvedEdgeBindings | length) >= 6
    and ([.resolvedEdgeBindings[]] | unique | length)
      == (.resolvedEdgeBindings | length)
    and all(.resolvedEdgeBindings[];
      type == "string" and length > 0)
  ' "${composition}" >/dev/null \
    || die "${label} composition lost target paths or shared-field bindings"
}

validate_semantic_profile() {
  local label=$1
  local smt=$2
  local reach_report=$3
  local work_root=$4
  case "${label}" in
    baseline)
      jq -e "${output_closure_helpers}"'
        .reachCondition.reachability == "UNREACHABLE"
        and (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) == 0
        and (.valuations | length) == 4
        and all(.valuations[]; .status == "unsat")
        and .reachCondition.formula == "false"
      ' "${reach_report}" >/dev/null \
        || die "baseline lost its constructor-bound UNSAT profile"
      grep -Fq '(define-fun java_int_wrap' "${smt}" \
        || die "baseline SMT has no Java int wrap semantics"
      grep -Eq '\(java_int_wrap \(\+ 10 [^)]+\)\)' "${smt}" \
        || die "baseline SMT omitted wrapped 10 + var"
      ;;
    cross-method-fields)
      jq -e '
        (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) == 3
        and (.valuations | length) == 4
        and ([.valuations[] | select(.status == "sat")]
          | length) == 1
        and ([.valuations[] | select(.status == "unsat")]
          | length) == 3
        and ([.valuations[] | select(.status == "sat")
          | [.values[]
              | if . then "1" else "0" end] | join("")]
          == ["10"])
        and ([.roots.existentialInputs[].javaTypeDescriptor]
          | sort) == ["I", "I", "I"]
      ' "${reach_report}" >/dev/null \
        || die "cross-method-fields lost an external root or exact truth row"
      validate_cross_method_joint_output_artifacts "${work_root}" "${smt}"
      ;;
    multitype)
      jq -e '
        (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) == 4
        and (.valuations | length) == 4
        and ([.valuations[] | select(.status == "sat")]
          | length) == 2
        and ([.valuations[] | select(.status == "unsat")]
          | length) == 2
        and ([.valuations[] | select(.status == "sat")
          | [.values[]
              | if . then "1" else "0" end] | join("")]
          == ["10", "11"])
        and ([.roots.existentialInputs[].javaTypeDescriptor]
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
        .state == "CANDIDATE_READY"
        and .trustState == "CANDIDATE_ONLY"
        and .reachCondition.reachability == "REACHABLE"
        and (.roots.booleanInputs | length) == 1
        and (.roots.existentialInputs | length) == 2
        and (.valuations | length) == 2
        and ([.valuations[] | select(.status == "sat")]
          | length) == 1
        and ([.valuations[] | select(.status == "unsat")]
          | length) == 1
        and ([.valuations[] | select(.status == "sat")
          | [.values[]
              | if . then "1" else "0" end] | join("")]
          == ["1"])
        and ([.valuations[]
          | ([.values[]
              | if . then "1" else "0" end] | join("")) as $key
          | select(($key == "1" and .status == "sat")
            or ($key == "0" and .status == "unsat"))]
          | length) == 2
        and ([.roots.existentialInputs[].javaTypeDescriptor]
          | sort) == ["I", "Ljava/lang/String;"]
        and ([.roots.existentialInputs[]
          | select(.javaTypeDescriptor == "Ljava/lang/String;"
            and (.nullnessSolverTerm
              | type == "string" and length > 0))]
          | length) == 1
      ' "${reach_report}" >/dev/null \
        || die "dependent-scalar lost its exact existential reach profile"
      jq -e '
        .fatalSite
          | startswith("<edu.uva.liftlab.graphchecker.fixtures.DependentScalarThreeThreadWorkload$ConsumerThread: void executeWorker()>#")
      ' "${work_root}/candidate/candidate_composition_manifest.json" >/dev/null \
        || die "dependent-scalar composition moved away from the annotated target"
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
        (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) >= 3
        and all(.roots.existentialInputs[];
          .javaTypeDescriptor == "I")
        and (.valuations | length) == 4
        and ([.valuations[] | select(.status == "sat")]
          | length) == 4
        and ([.valuations[] | select(.status == "unsat")]
          | length) == 0
        and all(.valuations[];
          .status == "sat")
      ' "${reach_report}" >/dev/null \
        || die "containers lost its Java int overflow reach profile"
      grep -Fq '(define-fun java_int_wrap' "${smt}" \
        || die "containers SMT omitted Java int wrap semantics"
      validate_container_producer_artifacts "${work_root}"
      ;;
    unreachable-parity)
      jq -e '
        .state == "CANDIDATE_READY"
        and .trustState == "CANDIDATE_ONLY"
        and .reachCondition.reachability == "UNREACHABLE"
        and (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) == 4
        and all(.roots.existentialInputs[];
          .javaTypeDescriptor == "I")
        and (.valuations | length) == 4
        and ([.valuations[] | select(.status == "sat")]
          | length) == 0
        and ([.valuations[] | select(.status == "unsat")]
          | length) == 4
        and .reachCondition.formula == "false"
        and all(.valuations[];
          .status == "unsat")
      ' "${reach_report}" >/dev/null \
        || die "unreachable-parity was not proved unreachable for all roots"
      validate_unreachable_parity_producer_artifacts "${work_root}"
      ;;
    unreachable-correlated-fields)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" I
      validate_scalar_unsat_producer_artifacts "${label}" "${work_root}"
      ;;
    unreachable-nested-object)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" I
      validate_scalar_unsat_producer_artifacts "${label}" "${work_root}"
      ;;
    unreachable-inherited-alias)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" I
      validate_scalar_unsat_producer_artifacts "${label}" "${work_root}"
      ;;
    unreachable-mutated-object)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" I
      validate_scalar_unsat_producer_artifacts "${label}" "${work_root}"
      ;;
    unreachable-long-fields)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" J
      validate_scalar_unsat_producer_artifacts "${label}" "${work_root}"
      ;;
    compound-target)
      jq -e '
        .state == "CANDIDATE_READY"
        and .trustState == "CANDIDATE_ONLY"
        and .reachCondition.reachability == "REACHABLE"
        and (.roots.booleanInputs | length) == 2
        and (.roots.existentialInputs | length) == 0
        and (.valuations | length) == 4
        and ([.valuations[] | select(.status == "sat")
          | [.values[]
              | if . then "1" else "0" end] | join("")]
          == ["01", "10", "11"])
        and ([.valuations[] | select(.status == "unsat")
          | [.values[]
              | if . then "1" else "0" end] | join("")] == ["00"])
      ' "${reach_report}" >/dev/null \
        || die "${label} lost its compound short-circuit truth table"
      grep -Fq ':named fatal_path' "${smt}" \
        || die "${label} SMT omitted the target reach-path assertion"
      grep -Fq '(or ' "${smt}" \
        || die "${label} SMT did not disjoin reached target paths"
      validate_compound_target_artifacts "${label}" "${work_root}"
      ;;
    unreachable-compound-target)
      validate_two_boolean_unsat_report "${label}" "${reach_report}" I none
      validate_compound_target_artifacts "${label}" "${work_root}"
      ;;
    tricky-divergent-object-fields|tricky-map-key-value)
      jq -e '
        .reachCondition.reachability == "REACHABLE"
        and any(.valuations[]; .status == "sat")
      ' "${reach_report}" >/dev/null \
        || die "${label} lost its reachable container profile"
      ;;
    tricky-nested-array-map-key|tricky-array-element-frame|tricky-compound-container-guard)
      jq -e '
        .reachCondition.reachability == "UNREACHABLE"
        and all(.valuations[]; .status == "unsat")
      ' "${reach_report}" >/dev/null \
        || die "${label} lost its unreachable container profile"
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
  local candidate_manifest="${candidate_root}/candidate_result_manifest.json"
  local reachability candidate_reachability
  local solver_output solver_status expected_status

  require_file "candidate SMT" "${smt}"
  [[ -s "${smt}" ]] || die "candidate SMT is empty: ${smt}"
  grep -Eq '^[[:space:]]*\(check-sat\)' "${smt}" \
    || die "candidate SMT has no check-sat command: ${smt}"
  validate_json_object "candidate composition manifest" "${composition}"
  validate_json_object "candidate reach model" "${reach_report}"
  validate_json_object "candidate result manifest" "${candidate_manifest}"
  validate_composition_common "${composition}"

  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_COMPOSED_SMT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
  ' "${composition}" >/dev/null \
    || die "candidate composition escaped CANDIDATE trust state"
  jq -e '
    .schemaVersion == 3
    and .kind == "BOOLEAN_REACH_CONDITION_REPORT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.reachCondition.reachability == "REACHABLE"
      or .reachCondition.reachability == "UNREACHABLE")
    and ((.gaps // []) | length) == 0
    and ((.roots.booleanInputs // []) | type) == "array"
    and ((.roots.existentialInputs // []) | type) == "array"
    and ((.valuations // []) | type) == "array"
    and all(.valuations[];
      (.status == "sat")
      or (.status == "unsat"))
    and ([.valuations[]
      | [.values[]
          | if . then "1" else "0" end] | join("")]
      | unique | length)
      == (.valuations | length)
    and (if .reachCondition.reachability == "REACHABLE"
      then any(.valuations[]; .status == "sat")
      else all(.valuations[]; .status == "unsat")
      end)
    and (.reachCondition | type == "object")
    and (.reachCondition.formula | type == "string" and length > 0)
  ' "${reach_report}" >/dev/null \
    || die "candidate Boolean reach model is incomplete"
  jq -e '
    .schemaVersion == 2
    and .kind == "CONCOLIC_CANDIDATE_RESULT"
    and .state == "CANDIDATE_READY"
    and .trustState == "CANDIDATE_ONLY"
    and (.reachability == "REACHABLE"
      or .reachability == "UNREACHABLE")
  ' "${candidate_manifest}" >/dev/null \
    || die "candidate result incorrectly claims trusted promotion"
  validate_artifact_binding "${candidate_manifest}" \
    candidateSmtArtifact "${smt}"
  validate_artifact_binding "${candidate_manifest}" \
    compositionManifestArtifact "${composition}"
  validate_artifact_binding "${candidate_manifest}" \
    candidateReachModelArtifact "${reach_report}"

  reachability=$(jq -er '
    .reachCondition.reachability
    | select(. == "REACHABLE" or . == "UNREACHABLE")
  ' "${reach_report}") \
    || die "candidate reach model has no reachability status"
  candidate_reachability=$(jq -er '
    .reachability
    | select(. == "REACHABLE" or . == "UNREACHABLE")
  ' "${candidate_manifest}") \
    || die "candidate result has no reachability status"
  [[ "${candidate_reachability}" == "${reachability}" ]] \
    || die "candidate result disagrees with the reach model"
  expected_status=$([[ "${reachability}" == "REACHABLE" ]] \
    && printf sat || printf unsat)
  solver_output=$("${z3}" "${smt}") \
    || die "z3 failed for ${label} candidate"
  printf '%s\n' "${solver_output}" | grep -Fq '(error' \
    && die "z3 reported an SMT error for ${label} candidate"
  solver_status=$(awk 'NF { print $1; exit }' <<< "${solver_output}")
  [[ "${solver_status}" == "${expected_status}" ]] \
    || die "${label} candidate expected z3 ${expected_status}, got ${solver_status}"
  validate_producer_contracts "${label}" "${work_root}"
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
  core|all|baseline|cross-method-fields|multitype|dependent-scalar|containers|unreachable-parity|unreachable-correlated-fields|unreachable-nested-object|unreachable-inherited-alias|unreachable-mutated-object|unreachable-long-fields|compound-target|unreachable-compound-target|container-tricky|tricky-nested-array-map-key|tricky-divergent-object-fields|tricky-array-element-frame|tricky-map-key-value|tricky-compound-container-guard) ;;
  help|-h|--help) usage; exit 0 ;;
  *) usage >&2; die "unknown matrix mode: ${mode}" ;;
esac

require_command awk
require_command find
require_command grep
require_command jq
require_command realpath
require_command sha256sum
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
      unreachable-parity unreachable-correlated-fields \
      unreachable-nested-object unreachable-inherited-alias \
      unreachable-mutated-object unreachable-long-fields compound-target \
      unreachable-compound-target)
    configs=(workflow.properties cross-method-fields/workflow.properties \
      multitype/workflow.properties dependent-scalar/workflow.properties \
      containers/workflow.properties unreachable-parity/workflow.properties \
      unreachable-correlated-fields/workflow.properties \
      unreachable-nested-object/workflow.properties \
      unreachable-inherited-alias/workflow.properties \
      unreachable-mutated-object/workflow.properties \
      unreachable-long-fields/workflow.properties \
      compound-target/workflow.properties \
      unreachable-compound-target/workflow.properties)
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
  unreachable-correlated-fields)
    labels=(unreachable-correlated-fields)
    configs=(unreachable-correlated-fields/workflow.properties)
    ;;
  unreachable-nested-object)
    labels=(unreachable-nested-object)
    configs=(unreachable-nested-object/workflow.properties)
    ;;
  unreachable-inherited-alias)
    labels=(unreachable-inherited-alias)
    configs=(unreachable-inherited-alias/workflow.properties)
    ;;
  unreachable-mutated-object)
    labels=(unreachable-mutated-object)
    configs=(unreachable-mutated-object/workflow.properties)
    ;;
  unreachable-long-fields)
    labels=(unreachable-long-fields)
    configs=(unreachable-long-fields/workflow.properties)
    ;;
  compound-target)
    labels=(compound-target)
    configs=(compound-target/workflow.properties)
    ;;
  unreachable-compound-target)
    labels=(unreachable-compound-target)
    configs=(unreachable-compound-target/workflow.properties)
    ;;
  container-tricky)
    labels=(tricky-nested-array-map-key tricky-divergent-object-fields \
      tricky-array-element-frame tricky-map-key-value \
      tricky-compound-container-guard)
    configs=(tricky-nested-array-map-key/workflow.properties \
      tricky-divergent-object-fields/workflow.properties \
      tricky-array-element-frame/workflow.properties \
      tricky-map-key-value/workflow.properties \
      tricky-compound-container-guard/workflow.properties)
    ;;
  tricky-nested-array-map-key)
    labels=(tricky-nested-array-map-key)
    configs=(tricky-nested-array-map-key/workflow.properties)
    ;;
  tricky-divergent-object-fields)
    labels=(tricky-divergent-object-fields)
    configs=(tricky-divergent-object-fields/workflow.properties)
    ;;
  tricky-array-element-frame)
    labels=(tricky-array-element-frame)
    configs=(tricky-array-element-frame/workflow.properties)
    ;;
  tricky-map-key-value)
    labels=(tricky-map-key-value)
    configs=(tricky-map-key-value/workflow.properties)
    ;;
  tricky-compound-container-guard)
    labels=(tricky-compound-container-guard)
    configs=(tricky-compound-container-guard/workflow.properties)
    ;;
esac

for matrix_position in "${!labels[@]}"; do
  run_case "${labels[${matrix_position}]}" \
    "${configs[${matrix_position}]}"
done

echo "[three-thread-rpc-matrix] validated ${#labels[@]} workflows"
