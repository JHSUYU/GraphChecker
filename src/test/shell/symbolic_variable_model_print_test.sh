#!/usr/bin/env bash

set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)
# shellcheck source=../../../run_engine.sh
source "${repo}/run_engine.sh"

test_tmp=$(mktemp -d)
cleanup() {
  [[ "${test_tmp}" == /tmp/* ]] || return 1
  rm -r -- "${test_tmp}"
}
trap cleanup EXIT

report="${test_tmp}/z3-result.json"
jq -n '{symbolicVariableModels: [{
  schemaVersion: 1, kind: "SYMBOLIC_VARIABLE_MODEL", valuationOrdinal: 0,
  variables: [
    {inputKind: "CONFIGURED_SOURCE_FIELD",
     sourceKey: "cluster/dn0#epoch0", sourceId: "RPC_COMPARE.A",
     sourcePhaseId: "SOURCE_PHASE.a", fieldSignature: "<DataNode: long a>",
     value: "7"},
    {inputKind: "CONFIGURED_SOURCE_FIELD",
     sourceKey: "cluster/dn1#epoch0", sourceId: "RPC_COMPARE.B",
     sourcePhaseId: "SOURCE_PHASE.b", fieldSignature: "<DataNode: long b>",
     value: "9"}]}]}' >"${report}"

output=$(campaign_print_symbolic_variable_models "${report}")
[[ "${output}" == *"source=cluster/dn0#epoch0 variable=RPC_COMPARE.A"* ]]
[[ "${output}" == *"field=<DataNode: long a> value=7"* ]]
[[ "${output}" == *"source=cluster/dn1#epoch0 variable=RPC_COMPARE.B"* ]]
[[ "${output}" == *"field=<DataNode: long b> value=9"* ]]

echo "symbolic variable model print test passed"
