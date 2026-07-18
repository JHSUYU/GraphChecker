#!/bin/bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE-$0}")"; pwd)
runner="${script_dir}/run_hdfs.sh"
fixture=$(mktemp -d)
trap 'rm -rf -- "${fixture}"' EXIT

dn_root='<org.apache.hadoop.hdfs.server.datanode.BPServiceActor: void run()>'
nn_root='<org.apache.hadoop.hdfs.server.blockmanagement.HeartbeatManager$Monitor: void run()>'
add_keys='<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: void addKeys(org.apache.hadoop.hdfs.security.token.block.ExportedBlockKeys)>'
remove_expired='<org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager: void removeExpiredKeys()>'

emit_region() {
    local catalog=$1
    local id=$2
    local root=$3
    shift 3
    jq -nc --arg id "${id}" --arg root "${root}" \
        --args '$ARGS.positional as $methods
          | {regionId:$id, rootMethod:$root, methods:$methods}' "$@" \
        >> "${catalog}"
}

good="${fixture}/good.jsonl"
emit_region "${good}" DN "${dn_root}" \
    "${dn_root}" "${add_keys}" "${remove_expired}"
emit_region "${good}" NN "${nn_root}" \
    "${nn_root}" "${remove_expired}"
"${runner}" verify-region-roots "${good}" >/dev/null

# The two DN methods must coexist in one region; two partial regions do not
# prove a heartbeat-rooted add-and-expire chain.
split_dn="${fixture}/split-dn.jsonl"
emit_region "${split_dn}" DN_ADD "${dn_root}" "${dn_root}" "${add_keys}"
emit_region "${split_dn}" DN_REMOVE "${dn_root}" \
    "${dn_root}" "${remove_expired}"
emit_region "${split_dn}" NN "${nn_root}" \
    "${nn_root}" "${remove_expired}"
if "${runner}" verify-region-roots "${split_dn}" >/dev/null 2>&1; then
    echo "split DN regions unexpectedly passed the region-root gate" >&2
    exit 1
fi

missing_nn="${fixture}/missing-nn.jsonl"
emit_region "${missing_nn}" DN "${dn_root}" \
    "${dn_root}" "${add_keys}" "${remove_expired}"
emit_region "${missing_nn}" NN "${nn_root}" "${nn_root}"
if "${runner}" verify-region-roots "${missing_nn}" >/dev/null 2>&1; then
    echo "NN region without removeExpiredKeys unexpectedly passed" >&2
    exit 1
fi

echo "HDFS static region-root gate fixture passed"
