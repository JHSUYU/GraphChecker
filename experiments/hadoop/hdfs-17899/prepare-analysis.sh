#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source "${here}/case.sh" "${1:?missing case}"
mkdir -p "${analysis}"
find "${analysis}" -type f -delete

copy_family() {
  local root=$1 family=$2 file found=false
  [[ -d "${root}" ]] || {
    echo "missing compiled class root: ${root}" >&2
    return 2
  }
  while IFS= read -r file; do
    found=true
    mkdir -p "${analysis}/$(dirname "${file}")"
    cp "${root}/${file}" "${analysis}/${file}"
  done < <(cd "${root}" && find "$(dirname "${family}")" -maxdepth 1 \
    -type f -name "$(basename "${family}")*.class" | sort)
  [[ "${found}" == true ]] || {
    echo "missing compiled class family: ${family}" >&2
    return 2
  }
}

common=${repo}/hadoop-common-project/hadoop-common/target/classes
client=${repo}/hadoop-hdfs-project/hadoop-hdfs-client/target/classes
hdfs=${module}/target/classes

copy_family "${common}" org/apache/hadoop/ipc/CausynthMessagePropagation
copy_family "${common}" org/apache/hadoop/ipc/CausynthSymbolicSource
copy_family "${common}" org/apache/hadoop/ipc/Client
copy_family "${common}" org/apache/hadoop/security/token/delegation/DelegationKey
copy_family "${client}" org/apache/hadoop/hdfs/protocol/datatransfer/sasl/DataTransferSaslUtil
copy_family "${client}" org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferClient
copy_family "${client}" org/apache/hadoop/hdfs/security/token/block/DataEncryptionKey
copy_family "${client}" org/apache/hadoop/hdfs/protocolPB/PBHelperClient
copy_family "${hdfs}" org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer
copy_family "${hdfs}" org/apache/hadoop/hdfs/protocolPB/PBHelper
copy_family "${hdfs}" org/apache/hadoop/hdfs/security/token/block/BlockKey
copy_family "${hdfs}" org/apache/hadoop/hdfs/security/token/block/BlockPoolTokenSecretManager
copy_family "${hdfs}" org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager
copy_family "${hdfs}" org/apache/hadoop/hdfs/security/token/block/ExportedBlockKeys

case "${case_id}" in
  bug1)
    # KeyManager is the case: its one cached DataEncryptionKey is what goes
    # stale.  Balancer and Dispatcher used to be here for
    # TestBalancerWithEncryptedTransfer; the bespoke workload drives the
    # KeyManager and the move directly, so neither class is entered.
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/balancer/KeyManager
    # The same two bug3 has, and for the same reason: the DataNode side of a
    # KeyUpdateCommand runs through them, and that is the only writer in the
    # corpus that can take a key OUT of the destination's allKeys.
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/BPOfferService
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/DataNode
    ;;
  bug2)
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/balancer/KeyManager
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/common/sps/BlockDispatcher
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/sps/ExternalSPSBlockMoveTaskHandler
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/sps/StoragePolicySatisfier
    ;;
  bug3)
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/BPOfferService
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/DataNode
    ;;
esac
