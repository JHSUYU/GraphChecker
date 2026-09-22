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
  pathA)
    # The write pipeline: the head DataNode's DataXceiver opens the mirror
    # connection whose SASL handshake carries the stale key.
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/DataXceiver
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/DataNode
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/BPOfferService
    # A region root must be a THREAD/TASK entry, main, an explicit fault or
    # the failure target (RuntimeRegionPlanner#validRootAuthority).  Without
    # these two, nothing in the slice that is such an entry reaches
    # BlockTokenSecretManager.updateKeys, so the rotation becomes a root of
    # its own and the trace refuses it: "region skeleton has no authoritative
    # execution context root".  HeartbeatManager$Monitor is the Runnable that
    # reaches it, through BlockManager.
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/blockmanagement/HeartbeatManager
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/blockmanagement/BlockManager
    ;;
esac
