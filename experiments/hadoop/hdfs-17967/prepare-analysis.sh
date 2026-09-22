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
# ipc/Client stays in scope even though this case removed the fault marker
# from it: the class carries the IPC message-propagation calls the causal
# context travels on, and without it the replay stops reaching the target
# at all.  Dropping it was tried and reverted.
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
    # DELIBERATELY NARROW, and modelled on hdfs-17897's scope, which passes.
    #
    # Adding DataXceiver/DataNode here made the target's enclosing region the
    # DataXceiverServer connection-accept loop, whose thread starts with the
    # cluster -- before the workload registers any source -- so both
    # DataNodes' target occurrences came back on workload/unregistered with a
    # lost context.  Two nodes with no node then share ONE address
    # (OCCURRENCE_ADDRESS_SHARED) and the closure cannot tell the mirror from
    # the head.  Left out, the target is enclosed by the per-connection SASL
    # callback handler instead, which is entered after registration and is
    # what every passing case in this family anchors on.
    #
    # The client family is needed because this case's client is in the
    # recorded window, unlike hdfs-17899's.
    copy_family "${client}" org/apache/hadoop/hdfs/DFSClient
    ;;
esac
