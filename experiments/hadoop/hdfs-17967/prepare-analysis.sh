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
  pathB)
    # The mover is the test, so no client family is needed.  DataXceiver IS,
    # and that is the whole of this case's second hop: the key the proxy has
    # to resolve is PRODUCED by the target's DataXceiver.replaceBlock, whose
    # occurrence is a ROLE.DATA_XCEIVER root.  Left out of the scope, no
    # session states that occurrence's rows and every path through the target
    # occurrence is an UNATTESTED_ARM on a HandoffLeafCarrier -- 40 of them,
    # measured 2026-09-22 -- "what was delivered is stated and why is not".
    # With the read unpinned the clocks are not NECESSARY and ClaimPolicy
    # falls past CLOCK_SKEW to NO_SUPPORTED_WITNESS.
    #
    # The three cases that pass with no such gap each state their producer a
    # different way: hdfs-17899 bug1's is the mover itself (a registered
    # EXTERNAL_APP), bug3's is DataNode.DataTransfer with DataNode in scope,
    # and path C's is the erasure-coding pool thread with
    # StripedBlockReconstructor in scope.
    copy_family "${hdfs}" org/apache/hadoop/hdfs/server/datanode/DataXceiver
    ;;
  pathC)
    # The annotated site is StripedWriter's "All targets are failed.", so the
    # erasure-coding reconstruction families are the case, not the shared
    # SASL ones alone.  StripedBlockReconstructor carries the request scope
    # into the pool thread, so it has to be woven too.
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/StripedWriter
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/StripedBlockWriter
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/StripedBlockReconstructor
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/StripedReconstructor
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/StripedReconstructionInfo
    copy_family "${hdfs}" \
      org/apache/hadoop/hdfs/server/datanode/erasurecode/ErasureCodingWorker
    ;;
esac
