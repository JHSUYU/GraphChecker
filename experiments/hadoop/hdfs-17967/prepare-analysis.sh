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

# Copies ONE class and its own nested classes, and nothing else.  copy_family
# globs on a prefix, so "DataXceiver" also matches DataXceiverServer -- and
# with the accept loop in scope the target occurrence became
#   workload/unregistered#epoch0/region/REGION.61e62f41/ctx:Lost:UNKNOWN
#   /idx:<DataXceiverServer: void run()>@0/...#u32@0/<DataXceiver: void run()>@0
# because that loop's thread starts with the cluster, long before the workload
# registers anything.  Measured 2026-09-22 on both path A and path B.
copy_class() {
  local root=$1 name=$2 file found=false
  [[ -d "${root}" ]] || {
    echo "missing compiled class root: ${root}" >&2
    return 2
  }
  while IFS= read -r file; do
    found=true
    mkdir -p "${analysis}/$(dirname "${file}")"
    cp "${root}/${file}" "${analysis}/${file}"
  done < <(cd "${root}" && find "$(dirname "${name}")" -maxdepth 1 -type f \
    \( -name "$(basename "${name}").class" \
       -o -name "$(basename "${name}")\$*.class" \) | sort)
  [[ "${found}" == true ]] || {
    echo "missing compiled class: ${name}" >&2
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
    # DataXceiver is deliberately NOT woven, here or in path B, and the
    # reason is measured (2026-09-22, with DataXceiverServer excluded, so it
    # is DataXceiver itself).  With it in scope DataXceiver.run() becomes the
    # region root and swallows the anchored REGION.7c569c3f entirely; PLAN
    # then refuses by name and the only observed target occurrence is
    #   workload/unregistered#epoch0/region/REGION.61e62f41/ctx:Lost:UNKNOWN
    #   /idx:<DataXceiver: void run()>@0
    # because that thread starts before any inbound context and before its
    # local owner is stamped.  Left out, the target is enclosed by the
    # per-connection SASL callback handler, which every passing case in this
    # family anchors on.
    #
    # The producer occurrence of the relay hop -- what UNATTESTED_ARM was
    # about -- is stated a different way: DataXceiver opens its own request
    # scope around the mirror/proxy socketSend.  Those are plain static
    # propagation calls and run whether or not the class is woven.
    #
    # The client family is left over from the client-driven workload this
    # case used to have; the DataNode-driven one enters none of it.
    copy_family "${client}" org/apache/hadoop/hdfs/DFSClient
    ;;
  pathB)
    # Nothing beyond the shared families.  The mover is the test, so no
    # client family is needed, and the two DataNode roles are covered.
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
