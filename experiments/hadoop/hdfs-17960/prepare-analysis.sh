#!/usr/bin/env bash
set -euo pipefail

repo=/u/vnr3ne/hadoop-hdfs-17960
analysis=/tmp/graphchecker-hdfs-17960-classes
common=${repo}/hadoop-common-project/hadoop-common/target/classes
hdfs=${repo}/hadoop-hdfs-project/hadoop-hdfs/target/classes
mkdir -p "${analysis}"
find "${analysis}" -type f -delete

copy_family() {
  local root=$1 family=$2 file found=false base
  [[ -d "${root}" ]] || {
    echo "missing compiled class root: ${root}" >&2
    return 2
  }
  base=$(basename "${family}")
  while IFS= read -r file; do
    found=true
    mkdir -p "${analysis}/$(dirname "${file}")"
    cp "${root}/${file}" "${analysis}/${file}"
  done < <(cd "${root}" && find "$(dirname "${family}")" -maxdepth 1 \
    -type f \( -name "${base}.class" -o -name "${base}\$*.class" \) \
    | sort)
  [[ "${found}" == true ]] || {
    echo "missing compiled class family: ${family}" >&2
    return 2
  }
}

copy_family "${common}" org/apache/hadoop/ipc/CausynthMessagePropagation
copy_family "${common}" org/apache/hadoop/ipc/CausynthSymbolicSource
copy_family "${common}" org/apache/hadoop/ipc/Client
copy_family "${common}" org/apache/hadoop/ipc/Server

copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSEditLogLoader
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSDirSnapshotOp
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSDirectory
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSImage
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSImageFormatProtobuf
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/snapshot/FSImageFormatPBSnapshot
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/FSNamesystem
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/INodeDirectory
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/NameNodeRpcServer

copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/snapshot/DirectorySnapshottableFeature
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/snapshot/Snapshot
copy_family "${hdfs}" org/apache/hadoop/hdfs/server/namenode/snapshot/SnapshotManager
copy_family "${hdfs}" org/apache/hadoop/hdfs/util/ReadOnlyList
