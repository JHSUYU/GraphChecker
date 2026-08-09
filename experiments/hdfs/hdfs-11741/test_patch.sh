#!/usr/bin/env bash

set -euo pipefail

experiment_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
source_repo=${HADOOP_SOURCE_REPO:-/opt/hadoop}
base_commit=ece33208b89a6a06c1b362d10fab31343fe5df13
temporary_root=$(mktemp -d /tmp/hdfs11741-patch-test.XXXXXX)
checkout="${temporary_root}/hadoop"

cleanup() {
  if [[ -e "${checkout}/.git" ]]; then
    git -C "${source_repo}" worktree remove --force "${checkout}" \
      >/dev/null 2>&1 || true
  fi
  rm -rf -- "${temporary_root}"
}
trap cleanup EXIT

git -C "${source_repo}" rev-parse --verify "${base_commit}^{commit}" \
  >/dev/null
git -C "${source_repo}" worktree add --detach "${checkout}" \
  "${base_commit}" >/dev/null

HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch

# Runtime discovery and custom-VM replay share one eight-activation envelope.
# A caller may shrink it, but cannot expand it beyond the generic loop bound.
HDFS11741_NN_UPDATE_ITERATIONS=1 \
HDFS11741_DATANODE_REFRESH_ITERATIONS=2 \
HDFS11741_BALANCER_REFRESH_ITERATIONS=3 \
  HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
if HDFS11741_NN_UPDATE_ITERATIONS=9 \
    HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch \
    >/dev/null 2>&1; then
  echo "[hdfs-11741] iteration bounds above eight must be rejected" >&2
  exit 1
fi

rg -Fq 'hdfs11741_loop_iteration_cap=8' "${experiment_dir}/run.sh"
! rg -q 'HDFS11741_(NN_UPDATE|DATANODE_REFRESH|BALANCER_REFRESH)_ITERATIONS:-?(8|32)' \
  "${experiment_dir}/run.sh"

git -C "${checkout}" diff --check
git -C "${checkout}" apply --reverse --check \
  "${experiment_dir}/patches/runtime-trace-workload.patch"
git -C "${checkout}" apply --reverse --check \
  "${experiment_dir}/patches/mark-fatal-target.patch"

# The patched variant layers only the production expiry guard over the same
# tracing workload.  Applying it twice must be idempotent, and the vulnerable
# variant must not silently accept the now-fixed source tree.
HDFS11741_VARIANT=patched \
  HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
HDFS11741_VARIANT=patched \
  HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
git -C "${checkout}" apply --reverse --check \
  "${experiment_dir}/patches/expiry-guard.patch"
rg -Fq 'import org.apache.hadoop.util.Time;' \
  "${checkout}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java"
rg -Fq 'encryptionKey.expiryDate < Time.now()' \
  "${checkout}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/server/balancer/KeyManager.java"
if HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch \
    >/dev/null 2>&1; then
  echo "[hdfs-11741] vulnerable variant accepted the expiry fix" >&2
  exit 1
fi

# Until the explicit fault-injection patch is supplied, patched-fault is a
# named but unavailable variant and must fail before mutating the checkout.
fault_patch="${experiment_dir}/patches/symbolic-rpc-fault.patch"
if [[ -s "${fault_patch}" ]]; then
  HDFS11741_VARIANT=patched-fault \
    HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
  HDFS11741_VARIANT=patched-fault \
    HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch
  git -C "${checkout}" apply --reverse --check "${fault_patch}"
else
  fault_error=""
  if fault_error=$(HDFS11741_VARIANT=patched-fault \
      HADOOP_REPO="${checkout}" "${experiment_dir}/run.sh" __patch 2>&1); then
    echo "[hdfs-11741] unavailable patched-fault variant unexpectedly succeeded" >&2
    exit 1
  fi
  [[ "${fault_error}" == *'variant patched-fault is unavailable'* ]] \
    || { echo "${fault_error}" >&2; exit 1; }
fi

bridge="${checkout}/hadoop-common-project/hadoop-common/src/main/java/org/apache/hadoop/ipc/CausynthRpcTrace.java"
rg -Fq 'recorderWithOwner.invoke(null, direction, transport, wireId, localOwner)' \
  "${bridge}"
! rg -q 'recordRpcEndpoint|String endpoint|payloadFingerprint|valueFingerprint' \
  "${bridge}"
rg -Fq '"HADOOP_IPC"' "${bridge}"
rg -Fq '"SASL_HANDSHAKE"' \
  "${checkout}/hadoop-hdfs-project/hadoop-hdfs-client/src/main/java/org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferClient.java"
rg -Fq 'causynth.replay.block.key.serial.seed' \
  "${checkout}/hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager.java"
! rg -qi 'fixed[- ]length|padding|Arrays\.copyOf' \
  "${experiment_dir}/patches/runtime-trace-workload.patch"

echo "[hdfs-11741] patch dry-run and idempotence checks passed"
