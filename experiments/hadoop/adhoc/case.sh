# Ad-hoc coordination checks of HDFS: a throw whose guard compares what one
# node holds with what another sent, and which a workload's healthy path
# evaluates and passes (tools/analysis: throwsites.py, coverage.sh,
# reached.py).  One case per check and workload, "<check>.<workload>":
# checks.tsv declares the checks and the workloads each is reached on,
# occurrences.tsv each case's target occurrence (discovered, README of lib).
# All run one JDK 8 tree, gc/hdfs-17967-pathC; tools/analysis/mkadhoc.py
# annotates it and writes targets/.  DataXceiver is never woven.
# Coverage counts the whole JVM, set-up before the recording window
# included; only a discovery run says the window reaches a check (the
# PacketResponder seqno check ran only for mirror's pre-window client write:
# the window's DataNode transfer starts no responder, so it is not a case).
check=${1%%.*}
workload=${1#*.}
[[ -n "${check}" && "${workload}" != "$1" ]] || {
  echo "usage: case.sh <check>.<workload>" >&2
  return 2
}
repo=/u/vnr3ne/hadoop-hdfs-17967-c
row=$(awk -F'\t' -v c="${check}" '$1 == c' "${here}/checks.tsv")
[[ -n "${row}" ]] || { echo "unknown ad-hoc check: ${check}" >&2; return 2; }
IFS=$'\t' read -r _ _ _ own workloads <<<"${row}"
[[ " ${workloads} " == *" ${workload} "* ]] || {
  echo "${check} is not declared on ${workload}" >&2
  return 2
}
target_spec=${here}/targets/${check}.yaml
target_occurrence=$(awk -F'\t' -v c="$1" '$1 == c {print $2}' \
  "${here}/occurrences.tsv")
# The family scope carries the IPC and SASL doors; Sender carries the
# data-transfer SEND door, one per op.  No door on reads: every pipeline ack
# is one, and a door per packet admits an occurrence per packet.
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/protocol/datatransfer/Sender)
[[ "${own}" == - ]] || scope+=("${own}")
datanode=org.apache.hadoop.hdfs.server.datanode
ec=hdfs:org/apache/hadoop/hdfs/server/datanode/erasurecode
case "${workload}" in
  mirror)
    test_class=${datanode}.TestCausynthWriteBlockMirrorStaleKey
    test_method=testWritePipelineAfterKeyRotations
    scope+=(client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  proxy)
    test_class=${datanode}.TestCausynthReplaceBlockProxyStaleKey
    test_method=testBlockMoveAfterKeyRotations
    ;;
  replicate)
    test_class=${datanode}.TestCausynthDataTransferRpcFailure
    test_method=testReplicationAfterModeledKeyRefreshRpcFailure
    ;;
  reconstruct)
    test_class=${datanode}.TestCausynthStripedReconstructTargetStaleKey
    test_method=testReconstructionAfterKeyRotations
    scope+=("${ec}/StripedWriter" "${ec}/StripedBlockWriter"
      "${ec}/StripedBlockReconstructor" "${ec}/StripedReconstructor"
      "${ec}/StripedReconstructionInfo" "${ec}/ErasureCodingWorker")
    ;;
  # Upstream tests, each on one DataNode: with more, the NameNode's choice of
  # a pipeline's head is a ThreadLocalRandom draw no run can repeat.
  flush)
    test_class=org.apache.hadoop.hdfs.TestFileAppend
    test_method=testSimpleFlush
    scope+=(client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  softlimit)
    test_class=org.apache.hadoop.hdfs.TestFileAppend
    test_method=testAppendAfterSoftLimit
    scope+=(client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  # Any other cluster test of the module, "<test class>-<method>", run as
  # it is written: the MiniDFSCluster it builds is made reproducible and
  # registered, and opens the window, by itself (CausynthCluster#AUTOMATIC).
  # Its classpath is the module's, stated by any of its reports.
  Test*-*)
    test_method=${workload#*-}
    test_class=$(cd "${repo}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes" \
      && find . -name "${workload%%-*}.class" | sed 's#^\./##; s#\.class$##; s#/#.#g')
    [[ -n "${test_class}" && "${test_class}" != *$'\n'* ]] || {
      echo "no single test class ${workload%%-*} in ${repo}" >&2
      return 2
    }
    classpath_test=org.apache.hadoop.hdfs.TestFileAppend
    workload_properties=(-Dcausynth.cluster.automatic=true)
    scope+=(client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  *)
    echo "unknown ad-hoc workload: ${workload}" >&2
    return 2
    ;;
esac
