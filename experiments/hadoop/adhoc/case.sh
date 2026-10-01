# Ad-hoc coordination checks of HDFS: a throw whose guard compares what one
# node holds with what another sent, and which a workload's healthy path
# evaluates and passes (tools/adhoc: sites.py, coverage.sh, reach.py; a
# sweep's are declared, named <Class>-<throw line>, and chosen by their static
# slice by select.py, slice.sh and score.py).  A case is one check on one
# workload, "<check>.<workload>", or a batch of checks on one workload,
# "B<n>": a row "B<n><TAB><workload><TAB><check> <check>..." of batches.tsv,
# whose target spec is targets/B<n>.yaml (tools/adhoc/prescreen.sh writes
# both).  checks.tsv declares the checks.  All run one JDK 8 tree, the one
# the file `tree` names (gc/hdfs-unified), as it is written:
# tools/adhoc/targets.py writes targets/, each check's class and throw line.
# The target occurrence is the one occurrences.tsv names, else the first
# observed occurrence of the check in the campaign's own recording.
# DataXceiver is never woven.  Coverage counts the whole JVM, set-up before
# the recording window included; only a recording says the window reaches a
# check (the PacketResponder seqno check ran only for mirror's pre-window
# client write: the window's DataNode transfer starts no responder).
if [[ "$1" =~ ^B[0-9]+$ ]]; then
  batch=$(awk -F'\t' -v b="$1" '$1 == b' "${here}/batches.tsv")
  [[ -n "${batch}" ]] || { echo "unknown batch: $1" >&2; return 2; }
  IFS=$'\t' read -r _ workload checks <<<"${batch}"
  target_spec=${here}/targets/$1.yaml
else
  checks=${1%%.*}
  workload=${1#*.}
  [[ -n "${checks}" && "${workload}" != "$1" ]] || {
    echo "usage: case.sh <check>.<workload>|B<n>" >&2
    return 2
  }
  target_spec=${here}/targets/${checks}.yaml
fi
read -r repo <"${here}/tree"
# Every test of the module runs on one classpath, which any of its surefire
# reports states.
classpath_test=$(cd "${repo}/hadoop-hdfs-project/hadoop-hdfs/target/surefire-reports" \
  2>/dev/null && ls TEST-*.xml 2>/dev/null | sed -n '1{s/^TEST-//; s/\.xml$//; p}')
target_occurrence=$(awk -F'\t' -v c="$1" '$1 == c {print $2}' \
  "${here}/occurrences.tsv")
target_occurrence=${target_occurrence:-first}
# The mappings' classes (system.sh), and each check's own class; the scope
# grows from there to what the slice needs (SEED, `slice`), and the library
# doors' classes join it by themselves (ScopeGrowth --doors).
scope=("${system_mapping_scope[@]}")
for check in ${checks}; do
  row=$(awk -F'\t' -v c="${check}" '$1 == c' "${here}/checks.tsv")
  [[ -n "${row}" ]] || { echo "unknown ad-hoc check: ${check}" >&2; return 2; }
  IFS=$'\t' read -r _ _ _ own _ <<<"${row}"
  scope+=("${own}")
done
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
  *-*)
    test_method=${workload#*-}
    test_class=$(cd "${repo}/hadoop-hdfs-project/hadoop-hdfs/target/test-classes" \
      && find . -name "${workload%%-*}.class" | sed 's#^\./##; s#\.class$##; s#/#.#g')
    [[ -n "${test_class}" && "${test_class}" != *$'\n'* ]] || {
      echo "no single test class ${workload%%-*} in ${repo}" >&2
      return 2
    }
    workload_properties=(-Dcausynth.cluster.automatic=true)
    scope+=(client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  *)
    echo "unknown ad-hoc workload: ${workload}" >&2
    return 2
    ;;
esac
