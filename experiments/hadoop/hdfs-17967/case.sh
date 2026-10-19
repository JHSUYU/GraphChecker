case "${1:?usage: case.sh pathA|pathB|pathC}" in
  pathA)
    repo=${GC_TREES}/hadoop-hdfs-study-r7
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthWriteBlockMirrorStaleKey
    test_method=testWritePipelineAfterKeyRotations
    target_occurrence="hdfs-17967/mirror-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
    scope=("${blockkey_scope[@]}" client:org/apache/hadoop/hdfs/DFSClient)
    ;;
  pathB)
    repo=${GC_TREES}/hadoop-hdfs-study-r7
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthReplaceBlockProxyStaleKey
    test_method=testBlockMoveAfterKeyRotations
    target_occurrence="hdfs-17967/proxy-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
    scope=("${blockkey_scope[@]}")
    ;;
  pathC)
    repo=${GC_TREES}/hadoop-hdfs-study-r7
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthStripedReconstructTargetStaleKey
    test_method=testReconstructionAfterKeyRotations
    target_occurrence="hdfs-17967/target-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122#1"
    ec=hdfs:org/apache/hadoop/hdfs/server/datanode/erasurecode
    scope=("${blockkey_scope[@]}"
      "${ec}/StripedWriter" "${ec}/StripedBlockWriter"
      "${ec}/StripedBlockReconstructor" "${ec}/StripedReconstructor"
      "${ec}/StripedReconstructionInfo" "${ec}/ErasureCodingWorker")
    ;;
  *)
    echo "unknown HDFS-17967 case: $1" >&2
    return 2
    ;;
esac
