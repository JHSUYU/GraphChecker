repo=${GC_TREES}/hadoop-hdfs-study-r7
case "${1:?usage: case.sh slowdisk-zero}" in
  slowdisk-zero)
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthSlowDiskZeroMax
    test_method=testAllSsdWriteAfterSlowDiskExclusionTurnedOff
    target_occurrence=first
    scope=(
      hdfs:org/apache/hadoop/hdfs/server/datanode/fsdataset/RoundRobinVolumeChoosingPolicy
      hdfs:org/apache/hadoop/hdfs/server/datanode/fsdataset/impl/FsVolumeList
      hdfs:org/apache/hadoop/hdfs/server/datanode/metrics/DataNodeDiskMetrics
      hdfs=:org/apache/hadoop/hdfs/server/datanode/DataNode)
    ;;
  *)
    echo "unknown HDFS bug-study case: $1" >&2
    return 2
    ;;
esac
