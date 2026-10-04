# HDFS bug-study cases on one tree, gc/hdfs-study (gc/hdfs-unified-dtx plus
# each case's workload and target marker, and the study checks' markers of
# experiments/hadoop/hdfs-adhoc).  Declarations only.
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next
case "${1:?usage: case.sh slowdisk-zero}" in
  # Bug study #15: DataNodeDiskMetrics' detector publishes the top slow disks
  # only while dfs.datanode.max.slowdisks.to.exclude is positive, so a list
  # published before a reconfiguration to 0 ("exclude nothing") stays, and
  # FsVolumeList keeps filtering the volume chooser by it.  The workload
  # flags the only SSD slow, turns exclusion off at once, and writes an
  # ALL_SSD file a few detector turns later; a detector turn that read the
  # value from before the reconfiguration leaves the write no SSD volume.
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
