# HDFS bug-study cases on one tree, gc/hdfs-study (gc/hdfs-unified-dtx plus
# each case's workload and target marker, and the study checks' markers of
# experiments/hadoop/hdfs-adhoc).  Declarations only.
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study
case "${1:?usage: case.sh slowdisk-zero|reencrypt-negative-sleep}" in
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
  # Bug study HDFS-2 #09: ReencryptionHandler's throttle (handler ratio
  # below 1.0) reads its all-time stopwatch twice, and the second reading
  # can make the sleep negative; Thread.sleep throws, the handler's run
  # returns, and the zone stays Processing, so every later START of it is
  # refused as "already submitted" until the NameNode restarts.  The
  # workload re-encrypts a ten-file zone in batches of five at ratio 0.5,
  # waits for it, and starts it again.
  reencrypt-negative-sleep)
    test_class=org.apache.hadoop.hdfs.server.namenode.TestCausynthReencryptNegativeSleep
    test_method=testReencryptAgainAfterThrottledReencryption
    # The second START: the one the first re-encryption's dead handler
    # would refuse (round HS1's recording: the first START is #1).
    target_occurrence="reencrypt/nn0#epoch0/region/REGION.8d993f8d-eed1-3457-a797-d073191c4fc5#2"
    scope=(
      hdfs:org/apache/hadoop/hdfs/server/namenode/ReencryptionHandler
      hdfs:org/apache/hadoop/hdfs/server/namenode/FSTreeTraverser
      hdfs:org/apache/hadoop/hdfs/server/namenode/ReencryptionUpdater
      hdfs:org/apache/hadoop/hdfs/server/namenode/EncryptionZoneManager
      hdfs:org/apache/hadoop/hdfs/server/namenode/FSDirEncryptionZoneOp
      client:org/apache/hadoop/hdfs/protocol/ReencryptionStatus
      client:org/apache/hadoop/hdfs/protocol/ZoneReencryptionStatus
      common:org/apache/hadoop/util/StopWatch
      common:org/apache/hadoop/util/Timer)
    ;;
  *)
    echo "unknown HDFS bug-study case: $1" >&2
    return 2
    ;;
esac
