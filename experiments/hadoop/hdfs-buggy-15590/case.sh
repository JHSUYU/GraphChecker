repo=${GC_TREES}/hadoop-hdfs-bug-15590
test_class=org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion
test_method=testOrderedDeletionWithRestart
target_occurrence="hdfs-17960/nn0#epoch1/region/REGION.9492ec77-0f65-34ba-a3af-14753ac7347d#2"
scope=(
  common:org/apache/hadoop/ipc/Client
  common:org/apache/hadoop/ipc/Server
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSDirSnapshotOp
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSDirectory
  hdfs:org/apache/hadoop/hdfs/server/namenode/INodeDirectory
  hdfs:org/apache/hadoop/hdfs/server/namenode/NameNodeRpcServer
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/DirectorySnapshottableFeature
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/Snapshot
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/SnapshotManager
  hdfs:org/apache/hadoop/hdfs/util/ReadOnlyList
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
