# HDFS-17960: ordered snapshot deletion miscounts after a restart.
# Declarations only.
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-r7
test_class=org.apache.hadoop.hdfs.server.namenode.snapshot.TestOrderedSnapshotDeletion
test_method=testOrderedDeletionWithRestart
target_occurrence="hdfs-17960/nn0#epoch1/region/REGION.5cf88831-22cf-3d39-88b2-258261af8fc8#1"
scope=(
  common:org/apache/hadoop/ipc/Client
  common:org/apache/hadoop/ipc/Server
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSEditLogLoader
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSDirSnapshotOp
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSDirectory
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSImage
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSImageFormatProtobuf
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/FSImageFormatPBSnapshot
  hdfs:org/apache/hadoop/hdfs/server/namenode/FSNamesystem
  hdfs:org/apache/hadoop/hdfs/server/namenode/INodeDirectory
  hdfs:org/apache/hadoop/hdfs/server/namenode/NameNodeRpcServer
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/DirectorySnapshottableFeature
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/Snapshot
  hdfs:org/apache/hadoop/hdfs/server/namenode/snapshot/SnapshotManager
  hdfs:org/apache/hadoop/hdfs/util/ReadOnlyList
)
