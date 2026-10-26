repo=${GC_TREES}/hadoop-hdfs-bug-14075
test_class=org.apache.hadoop.hdfs.server.namenode.TestCausynthRollSegmentFailure
test_method=testNextRollAfterFailedStartLogSegment
target_occurrence=first
scope=(
  common:org/apache/hadoop/ipc/Client
  hdfs=:org/apache/hadoop/hdfs/server/namenode/FSEditLog
  hdfs:org/apache/hadoop/hdfs/server/namenode/JournalSet
  hdfs:org/apache/hadoop/hdfs/server/namenode/NameNodeResourcePolicy
  hdfs:org/apache/hadoop/hdfs/server/namenode/FileJournalManager
  hdfs:org/apache/hadoop/hdfs/server/namenode/EditLogFileOutputStream
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
export CAUSYNTH_REGION_PATH_MAX_TASKS=128
