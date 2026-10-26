repo=${GC_TREES}/hadoop-hdfs-bug-14075
test_class=org.apache.hadoop.hdfs.server.namenode.TestCausynthRollSegmentFailure
test_method=testNextRollAfterFailedStartLogSegment
target_occurrence="roll/client0#epoch0/region/REGION.08181728-581c-34d3-a3b3-c56c8c745343/ctx:Root:CLIENT/roll-2#1/idx:<org.apache.hadoop.hdfs.server.namenode.FSEditLog: long rollEditLog(int)>@0/<org.apache.hadoop.hdfs.server.namenode.FSEditLog: void endCurrentLogSegment(boolean)>@0"
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
