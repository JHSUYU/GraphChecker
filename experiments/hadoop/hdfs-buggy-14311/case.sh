repo=${GC_TREES}/hadoop-hdfs-bug-14311
test_class=org.apache.hadoop.hdfs.TestDFSUpgrade
test_method=testParallelVolumeUpgrade
target_occurrence=first
cluster_automatic=true
scope=(
  hdfs:org/apache/hadoop/hdfs/server/datanode/DataStorage
  hdfs:org/apache/hadoop/hdfs/server/datanode/BlockPoolSliceStorage
  hdfs:org/apache/hadoop/hdfs/server/common/Storage
  hdfs:org/apache/hadoop/hdfs/server/common/StorageInfo
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
export CAUSYNTH_REGION_PATH_MAX_TASKS=128
export CAUSYNTH_REPLAY_TIMEOUT_S=7200
