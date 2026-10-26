repo=${GC_TREES}/hadoop-hdfs-bug-5766
test_class=org.apache.hadoop.hdfs.TestCausynthEncryptedPread
test_method=testStaleEncryptionKeyFailsPread
target_occurrence="hdfs-5766/dn0#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-5766/client#epoch0/encrypted-pread#1"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/DFSInputStream
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
