repo=${GC_TREES}/hadoop-hdfs-bug-10609
test_class=org.apache.hadoop.hdfs.TestCausynthEncryptedAppendTransfer
test_method=testStaleEncryptionKeyFailsAppendTransfer
target_occurrence="hdfs-10609/dn0#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-10609/client#epoch0/append-block#1"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/DataStreamer
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
