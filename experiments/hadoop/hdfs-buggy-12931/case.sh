repo=${GC_TREES}/hadoop-hdfs-bug-12931
test_class=org.apache.hadoop.hdfs.TestCausynthReplicatedChecksum
test_method=testStaleEncryptionKeyFailsReplicatedChecksum
target_occurrence="hdfs-12931/dn0#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-12931/client#epoch0/replicated-file-checksum#1"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
