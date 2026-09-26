# FALSE-POSITIVE EXPERIMENT E1: hdfs-17897 without the two block-key WIRE flows
# (NameNode -> DataNode key id and expiry date), so the DataNode's received
# keys are constants in the model while the NameNode's stay symbolic.
repo=/u/vnr3ne/hadoop-hdfs-17897
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
target_occurrence="hdfs-17897/dn0#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-17897/client#epoch0/striped-file-checksum#1"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
)
