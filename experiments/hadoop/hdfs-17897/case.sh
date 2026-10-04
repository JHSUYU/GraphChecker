# HDFS-17897: the client's cached data-encryption key is rejected by the
# striped block-group checksum leader.  Declarations only.
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
target_occurrence="hdfs-17897/dn0#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-17897/client#epoch0/striped-file-checksum#1"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
)
