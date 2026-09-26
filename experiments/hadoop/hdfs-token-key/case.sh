# The block-token variant of the key family: a DataNode that missed a
# KeyUpdateCommand (the heartbeat response lost after the NameNode applied the
# rotation) rejects a block token the NameNode signed with a key it no longer
# resends.  Same workload and tree as hdfs-17897; the anchor is the token
# check, BlockTokenSecretManager#retrievePassword's missing-key InvalidToken.
repo=/u/vnr3ne/hadoop-hdfs-17897
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
# The one occurrence PLAN observed (DataXceiver.run on dn0).
target_occurrence="hdfs-17897/dn0#epoch0/region/REGION.61e62f41-34c6-3a5d-b610-b639dc3f4838/ctx:Lost:UNKNOWN/idx:<org.apache.hadoop.hdfs.server.datanode.DataXceiver: void run()>@0"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
  hdfs=:org/apache/hadoop/hdfs/server/datanode/DataXceiver
)
