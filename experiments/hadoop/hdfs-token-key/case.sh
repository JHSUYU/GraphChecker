# The block-token variant of the key family: a DataNode that missed a
# KeyUpdateCommand (the heartbeat response lost after the NameNode applied the
# rotation) rejects a block token the NameNode signed with a key it no longer
# resends.  Same workload and tree as hdfs-17897; the anchor is the token
# check, BlockTokenSecretManager#retrievePassword's missing-key InvalidToken.
repo=/u/vnr3ne/hadoop-hdfs-17897
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
# Empty: PLAN lists every observed occurrence of the target.  Not in scope:
# DataXceiver -- its run() would be the region, opened before the SASL
# handshake names the connection's cause, so two connections share one Lost
# address (OCCURRENCE_ADDRESS_SHARED, t1).
target_occurrence=
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
)
