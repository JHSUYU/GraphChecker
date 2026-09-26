# The block-token variant of the key family: a DataNode that missed a
# KeyUpdateCommand (the heartbeat response lost after the NameNode applied the
# rotation) rejects a block token the NameNode signed with a key it no longer
# resends.  Same workload and tree as hdfs-17897; the anchor is the token
# check, BlockTokenSecretManager#retrievePassword's missing-key InvalidToken.
repo=/u/vnr3ne/hadoop-hdfs-17897
test_class=org.apache.hadoop.hdfs.TestCausynthStripedChecksum
test_method=testStaleEncryptionKeyFailsStripedChecksum
# The first observed occurrence of the token check (t2).  Not in scope:
# DataXceiver -- its run() would be the region, opened before the SASL
# handshake names the connection's cause, so two connections share one Lost
# address (OCCURRENCE_ADDRESS_SHARED, t1).
target_occurrence="hdfs-17897/dn0#epoch0/region/REGION.7f08d6f5-b1ef-323d-8084-ce44a2259712/ctx:Root:DATA_XCEIVER#1/idx:<org.apache.hadoop.hdfs.security.token.block.BlockPoolTokenSecretManager: void checkAccess(org.apache.hadoop.security.token.Token,java.lang.String,org.apache.hadoop.hdfs.protocol.ExtendedBlock,org.apache.hadoop.hdfs.security.token.block.BlockTokenIdentifier\$AccessMode,org.apache.hadoop.fs.StorageType[],java.lang.String[])>@0"
scope=("${blockkey_scope[@]}"
  client:org/apache/hadoop/hdfs/DFSClient
  client:org/apache/hadoop/hdfs/FileChecksumHelper
)
