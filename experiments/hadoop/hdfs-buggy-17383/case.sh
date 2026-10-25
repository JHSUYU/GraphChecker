repo=${GC_TREES}/hadoop-hdfs-bug-17383
test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthStandbyCurrentKey
test_method=testTransferAfterStandbyKeyUpdate
target_occurrence=first
scope=(
  common:org/apache/hadoop/ipc/Client
  common:org/apache/hadoop/security/token/delegation/DelegationKey
  client:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/DataTransferSaslUtil
  client:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferClient
  client:org/apache/hadoop/hdfs/security/token/block/DataEncryptionKey
  client:org/apache/hadoop/hdfs/protocolPB/PBHelperClient
  hdfs:org/apache/hadoop/hdfs/protocol/datatransfer/sasl/SaslDataTransferServer
  hdfs:org/apache/hadoop/hdfs/protocolPB/PBHelper
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockKey
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockPoolTokenSecretManager
  hdfs:org/apache/hadoop/hdfs/security/token/block/BlockTokenSecretManager
  hdfs:org/apache/hadoop/hdfs/security/token/block/ExportedBlockKeys
  hdfs:org/apache/hadoop/hdfs/server/datanode/BPOfferService
  hdfs=:org/apache/hadoop/hdfs/server/datanode/DataNode
)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
export CAUSYNTH_REGION_PATH_MAX_TASKS=128
