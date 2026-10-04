# HDFS-17899: three paths to a stale block key.  Declarations only.
case "${1:?usage: case.sh bug1|bug2|bug3}" in
  bug1)
    repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next
    test_class=org.apache.hadoop.hdfs.server.balancer.TestCausynthBalancerCachedKey
    test_method=testBlockMoveWithCachedKeyAfterRotations
    target_occurrence="hdfs-17899/target-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-17899/balancer#epoch0/balance-block#1"
    scope=("${blockkey_scope[@]}"
      hdfs:org/apache/hadoop/hdfs/server/balancer/KeyManager
      hdfs:org/apache/hadoop/hdfs/server/datanode/BPOfferService
      hdfs:org/apache/hadoop/hdfs/server/datanode/DataNode)
    ;;
  bug2)
    repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next
    test_class=org.apache.hadoop.hdfs.server.sps.TestExternalStoragePolicySatisfier
    test_method=testCausynthSpsKeyRefreshRpcFailure
    target_occurrence="hdfs-17899/target-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-17899/sps#epoch0/satisfy-storage-policy#1"
    scope=("${blockkey_scope[@]}"
      hdfs:org/apache/hadoop/hdfs/server/balancer/KeyManager
      hdfs:org/apache/hadoop/hdfs/server/common/sps/BlockDispatcher
      hdfs:org/apache/hadoop/hdfs/server/sps/ExternalSPSBlockMoveTaskHandler
      hdfs:org/apache/hadoop/hdfs/server/namenode/sps/StoragePolicySatisfier)
    ;;
  bug3)
    repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-study-next
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthDataTransferRpcFailure
    test_method=testReplicationAfterModeledKeyRefreshRpcFailure
    loop_bounds=${here}/loop-bounds-datanode.jsonl
    target_occurrence="hdfs-17899/target-dn#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-17899/source-dn#epoch0/replicate-block#1"
    scope=("${blockkey_scope[@]}"
      hdfs:org/apache/hadoop/hdfs/server/datanode/BPOfferService
      hdfs:org/apache/hadoop/hdfs/server/datanode/DataNode)
    ;;
  *)
    echo "unknown HDFS-17899 case: $1" >&2
    return 2
    ;;
esac
