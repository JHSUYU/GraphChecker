#!/usr/bin/env bash

case_id=${1:?usage: case.sh bug1|bug2|bug3}
loop_bounds=${here}/loop-bounds.jsonl
# Which occurrence of the annotated site this case is about, as an
# occurrence address or as the request family and k.  The campaign is
# target-directed: it composes and judges the occurrence the case names and
# reports the others.  Left empty the run keeps every observed occurrence,
# which is what a recording that never took the fatal arm needs.
target_occurrence=
case "${case_id}" in
  bug1)
    repo=/opt/hadoop-hdfs-17899-bug1
    test_class=org.apache.hadoop.hdfs.server.balancer.TestBalancerWithEncryptedTransfer
    test_method=testEncryptedBalancer1
    ;;
  bug2)
    repo=/opt/hadoop-hdfs-17899-bug2
    test_class=org.apache.hadoop.hdfs.server.sps.TestExternalStoragePolicySatisfier
    test_method=testCausynthSpsKeyRefreshRpcFailure
    # The SPS asks the DataNode once; laneB2n observed exactly that one
    # occurrence of the annotated site.
    target_occurrence="hdfs-17899/sps#epoch0/satisfy-storage-policy#1"
    ;;
  bug3)
    repo=/opt/hadoop-hdfs-17899-bug3
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthDataTransferRpcFailure
    test_method=testReplicationAfterModeledKeyRefreshRpcFailure
    loop_bounds=${here}/loop-bounds-datanode.jsonl
    # One replication, one target DataNode read; laneVM23 observed exactly
    # that one occurrence of the annotated site.
    target_occurrence="hdfs-17899/source-dn#epoch0/replicate-block#1"
    ;;
  *)
    echo "unknown HDFS-17899 case: ${case_id}" >&2
    return 2
    ;;
esac

module=${repo}/hadoop-hdfs-project/hadoop-hdfs
report=${module}/target/surefire-reports/TEST-${test_class}.xml
analysis=/tmp/graphchecker-hdfs-17899-${case_id}-classes
test_name=${test_class}#${test_method}
