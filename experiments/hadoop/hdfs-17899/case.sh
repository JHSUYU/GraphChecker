#!/usr/bin/env bash

case_id=${1:?usage: case.sh bug1|bug2|bug3}
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
    ;;
  bug3)
    repo=/opt/hadoop-hdfs-17899-bug3
    test_class=org.apache.hadoop.hdfs.server.datanode.TestCausynthDataTransferRpcFailure
    test_method=testReplicationAfterModeledKeyRefreshRpcFailure
    ;;
  *)
    echo "unknown HDFS-17899 case: ${case_id}" >&2
    return 2 2>/dev/null || exit 2
    ;;
esac

module=${repo}/hadoop-hdfs-project/hadoop-hdfs
report=${module}/target/surefire-reports/TEST-${test_class}.xml
analysis=/tmp/graphchecker-hdfs-17899-${case_id}-classes
test_name=${test_class}#${test_method}
