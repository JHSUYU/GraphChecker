# HDFS-11741: the balancer presents an expired cached block key.
# Declarations only; lib/ runs them (lib/run.sh <this dir> "" <command>).
repo=/bigtemp/vnr3ne/wt/hadoop-hdfs-11741-r5
test_class=org.apache.hadoop.hdfs.server.balancer.TestCausynthExpiredBalancerKey
test_method=testEncryptedBalancerAfterKeyRotations
target_occurrence="hdfs-11741/dn1#epoch0/region/REGION.7c569c3f-b4d3-305a-bd9c-bebff1048122@hdfs-11741/balancer#epoch0/balance-block#1"
# 11741 never woven ipc/Client; the shared family minus it, plus the balancer.
scope=()
for entry in "${blockkey_scope[@]}"; do
  [[ "${entry}" == common:org/apache/hadoop/ipc/Client ]] || scope+=("${entry}")
done
scope+=(
  hdfs:org/apache/hadoop/hdfs/server/balancer/KeyManager
  hdfs:org/apache/hadoop/hdfs/server/balancer/Dispatcher
  hdfs:org/apache/hadoop/hdfs/server/balancer/Balancer
)
