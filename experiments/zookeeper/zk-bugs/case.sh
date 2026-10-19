repo=${GC_TREES}/zookeeper-unified
case "${1:?usage: case.sh quota-init|election-offer}" in
  quota-init)
    test_class=org.apache.zookeeper.test.CausynthQuotaRetryTest
    test_method=raisesARetriedHardQuota
    target_occurrence="auto0/server0#epoch0/region/REGION.860d3eb6-a432-3c9e-87a7-161a28678252#6"
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      server:org/apache/zookeeper/cli/SetQuotaCommand
      server=:org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  election-offer)
    zk_module=zookeeper-recipes/zookeeper-recipes-election
    test_class=org.apache.zookeeper.recipes.leader.LeaderElectionSupportTest
    test_method=testNodes3
    target_occurrence="auto0/server0#epoch0/region/REGION.860d3eb6-a432-3c9e-87a7-161a28678252#2"
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      election:org/apache/zookeeper/recipes/leader/LeaderElectionSupport
      server=:org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  *)
    echo "unknown ZooKeeper bug case: $1" >&2
    return 2
    ;;
esac
