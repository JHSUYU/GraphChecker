# Known ZooKeeper coordination bugs (~/bug_study/ZooKeeper.txt), on one
# branch-3.9 tree that marks each bug's target throw.  Declarations only.
repo=/bigtemp/vnr3ne/wt/zookeeper-unified
case "${1:?usage: case.sh quota-init|election-offer}" in
  quota-init)
    # Bug 01: SetQuotaCommand.createQuota commits the limit node, then
    # creates the stat node in a request of its own.  A fault at the limit's
    # create (ZOOKEEPER WRITE door: the write happened, the client sees
    # ConnectionLoss) leaves no stat; the client's retry finds the limit,
    # takes the update branch and reads the stat: the server's NoNode guard.
    # The workload is the tree's own (owner-approved): a client sets a hard
    # quota retrying on ConnectionLoss, raises it, and the server enforces it.
    test_class=org.apache.zookeeper.test.CausynthQuotaRetryTest
    test_method=raisesARetriedHardQuota
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      server:org/apache/zookeeper/cli/SetQuotaCommand
      server:=org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  election-offer)
    # Bug 05: LeaderElectionSupport.determineElectionStatus lists the offers,
    # then reads each (toLeaderOffers); a competitor's stop() deleting its
    # offer in between makes the read hit the server's NoNode guard -- the
    # server's lookup of the offer paired with the delete.
    zk_module=zookeeper-recipes/zookeeper-recipes-election
    test_class=org.apache.zookeeper.recipes.leader.LeaderElectionSupportTest
    test_method=testNodes3
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      election:org/apache/zookeeper/recipes/leader/LeaderElectionSupport
      server:=org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  *)
    echo "unknown ZooKeeper bug case: $1" >&2
    return 2
    ;;
esac
