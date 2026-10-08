# Known ZooKeeper coordination bugs (~/bug_study/ZooKeeper.txt), on one
# branch-3.9 tree that marks each bug's target throw.  Declarations only.
repo=${GC_TREES}/zookeeper-unified
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
    # The server answers six getData requests at the guard: per quota call
    # the child-quota walk's read of the quota path (the first call's finds
    # no node: a NoNode the walk expects), then the limit and the stat.  The
    # question is the stat read of the call that takes the update branch,
    # the sixth: the retry of a call whose limit create failed reads it at
    # this address too (createQuota's second entry, its second getData).
    target_occurrence="auto0/server0#epoch0/region/REGION.860d3eb6-a432-3c9e-87a7-161a28678252#6"
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      server:org/apache/zookeeper/cli/SetQuotaCommand
      server=:org/apache/zookeeper/server/DataTree
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
    # The question: the server's second getData of an offer.  Each of the
    # three contenders lists the offers and reads them in the list's order
    # (n_0, n_1, n_2), so the first two reads are of n_0, by its creator
    # first, then by a competitor whose read its creator's stop() can race.
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
