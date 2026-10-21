repo=${GC_TREES}/zookeeper-checks
# The ZooKeeper bug checks (docs/checks/ZOOKEEPER.md §E). Target occurrences marked "placeholder" are not known yet: read each
# off a STOP_AFTER=SEED run on the built tree (DECLARED_TARGET_OCCURRENCE_UNOBSERVED lists every observed occurrence;
# TODO ZooKeeper D9) and write it here. The getData target's region is FinalRequestProcessor#processServed (the adapter's
# split of processRequest); each selector below names the request occurrence the 2026-10-03 PASS declared (V25: the same
# request anchors, read off SEEDs ZA1-quota and ZA1-offer).
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
case "${1:?usage: case.sh quota-init|election-offer|container-reuse|retry-seq-quota|trunc-sync|observer-master}" in
  quota-init)
    # the pasted bug 2: createQuota's two RPCs, a lost reply between them, the retry's getData(stat) NoNode
    test_class=org.apache.zookeeper.test.CausynthQuotaRetryTest
    test_method=raisesARetriedHardQuota
    target_occurrence="auto0/server0#epoch0/region/REGION.ce9149ce-ad44-3ad7-b99b-58659d47dae2#6"
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      server:org/apache/zookeeper/cli/SetQuotaCommand
      server=:org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  election-offer)
    # the pasted bug 3: LeaderElectionSupport.start's getData NoNode on a vanished competitor -> FAILED, offer orphaned
    zk_module=zookeeper-recipes/zookeeper-recipes-election
    test_class=org.apache.zookeeper.recipes.leader.LeaderElectionSupportTest
    test_method=testNodes3
    target_occurrence="auto0/server0#epoch0/region/REGION.ce9149ce-ad44-3ad7-b99b-58659d47dae2#2"
    scope=(
      server:org/apache/zookeeper/server/FinalRequestProcessor
      election:org/apache/zookeeper/recipes/leader/LeaderElectionSupport
      server=:org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  container-reuse)
    # the pasted bug 4 (catalogue #33): the cleanup's DeleteContainerRequest(path) deletes the replacement at the path.
    test_class=org.apache.zookeeper.server.CausynthContainerReuseTest
    test_method=keepsTheReplacementOfACleanedContainer
    target_occurrence="auto0/server0#epoch0/region/REGION.ce9149ce-ad44-3ad7-b99b-58659d47dae2#1"  # its one getData (ZA1-cont)
    scope=(
      server:org/apache/zookeeper/server/ContainerManager
      server:org/apache/zookeeper/server/PrepRequestProcessor
      server:org/apache/zookeeper/server/FinalRequestProcessor
      server=:org/apache/zookeeper/server/DataTree
      server:org/apache/zookeeper/server/NodeHashMapImpl
    )
    ;;
  retry-seq-quota)
    # catalogue #32 (bug_study): ZooInspector's ZooKeeperRetry re-creates a sequential node after a lost reply; the hard
    # count quota then refuses the caller's next create (the module is in the reactor under -Pfull-build).
    zk_module=zookeeper-contrib/zookeeper-contrib-zooinspector
    zk_maven_profiles=(full-build)
    zk_jvm_properties=(-Dzookeeper.enforceQuota=true)
    test_class=org.apache.zookeeper.retry.CausynthZooKeeperRetryQuotaTest
    test_method=createsTwoSequentialChildrenUnderAHardQuota
    target_occurrence=first  # placeholder: read the real one off a SEED (D9)
    scope=(
      inspector:org/apache/zookeeper/retry/ZooKeeperRetry
      server:org/apache/zookeeper/server/PrepRequestProcessor
      server=:org/apache/zookeeper/server/ZooKeeperServer
      server=:org/apache/zookeeper/server/DataTree
    )
    ;;
  trunc-sync)
    # ZOOKEEPER-5094 (apache/zookeeper PR 2459): a follower whose TRUNC sync ends before NEWLEADER keeps its database;
    # its restart's replay throws at ZKDatabase.addCommittedProposal. Needs the quorum adapter (TODO ZooKeeper D3, D4).
    # Workload: tree gc/zk-quorum-bugs, CausynthQuorumHarness's held ACKs and one paused startForwarding
    # (docs/checks/ZOOKEEPER.md §E).
    test_class=org.apache.zookeeper.server.quorum.CausynthTruncSyncTest
    test_method=aTruncSyncedFollowerRestarts
    target_occurrence=first  # placeholder: read the real one off a SEED (D9)
    scope=(
      server=:org/apache/zookeeper/server/ZKDatabase
      server=:org/apache/zookeeper/server/quorum/Learner
      server:org/apache/zookeeper/server/quorum/QuorumPeer
      server=:org/apache/zookeeper/server/quorum/LearnerHandler
    )
    ;;
  observer-master)
    # ZOOKEEPER-5088 (apache/zookeeper PR 2454): a proposal pending at an ObserverMaster follower's sync never reaches the
    # OM's queue, no INFORM is sent, the observer throws at ZKDatabase.addCommittedProposal. Needs D3, D4, D5.
    # Workload: tree gc/zk-quorum-bugs, CausynthQuorumHarness's held ACKs; the test restarts the observer after the
    # pending create's reply (docs/checks/ZOOKEEPER.md §E).
    test_class=org.apache.zookeeper.server.quorum.CausynthObserverMasterSyncTest
    test_method=aProposalPendingAtTheObserverMastersStart
    target_occurrence=first  # placeholder: read the real one off a SEED (D9)
    scope=(
      server=:org/apache/zookeeper/server/ZKDatabase
      server=:org/apache/zookeeper/server/DataTree
      server=:org/apache/zookeeper/server/quorum/LearnerHandler
      server=:org/apache/zookeeper/server/quorum/ObserverMaster
    )
    ;;
  *)
    echo "unknown ZooKeeper bug case: $1" >&2
    return 2
    ;;
esac
