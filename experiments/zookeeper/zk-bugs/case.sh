repo=${GC_TREES}/zookeeper-checks
# The ZooKeeper bug checks (docs/checks/ZOOKEEPER.md §E). A target occurrence is read off a STOP_AFTER=SEED run on the
# built tree (DECLARED_TARGET_OCCURRENCE_UNOBSERVED lists every observed occurrence; the seed's
# runtime/concolic_region_plan.jsonl marks the resolved one `declaredOccurrence`) and written here; the final series'
# F0 seeds checked each on the final pair (lead/final/PLAN.md). The getData target's region is FinalRequestProcessor#processServed (the adapter's
# split of processRequest); each selector below names the request occurrence the 2026-10-03 PASS declared (V25: the same
# request anchors, read off SEEDs ZA1-quota and ZA1-offer).
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0
case "${1:?usage: case.sh quota-init|election-offer|container-reuse|retry-seq-quota|trunc-sync|observer-master}" in
  quota-init)
    # the pasted bug 2: createQuota's two RPCs, a lost reply between them, the retry's getData(stat) NoNode
    # Claims: COMPOSE's recorded valuation pairs the target read with writes the synchronous caller made before it
    # (TODO HBase 15's F4), CONFIRM refutes each by the client's program order at the order timeout, and the fault world
    # comes after them: 20 claims, and an order timeout of 2x the slowest replay (56 s, ZA3-quota) for CONFIRM's holds.
    export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20
    zk_jvm_properties=(-Dcausynth.confirm.order.timeout.ms=120000)
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
    # Claims as quota-init's (ZA3/ZA4-offer: pairings refuted by the client's program order before the real one)
    export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20
    zk_jvm_properties=(-Dcausynth.confirm.order.timeout.ms=120000)
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
    # The workload widens the cleanup's scan-to-post window (its worker posts the deletion 3 s after the scan), so the
    # race -- the cleanup posting after the replacement's create -- happens natively: the client's delete, create and
    # getData run inside the window and the cleanup deletes the replacement after the read. The bug's world is the
    # read order that exposes the deleted replacement: getData paired with the cleanup's remove (depth 0). Without the
    # window the world needs the client's delete to succeed, a write no depth-0 session holds, and at depth 1 EXPLORE
    # cannot re-pair the node-map lookup that decides it (FlipQuery#movableReads skips container reads; ZA15-cont).
    # 20 claims; a CONFIRM order timeout of 2x its seed replay (71 s, ZA5-cont).
    export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20
    zk_jvm_properties=(-Dcausynth.confirm.order.timeout.ms=150000)
    test_class=org.apache.zookeeper.server.CausynthContainerReuseTest
    test_method=keepsTheReplacementOfACleanedContainer
    target_occurrence="auto0/server0#epoch0/region/REGION.ce9149ce-ad44-3ad7-b99b-58659d47dae2#1"  # its one getData (ZA17-contfb)
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
    # The second sequential create's checkQuota (the two observed occurrences of the count guard, ZA6-rseq; both stand
    # on the retrying client's CONNECT anchor in Prep, numbered by the throttler's items: reported to the quorum cluster)
    target_occurrence="auto0/server0#epoch0/region/REGION.3cfb4ed2-6604-303b-82a1-6cb936dd8da0#2"
    scope=(
      inspector:org/apache/zookeeper/retry/ZooKeeperRetry
      server:org/apache/zookeeper/server/PrepRequestProcessor
      server=:org/apache/zookeeper/server/ZooKeeperServer
      server=:org/apache/zookeeper/server/DataTree
    )
    ;;
  trunc-sync)
    # ZOOKEEPER-5094 (apache/zookeeper PR 2459): a follower whose TRUNC sync ends before NEWLEADER keeps its database;
    # its restart's replay throws at ZKDatabase.addCommittedProposal. It runs on the quorum adapter and the learner-stream door (STATUS "Per-system surface").
    # Workload: tree gc/zk-quorum-bugs, CausynthQuorumHarness's held ACKs and one paused startForwarding; the test waits
    # on what the leader sees (docs/checks/ZOOKEEPER.md §E).
    # World depth 1 (lead 2026-10-21, owner: several counterfactuals are fine): the follower's second life, whose TRUNC sync's
    # NEWLEADER read is the FAULT, enters the closure only as an exposure, recorded in the re-run of a flipped world, so its
    # FAULT is a second counterfactual on top of that flip (ZB13-trunc: depth 0 cut every such path).
    export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=1
    test_class=org.apache.zookeeper.server.quorum.CausynthTruncSyncTest
    test_method=aTruncSyncedFollowerRestarts
    # F's third life's construction (runFromConfig; its replay's addCommittedProposal folds into it), SEED ZB4-trunc
    target_occurrence="auto0/peer1#epoch2/region/REGION.98b8e38a-d414-366b-972d-5bccb78d80a7#1"
    scope=(
      server=:org/apache/zookeeper/server/ZKDatabase
      server=:org/apache/zookeeper/server/quorum/Learner
      server:org/apache/zookeeper/server/quorum/QuorumPeer
      server=:org/apache/zookeeper/server/quorum/LearnerHandler
      # the restart replay's start after the snapshot (fastForwardFromEdits) and the log iterator it reads (FileTxnIterator)
      server=:org/apache/zookeeper/server/persistence/FileTxnSnapLog
      server:org/apache/zookeeper/server/persistence/FileTxnLog
    )
    ;;
  observer-master)
    # ZOOKEEPER-5088 (apache/zookeeper PR 2454): a proposal pending at an ObserverMaster follower's sync never reaches the
    # OM's queue, no INFORM is sent, the observer throws at ZKDatabase.addCommittedProposal. It runs on the quorum adapter, the learner door and its txn headers.
    # Workload: tree gc/zk-quorum-bugs, CausynthQuorumHarness's held ACKs; the test restarts the observer after the
    # pending create's reply (docs/checks/ZOOKEEPER.md §E).
    test_class=org.apache.zookeeper.server.quorum.CausynthObserverMasterSyncTest
    test_method=aProposalPendingAtTheObserverMastersStart
    # the observer's second life's CommitProcessor.run (its applies, the follow-up INFORM's), SEED ZB4-om
    target_occurrence="auto0/peer4#epoch1/region/REGION.140fb26c-dd61-31ad-a4df-3417de43228b#1"
    # PLAN admits the writers of the reads deciding the observer master's resend (syncFollower's lastProcessedZxid: F's
    # own apply, another CommitProcessor.run activation, its DataTree a decoded snapshot) as dependencies (lead 2026-10-21,
    # owner: 5088 may be ad hoc; STATUS "case: zk-bugs-observer-master's export-guard writers")
    export_guard_writers=true
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
