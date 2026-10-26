repo=${GC_TREES}/zookeeper-bug-2886
# zk-buggy-2886 (ZOOKEEPER-2886, point zk-adhoc-02): the multi-only shape of ZOOKEEPER-710. A multi's
# SessionMoved stays a per-op ErrorResult, so ZOOKEEPER-710's connection teardown never runs for a multi; the
# multi-only old connection keeps getting SessionMoved. The old connection issues only multi ops while it owns
# the session; a second handle on another server then takes it over. The recording keeps both multis ahead of
# the late REVALIDATE's setOwner, so no SessionMoved fires natively. GraphChecker re-pairs the two multis' reads
# of session.owner to the late setOwner: the first multi throws at SessionTrackerImpl.checkSession (:367) and --
# the bug keeping the connection open -- the second throws there again. The target is that second throw.
test_class=org.apache.zookeeper.test.CausynthSessionMoved2886Test
test_method=aMovedMultiOnlyConnectionKeepsThrowing
target_occurrence=first
scope=(
  server:org/apache/zookeeper/server/SessionTrackerImpl
  server:org/apache/zookeeper/server/quorum/LeaderSessionTracker
  server:org/apache/zookeeper/server/quorum/Leader
  server:org/apache/zookeeper/server/quorum/LearnerHandler
  server:org/apache/zookeeper/server/PrepRequestProcessor
)
client_fault_transports=(ZK_QUORUM)
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2
export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20
zk_jvm_properties=(-Dcausynth.confirm.order.timeout.ms=120000)
