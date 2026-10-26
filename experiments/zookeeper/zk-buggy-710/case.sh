repo=${GC_TREES}/zookeeper-bug-710
# zk-buggy-710 (ZOOKEEPER-710, point zk-adhoc-02): the old connection keeps getting SessionMoved after the
# session moved, because FinalRequestProcessor no longer tears the connection down. The old connection creates
# and writes twice while it owns the session; a second handle on another server then takes it over. The
# recording keeps both writes ahead of the late REVALIDATE's setOwner, so no SessionMoved fires natively.
# GraphChecker re-pairs the two writes' reads of session.owner to the late setOwner: the first write throws at
# SessionTrackerImpl.checkSession (:367) and -- the bug staying open -- the second throws there again, which on
# the fixed tree the first throw's connection teardown would have prevented. The target is that second throw.
test_class=org.apache.zookeeper.test.CausynthSessionMoved710Test
test_method=aMovedConnectionKeepsThrowing
target_occurrence=first
scope=(
  server:org/apache/zookeeper/server/SessionTrackerImpl
  server:org/apache/zookeeper/server/quorum/LeaderSessionTracker
  server:org/apache/zookeeper/server/quorum/Leader
  server:org/apache/zookeeper/server/quorum/LearnerHandler
  server:org/apache/zookeeper/server/PrepRequestProcessor
)
# the mechanism is the session.owner re-pairing, so the workload client's ZOOKEEPER doors do not fail -- a
# transport this client never relies on, as zk-adhoc-02's case.sh cuts
client_fault_transports=(ZK_QUORUM)
# two re-pairings of session.owner: the first write's and the second write's reads both to the late setOwner
export CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2
export CAUSYNTH_CAMPAIGN_MAX_CLAIMS=20
zk_jvm_properties=(-Dcausynth.confirm.order.timeout.ms=120000)
