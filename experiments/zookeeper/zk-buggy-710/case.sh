repo=${GC_TREES}/zookeeper-bug-710
# zk-buggy-710 (ZOOKEEPER-710, point zk-adhoc-02; README.md): the old connection creates and writes twice
# while it owns the session; a takeover thread, started before the old writes with no happens-before from them, sleeps 5 s
# and opens a second handle on another server with the same session (its REVALIDATE sets session.owner to that
# server's LearnerHandler). Natively no SessionMoved fires. The target is the second old write (on a thread of its own,
# a hold point for CONFIRM), whose checkSession (SessionTrackerImpl:367) throws once its session.owner read is paired
# with the takeover's setOwner. No scope growth (workflow.properties): G's connect handling stays the client's role
# occurrence, so the takeover's REVALIDATE write reaches a ROOT and COMPOSE can offer it.
test_class=org.apache.zookeeper.test.CausynthSessionMoved710Test
test_method=aMovedConnectionKeepsThrowing
# the old connection's second setData at the leader (peer5 is the leader deterministically, highest id):
# its leader-side forwarded Prep (REGION.3cfb4ed2, submitLearnerRequest path), the 3rd occurrence of that
# region -- #1 the create of /sm710, #2 the first setData, #3 the second setData. The second setData is the
# second SessionMoved on the never-closed connection: the bug's occurrence (SEED ZS1-buggy-710)
target_occurrence="auto0/peer5#epoch0/region/REGION.3cfb4ed2-6604-303b-82a1-6cb936dd8da0#3"
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
