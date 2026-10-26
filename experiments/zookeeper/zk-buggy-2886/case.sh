repo=${GC_TREES}/zookeeper-bug-2886
# zk-buggy-2886 (ZOOKEEPER-2886, point zk-adhoc-02; README.md): the old connection issues only multis (create, then two setData)
# while it owns the session; a takeover thread, started before the old multis with no happens-before from them, sleeps 5 s
# and opens a second handle on another server with the same session (its REVALIDATE sets session.owner to that
# server's LearnerHandler). Natively no SessionMoved fires. The target is the second old multi (on a thread of its own,
# a hold point for CONFIRM), whose checkSession (SessionTrackerImpl:367) throws once its session.owner read is paired
# with the takeover's setOwner. No scope growth (workflow.properties): G's connect handling stays the client's role
# occurrence, so the takeover's REVALIDATE write reaches a ROOT and COMPOSE can offer it.
test_class=org.apache.zookeeper.test.CausynthSessionMoved2886Test
test_method=aMovedMultiOnlyConnectionKeepsThrowing
# the old connection's second multi setData at the leader (peer5, the deterministic highest-id leader): its
# forwarded Prep (REGION.3cfb4ed2), the 3rd occurrence -- #1 the multi create, #2 the first multi setData, #3
# the second multi setData, the second SessionMoved on the never-closed multi-only connection (as zk-buggy-710)
target_occurrence="auto0/peer5#epoch0/region/REGION.3cfb4ed2-6604-303b-82a1-6cb936dd8da0#3"
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
