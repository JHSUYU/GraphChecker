<!-- Moved into the repo at the 2026-10-05 handover from /bigtemp/vnr3ne/analysis/study-2026-10-04/zookeeper.md (investigator tables of 2026-10-04, read against our trees). Ids never move. Live status per check: docs/checks/README.md and docs/handover/STATE.md. -->
# ZooKeeper: study.txt checks and bug_study additions (investigator, 2026-10-04)

Tree read: `/bigtemp/vnr3ne/wt/zookeeper-unified` (`gc/zk-unified` 8f18cf3a4, branch-3.9 plus the adapter). The study used
3.8.7. I mapped each site with `git show release-3.8.7:<file>` from `~/zookeeper`. Read-only: nothing was built or run.

**What GraphChecker can reach on ZooKeeper today** (adapter commit 8f18cf3a4, library catalog):
- Only `ClientBase` tests are wired. `CausynthZkCluster` registers a server only from `ClientBase.startServerInstance` and a
  client only from `createClient`. It also sets every session timeout to `NEVER_MS` = 6 h, so no session expires in a slow
  replay. Not wired: QuorumPeers, `QuorumBase`/`QuorumUtil`/`QuorumPeerTestBase.MainThread` ensembles, and clients made
  outside `createClient`.
- Messages: a client request is one message (`CausynthZk`), from `ClientCnxn.queuePacket` to Prep and then
  FinalRequestProcessor. Not wired: responses, watches, the ConnectRequest handshake and election (`QuorumCnxManager`)
  messages. The `zookeeper-hb` tree adds a RESPONSE door. On `gc/zk-learner` (2026-10-21) every Learner<->Leader
  `QuorumPacket` is a `ZK_QUORUM` message (`CausynthQuorum`, below).
- FAULT doors: `ZOOKEEPER WRITE` on `ZooKeeper#create` (both overloads), `#setData`, `#delete` and `#multiInternal`, placed
  after `submitRequest`. The write commits and the caller sees ConnectionLoss or SessionExpired (no OperationTimeout:
  no client code raises it, only `KeeperException`'s own classes name it). Reads,
  `setACL` and the election socket have no door; the learner stream's sync reads have one (`ZK_QUORUM READ`, below).
- CLOCK: `Time.currentElapsedTime` and `nanoTime`, with a forward window of up to 30 days. CONFIG: JVM getters such as
  `Integer.getInteger`, `Boolean.getBoolean` and `System.getProperty`+parse. ZooKeeper's `ZKConfig`/`QuorumPeerConfig`
  getters are not catalog rows.
- Standalone owner fact: in standalone mode every request's owner is the static `ServerCnxn.me` (ZooKeeperServer.java:1809),
  and so is the leader's own clients' owner (LeaderZooKeeperServer.java:303). A forwarded request's owner is the follower's
  `LearnerHandler` (LearnerHandler.java:710). So `SessionMovedException` can only fire in a quorum.

## A. study.txt items (all 13)

None of the sites is a `checkState` or an assert. Each marked site is a `throw new X(..)` line that takes
`throw new @CausynthExceptionTarget("zk-adhoc-NN") X(..)`. The one exception is 09: it is `throw e;` (a rethrow), so a marker
would need `throw new SessionExpiredException()`, but 09 is dropped anyway (NO_PATH).

| id | our file:line (zookeeper-server/src/main/java/org/apache/zookeeper/server/...) | kind | guard | coordination? | counterfactual that could flip it | IO ok? | test in our tree | fit |
|---|---|---|---|---|---|---|---|---|
| 01 | SessionTrackerImpl.java:317 | throw SessionExpired | `session.isClosing()` in `checkSession` | Y: the client's liveness (pings, touches forwarded by followers) vs the session tracker's expiry thread (deadline vs clock) | CLOCK on the session tracker's `ExpiryQueue` (`Time.currentElapsedTime` in `getWaitTime`/`poll`). It must pass the session's bucket, so it needs a skew of at least `NEVER_MS` = 6 h under the adapter. The poll loop then walks the empty buckets in one replay. A realistic stand-in is a long pause of the expiry thread. No STATE writer: `setSessionClosing` comes only from expiry, or from the session's own `closeSession` on the same Prep thread (HB) | yes | QuorumPeerMainTest#testQuorum (exists). The guard is also evaluated in every ClientBase test, e.g. CausynthQuotaRetryTest#raisesARetriedHardQuota | B |
| 02 | SessionTrackerImpl.java:323 | throw SessionMoved | `session.owner != owner` | Y: two connections or paths of one session (old vs new follower's LearnerHandler, or leader-direct) vs the leader's owner record | STATE re-pairing of `session.owner` (read in leader Prep `checkSession`) with the `setOwner` of the session's other path (REVALIDATE at Leader.java:1782, or LeaderZooKeeperServer.java:303). testQuorum never moves a session, so the guard is always false there. QuorumTest#testSessionMovedWithSynchronousSync moves a session: the old connection's request throws as designed, so the case must declare the new connection's occurrence. Standalone cannot throw | yes | testQuorum (exists, cannot throw); equivalent QuorumTest#testSessionMovedWithSynchronousSync | B |
| 03 | SessionTrackerImpl.java:330 | throw SessionExpired | `session == null \|\| session.isClosing()` in `setOwner` (createSession Prep, PrepRequestProcessor.java:583) | Y (weak): connection thread's `createSession` vs Prep's `setOwner` | Needs the session removed or closing between `createSession` (NIO worker, then queued to Prep: HB) and its Prep: only expiry within that gap (CLOCK, as 01) | yes | testQuorum; ClientBase equivalent as 01 | C |
| 04 | ZooKeeperServer.java:1537 | throw CloseRequestException (CLIENT_ZXID_AHEAD) | `connReq.lastZxidSeen > zkDb.dataTree.lastProcessedZxid` | Y: zxid the client saw at one server (carried in the ConnectRequest) vs a lagging peer's applied state | STATE re-pairing of the follower's `lastProcessedZxid` read (connection thread) with an older HB-concurrent apply write. testQuorum's clients are fresh ZooKeeper objects, so lastZxidSeen = 0 and the throw is impossible there. Needs the same client object reconnecting to another peer. In standalone the reply is unwired, so a witness would be false (CONFIRM refutes) | yes in quorum (a restarted peer's zxid comes from disk: no) | testQuorum (exists, cannot throw); candidate ReadOnlyModeTest#testSeekForRwServer (same client object moves from the RO peer to the RW peers) | C |
| 05 | quorum/Follower.java:102 | throw IOException | `newEpoch < self.getAcceptedEpoch()` after `registerWithLeader` | Y: the leader's epoch (in the LEADERINFO message) vs the follower's accepted epoch | None. `registerWithLeader` already throws at Learner.java:522 for a lower LEADERINFO epoch, or sets acceptedEpoch = newEpoch. The only writers of `acceptedEpoch` are this thread (Learner.java:514/532) and Leader.java:1476 when this peer leads. The throw needs a pre-1.0 leader whose first packet is NEWLEADER. The code itself says "this should never happen" | - | testQuorum | C: **throw is dead in our tree** |
| 06 | quorum/Leader.java:1515 | throw IOException | `ss.isMoreRecentThan(leaderStateSummary)` in `waitForEpochAck` | Y: the follower's (currentEpoch, lastZxid) in ACKEPOCH vs the elected leader's summary (election should prevent it) | None of our kinds. Both summaries come from each peer's disk state (fresh in testQuorum: 0/0) and cross the learner stream (ACKEPOCH) plus the election stream (votes). No door on either | the values come from disk: no | testQuorum | C |
| 07 | quorum/Learner.java:522 | throw IOException | LEADERINFO `newEpoch < acceptedEpoch` | Y: the leader's proposed epoch (computed from a quorum's FOLLOWERINFO) vs a learner's accepted epoch | Multi-step: needs a learner that accepted a higher epoch from an aborted round. `acceptedEpoch` of a restarted peer is read from a file. The epoch crosses FOLLOWERINFO/LEADERINFO with no door | no (restart reads `acceptedEpoch` file) | QuorumRestartTest#testRollingRestart (exists) | C |
| 08 | quorum/LearnerSessionTracker.java:174 | throw SessionExpired | `!isGlobalSession(sessionId)` after local UnknownSession | (local vs global session) | study NO_PATH | - | none | C (NO_PATH) |
| 09 | quorum/LearnerSessionTracker.java:191 | `throw e;` (rethrow, no `throw new`) | same, in `setOwner` | - | study NO_PATH | - | none | C (NO_PATH) |
| 10 | quorum/ObserverMaster.java:371 | throw RuntimeException | head of `proposedPkts` zxid != committed zxid (smaller) | Y: the leader's PROPOSAL/COMMIT order (stream) vs the follower's observer-master queue | None. Writer (`proposalReceived`) and reader (`proposalCommitted`) both run on the follower's QuorumPeer thread (`Follower.processPacket`), so there is no HB-concurrent writer. A lost or reordered COMMIT is not one of our kinds. The zxids cross the stream | yes | ObserverMasterTest#testInOrderCommits(boolean) (exists; parameterized, the true row) | C |
| 11 | quorum/QuorumPeer.java:1177 | throw IOException | `currentEpoch < epochOf(lastProcessedZxid)` and no `currentEpoch.tmp` | weak: epoch files vs txn log of one peer | None: disk only | **no** (files) | CurrentEpochWriteFailureTest#testReadCurrentEpochFromAcceptedEpochTmpFile (exists) | C |
| 12 | quorum/QuorumPeer.java:1197 | throw IOException | `acceptedEpoch < currentEpoch` | weak: two epoch files | None: disk only | **no** | testQuorum | C |
| 13 | quorum/ReadOnlyZooKeeperServer.java:126 | throw CloseRequestException | `isGlobalSession(sessionId)` at a session renewal on an RO peer | Y: the client's session (created while the quorum was up) vs the RO peer's global-session map (filled by createSession txns committed through Zab) | testGlobalSessionInRO **throws in the recording** (the refusal is the test's expectation). A real question needs a renewal that passes: ReadOnlyModeTest#testConnectionEvents (local sessions; the renewal at the RO peer evaluates the guard false). Flipping it needs the session in the RO peer's global map, and only a committed createSession or upgrade (leader-to-follower stream) writes it. The ConnectRequest has no door | yes | ReadOnlyModeTest#testGlobalSessionInRO (exists); prefer #testConnectionEvents | C |

### The Learner<->Leader socket stream, per quorum-path site

Since `gc/zk-learner` (2026-10-21) every `QuorumPacket` of a learner stream (a leader or observer master and its
learner) is a `ZK_QUORUM` `REQUEST` message (tree `CausynthQuorum`; STATUS "Per-system surface", "tree: transport"): sent
where its producer hands it to the stream (`LearnerHandler.queuePacket`, `Learner.writePacket`), put on the wire where its
bytes are written, under the learner end's local port, the direction and its place in it, and served by the reading end
(`Learner.readPacket`, `LearnerHandler.run`'s reads) until its next read or the end of the learner's role or handler. Its FAULT door: `ZK_QUORUM READ`, a
`SocketTimeoutException` before each read of a sync (`Learner.readSyncPacket`, every read of `syncWithLeader`); the
broadcast loop's reads are no door. A PROPOSAL's or INFORM's txn header crosses as the packet's message (D5,
`CausynthQuorum#carrying`, the catalog's `MESSAGE` row; STATUS "tree: a txn's header crosses the learner stream"), so a
learner's `TxnHeader` getters attach the sender's export; the envelope's own fields (`QuorumPacket.zxid`, `type`: a
LEADERINFO's epoch, an ACK's or COMMIT's zxid) are not carried, a receiver's own constant. The election stream
(`QuorumCnxManager` SendWorker/RecvWorker, FastLeaderElection notifications as a ByteBuffer) has no door.

| site | crosses the learner stream? | door it would need |
|---|---|---|
| 01 | The guard's data is leader-local: clock to expiry thread to `isClosing`. A follower client's request arrives as a REQUEST packet, and its renewals arrive as the follower's touch table in PING. | QUORUM REQUEST envelope (follower to leader: REQUEST, PING) carrying the client message context. It is like `CausynthZk`'s WIRE map, keyed by (sid, packet sequence), since all peers share the JVM. Without it, attribution only. |
| 02 | Yes. The new owner is set by a REVALIDATE packet; the stale request arrives as a REQUEST packet. | The same follower-to-leader envelope (REQUEST, REVALIDATE). No payload codec is needed (owner identity is the LearnerHandler object). |
| 03 | Like 01 (the createSession of a follower client arrives as REQUEST). | Like 01. |
| 04 | The values written to `lastProcessedZxid` come from COMMIT/INFORM packets (leader to follower). The re-pairing chooses among recorded writes, so no symbolic payload is needed. | None for the pairing. Needs the QuorumPeers registered as nodes, and the follower's commit thread attributed to its peer. |
| 05, 07 | Yes: LEADERINFO zxid (leader to follower), FOLLOWERINFO (follower to leader). | QUORUM envelope both directions plus a LEAF codec for `QuorumPacket.zxid` (long) and the epoch int inside `data` (ByteBuffer). 07 also reads `acceptedEpoch` from a file after restart (IO). |
| 06 | Yes: ACKEPOCH (follower to leader) carries `lastLoggedZxid` and the epoch bytes. The election stream carries the votes. | QUORUM envelope plus codec as above, plus an ELECTION door on `QuorumCnxManager`/FastLeaderElection notifications. The values still originate on disk. |
| 10 | Yes: PROPOSAL/COMMIT zxids (leader to follower). | QUORUM envelope plus zxid codec. Even with it, no single counterfactual reorders Zab. |
| 13 | Yes: the global-session map is filled by committed createSession txns (PROPOSAL/COMMIT). The renewal enters through the ConnectRequest. | QUORUM envelope plus a CONNECT door on the client handshake (`ClientCnxnSocket` ConnectRequest to `processConnectRequest`). |
| 11, 12 | No socket: disk only. | none (IO rule) |

## B. bug_study bugs not covered by README §0.3 (#16-#59), and first-batch bugs that coincide with a study site

Present means I read the faulty logic and the fatal throw in our tree. Recover means: does a retry or restart fix it?

| bug | present in our tree (fatal throw) | coordination? | single counterfactual | chain in memory? | cluster test | fit | on a study site? |
|---|---|---|---|---|---|---|---|
| #11 expiry stale bucket (first batch) | ExpiryQueue.update/poll race; SessionTrackerImpl:317 + FinalRequestProcessor:709 | Y | no: CLOCK to reach the deadline plus the update/poll interleaving (§0.3: several flips) | yes | self-written | C (§0.3 verdict stands) | yes: 01 |
| #13 late RO startup (first batch) | ZooKeeperServer.java:1523 NOT_READ_ONLY | Y | no: thread schedule plus RO grace timing (§0.3) | yes | self-written | C (§0.3) | next to 04 (same method) and 13 (RO server) |
| #15 learner touch-table swap (first batch) | LearnerSessionTracker touchSession/snapshot; leader SessionTrackerImpl:317 / NoNode | Y | no: two swaps plus expiry (§0.3); the touch table crosses PING | no (stream) | self-written | C (§0.3) | yes: 01 |
| #16, #17 recursive setAcl -R | zkCli SetAclCommand/ZKUtil; server NoAuth | weak | deterministic API sequence / operator input | - | none | C | no |
| #18, #19, #20, #23, #41 ZooInspector create/delete/setData false success | ZooKeeperRetry.java:76-111, 243-263 present | Y | #23 and #41 need a fault *before* commit; our door plants commit-then-lost-reply. #18, #19, #20 are deterministic | - | none (ZooInspectorManagerImplTest mocks) | C | no |
| #21 ZooInspector setData lost ack: BadVersion | ZooKeeperRetry.java:254 `getData(..) == data` (reference compare) present; PrepRequestProcessor.java:794 BadVersion | Y | WRITE-door fault on setData | yes | self-written | B: data is committed and only the caller gets a false failure (recoverable by a re-read), so not added | no |
| #22, #31 ZooInspector setACL lost ack | ZooKeeperRetry.setACL | Y | `setACL` has no door | - | self-written | C | no |
| **#32 ZooInspector sequential create lost ack: hard quota** | ZooKeeperRetry.java:82-86: on ConnectionLoss, `exists(path)` with the **requested prefix**, never true for a sequential node, so the loop creates again. ZooKeeperServer.java:2256 QuotaExceeded (count hard limit; `zookeeper.enforceQuota`, ZooKeeperServer.java:158) | Y: the wrapper's view (prefix) vs the server's sequential name and quota stats | **one WRITE-door fault** on the first sequential `create` | yes: server-side stat count in DataTree, read by Prep `checkQuota` (PrepRequestProcessor.java:698) | self-written (justified below) | **A-: ADDED** (hard: an orphan sequential node keeps consuming quota under a name the caller never learns; every retry fails until manual cleanup) | no |
| #24, #25, #34, #38 REST | contrib REST (Jersey) | Y | - | HTTP | - | C (contrib REST, as §0.3 #09/#10) | no |
| #26 | known ASF (ZOOKEEPER-4286) | - | - | - | - | C | no |
| #27 chroot getConfig removeWatches | deterministic path mapping | weak | none | - | - | C | no |
| #28 X509 password file reload | file watcher | - | - | **no** (files) | - | C | no |
| #29, #30 TCP fragmentation | raw socket reads | - | read-length choice is not one of our kinds | no door | - | C | no |
| **#33 container cleanup deletes a fresh generation** | PrepRequestProcessor.java:332-342: `deleteContainer` checks only `childCount > 0` and `EphemeralType == NORMAL`, with no generation, cversion or czxid fence. ContainerManager sends the path only. Fatal: client `getData` NoNode, FinalRequestProcessor.java:709 (our marker) | Y: the cleanup's candidate (scanned earlier) vs the authoritative node at delete time | **one STATE re-pairing**: the client's `getData` node-map lookup re-paired to the cleanup's delete (`assoc_remove`). CONFIRM orders the delete after the client's recreate. This is the election-offer mechanism | yes (DataTree node map) | self-written (CreateContainerTest-style ClientBase, below) | **B: ADDED** (hard: the new znode and its data are gone) | no |
| #35 LES lost offer-create ack | LeaderElectionSupport.makeOffer | Y | WRITE-door fault on `create` | yes | self-written | C: no fatal throw beyond the fault's own ConnectionLoss (echo); the effect is a stuck READY | no |
| #36, #45 chroot sequential root / multi delete root | deterministic | weak | none | - | - | C | no |
| #37 | downgraded (README declares no ConnectionLoss handling) | - | - | - | - | C | no |
| #39 queue concurrent bootstrap NodeExists | DistributedQueue.java:262-270 (`offer`) and :228-238 (`take`) create `dir` without catching NodeExists; PrepRequestProcessor.java:687 | Y | STATE re-pairing to INITIAL of the parent lookup (existing DistributedQueueTest#testTakeWait1 races `take`'s bootstrap with `offer`) | yes | exists | C: transient (a retry succeeds), so it fails the hard-to-recover rule; not added | no |
| #40 multiRead budget vs client frame | FinalRequestProcessor budget, ClientCnxnSocket frame check | weak | CONFIG on both sides | client frame read has no door | - | C | no |
| #42 ZooInspector null setData false commit | ZooKeeperRetry.java:254 | Y | needs a fault before commit (not our door) | - | - | C | no |
| #43, #48 LES stop | LeaderElectionSupport.stop | Y | #43 deterministic (stop twice); #48 needs an admin ACL change, and NoAuth is correct | - | - | C | no |
| #44 local/global owner handoff | LeaderSessionTracker.java:184-193 `setOwner` returns after local (present); SessionTrackerImpl:323 | Y | no: upgrade window plus old-connection check plus new-owner set (3 interleavings); recoverable by reconnect | yes | self-written | C | **yes: 02** |
| #46 WriteLock watch after retry exhaustion | ProtocolSupport retry throw | Y | 10 read faults (no read door) | - | - | C | no |
| #47 local/global upgrade touch | LeaderSessionTracker.java:126-131 `touchSession` returns after local (present); SessionTrackerImpl:317 | Y | no: the upgrade window must stay open for a session timeout (schedule plus CLOCK) | yes | self-written | C | **yes: 01** |
| #49 quota child pre-check swallowed ConnectionLoss | SetQuotaCommand.checkIfChildQuota | Y | fault on `getChildren` (no read door); the fault makes the guard *not* fire | - | - | C | no |
| #50 Netty sessionless sockets | raw sockets | - | - | - | - | C | no |
| #51 ObserverMaster oversized INFORM | ObserverMaster.java:377-405 eviction, then `startForwarding` skips the gap check when `committedPkts` is empty (present) | Y | CONFIG `zookeeper.observerMaster.sizeLimit` plus an observer reconnect at the right moment | no (follower to observer stream) | self-written | C | same class as 10, different throw |
| #52, #53 large-request budget leaks | RequestThrottler mustDrop / `authWriteRequest` early return | weak (local accounting) | 2-3 CONFIGs plus stale close or NoAuth; quorum only | - | - | C | no |
| #54 ACL-filtered watch consumed | WatchManager plus NoWatcher | weak | admin ACL change | - | - | C | no |
| #55 chroot quota delete | deterministic path mapping | weak | none | - | - | C | no |
| #56-#59 live restore | admin restore / snapshot | - | - | **no** (snapshot, files) | - | C | no |

## C. Known cases vs study items

- `zk-bugs-quota-init` and `zk-bugs-election-offer` both mark FinalRequestProcessor.java:709 (`handleGetDataRequest` NoNode). That
  is **not** a study.txt site: the study has no FinalRequestProcessor item. No study item is the same throw.
- Related but distinct: study 01-03 (SessionTrackerImpl) sit on the same request path. Prep `checkSession` runs before Final
  for every write. The proposed `zk-bugs-container-reuse` reuses the :709 marker (third id on the same annotation).

## D. Pick list (owner ruling 2026-10-04: every TESTED study item, dropped only for a hard reason)

**Dropped, with the hard reason:** 08, 09 (NO_PATH: no cluster test). 05: the throw is dead code in our tree. Learner.java:522
throws first for a lower epoch, `acceptedEpoch` has no writer on another thread, and only a pre-1.0 leader's NEWLEADER-first
answer reaches line 102. If the lead keeps 05 anyway, it is the same chain as 07.

**Adapter work every study check needs (one step, before any of them runs):** a quorum adapter.
- Register each QuorumPeer as a node: its main thread, election workers, role ZooKeeperServer and processors (incl. the
  CommitProcessor workers), LearnerHandler threads, session tracker, ZKDatabase and connection factory.
- Hook the three ensemble bases: `QuorumPeerTestBase.MainThread` (QuorumPeerMain from a zoo.cfg), `QuorumUtil`, and
  `QuorumBase`/`ObserverMasterTestBase`.
- No-expiry rule: max session timeout and client timeout `NEVER_MS`; initLimit and syncLimit large, so a slow replay neither
  expires sessions nor drops learners.
- Open the window once the quorum is up.
- 02, 06, 07, 10 and 13 also need the QUORUM envelope door from §A.

Numbered checks: each line gives the marker line, the workload, the counterfactual, the scope classes to start from, and the
expected chain.

1. **zk-adhoc-01**: SessionTrackerImpl.java:317 (`throw new @CausynthExceptionTarget("zk-adhoc-01") KeeperException.SessionExpiredException()`).
   - Workload: QuorumPeerMainTest#testQuorum. It can also run today on a ClientBase test, CausynthQuotaRetryTest#raisesARetriedHardQuota (standalone tracker, no quorum adapter).
   - Counterfactual: CLOCK on the tracker's `ExpiryQueue` reads, a skew of at least the granted timeout.
   - Scope: SessionTrackerImpl, ExpiryQueue, PrepRequestProcessor (LeaderSessionTracker in a quorum).
   - Chain: skewed `now` in `getWaitTime`/`poll` → buckets advance to the session's → `setSessionClosing` → the next write's `checkSession` reads `isClosing` → throw. Fit B (the poll loop must walk many empty buckets).
2. **zk-adhoc-02**: SessionTrackerImpl.java:323 (SessionMovedException).
   - Workload: testQuorum cannot throw. Use QuorumTest#testSessionMovedWithSynchronousSync and declare the new connection's request occurrence; the old connection's throw is the test's expectation.
   - Counterfactual: STATE re-pairing of `session.owner`.
   - Scope: SessionTrackerImpl, LeaderSessionTracker, Leader (revalidateSession), LearnerHandler, PrepRequestProcessor.
   - Chain: REVALIDATE `setOwner(LearnerHandler_new)` vs forwarded REQUEST owner. Needs the follower-to-leader envelope. Fit B.
3. **zk-adhoc-03**: SessionTrackerImpl.java:330.
   - Workload: testQuorum, or the ClientBase test above.
   - Counterfactual: CLOCK as 01, but inside the createSession-to-Prep gap.
   - Scope: SessionTrackerImpl, ExpiryQueue, PrepRequestProcessor (createSession case, :583). Fit C.
4. **zk-adhoc-04**: ZooKeeperServer.java:1537 (CLIENT_ZXID_AHEAD).
   - Workload: testQuorum cannot throw (fresh clients send lastZxidSeen = 0). Use ReadOnlyModeTest#testSeekForRwServer.
   - Counterfactual: STATE re-pairing of the follower's `DataTree.lastProcessedZxid` with an older HB-concurrent apply.
   - Scope: ZooKeeperServer (processConnectRequest), DataTree, FollowerZooKeeperServer / CommitProcessor. Fit C.
5. **zk-adhoc-06**: quorum/Leader.java:1515. Workload: testQuorum. Counterfactual: none of our kinds (disk values plus ACKEPOCH and election streams). Scope: Leader (waitForEpochAck), StateSummary, LearnerHandler. Fit C; needs the QUORUM and ELECTION doors.
6. **zk-adhoc-07**: quorum/Learner.java:522. Workload: QuorumRestartTest#testRollingRestart. Counterfactual: none of our kinds (acceptedEpoch from a file at restart; epoch over LEADERINFO). Scope: Learner (registerWithLeader), Leader (getEpochToPropose), QuorumPeer (acceptedEpoch). Fit C.
7. **zk-adhoc-10**: quorum/ObserverMaster.java:371. Workload: ObserverMasterTest#testInOrderCommits(boolean) [true]. Counterfactual: none (writer and reader on one thread; zxids over the stream). Scope: ObserverMaster, Follower (processPacket). Fit C.
8. **zk-adhoc-11**: quorum/QuorumPeer.java:1177. Workload: CurrentEpochWriteFailureTest#testReadCurrentEpochFromAcceptedEpochTmpFile. Disk only (IO rule). Scope: QuorumPeer (loadDataBase). Fit C.
9. **zk-adhoc-12**: quorum/QuorumPeer.java:1197. Workload: testQuorum. Disk only (IO rule). Scope: QuorumPeer (loadDataBase). Fit C.
10. **zk-adhoc-13**: quorum/ReadOnlyZooKeeperServer.java:126.
    - Workload: ReadOnlyModeTest#testConnectionEvents. testGlobalSessionInRO throws in its recording (expected refusal).
    - Counterfactual: none in memory today. The global-session map is filled over the Zab stream, and the ConnectRequest has no door.
    - Scope: ReadOnlyZooKeeperServer, LearnerSessionTracker, ZooKeeperServer (processConnectRequest). Fit C.

bug_study additions (all criteria hold; neither is on a study site, since no checkable bug on a study site was found: #11, #15, #44
and #47 each need several flips):

11. **zk-bugs-retry-seq-quota** (#32).
    - Marker: ZooKeeperServer.java:2256 (count hard-limit QuotaExceeded).
    - Self-written workload in `zookeeper-contrib/zookeeper-contrib-zooinspector`. No test there starts a server; ZooInspectorManagerImplTest mocks ZooKeeperRetry. The test must:
      - run under ClientBase from the zookeeper-server test-jar, with `-Dzookeeper.enforceQuota=true` in the JVM properties (a static final read at class load);
      - create `/q`, set a hard count limit that allows exactly two children, open a `ZooKeeperRetry` client;
      - call `create("/q/n-", .., PERSISTENT_SEQUENTIAL)` twice; both pass in the recording.
    - Counterfactual: WRITE-door fault on the first `create`.
    - Scope: ZooKeeperRetry, ZooKeeper (create door), PrepRequestProcessor, ZooKeeperServer (checkQuota), DataTree.
    - Chain: the fault (committed, reply lost) → `exists("/q/n-")` is null → the loop creates `/q/n-0001` → the test's second call's create → Prep `checkQuota` count 3 > 2 → throw at the recorded second-call occurrence (as quota-init declares the retry's address).
    - system.sh needs `zk_module` and an `inspector:` source root.
12. **zk-bugs-container-reuse** (#33).
    - Marker: FinalRequestProcessor.java:709 (add the id).
    - Self-written ClientBase workload, modelled on CreateContainerTest. No existing test recreates a path the cleanup is about to delete. The test must:
      - create container `/c` with a child, then delete the child (cversion > 0, empty);
      - start the production `ContainerManager` timer (short interval) on its own thread;
      - on the test thread, after a short sleep: `delete("/c")` swallowing NoNode, `create("/c", PERSISTENT)`, `getData("/c")`. In the recording the cleanup deletes the old `/c` first.
    - Counterfactual: STATE re-pairing of the `getData` node-map lookup to the cleanup's delete. CONFIRM orders that delete after the recreate; Prep passes the new node (childCount 0, type VOID).
    - Scope: ContainerManager, PrepRequestProcessor (deleteContainer), FinalRequestProcessor, DataTree, NodeHashMapImpl.
    - Chain: the fresh generation is deleted → `getData` NoNode. Fit B (HB-concurrency rests on the timer thread and the unwired responses).

Already cases: `zk-bugs-quota-init` (#01, CausynthQuotaRetryTest#raisesARetriedHardQuota) and `zk-bugs-election-offer` (#05; case.sh
runs LeaderElectionSupportTest#testNodes3).

## E. The ZooKeeper case list (2026-10-21, on the fork's master eab165995)

The owner (2026-10-21) chose ZooKeeper next, as HBase: the study checks of §D plus five bugs. The bugs are:
- apache/zookeeper PR 2459 (ZOOKEEPER-5094) and PR 2454 (ZOOKEEPER-5088), whose fixes are fork branches
  `fix-trunc-sync-shutdown-state` and `fix/observer-master-pending-proposals`;
- the partially initialized quota (`zk-bugs-quota-init`);
- the orphaned election offer (`zk-bugs-election-offer`);
- the container cleanup that deletes a replacement node (`zk-bugs-container-reuse`, #33).

The tree is the fork's master eab165995 (Apache ZooKeeper master, Java 8: `maven.compiler.source/target 1.8`), where both
PR bugs are present. Every row below was read on it (Z1, Z2: `docs/handover/zookeeper-agents/`); the line numbers of §A-§D
are branch-3.9's. The case declarations are `experiments/zookeeper/zk-adhoc/checks.tsv` and `zk-bugs/case.sh`; the case
table with budgets is `experiments/zookeeper/zookeeper-cases.tsv`.

The "needs" column names the work in TODO "ZooKeeper": **T** = the tree (the adapter ported, markers, workloads); **Q** = the
quorum adapter (D3 automatic quorum cluster, D7 repeatability, D8 election-thread attribution); **L** = the learner-stream
message and FAULT door (D4); **Z** = zxid carriage on that door (D5); **S** = the txn log as a store (D6, optional).

Paths are under `zookeeper-server/src/main/java/org/apache/zookeeper/server/` unless named.

| case | marker (throw, master) | workload | counterfactual | needs | fit |
| --- | --- | --- | --- | --- | --- |
| zk-bugs-trunc-sync (ZOOKEEPER-5094) | ZKDatabase.java:341 IllegalStateException "Committed proposal cached out of order" (one annotation, two ids; the guard tests `request.zxid != maxCommittedLog + 1` last, its immediate guard: STATUS "tree: ZKDatabase:333's guard order") | `quorum.CausynthTruncSyncTest#aTruncSyncedFollowerRestarts` (tree `gc/zk-quorum-bugs`; 3 participants, `snapCount=100000`). `CausynthQuorumHarness` (the shape of the 5088 PR's test) holds the leader's ACKs of `/ahead` (Z1) until F has logged it and restarted, pauses F's handler once before `Leader.startForwarding` (TRUNC queued, the log's read lock held), and releases it once Z1 committed; Z1 is then in `toBeApplied`, so PROPOSAL+COMMIT(Z1) go before NEWLEADER and F applies Z1 in memory. `/after` and `/after2` (Z2, Z3), then F's second restart, whose replay applies Z2 then Z3 (Z3 runs the guard); the test stops that life after its last check, so the target occurrence ends inside the window. The test waits on what the leader sees (F's ACK of a create, its ACK of UPTODATE), never a poll; the held ACKs go in server id order. Target: F's third life's construction, `auto0/peer1#epoch2/region/REGION.98b8e38a#1` (runFromConfig; the replay's addCommittedProposal folds into it). Native (JDK 8) 10/10, 1.2-1.7 s. By hand (scratch, not committed): a SocketTimeoutException at that NEWLEADER read throws at ZKDatabase.java:341 in F's restart replay on master (`0x100000004 is not the next proposal of 0x100000002`), not on `fix-trunc-sync-shutdown-state` | one FAULT, depth 0: SocketTimeoutException at the follower's read of NEWLEADER in its TRUNC sync (Learner.readPacket from syncWithLeader); kind as DIFFSyncConsistencyTest's | T Q L (S for the symbolic chain through the log) | B- |
| zk-bugs-observer-master (ZOOKEEPER-5088) | ZKDatabase.java:341 (the same annotation and guard order) | `quorum.CausynthObserverMasterSyncTest#aProposalPendingAtTheObserverMastersStart` (tree `gc/zk-quorum-bugs`; 3 participants, observer O on follower F's ObserverMaster). O and F stop; the harness holds the ACKs of `/pending` (Z2) while F restarts, so F gets PROPOSAL(Z2) in its sync, logs it after UPTODATE and starts its OM with Z2 pending; the ACKs are released, Z2 commits, and the test restarts O after the create's reply (workaround: O's own ~1 s reconnect timer raced F's apply of Z2, and no wait on F's apply, which CONFIRM must be free to hold); O syncs through F's OM, then `/after` (Z3). The test waits on the leader's view (ACKs, F's ACK of UPTODATE) except for the observer's own state, which it polls. Target: O's second life's `CommitProcessor.run`, `auto0/peer4#epoch1/region/REGION.140fb26c#1`. Native (JDK 8) 10/10, 3.0-3.6 s. By hand (scratch): F's apply of Z2 held until O resynced throws at O's ZKDatabase.java:341 on master (`0x100000004 is not the next proposal of 0x100000002`), not with e70951a21's fix on eab165995 | one STATE re-pairing, depth 0 (maybe 1): the follower OM handler's read of `DataTree.lastProcessedZxid` (LearnerHandler.java:804, branch :849) paired with its version before the follower applied the pending txn | T Q L Z | B-/C |
| zk-bugs-quota-init | FinalRequestProcessor.java:674 NoNodeException (694 with the adapter; one annotation, three ids); target REGION.ce9149ce#6 (processServed, the second call's stat getData) | `test.CausynthQuotaRetryTest#raisesARetriedHardQuota` (self-written on gc/zk-unified; ports unchanged) | WRITE-door ConnectionLoss on createQuota's limit-node create (committed, reply lost); the retry's update branch reads the absent stat node (SetQuotaCommand.java:270). **PASS** ZA5-quota: MARKER_FLIPPED on that root, confirmed, native 10/10, control 0/10 (20 claims, 120 s order timeout: the pairings first, TODO HBase 15) | T | A |
| zk-bugs-election-offer | FinalRequestProcessor.java:674 (same annotation) | `recipes.leader.LeaderElectionSupportTest#testNodes3` (recipes-election) | STATE re-pairing: toLeaderOffers' getData (LeaderElectionSupport.java:310) of a listed offer to its owner's delete. **PASS** ZA9-offer: that pairing, confirmed, native 10/10, control 0/10 at the anchor (target REGION.ce9149ce#2; 20 claims, 120 s order timeout) | T | A- |
| zk-bugs-container-reuse (#33) | FinalRequestProcessor.java:674 (same annotation) | `server.CausynthContainerReuseTest#keepsTheReplacementOfACleanedContainer` (self-written, ClientBase, as CreateContainerTest: the test's own ContainerManager checks once, 100 ms after it starts, its Timer's thread on the server's node, and submits each deletion through a one-worker SynchronousQueue pool it waits for (a hand-off CONFIRM can hold after the scan: the race's window made controllable). **Workaround** (tree `gc/zk-tree-contfb`): the workload widens the cleanup's scan-to-post window so the race (the cleanup posting after the replacement's create) happens natively; GraphChecker finds the read order that exposes the deleted replacement. The worker posts the deletion 3 s after the scan, a delay and no happens-before; the client deletes, recreates persistent and reads the path 1 s after the manager starts, then sends one request behind the deletion; the recording (ZA17-contfb): the client's delete, create and getData, then the cleanup's remove of the replacement; native 5/5 (getData before the remove). Without the window the bug's world needs the client's delete to succeed, a write no depth-0 session holds, and at depth 1 EXPLORE cannot re-pair the node-map lookup that decides it (`getRecordForPath#u13`, NOT_FLIPPABLE: `FlipQuery#movableReads` skips container reads; ZA15-cont)) | STATE re-pairing of the test's getData lookup to the cleanup's remove of the replacement (depth 0) | T | B |
| zk-bugs-retry-seq-quota (#32) | ZooKeeperServer.java:2201 QuotaExceededException (count hard limit) | `org.apache.zookeeper.retry.CausynthZooKeeperRetryQuotaTest#createsTwoSequentialChildrenUnderAHardQuota` in zooinspector (self-written, ClientBase; `-Dzookeeper.enforceQuota=true`; hard count limit **3** = the node + two children; the ZooKeeperRetry client registered by the ZooKeeper constructor in automatic mode; pom deps as the recipes'; `zk_maven_profiles=(full-build)`; native 5/5) | WRITE-door ConnectionLoss on the first sequential create (ZooKeeperRetry.java:81, the `exists(path)` check :85 never sees the sequential name) | T | A- |
| zk-adhoc-01 | SessionTrackerImpl.java:317 SessionExpiredException | `server.quorum.QuorumPeerMainTest#testQuorum`; ClientBase stand-in `CausynthQuotaRetryTest#raisesARetriedHardQuota` | CLOCK on the tracker's ExpiryQueue (skew >= the granted timeout) | T (stand-in), Q | B |
| zk-adhoc-02 | SessionTrackerImpl.java:323 SessionMovedException | `test.QuorumTest#testSessionMovedWithSynchronousSync` (declare the new connection's request) | STATE re-pairing of `session.owner` (REVALIDATE's setOwner, Leader.java:1789) | T Q L | B |
| zk-adhoc-03 | SessionTrackerImpl.java:330 SessionExpiredException | testQuorum; the same stand-in | CLOCK as 01, inside the createSession-to-Prep gap | T, Q | C |
| zk-adhoc-04 | ZooKeeperServer.java:1516 CloseRequestException CLIENT_ZXID_AHEAD | `test.ReadOnlyModeTest#testSeekForRwServer` | STATE re-pairing of the follower's lastProcessedZxid with an older apply | T Q L | C |
| zk-adhoc-06 | quorum/Leader.java:1522 IOException | testQuorum | none of our kinds (disk values, ACKEPOCH, election stream) | T Q L | C |
| zk-adhoc-07 | quorum/Learner.java:522 IOException | `test.QuorumRestartTest#testRollingRestart` | none (acceptedEpoch from a file; epoch over LEADERINFO) | T Q L | C |
| zk-adhoc-10 | quorum/ObserverMaster.java:371 RuntimeException | `test.ObserverMasterTest#testInOrderCommits[1]` (the `true` row; surefire runs both natively; automatic mode writes 21 per client, not 10001: STATUS "tree: zk-adhoc-10's focused workload") | none: writer and reader on one thread | T Q L | C |
| zk-adhoc-11 | quorum/QuorumPeer.java:1236 IOException | `server.quorum.CurrentEpochWriteFailureTest#testReadCurrentEpochFromAcceptedEpochTmpFile` | disk only (IO rule) | T Q | C |
| zk-adhoc-12 | quorum/QuorumPeer.java:1256 IOException | testQuorum | disk only | T Q | C |
| zk-adhoc-13 | quorum/ReadOnlyZooKeeperServer.java:126 CloseRequestException | `test.ReadOnlyModeTest#testConnectionEvents` (check the seed observes the first client's renewal at the RO peer: timing) | none in memory today (the global-session map over Zab; no ConnectRequest door) | T Q L | C |

State per case (runs and readings: STATUS "ZooKeeper checks"; target occurrences in `zk-adhoc/checks.tsv`, read off
SEEDs on the automatic quorum cluster of tree `gc/zk-quorum`):
- zk-adhoc-12: UNSAT_CLOSED at the fixed point, substantive (ZC7-12): on a fresh ensemble both epochs are
  `epochOf(lastProcessedZxid)`, so `acceptedEpoch < currentEpoch` cannot hold; disk only. Target: server 1's first
  start (`auto0/peer1#epoch0`, `QuorumPeerMain#runFromConfig`, into which `start` and `loadDataBase` fold), window `startup`.
- zk-adhoc-06: UNSAT with no root (ZC10-06 on integration 9, UNSAT_CLOSED at the fixed point, 0 BLOCKING; ZC8-06 the
  same, vacuous): the ACKEPOCH summary and the leader's are both fresh disks' values. vacuity.py now calls it
  substantive, but only because one read of `waitForEpochAck` is offered another writer, and every writer holds a
  fresh summary. Target the leader's `LearnerHandler#run` for its follower (`auto0/peer2#epoch0`), window `startup`.
- zk-adhoc-11: vacuous UNSAT by construction (ZC7-11, IO rule): the epoch files and the replayed log are file state no
  symbol carries, no LOCAL_IO door at `currentTmp.exists()`. Target server 0's third start (`auto0/peer0#epoch2`, after
  the test rewrote its epoch files).
- zk-adhoc-01: target client1's `create` at the leader, the window's second `checkSession` (`auto0/peer2#epoch0`, Prep
  `#2`). The first, client0's forwarded create, comes before any expirer turn in the window: client0's session was made
  before the window, and the leader does not touch a follower's session. client1's create is touched in
  `submitRequestNow` (a clock root); the expirer's turn comes next (`getWaitTime`, a clock root), then Prep's
  `checkSession`. The expiry deadline enters the guard as follows (STATUS "tree: the session expirer's grid"):
  the leader's tracker counts its buckets from its start, 12 h each, so client1's session stands in the first
  bucket, base + 12 h = `nextExpirationTime`. The turn reads the clock once; its guard is `nextExpirationTime - clk
  <= 0`, plus the 60 s margin. One jump of the leader's clock past base + 12 h at that turn makes `poll(clk)` take
  client1's bucket; `setSessionClosing` runs, and `checkSession` throws. A session that closes before the touch
  drops the request (`MissingSessionException`), so no check runs. The clock domain is 30 days ahead of each reading
  (`CLOCK_SKEW_WINDOW_NANOS`), so it holds 12 h. Before: ZC10-01/-03 ran on the old grid, where the flip was UNSAT,
  because it kept `getWaitTime`'s inner ternary arm, and the session stood two buckets on. ZC11 flipped only the turns
  after the target (`ClosurePlanner#decidedAway`, PIPELINE §7.2). In ZC12, `poll` read the host's clock.
- zk-adhoc-03: target client1's `createSession` at the leader (Prep `#1`, the window's only `setOwner`). The
  chain is 01's, at the expirer turn between `submitRequestNow`'s touch and Prep's `trackSession`/`setOwner`.
  `poll` decides on the turn's own reading, so no clock cell is reached only by the arm (ZC12-03: `poll`'s second
  reading was unplanned and read the host's clock).
- zk-adhoc-07: UNSAT_CLOSED at the fixed point, substantive (ZD11-07, integration 9): the guard compares the epoch of
  LEADERINFO's envelope zxid (no door carries it, a constant at the learner) with a re-pairable `acceptedEpoch` (36 of 48
  paths offered another writer), and no explored writer exceeds the leader's proposed epoch. Class C, accepted. Target
  `first`, window `up`.
- zk-adhoc-10: vacuous UNSAT by construction (ZD11-10, integration 9, 21 writes per client): the guard reads
  `QuorumPacket.getZxid` (the envelope), writer and reader on F's QuorumPeer thread, no root. Target `first` (F's
  `QuorumPeer.run`, `auto0/peer1#epoch0`). Seed replay 3426 of 3477 slots taken.
- zk-adhoc-02: SAT_UNCONFIRMED (ZD9-02, int-9 + the client-fault cut + D5): each of 3 claims moves 8 CLOCK roots (Prep's
  `currentTimeMillis`, `processConnectRequest`'s `nanoTime`) and CONFIRM is NOT_ADMITTED for want of their root mint rows
  (E's producer-side movedRoots cut); client faults cut (`case.sh` 02). Rerun on integration 10.
- zk-adhoc-04, zk-adhoc-13: blocked by an attribution gap (ZD11-04 FATAL_TARGET_NOT_IN_WINDOW; ZD11-13 vacuous, its target
  on `workload/unregistered`): ReadOnlyModeTest builds its peers with QuorumUtil, whose NIOServerCxnFactory threads belong
  to no node, so `processConnectRequest` opens no occurrence. Rerun after C's fix.

Selected but not run (`docs/checks/SELECTION.md`): 05 (dead throw), 08, 09 (no path). Fit: A = one counterfactual, workload ready or trivial; B = one
counterfactual, more adapter or a written workload; C = a named bound or vacuous expected (still run: the owner's rule
"every tested study item").

Corrections to §A-§D found on master (Z1):
- **Line numbers.** ZooKeeperServer 1537→1516, 1523→1502, 1809→1754, 2256→2201; Leader 1515→1522, 1476→1483, 1782→1789;
  LeaderZooKeeperServer 303→296; QuorumPeer 1177→1236, 1197→1256; PrepRequestProcessor 583→568, 698→682, 332-342→326-344;
  FinalRequestProcessor 709→674 (694 with the adapter).
- **#32's arithmetic.** A quota's count includes the node itself, so "two children" is a hard limit of 3, and the throw is
  count 4 > 3.
- **Substance.** The guards and throws are unchanged.
