# Injected ad hoc coordination bugs: ZooKeeper proposals (research agent, 2026-10-30)

Read-only research. Nothing was edited, built or run. Every file:line below was read in the unmodified checks tree
`/bigtemp/vnr3ne/wt/mallory-trees-1/zookeeper-checks` (branch `baseline/mallory` at 889f0e96 = fork
`graphchecker/zookeeper-checks` 889f0e961). The old-bug trees `bd-trees-1/zookeeper-bug-710|2886` stand on 92c0f2b5 =
889f0e96 plus the low-port fix (PortAssignment), so a put-back tree should branch from 92c0f2b5 as zk-bug-710 did.
`S` = `zookeeper-server/src/main/java/org/apache/zookeeper/server`.

Sources: `docs/design/README.md`, `docs/handover/CHECKING.md` §1, `docs/handover/BUGGY-DETECT.md`, `docs/checks/ZOOKEEPER.md`,
`experiments/zookeeper/*` (case.sh, checks.tsv, trees.tsv, doors.jsonl, system.sh), zk-buggy-710/2886 READMEs,
`results/zookeeper/README.md` (gc-zookeeper) and `results/zookeeper-buggy/`, the final runs under
`/bigtemp/vnr3ne/gc-out/zookeeper-final/` (claims, `io_doors.jsonl`, PLAN logs), the GraphChecker catalog
(`library-catalog.jsonl`, `RootCatalog`, `ConfigRoots`, `RuntimeSelectedRegionFinalizer#fetchDoor`).

## 0. What constrains ZooKeeper injections (read first)

1. **Root kinds that work on ZooKeeper today: WRITE door, STATE re-pairing, CLOCK.**
   - ZOOKEEPER WRITE door (`ZooKeeper#create`/`setData`/`delete`/`multiInternal`, after `submitRequest`: the write commits,
     the caller gets ConnectionLoss or SessionExpired): quota-init and retry-seq-quota, MARKER_FLIPPED, native 10/10.
   - STATE re-pairing: election-offer, container-reuse, observer-master, 710, 2886 (depth 0; a container read such as the
     node-map lookup is paired by COMPOSE at depth 0, but EXPLORE does not flip container reads, ZA15-cont).
   - CLOCK: zk-adhoc-03 CLOCK_SKEW confirmed, native 4/10.
   - **ZOOKEEPER READ doors are not usable in ZooKeeper-native cases.** They are asked only for store fetches, and the ZK
     tree hands no client read to that rule: the PLAN log of F1C-quota and F1C-rseq reads `data-flow doors: 0 store
     read(s) ... 0 asked`.
   - **LOCAL_IO**: the demanded doors of the epoch-file cases (F2S-11, F1C-12 `io_doors.jsonl`) are test-class temp
     files, `mkdirs`, `deleteIfExists` and `QuorumPeerConfig.parse`. `QuorumPeer.readLongFromFile`'s `FileReader`
     (QuorumPeer.java:2320-2332) is not among them.
   - **CONFIG**: no in-window JVM getter sits on a path to a ZK point. `LearnerHandler`'s `forceSnapshotSync` is read on
     the leader, but the learner branches on the packet's envelope type, which is not carried (a receiver constant).
2. **The session study points are defensive throws that correct code reaches.**
   - zk-adhoc-01 (361) and zk-adhoc-03 (374) are reached by the expirer's clock (03 SAT on the unmodified tree; 01's
     formula is SAT, its CONFIRM failed for engine reasons).
   - zk-adhoc-02 (367) is reached by any moved session's straggler: the 710/2886 fixed-tree controls are SAT 10/10.
   - An injection there discriminates only if the workload and scope remove that path (zk-inj-d does this).
3. **The discriminating points are the bug-check targets.** They are FinalRequestProcessor.java:694 (getData NoNode),
   ZooKeeperServer.java:2201 (hard count quota) and ZKDatabase.java:341 (committed log out of order). Their current SATs
   come from the real bugs left in the tree (quota-init, election-offer, container-reuse, #32, 5088), so each injected
   case needs a workload that avoids those bugs. Each case must also run its **control**: the unmodified tree with the
   same workload and declaration (expected UNSAT, or claims CONFIRM refutes), as BUGGY-DETECT's controls did.
4. **The target occurrence must exist in the recording.** A server-side occurrence is answered by shape, which is how
   quota-init's retry answered the recorded `#6`. Read each target off a `STOP_AFTER=SEED` run.

## 1. Detectable candidates

### zk-inj-a: the container cleanup trusts its own scan (P1, STATE, 694)

1. **Point.** zk-bugs-container-reuse's target (shared with quota-init and election-offer):
   `S/FinalRequestProcessor.java:694` `throw new @CausynthExceptionTarget(...) NoNodeException()`, guard `n == null`
   (:689) on `zks.getZKDatabase().getNode(path)` (:688) in `handleGetDataRequest`.
2. **Pattern.** P1: stale coordination state (the cleanup's scan) used without re-validation at the authoritative point.
   - Analogue: bug_study #33 / zk-bugs-container-reuse. Prep's deleteContainer re-checks only the child count and the
     ephemeral type; this injection drops the child-count re-check ("ContainerManager already found it empty").
3. **Mutation** (`S/PrepRequestProcessor.java:327-337`, `case OpCode.deleteContainer`):
   ```diff
                ChangeRecord nodeRecord = getRecordForPath(path);
   -            if (nodeRecord.childCount > 0) {
   -                throw new KeeperException.NotEmptyException(path);
   -            }
   +            // ContainerManager#getCandidates posts only containers it found empty
                if (EphemeralType.get(nodeRecord.stat.getEphemeralOwner()) == EphemeralType.NORMAL) {
   ```
   **Healthy run.**
   - The scan (100 ms) finds the used, empty container. The client creates a child and reads the container at about
     1 s: the getData is served (guard evaluated, false).
   - The worker posts at 3.1 s, and the buggy Prep deletes the non-empty container. `DataTree.deleteNode` (:534-563)
     has no children check, so `/c/c2` is left orphaned in the node map and nothing throws. This is after the read.
4. **Workload.** New `server.CausynthContainerChildTest`, copied from `CausynthContainerReuseTest` (the same `OneCheck`
   manager: CHECK_MS 100, POST_DELAY_MS 3000, AFTER_SCAN_MS 1000):
   ```java
   zk.create(PATH, b, OPEN, CONTAINER); zk.create(PATH + "/c1", b, OPEN, PERSISTENT); zk.delete(PATH + "/c1", -1);
   OneCheck cleanup = CausynthZkCluster.serverWork(server, () -> { OneCheck m = new OneCheck(server); m.start(); return m; });
   Thread.sleep(AFTER_SCAN_MS);
   zk.create(PATH + "/c2", b, OPEN, PERSISTENT);   // the container is in use again (not caught: NoNode here ends the test)
   zk.getData(PATH, false, null);                 // target
   cleanup.checked.await(CHECKED_S, TimeUnit.SECONDS);
   zk.exists("/", false);                         // behind the cleanup's deletion
   ```
   - `case.sh`: zk-bugs container-reuse's branch (scope ContainerManager, Prep, Final, `server=:DataTree`,
     NodeHashMapImpl; 20 claims; CONFIRM order timeout 150000; depth 0).
   - Target `REGION.ce9149ce-...#1` (its only getData; confirm on a SEED).
   - Add the id to the marker at :694.
5. **Trigger.** STATE re-pairing.
   - Reader: the getData's node-map lookup (:688).
   - Writer: `nodes.remove(path)` (DataTree.java:563) in the cleanup's deleteContainer txn, posted through
     `ContainerManager.postDeleteRequest` (:163-165) straight to `firstProcessor`.
   - Both are inside the window (the manager starts in-window through `serverWork`). The recording has container-reuse's
     shape: the read, then the remove.
   - CONFIRM holds the getData at RequestThrottler's claim. The remove does not pass the throttler.
   - Expected `STATE_PAIRING_FLIPPED`, depth 0, no root moved.
6. **Why detectable.**
   - Precedent: zk-bugs-container-reuse (F1B-cont: the same reader and writer kind, the same workload frame, SAT, CONFIRM,
     native 10/10, control 0/10).
   - The point's current verdict is SAT only because #33 is present.
   - With this workload the unmodified Prep refuses the delete (NotEmpty), so the recording has no remove: expect UNSAT.
     If COMPOSE pairs the cleanup's child-count read before c2's create, CONFIRM refutes it: c2's create then fails with
     NoNode and the getData never runs.
7. **Risks.** The 3 s window is timing, as container-reuse's (native 5/5 there). The orphan child stays in the DataTree
   (only a digest log). **Confidence HIGH.**

### zk-inj-b: WriteLock forgets its own node after a lost reply (P3, WRITE door, 2201)

1. **Point.** zk-bugs-retry-seq-quota's target: `S/ZooKeeperServer.java:2201` QuotaExceededException, guard
   `newCount > countLimit` (:2196) in the private `checkQuota` (:2152), reached from Prep's create
   (PrepRequestProcessor.java:683).
2. **Pattern.** P3: a non-idempotent retry after a lost reply.
   - Analogues: bug_study #32 (ZooKeeperRetry, the existing case), HBASE-20642.
   - The removed code is the recipe's own guard ("lets try look up the current ID if we failed in the middle of creating
     the znode", WriteLock.java:217-219).
3. **Mutation** (`zookeeper-recipes/zookeeper-recipes-lock/src/main/java/org/apache/zookeeper/recipes/lock/WriteLock.java:185-201`):
   ```diff
            private void findPrefixInChildren(String prefix, ZooKeeper zookeeper, String dir)
                throws KeeperException, InterruptedException {
   -            List<String> names = zookeeper.getChildren(dir, false);
   -            for (String name : names) {
   -                if (name.startsWith(prefix)) {
   -                    id = name;
   -                    LOG.debug("Found id created last time: {}", id);
   -                    break;
   -                }
   -            }
   -            if (id == null) {
   -                id = zookeeper.create(dir + "/" + prefix, data, getAcl(), EPHEMERAL_SEQUENTIAL);
   -
   -                LOG.debug("Created id: {}", id);
   -            }
   +            // the name carries our session id: a node we create is always ours, no need to list
   +            id = zookeeper.create(dir + "/" + prefix, data, getAcl(), EPHEMERAL_SEQUENTIAL);
   +            LOG.debug("Created id: {}", id);
            }
   ```
   **Healthy run.** One node per locker. B's create counts /locks (1) + A + B = 3, which is not above 3 (guard false).
4. **Workload.** New `org.apache.zookeeper.recipes.lock.CausynthWriteLockQuotaTest` (ClientBase, module
   zookeeper-recipes-lock), modelled on `CausynthZooKeeperRetryQuotaTest`:
   ```java
   setUp: System.setProperty(ZooKeeperServer.ENFORCE_QUOTA, "true"); super.setUp();
   ZooKeeper admin = createClient();
   admin.create("/locks", new byte[0], OPEN, PERSISTENT);
   StatsTrack q = new StatsTrack(); q.setCountHardLimit(3);      // the node + two contenders
   SetQuotaCommand.createQuota(admin, "/locks", q);
   new WriteLock(createClient(), "/locks", null).lock();          // A: x-<sidA>-0000000000 (acquired)
   new WriteLock(createClient(), "/locks", null).lock();          // B: its create's checkQuota is the target
   ```
   - `case.sh`: `zk_module=zookeeper-recipes/zookeeper-recipes-lock`, `zk_jvm_properties=(-Dzookeeper.enforceQuota=true)`
     (as retry-seq-quota).
   - Scope: `lock:.../WriteLock`, `lock:.../WriteLock$LockZooKeeperOperation`, `lock:.../ProtocolSupport`,
     `server:PrepRequestProcessor`, `server=:ZooKeeperServer`, `server=:DataTree`.
   - Target: B's create in Prep (`REGION.3cfb4ed2-...#k` on B's connection; read off SEED).
   - `lock:` is already a source root in `experiments/zookeeper/system.sh`.
5. **Trigger.** The ZOOKEEPER WRITE door on `ZooKeeper#create(String,byte[],List,CreateMode)` (ZooKeeper.java:1427),
   ConnectionLoss after commit, at A's create (WriteLock.java:196, from `execute`:219).
   - `ProtocolSupport.retryOperation` (:121-140) catches ConnectionLoss and re-runs `execute` with `id` still null.
     Buggy: a second node x-<sidA>-0000000001, and B's create counts 4 > 3.
   - Inside the window. Expected `MARKER_FLIPPED`, depth 0.
6. **Why detectable.**
   - Precedent: retry-seq-quota (F1C-rseq: the same door kind and the same throw, a retry re-creating a sequential node,
     MARKER_FLIPPED, native 10/10, control 0/10).
   - Unmodified: A's retry finds its node by prefix, and B counts 3: UNSAT.
7. **Risks.** A new module in the build (recipes-election's precedent: election-offer). Inner-class scope. Side
   finding (§4): in the same lost-reply world the unmodified recipe already hangs A on its own node, with no throw, so
   the control stays UNSAT at 2201. **Confidence HIGH.**

### zk-inj-c: "0 = never" for never-used containers lost (P6 with P8, CLOCK, 694)

1. **Point.** FinalRequestProcessor.java:694, as zk-inj-a.
2. **Pattern.** P6: a configuration value's special meaning is not handled. The interval 0 means "never delete a
   never-used container": ZOOKEEPER-3546, b2a671e6 "default should be 0 not Long.MAX_VALUE". ZOOKEEPER-4915 (f9fa0ccc)
   made 5 min the production default. Normalizing 0 to that default turns a configured "never" into a clock decision
   (P8).
3. **Mutation** (`S/ContainerManager.java:89-98`, the 5-argument constructor, line 94):
   ```diff
   -        this.maxNeverUsedIntervalMs = maxNeverUsedIntervalMs;
   +        // unset or non-positive: the ZOOKEEPER-4915 default
   +        this.maxNeverUsedIntervalMs = maxNeverUsedIntervalMs > 0 ? maxNeverUsedIntervalMs : TimeUnit.MINUTES.toMillis(5);
   ```
   **Healthy run.**
   - The test's manager uses the 4-argument constructor (:75-77, interval 0), now 5 min. The scan comes about 100 ms
     after the container's create, so `getElapsed(node) > 300000` (:204) is false: no candidate.
   - The getData is served (guard false). The production constructor (:58-65) already passes 5 min, so it is unchanged.
4. **Workload.** New `server.CausynthNeverUsedContainerTest` from `CausynthContainerReuseTest`:
   create container `/c` (no child); start `OneCheck` through `serverWork` (one scan; no post delay needed); await
   `checked`; `zk.getData("/c")` (target `REGION.ce9149ce#1`). Scope as zk-inj-a.
5. **Trigger.** A CLOCK root at `Time.currentWallTime()` (Time.java:47-49, a `System.currentTimeMillis` wrapper, so a
   RootCatalog WALL clock) in `ContainerManager.getElapsed` (:228-230), read in the in-window scan.
   - A forward skew of at least 300 000 ms makes `/c` a candidate. `checkContainers` (:141-149) posts deleteContainer.
     Prep passes it (child count 0, type CONTAINER) and the node is removed.
   - The getData comes after `checked`, behind the delete in Prep's FIFO, so NoNode at :694.
   - The mtime is Prep's own wall reading (PrepRequestProcessor.java:315-316) on the same node.
   - Expected `CLOCK_SKEW`, depth 0.
6. **Why detectable.**
   - CLOCK_SKEW precedents: zk-adhoc-03 (confirmed, native 4/10) and HDFS-11741 (10/10). The delete-then-NoNode chain
     is container-reuse's.
   - Unmodified: `maxNeverUsedIntervalMs != 0` short-circuits, so `getElapsed` never runs and no clock is on the path:
     UNSAT (no writer).
7. **Risks.** RootDemand must reach the manager's decision from the 694 guard through the request hand-off. The deletion
   exists only in the flipped world, unlike container-reuse's recorded remove. The native plant of a wall-clock reading
   is also a risk. **Confidence MEDIUM.**

### zk-inj-d: a learner's close marks the session closing ahead of the pipeline (P5, STATE, 361 / zk-adhoc-01)

1. **Point.** zk-adhoc-01: `S/SessionTrackerImpl.java:361` SessionExpiredException, guard `session.isClosing()` (:360) in
   `checkSession`. The leader's Prep calls it for a forwarded setData (PrepRequestProcessor.java:379).
2. **Pattern.** P5: a writer reordered ahead of a reader it was ordered behind.
   - Analogue: ZOOKEEPER-1208 (fa9e821e put `setSessionClosing` into Prep's closeSession, in pipeline order:
     PrepRequestProcessor.java:610). The injection marks the session at the learner-request hand-off instead.
   - Effect: a write the client sent before `close()` gets SESSIONEXPIRED.
3. **Mutation** (`S/quorum/LeaderZooKeeperServer.java:193`, `submitLearnerRequest`, which runs on the LearnerHandler
   thread):
   ```diff
        public void submitLearnerRequest(Request request) {
   +        if (request.type == ZooDefs.OpCode.closeSession) {
   +            // the client is leaving: refuse whatever of the session is still queued
   +            sessionTracker.setSessionClosing(request.sessionId);
   +        }
            prepRequestProcessor.processRequest(request);
        }
   ```
   (Plus `import org.apache.zookeeper.ZooDefs;`.)

   **Healthy run.**
   - The forwarded setData passes `checkSession` in milliseconds. The close comes 2 s later, so the early mark falls
     after the read: guard evaluated, false.
   - The close itself still works. Prep's closeSession does no `checkSession` (PrepRequestProcessor.java:572-575), and
     forwarded requests are not touched on the leader (`submitLearnerRequest` bypasses `submitRequestNow`'s touch,
     ZooKeeperServer.java:1262).
4. **Workload.** `test.CausynthSessionCloseOrderTest`, copied from `CausynthSessionMoved710Test`
   (bd-trees-1/zookeeper-bug-710; QuorumBase, 5 peers, peer5 the leader):
   - H connects to follower F = `(leader+1)%5` and creates `/sc` PERSISTENT.
   - A closer thread sleeps 2 s, then calls `H.close()`. It has no happens-before from the write.
   - A writer thread does `H.setData("/sc", d, -1)` and is joined. Its forwarded Prep at peer5 is the target
     (`REGION.3cfb4ed2#k`, read off SEED).
   - `case.sh`: zk-adhoc-02's scope (SessionTrackerImpl, LeaderSessionTracker, Leader, LearnerHandler, Prep: **no
     ExpiryQueue**); `causynth_scope_growth_budget=0`; `client_fault_transports=(ZK_QUORUM)`; 20 claims; order timeout
     120000.
5. **Trigger.** STATE re-pairing.
   - Reader: `session.isClosing()` (:360) in the setData's Prep.
   - Writer: `s.isClosing = true` (:277), from the injected call on F's LearnerHandler thread (the REQUEST case,
     LearnerHandler.java:714-727).
   - CONFIRM holds the leader's Prep claim of the setData, as with 710's w2, until that write exits. The writer is on
     the LearnerHandler thread, not Prep.
   - Inside the window. Expected `STATE_PAIRING_FLIPPED`, depth 0.
6. **Why detectable.**
   - Precedent: zk-buggy-710 and -2886 use the same hold (the leader's Prep claim) against a write on a LearnerHandler
     thread (the REVALIDATE's setOwner): SAT, native 10/10.
   - Unmodified: the only in-window `isClosing` writer is Prep's own closeSession, queued behind the read. That is the
     ORDER refutation zk-adhoc-02's F2S-02 claims got, so not detected.
7. **Risks.**
   - CLOCK confound: the leader's expirer takes a turn when the session is tracked, and a skew there reaches 361 on the
     unmodified tree too (zk-adhoc-01's own claim). ExpiryQueue's poll decision must stay out of scope, or the session
     must be made before the window. Run the control.
   - 5-peer replays (710's took 300 s). **Confidence MEDIUM.**

### zk-inj-e: the leader forwards from the applied zxid (P9/P5, STATE, ZKDatabase:341)

1. **Point.** zk-bugs-observer-master / trunc-sync's target: `S/ZKDatabase.java:341` IllegalStateException, guard
   :333-335 (`request.zxid != maxCommittedLog + 1`, decided last).
2. **Pattern.** P9: state from the wrong source.
   - `DataTree.lastProcessedZxid` runs ahead of the committed log: the apply happens before FinalRequestProcessor's
     `addCommittedProposal`.
   - Analogue: ZOOKEEPER-5088 (PR 2454): a txn pending at an observer master's sync is neither in the diff nor
     forwarded.
3. **Mutation** (`S/quorum/LearnerHandler.java:940-941`, `syncFollower`, under the log's read lock):
   ```diff
   -            leaderLastZxid = learnerMaster.startForwarding(this, currentZxid);
   +            // forward from the newest txn this leader has applied: anything older is in the diff
   +            leaderLastZxid = learnerMaster.startForwarding(this, Math.max(currentZxid, db.getDataTreeLastProcessedZxid()));
   ```
   **Healthy run.** No commit is concurrent with a follower's sync, so both values are equal. F's applies are
   consecutive, and :333-335 is evaluated false.
4. **Workload.** New `quorum.CausynthForwardingGapTest` on `CausynthQuorumHarness` (3 participants, as
   `CausynthObserverMasterSyncTest` without the observer):
   - F stops, and the leader commits `/w1` (so F needs a DIFF). F restarts.
   - A writer with a fixed delay and **no** happens-before from F's sync creates `/w2` (Z) and `/w3` (Z+1). Natively
     this is after F's UPTODATE.
   - Target: F's first apply after its sync (F's second life's CommitProcessor/Final occurrence; SEED).
   - `export_guard_writers=true` (observer-master's), so PLAN plans the leader's apply of Z.
5. **Trigger.** STATE re-pairing of the injected second `getDataTreeLastProcessedZxid()` read (:941) with the leader's
   `DataTree.processTxn` write of Z.
   - Z's `addCommittedProposal` stays blocked behind the read lock, as it naturally would.
   - `Leader.startForwarding` (Leader.java:1476-1508) skips Z (≤ lastSeenZxid). Z is in neither the diff nor the
     forwarding, so F applies Z+1 after Z-1 and :341 throws.
   - Expected `STATE_PAIRING_FLIPPED`, depth 0.
6. **Why detectable.**
   - Precedent: zk-bugs-observer-master (F1F-om: the same field read in `syncFollower` re-paired, CONFIRMED,
     native 4/10).
   - Unmodified: the read lock plus `toBeApplied`'s resend keep Z, so UNSAT for this workload.
7. **Risks.** A new quorum workload. WITNESS_CHAIN_OPEN as observer-master's. Native 4/10-like. **Confidence
   MEDIUM-LOW.**

### zk-inj-f: the quota limit cached per prefix (P1, STATE, 2201)

1. **Point.** ZooKeeperServer.java:2201.
2. **Pattern.** P1: a stale cache, not refreshed when the limit changes. Analogues: HDFS-11741 (the stale key cache),
   SOLR-9440 (the frozen view).
3. **Mutation** (`S/ZooKeeperServer.java:2158-2167`): cache `limitStats` per `limitNode` in a field
   `ConcurrentHashMap<String, StatsTrack>` (`computeIfAbsent(limitNode, k -> new StatsTrack(node.data))`, 4 lines).
   - Healthy run: natively the first limit read comes after the raise.
4. **Workload.** Two clients:
   - A runs `setCountHardLimit(2)` then `(4)`.
   - B, with no happens-before from A's raise, sleeps 1 s and creates `child0`, then awaits a latch A counts down after
     its raise, then creates `child1` (the target) and `child2`.
5. **Trigger.** STATE re-pairing of `child0`'s `node.data` read (:2166) with the limit node's create-time version
   instead of A's raise (`DataTree.setData`, n.data at :641).
   - The cache keeps limit 2, so `child1` counts 3 > 2.
6. **Why.** The throw is retry-seq-quota's. Pairing a read with an earlier writer is observer-master's.
7. **Risk.** The limit reaches the guard only through `StatsTrack`'s text parse of `byte[]`, which the VM probably does
   not carry symbolically. FlipQuery may then have no decision to flip, and the world is never proposed.
   **Confidence LOW** (listed for completeness; not recommended).

### zk-inj-g: a compensating rollback for the half-made quota (P2/P4, WRITE door, 694)

1. **Point.** FinalRequestProcessor.java:694.
2. **Pattern.** P2: an ambiguous remote error taken as a definite failure. P4: a cleanup that undoes the half that
   succeeded.
   - Analogue: this is the natural fix attempt for zk-bugs-quota-init's partial quota (undo the limit when the stat
     fails).
   - Also: bug_study #21/#23 (ZooInspector false failures after a lost ack), HDFS-17967.
3. **Mutation** (`zookeeper-server/src/main/java/org/apache/zookeeper/cli/SetQuotaCommand.java:243-244`, the create
   branch of `createQuota`; `quotaPath` is the limit path, :232):
   ```diff
   -            zk.create(statPath, stats.getStatsBytes(),
   -                    ZooDefs.Ids.OPEN_ACL_UNSAFE, CreateMode.PERSISTENT);
   +            try {
   +                zk.create(statPath, stats.getStatsBytes(),
   +                        ZooDefs.Ids.OPEN_ACL_UNSAFE, CreateMode.PERSISTENT);
   +            } catch (KeeperException e) {
   +                // no limit without its stat: undo the half-made quota, the caller may retry
   +                zk.delete(quotaPath, -1);
   +                throw e;
   +            }
   ```
   **Healthy run.** No fault, so no rollback. `listQuota` reads both nodes (guard false).
4. **Workload.** New `test.CausynthQuotaRollbackTest` from `CausynthQuotaRetryTest`:
   ```java
   zk.create(PATH, ...);
   try { SetQuotaCommand.createQuota(zk, PATH, hardCount3); } catch (ConnectionLossException mayHaveFailed) { }
   ListQuotaCommand.listQuota(zk, PATH);   // target: its getData of the limit node (ListQuotaCommand.java:92)
   ```
   Scope: quota-init's plus `server:org/apache/zookeeper/cli/ListQuotaCommand`.
5. **Trigger.** The ZOOKEEPER WRITE door (ConnectionLoss, committed) on `createQuota`'s stat create
   (SetQuotaCommand.java:243).
   - The rollback's delete of the limit commits. `listQuota`'s limit getData then gets NoNode at :694.
   - Expected `MARKER_FLIPPED`, depth 0.
6. **Why detectable.**
   - Precedent: zk-bugs-quota-init (F1C-quota: the WRITE door on the same method's limit create, MARKER_FLIPPED,
     native 10/10, control 0/10).
   - Unmodified: nothing deletes the limit, so the limit getData cannot miss: UNSAT at the declared occurrence.
7. **Risks.**
   - The control's quota-init world (a fault on the limit create) does reach :694, but at `listQuota`'s *stat* getData
     (ListQuotaCommand.java:96), another occurrence. The declaration must name the limit getData.
   - The bug world skips `createQuota`'s own two getDatas, so the target is answered by shape (as quota-init's `#6`).
     Check it on a SEED. **Confidence MEDIUM-HIGH.**

Coverage: patterns P1 (a, f), P2/P4 (g), P3 (b), P5 (d), P6/P8 (c), P9 (e). Roots: STATE (a, d, e, f), WRITE door
(b, g), CLOCK (c). Points: 694 (a, c, g), 2201 (b, f), 361 / zk-adhoc-01 (d), ZKDatabase:341 (e).

## 2. Undetectable candidates

### zk-inj-u1: DistributedQueue.take() looks without a watch (P5 lost wakeup, liveness)

1. **Point.** 694, through the consumer's head read (`take`'s getData, DistributedQueue.java:247).
2. **Pattern.** P5, the watcher/reader race in its lost-wakeup form. The ZooKeeper rule is to set the watch with the
   read that saw the state. Analogue: the lost-watch class (the external study's lost-watch candidate in the solr-adhoc-40
   notes).
3. **Mutation** (`zookeeper-recipes/zookeeper-recipes-queue/src/main/java/org/apache/zookeeper/recipes/queue/DistributedQueue.java:234`):
   ```diff
   -                orderedChildren = orderedChildren(childWatcher);
   +                orderedChildren = orderedChildren(null);   // one watch per take() leaks watches on a busy queue
   ```
   Line 240's `childWatcher.await()` stays: an empty look now waits on a latch nobody counts down.
4. **Workload.**
   - For GraphChecker, new `recipes.queue.CausynthQueueTakeTest` (recipes-queue module): an offer thread offers at
     once, and a take thread sleeps 1 s then takes. Natively take sees `qn-0`, and its getData (the declared target)
     is served.
   - Native symptom: the stock `DistributedQueueTest#testTakeWait1` (:191-227: take first, offer 1 s later) hangs at
     `takeThread.join()` (:223) on the injected tree and passes on the unmodified one. Catch it with a JUnit timeout.
5. **Trigger.** STATE: take's `getChildren` (DistributedQueue.java:69) observing the queue before the offer's create
   (:265), the race GraphChecker explores. The effect is a thread parked at :240.
6. **Why GraphChecker cannot detect it.**
   - It asks one question: does a world reach the declared throw at `(r,c,i)`? In this world nothing throws, and the
     declared occurrence (take's getData) is never reached.
   - A replay that blocks is a stall: the watchdog gives up after 15 s ("did not happen"), and in CONFIRM a stall or
     timeout refutes.
   - There is no "must eventually happen" target. Expected UNSAT_CLOSED on both the injected and the unmodified tree.
7. **Confidence** that it stays undetected: high. The native symptom is deterministic.

### zk-inj-u2: TTL age measured on the monotonic clock (P8, silent failure)

1. **Point.** 694 (the TTL/container cleanup's observable).
2. **Pattern.** P8, a clock-domain mix-up. ZOOKEEPER-1366 (2789d1df) introduced `Time.currentElapsedTime` beside the
   wall clock.
3. **Mutation** (`S/ContainerManager.java:229`):
   ```diff
   -        return Time.currentWallTime() - node.stat.getMtime();
   +        return Time.currentElapsedTime() - node.stat.getMtime();
   ```
   Elapsed becomes uptime ms minus epoch ms, about −1.8e12. TTL nodes, and never-used containers with an interval, are
   never deleted.
4. **Workload.**
   - For GraphChecker: a TTL node (ttl 1 h), one `OneCheck` scan, a getData.
   - Native symptom: `-Dzookeeper.extendedTypesEnabled=true`, a TTL node with ttl 200 ms, sleep 1 s,
     `checkContainers()` with the real `getElapsed` (not CreateTTLTest's fake), then
     `assertNull(zk.exists(ttlPath, false))`. It fails on the injected tree.
5. **Trigger.** None needed: the wrong state is silent and deterministic.
6. **Why undetectable.**
   - No throw guards "an expired TTL node must be gone". The nearby point (694) fires only when a node *is* deleted, the
     opposite of this bug.
   - The verdict is inverted. On the unmodified tree a forward skew ≥ ttl at `getElapsed` reaches 694 (a legitimate
     expiry: SAT). On the injected tree no forward skew inside the 30-day window (2.6e9 ms) makes elapsed positive:
     UNSAT.
   - GraphChecker reports reachable failures, not missing actions.
7. **Confidence** high; deterministic symptom.

## 3. Points considered and not proposed

- **zk-adhoc-02 (367):** correct code throws for every straggler of a moved session (the 710/2886 fixed-tree controls are
  SAT 10/10). In a workload with no move, an injected wrong-owner write fires natively.
- **zk-adhoc-03 (374):** already SAT on the unmodified tree (CLOCK, native 4/10).
  `LeaderZooKeeperServer.revalidateSession` (:291-300) already catches this throw ("this is ok").
- **zk-adhoc-04 (1516):** `lastZxidSeen` is 0 at the declared connect. A client-side mutation feeding it (for example
  from ping replies) would need the read-write peer to serve a connect before its sync ends, which "ZooKeeperServer not
  running" refuses.
- **06, 07, 10, 11, 12 (Leader:1637, Learner:537, ObserverMaster:376, QuorumPeer:1246/1266):**
  - The values come from fresh disks, or from LEADERINFO/ACKEPOCH envelope fields that are not carried.
  - In 10, the writer and reader share one thread.
  - No LOCAL_IO door at the epoch-file reads (§0).
- **13 (ReadOnlyZooKeeperServer:132):** ReadOnlyModeTest's session is local. A mutation making it global fires natively
  at the read-only renewal.
- **trunc-sync's ZK_QUORUM READ door (341):** reached, but the throw needs a second flip in life 3 (the owner's "not
  detected").

## 4. Side finding (no change made)

**The unmodified lock recipe already deadlocks after a lost create reply, without any throw.**
- `findPrefixInChildren` stores the child name without the directory (`id = name`, WriteLock.java:190), while
  `sortedNames` holds full paths (:231).
- In the ZNodeName order, `/locks/x-<sid>-N` sorts before `x-<sid>-N`, so `lessThanMe` (:234) contains the client's own
  node. It watches itself (:239-241), and `isOwner` (:290) never matches.
- This is an upstream latent liveness bug: a natural example of what GraphChecker cannot detect, and the reason
  zk-inj-u1 uses the queue rather than the lock.

## 5. Ranked recommendation (4 detectable + 1 undetectable)

1. **zk-inj-a** (694, STATE, P1): container-reuse's proven mechanism. The removed child-count check is the only thing
   between the scan and the delete.
2. **zk-inj-b** (2201, WRITE door, P3): retry-seq-quota's mechanism on the lock recipe, with a clean control.
3. **zk-inj-g** (694, WRITE door, P2/P4): quota-init's door and workload. A plausible "fix" of a real bug that is itself
   buggy.
4. **zk-inj-d** (361 / zk-adhoc-01, STATE, P5): brings in a study point. 710's hold precedent applies. Keep ExpiryQueue
   out of scope so the control is not SAT by clock.
5. **zk-inj-u1** (undetectable, liveness): the stock `testTakeWait1` hangs, and no declared throw exists on the bug's
   path.

Swap-ins:
- zk-inj-c (CLOCK) in place of g or d, if a third root kind is wanted.
- zk-inj-e (ZKDatabase:341), if five distinct points are required: a/b/d/e plus u1.
- zk-inj-u2 for a silent-failure undetectable.
