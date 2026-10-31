# Solr: injected ad hoc coordination bugs -- proposals (read-only research, 2026-10-30)

Brief: `BRIEF-research.md` (this folder), `<sys>` = solr. Tree read for every file:line below:
`/bigtemp/vnr3ne/wt/sg3j-trees/lucene-solr-checks` = `graphchecker/solr-checks` 12d23091d1 (unless a line says otherwise).
Engine read: `/bigtemp/vnr3ne/wt/gc-solr-bd` (`system/solr-buggy-detect` 44b3a2ab7). Nothing was edited, built or run.

## 0. What decided the choices

1. **Workloads.** The 12 study checks ran slow on their upstream tests (`results/solr`, `gc-solr`): 38 SAT, 21 UNSAT_CLOSED,
   the other ten RUN_DEFECT at named bounds or the 2 h cap. Every fast, reliable Solr run used a short focused `TestCausynth*`
   workload on 1-2 nodes: the 8 bug checks (610-2019 s) and the 3 old bugs (539-632 s alone, E1). So every candidate below uses
   one of those workloads, or a new one copied from a named existing one.
2. **Bug-check targets** (DZUP:238, :934, HashBasedRouter:67, BaseCloudSolrClient:908, CoreAdminOperation:186,
   DeleteCollectionCmd:246, BackupCmd:209, IndexDeletionPolicyWrapper:179) are already SAT on today's tree because the real bug
   is there. An injection can use one only with a workload the real bug cannot touch.
3. **Roots proven in Solr.**
   - A ZooKeeper write fault at a SolrZkClient door. This is a ConnectionLoss past ZkCmdExecutor's retries: the write commits,
     but the caller sees the failure. A planted SessionExpired also counts. Proven by migrate-buffer-leak, overseer-lock-leak,
     restore-construction, reindex-cleanup and 9440, natively 9/10 to 10/10.
   - A SolrJ HTTP fault: the REQUESTAPPLYUPDATES request world of migrate-buffer-leak, and SGF2's buffer-response world.
   - A CLOCK on `System.nanoTime`/`currentTimeMillis` (18406, 18413).
   - A field-backed CONFIG (6101, 6197; it needs the `CausynthLegacyCloud` holder).
   - A STATE VIEW pairing of a published view. doors.jsonl has PUBLISHED_VIEW for `/aliases.json` and
     `/collections/*/state.json`. tra-start-overwrite moved VIEW@1, natively 10/10 with VIEW_HOLD rows.

   Not proven in Solr: ZooKeeper READ doors as fault roots (they are DATA_FLOW doors), TIMED_WAIT, LOCAL_IO.
4. **The engine rules that decide every STATE candidate** (`explore/PairingFlip.java`; PIPELINE.md, the published-view
   paragraph):
   - **Which read gets a pairing.** A VIEW pairing is offered only for the earliest read of each view in the target's
     occurrence. A role-work read on the same node and causal context just before the occurrence also counts
     (`PairingFlip#reads`, `Corpus#rolePrefix`).
   - **Which versions are offered.** Only versions the node decoded before the read, at or after the newest decode made in the
     reader's own context (`floor`), at most 8.
   - **Synchronous publications.** Solr's own `forceUpdateCollection`, `AliasesManager#update`, a lazy collection's live fetch,
     and the setIfNewer after the system's own write are never deferred. This is exactly why the unmodified code is UNSAT, and
     why removing such a refresh opens the pairing.
   - **Hold length.** A hold is realistic for at most VIEW_HOLD_MAX = 3000 ms of recorded time.
   - **`_stateVer_` override.** A CloudSolrClient update carries `_stateVer_`. The server then refreshes that collection's
     `state.json` at once (`ZkStateReader#compareStateVersions` :513-540, called from `HttpSolrCall` :321), named
     PAIRING_OVERRIDDEN. So no state.json VIEW pairing at a server's read on a client update path can hold.

**Points examined and dropped (with the code reason):**
- **solr-adhoc-05** (ZkController:1274). Removing register's waitForState (:1267) is not enough. The same request waits for the
  replica twice more before register: `checkStateInZk`'s waitForState, 10 s (:1962), and `waitForShardId`'s 320 x 1 s poll
  (:1841-1857). A pairing that hides the replica blocks there, the hold gives way, and :1274 is never reached. Three removals is
  not a plausible slip.
- **solr-adhoc-38** (DZUP:1031): already SAT on today's tree (SGF9).
- **solr-adhoc-39/40** (RAUP:247/:133). 8.11 never refreshes on a miss here (`getAliasProps` :129-135,
  `lookupShardLeadersOfCollections` :243-249). On a TRA workload the earliest alias read in the request is already offered older
  views on the unmodified tree (the SOLR-40 shape), so there is no clean UNSAT to turn.
- **solr-adhoc-09/14**: vacuous by construction (the callable returns constants; the ZooKeeper `exists` Stat has no root).
- **solr-adhoc-21**: needs a concurrent replica delete during a reload; no small slip makes it.
- **DZUP:238** (overseer-lock-leak's point). It is latent on today's tree for any readOnly-toggle workload:
  - A SOLR_HTTP REQUEST fault on modifyCollection's RELOAD (OCMH:683, through collectionCmd; failures are collected, not thrown)
    leaves the old core at `readOnly=true` (CoreContainer:1739-1751) while state says the collection is writable.
  - The next add then throws at :238.
  - This is a real-bug candidate, read in the code, not run.
- **CoreAdminOperation:186**: only MIGRATE reaches it. Any injection lands on the same occurrence (#2) as the real buffer leak,
  or on an unrecorded retry handler (HBASE-20642's shape).
- **HashBasedRouter:67 via a split, STATE only**: killed by the `_stateVer_` override above. Only the FAULT form below
  (solr-inj-f) remains.

## 1. Summary

| id | point (throw) | pattern | root | workload | depth | confidence |
| --- | --- | --- | --- | --- | --- | --- |
| solr-inj-a | solr-adhoc-19, CoreContainer:1330 | P2 failed state write taken as "fall back to self-registration" | FAULT, ZooKeeper create (state-queue offer) | new TestCausynthAddReplicaState (from TestCausynthMigrateRuleTarget) | 1 | high |
| solr-inj-b | solr-adhoc-19, CoreContainer:1330 | P6 split placeholder replicas lose coreNodeName under non-legacy | CONFIG legacyCloud (field-backed) | solr-buggy-6101's workload, 2 nodes, 1x2 | 1 | high |
| solr-inj-c | solr-adhoc-13, RoutedAlias:350 | P1 alias view not refreshed after MAINTAINROUTEDALIAS | STATE (VIEW of /aliases.json) | new TestCausynthTraSyncCreate (from TestCausynthTraStartAlias) | 1 | medium |
| solr-inj-d | solr-adhoc-31, CollectionsHandler:1477 | P4 a wait's watcher never removed, so the view lags (P5) | STATE (VIEW of state.json) | solr-buggy-9440's workload | 1 | medium |
| solr-inj-e | solr-adhoc-19, CoreContainer:1330 | P8 5 s bound on the replica's state, then proceed without coreNodeName | CLOCK (Overseer nanoTime) | TestCausynthAddReplicaState | 1 | medium |
| solr-inj-f | restore-construction's HashBasedRouter:67 | P4 parent deactivated before the split's final commit (non-atomic switch) | FAULT SOLR_HTTP request (+ STATE order) | solr-buggy-6101's workload without legacyCloud | 1-2 | low-medium |
| solr-inj-g | solr-adhoc-07, ZkController:1326 | P10 registration moved to the background ahead of putCore | STATE (core map INITIAL, writer ORDER) | TestCausynthAddReplicaState | 1 | low-medium |
| solr-inj-h | reindex-cleanup's DeleteCollectionCmd:246 | P1 after P2: DELETE trusts the Overseer's cached aliases | FAULT ZooKeeper setData + STATE (VIEW of /aliases.json) | new TestCausynthDeleteAliasedCollection | 2 | low-medium |
| **solr-inj-u** (undetectable) | the solr-adhoc-19 coordination | P2 silent: failed state write swallowed, core never created | (FAULT, same door as a) | TestCausynthAddReplicaState | -- | not detected: high |

Spread: 6 points (19, 13, 31, HashBasedRouter:67, 07, DeleteCollectionCmd:246), 7 patterns (P1, P2, P4, P5, P6, P8, P10) and
4 root kinds (FAULT, CONFIG, STATE, CLOCK).

---

## 2. Detectable candidates

### solr-inj-a: AddReplicaCmd falls back to self-registration when the replica's state write fails

1. **Point.** solr-adhoc-19, `CoreContainer.java:1330`, `throw new @CausynthExceptionTarget("solr-adhoc-19") SolrException(..
   "non legacy mode coreNodeName missing")`. The guard is :1328-1329: `!Overseer.isLegacy(..)` and
   `cd.getCloudDescriptor().getCoreNodeName() == null`. Extend the marker to `"solr-adhoc-19,solr-inj-a"`, as the old bugs did.
2. **Pattern.** P2, a remote error handled as a generic failure that takes the wrong recovery path. Analogue: SOLR-6101 and
   SOLR-6197, a core-admin CREATE without coreNodeName refused in non-legacy mode, reached here through a failed ZooKeeper write
   instead of a configuration. It is the HDFS-17897/-12931 class: an error treated as "carry on".
3. **Mutation** (`AddReplicaCmd.java:246-267`, `getReplicaParams`, non-legacy branch):
   ```diff
        if (!Overseer.isLegacy(zkStateReader)) {
   +      boolean inState = true;
          if (!skipCreateReplicaInClusterState) {
            ZkNodeProps props = ...ADDREPLICA, state DOWN...;          // :248-258 unchanged
            try {
              ocmh.overseer.offerStateUpdate(Utils.toJSON(props));      // :260
            } catch (Exception e) {
   -          throw new SolrException(SolrException.ErrorCode.SERVER_ERROR, "Exception updating Overseer state queue", e);
   +          // the core registers itself when it comes up, as in legacy mode
   +          log.warn("Could not queue ADDREPLICA of {}; the core will register itself", createReplica.coreName, e);
   +          inState = false;
            }
          }
   -      params.set(CoreAdminParams.CORE_NODE_NAME,
   -          ocmh.waitToSeeReplicasInState(collectionName, Collections.singletonList(createReplica.coreName)).get(createReplica.coreName).getName());
   +      if (inState) {
   +        params.set(CoreAdminParams.CORE_NODE_NAME,
   +            ocmh.waitToSeeReplicasInState(collectionName, Collections.singletonList(createReplica.coreName)).get(createReplica.coreName).getName());
   +      }
        }
   ```
   - **Why the healthy run is unchanged.** With no fault the offer returns, `inState` stays true, and the CREATE carries
     coreNodeName exactly as before.
   - **Why the guard is still reached.** node0's `CoreContainer.create` evaluates the guard at :1328 with coreNodeName set, so
     it passes.
4. **Workload.** New `org.apache.solr.cloud.TestCausynthAddReplicaState#addReplicaOnTheOtherNode`, 2 nodes, copied from the first
   half of `TestCausynthMigrateRuleTarget` in the bug-check style (each failure returned, waits bounded by a count):
   ```java
   @BeforeClass setup: System.setProperty("use.perreplica", "false");   // as TestCausynthSnapshotBackup:62
                       configureCluster(2).addConfig("conf", configset("cloud-minimal")).configure();
   test: createCollection(C, "conf", 1, 1).setCreateNodeSet(jetty(1)).process(client); waitForActiveCollection(C, 1, 1);
         Exception added = null;
         try { addReplicaToShard(C, "shard1").setNode(jetty(0).getNodeName()).process(client); } catch (Exception e) { added = e; }
         int active = 0; for (int p = 0; p < 30 && (active = activeReplicas(C)) < 2; p++) Thread.sleep(1000);
         assertNull("ADDREPLICA: " + added, added); assertEquals(2, active);
   ```
   - **case.sh** (solr-bugs style): scope `core:org/apache/solr/cloud/api/collections/AddReplicaCmd` and
     `core:org/apache/solr/core/CoreContainer`.
   - **Target.** `target_occurrence='auto0/node0#epoch0/region/REGION.05d95c18-e743-3177-861c-d3167f8ea67b#1'`. That is node0's
     first `CoreContainer.create`; the region id is the one solr-buggy-6101 declares. The collection's own core is node1's #1.
   - **Depth.** `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` is enough.
5. **Trigger.**
   - **Root.** FAULT on the ZOOKEEPER write door `ZooKeeper.create` under `SolrZkClient.create` (:573-591; the door stands
     after ZkCmdExecutor's retries).
   - **Path.** `ZkDistributedQueue.offer:328` <- `Overseer.offerStateUpdate:1062` <- `AddReplicaCmd:260`, in the ADDREPLICA
     Overseer task (OVERSEER_TASK on the Overseer's node).
   - **Effect.** A ConnectionLoss past the retries: the queue item commits (the replica appears DOWN in state.json), but
     AddReplicaCmd sees the failure. The CREATE goes to node0 without coreNodeName and throws at :1330.
   - **Window.** The ADDREPLICA is the test method's second command, inside the window.
   - **Expected `report.py`.** MARKER_FLIPPED by a ZOOKEEPER create fault, no clock; depth 1.
6. **Why GraphChecker can detect it.**
   - **The same door has detected before.** solr-bugs-migrate-buffer-leak's accepted witness is the same door on the same path
     (`SolrZkClient.create#u17`, MigrateCmd:205 -> ZkDistributedQueue.offer:328, a ConnectionLoss past the retries in an
     Overseer task; native 10/10). overseer-lock-leak's witness is the same door type (native 10/10).
   - **The point's throw has fired before.** It is reached and confirmed in solr-buggy-6101 and -6197 (native 10/10).
   - **Today's verdict.** solr-adhoc-19 is RUN_DEFECT, vacuous (NO_ROOT), on its study workload (X1).
   - **Why the unmodified code is UNSAT on this workload.** A failed offer throws "Exception updating Overseer state queue"
     (:262) before any CREATE, and every non-legacy CREATE carries coreNodeName (:265-266; CreateCollectionCmd:361). No
     legacyCloud world helps either: in this tree `isLegacy` is a getter root, refused on the Overseer, and only the node-side
     `true` would be reachable, which makes the guard false.
7. **Risks.**
   - EXPLORE must plan the Overseer's ADDREPLICA task, the producer of the request node0's create serves, and flip its offer
     door. migrate-buffer-leak's run did exactly this.
   - The coreNodeName crosses HTTP as a parameter that the formula likely holds. That is fine: the witness session itself
     observes the fatal (as in 9440, whose CONFIRM is the run itself), and `polarityDecides` rests on the door marker.
   - Set `use.perreplica` false so the Overseer takes no PRS path.
   - Confidence: **high**.

### solr-inj-b: the split's placeholder replicas lose their coreNodeName under non-legacy

1. **Point.** solr-adhoc-19, `CoreContainer.java:1330`, here at the create of a split placeholder replica on the node that does
   not host the parent.
2. **Pattern.** P6, an unhandled configuration-dependent path. Analogue: SOLR-6101 (SPLITSHARD under legacyCloud=false) and
   SOLR-6197 (MIGRATE under legacyCloud=false). This is a third path of the same family: the split's extra replicas, created with
   `SKIP_CREATE_REPLICA_IN_CLUSTER_STATE` (SplitShardCmd:470-516, :512, the addReplica loop :581-585).
3. **Mutation.**
   - **Base.** graphchecker/solr-checks plus the legacyCloud holder: cherry-pick fb0c5878b2 from `graphchecker/solr-bug-6101`,
     or da4cea38b8 from solr-bug-6197. It adds one import to AddReplicaCmd, so its lines are +1 from the checks tree: :247-268.
   - **Diff.** The coreNodeName lookup moves into the branch that writes the replica into state:
   ```diff
        if (!CausynthLegacyCloud.isLegacy(zkStateReader)) {
          if (!skipCreateReplicaInClusterState) {
            ... offerStateUpdate(ADDREPLICA) ...
   -      }
   -      params.set(CoreAdminParams.CORE_NODE_NAME,
   -          ocmh.waitToSeeReplicasInState(collectionName, Collections.singletonList(createReplica.coreName)).get(createReplica.coreName).getName());
   +        params.set(CoreAdminParams.CORE_NODE_NAME,      // only for a replica this call put into the state
   +            ocmh.waitToSeeReplicasInState(collectionName, Collections.singletonList(createReplica.coreName)).get(createReplica.coreName).getName());
   +      }
        }
   ```
   - **Why the healthy run is unchanged.** The workload runs with legacyCloud=true, as 6101 does. The whole non-legacy block is
     skipped. A CREATE without coreNodeName is valid in legacy mode: the node finds its name by node and core name
     (ZkController.waitForCoreNodeName :1806-1830), and the split completes.
4. **Workload.** solr-buggy-6101's `TestCausynthSplitShardLegacy` (graphchecker/solr-bug-6101 040ae6d4c6) with three changes:
   - `configureCluster(2)` and `createCollection(C, "conf", 1, 2)`, so a 1x2 collection makes SplitShardCmd create placeholder
     replicas on the non-parent node;
   - `waitForActiveCollection(C, 1, 2)`;
   - `activeClusterShape(2, 4)` after the split.

   The case is 6101's: scope `CoreContainer`, `SplitShardCmd`, `=CausynthLegacyCloud`, plus `AddReplicaCmd`; depth 0. The
   target is node1's CoreContainer.create of the first placeholder. That is node1's #2, after the collection's second replica;
   read the index from the seed.
5. **Trigger.**
   - **Root.** CONFIG `CONFIG:legacyCloud==true` moved to false. The value is field-backed (`CausynthLegacyCloud.legacyCloud`)
     and written at every read, cluster-wide.
   - **Effect.** The Overseer's CreateCollectionCmd and AddReplicaCmd take the non-legacy branch, so the collection's CREATE and
     the sub-shard leaders' CREATEs carry coreNodeName. The placeholders' CREATEs (skip=true) do not, so node1 throws at :1330.
   - **Window.** The test sets legacyCloud itself, inside the window.
   - **Expected `report.py`.** MARKER_FLIPPED (CONFIG), `configurationOnly`; depth 1.
6. **Why GraphChecker can detect it.**
   - **Precedent.** solr-buggy-6101 and -6197: the same root on the same point, natively 10/10 through the field plant. The
     engine support for that plant is on this branch: 61e881776, e5c894636, ad3d08028.
   - **Why the unmodified code is UNSAT.** In the false world every non-legacy CREATE, skip=true included, carries coreNodeName.
7. **Risks.**
   - A split with replication factor 2 records longer: the sub-replicas recover and ReplicaMutator switches the slices. Keep
     depth 0 and few documents.
   - It is close to 6101 (same pattern, root and point); only the code path is new.
   - Confidence: **high**.

### solr-inj-c: the routing node no longer refreshes its alias view after MAINTAINROUTEDALIAS

1. **Point.** solr-adhoc-13, `RoutedAlias.java:350` in `doSynchronous`. The guard is :347-348:
   `!observedCols.contains(targetCollectionDesc.creationCollection)` on `zkStateReader.aliasesManager.getAliases()`.
2. **Pattern.** P1, stale cached coordination state not refreshed on a miss. Analogues: SOLR-40, SOLR-9440. The hazard is written
   in the code's own comment at :400-402: "If we didn't do this, our zkStateReader might not yet know about the new alias ...
   and we might think we failed."
3. **Mutation** (`RoutedAlias.java:400-403`, in `ensureCollection`; below :350, so the marker does not move):
   ```diff
          MaintainRoutedAliasCmd.remoteInvoke(collectionsHandler, getAliasName(), targetCollection);
          ...
   -      // Ensure our view of the aliases has updated. If we didn't do this, our zkStateReader might
   -      //  not yet know about the new alias (thus won't see the newly added collection to it), and we might think
   -      //  we failed.
   -      coreContainer.getZkController().getZkStateReader().aliasesManager.update();
          updateParsedCollectionAliases(coreContainer.getZkController().getZkStateReader(),false);
   ```
   - **Why the healthy run passes.** The Overseer writes `/aliases.json` (MaintainRoutedAliasCmd.addCollectionToAlias :72-84)
     before it completes the task and writes the response on the Overseer collection queue (OCP queue).
   - The routing node receives the aliases watch event before the response-node event: one ZooKeeper session, ordered events.
   - Its alias watcher then needs one getData. The request thread needs two ZooKeeper round trips (response read, delete) before
     it reads :346-347.
   - So in practice the view holds the new collection when the guard is evaluated. Take 20 native healthy runs (as 9440's README
     did) before the case runs.
4. **Workload.** New `TestCausynthTraSyncCreate#documentPastTheHeadCollection`, 2 nodes, copied from `TestCausynthTraStartAlias`
   (it finds the Overseer's node and puts the TRA's collection template on the other node). Changes:
   - **Fixed start** `2019-09-14T00:00:00Z`, with no date math. The start rewrite never runs (TimeRoutedAlias:366-390, the real
     tra-start bug's code).
   - Interval `+1DAY`; no plain alias; `use.perreplica` false.
   - **One add** with `timestamp_dt=2019-09-15T01:00:00Z`. It is past the head's range, so creation is SYNCHRONOUS
     (TimeRoutedAlias.calcCandidateCollection :492-506).
   - Then commit, and assert the document is in `causynthTraSync__TRA__2019-09-15`.

   **case.sh.** Scope `RoutedAlias`, `TimeRoutedAlias`, `RoutedAliasUpdateProcessor`, `MaintainRoutedAliasCmd`. RAUP and the
   TRA classes must be in the scope: their earlier alias reads in the same request (RAUP.getAliasProps :131,
   findCandidateGivenValue :456/:463) must fall into their own region occurrences, not into doSynchronous's role prefix, where the
   earliest-read rule would pick them instead. `target_occurrence=first`: only the routing node runs doSynchronous.
5. **Trigger.**
   - **Root.** STATE, a VIEW pairing of the routing node's `/aliases.json` view. The routing node is the non-Overseer node, the
     one that hosts the head collection's leader.
   - **Reader.** doSynchronous's first alias read (:346 `updateParsedCollectionAliases(.., true)` or :347 `getAliases()`). It
     observed v(n+1), MAINTAIN's write.
   - **Re-paired writer.** VIEW@n, the node watcher's decode of the version that created the TRA, decoded before the add.
   - **Hold.** The node's publication of v(n+1) waits until doSynchronous exits. The recorded span is about the OCP response
     latency (milliseconds), well under VIEW_HOLD_MAX.
   - **Expected `report.py`.** STATE_PAIRING_FLIPPED, no root moved; depth 1.
6. **Why GraphChecker can detect it.**
   - **Precedent.** solr-bugs-tra-start-overwrite: the same view, the same node role (a non-Overseer node routing a TRA
     document), STATE_PAIRING_FLIPPED VIEW@1, natively 10/10 with VIEW_HOLD rows.
   - **Today's verdict.** solr-adhoc-13 is a named bound: its slow study workload never reached doSynchronous.
   - **Why the unmodified code is UNSAT, by the engine's own rule.** `aliasesManager.update()` (:403) is a synchronous
     publication in the reader's own context. PairingFlip's `floor` is therefore v(n+1), and nothing older is offered.
7. **Risks.**
   - The earliest-read rule: any `/aliases.json` read in role work of the same request before doSynchronous takes the slot.
     Check the seed's read rows.
   - The healthy race in 3: a rare native throw would show in the control.
   - MAINTAIN creates a collection inside the window; the TRA bug check took 943 s.
   - Confidence: **medium**.

### solr-inj-d: CREATE's wait for an active collection leaks its watcher, so FORCELEADER reads a lagging view

1. **Point.** solr-adhoc-31, `CollectionsHandler.java:1477`. The guard is :1475-1476,
   `leader != null && leader.getState() == ACTIVE`, on the receiving node's view, read at :1460/:1466.
2. **Pattern.** P4 (a cleanup is missing: a watcher registered for a wait is never removed), which yields P5 (the reader's view
   lags behind its watcher). Analogues: SOLR-9440 (a node keeps the DocCollection of a collection it only watched once) and
   SOLR-8323 (the watched versus lazy collection lifecycle). It differs from 9440: there the cached view freezes because the
   eviction is gone; here the view stays watched and only lags.
3. **Mutation** (`CollectionsHandler.waitForActiveCollection` :1548-1589; the predicate body is unchanged). Use fully qualified
   names, so no import is added and :1477 does not move:
   ```diff
        try {
   -      cc.getZkController().getZkStateReader().waitForState(collectionName, seconds, TimeUnit.SECONDS, (n, c) -> {
   +      org.apache.solr.common.cloud.CollectionStatePredicate active = (n, c) -> {
            ... predicate body unchanged ...
   -      });
   +      };
   +      java.util.concurrent.CountDownLatch done = new java.util.concurrent.CountDownLatch(1);
   +      cc.getZkController().getZkStateReader().registerCollectionStateWatcher(collectionName,
   +          (n, c) -> { if (active.matches(n, c)) done.countDown(); return false; });  // keeps watching: never removed
   +      if (!done.await(seconds, TimeUnit.SECONDS)) throw new TimeoutException();
        } catch (TimeoutException | InterruptedException e) {
   ```
   - **What changes.** node0 now watches the collection for good: `registerCollectionStateWatcher` (ZkStateReader:1827-1838)
     and a watcher that returns false.
   - **Why the healthy run passes.** FORCELEADER reads the watched DocCollection. By the time the client has seen the replica
     DOWN in its own waitForState and sent FORCELEADER, node0's watcher has fetched the same `state.json` version: both watches
     fire on one write, and the client adds an HTTP hop. So the leader is DOWN, FORCELEADER applies, and nothing throws.
   - A rare native refusal is possible (eventual consistency). Take 20 healthy runs.
4. **Workload.** `TestCausynthForceLeaderStaleView` from graphchecker/solr-bug-9440 (the 2e2acd32d6 form), copied onto the
   injected tree:
   - Drop its Overseer retry-delay workaround (1e7324c461); it is not needed here.
   - Recommended reorder: send FORCELEADER right after the client sees the replica DOWN, and only then call
     `waitForJettyToStop(second)`. Then node0's held publication of the DOWN version and FORCELEADER's read are well inside
     VIEW_HOLD_MAX.
   - case.sh as solr-buggy-9440: scope `CollectionsHandler`, `target_occurrence=first`, depth 0.
5. **Trigger.**
   - **Root.** STATE, a VIEW pairing of node0's `/collections/causynthForceLeaderStale/state.json` view.
   - **Reader.** FORCELEADER's first read (:1460 `getClusterState()`, :1466 `getCollection`). It observed v_down, the DOWNNODE
     write after node1's preClose.
   - **Re-paired writer.** node0's decode of v_active (replica ACTIVE and leader), made through the leaked watcher.
   - **Hold.** node0's publication of v_down waits until FORCELEADER's occurrence exits at the throw. FORCELEADER is an admin
     request with no `_stateVer_`, so nothing overrides the hold.
   - **Expected `report.py`.** STATE_PAIRING_FLIPPED; depth 1.
6. **Why GraphChecker can detect it.**
   - **Precedent.** solr-buggy-9440: the same point, the same workload, node0's stale view leading to the refusal, natively
     10/10. Its plant already holds the FORCELEADER reader's view (VIEW_HOLD rows). tra-start-overwrite shows a VIEW pairing as
     the moved choice.
   - **Why the unmodified code is UNSAT.** node0 reads the collection lazily (LazyCollectionRef.get, ZkStateReader:836-863), a
     live fetch the engine never defers, so no pairing is offered. The 9440 SessionExpired world passes on the fixed code (its
     README: fixed tree 5/5 pass, 20/20 healthy).
   - **Today's verdict.** solr-adhoc-31 is a named bound (ForceLeaderTest, 2 h cap).
7. **Risks.**
   - VIEW_HOLD_MAX (3 s of recorded time) if node1's shutdown runs long between its DOWNNODE and FORCELEADER; the reorder in 4
     addresses this.
   - The healthy-run lag race.
   - The leaked watcher adds a little watch work on node0.
   - Confidence: **medium**.

### solr-inj-e: AddReplicaCmd bounds its wait for the replica's state at 5 s, then proceeds

1. **Point.** solr-adhoc-19, `CoreContainer.java:1330`.
2. **Pattern.** P8, a time assumption: "the Overseer applies the ADDREPLICA within 5 s; past that, let the core register
   itself". Analogue: SOLR-18406 and SOLR-18413 (a time bound assumed across components).
3. **Mutation** (`AddReplicaCmd.java:265-266`; it replaces the 120 s `waitToSeeReplicasInState`, OCMH:695-724):
   ```diff
   -      params.set(CoreAdminParams.CORE_NODE_NAME,
   -          ocmh.waitToSeeReplicasInState(collectionName, Collections.singletonList(createReplica.coreName)).get(createReplica.coreName).getName());
   +      // don't hold the Overseer on a slow state update: after 5 s the core registers itself
   +      String coreNodeName = null;
   +      long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
   +      while (coreNodeName == null && System.nanoTime() < deadline) {
   +        for (Replica r : zkStateReader.getClusterState().getCollection(collectionName).getReplicas()) {
   +          if (createReplica.coreName.equals(r.getCoreName())) coreNodeName = r.getName();
   +        }
   +        if (coreNodeName == null) Thread.sleep(100);
   +      }
   +      if (coreNodeName != null) params.set(CoreAdminParams.CORE_NODE_NAME, coreNodeName);
   ```
   **Why the healthy run passes.** The state updater applies the ADDREPLICA in milliseconds (unbatched in an automatic cluster,
   Overseer:291). The poll finds the replica on its first or second lap, coreNodeName is set, and nothing throws.
4. **Workload.** TestCausynthAddReplicaState, as for solr-inj-a, with the same case.sh.
5. **Trigger.**
   - **Root.** CLOCK. The Overseer's `System.nanoTime()` at the loop condition reads at least 5 s past the deadline read.
   - **Effect.** The loop exits before its first lookup, the CREATE goes out without coreNodeName, and node0 throws at :1330.
   - **Window.** One forward skew on one node, inside the ADDREPLICA task.
   - **Expected `report.py`.** CLOCK_SKEW; depth 1.
6. **Why GraphChecker can detect it.**
   - **Precedent.** solr-18406: two `System.nanoTime()` reads on one node (setReserveDuration :211-212, IndexCommitWrapper.delete
     :345); a skew between them decides the throw. CONFIRM and native 10/10, with the clocks planted natively.
   - **Why the unmodified code is UNSAT.** waitToSeeReplicasInState reads its clock through `TimeOut`/`TimeSource` and throws on
     timeout (OCMH:718-719) before any CREATE is sent.
7. **Risks.**
   - The two clock reads must be minted in AddReplicaCmd: direct calls in a scoped class, as 18406's were in
     IndexDeletionPolicyWrapper.
   - COMPOSE must place both cells on the timeline. A 5 s forward jump inside one task is a large but legal skew; 18406's was an
     hour.
   - Confidence: **medium** (medium-high if the CLOCK root is minted as in 18406).

### solr-inj-f: the split deactivates the parent before its final commit (a non-atomic switch)

1. **Point.** restore-construction's throw `HashBasedRouter.java:67`, "No active slice servicing hash code". It is taken where
   the client routes the first add after the split, on client0, as restore-construction declares.
2. **Pattern.** P4, a partial failure leaves state inconsistent, here through a two-step state switch. Analogues: SOLR-9455 and
   SOLR-13945 (the split's state switch and its cleanup), and the restore-construction leftover.
3. **Mutation** (`SplitShardCmd.java:551-567`, the `repFactor == 1` branch): parent INACTIVE goes as its own message before the
   final commit, and the sub-shards' ACTIVE stays where it is:
   ```diff
          if (repFactor == 1) {
   +        // stop routing to the parent before the final commit
   +        ocmh.overseer.offerStateUpdate(Utils.toJSON(new ZkNodeProps(Overseer.QUEUE_OPERATION,
   +            OverseerAction.UPDATESHARDSTATE.toLower(), slice.get(), Slice.State.INACTIVE.toString(),
   +            ZkStateReader.COLLECTION_PROP, collectionName)));
            t = timings.sub("finalCommit");
            ocmh.commit(results, slice.get(), parentShardLeader);              // :556
            ...
   -        propMap.put(slice.get(), Slice.State.INACTIVE.toString());         // :562
   ```
   **Why the healthy run passes.** Both messages are applied before SPLITSHARD returns. The Overseer is unbatched, so each
   message gets its own write. The workload adds only before and after the split.
4. **Workload.** solr-buggy-6101's TestCausynthSplitShardLegacy without its legacyCloud lines: the plain SplitShardTest#doTest
   shape on 1 node.
   - The wait for `activeClusterShape(2, 3)` becomes at most 30 polls, 1 s apart, with no assert.
   - Then one more add and a commit, with the count assert at the end.
   - Scope `SplitShardCmd` and `solrj:org/apache/solr/common/cloud/HashBasedRouter`; client faults on (the default).
5. **Trigger.**
   - **Root.** FAULT, SOLR_HTTP REQUEST, on the final commit (OCMH.softCommit's HttpSolrClient, OCMH:532-541, called at
     SplitShardCmd:556).
   - **Effect.** SplitShardCmd fails after parent INACTIVE was queued, and `cleanupAfterFailure` (:679ff) runs. If its
     `forceUpdateCollection` read (:684) comes before the Overseer applies the INACTIVE write, the cleanup neither reactivates
     the parent (:727-730) nor keeps the sub-shards (CONSTRUCTION, then DELETESHARD). The parent stays INACTIVE with no
     sub-shards, and the client's add throws at hashToSlice :67.
   - **Depth.** 1 when the replay happens to order the cleanup's read first. Otherwise 2: the cleanup's store read re-paired
     before the Overseer's INACTIVE write, held by a writer ORDER.
   - **Expected `report.py`.** MARKER_FLIPPED (SOLR_HTTP), possibly with STATE_PAIRING_FLIPPED.
6. **Why GraphChecker can detect it.**
   - **Precedent.** restore-construction: the same throw on client0, MARKER_FLIPPED, natively 9/10. The HTTP request door is
     also flipped in migrate-buffer-leak's alternative world.
   - **Why the unmodified code is UNSAT.** On a 1x1 split the switch is a single message after the commit, so a failure before
     it leaves the parent ACTIVE.
   - **Not available.** The pure STATE world at the leader's routing read (DZUP.setupRequest :609-611, paired with the
     intermediate `state.json`): the client's add carries `_stateVer_`, the leader refreshes, and the pairing is overridden.
7. **Risks.** The race between the cleanup's read and the state updater means a few native reproductions out of 10 at best.
   Confidence: **low-medium**.

### solr-inj-g: core registration moved to the background ahead of the core map

1. **Point.** solr-adhoc-07, `ZkController.java:1326`. In register, `cc.getCore(desc.getName())` at :1317 returns null and
   :1326 throws.
2. **Pattern.** P10, a concurrent-initialization race on shared state: the HDFS-14311 shape, GraphChecker's known limit. Solr
   analogue: SOLR-14969, concurrent core creation (`inFlightCreations`, CoreContainer:1294).
3. **Mutation** (`CoreContainer.registerCore` :1257-1280; the line count is unchanged in effect):
   ```diff
        assert core.getName().equals(cd.getName()) : ...;
   +    if (registerInZk) zkSys.registerInZk(core, true, skipRecovery);   // register in the background: CREATE returns sooner
        SolrCore old = solrCores.putCore(cd, core);
        ...
   -      if (registerInZk) {
   -        zkSys.registerInZk(core, false, skipRecovery);
   -      }
          return null;
        } else {
          ...
          old.close();
   -      if (registerInZk) {
   -        zkSys.registerInZk(core, false, skipRecovery);
   -      }
          return old;
   ```
   **Why the healthy run passes.** The background register (ZkContainer.registerInZk with background=true, :198-238, the
   coreZkRegister executor) makes ZooKeeper round trips before `cc.getCore`: waitForState, the shard-terms write, joinElection
   and getLeader. putCore runs microseconds after the submit, so the core is found.
4. **Workload.** TestCausynthAddReplicaState. The ADDREPLICA core is a follower, so its election never calls `cc.getCore`: the
   `getCore` calls in ShardLeaderElectionContext (:76-283) run only for a leader. Scope `ZkController`, `CoreContainer`,
   `SolrCores`, `ZkContainer`; target node0's register #1.
5. **Trigger.**
   - **Root.** STATE re-pairing of the SolrCores map read (`getCoreFromAnyList` under `cc.getCore`) with that key's INITIAL,
     before putCore.
   - **Hold.** CONFIRM holds the writer putCore after the read (a writer ORDER).
   - **Expected `report.py`.** STATE_PAIRING_FLIPPED; depth 1.
6. **Why GraphChecker can detect it.**
   - **Precedent.** solr-adhoc-07's own run (X1B): UNSAT, substantive; "the core-map read offered another writer: its
     re-pairing explored", no witness. It was refused only because putCore precedes register on the same thread.
   - **Negative precedent.** HDFS-14311 (P10) was not detected.
7. **Risks.**
   - The engine must treat the executor submit as the start edge, so that putCore and the read are concurrent.
   - CONFIRM's ORDER hold must sit before the read; this is where 14311 failed.
   - The recording's shape changes: CREATE returns before register.
   - Confidence: **low-medium**. If it is not detected, it can serve as a second "cannot detect" example (P10).

### solr-inj-h: DELETE trusts the Overseer's cached aliases

1. **Point.** reindex-cleanup's throw `DeleteCollectionCmd.java:246`.
2. **Pattern.** P1 (a stale cache not refreshed) that follows a P2 event (an alias write that committed but reported failure).
   Analogues: the code's own comments at :86 and :237 ("aliases may have been stale; get latest from ZK"), and SOLR-40.
3. **Mutation.** Remove the two refreshes. Replace each with a comment line so :246 does not move:
   ```diff
        if (zkStateReader.aliasesManager != null) { // not a mock ZkStateReader
   -      zkStateReader.aliasesManager.update(); // aliases may have been stale; get latest from ZK      // :86
   +      // the Overseer keeps its own alias view current
        }
        ...
        if (aliasesRefs.size() > 0) {
   -      zkStateReader.aliasesManager.update(); // aliases may have been stale; get latest from ZK      // :237
   +      // (no refresh)
   ```
   **Why the healthy run passes.** The Overseer itself ran DELETEALIAS and set its own view on success
   (`applyModificationAndExportToZk`, ZkStateReader:2344-2397, setIfNewer at :2373). The view is current, so DELETE is not
   refused.
4. **Workload.** New `TestCausynthDeleteAliasedCollection`, 2 nodes, in the style of TestCausynthReindexAbortAlias (alias steps
   tolerate their failures): CREATE C; CREATEALIAS A->C; DELETEALIAS A (a failure is logged and the test goes on); DELETE C (its
   failure returned); assert C is gone.
   - **case.sh:** `client_fault_transports=(NONE)`. A client-side fault on DELETEALIAS leaves A in place and fires :246 on the
     unmodified tree too, as a correct refusal.
   - **Depth:** the default; depth 2 is needed.
5. **Trigger.**
   - **The fault.** ZOOKEEPER setData on `/aliases.json` in DELETEALIAS's compare-and-set write: `SolrZkClient.setData`, the
     door after the write (:527, the S9440a door type). The alias is gone in ZooKeeper, but the Overseer's setIfNewer is skipped
     (:2392-2393 rethrows the KeeperException).
   - **The pairing.** STATE: DELETE's first alias read (checkAliasReference :233) paired with VIEW@(A present), by holding the
     Overseer node's watcher publication of the new version.
   - **Expected `report.py`.** MARKER_FLIPPED with STATE_PAIRING_FLIPPED; depth 2.
6. **Why GraphChecker can detect it.**
   - **Precedent.** reindex-cleanup: this throw, with an Overseer-side ZooKeeper fault root, natively 10/10. 9440's S9440a: a
     setData ConnectionLoss after the write, confirmed. tra-start: an aliases VIEW pairing.
   - **Why the unmodified code is UNSAT** (with client faults off). The `update()` at :86 is a synchronous publication in
     DELETE's own context, so `floor` excludes every older view.
7. **Risks.** Depth 2; the DELETEALIAS task must be in the closure for its door to be flipped. Confidence: **low-medium**.

---

## 3. Undetectable candidate

### solr-inj-u: a failed replica state write is swallowed and the core is never created

1. **Point.** The coordination solr-adhoc-19 guards: the Overseer's replica entry against the node's core creation. The declared
   throw is `CoreContainer.java:1330`.
2. **Pattern.** P2, silent: the remote error is swallowed, so the replica is "created" in the state while no core exists.
   Analogues: bug-study #37/#39 (a term-write failure leaves a ghost replica), and "phantom DOWN replica" reports.
3. **Mutation** (`AddReplicaCmd.java:261-262` and :175-176):
   ```diff
            } catch (Exception e) {
   -          throw new SolrException(SolrException.ErrorCode.SERVER_ERROR, "Exception updating Overseer state queue", e);
   +          log.warn("Could not queue ADDREPLICA of {}; the Overseer will create it later", createReplica.coreName, e);
   +          return null;
            }
        ...
          ModifiableSolrParams params = getReplicaParams(...);                 // :175
   -      shardRequestTracker.sendShardRequest(createReplica.node, params, shardHandler);
   +      if (params != null) shardRequestTracker.sendShardRequest(createReplica.node, params, shardHandler);
   ```
   **Why the healthy run is unchanged.** With no fault the code path is identical.
4. **Workload.** TestCausynthAddReplicaState, as for solr-inj-a.
5. **Trigger and symptom.**
   - **Trigger.** The same door as solr-inj-a. In that world the queue item commits (the replica is DOWN in the state, with its
     coreNodeName) and getReplicaParams returns null, so no CREATE is sent.
   - **Why ADDREPLICA still succeeds.** The task's `waitForCoreNodeName` (:182, then OCMH:545-570) finds the DOWN replica, and
     ADDREPLICA answers success. Nothing throws: `CoreContainer.create` never runs.
   - **Symptom, checkable natively.** The workload's bounded wait ends with 1 active replica, and `assertEquals(2, active)`
     fails. The collection keeps a coreless DOWN replica for good. To check it, plant the ConnectionLoss at that door with
     scratch code, as 9440's README did.
6. **Why GraphChecker cannot detect it.**
   - GraphChecker answers whether a declared throw `(r, c, i)` is reached.
   - In the only world where this bug acts, the coordination's guarded throw never executes: no CREATE is sent, so there is no
     create occurrence at all.
   - The failure lives only in the test's assertion and in a missing core. That is a silent wrong state with a liveness-style
     symptom (the replica never becomes active), and neither is a declared target.
   - The fault world is explored and admitted but never observes the fatal, so the run ends UNSAT_CLOSED, which is correct by
     design.
   - The contrast with solr-inj-a is the point: the same door and the same code spot, detectable only when the wrong state
     reaches a guarded throw.
7. **Confidence that it is not detected:** high.

---

## 4. Ranked recommendation (Solr: 5 detectable)

1. **solr-inj-a** (19, FAULT, P2): the exact door precedent (migrate-buffer-leak) and a one-flip chain to the point's own
   throw. The unmodified code throws before any CREATE.
2. **solr-inj-c** (13, STATE, P1): the code's own comment names the hazard. Once the synchronous refresh is gone, PairingFlip
   offers exactly this read; precedent tra-start (VIEW of `/aliases.json`, natively 10/10).
3. **solr-inj-b** (19, CONFIG, P6): the 6101/6197 root on the same point, with the engine's field plant (natively 10/10), on a
   new code path.
4. **solr-inj-e** (19, CLOCK, P8): 18406's mechanism (two nanoTime reads on one node); a single forward skew decides the throw.
5. **solr-inj-d** (31, STATE, P4/P5): the 9440 workload is proven fast. The leaked watcher turns a strongly consistent lazy read
   into a lagging one.

If spread over points matters more than certainty, replace #4 with **solr-inj-g** (07) for a fourth point; it is the weakest
of the set (P10). solr-inj-u is the optional "cannot detect" example, a silent twin of #1.

## 5. Doubts

- **Three of the five most reliable candidates sit on CoreContainer:1330** (a, b, e). Solr's other points can only be reached
  through VIEW pairings (c, d) or through depth-2 worlds (f, h). The brief allows the same point with a clearly different
  pattern and root, and here all three differ (P2/FAULT, P6/CONFIG, P8/CLOCK).
- **None of the new (point, workload) pairs has been run on the unmodified tree.** UNSAT is expected from code reading and the
  engine rules quoted in §0.4. Run the control (the unmodified tree with the same workload, expected UNSAT) and 20 native
  healthy runs for each pick before the injected runs.
- **The STATE candidates (c, d) depend on three things.**
  - The earliest VIEW read per view in the target occurrence must be the right read; check the seed's read rows.
  - VIEW_HOLD_MAX is 3 s of recorded time. For d, that is why the workload reorder is recommended.
  - Both have a small native eventual-consistency race in the healthy run.
- **Latent bugs seen on today's tree (not used, not run).** If a lead wants new-bug candidates instead:
  - DZUP:238: a RELOAD request fault leaves the core read-only.
  - RAUP:133/:247: no refresh on a miss (the SOLR-40 shape).
  - A split with replication factor 2: the cleanup's read races ReplicaMutator's switch, which can leave the parent INACTIVE with
    the sub-shards deleted (HashBasedRouter:67).
- **solr-adhoc-05 dropped:** the replica is awaited three times before :1274, so a single plausible removal changes nothing.
