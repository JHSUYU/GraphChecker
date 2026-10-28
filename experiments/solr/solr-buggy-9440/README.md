# SOLR-9440 put back (solr-buggy-9440, point solr-adhoc-31)

## The bug

[SOLR-9440](https://issues.apache.org/jira/browse/SOLR-9440) (fix 39376cd8b5e, 2017):
`ZkStateReader.removeCollectionStateWatcher` could cache a `DocCollection` reference and never update it, returning
stale state from `ClusterState`. When the last watcher (and local core) of a collection was removed, the reader
dropped the ZooKeeper watch but left the collection's `DocCollection` in `watchedCollectionStates`, while its
`StateWatcher` returns early for a collection no longer watched. So a node that had watched a collection it does not
host -- any `waitForState`, e.g. `CollectionsHandler.waitForActiveCollection` after a CREATE -- kept serving that
frozen state forever, neither refreshed nor lazy. The fix evicts the entry back to a `LazyCollectionRef` and rebuilds
the cluster state.

Point solr-adhoc-31 is FORCELEADER's guard `CollectionsHandler.java:1477`, "The shard already has an active leader.
Force leader is not applicable", on the receiving node's view of the slice's leader. The study's row names this bug:
re-pair that read with the frozen `DocCollection` the removal left, in which the killed leader is still ACTIVE, and
FORCELEADER is refused.

## What was put back, on graphchecker/solr-bug-9440

`graphchecker/solr-checks` (12d23091d1) plus four commits (the last, 1e7324c461, is what the verdict ran on):

- **The bug, by hand** (aa5c404b12): `ZkStateReader.removeDocCollectionWatcher` (where
  `removeCollectionStateWatcher` and every `waitForState` end) no longer evicts -- the
  `watchedCollectionStates.remove` + `lazyCollectionStates.put(new LazyCollectionRef)` + `constructState` under the
  update lock are gone; the watch itself is still dropped. The same eviction in `unregisterCore` (SOLR-8323's, a
  local core's close, not part of this fix) stays.
- **The workload and the target** (42e4f16231): `TestCausynthForceLeaderStaleView`, and `solr-buggy-9440` added to
  the marker on FORCELEADER's throw (beside `solr-adhoc-31`); 2e2acd32d6 drops the workload's second watch (below).
- **1e7324c461, a GraphChecker workaround: the Overseer waits before it retries a failed state write.** A test-only
  static, `Overseer#failedStateWriteRetryDelayMs` (0 unless a test sets it; the workload sets 5 s in `@BeforeClass`
  and resets it in `@AfterClass`). In the state-update loop's main exception path (`Overseer.java`, the
  `catch (Exception e)` that logs "Exception in Overseer main queue loop" and sets `refreshClusterState`), after a
  `KeeperException` the loop sleeps that long before it refreshes and re-processes the failed message, so the
  messages queued meanwhile are written after the wait. Without a failed ZooKeeper write nothing waits (the catch is
  not reached). It adds no happens-before and never decides the throw: with the fault and the wait, the fixed code
  still evicts the entry to a `LazyCollectionRef` and FORCELEADER passes (native checks below). It was made for
  S9440a's witness; the accepted witness (S9440b) never reaches it.

## The workload

`org.apache.solr.cloud.TestCausynthForceLeaderStaleView#forceLeaderOnAWatchingNode` (two nodes, 2e2acd32d6): a 1x1
collection lives on node1; an `HttpSolrClient` to node0 sends every collection request. node0's `CollectionsHandler`
waits for the new collection to be active (`waitForActiveCollection`, a state watch it drops once the replica is
ACTIVE). node1 is then stopped; once the test client sees the replica DOWN, FORCELEADER goes to node0. It finds the
leader DOWN, so it is applicable; no live replica can take over, and after its 9 x 5 s wait it answers without a
leader. Natively it passes on both trees.

Why natively the bug does not fire here (native probes on the buggy tree, scratch `TestCausynthS2Scratch#probeView*`):
the CREATE's wait is satisfied at its registration (the replica is already ACTIVE when the CREATE returns), and in
8.11 a registration refresh publishes twice -- `refreshAndWatchChildren` (per-replica states), then the state
refresh. The first publication's notification drops the watcher; the second publish, of a collection no longer
watched, removes the entry (`publishWatchedCollection`'s race resolution with `unregisterCore`, SOLR-8323,
`ZkStateReader.java:2177-2181`). node0 then reads the collection lazily: `watched=false lazy=true` right after the
CREATE, and after a register-and-drop of a watcher of its own. With the bug a node's view freezes only when its last
watcher is dropped on a watch EVENT (one publication). The bug's own scenario: node0's CREATE wait registers before
the replica is ACTIVE, the replica's ACTIVE event satisfies it, the watch is dropped on that single publication, and
node0 keeps the replica ACTIVE and leading for good: FORCELEADER after node1 stopped refuses.

An earlier form of the workload (42e4f16231) added a second watch on node0 (wait until node1 is gone) as the last
refresh; the probes show such a registration evicts a frozen entry instead of refreshing it, so it was removed.

The workaround (1e7324c461) changes nothing in a run without a failed Overseer write: natively the workload passes
20/20 on the buggy tree and 20/20 on the fixed tree (below).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-31,solr-buggy-9440")` on FORCELEADER's throw, `CollectionsHandler.java:1477` |
| the occurrence | `target_occurrence` in `case.sh` | `first`: the FORCELEADER request on node0 (`forceLeaderElection`'s region folds into the request's occurrence, as in solr-adhoc-31's seeds) |
| scope | `case.sh` | `CollectionsHandler`; the ZooKeeper-state classes come from `system.sh` (ZkStateReader, ClusterState, DocCollection, Slice, Replica) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| workaround | the tree (1e7324c461) | `Overseer#failedStateWriteRetryDelayMs` = 5 s, set by the workload: the state-update loop waits after a failed ZooKeeper write before its retry (inert unless a write fails; not reached by the accepted witness) |
| mechanism | `experiments/accept/report.py` | `solr-buggy-9440`: `MARKER_FLIPPED` by a `SolrZkClient`/`ZooKeeper` fault, no clock (the witness's; the declared `STATE_PAIRING_FLIPPED` guess before the run was wrong, see Result) |

Budget 21600 s.

## Native check of the bug's own world (scratch, not committed)

`TestCausynthS2Scratch#probeView`, `#probeView2`, `#probeView3` on the buggy tree print node0's maps and view at
each step (above). `#forceLeaderWithoutRefresh` (= this workload) passes on the buggy tree.

**Running it (liftlab):** START-HERE §3 (`CASES=solr-buggy-9440`, the tree set `/bigtemp/vnr3ne/wt/bd-trees-1`, the
snapshot `/u/vnr3ne/gc-run/bd-solr-1`, round B1: `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-solr-buggy-9440`). The
rounds below ran on CloudLab (2026-10-26); their `/bulk` paths were that cluster's and stay as the record. Liftlab:
B1 (lead fills in).

## Result: SAT, accepted (S9440b)

Round S9440b (2026-10-26, agent S9; snapshot `/bulk/gc-run/solr-b9440-3` = GraphChecker 3ca19cf52, tree set
`/bulk/trees/sb9440-3` = 1e7324c461, `/bulk/gc-out/solr-buggy/9440/accept-S9440b-solr-buggy-9440`): 821 s,
`SAT_CANDIDATE` `FINAL_READY`, `MARKER_FLIPPED` at valuation 24, `polarityDecides` true, no gap, no defect, nothing
bounded; `report.py` **PASS**; `round-verify.sh`: `end=(WITNESSED) z3=sat moved=1 polarityDecides=True leaves=154
confirmed`, 0 BOUNDED, 0 UNBOUND, 0 HOLD; `cone.json`: the moved root in the cone, 0 unbound.

- **CONFIRM**: the selected session `38c060c3aa4df972-f132dbaa` is itself the run (4 arms, all its own deliveries;
  every moved root at the model's value; the fatal observed at the anchor).
- **Native REPRODUCE 10/10, control 0/10** (`final/reproduce.json`: planted 10, fatal 10, atAnchor 10; control fatal 0).
- **The moved root is not S9440a's.** It is a FAULT: a planted ZooKeeper `SessionExpired` at node1's
  `SolrZkClient.create` (`#u22`, invocation 1), in `ShardLeaderElectionContextBase.<init>`'s `ensureExists` of
  `/collections/<c>/leaders/shard1`. It fires while node1's core-admin CREATE registers the new core
  (`ZkController.register` -> `joinElection`). The fork's adapter makes a planted SessionExpired a real expiry
  (b707106739: the in-process ZooKeeper server expires node1's session).
- **The chain** (witness replay `iteration-0000/obligations-0000/38c060c3aa4df972/replay.log`, times in ms; native
  `final/reproduce/run-1` in brackets):
  - 101709 [16407]: node1's session expires. Its `register` fails (`RuntimeException(SessionExpired)` from the
    election context); `ZkContainer.registerInZk` logs it, and the core-admin CREATE still answers status=0
    (102279 [16535]). node0's CREATE thus completes before node1's replica is registered.
  - node1's reconnect re-registers the core in the background (`coreZkRegister`, `afterExpiration? true`,
    102367 [16609]): leader election, "I am the new leader" at 103042.
  - 103112 [16664]: node0's `waitForActiveCollection` registers while ZooKeeper does not yet show the replica ACTIVE,
    so the wait is not satisfied at registration.
  - node1 publishes ACTIVE (120999, "no recovery necessary"; the state.json event at 121200). node0's wait ends on
    that event's single publication and the watch is dropped. With the put-back, node0 keeps that `DocCollection`
    (state.json v6).
  - 127041 [17257]: node1 has stopped and the client has seen the replica DOWN. FORCELEADER on node0 logs
    `DocCollection(.../state.json/6)`: frozen, with the replica `active` and `leader:true`. It throws at
    `CollectionsHandler.java:1477`, "The shard already has an active leader", which is the point's own throw (the
    plant's TARGET row, `forceLeaderElection#u40`).
- **Why it reproduces natively where S9440a did not.** The fault itself produces the order node0 needs
  (registration before ACTIVE). node1's registration moves to a background thread after the reconnect, past node0's
  CREATE response. No scheduling is needed.
- **The workaround played no part.** "Exception in Overseer main queue loop" appears neither in the witness replay
  nor in any of the 10 native runs: the Overseer never fails a write, so its wait is never reached. Both rounds'
  explorations held the same obligations. The SessionExpired root (`REGION.6140aa2b...`; e.g. obligations
  `fbf6b7de20352e84`, `c9328cdabff81d42`) was already SAT_MODEL_READY in S9440a. Which witness becomes the claim
  depends on which replay first observes the fatal. S9440b's verdict therefore does not depend on 1e7324c461; the
  code it executes is the same on 2e2acd32d6.
- **The witness discriminates.** The same expiry, planted by scratch code, throws 5/5 on the buggy tree and passes
  5/5 on the fixed tree, where FORCELEADER reads a `LazyCollectionRef` (below).
- `smt-legend.py --repo /bulk/trees/sb9440-3/solr-bug-9440` lists all 203 leaves as OTHER: it names no ROOT for
  Solr's Boolean door markers. The moved root `M_Z_field_REGION.6140aa2b-...in.a00eae7b-...occ.73e9a297..._java/lang/Boolean`
  is among them and in the cone (`cone.json`).

## Native checks (agent S9, 2026-10-26; logs `/bulk/analysis/buggy-detect-2026-10-26/solr-logs/s9-native/`)

Workload alone (seed F0993D5343E20BA4, `build.sh` with the tree build skipped):
- buggy tree (a clean worktree at 1e7324c461, `/bulk/trees/s9scratch/bug-clean`): 20/20 PASSED;
- fixed tree (1e7324c461 with aa5c404b12 reversed, `/bulk/trees/s9scratch/fixed`): 20/20 PASSED;
- the verdict tree `/bulk/trees/sb9440-3/solr-bug-9440` passes in its build (47.6 s).

Faults planted by scratch code (uncommitted; off unless a scratch test arms it; the `TestCausynthS9Scratch*` tests
are subclasses of the workload):

| world | buggy tree | fixed tree |
| --- | --- | --- |
| S9440a's root (lost reply of the Overseer's leader write: `SolrZkClient.setData` throws ConnectionLoss after ZooKeeper applied it), with the 5 s wait | 5/5 FAILED at :1477, plus 1/1 in the first build. node0 registers at 8700; the Overseer's retry writes after the wait (13649); FORCELEADER reads `state.json/5` | 5/5 PASSED (52 s), plus 1/1; FORCELEADER reads `LazyCollectionRef` |
| the same, wait 0 (`TestCausynthS9ScratchNoDelay`) | 5/5 PASSED, plus 1/1: the retry and ACTIVE land before node0 registers (S9440a's native 0/10) | 1/1 PASSED |
| S9440b's root (SessionExpired at node1's election-parent `ensureExists`, through `Sessions.expires` as the plant does) | 5/5 FAILED at :1477; `state.json/6` frozen; no Overseer retry | 5/5 PASSED (48.5 s); `LazyCollectionRef` |

So the workaround does what it was made for: it takes S9440a's witness from 0/5 to 5/5 on the buggy tree, and the
fixed tree passes 5/5. It decides nothing by itself: with no failed write, both trees pass 20/20.

## Earlier round S9440a: SAT, confirmed in the VM; native REPRODUCE 0/10 -- not accepted

Round S9440a (2026-10-26, snapshot `/bulk/gc-run/solr-b9440-2` = GraphChecker abc3e8ec9, tree set
`/bulk/trees/sb9440-2` = 2e2acd32d6, `/bulk/gc-out/solr-buggy/9440`): 700 s, `SAT_CANDIDATE` `FINAL_READY`,
`MARKER_FLIPPED` at valuation 24, `polarityDecides` true, no gap, no defect, nothing bounded.

- **SAT, confirmed in the VM.** CONFIRM: the selected session `9e4cbffc55a56407-0b106fe3` is itself the run (every
  edge the model chose, every moved root at the model's value, the fatal observed at the anchor). One moved root, a
  FAULT: a ZooKeeper ConnectionLoss planted at the Overseer's `SolrZkClient.setData` (`#u16`, OVERSEER_STATE_UPDATE#4
  on node0) -- the state.json write of the replica's leader/ACTIVE state right after node1's core became leader.
- **The declared mechanism was wrong.** Before the run this case declared `STATE_PAIRING_FLIPPED` (the study's guess:
  node0's view re-paired with an older decode). GraphChecker built the needed order with a ConnectionLoss on the
  Overseer's ACTIVE write instead of a re-pairing; the `report.py` row is now `MARKER_FLIPPED` by a
  SolrZkClient/ZooKeeper fault, no clock (with the old row the run's `report.py` said FAIL on the mechanism only; re-run with the new row on S9440a's
  output: PASS -- `report.py` does not read REPRODUCE, which is what fails the acceptance).
- **The witness discriminates.** The witness replay's log
  (`iteration-0000/obligations-0000/9e4cbffc55a56407/replay.log`, times in ms):
  - 102912: the Overseer's main loop fails that write ("Exception in Overseer main queue loop",
    ConnectionLoss) and re-processes it later;
  - 106220: node0's CREATE `waitForActiveCollection` registers while ZooKeeper does not yet show the replica ACTIVE,
    so it is not satisfied at registration;
  - 122022: the re-written ACTIVE arrives as a watch event and satisfies node0's wait on that single publication;
    the watch is dropped and, with the put-back, node0 keeps that `DocCollection` (state.json v5);
  - 127431: after node1 stopped and the client saw the replica DOWN, FORCELEADER on node0 logs
    `collections:{causynthForceLeaderStale=DocCollection(.../state.json/5)}` -- the frozen view, not a
    `LazyCollectionRef` -- and throws at `CollectionsHandler.java:1477`, "The shard already has an active leader".

  On the fixed code the dropped watch evicts to a `LazyCollectionRef`, FORCELEADER reads the DOWN state from
  ZooKeeper and passes. So the buggy tree's frozen `DocCollection` is what turns FORCELEADER away.
- **Native REPRODUCE 0/10 (control 0/10): not accepted.** The witness also needs node0's `waitForActiveCollection`
  registration to land before the Overseer re-processes the ACTIVE write. The VM schedule held that order, but it is
  not in the claim's cone: `final/reproduce/plant.jsonl` has the fault (ROOT row) and the FORCELEADER reader's view
  holds (VIEW_HOLD rows), no ORDER row (`holding` 0). Natively the Overseer re-writes ACTIVE within milliseconds:
  run 1 (`final/reproduce/run-1/stdout.log`) plants the ConnectionLoss at 18230 ms, the Overseer re-writes ACTIVE
  before node0's wait registers at 18799 ms, so the wait is satisfied at registration, the registration's second
  publication evicts the entry (the double publish above), and FORCELEADER (19412 ms) reads
  `LazyCollectionRef(causynthForceLeaderStale)` and passes. A one-fault witness that relies on an order the native run
  does not keep is not accepted (HDFS round, 2026-10-25). No engine change was made (lead, 2026-10-26).
- **Arms#concurrent** (the expected obstacle to a STATE re-pairing of node0's registration fetch) was not reached:
  the witness needed no re-pairing.
- **Correction (S9, after reading the witness and the native run).** The faulted write at OVERSEER_STATE_UPDATE#4 is
  node1's LEADER message, not ACTIVE. The fault is at `SolrZkClient.java:527`, the door after `keeper.setData`
  returned: ZooKeeper applied v3 and the reply was lost. The main loop's retry re-writes it (v4), and the replica's
  ACTIVE is the next message (v5). node1 is not blocked, since it sees its leadership in v3. So a wait before the
  retry (1e7324c461) delays ACTIVE past node0's registration; the native checks above show it.
