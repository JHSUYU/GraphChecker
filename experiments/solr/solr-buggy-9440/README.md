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

`graphchecker/solr-checks` (12d23091d1) plus two commits:

- **The bug, by hand** (aa5c404b12): `ZkStateReader.removeDocCollectionWatcher` (where
  `removeCollectionStateWatcher` and every `waitForState` end) no longer evicts -- the
  `watchedCollectionStates.remove` + `lazyCollectionStates.put(new LazyCollectionRef)` + `constructState` under the
  update lock are gone; the watch itself is still dropped. The same eviction in `unregisterCore` (SOLR-8323's, a
  local core's close, not part of this fix) stays.
- **The workload and the target** (42e4f16231): `TestCausynthForceLeaderStaleView`, and `solr-buggy-9440` added to
  the marker on FORCELEADER's throw (beside `solr-adhoc-31`).

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

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-31,solr-buggy-9440")` on FORCELEADER's throw, `CollectionsHandler.java:1477` |
| the occurrence | `target_occurrence` in `case.sh` | `first`: the FORCELEADER request on node0 (`forceLeaderElection`'s region folds into the request's occurrence, as in solr-adhoc-31's seeds) |
| scope | `case.sh` | `CollectionsHandler`; the ZooKeeper-state classes come from `system.sh` (ZkStateReader, ClusterState, DocCollection, Slice, Replica) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| mechanism | `experiments/accept/report.py` | `solr-buggy-9440`: `STATE_PAIRING_FLIPPED` (the study's: a node's view of the collection held at an older decode) |

Budget 21600 s.

## Native check of the bug's own world (scratch, not committed)

`TestCausynthS2Scratch#probeView`, `#probeView2`, `#probeView3` on the buggy tree print node0's maps and view at
each step (above). `#forceLeaderWithoutRefresh` (= this workload) passes on the buggy tree.

## Result

<!-- filled from the run -->
