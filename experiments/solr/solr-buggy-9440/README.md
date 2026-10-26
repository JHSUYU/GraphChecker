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

`org.apache.solr.cloud.TestCausynthForceLeaderStaleView#forceLeaderOnAWatchingNode` (two nodes): a 1x1 collection
lives on node1; an `HttpSolrClient` to node0 sends every collection request. node0's `CollectionsHandler` waits for
the new collection to be active (a state watch it drops once the replica is ACTIVE) -- with the bug its view keeps
that state, the replica ACTIVE and leading. node1 is then stopped; once the test client sees the replica DOWN, node0
waits until it sees node1 gone (one more watch of the collection, whose registration refreshes the state and which
its predicate drops at once). FORCELEADER on node0 then finds the leader DOWN, so it is applicable; no live replica
can take over, and after its wait it answers without a leader. Natively it passes on both trees (node0's last
refresh does land). The bug is reached only in a world where that last refresh does not land: with the bug node0
stays on the frozen ACTIVE view and FORCELEADER throws.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("solr-adhoc-31,solr-buggy-9440")` on FORCELEADER's throw, `CollectionsHandler.java:1477` |
| the occurrence | `target_occurrence` in `case.sh` | the FORCELEADER request on node0 (named from the seed) |
| scope | `case.sh` | `CollectionsHandler`; the ZooKeeper-state classes come from `system.sh` (ZkStateReader, ClusterState, DocCollection, Slice, Replica) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=0` |
| mechanism | `experiments/accept/report.py` | `solr-buggy-9440`: `MARKER_FLIPPED` by a SolrZkClient/ZooKeeper store-read fault, no clock (the deferred refresh) -- revised to `STATE_PAIRING_FLIPPED` if the witness re-pairs the frozen `DocCollection` read directly |

Budget 21600 s.

## Native check of the bug's own world (scratch, not committed)

`TestCausynthS2Scratch#forceLeaderWithoutRefresh` (the workload without node0's second watch): on `solr-bug-9440`
FORCELEADER throws "The shard already has an active leader" (node0's frozen ACTIVE view from the CREATE's wait);
on the fixed tree the dropped watch left a lazy reference, so FORCELEADER reads ZooKeeper, sees the leader DOWN, and
is accepted.

## Result

<!-- filled from the run -->
