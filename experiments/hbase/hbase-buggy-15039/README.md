# HBASE-15039 put back (hbase-buggy-15039, point hbase-adhoc-34)

## The bug

[HBASE-15039](https://issues.apache.org/jira/browse/HBASE-15039) (fix 1c7e9ec124, 2015): authentication-token keys are
made by the elected key master and reach every other master and region server only through ZooKeeper watches
(`ZKSecretWatcher` on `/hbase/tokenauth/keys`). Before the fix `AuthenticationTokenSecretManager.retrievePassword` threw
`InvalidToken("Unknown master key for token")` as soon as its `allKeys` map had no entry for the token's key id, so a
server whose watcher had not yet applied (or had missed) a key event rejected a valid token. The fix refreshes the keys
from ZooKeeper on a miss (`ZKSecretWatcher.refreshKeys`) and looks again before throwing.

Point hbase-adhoc-34 is that throw: `allKeys.get(keyId) == null` -> `InvalidToken` (AuthenticationTokenSecretManager:160
on graphchecker/hbase-checks, :139 on this branch once the refresh block is gone).

## What was put back, on graphchecker/hbase-bug-15039

graphchecker/hbase-checks (b5d5cc6a20) plus two commits:

- **The bug, by hand** (729d39b9c5): `retrievePassword` throws on the first miss again; the refresh block between the
  lookup and the throw (the watcher-abort check, the leader-elector restart, `zkWatcher.refreshKeys()`, the second
  lookup) is gone, the throw and its marker stay. The fix's `ZKSecretWatcher.refreshKeys` and `getKeysParentZNode`,
  which only that block and the fix's test called, are deleted, and so is the fix's test `TestZKSecretWatcherRefreshKeys`.
- **The workload and the target** (c2cecb3756): `TestCausynthTokenKeyWatch`, and `hbase-buggy-15039` added to
  hbase-adhoc-34's marker.

## The workload

`org.apache.hadoop.hbase.security.token.TestCausynthTokenKeyWatch#theOtherServerValidatesATokenOfANewKey`: a
one-region-server cluster whose servers run their token secret managers on simple authentication (the tree's
`RpcServer#CAUSYNTH_TOKEN_SECRETS`, owner 2026-10-19: no Kerberos, as hbase-adhoc-34). The window opens once the cluster
is up. The test finds the elected key master and the other server, has the key master roll a new key
(`rollCurrentKey`: `allKeys.put`, `addKeyToZK`, which the other server's watcher applies from its ZooKeeper event),
sleeps two seconds, has the key master issue a token under the new key, and has the other server validate it.

Why not hbase-adhoc-34's workload: `TestCausynthTokenKeys` removes the key from the other server's map by hand before
validating, so on this tree it throws on every native run. Here no key is removed; the other server holds the new key
only once its watcher's `addKey` ran, and natively that is well within the two seconds. The sleep is hbase-adhoc-22's
device (`TestCausynthTruncatedTableQuota`): it orders the run natively and states no happens-before, so the
validation's read of `allKeys` and the watcher's `addKey` stay concurrent for GraphChecker.

The witness this case is built for: the other server's `retrievePassword` read of `allKeys` for the new key id paired to
before its watcher's `addKey` of that key (STATE re-pairing: the watch event not yet processed), so the lookup misses and
:139 throws; or a ZooKeeper READ fault on the watcher's read of the new key (its map never gets the key; the watcher
aborts its server). With the fix either world refreshes from ZooKeeper and finds the key (after an abort it throws a
different InvalidToken, "Token keys could not be sync from zookeeper").

Natively the workload passed 6 of 6 runs before any campaign (2.27-2.32 s).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hbase-adhoc-34,hbase-buggy-15039")` on retrievePassword's `throw new InvalidToken` |
| the occurrence | `target_occurrence` in `case.sh` | `first`: the test's one `retrievePassword` |
| scope | `case.sh` | hbase-adhoc-34's: AuthenticationTokenSecretManager, ZKSecretWatcher |
| window | `case.sh` | the default (`up`): the new key is made and distributed inside it |
| world depth | `case.sh` | 0: one re-pairing or one fault |
| heap | `workflow.properties` | `engine_memory_mb` 12288, hbase-bugs' (a lift has 30 GB; the CloudLab rounds below ran at 24576) |
| mechanism | `experiments/accept/report.py` | `hbase-buggy-15039`: STATE_PAIRING_FLIPPED or MARKER_FLIPPED, no clock; a MARKER claim has to be the watcher's ZooKeeper READ fault (read by hand) |

## Result: SAT, STATE re-pairing, confirmed and reproduced 10/10 (HB15039b on CloudLab, PASS)

Liftlab (series B1, 2026-10-28, `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-hbase-buggy-15039`): B1 (lead fills in).

Round HB15039b (CloudLab, 2026-10-26; GraphChecker f82385bcc, tree c2cecb3756): 1211 s,
`SAT_CANDIDATE` `FINAL_READY`, `report.py` **PASS** (`STATE_PAIRING_FLIPPED` at valuation 0, `polarityDecides` true, no
gap, no defect). `round-verify.sh`: `end=(FIXED_POINT)`, z3 sat on the exported `candidate.smt2`, 2 leaves, confirmed,
0 BOUNDED, 0 UNBOUND, 0 HOLD. The claim moves no root (`movedRoots` {}): it is a re-pairing, the shape of
hbase-adhoc-22's accepted STATE claim.

- **Exploration.** The seed planned only the target occurrence (the test's `retrievePassword` on the other
  server, rs0; the key master is master0). Round 0's flip of the guard was `NOT_FLIPPABLE`: the read of `allKeys`
  had only its INITIAL version, because the other server's watcher, whose `allKeys.put` is a library call and no
  field write, ran unplanned. Round 0's growth exposed the watcher's occurrences (`ZKSecretWatcher` regions under the
  `HBASE_ZK.ZKSECRETWATCHER` anchors of the key master's ZooKeeper writes, on rs0 and master0); round 2 ran them
  instrumented, so their puts became writer rows of the map (`MAP/11#-3`), and EXPLORE reached its fixed point.
- **The formula** (4 paths): on the two grown sessions' paths the map's version at the target read is one of three
  `assoc_put` writers (`writer_family`, the watcher's puts and the INITIAL map), and the fatal is
  `masterKey == null` on that map at the token's key id.
- **The model** (`final/confirm/worker/expected_edges.jsonl`): a STATE edge that has the target's read of `allKeys`
  take the map's INITIAL version (writer INITIAL, version 28) instead of a put of the new key, and three ORDER rows
  holding rs0's `ZKSecretWatcher.refreshNodes` -> `addKey` occurrences until after the anchor. The chain, on the bug
  tree: master0's `rollCurrentKey` puts key 2 in its own map and writes `/hbase/tokenauth/keys/2`
  (AuthenticationTokenSecretManager:236-238); `generateToken` signs with it (:124, :150); rs0's watcher would apply it
  in `nodeChildrenChanged` -> `refreshNodes` -> `addKey` -> `allKeys.put` (ZKSecretWatcher:122/140/153,
  AuthenticationTokenSecretManager:168); in the model rs0's `retrievePassword` reads the map first,
  `allKeys.get(keyId)` misses (:137), and :139 throws `InvalidToken("Unknown master key for token")`. In words: a
  server validates a token whose key its ZooKeeper watcher has not applied yet -- HBASE-15039.
- **CONFIRM** (`final/confirm.json`): "every edge the model chose was taken, and the claim's anchor observed the
  fatal".
- **REPRODUCE** (`final/reproduce.json`): 10 of 10 native runs took the fatal at the anchor with every order held;
  control 0 of 10. `planted` reads 0 because the held ORDER rows end past the anchor, where the run stops
  (CHECKING trap 21: their after-activation runs past the anchor).
- **With the fix** the same world refreshes the keys from ZooKeeper on the miss (`refreshKeys`) and finds key 2; no
  throw.

Earlier: HB15039a (CloudLab, GraphChecker 9649eb08b) was stopped in SEED, its head steps held by the shared ledger's
mixed core units (CloudLab's core-charging ledger; liftlab's charges memory only).
