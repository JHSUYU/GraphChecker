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

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hbase-adhoc-34,hbase-buggy-15039")` on retrievePassword's `throw new InvalidToken` |
| the occurrence | `target_occurrence` in `case.sh` | `first`: the test's one `retrievePassword` |
| scope | `case.sh` | hbase-adhoc-34's: AuthenticationTokenSecretManager, ZKSecretWatcher |
| window | `case.sh` | the default (`up`): the new key is made and distributed inside it |
| world depth | `case.sh` | 0: one re-pairing or one fault |
| heap | `workflow.properties` | `engine_memory_mb` 24576, as hbase-buggy-20642 |
| mechanism | `experiments/accept/report.py` | `hbase-buggy-15039`: STATE_PAIRING_FLIPPED or MARKER_FLIPPED, no clock; a MARKER claim has to be the watcher's ZooKeeper READ fault (read by hand) |

## Result

(pending)
