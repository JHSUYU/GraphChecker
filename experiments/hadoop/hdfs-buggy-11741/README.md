# HDFS-11741 put back (hdfs-buggy-11741, point hdfs-adhoc-11)

## The bug

[HDFS-11741](https://issues.apache.org/jira/browse/HDFS-11741) (fix 6a3fc685a98, 2017): a long-running
Balancer fails because its cached `DataEncryptionKey` outlives the block key it was derived from. The
Balancer's `KeyManager` mints one data-encryption key from the block key current at its first move and
hands it to every later move. The NameNode retires that block key at its next rotation, gives it an
expiry of `now + keyUpdateInterval + tokenLifetime`, and drops it in `removeExpiredKeys` once that
passes; every DataNode drops it in its own `removeExpiredKeys`, which `addKeys` runs before taking a
key update. The Balancer then presents the cached key id, and the destination DataNode's
`BlockTokenSecretManager.retrieveDataEncryptionKey` finds no block key for it and throws
`InvalidEncryptionKeyException` ("Can't re-compute encryption key for nonce, since the required block
key (keyID=...) doesn't exist"). The fix makes `newDataEncryptionKey` mint a new key once the cached
one is past its own expiry, which the NameNode's schedule keeps inside the block key's life.

Point hdfs-adhoc-11 (`docs/checks/HDFS.md`, `checks.tsv`) is that throw: a key-id lookup that misses
when the NameNode's rotation and the DataNode's key set disagree.

## What was put back, on graphchecker/hdfs-bug-11741

The fork's branch is `graphchecker/hdfs-checks` (899c200cc8e, the tree every HDFS ad hoc check runs)
plus two commits:

- **The bug, by hand** (`HDFS-11741 put back: ...`): `KeyManager.newDataEncryptionKey` mints only when
  no key is cached (`if (encryptionKey == null)`), as before the fix, instead of also when
  `encryptionKey.expiryDate < timer.now()`. The fix's `Timer` field, which only that check read, and its
  comment go with it. The fix's other half (`BlockTokenSecretManager` reading its clock through a `Timer`,
  for testing) changes no behaviour and stays. The fix's test `TestKeyManager` is removed: it asserts the
  check this puts back out and sets the removed field by reflection.
- **The workload and the target** (`GraphChecker: ...`): `TestCausynthExpiredBalancerKey` and
  `hdfs-buggy-11741` added to the marker on `retrieveDataEncryptionKey`'s throw (line 584).

## The workload

`org.apache.hadoop.hdfs.server.balancer.TestCausynthExpiredBalancerKey#testBlockMoveWithCachedKeyAfterRotations`,
a `TestCausynth*` of its own on the shape of hdfs-17899 bug1's `TestCausynthBalancerCachedKey` (in the
tree, SAT 10/10 natively on CloudLab): the mover is the test holding a real `KeyManager`, which takes its
keys from the NameNode over the recorded RPC, caches its encryption key and signs the move's access
token as `Dispatcher.PendingMove.dispatch` does, and sends one REPLACE_BLOCK over an encrypted
connection; `Balancer` and `Dispatcher` (block selection) take no part in the mechanism. No existing test
reaches the bug: it needs a Balancer whose cached key outlives two rotations inside the window, and the
fix's `TestKeyManager` is a mocked unit test with no DataNode.

Two DataNodes, the block written before the window to the first (`proxy-dn`); the block keys pinned
before the window to the serials S+1 (current) and S+2 on every node (S = `Integer.MAX_VALUE / 11741`).
Inside the window:

1. nn0 rotates once (S+2 current); each DataNode, in name order, is marked for a key update and takes the
   keys over one heartbeat of its own (`CausynthCluster.refreshKeysFromNameNode`): S+2's expiry on the
   DataNodes is now written by a recorded nn0 clock.
2. The Balancer starts (`fetch-block-keys`): its `KeyManager` takes nn0's keys and mints the encryption
   key it caches, of S+2.
3. nn0 rotates twice: the first retires S+2, the second runs `removeExpiredKeys` over it. Each DataNode
   takes the keys over one more heartbeat, whose `addKeys` first runs `removeExpiredKeys` on its clock.
4. The Balancer's key-updater turn (`refresh-block-keys`): its block keys follow nn0 (S+4 current), its
   cached encryption key does not.
5. The move (`balance-block`): the Balancer presents S+2 to `target-dn`.

The recording succeeds: interval 60 min, token lifetime 600 min, so nothing expires inside the window,
and the target still holds S+2 (retired, not expired). The recording's checks (`recordingPrecondition`)
say so. The witness has to be a world in which nn0's clock at its third rotation's `removeExpiredKeys`
is past S+2's retired expiry, so nn0 no longer exports it, and `target-dn`'s clock at its second key
update's `removeExpiredKeys` is past S+2's expiry there, so it drops it: a Balancer that has run for half a
day while its cached key did not move. No fault world reaches the target: `target-dn` holds S+2 since the
pin, before the window, so a lost heartbeat cannot take it away.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-buggy-11741` (beside hdfs-adhoc-11 and the named block-key cases) on `retrieveDataEncryptionKey`'s missing-key `throw new` (line 584); `run.sh` derives the spec from it |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-11741/target-dn#epoch0/region/REGION.7c569c3f-...@hdfs-11741/balancer#epoch0/balance-block#1`: target-dn's SASL handler occurrence (`SaslDataTransferServer$SaslServerCallbackHandler.handle`) under the Balancer's move, the one every `retrieveDataEncryptionKey` of the move is nested in (as hdfs-11741 and hdfs-17899 bug1) |
| clock roots | the program text (`causynth/RootCatalog`) | every clock read the slice reaches (`Timer.now()` in `removeExpiredKeys` and `updateKeys`) is a root |
| hook-minted roots | the tree | `HDFS.BLOCK_KEY.SERIAL_NO` and `HDFS.BLOCK_KEY.EXPIRY_DATE*` (`CausynthSymbolicSource.symbolize` in `BlockTokenSecretManager`, already in 899c200cc8e); no `root-domains.jsonl`, so they are pinned to the recording: the presented key id is a constant of the run and only the clocks decide |
| wire mappings | `../communication-mappings.jsonl` | the SASL key id (`data-encryption-key-id`); the block keys' ids and expiry dates are protobuf message fields the IPC door walks |
| scope | `case.sh` | hdfs-11741's: the block-key family (`blockkey_scope` in `../system.sh`) without `ipc/Client`, plus `KeyManager` (no `Dispatcher`/`Balancer`: the workload has none) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2`: the witness moves two clocks, on two nodes; `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=1` as hdfs-11741 |
| loop bounds | `loop-bounds.jsonl` (hdfs-11741's three rows at 8) | the expiry scan, the block-key reply conversion, the Balancer's key-updater loop |
| mechanism | `experiments/accept/report.py` | `hdfs-buggy-11741`: `CLOCK_SKEW` |

The run's budget is `hdfs-buggy-cases.tsv`'s 21600 s.

## Result

(filled in after the run)
