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
plus three commits:

- **The bug, by hand** (a55f17c918c, `HDFS-11741 put back: ...`): `KeyManager.newDataEncryptionKey` mints
  only when no key is cached (`if (encryptionKey == null)`), as before the fix, instead of also when
  `encryptionKey.expiryDate < timer.now()`. The fix's `Timer` field, which only that check read, and its
  comment go with it. The fix's other half (`BlockTokenSecretManager` reading its clock through a `Timer`,
  for testing) changes no behaviour and stays. The fix's test `TestKeyManager` is removed: it asserts the
  check this puts back out and sets the removed field by reflection.
- **The workload and the target** (226544c3aa7, then c0af4cbcfe5 after the first run):
  `TestCausynthExpiredBalancerKey`, and `hdfs-buggy-11741` added to the marker on
  `retrieveDataEncryptionKey`'s throw (line 584).

## The workload

`org.apache.hadoop.hdfs.server.balancer.TestCausynthExpiredBalancerKey#testBlockMoveWithCachedKeyAfterRotations`,
a `TestCausynth*` of its own on the shape of hdfs-17899 bug1's `TestCausynthBalancerCachedKey` (in the
tree, SAT 10/10 natively on CloudLab): the mover is the test holding a real `KeyManager`, which takes its
keys from the NameNode over the recorded RPC, caches its encryption key and signs each move's access
token as `Dispatcher.PendingMove.dispatch` does, and sends REPLACE_BLOCK over an encrypted connection;
`Balancer` and `Dispatcher` (block selection) take no part in the mechanism. No existing test reaches the
bug: it needs a Balancer whose cached key outlives two rotations inside the window, and the fix's
`TestKeyManager` is a mocked unit test with no DataNode.

Two DataNodes, two blocks written before the window to the first (`proxy-dn`); the block keys pinned
before the window to the serials S+1 (current) and S+2 on every node (S = `Integer.MAX_VALUE / 11741`).
Inside the window:

1. nn0 rotates once (S+2 current); each DataNode, in name order, is marked for a key update and takes the
   keys over one heartbeat of its own (`CausynthCluster.refreshKeysFromNameNode`): S+2's expiry on the
   DataNodes is now written by a recorded nn0 clock.
2. The Balancer starts (`fetch-block-keys`): its `KeyManager` takes nn0's keys.
3. Its first move (`balance-block#1`) mints the encryption key it caches, of S+2, and moves the first block
   to `target-dn`.
4. nn0 rotates twice: the first retires S+2, the second runs `removeExpiredKeys` over it. Each DataNode
   takes the keys over one more heartbeat, whose `addKeys` first runs `removeExpiredKeys` on its clock.
5. The Balancer's key-updater turn (`refresh-block-keys`): its block keys follow nn0 (S+4 current), its
   cached encryption key does not.
6. The second move (`balance-block#2`) presents S+2 to `target-dn` with the second block.

The recording succeeds: interval 60 min, token lifetime 600 min, so nothing expires inside the window,
and the target still holds S+2 (retired, not expired); the recording's checks (`recordingPrecondition`)
say so. The witness has to be a world in which nn0's clock at its third rotation's `removeExpiredKeys`
is past S+2's retired expiry, so nn0 no longer exports it, and `target-dn`'s clock at its second key
update's `removeExpiredKeys` is past S+2's expiry there, so it drops it: a Balancer that has run for half a
day while its cached key did not move. No fault world reaches the target: `target-dn` holds S+2 since the
pin, before the window, so a lost heartbeat cannot take it away.

One workaround, in the workload's own configuration: `dfs.heartbeat.interval` is 6 h, so a DataNode
heartbeats once at its registration and inside the window only the workload's own heartbeats deliver
keys. It makes the delivery order controllable and changes nothing on the path to the target (see the
first run below).

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-buggy-11741` (beside hdfs-adhoc-11 and the named block-key cases) on `retrieveDataEncryptionKey`'s missing-key `throw new` (line 584); `run.sh` derives the spec from it |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-11741/target-dn#epoch0/region/REGION.7c569c3f-...@hdfs-11741/balancer#epoch0/balance-block#2`: target-dn's SASL handler occurrence (`SaslDataTransferServer$SaslServerCallbackHandler.handle`) under the Balancer's second move, the one every `retrieveDataEncryptionKey` of that move is nested in (as hdfs-11741 and hdfs-17899 bug1) |
| clock roots | the program text (`causynth/RootCatalog`) | every clock read the slice reaches (`Timer.now()` in `removeExpiredKeys` and `updateKeys`) is a root |
| hook-minted roots | the tree | `HDFS.BLOCK_KEY.SERIAL_NO` and `HDFS.BLOCK_KEY.EXPIRY_DATE*` (`CausynthSymbolicSource.symbolize` in `BlockTokenSecretManager`, already in 899c200cc8e); no `root-domains.jsonl`, so they are pinned to the recording: the presented key id is a constant of the run and only the clocks decide |
| wire mappings | `../communication-mappings.jsonl` | the SASL key id (`data-encryption-key-id`); the block keys' ids and expiry dates are protobuf message fields the IPC door walks |
| scope | `case.sh` | hdfs-11741's: the block-key family (`blockkey_scope` in `../system.sh`) without `ipc/Client`, plus `KeyManager` (no `Dispatcher`/`Balancer`: the workload has none) |
| world depth | `case.sh` | `CAUSYNTH_REGION_PATH_MAX_WORLD_DEPTH=2`: the witness moves two clocks, on two nodes; `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=1` as hdfs-11741 |
| loop bounds | `loop-bounds.jsonl` (hdfs-11741's three rows at 8) | the expiry scan, the block-key reply conversion, the Balancer's key-updater loop |
| mechanism | `experiments/accept/report.py` | `hdfs-buggy-11741`: `CLOCK_SKEW` |

The run's budget is `hdfs-buggy-cases.tsv`'s 21600 s.

## Result: SAT, CLOCK_SKEW on two nodes, confirmed and reproduced 10/10 (B11741b, PASS)

Round B11741b (2026-10-26, snapshot `/bulk/gc-run/hb11741-2` = GraphChecker f79b607b1, tree set
`/bulk/trees/b11741-2` = c0af4cbcfe5, `/bulk/gc-out/hdfs-buggy/11741`): 3353 s, `SAT_CANDIDATE`
`FINAL_READY`, `report.py` **PASS**: `CLOCK_SKEW` at valuation 0, `polarityDecides` true, no gap, no
defect, nothing bounded, `cone.json` unbound empty; EXPLORE ended `WITNESSED` after 8 rounds.

- **The two moved roots** are the two removals the workload was built around: nn0's `Timer.now()` in
  `removeExpiredKeys` (`BlockTokenSecretManager` :221) inside its third rotation (`updateKeys` :276,
  `KEY_MANAGER_TICK#3`, REGION.08ab84c9), and target-dn's in its second key update (`addKeys` :244 under its
  `heartbeat#2`, REGION.ba3902cd). The other 12 clock cells stay at the recording.
- **The chain in the formula** (read by hand: `smt-legend.py` decodes the 14 clock leaves; the path's
  families were read in `final/candidate.smt2`): `path_fatal__5` (the selected path, its own run's
  session c551cfde, every arm attested there, none re-paired) is `allKeys.get(keyId) == null` on target-dn's
  map, built by `container_dag` puts and removals whose removal guards compare each key's expiry with
  target-dn's two removal clocks; the map's puts come from the heartbeat answers' `ExportedBlockKeys`
  (`message_family__5__a36cb10a`/`b8d890d1`, nn0's export, whose arms carry nn0's third-rotation removal
  clock: what nn0 still holds decides what it exports); `keyId` is the Balancer's cached key's id over the
  SASL user name (`data-encryption-key-id`, `message_family__5__c2cca287`), bound to its producer.
- **CONFIRM** (worker-f6a80fe4): "every edge the model chose was taken, and the claim's anchor observed the
  fatal"; in the witness replay and in CONFIRM's, target-dn's SASL handler under `balance-block#1`
  observed no fatal and the one under `balance-block#2` (the declared occurrence) did.
- **REPRODUCE**: 10/10 natively (every row planted: target-dn's clock +48213453 ms = 13.4 h, nn0's
  +39659208 ms = 11.0 h, 4 ORDER rows; the fatal at the anchor), control 0/10.
- **Each moved root is necessary**, natively: a scratch copy of the workload (not committed) offsetting
  nn0's `Timer` during its third rotation and target-dn's during its second key update by the plant's
  skews: neither, either one alone: the move succeeds; both: `InvalidEncryptionKeyException: Can't
  re-compute encryption key for nonce, since the required block key (keyID=182906) doesn't exist. Current
  key: 182908`.
- z3 alone on the whole exported file does not decide within `round-verify.sh`'s 300 s (COMPOSE's own
  path-scoped asks decided it, the whole composition in 85 s; `polarityDecides` is its recorded-valuation
  ask, unsat).

What the witness says about the fix: the world skews nn0's and target-dn's clocks and leaves the
Balancer's at the recording. HDFS-11741's fix compares the cached key's expiry with the Balancer's own
clock, so it closes the bug's real trigger, every clock moving on together under a long-running
Balancer; it does not make a Balancer immune to an 11-13 h skew between nodes, which this world also is.
The check shows the bug's mechanism (a cached key outliving the block key the NameNode and the DataNode
rotated away), as the owner expected.

### The first run (B11741a, FAIL by report.py; what the revision changed)

B11741a (snapshot `hb11741-1` = bc79fc184, tree set `/bulk/trees/b11741` = 226544c3aa7: the key minted in the
Balancer's fetch, one move, daemon heartbeats every 3 s): 3612 s, confirmed in the VM and reproduced
10/10 natively with the same two clocks (+11.0 h nn0, +13.2 h target-dn; control 0/10), but withheld:
- 16 BLOCKING `TOPOLOGY_DIVERGENCE` rows (EXPLORE): nn0's `KeyUpdateCommand` conversion ran under the
  proxy's and under `BP_SERVICE_ACTOR` heartbeat anchors, not target-dn's recorded ones: in those replays a
  daemon heartbeat, which no recording had, answered a node's key-update mark. Gone with the 6 h heartbeat
  interval.
- `FORMULA_SAT` at valuation 0, `polarityDecides` false: the chain was open over the Balancer's received
  block-key id (`BlockKeyProto.KeyId` = 182906 in the fetch reply), whose producer, nn0's export under the
  fetch (REGION.2392e4b7 `PBHelper.convert`), PLAN had not demanded; growth added it only at round 10, and
  no session had run it instrumented when the first witness ended EXPLORE. An open link is free in the
  formula, so the recorded valuation was satisfiable too and the clock-world claim was not taken.
  hdfs-17899 bug1 (same shape) planned that export from the start; there the key was minted in the move,
  here in the fetch's reply context. With the key minted in the first move (c0af4cbcfe5) PLAN still does not
  demand the export up front, but growth added it at round 2 and the chain was closed when the witness came.

The case's `report.py` row (`hdfs-buggy-11741`: `CLOCK_SKEW`) is in `experiments/accept/report.py`.
