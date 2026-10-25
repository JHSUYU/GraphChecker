# HDFS-17383 (hdfs-buggy-17383)

## The bug

[HDFS-17383](https://issues.apache.org/jira/browse/HDFS-17383), fixed by f49a4df797d (PR 6562, 2024, "Datanode current
block token should come from active NameNode in HA mode"). In HA a DataNode heartbeats every NameNode and takes the
KeyUpdateCommand of the standby as well as of the active. Before the fix every export it took set its current block
key (`BlockTokenSecretManager#addKeys`), so the current key was the key of whichever NameNode it heard last. A DataNode
signs the block token of a transfer it sources (`DataNode.DataTransfer`, `createPassword` with `currentKey`) with that
key; after the standby's key update the token is keyed by the standby's newest key, and a target DataNode that has not
received the standby's update rejects it: `BlockTokenSecretManager#retrievePassword`, `allKeys.get(keyId) == null`,
`InvalidToken` "the required block key ... doesn't exist" -- the throw of the ad hoc point hdfs-adhoc-12
(`docs/checks/HDFS.md` row 12). The fix sets the current key only from the active NameNode's keys (or when none is set).

## The tree: the bug put back, the workload

Tree `$GC_TREES/hadoop-hdfs-bug-17383`, the fork's `graphchecker/hdfs-bug-17383` = `graphchecker/hdfs-checks`
(899c200cc8e) plus two commits:

- **7509b70100d, HDFS-17383 put back.** `BlockTokenSecretManager#addKeys(ExportedBlockKeys, boolean)` sets
  `this.currentKey = exportedKeys.getCurrentKey()` from every export again: the fix's guard
  `if (updateCurrentKey || currentKey == null)` is gone (one line of today's code). `BPOfferService` still passes
  whether the keys come from the active NameNode (false for a standby's KeyUpdateCommand, `processCommandFromStandby`,
  and for a registration with a non-active NameNode); the DataNode no longer heeds it. That is exactly the pre-fix
  behaviour of the DataNode. The rest of the fix stays (the parameter and its callers, the NameNode's key-update mark
  of every DataNode at failover, `markAllDatanodesStaleAndSetKeyUpdateIfNeed`): only the DataNode's choice of its
  current key is the bug. The fix's regression test `TestUpdateDataNodeCurrentKey` fails with the bug back and goes.
- **1e519fa598a, the workload and the target.** `TestCausynthStandbyCurrentKey#testTransferAfterStandbyKeyUpdate`
  (`hadoop-hdfs/src/test/.../server/datanode`), and `retrievePassword`'s throw (line 540) names `hdfs-buggy-17383`
  beside `hdfs-adhoc-12`.

The workload is the fix's test (an HA MiniDFSCluster, `simpleHATopology`, block tokens on) in the shape of
hdfs-adhoc-12's own (`TestCausynthDataTransferRpcFailure`; that one is non-HA, so it cannot reach this bug): data
transfer unencrypted, so the target checks the token with no SASL key check before it (row 11's throw at :582 would
fire first).

1. Before the window: two NameNodes and two DataNodes, nn0 made active; each DataNode hears it (one triggered
   heartbeat) and takes nn0's keys. A one-byte file is written to dn0 (`CausynthCluster.createOnNode`): dn0 is the
   source, dn1 the target. Both masters' key serials are pinned (`setSerialNo`, two rotations, the constructor-time
   keys dropped: every replay JVM mints the same ids, as in the block-key precedents) and every DataNode holds both
   pinned pairs, nn0's current key current. Every node registered whole (`CausynthCluster`).
2. In the window: the standby nn1 rotates twice (as its own request: an explicit `updateKeys`, as its heartbeat
   manager does every key-update interval) and the workload marks both DataNodes for a key update on nn1 (an explicit
   rotation marks none). The target, then the source, each takes nn1's KeyUpdateCommand over one heartbeat of its own
   to nn1, the command applied before the call returns (`processCommandFromActor` with the actor of nn1: the standby
   path). With the bug the source's current key is now nn1's newest.
3. The source replicates its block to the target (`DataNode#transferBlock`) with a token under that key; the target
   holds it because its own heartbeat to nn1 delivered it. The recording passes.

A witness has to lose the target's heartbeat to nn1 (its request never reaching nn1, or nn1's answer lost after it
cleared the target's mark): the target then holds only nn1's pinned pair and the source signs with a serial two ahead,
so `retrievePassword` throws. Checked natively with the target's refresh left out: `InvalidToken` (keyID = nn1's
newest) on this tree, a clean transfer on the fixed code. With the fix the source signs with nn0's key whatever nn1
sends, and the same loss is harmless: the witness is this bug, not hdfs-adhoc-12's lost key update of the active.

Workarounds in the workload (configuration only): the DataNodes' heartbeat interval, the stale-node interval and the
standby's edit-tailing period are six hours, so the window has no daemon heartbeat (four streams, two DataNodes to two
NameNodes, would race the workload's heartbeats for the key-update mark) and the standby tails no edits in it. The
recording's heartbeats are the workload's own, as in the precedents' `refreshKeysFromNameNode`.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hdfs-adhoc-12,hdfs-buggy-17383")` on `retrievePassword`'s missing-key `throw new`; no `target.yaml` |
| the occurrence | `target_occurrence=first` in `case.sh` | the first occurrence of the target the recording observes: the target DataNode's check of the transfer's token (the only `retrievePassword` in the window) |
| scope | `case.sh` | hdfs-adhoc-12's classes: the block-key family, the IPC client (its fault doors), PBHelper, BPOfferService, DataNode |
| fault points, clocks, hooks | the engine's catalog, `RootCatalog`, the tree's `CausynthSymbolicSource.symbolize` | as every block-key case: `FAULT:HADOOP_IPC:REQUEST`/`RESPONSE` (the heartbeat to nn1), the clocks the slice reads, the block-key serial and expiry hooks (no `root-domains.jsonl`: the serial is pinned to its recording) |
| world depth | `case.sh` | 0 (one counterfactual), tasks 128, as the ad hoc family |
| loop bounds | `loop-bounds.jsonl` | none declared (default 8) |

## Result

Pending (run B17383a).
