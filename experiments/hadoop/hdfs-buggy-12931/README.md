# HDFS-12931 put back (hdfs-buggy-12931, point hdfs-adhoc-11)

## The bug

[HDFS-12931](https://issues.apache.org/jira/browse/HDFS-12931) (fix 3ba985997d1, 2018):
`DistributedFileSystem#getFileChecksum` on a replicated file fails when a DataNode cannot re-compute
the data-encryption key the client presents. The client's replicated checksum path
(`FileChecksumHelper.ReplicatedFileChecksumComputer.checksumBlock`) takes the
`InvalidEncryptionKeyException` that `DFSClient.connectToDN` raises out of the SASL handshake for an
ordinary failure of that DataNode: it logs it, keeps its cached key, tries the next location with
the same key, and once the locations run out the checksum ends in `PathIOException` ("Fail to get
block MD5"). The fix catches the exception, clears the cached key (`clearDataEncryptionKey`) and
retries the block once. It is the replicated-file twin of HDFS-17897 (the striped path; case
hdfs-17897).

Point hdfs-adhoc-11 (`docs/checks/HDFS.md`, `checks.tsv`) is the exception's origin on the
DataNode: `BlockTokenSecretManager.retrieveDataEncryptionKey`'s missing-key throw, a key-id lookup
that misses when the NameNode's rotation and the DataNode's key set disagree.

## What was put back, on graphchecker/hdfs-bug-12931

The fork's branch is `graphchecker/hdfs-checks` (899c200cc8e) plus two commits:

- **The bug, by hand** (28582861033, `HDFS-12931 put back: ...`): the
  `catch (InvalidEncryptionKeyException iee)` clause the fix added to `checksumBlock`
  (FileChecksumHelper :536-546 on 899c200cc8e) is removed, and the import only it used; the exception
  then falls into the generic `catch (IOException ie)`, as before the fix. The fix's other half (the
  method no longer declaring `throws IOException`) changes no behaviour and stays. The fix's test
  `TestEncryptedTransfer#testFileChecksumWithInvalidEncryptionKey` is removed: it asserts the clause
  (the key cleared once).
- **The workload and the target** (d9fde9f9480): `TestCausynthReplicatedChecksum`, and
  `hdfs-buggy-12931` added to the marker on `retrieveDataEncryptionKey`'s throw (line 584).

## The workload

`org.apache.hadoop.hdfs.TestCausynthReplicatedChecksum#testStaleEncryptionKeyFailsReplicatedChecksum`,
hdfs-17897's `TestCausynthStripedChecksum` on a replicated file: one DataNode (`dn0`), a file of one
replica written before the window, the block keys pinned before it (S+1 current, S+2 next on nn0 and
dn0; S = `Integer.MAX_VALUE / 12931`). Inside the window:

1. nn0 rotates twice (`KEY_MANAGER_TICK`; S+3 current).
2. dn0 is marked for a key update and takes the keys over one heartbeat of its own
   (`CausynthCluster.refreshKeysFromNameNode`, `DNA_ACCESSKEYUPDATE`).
3. The client fetches nn0's current encryption key over its own RPC (`cache-encryption-key`): S+3.
4. `replicated-file-checksum`: `getFileChecksum` presents it to dn0.

The recording succeeds (dn0 holds S+3). A world in which dn0's key-update heartbeat fails -- the
request never reaching nn0, or nn0's answer lost after it cleared dn0's key-update mark -- leaves dn0
without S+3, and its SASL handler's `retrieveDataEncryptionKey` throws. No existing test reaches it:
the fix's test needs keys that expire on the wall clock and a Mockito spy, and has no key update in a
window.

One workaround, in the workload's own configuration: `dfs.heartbeat.interval` is 6 h, so dn0's daemon
heartbeat runs at its registration only and the key update is delivered by the workload's heartbeat
alone (hdfs-buggy-11741's lesson: a slow replay's daemon heartbeat took the mark).

What the put-back changes in the witness world: the throw is dn0's and happens with or without the
fix; the bug is what the client does after it (the checksum fails, the key stays cached). In this
world the fixed client would fail too: its refetched key is nn0's current key, the one dn0 lacks; the
fix rescues a key that expired on the DataNode. The study's mechanism for this bug (a lost
`KeyUpdateCommand` reply, as hdfs-17897) is what the case asks for.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-buggy-12931` (beside hdfs-adhoc-11 and the named block-key cases) on `retrieveDataEncryptionKey`'s missing-key `throw new` (line 584) |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-12931/dn0#epoch0/region/REGION.7c569c3f-...@hdfs-12931/client#epoch0/replicated-file-checksum#1`: dn0's SASL handler occurrence under the client's checksum request |
| fault doors | the library catalog | the transport doors (`FAULT:HADOOP_IPC:REQUEST`, ...), as every HDFS case; none of its own |
| hook-minted roots | the tree | `HDFS.BLOCK_KEY.SERIAL_NO`, `HDFS.BLOCK_KEY.EXPIRY_DATE*` (`CausynthSymbolicSource.symbolize` in `BlockTokenSecretManager`) |
| root domains | `root-domains.jsonl` | hdfs-17897's row: `HDFS.BLOCK_KEY.SERIAL_NO` from +0 to +3 |
| wire mappings | `../communication-mappings.jsonl` | the SASL key id (`data-encryption-key-id`); block keys over the IPC door |
| scope | `case.sh` | hdfs-17897's: the block-key family (`blockkey_scope`) plus `DFSClient` and `FileChecksumHelper` |
| world depth | `case.sh` | 0 (RULES) |
| loop bounds | `loop-bounds.jsonl` | hdfs-17897's two rows at 8 |
| mechanism | `experiments/accept/report.py` | `hdfs-buggy-12931`: RPC_FAILURE (`MARKER_FLIPPED` by an `ipc.Client` fault, no clock) |

The run's budget is `hdfs-buggy-cases.tsv`'s 21600 s.

## Result

Pending.
