# HDFS-5766 put back (hdfs-buggy-5766, point hdfs-adhoc-11)

## The bug

[HDFS-5766](https://issues.apache.org/jira/browse/HDFS-5766) (fix c3b236ce5d2, 2014): a positional
read (`DFSInputStream.fetchBlockByteRange`) whose DataNode cannot re-compute the data-encryption key
the client presents takes that DataNode for a dead one. On the `InvalidEncryptionKeyException` out
of the SASL handshake the client clears its cached key, as it should, but then falls through to the
handling of every other `IOException`: it adds the DataNode to its dead nodes and chooses another
one, so with no other replica the read ends in `BlockMissingException` instead of retrying the same
DataNode with a new key. The fix added the missing `continue`.

Point hdfs-adhoc-11 (`docs/checks/HDFS.md`, `checks.tsv`) is the exception's origin on the
DataNode: `BlockTokenSecretManager.retrieveDataEncryptionKey`'s missing-key throw, a key-id lookup
that misses when the NameNode's rotation and the DataNode's key set disagree.

## What was put back, on graphchecker/hdfs-bug-5766

The fork's branch is `graphchecker/hdfs-checks` (899c200cc8e) plus two commits:

- **The bug, by hand** (73ee61e9b21, `HDFS-5766 put back: ...`). Today the code is
  `DFSInputStream.actualGetFromOneDataNode`'s `catch (IOException e)` (:1264-1294 on 899c200cc8e):
  an if / else-if / else chain whose first branch clears the key on an
  `InvalidEncryptionKeyException`, whose second refetches the block on a token error, and whose last
  marks the DataNode dead (`addToLocalDeadNodes`, `addNodeToDeadNodeDetector`) and throws so that
  `fetchBlockByteRange` chooses another node; after the first two the loop retries the same DataNode
  (the fix's `continue`, in today's shape). The bug is put back as it was: the encryption-key branch
  is its own `if`, so after clearing the key the exception goes on to the token check (false for this
  exception) and then to the dead-node branch. Every other exception takes the path it took. The fix
  had no test.
- **The workload and the target** (a8f16edc154): `TestCausynthEncryptedPread`, and `hdfs-buggy-5766`
  added to the marker on `retrieveDataEncryptionKey`'s throw (line 584).

## The workload

`org.apache.hadoop.hdfs.TestCausynthEncryptedPread#testStaleEncryptionKeyFailsPread`, hdfs-17897's
`TestCausynthStripedChecksum` shape (and hdfs-buggy-12931's) ending in a positional read: one
DataNode (`dn0`), a file of one replica written before the window, the block keys pinned before it
(S+1 current, S+2 next on nn0 and dn0; S = `Integer.MAX_VALUE / 5766`). Inside the window:

1. nn0 rotates twice (`KEY_MANAGER_TICK`; S+3 current).
2. dn0 is marked for a key update and takes the keys over one heartbeat of its own
   (`CausynthCluster.refreshKeysFromNameNode`, `DNA_ACCESSKEYUPDATE`).
3. The client fetches nn0's current encryption key over its own RPC (`cache-encryption-key`): S+3.
4. `encrypted-pread`: the file is opened and read at a position (`readFully(256, ...)`: `pread`,
   `fetchBlockByteRange`, `actualGetFromOneDataNode`), presenting S+3 to dn0.

The recording succeeds (dn0 holds S+3). A world in which dn0's key-update heartbeat fails leaves dn0
without S+3, and its SASL handler's `retrieveDataEncryptionKey` throws. No existing test reaches it
(the fix had none; TestEncryptedTransfer's reads have no key update in a window).

Two settings in the workload's own configuration, each named here:
- `dfs.heartbeat.interval` 6 h: dn0's daemon heartbeat runs at its registration only and the key
  update is delivered by the workload's heartbeat alone (hdfs-buggy-11741's lesson).
- `dfs.client.max.block.acquire.failures` 0 (as TestEncryptedTransfer's client in 899c200cc8e): a read
  that finds no live replica gives up at once instead of sleeping and refetching. It acts only after
  dn0's throw, on what the client does with it.

What the put-back changes in the witness world: the throw is dn0's and happens with or without the
fix; the bug is what the client does after it (dn0 taken for dead, the read failed). In this world the
fixed client would fail too: its retry presents a refetched key, nn0's current one, which dn0 lacks;
the fix rescues a key that expired on the DataNode. The study's mechanism for this bug (a lost
`KeyUpdateCommand` reply, as hdfs-17897) is what the case asks for.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget` naming `hdfs-buggy-5766` (beside hdfs-adhoc-11 and the named block-key cases) on `retrieveDataEncryptionKey`'s missing-key `throw new` (line 584) |
| the occurrence | `target_occurrence` in `case.sh` | `hdfs-5766/dn0#epoch0/region/REGION.7c569c3f-...@hdfs-5766/client#epoch0/encrypted-pread#1`: dn0's SASL handler occurrence under the client's read request |
| fault doors | the library catalog | the transport doors (`FAULT:HADOOP_IPC:REQUEST`, ...), as every HDFS case; none of its own |
| hook-minted roots | the tree | `HDFS.BLOCK_KEY.SERIAL_NO`, `HDFS.BLOCK_KEY.EXPIRY_DATE*` (`CausynthSymbolicSource.symbolize` in `BlockTokenSecretManager`) |
| root domains | `root-domains.jsonl` | hdfs-17897's row: `HDFS.BLOCK_KEY.SERIAL_NO` from +0 to +3 |
| wire mappings | `../communication-mappings.jsonl` | the SASL key id (`data-encryption-key-id`); block keys over the IPC door |
| scope | `case.sh` | the block-key family (`blockkey_scope`) plus `DFSClient` and `DFSInputStream` (hdfs-17897's pattern: the client class that caches the key and the class of the operation) |
| world depth | `case.sh` | 0 (RULES) |
| loop bounds | `loop-bounds.jsonl` | hdfs-17897's two rows at 8 |
| mechanism | `experiments/accept/report.py` | `hdfs-buggy-5766`: RPC_FAILURE (`MARKER_FLIPPED` by an `ipc.Client` fault, no clock) |

The run's budget is `hdfs-buggy-cases.tsv`'s 21600 s.

## Result

Pending.
