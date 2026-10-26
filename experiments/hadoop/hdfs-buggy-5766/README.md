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

## Result: SAT, MARKER_FLIPPED by a lost key-update heartbeat request, confirmed and reproduced 10/10 (B5766a, PASS)

Round B5766a (2026-10-26, snapshot `/bulk/gc-run/hb5766-1` = GraphChecker 0c3de7a23, tree set
`/bulk/trees/b5766` = a8f16edc154, `/bulk/gc-out/hdfs-buggy/5766`): 610 s, `SAT_CANDIDATE`
`FINAL_READY`, `report.py` **PASS**: `MARKER_FLIPPED` at valuation 1, `polarityDecides` true (the
recorded valuation, ordinal 0, is unsat), no gap, no defect, nothing bounded, `cone.json` unbound
empty; EXPLORE ended `WITNESSED` after 3 rounds (16 obligation verdicts, 14 planned tasks).
`round-verify.sh`: `end=(WITNESSED) z3=sat moved=1 polarityDecides=True leaves=87 confirmed`.

- **The moved root** is `REGION.763d087e-....in.8f25770d-...` = true: the `FAULT:HADOOP_IPC:REQUEST`
  door (`ipc.Client$Connection.sendRpcRequest`) of dn0's key-update heartbeat
  (`DatanodeProtocol.sendHeartbeat` under the workload's `heartbeat#1`): the request never reaches
  nn0, and no other heartbeat of dn0 runs in the window. hdfs-buggy-12931's witness failed the other
  direction (the answer); both are the study's lost key update.
- **The chain in the formula** (`final/candidate.smt2`, read by hand): `path_fatal__1` (the selected
  path, its own run's session b648a318, every arm attested there) is `allKeys.get(keyId) == null` on
  dn0's map (BlockTokenSecretManager :582-584), the map built by `container_dag` puts of the two pinned
  keys only (372440 = S+1, 372441 = S+2): with the marker true no heartbeat answer's keys are put;
  `keyId` is the SASL handoff of the client's key id (`data-encryption-key-id`,
  `message_family__1__698a5cf49693`), bound by `message_family__1__8049a0558300` to the client's received
  key 372442 (S+3: nn0's `generateDataEncryptionKey` from its current key, over
  `cache-encryption-key`).
- **CONFIRM**: "the selected session b648a318658afe1a-1ea6b601 is itself the run: it took every edge the
  model chose (2 arm(s), all its own deliveries), ran every moved root at the model's value, and
  observed the fatal at the anchor".
- **REPRODUCE**: 10/10 natively (the plant: the REQUEST fault on dn0's heartbeat; the fatal at the
  anchor in every run), control 0/10.
- **The moved root is necessary**: z3 on the exported file with the selected path asserted: sat; with
  the marker pinned to its recorded false as well: unsat.

**What the check detects here, and what it does not.** As for hdfs-buggy-12931: the point's throw is
on dn0, upstream of the client code the bug lives in, so the same world fires it with or without the
fix. Natively, with a scratch program (not committed) that drops dn0's key-update answer and then
reads at a position: on this tree, one throw on dn0, "Will fetch a new encryption key and retry" and at
once "Failed to read block ... Retry with the next available datanode" (dn0 taken for dead), then
`BlockMissingException`; with the fixed client (graphchecker/hdfs-checks' `hadoop-hdfs-client` classes
first on the class path), two throws on dn0 (the retry of the same DataNode presents a refetched key,
nn0's current one, which dn0 still lacks), then the same dead node and `BlockMissingException`. The
witness shows the bug's trigger reaching the point's own throw; it does not separate the put-back
client from the fixed one, which differs only after the throw.
