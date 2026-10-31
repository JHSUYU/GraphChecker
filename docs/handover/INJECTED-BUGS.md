# TODO: injected ad hoc coordination bugs, 5 per system, 20 in all (from 2026-10-30)

This file is a self-contained work order: a coding agent that reads it, then `START-HERE.md`, `RULES.md` and
`CHECKING.md` of its branch, can take over. The same file is on the four `system/<x>-injected` branches
(`docs/handover/INJECTED-BUGS.md`) and in `/bigtemp/vnr3ne/analysis/injected-2026-10-30/`.

## 0. The goal

The owner (2026-10-30, verbatim): "我们要从4个sys，每个sys sample 5个case。这5个case是我们自己从这么多bug模式总结的，我们自己
手动改总共adhod check代码，让adhoc coordiaont变成bugggy的。然后再看我们的tool能不能detect到。这里总共20个，在你充分理解我们
tool的能力后，设计出来18个我们的tool能detect到，2个能反映出我们的tool无法detect到（比如silent failrue?)或者别的什么".

For each of the four systems, five existing ad hoc coordination check points get a bug injected by hand into the
system's own code. Each injection follows a bug pattern of the real bugs we studied. The point's own declared throw
becomes reachable in a world GraphChecker can build. GraphChecker then runs on each case.

- **18 cases are designed to be detected.** GraphChecker finds them, the same way it detected the old bugs
  (`BUGGY-DETECT.md`).
- **2 cases are designed to be missed.** They show, with evidence, what GraphChecker does not cover by design: a silent
  failure, and a liveness bug. A real native run shows each bug, and GraphChecker's run shows it is not detected.

The specification of every case (§3) is a design to verify. If the code or a run shows that a case does not work as
written, fix the case in a general way: another mutation of the same pattern at the same point, or another
existing workload. Never change the engine for one case. Record what changed and why in the case README and in §6.

### The bug patterns (from our old bugs and bug checks)

| pattern | what goes wrong | real bugs it is drawn from |
| --- | --- | --- |
| P1 | stale cached coordination state, not refreshed on a miss | HDFS-11741, -12931, -5766, -10609; HBASE-15039; SOLR-40, SOLR-9440 |
| P2 | a remote error handled as a generic failure (no retry with fresh state, a wrong fallback) | HDFS-17897, -12931, -5766, -10609, -17967 |
| P3 | a non-idempotent retry after a lost reply | HBASE-20642; the HBase backup-lock CAS; ZooKeeperRetry (#32) |
| P4 | a partial failure leaves state inconsistent (no rollback or cleanup, skipped bookkeeping) | HDFS-14075; HBASE-28533, HBASE-30483; Solr migrate-buffer leak, restore construction, overseer lock leak |
| P5 | a race between a watcher, notification or writer and a reader (a stale view, a lost wakeup) | SOLR-9440; HBASE-15039; ZK election offer, container reuse; TRA start overwrite |
| P6 | an unhandled configuration-dependent path | SOLR-6101/6197 (`legacyCloud`); HDFS-17960 (`ordered=false`) |
| P7 | an ownership or session transfer not handled | ZOOKEEPER-710/2886 |
| P8 | time and expiry assumptions | SOLR-18406, SOLR-18413; HBase master activeTime; HDFS-11741 |
| P9 | state from the wrong source accepted | HDFS-17383 |
| P10 | a concurrent-initialization race on shared state | HDFS-14311 (GraphChecker's known limit) |
| P11 | a state change acknowledged before it is applied | HBASE-19953 |

GraphChecker's roots (docs/design/README.md):
- a transport fault at a woven door (either half);
- a LOCAL_IO or TIMED_WAIT door;
- a clock skew;
- a configuration value;
- a different pairing of a message, or of a shared-state read, with another writer (STATE).

It needs a declared `throw` that the bug's world reaches, inside the workload's recording window. The two designed-undetectable
cases fall outside this:
- **`hbase-inj-05`** is a silent failure: no throw fires, and a wrong value is returned.
- **`zk-inj-05`** is a liveness bug: a hang, with no throw.

## 1. Branches: where everything goes

Branches now form one chain per system. The engine and the shared case machinery only flow down it, by merging the
upper branch into the lower one:

```
system/<x>                 the ad hoc checks          (HDFS: system/hdfs-liftlab)
  -> system/<x>-buggy-detect   + the old bugs put back    (results/<sys>-buggy, BUGGY-DETECT.md)
       -> system/<x>-injected     + these injected bugs      (results/<sys>-injected, this file)
```

### GraphChecker (`git@github.com:JHSUYU/GraphChecker.git`)

| system | branch for this work | made from | worktree on liftlab |
| --- | --- | --- | --- |
| HDFS | `system/hdfs-injected` (cases `experiments/hadoop/hdfs-inj-NN/`, list `experiments/hadoop/hdfs-injected-cases.tsv`) | `system/hdfs-buggy-detect` | `/bigtemp/vnr3ne/wt/gc-hdfs-inj` |
| HBase | `system/hbase-injected` (`experiments/hbase/hbase-inj-NN/`, `hbase-injected-cases.tsv`) | `system/hbase-buggy-detect` | `/bigtemp/vnr3ne/wt/gc-hbase-inj` |
| ZooKeeper | `system/zookeeper-injected` (`experiments/zookeeper/zk-inj-NN/`, `zookeeper-injected-cases.tsv`: the file name must match `zookeeper-*cases.tsv`) | `system/zookeeper-buggy-detect` | `/bigtemp/vnr3ne/wt/gc-zookeeper-inj` |
| Solr | `system/solr-injected` (`experiments/solr/solr-inj-NN/`, `solr-injected-cases.tsv`) | `system/solr-buggy-detect` | `/bigtemp/vnr3ne/wt/gc-solr-inj` |

On its branch, each case is:
- a case directory `experiments/<sys dir>/<case id>/`, holding `case.sh` and `README.md`, the same shape as an old-bug
  case;
- one row in `experiments/<sys dir>/<prefix>-injected-cases.tsv`;
- one row in that system's `trees.tsv`;
- the case's expected mechanism in `experiments/accept/report.py` (`EXPECTED_MECHANISM`);
- in the end, its formula, claim and time row under `results/<sys>-injected/`.

`<sys dir>` is `hadoop`, `hbase`, `zookeeper` or `solr`. The case ids are `hdfs-inj-NN`, `hbase-inj-NN`, `zk-inj-NN` and
`solr-inj-NN`, with NN 01-05 as in §3.

### The system forks (the trees under test)

For each case, make one branch of the system's fork, from the base below. It holds exactly two commits on the base, as
the old bugs' trees do:
1. `<case id> injected: <what was changed>`: the mutation of §3 and nothing else; production code only.
2. `GraphChecker: <case id>'s workload and target (<test>)`: the target marker
   `@CausynthExceptionTarget("<case id>")` added on the point's throw, plus the workload test if the case needs a new
   one.

| system | fork | base of every injected tree | branch | tree name (`trees.tsv`) |
| --- | --- | --- | --- | --- |
| HDFS | `JHSUYU/hadoop` | `graphchecker/hdfs-checks` 899c200cc8e | `graphchecker/hdfs-inj-NN` | `hadoop-hdfs-inj-NN` |
| HBase | `JHSUYU/hbase` | `graphchecker/hbase-checks` b5d5cc6a209 | `graphchecker/hbase-inj-NN` | `hbase-inj-NN` |
| ZooKeeper | `JHSUYU/zookeeper` | 92c0f2b51 (the base of `graphchecker/zk-bug-*`: `graphchecker/zookeeper-checks` 889f0e961 + workload ports below the ephemeral range) | `graphchecker/zk-inj-NN` | `zookeeper-inj-NN` |
| Solr | `JHSUYU/solr` | `graphchecker/solr-checks` 12d23091d13 (`solr-inj-03` also cherry-picks the `CausynthLegacyCloud` holder fb0c5878b2) | `graphchecker/solr-inj-NN` | `solr-inj-NN` |

**The control tree.** For each detectable case, also make `graphchecker/<case-branch>-control`. It is the base plus
commit 2 only: the workload and the marker, with no mutation. This is how the ZooKeeper old bugs' `-control` branches
were made. Its tree name is `<tree>-control`.
- **Declaring it:** the case declares both trees through its argument. The id `<case id>-control` resolves to the same
  case directory with the argument `control` (`experiments/lib/case-id.sh`). So `case.sh` sets
  `repo=${GC_TREES}/<tree>${1:+-$1}`.
- **What it must give:** on the control tree the case must end UNSAT at the fixed point, or with every claim
  CONFIRM-refuted. This is the case's evidence that GraphChecker detects the injected bug, and not something the base
  tree already does.
- **Not to be confused with REPRODUCE's native "control 0/10",** which is a fault-free native run on the injected tree.

Never commit to the base branches (`graphchecker/<sys>-checks`), nor to the old-bug branches, nor to `baseline/mallory`.

### Liftlab paths for this work

| what | path |
| --- | --- |
| tree set (`GC_TREES`) | `/bigtemp/vnr3ne/wt/inj-trees-1` (a rebuilt tree is a new set: `inj-trees-2`, ...) |
| Maven repositories (`GC_M2`) | `/bigtemp/vnr3ne/m2/inj-1` |
| snapshots (what a run executes) | `/u/vnr3ne/gc-run/inj-<x>-<n>` (a commit of `system/<x>-injected`, built) |
| run outputs (`GC_OUT`) | `/bigtemp/vnr3ne/gc-out/injected/accept-<ROUND>-<case>` |
| notes, drivers, decision log | `/bigtemp/vnr3ne/analysis/injected-2026-10-30/` (`RUNS.txt`) |
| VM images | `/bigtemp/vnr3ne/vm-force12` (HDFS, HBase), `vm-force13` (ZooKeeper), `vm-force10` (Solr) |

## 2. One case, step by step

Model each step on an old-bug case of the same system (`experiments/<sys dir>/<sys>-buggy-*/`): its `case.sh`, its
README sections, and its tree's two commits.

1. **The tree branch.**
   - Clone the fork at the base: `git clone --branch <base branch> https://github.com/JHSUYU/<repo>.git`, or use a
     worktree of `~/<repo>`.
   - Create `graphchecker/<case-branch>` and make commit 1, the mutation.
   - Check that the mutation compiles, and that it is exactly the bug of §3, no wider.
2. **The workload and the marker** (commit 2).
   - Prefer the existing workload named in §3.
   - A new test copies the named model test and changes only what §3 says. Keep the recording-window calls of its
     model (`CausynthCluster.startRecording`, `beginTick`/`beginRequest`, ...), so the trigger lies inside the window.
   - Then make the control branch: the base plus the same commit 2, cherry-picked.
3. **Push the tree branch** to `JHSUYU/<repo>`. This needs the owner's OK. Ask once for all trees of a system.
4. **The case** on `system/<x>-injected`:
   - `experiments/<sys dir>/<case id>/case.sh`: copy the model case's and change the repo, test, target occurrence and
     scope.
   - `README.md`: the bug, what was injected (the diff), the workload, the declarations, the expected mechanism.
   - The rows in `<prefix>-injected-cases.tsv` and `trees.tsv`.
   - `EXPECTED_MECHANISM` in `report.py`.
5. **Build the tree** on a Maven host (lift02-06, lift08-10), from a built snapshot of the branch:
   `tools/onlift.sh -h <host> -g 8 env GC_TREES=/bigtemp/vnr3ne/wt/inj-trees-1 GC_M2=/bigtemp/vnr3ne/m2/inj-1
   experiments/<sys dir>/prepare-trees.sh <tree>`. Its log must end with `PASSED` for the workload: the healthy run
   passes.
   - **For a detectable case,** also check the healthy run never fires the target: `validate`, as in START-HERE §4.
   - **For an undetectable case,** run its native demonstration test (§3) and record that it FAILS on the injected
     tree, and passes on the base tree.
6. **The run.** One round with the system's cases, from lift11:
   `env GC_OUT=/bigtemp/vnr3ne/gc-out/injected GC_TREES=/bigtemp/vnr3ne/wt/inj-trees-1 GC_M2=/bigtemp/vnr3ne/m2/inj-1
   LIFTS="lift02 lift03 lift04 lift05 lift06 lift08 lift09 lift10 lift12 lift13 lift14"
   CAUSYNTH_CUSTOM_JDK_HOME=<image>/j2sdk-image CASE_TIMEOUT_SECONDS=21600 PRUNE=0 CASES="<case> <case>-control ..."
   bash <snapshot>/tools/rounds/launch-round.sh <snapshot> <ROUND>`.
   - Every detectable case runs beside its control.
   - An undetectable case needs no control tree: its evidence is the native demonstration.

   Rounds:
   - `I1`: all cases, side by side.
   - `IE1`: each case alone, for the time breakdown, as round E1 did (`/bigtemp/vnr3ne/analysis/buggy-detect-exclusive-2026-10-28/series-E1.sh`
     is the model driver; copy it, never edit a driver a series reads).
7. **Read and accept** (`CHECKING.md`).
   - **A detectable case is detected when** all of these hold:
     - it is SAT and CONFIRM confirmed it;
     - its control case on the control tree is UNSAT, or every claim there is refuted;
     - native REPRODUCE gives k/10, with REPRODUCE's own fault-free control 0/10;
     - `report.py` says PASS, with the expected mechanism and the injected root in `movedRoots`;
     - the chain read with `tools/analysis/smt-legend.py` runs through the injected code.
   - **A designed-undetectable case is done when** both hold:
     - its native demonstration shows the bug;
     - GraphChecker's run ends without a detection (UNSAT at the fixed point, or no witness), and the README says, with
       file:line, why the design cannot see it.
   - A detectable case that is not detected is a finding. Find the cause (CHECKING traps; `vacuity.py`). Fix it
     generally (an engine fix by the rules, a workaround named in STATUS), or rework the case per §0. Never declare
     it undetectable after the fact without the owner's word.
8. **Record:**
   - the case README's result section;
   - the table of §4;
   - `results/<sys>-injected/` (`final-stats.py`, as `results/<sys>-buggy/`);
   - `RUNS.txt`.

## 3. The 20 cases

Each case below gives its point, pattern, mutation, workload, trigger, precedent and control. The full research,
with every file:line and the alternates, is in `docs/handover/injected/proposals-<sys>.md` beside this file.

### HDFS (`system/hdfs-injected`; fork `JHSUYU/hadoop`, base 899c200cc8e; 5 detectable)

HDFS notes from the research:
- **Roots proven here:** the IPC door (the DataNode heartbeat and key update: 12931, 5766, 10609, 17383, 17899,
  hdfs-adhoc-12), LOCAL_IO (14075, hdfs-adhoc-10), CLOCK (11741), CONFIG (17960) and STATE (slowdisk-zero).
- **The control is mandatory:** the base tree, with the same workload and declaration, must be UNSAT, or its claims
  CONFIRM-refuted, with the native control at 0/10.
- **Block-key points (11, 12):** the base tree reaches the throw only when a DataNode misses TWO rotations, because the
  NameNode publishes its next key ahead of time (BlockTokenSecretManager:180-207, :302). So a ONE-rotation workload is
  safe on the correct code, and that is what makes the block-key controls UNSAT.
- **Avoiding duplicates:** `hdfs-inj-c` of the research was the HDFS-11741 put-back itself, and was dropped. No case may
  duplicate an old bug's put-back.

| case | point | pattern | root (expected mechanism) | confidence |
| --- | --- | --- | --- | --- |
| `hdfs-inj-01` | hdfs-adhoc-45, FSEditLog:1471 | P4 failed segment start swallowed | LOCAL_IO (MARKER_FLIPPED) | high |
| `hdfs-inj-02` | hdfs-adhoc-12, BlockTokenSecretManager:542 | P9 the standby's key taken as current | IPC door RESPONSE (MARKER_FLIPPED) | high |
| `hdfs-inj-03` | hdfs-adhoc-11, BlockTokenSecretManager:584 | P1 the next key no longer published ahead | IPC door (MARKER_FLIPPED) | high |
| `hdfs-inj-04` | hdfs-adhoc-20, BPOfferService:617 | P7 a stale ACTIVE claim accepted | STATE (STATE_PAIRING_FLIPPED) | medium |
| `hdfs-inj-05` | hdfs-adhoc-10, Journal:521 | P2 a JournalNode that rejected a batch keeps getting batches | IPC door or LOCAL_IO (MARKER_FLIPPED) | medium |

1. **`hdfs-inj-01`: a failed log-segment start is swallowed, not fatal.**
   - **Mutation** (FSEditLog:1438-1446, the private `startLogSegment`'s catch): log and `return`, instead of cleaning up
     and `terminate(1, msg)`, "best-effort: a redundant journal failed; the next roll re-opens the segment".
     HDFS-14075's put-back re-threw the exception instead; this is a different mutation of the same pattern.
   - **Workload:** copy hdfs-buggy-14075's `TestCausynthRollSegmentFailure#testNextRollAfterFailedStartLogSegment`
     (with the third commit: "the second roll rolls at once") and its case.sh.
   - **Trigger:** a LOCAL_IO fault at roll 1's edits_inprogress open (`EditLogFileOutputStream.<init>`, :89). The state
     stays BETWEEN_LOG_SEGMENTS, and roll 2's `endCurrentLogSegment` throws.
   - **Precedent and control:** hdfs-buggy-14075 (native 10/10). On the base, `terminate` kills the NameNode at roll 1:
     UNSAT.
2. **`hdfs-inj-02`: a DataNode takes the standby's key as its current key** (the caller side of HDFS-17383).
   - **Mutation** (BPOfferService:833-840, `processCommandFromStandby` DNA_ACCESSKEYUPDATE): `addKeys(bpid, keys, true)`
     instead of `false`, copied from the active path at :796-799. HDFS-17383's put-back changed the callee
     (`BlockTokenSecretManager.addKeys`).
   - **Workload:** copy hdfs-buggy-17383's `TestCausynthStandbyCurrentKey#testTransferAfterStandbyKeyUpdate` (HA, two
     DataNodes, unencrypted transfer, the standby rotates twice) and its case.sh.
   - **Trigger:** an IPC RESPONSE fault on the TARGET DataNode's heartbeat to the standby. Its KeyUpdateCommand is lost,
     while the source signs with the standby's newest key, so the target's `retrievePassword` throws.
   - **Precedent and control:** hdfs-buggy-17383 (native 10/10). On the base, the source signs with nn0's key whatever
     the standby sends: UNSAT.
3. **`hdfs-inj-03`: the NameNode stops publishing its next block key ahead of time.**
   - **Mutation:** delete `allKeys.put(nextKey.getKeyId(), nextKey)` in `generateKeys` (BlockTokenSecretManager:207) and
     in `updateKeys` (:302), "allKeys holds the keys tokens can carry now".
   - **Workload:** copy hdfs-17899-bug3's encrypted
     `TestCausynthDataTransferRpcFailure#testReplicationAfterModeledKeyRefreshRpcFailure` as a new method
     `testReplicationAfterOneRotation`:
     - rotate ONCE (`rotation < 1`, precondition `+1`);
     - make the pin asserts tree-agnostic: the keys are a subset of `pinned`, they contain S+1, and S+1 is current;
     - set `dfs.heartbeat.interval` to 6 h.
   - **Trigger:** an IPC door fault (request or response) on the TARGET DataNode's key-update heartbeat. The target
     holds only S+1, the source presents a DEK under S+2, and :584 throws.
   - **Precedent and control:** the 17899 and 12931/5766/10609 door (native 10/10). On the base, the target already holds
     S+2 from the pin, so no fault, clock or combination removes it: UNSAT.
4. **`hdfs-inj-04`: a stale ACTIVE claim is accepted.**
   - **Mutation** (BPOfferService:587-601): drop the `isMoreRecentClaim` check, so any ACTIVE claim sets
     `bpServiceToActive`.
   - **Workload:** new `TestCausynthHaClaimReorder` from `TestCausynthStandbyCurrentKey` (HA). In the window, nn0
     claims ACTIVE at a high txid over dn0's heartbeat, then nn1 sends a late ACTIVE claim at a lower txid. The
     recording orders them high, then low.
   - **Trigger:** STATE. The second heartbeat's read of `lastActiveClaimTxId` (:587/:616) is re-paired, so that the
     low-txid claim is processed while `bpServiceToActive == actor` with the high value: `txid >= lastActiveClaimTxId`
     is false, and :617 throws.
   - **Precedent:** slowdisk-zero (STATE, native 10/10). On the base, the guard at :592 rejects the stale claim first:
     UNSAT.
   - **Risk:** the HDFS-14311 lesson. The differing writer must be recorded before the reader's occurrence closes, and
     CONFIRM must hold the pairing after the deciding reads. The fallback is `hdfs-inj-j` (CLOCK) of the research.
5. **`hdfs-inj-05`: a JournalNode that rejected a batch keeps getting batches.**
   - **Mutation** (IPCLoggerChannel:363-370, `sendEdits`): drop `outOfSync = true` on a failed `journal()`, "a failed
     batch is just logged; the quorum covers it".
   - **Workload:** hdfs-adhoc-10's `TestQuorumJournalManager` with a new method `testSingleWriterTwoFlushes`:
     `writeSegment(cluster, qjm, 1, 3, false)`, then `writeTxns(stm, 4, 2)`, close, `finalizeLogSegment(1, 5)`, then
     `checkRecovery`. The DECLARED occurrence is jnK's SECOND `journal()` (flush 2), read off a SEED.
   - **Trigger:** H1-adhoc-10's root for jnK's segment start. It is either an IPC REQUEST fault on
     `QJournalProtocol.startLogSegment` to jnK, or the LOCAL_IO SYNC fault at jnK's `lastWriterEpoch` persist. jnK keeps
     epoch 0. Flush 2's `journal()` is still sent to it, and :520 compares 1 with 0.
   - **Precedent and control:** H1-adhoc-10 (SAT, native 10/10) at flush 1, QJM's designed tolerance. On the base,
     `outOfSync` stops flush 2 at `throwIfOutOfSync` (:358), so the declared occurrence is unreachable: UNSAT.
     Check that the declared occurrence is not answered by shape by flush 1's occurrence.

Alternates (researched, `proposals-hdfs.md`):
- `hdfs-inj-j`: point 11, P8, CLOCK, medium. `addKeys` prunes expired keys after the merge instead of before; a skew of
  the target DataNode's `removeExpiredKeys` clock prunes the key it just received.
- `hdfs-inj-e`: point 30, STATE, medium-low. Block recovery against a relinquished ACTIVE.
- `hdfs-inj-f`: point 33, STATE, low.

### HBase (`system/hbase-injected`; fork `JHSUYU/hbase`, base b5d5cc6a209; 4 detectable + 1 undetectable)

HBase notes from the research:
- **Roots with a precedent here:** HBase RPC request and response faults, the ZooKeeper read fault, STATE and CONFIG.
  There is no LOCAL_IO or CLOCK precedent.
- **Claims:** run every case with `CAUSYNTH_CAMPAIGN_MAX_CLAIMS=8`. COMPOSE still proposes re-pairings that the client's
  program order forbids (TODO HBase 15), and CONFIRM refutes them first, as in hbase-buggy-20642.
- **Avoid the existing bugs:** several points are already buggy on the unmodified tree (04, 22, 34). Each workload below
  avoids the existing witness; keep it that way.

| case | point | pattern | root (expected mechanism) | confidence |
| --- | --- | --- | --- | --- |
| `hbase-inj-01` | hbase-adhoc-04, AbstractStateMachineTableProcedure:163 | P3 non-idempotent retry | HBASE_RPC RESPONSE fault (MARKER_FLIPPED) | high |
| `hbase-inj-02` | hbase-adhoc-22, NamespaceStateManager:168 | P4 bookkeeping skipped | STATE (STATE_PAIRING_FLIPPED) | medium-high |
| `hbase-inj-03` | hbase-adhoc-08, ClusterSchemaServiceImpl:111 | P1+P2 failed write drops the cache entry | HBASE_RPC REQUEST fault (MARKER_FLIPPED) | medium |
| `hbase-inj-04` | hbase-adhoc-34, AuthenticationTokenSecretManager:160 | P1 the refresh reads a stale snapshot | STATE (STATE_PAIRING_FLIPPED) | high |
| `hbase-inj-05` | hbase-adhoc-34 (:160) | silent failure (P1+P2) | **designed undetectable** | -- |

1. **`hbase-inj-01`: the master drops a DisableTable's nonce.**
   - **Mutation** (MasterRpcServices:878-887): `server.disableTable(table, HConstants.NO_NONCE, HConstants.NO_NONCE)`
     instead of the request's nonce group and nonce, "disabling an already-disabling table is a no-op".
   - **Workload:** copy `TestCausynthDisableRetryNonce` and case.sh from hbase-buggy-20642 (target `REGION.98cba534...#2`,
     depth 1).
   - **Trigger:** a lost reply at `RpcConnection.finishCall` for the first DisableTable. The client retries with the same
     nonce, the master builds a second DisableTableProcedure, and its preflight throws.
   - **Precedent and control:** hbase-buggy-20642's world exactly; native by shape (accepted for 20642). On the
     unmodified tree the retry is deduplicated by its nonce: UNSAT.
2. **`hbase-inj-02`: a merge does not give its region back to the namespace quota.**
   - **Mutation** (NamespaceStateManager:98-100): `if (nsInfo != null && incr > 0)`, "a merge only shrinks; reconciled
     when the table goes".
   - **Workload:** new `TestCausynthMergedTableQuota` from `TestCausynthTruncatedTableQuota` (hbase-adhoc-22's). Steps:
     quota max 2; create T with 2 regions; merge them into 1; disable T; `deleteTableAsync(T)`; sleep 2 s; create U with
     1 region. Use 22's scope; depth 0; read the target off a SEED.
   - **Trigger:** U's quota read is paired with T's addTable(2) version, before the deletion's removeTable, held at its
     claim entry: 2 + 1 > 2.
   - **Precedent:** hbase-adhoc-22's own PASS (the same read, the same hold), where the truncate, like this merge,
     writes nothing.
3. **`hbase-inj-03`: a failed namespace update drops the cached descriptor, and nothing reloads it.**
   - **Mutation** (ModifyNamespaceProcedure:85-91): in the retriable catch of MODIFY_NAMESPACE_UPDATE_NS_TABLE,
     `invalidate` the cached descriptor and finish (`Flow.NO_MORE_STATE`), plus a 3-line public wrapper of
     `TableNamespaceManager.uncached`.
   - **Workload:** new `TestCausynthNamespaceQuotaSplit`: namespace max 10; create `ns:t`; modify the namespace to 20;
     split the region. The target is the split procedure's getNamespace activation, the k-th on master0, read off a
     SEED. The handler-side calls are folded (they carry no occurrence address), which is why the split is the consumer.
   - **Trigger:** an HBASE_RPC REQUEST fault on master0's hbase:meta Mutate in UPDATE_NS_TABLE
     (`AbstractRpcClient.callMethod` under `TableNamespaceManager.addOrUpdateNamespace`). The cache entry is dropped,
     and the split's quota read misses at :111. That throw is caught at NamespaceStateManager:143; count it as
     hbase-adhoc-24's was.
   - **Precedent:** ns-rsgroup-removal moved this door kind (native 10/10). F2S-adhoc-08 admitted these very doors
     (obligations `688dd4026bc4bcc1`, `da0d4a10308716ca`), which the unmodified retry refused.
4. **`hbase-inj-04`: the key refresh on a miss rebuilds from the watcher's last children snapshot, not from ZooKeeper.**
   - **Mutation** (`ZKSecretWatcher`, hbase-server `.../security/token/ZKSecretWatcher.java`):
     - add a field `private volatile List<ZKUtil.NodeAndData> lastNodes;`;
     - set it wherever the watcher fetches the children (`start` :63-65, `nodeCreated` :73-75, `nodeChildrenChanged`
       :126-128);
     - make `refreshKeys` (:219-228) call `refreshNodes(lastNodes)` when it is non-null, instead of
       `ZKUtil.getChildDataAndWatchForNewChildren`, "the watcher already holds the children; save a ZooKeeper round
       trip per miss".

     This is deliberately NOT HBASE-15039's put-back, which removed the refresh. Here the refresh runs, but on a stale
     view.
   - **Workload:** copy `TestCausynthTokenKeyWatch` and case.sh from hbase-buggy-15039. Add no ZOOKEEPER faults: the key
     master's write fault reaches :160 on the unmodified code too.
   - **Trigger:** STATE. The other server's lookup (:137) is paired with the map before its watcher's
     `nodeChildrenChanged`/addKey; the watcher's occurrences are held after the anchor. The refresh rebuilds from
     `lastNodes`, which lacks the new key, so :160 throws.
   - **Precedent and control:** hbase-buggy-15039's world and holds (native 10/10 / 8/10). On the base, `refreshKeys`
     reads ZooKeeper, finds the key and nothing throws: UNSAT.
5. **`hbase-inj-05` (designed undetectable, a silent failure): a key miss is answered with the current key.**
   - **Mutation** (AuthenticationTokenSecretManager:137-158): replace the whole miss block (the abort check, the elector
     restart, refreshKeys and the re-read) with `masterKey = currentKey;`, "a token is almost always signed with the
     newest key".
   - **GraphChecker run:** TestCausynthTokenKeyWatch as is. Expected UNSAT_CLOSED: `currentKey` is never null in the
     window, so no world takes :160.
   - **Native demonstration** (it must FAIL on the injected tree and pass on the base):
     1. issue T1 under K1;
     2. roll to K2 and sleep 2 s;
     3. `other.removeKey(K1)`, the device of TestCausynthTokenKeys;
     4. `assertArrayEquals(T1.getPassword(), other.retrievePassword(T1 id))`.

     The password is computed with K2, so the assertion fails on every run. On the base, refreshKeys reloads K1 and
     the assertion holds.
   - **Why GraphChecker cannot see it:** the wrong value is returned silently. It surfaces only in SASL or the test's
     assertion, which is no declared throw.

Alternates (researched, `proposals-hbase.md`):
- `hbase-inj-d`: point 04, P11 "acknowledged before applied", STATE, medium. The quota observer enables
  asynchronously, with 04's workload, a sleep, and the client's HBase RPC faults off.
- `hbase-inj-g`: point 34, P8, CONFIG, low-medium. An old key is kept for lifetime minus interval; needs the startup
  window.
- `hbase-inj-f`: point 08, P5, STATE, medium-low.

**Side finding:** a split rolled back after PRE_OPERATION never returns its namespace-quota increment.
`onRegionSplitReverted` has had no caller since HBASE-14614. This is a real-bug candidate for a check, not used here.

### ZooKeeper (`system/zookeeper-injected`; fork `JHSUYU/zookeeper`, base 92c0f2b51; 4 detectable + 1 undetectable)

ZooKeeper notes from the research:
- **Roots that work here today:** the ZooKeeper WRITE door (a commit, then ConnectionLoss), STATE, and CLOCK. READ doors
  are never asked in ZooKeeper-native cases, and no LOCAL_IO door sits at the epoch reads.
- **Controls:** the session points (01-03) are reached on correct code by the expirer's clock or a moved session's
  straggler. The discriminating points are the bug-check targets (FinalRequestProcessor:694, ZooKeeperServer:2201,
  ZKDatabase:341), each already SAT because of a real bug left in the tree. Every case therefore runs its CONTROL: the
  base tree, the same workload and declaration, expected UNSAT or a claim CONFIRM refutes. Read every target occurrence
  off a `STOP_AFTER=SEED` run.

| case | point | pattern | root (expected mechanism) | confidence |
| --- | --- | --- | --- | --- |
| `zk-inj-01` | FinalRequestProcessor:694 (container-reuse's target) | P1 stale scan trusted | STATE (STATE_PAIRING_FLIPPED) | high |
| `zk-inj-02` | ZooKeeperServer:2201 (retry-seq-quota's target) | P3 non-idempotent retry | ZOOKEEPER WRITE fault (MARKER_FLIPPED) | high |
| `zk-inj-03` | FinalRequestProcessor:694 (quota-init's target) | P2/P4 rollback of a half-made quota | ZOOKEEPER WRITE fault (MARKER_FLIPPED) | medium-high |
| `zk-inj-04` | zk-adhoc-01, SessionTrackerImpl:361 | P5 a writer moved ahead of its reader | STATE (STATE_PAIRING_FLIPPED) | medium |
| `zk-inj-05` | the queue recipe's take (FinalRequestProcessor:694 declared) | P5 lost wakeup, a liveness bug | **designed undetectable** | -- |

1. **`zk-inj-01`: the container cleanup trusts its own scan.**
   - **Mutation** (PrepRequestProcessor:327-337, `case OpCode.deleteContainer`): drop the `childCount > 0` NotEmpty
     check, "ContainerManager posts only containers it found empty".
   - **Workload:** new `server.CausynthContainerChildTest` from `CausynthContainerReuseTest`, with the same `OneCheck`
     manager. Steps: create container `/c`, add and delete a child, start the cleanup, sleep 1 s, create `/c/c2`, then
     getData `/c` (the target, `REGION.ce9149ce#1`). Use container-reuse's case.sh branch.
   - **Trigger:** the getData's node-map lookup is paired with the cleanup's `nodes.remove` (DataTree:563).
   - **Precedent and control:** container-reuse (native 10/10). The base Prep refuses the delete, so the control is UNSAT.
2. **`zk-inj-02`: WriteLock forgets its own node after a lost reply.**
   - **Mutation** (recipes-lock `WriteLock.findPrefixInChildren` :185-201): always create, without first listing the
     children for its own prefix, "the name carries our session id".
   - **Workload:** new `recipes.lock.CausynthWriteLockQuotaTest` from `CausynthZooKeeperRetryQuotaTest`. Steps:
     `/locks` with hard count quota 3; locker A locks; locker B locks (B's create is the target).
     Declarations: `zk_module=zookeeper-recipes/zookeeper-recipes-lock`, `-Dzookeeper.enforceQuota=true`.
   - **Trigger:** the WRITE door on A's create commits, then ConnectionLoss. The retry creates a second node, and B
     counts 4 > 3.
   - **Precedent and control:** retry-seq-quota (native 10/10). The base retry finds its node, so the control is UNSAT.
3. **`zk-inj-03`: a compensating rollback of a half-made quota.**
   - **Mutation** (cli `SetQuotaCommand.createQuota` :243-244): if the stat create throws, delete the limit node and
     rethrow, "no limit without its stat". This is a plausible but wrong "fix" of quota-init's bug.
   - **Workload:** new `test.CausynthQuotaRollbackTest` from `CausynthQuotaRetryTest`. Steps: createQuota, tolerating
     ConnectionLoss; then `listQuota`. The target is listQuota's getData of the LIMIT node (ListQuotaCommand:92), not of
     the stat node.
   - **Trigger:** the WRITE door on the stat create commits, then ConnectionLoss. The rollback deletes the limit, and the
     limit getData gets NoNode.
   - **Precedent:** quota-init (native 10/10). The quota-init world on the base fires at the stat getData, another
     occurrence. Check the target answers by shape on a SEED.
4. **`zk-inj-04`: a learner's close marks the session closing ahead of the pipeline.**
   - **Mutation** (`LeaderZooKeeperServer.submitLearnerRequest` :193): if the request is a closeSession,
     `sessionTracker.setSessionClosing(request.sessionId)` before `prepRequestProcessor.processRequest`.
     ZOOKEEPER-1208 put this mark in pipeline order.
   - **Workload:** `test.CausynthSessionCloseOrderTest` from `CausynthSessionMoved710Test` (5 peers). The client on a
     follower creates `/sc`. A closer thread closes after 2 s; a writer thread does setData `/sc` (the leader's Prep of
     it is the target).
   - **Scope:** zk-adhoc-02's WITHOUT ExpiryQueue, `causynth_scope_growth_budget=0`, `client_fault_transports=(ZK_QUORUM)`.
     Keeping the expirer's clock out of scope is what keeps the control UNSAT.
   - **Trigger:** `session.isClosing()` (:360) is paired with the injected write on the LearnerHandler thread, held at
     the leader's Prep claim, as in 710.
   - **Precedent:** zk-buggy-710/2886's hold (native 10/10).
5. **`zk-inj-05` (designed undetectable, a liveness bug): DistributedQueue.take() looks without a watch.**
   - **Mutation** (recipes-queue `DistributedQueue.java:234`): `orderedChildren(null)` instead of
     `orderedChildren(childWatcher)`, "one watch per take leaks watches". An empty look then waits forever on a latch
     nobody counts down.
   - **GraphChecker run:** new `recipes.queue.CausynthQueueTakeTest`. An offer thread offers at once; a take thread
     sleeps 1 s and takes. The declared target is take's getData. Expected UNSAT_CLOSED.
   - **Native demonstration:** the stock `DistributedQueueTest#testTakeWait1` (take first, offer 1 s later) HANGS on the
     injected tree, caught by a JUnit timeout, and passes on the base.
   - **Why GraphChecker cannot see it:** nothing throws, and the declared occurrence is never reached. A replay that
     blocks is a stall, and a stall refutes; there is no "must eventually happen" target.

Alternates (researched, `proposals-zookeeper.md`):
- `zk-inj-c`: point 694, P6+P8, CLOCK, medium. A refactor turns the interval 0 ("never") into the 5-minute default.
- `zk-inj-e`: ZKDatabase:341, P9, STATE, medium-low. The leader forwards from its applied zxid.
- `zk-inj-u2`: a silent failure. The TTL age is computed on the monotonic clock.

**Side finding:** the unmodified lock recipe deadlocks after a lost create reply, with no throw. `findPrefixInChildren`
stores the child name without its directory (WriteLock.java:190).

### Solr (`system/solr-injected`; fork `JHSUYU/solr`, base 12d23091d13; 5 detectable)

Solr notes from the research:
- **Workloads:** every case uses a short focused `TestCausynth*` workload on 1-2 nodes. The study workloads ran into the
  2 h cap.
- **Roots proven here:** the ZooKeeper write door (after ZkCmdExecutor's retries), the SolrJ HTTP door, CLOCK
  (nanoTime), field-backed CONFIG (the `CausynthLegacyCloud` holder), and a STATE VIEW pairing of a published view.
- **The rules a VIEW pairing obeys:**
  - A VIEW pairing is offered only for the earliest read of the view in the target occurrence.
  - Solr's own synchronous refreshes are never deferred.
  - A hold lasts at most 3000 ms of recorded time.
  - A client update's `_stateVer_` refreshes `state.json` at once.
- **Before each case runs:** run the control (the base tree, expected UNSAT) and 20 native healthy runs.
- **Point 19 is used three times,** with three different patterns and roots. Solr's other points are reachable only
  through VIEW pairings or depth-2 worlds.

| case | point | pattern | root (expected mechanism) | confidence |
| --- | --- | --- | --- | --- |
| `solr-inj-01` | solr-adhoc-19, CoreContainer:1330 | P2 failed state write taken as "self-registration" | ZOOKEEPER create fault (MARKER_FLIPPED) | high |
| `solr-inj-02` | solr-adhoc-13, RoutedAlias:350 | P1 alias view not refreshed | STATE VIEW of `/aliases.json` (STATE_PAIRING_FLIPPED) | medium |
| `solr-inj-03` | solr-adhoc-19, CoreContainer:1330 | P6 split placeholders lose coreNodeName | CONFIG legacyCloud (MARKER_FLIPPED, configurationOnly) | high |
| `solr-inj-04` | solr-adhoc-19, CoreContainer:1330 | P8 a 5 s bound, then proceed | CLOCK nanoTime (CLOCK_SKEW) | medium |
| `solr-inj-05` | solr-adhoc-31, CollectionsHandler:1477 | P4/P5 a wait's watcher never removed | STATE VIEW of `state.json` (STATE_PAIRING_FLIPPED) | medium |

1. **`solr-inj-01`: AddReplicaCmd falls back to self-registration when the replica's state write fails.**
   - **Mutation** (AddReplicaCmd:246-267, the non-legacy branch): catch the `offerStateUpdate` exception, log it, set
     `inState=false`, and set CORE_NODE_NAME only if `inState`.
   - **Workload:** new `TestCausynthAddReplicaState#addReplicaOnTheOtherNode` (2 nodes; `use.perreplica=false`), from
     `TestCausynthMigrateRuleTarget`. Steps: create C (1x1) on node1; ADDREPLICA on node0; then a bounded wait for 2
     active replicas. Target: node0's first `CoreContainer.create` (`REGION.05d95c18-...#1`); depth 0.
   - **Trigger:** the ZOOKEEPER create door under `SolrZkClient.create` (ZkDistributedQueue.offer:328) in the ADDREPLICA
     Overseer task: the item commits, then ConnectionLoss. The CREATE goes out without coreNodeName.
   - **Precedent and control:** migrate-buffer-leak's door and path (native 10/10). On the base, the failed offer throws
     before any CREATE: UNSAT.
2. **`solr-inj-02`: the routing node no longer refreshes its alias view after MAINTAINROUTEDALIAS.**
   - **Mutation** (RoutedAlias:400-403): delete `aliasesManager.update()` in `ensureCollection`, together with the comment
     that names this very hazard.
   - **Workload:** new `TestCausynthTraSyncCreate` from `TestCausynthTraStartAlias`. Use a fixed start 2019-09-14 and
     interval `+1DAY`; one add past the head's range makes the creation synchronous. Scope RoutedAlias,
     TimeRoutedAlias, RoutedAliasUpdateProcessor, MaintainRoutedAliasCmd; target `first`.
   - **Trigger:** doSynchronous's first alias read is paired with VIEW@n (the TRA's creation), and the publication of
     MAINTAIN's version is held.
   - **Precedent:** tra-start-overwrite (the VIEW of `/aliases.json`, native 10/10). On the base, `update()` is a
     synchronous publication, so nothing older is offered.
3. **`solr-inj-03`: the split's placeholder replicas lose their coreNodeName under non-legacy.**
   - **Mutation:** the base plus the legacyCloud holder (cherry-pick fb0c5878b2 from `graphchecker/solr-bug-6101`). In
     AddReplicaCmd, move the CORE_NODE_NAME lookup inside `if (!skipCreateReplicaInClusterState)`.
   - **Workload:** solr-buggy-6101's `TestCausynthSplitShardLegacy` with 2 nodes and a 1x2 collection; the target is
     node1's create of the first placeholder (a SEED gives the index).
   - **Trigger:** CONFIG `legacyCloud` true -> false.
   - **Precedent:** solr-buggy-6101/6197 (native 10/10 through the field plant). It is close to 6101; only the code path
     is new.
4. **`solr-inj-04`: AddReplicaCmd bounds its wait for the replica's state at 5 s, then proceeds.**
   - **Mutation** (AddReplicaCmd:265-266): replace `waitToSeeReplicasInState` with a `System.nanoTime()` 5 s poll loop
     that sets CORE_NODE_NAME only if found, "don't hold the Overseer on a slow state update".
   - **Workload:** TestCausynthAddReplicaState, as `solr-inj-01`.
   - **Trigger:** a forward skew of the Overseer's nanoTime of at least 5 s between the deadline read and the loop check.
   - **Precedent:** solr-18406 (two nanoTime reads on one node, native 10/10).
5. **`solr-inj-05`: CREATE's wait for an active collection leaks its watcher, so FORCELEADER reads a lagging view.**
   - **Mutation** (CollectionsHandler.waitForActiveCollection :1548-1589): `registerCollectionStateWatcher` with a watcher
     that never returns true, plus a latch. Use fully qualified names so :1477 does not move.
   - **Workload:** `TestCausynthForceLeaderStaleView` from solr-bug-9440 (2e2acd32d6), without 9440's Overseer-delay
     workaround. Reorder it to send FORCELEADER right after the client sees the replica DOWN, which keeps the hold
     under 3 s.
   - **Trigger:** FORCELEADER's first read of node0's `state.json` view is paired with v_active, and node0's publication
     of v_down is held.
   - **Precedent:** solr-buggy-9440 (the same point and workload, native 10/10). On the base, node0 reads lazily (a live
     fetch, never deferred): UNSAT.

Alternates (researched, `proposals-solr.md`):
- `solr-inj-g`: point 07, P10, low-medium. The HDFS-14311 shape; if not detected, a further limit example.
- `solr-inj-f`: HashBasedRouter:67, P4, HTTP fault.
- `solr-inj-h`: DeleteCollectionCmd:246, depth 2.
- `solr-inj-u`: a silent twin of `solr-inj-01`.

**Side findings (real-bug candidates, not run):**
- DZUP:238: a lost RELOAD request leaves a core read-only.
- RAUP:133/247: no refresh on a miss.
- A split with replication factor 2: a cleanup race can leave no active slice.

## 4. Results (fill in as the cases finish)

| case | pattern | point | root (expected) | designed | I1 verdict | control-tree verdict | native k/10 | report.py | IE1 wall (s) | seeding | exploration | compose+solver |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| `hdfs-inj-01` | P4 | hdfs-adhoc-45 | LOCAL_IO | detect | | | | | | | | |
| `hdfs-inj-02` | P9 | hdfs-adhoc-12 | IPC RESPONSE | detect | | | | | | | | |
| `hdfs-inj-03` | P1 | hdfs-adhoc-11 | IPC | detect | | | | | | | | |
| `hdfs-inj-04` | P7 | hdfs-adhoc-20 | STATE | detect | | | | | | | | |
| `hdfs-inj-05` | P2 | hdfs-adhoc-10 | IPC / LOCAL_IO | detect | | | | | | | | |
| `hbase-inj-01` | P3 | hbase-adhoc-04 | HBASE_RPC RESPONSE | detect | | | | | | | | |
| `hbase-inj-02` | P4 | hbase-adhoc-22 | STATE | detect | | | | | | | | |
| `hbase-inj-03` | P1+P2 | hbase-adhoc-08 | HBASE_RPC REQUEST | detect | | | | | | | | |
| `hbase-inj-04` | P1 | hbase-adhoc-34 | STATE | detect | | | | | | | | |
| `hbase-inj-05` | silent | hbase-adhoc-34 | -- | **miss** | | | | | | | | |
| `zk-inj-01` | P1 | FinalRequestProcessor:694 | STATE | detect | | | | | | | | |
| `zk-inj-02` | P3 | ZooKeeperServer:2201 | ZK WRITE | detect | | | | | | | | |
| `zk-inj-03` | P2/P4 | FinalRequestProcessor:694 | ZK WRITE | detect | | | | | | | | |
| `zk-inj-04` | P5 | zk-adhoc-01 | STATE | detect | | | | | | | | |
| `zk-inj-05` | liveness | FinalRequestProcessor:694 | -- | **miss** | | | | | | | | |
| `solr-inj-01` | P2 | solr-adhoc-19 | ZK create | detect | | | | | | | | |
| `solr-inj-02` | P1 | solr-adhoc-13 | STATE VIEW | detect | | | | | | | | |
| `solr-inj-03` | P6 | solr-adhoc-19 | CONFIG | detect | | | | | | | | |
| `solr-inj-04` | P8 | solr-adhoc-19 | CLOCK | detect | | | | | | | | |
| `solr-inj-05` | P4/P5 | solr-adhoc-31 | STATE VIEW | detect | | | | | | | | |

## 5. Rules (binding; RULES.md has them in full)

- **Generality:**
  - General fixes only; no per-case engine code.
  - A tree workaround only makes an order controllable or a value trackable. It never switches the fatal outcome, and
    is marked `// GraphChecker:`.
  - An injected mutation is production code that a developer could have written. It never touches GraphChecker hooks.
- **Shell:**
  - Prefix every bash command with `env -u BASH_ENV`.
  - Kill only by pid (`tools/rounds/stop-run.sh` for runs).
  - Never `rm -rf $VAR/...` unquoted.
  - Never rebuild a tree or snapshot a run reads.
  - No lift above 70 % memory; lift11 is the control host.
  - At most 5 coding agents, each on its own worktree, snapshot and `GC_OUT`.
- **Git:**
  - Never `git add -A`.
  - Commits are authored `Zhenyu Li <zhl136@ucsd.edu>` and end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
  - Push only with the owner's OK (GraphChecker branches and fork branches alike); never push to apache.
- **Docs:** they track the code. Keep this file's §4 and §6 current, and each case README.

## 6. Decisions and changes log

- 2026-10-30: design, branches and paths (this file). Candidates researched per system:
  `/bigtemp/vnr3ne/analysis/injected-2026-10-30/proposals-<sys>.md`.
