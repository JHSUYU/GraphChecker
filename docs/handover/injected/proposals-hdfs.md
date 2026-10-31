# Injected ad hoc coordination bugs: HDFS proposals (research agent, 2026-10-30)

Read-only research. Nothing was edited, built or run. Every file:line below was read in the unmodified checks tree
`/bigtemp/vnr3ne/wt/hl-trees-1/hadoop-hdfs-study-r7` (branch `graphchecker/hdfs-checks` 899c200cc8e). The old-bug trees
`/bigtemp/vnr3ne/wt/bd-trees-1/hadoop-hdfs-bug-*` stand on 899c200cc8e plus two/three commits each; a put-back tree for
an injected case should branch the same way (one mutation commit, one workload+target commit). Paths are short:
`H/` = `hadoop-hdfs-project/hadoop-hdfs/src/main/java/org/apache/hadoop/hdfs/`,
`C/` = `hadoop-hdfs-project/hadoop-hdfs-client/src/main/java/org/apache/hadoop/hdfs/`,
`T/` = `hadoop-hdfs-project/hadoop-hdfs/src/test/java/org/apache/hadoop/hdfs/`.

Per the lead's instruction for this system: **DETECTABLE candidates only** (the two undetectable slots are covered by
other systems).

Sources read: `docs/design/README.md` (the question, the stage list), `docs/handover/CHECKING.md` §1 (what counts as a
detection), `docs/handover/BUGGY-DETECT.md` (the 13 detected old bugs), `docs/checks/HDFS.md` (every study point with
site, guard, workload, scope), `experiments/hadoop/hdfs-adhoc/{case.sh,checks.tsv}`, `experiments/hadoop/trees.tsv`,
the old-bug case READMEs (`hdfs-buggy-11741/12931/5766/10609/17383/14075/14311`) and their put-back diffs, the H1
run outputs `/bigtemp/vnr3ne/gc-out/hdfs-final/accept-H1-*` (root_demand.jsonl, io_doors.jsonl, static_scope_map.jsonl,
claims) and the exclusive buggy-detect runs `/bigtemp/vnr3ne/gc-out/buggy-detect-exclusive/accept-E1-*`, and
`results/hdfs/README.md`.

## 0. What constrains HDFS injections (read first)

1. **The five root kinds that work on HDFS today, each with a precedent at or near an ad hoc point:**
   - **IPC door FAULT** (Hadoop `ipc.Client`/`Server`, request or response half; a transport fault ends the request in
     hand). The DataNode heartbeat / KeyUpdateCommand door is the strongest: `MARKER_FLIPPED`, native 10/10 for
     12931/5766/10609/17383/17899/17967 and hdfs-adhoc-12. Fast (368-572 s alone).
   - **LOCAL_IO** demanded door (a JDK file op on the traced flow). Precedent: hdfs-14075 at hdfs-adhoc-45 (a fault on
     the edits_inprogress open), `MARKER_FLIPPED`, native 10/10, 463-490 s; hdfs-adhoc-10 (a QJM `PersistentLongFile`
     write), the designed-tolerance SAT.
   - **CLOCK** skew. Precedent: hdfs-11741 at hdfs-adhoc-11 (`CLOCK_SKEW`, nn0 key-manager clock + a DataNode's
     `removeExpiredKeys` clock). The slowest and hardest case (1123 s alone, native plant needed a serial-no hook).
   - **CONFIG** (field-backed keys; `ConfigRoots` recognizes a field whose one writer stores `conf.get*` of a key).
     Precedent: hdfs-17960 at hdfs-adhoc-52 (`HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` true -> false), `MARKER_FLIPPED`.
   - **STATE re-pairing** (`STATE_PAIRING_FLIPPED`, no root moved). Precedent: hdfs-bugs-slowdisk-zero at
     `RoundRobinVolumeChoosingPolicy.java:84`, native 10/10, 402 s. **Caveat** (CHECKING §1, trap from 14311): a STATE
     re-pairing holds only if CONFIRM can hold the pairing after the reads that decide the guard; HDFS-14311 was *not*
     detected because the engine offered the reader's own later task as the concurrent writer and CONFIRM's hold sat
     after the deciding reads. So a STATE candidate must pair a read with a writer that is **recorded before the read's
     occurrence closes**, and whose value differs.
2. **A clean injection site is a point that is UNSAT on the unmodified r7 tree** (`results/hdfs/README.md`), where the
   correct code refuses the bad world; removing that protection flips UNSAT -> SAT. The UNSAT points with a real guard
   to remove include **45** (NO_ROOT), **20** (NO_ROOT), **28/29/30** (BP map written only at shutdown), **33**
   (hot-swap vs BP registration), **11** (no rotation in the study window). The already-SAT points (**10**, **12**,
   slowdisk-zero, and the named-bug points) detect an existing fragility with no bug; an injection there must bring a
   **workload that removes that fragility from the recording** and a mutation that re-introduces it in a world GC
   builds (as hdfs-buggy-12931/17383 do with a key-rotation workload).
3. **The healthy (fault-free) recording must reach the guard and not throw.** Every candidate below is checked for this:
   the workload rotates/records so the guard is evaluated false on the recorded path, and only the flipped world makes
   it true. A candidate whose healthy run already throws is worthless (CHECKING trap: a degenerate point).
4. **The control is mandatory** (BUGGY-DETECT standard): the unmodified r7 tree with the same workload and declaration
   must be UNSAT (or CONFIRM-refuted), and the native control 0/10. Each candidate states its expected control.
5. **The marker.** The point already carries `@CausynthExceptionTarget("hdfs-adhoc-NN"[,...])`; the injected id is
   added to that list (as 12931/17383 added theirs). A checkState/assert/checkArgument point that was rewritten to
   `if(!cond) throw new @...` keeps that form.
6. **Workload mode** (HDFS.md §0.1): `-Dcausynth.cluster.automatic=true`; a MiniDFSCluster test runs as written and the
   window opens after `waitActive`. A guard that runs only at cluster start-up needs `recording_window=startup` (21, 46).
   QJM tests (05-10) need the MiniJournalCluster adapter. The RBF module is out (no Router adapter).

## 1. Detectable candidates

### hdfs-inj-a: a failed log-segment start is swallowed, not fatal (P4, LOCAL_IO, hdfs-adhoc-45)

1. **Id and point.** `hdfs-inj-a`, point **hdfs-adhoc-45**, throw `H/server/namenode/FSEditLog.java:1471`
   (`endCurrentLogSegment`, `if (!isSegmentOpen()) throw new @CausynthExceptionTarget("hdfs-adhoc-45")
   IllegalStateException("Bad state: %s")`).
2. **Pattern.** **P4** (a partial failure leaves state inconsistent, with no rollback/cleanup). Real-world analogue:
   HDFS-14075 ("Terminate the namenode when failed to start log segment"), the exact point. This is a *distinct
   mutation* of the same pattern at the same point as hdfs-buggy-14075 (that one re-throws; this one swallows).
3. **Mutation** (`H/server/namenode/FSEditLog.java:1438-1446`, the private `startLogSegment`'s catch):
   ```diff
        try {
          editLogStream = journalSet.startLogSegment(segmentTxId, layoutVersion);
        } catch (IOException ex) {
          final String msg = "Unable to start log segment " + segmentTxId
              + ": too few journals successfully started.";
   -      LOG.error(msg, ex);
   -      synchronized (journalSetLock) {
   -        IOUtils.cleanupWithLogger(LOG, journalSet);
   -      }
   -      terminate(1, msg);
   +      // best-effort: a redundant journal failed, keep serving and let the
   +      // next roll re-open the segment
   +      LOG.error(msg, ex);
   +      return;
        }
        curSegmentTxId = segmentTxId;
        state = State.IN_SEGMENT;
   ```
   **Healthy run passes and reaches the guard:** with no fault, roll-1's `startLogSegment` succeeds, `state` becomes
   `IN_SEGMENT`, and roll-2's `endCurrentLogSegment` sees `isSegmentOpen()` true -> no throw. The guard is evaluated
   (false) on both rolls, so the point is reached.
4. **Workload.** Copy `hdfs-buggy-14075`'s `T/server/namenode/TestCausynthRollSegmentFailure#testNextRollAfterFailedStartLogSegment`
   (one NameNode, zero DataNodes, one **redundant** edit journal with `dfs.namenode.edits.dir.minimum=1`, synchronous
   edit logging; two rolls inside the window, roll-1 wrapped so its IOException does not end the workload, roll-2 rolls
   at once). It already passes healthy and leaves a segment open after each roll.
5. **Trigger.** **LOCAL_IO** fault at the `new RandomAccessFile(name, "rw")` of roll-1's edits_inprogress open
   (`EditLogFileOutputStream.<init>`, `H/server/namenode/EditLogFileOutputStream.java:89`; `io_doors.jsonl` of the
   14075 run shows this door, reach `ESCAPE`). The fault fails roll-1's journal open -> `JournalSet.mapJournalsAndReportErrors`
   disables the redundant journal and throws "...failed for too many journals" (`JournalSet.java:415-418`) ->
   `startLogSegment` swallows it (the bug) and returns with `state` still `BETWEEN_LOG_SEGMENTS` -> roll-2's
   `endCurrentLogSegment` compares `BETWEEN_LOG_SEGMENTS` with `IN_SEGMENT` -> throw. Inside the window (both rolls are
   the workload's own requests). Expected `MARKER_FLIPPED`, world depth 0.
6. **Why GraphChecker can detect it.** Precedent: hdfs-buggy-14075, *identical point, workload, root and mechanism*,
   SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 463-490 s. The point's unmodified verdict is
   `UNSAT_CLOSED` (vacuous NO_ROOT: one thread under its monitor). The control (unmodified tree, same workload) is
   UNSAT, because `terminate` kills the NameNode at roll-1 and no second roll runs.
7. **Risks.** Minimal. The only risk is that `return` (vs 14075's re-throw) leaves `editLogStream` null and roll-2's
   path dereferences it before `endCurrentLogSegment`; 14075's third commit ("the second roll rolls at once") already
   solved that ordering, so copy it. **Confidence HIGH.**

### hdfs-inj-b: a DataNode takes the standby's key as its current key (P9, IPC door, hdfs-adhoc-12)

1. **Id and point.** `hdfs-inj-b`, point **hdfs-adhoc-12**, throw `H/security/token/block/BlockTokenSecretManager.java:542`
   (`retrievePassword`, `if (key == null) throw new @CausynthExceptionTarget("hdfs-adhoc-12") InvalidToken("...the
   required block key (keyID=...) doesn't exist.")`).
2. **Pattern.** **P9** (state from the wrong source accepted). Real-world analogue: HDFS-17383 ("Datanode current block
   token should come from active NameNode in HA mode"). This injects the **caller side** of 17383 (BPOfferService),
   whereas hdfs-buggy-17383 injects the callee side (BTSM.addKeys drops its guard) -- a different, equally plausible
   mutation of the same pattern.
3. **Mutation** (`H/server/datanode/BPOfferService.java:833-840`, `processCommandFromStandby`'s DNA_ACCESSKEYUPDATE):
   ```diff
        case DatanodeProtocol.DNA_ACCESSKEYUPDATE:
          LOG.info("DatanodeCommand action from standby NN {}: DNA_ACCESSKEYUPDATE",
              nnSocketAddress);
          if (dn.isBlockTokenEnabled) {
            dn.blockPoolTokenSecretManager.addKeys(
                getBlockPoolId(),
   -            ((KeyUpdateCommand) cmd).getExportedKeys(), false);
   +            ((KeyUpdateCommand) cmd).getExportedKeys(), true);
          }
          break;
   ```
   (The `true`/`false` final argument is `updateCurrentKey`; the active path at :796-799 passes `true`. A developer
   copying that line into the standby path is the mistake.) **Healthy run passes and reaches the guard:** both DataNodes
   take the standby's update over their own heartbeat; the target holds the key the source signs with; the transfer's
   `retrievePassword` is evaluated (key found) and no throw.
4. **Workload.** Copy `hdfs-buggy-17383`'s `T/server/datanode/TestCausynthStandbyCurrentKey#testTransferAfterStandbyKeyUpdate`
   (HA `simpleHATopology`, two DataNodes, block tokens on, **unencrypted** transfer so the SASL/DEK check at :584 does
   not fire first; the standby rotates twice in-window, each DataNode refreshes over its own heartbeat to the standby,
   then the source replicates to the target). It already passes healthy.
5. **Trigger.** **IPC door RESPONSE fault** on the *target* DataNode's heartbeat to the standby
   (`BPServiceActor#sendHeartBeat`, `DatanodeProtocol.sendHeartbeat`, `ipc.Client#getRpcResponse`): the standby answered
   and cleared the target's key-update mark, and the KeyUpdateCommand in the answer is lost. Inside the window. The
   source, with the bug, now has the standby's newest key as *current* and signs the transfer token with it; the target
   holds only its pinned pair -> `allKeys.get(keyId) == null` -> throw. Expected `MARKER_FLIPPED` (RPC_FAILURE), depth 0.
6. **Why GraphChecker can detect it.** Precedent: hdfs-buggy-17383, *same point, same workload shape, same root*, SAT,
   CONFIRM, native 10/10, control 0/10, 530-572 s; the bd root_demand/static_scope confirm the heartbeat door and the
   `isExpired` clock are the only roots. The point's unmodified verdict with its own non-HA study workload is SAT
   (hdfs-adhoc-12, lost key update), but with *this HA workload* on the unmodified tree the source signs with nn0's key
   whatever the standby sends, so the same loss is harmless -> control UNSAT.
7. **Risks.** The HA cluster needs the standby's edit-tailing and daemon heartbeats pinned to 6 h (the workload already
   does this, to keep the window's heartbeats the workload's own). With encryption on, the :584 DEK check fires first;
   the workload keeps transfer unencrypted (checked). Mechanism and native plant are the proven block-key ones.
   **Confidence HIGH.**

### hdfs-inj-c: a cached DataEncryptionKey outlives its block key (P1/P8, CLOCK, hdfs-adhoc-11)

1. **Id and point.** `hdfs-inj-c`, point **hdfs-adhoc-11**, throw `H/security/token/block/BlockTokenSecretManager.java:584`
   (`retrieveDataEncryptionKey`, `if (key == null) throw new @CausynthExceptionTarget("hdfs-17897,...,hdfs-adhoc-11")
   InvalidEncryptionKeyException("Can't re-compute encryption key for nonce, since the required block key (keyID=...)
   doesn't exist.")`).
2. **Pattern.** **P1** (stale cached coordination state, not refreshed on a miss) / **P8** (time/expiry assumption).
   Real-world analogue: HDFS-11741 ("Long running balancer may fail due to expired DataEncryptionKey"), the exact
   point. The injection re-introduces 11741's bug by hand (a KeyManager that mints only when no key is cached).
3. **Mutation** (`H/server/balancer/KeyManager.java`, `newDataEncryptionKey`; read the 11741 put-back diff
   `git -C /bigtemp/vnr3ne/wt/bd-trees-1/hadoop-hdfs-bug-11741 show HEAD~1` for the exact hunk):
   ```diff
        public DataEncryptionKey newDataEncryptionKey() {
          if (encryptDataTransfer) {
            synchronized (this) {
   -          if (encryptionKey == null ||
   -              encryptionKey.expiryDate < timer.now()) {
   +          if (encryptionKey == null) {   // mint once, reuse forever (pre-11741)
                encryptionKey = blockTokenSecretManager.generateDataEncryptionKey();
              }
              return encryptionKey;
            }
          } ...
   ```
   (plus the `Timer` field the removed check read, as the 11741 put-back does.) **Healthy run passes:** interval 60 min,
   token lifetime 600 min, so inside the window nothing expires; the target still holds the retired key, and the
   cached-key path is served (guard false).
4. **Workload.** Copy `hdfs-buggy-11741`'s `T/server/balancer/TestCausynthExpiredBalancerKey#testBlockMoveWithCachedKeyAfterRotations`
   (two DataNodes, two blocks on the proxy, keys pinned S+1/S+2; in-window: nn0 rotates once, DataNodes refresh, the
   Balancer's first move caches a DEK of S+2 and moves block 1, nn0 rotates twice more and the DataNodes refresh so
   S+2 is retired then dropped, the Balancer's key-updater turn follows nn0 but the cached DEK does not, the second
   move presents S+2 to the target).
5. **Trigger.** **CLOCK** skew on nn0's `removeExpiredKeys` clock at its third rotation (`Timer.now()` in
   `BlockTokenSecretManager.removeExpiredKeys`, `static_scope_map.jsonl` ROOT_SITE
   `removeExpiredKeys()>#u2`) and on the target DataNode's `removeExpiredKeys` clock, so both drop the retired S+2 that
   the Balancer still presents. Expected `CLOCK_SKEW`, `movedRoots` holding those two clocks, nested world depth
   (the 11741 claim moved two Long clock cells).
6. **Why GraphChecker can detect it.** Precedent: hdfs-buggy-11741, *same point, same workload, same CLOCK_SKEW
   mechanism*, SAT, CONFIRM, native 10/10 (on CloudLab with the serial-no hook), control 0/10. The point's unmodified
   study verdict (hdfs-adhoc-11) is `UNSAT_CLOSED` (NO_ROOT: no rotation in the study window). Control (unmodified
   tree, this workload): the fixed KeyManager re-mints the DEK once its own expiry passes, so the clock skew is harmless
   -> UNSAT.
7. **Risks.** CLOCK is the slowest and most fragile HDFS root: 11741 took 1123 s alone, its native reproduction needed
   a `SERIAL_NO` hook that is a follow-up TODO (the liftlab H1 row reproduced 0/10 without it; CloudLab 10/10 with it).
   The nested clock placement (`Composer#placeClocks`) and the two-clock witness are the hard part. **Confidence
   MEDIUM** (detectable, but the slowest/least reliable; the native-plant caveat applies).

### hdfs-inj-d: a stale ACTIVE claim is accepted (P7, STATE re-pairing, hdfs-adhoc-20)

1. **Id and point.** `hdfs-inj-d`, point **hdfs-adhoc-20**, throw `H/server/datanode/BPOfferService.java:617`
   (`updateActorStatesFromHeartbeat`, after the assert rewrite: `if (bpServiceToActive == actor) { if (!(txid >=
   lastActiveClaimTxId)) throw new @CausynthExceptionTarget("hdfs-adhoc-20") AssertionError(); lastActiveClaimTxId =
   txid; }`).
2. **Pattern.** **P7** (ownership/session transfer not handled) with a **P5** (watcher/reader stale-view) flavour.
   Real-world analogue: the HA split-brain guard family (the assert itself documents "Split-brain scenario"). No single
   old HDFS bug sits here; the mutation removes the recency guard the DataNode uses to reject a stale active claim.
3. **Mutation** (`H/server/datanode/BPOfferService.java:587-601`):
   ```diff
          final boolean nnClaimsActive =
              nnHaState.getState() == HAServiceState.ACTIVE;
          final boolean bposThinksActive = bpServiceToActive == actor;
   -      final boolean isMoreRecentClaim = txid > lastActiveClaimTxId;

          if (nnClaimsActive && !bposThinksActive) {
   -        if (!isMoreRecentClaim) {
   -          LOG.warn("NN " + actor + " tried to claim ACTIVE state at txid=" + ...);
   -          return;
   -        } else {
   -          ...
   -          bpServiceToActive = actor;
   -        }
   +        // accept any ACTIVE claim (drops the split-brain recency check)
   +        bpServiceToActive = actor;
          } else if (!nnClaimsActive && bposThinksActive) {
            bpServiceToActive = null;
          }
   ```
   **Healthy run passes:** in the recording the two NameNodes' heartbeats arrive in txid order, so the accepted claim's
   txid is `>= lastActiveClaimTxId` and the guard at :617 is false.
4. **Workload.** The study workload `TestClientProtocolForPipelineRecovery#testPipelineRecoveryOnOOB` (hdfs-adhoc-20's
   row) is non-HA. This candidate needs an HA cluster with two NameNodes failing over inside the window, i.e. a new
   `T/server/datanode/TestCausynthHaClaimReorder` modelled on `hdfs-buggy-17383`'s `TestCausynthStandbyCurrentKey`
   (HA `simpleHATopology`, register nodes, open the window, then: nn0 claims ACTIVE at a high txid over dn0's heartbeat,
   then nn1 (former active) sends a late ACTIVE heartbeat at a *lower* txid over a second heartbeat; the recording
   orders them high-then-low so the low one is rejected and :617 is not hit).
5. **Trigger.** **STATE re-pairing** of the second heartbeat's read of the shared field `lastActiveClaimTxId`
   (`BPOfferService.java:587/616`, written at :619 under the write lock) with the *earlier* (lower-txid) claim's write,
   i.e. a reorder so the low-txid claim is processed when `bpServiceToActive == actor` and `lastActiveClaimTxId` is
   already the high value -> `txid >= lastActiveClaimTxId` false -> throw. Reader and writer are both in-window heartbeat
   occurrences on dn0 under the BPOS write lock; the field has an INITIAL (-1), a high WRITE and a low WRITE.
   Expected `STATE_PAIRING_FLIPPED`, no root moved, depth 0.
6. **Why GraphChecker can detect it.** STATE re-pairing precedent: hdfs-bugs-slowdisk-zero (`STATE_PAIRING_FLIPPED`,
   native 10/10, 402 s). The point's unmodified verdict (hdfs-adhoc-20) is `UNSAT_CLOSED` (NO_ROOT: the txid is
   monotonic, "a re-pairing to an older edit-log write is formally eligible but CONFIRM refutes it"). The control
   (unmodified tree, this HA workload) is UNSAT, because the guard at :592 rejects the stale claim before :617 is
   reached.
7. **Risks.** This is the 14311 shape of risk: a STATE re-pairing is detected only if CONFIRM can hold the pairing
   after the reads that decide the guard, and if the engine offers the *earlier* claim (not the reader's own later
   write) as the concurrent writer. The two heartbeats must be distinct recorded occurrences on the same node with the
   field written between them. Needs a new HA workload. **Confidence MEDIUM** (new point + STATE risk; the clean
   monotonic-field structure is in its favour).

### hdfs-inj-e: block recovery races block-pool shutdown (P4, STATE re-pairing, hdfs-adhoc-28/29/30)

1. **Id and point.** `hdfs-inj-e`, point **hdfs-adhoc-30** (choose one of 28/29/30; 30 is the richest:
   `activeNN == null`), throw `H/server/datanode/BlockRecoveryWorker.java:609`
   (`getActiveNamenodeForBP`, `if (activeNN == null) throw new @CausynthExceptionTarget("hdfs-adhoc-30") IOException("Block
   pool ... has not recognized an active NN")`). (28 is `getDatanodeID` `bpos==null` :566; 29 is `getActiveNamenodeForBP`
   `bpos==null` :604.)
2. **Pattern.** **P4** (a partial failure / lifecycle teardown leaves state inconsistent). Analogue: the block-recovery
   vs BP-shutdown races in HDFS-2 #14/#28-class bugs. The mutation removes the recovery worker's tolerance of a
   concurrently-cleared active NN.
3. **Mutation** (`H/server/datanode/BlockRecoveryWorker.java:604-611`): rather than *adding* a bug, the clean injection
   is to **drop a null-guard the recovery worker uses to skip a block whose BP is being torn down** -- e.g. make
   `getActiveNamenodeForBP` read `bpServiceToActive` through a cached local taken before the loop (P1) so a shutdown
   between the cache and the use is not seen:
   ```diff
   -    DatanodeProtocolClientSideTranslatorPB activeNN = bpos.getActiveNN();
   -    if (activeNN == null) {
   -      throw new @CausynthExceptionTarget("hdfs-adhoc-30") IOException(...);
   -    }
   -    return activeNN;
   +    return bpos.getActiveNN();   // may be null if the BP relinquished ACTIVE
   ```
   — no; that moves the throw. **Keep the throw**; instead make the *caller* not re-check after the recovery RPC. The
   minimal faithful mutation keeps :609 and injects at `recoverBlocks`/`recoverBlock` a reordering: the recovery daemon
   reads the active NN once and caches it, so a heartbeat that clears `bpServiceToActive` (NN relinquishes ACTIVE) mid-
   recovery is not re-observed and a later `getActiveNamenodeForBP` on a second block throws. **Healthy run passes:** in
   the recording the active NN stays set through the recovery, so :609 is false.
4. **Workload.** `TestBlockRecovery2#testRecoveryTimeout` (hdfs-adhoc-28/29/30's study workload) drives a recovery; it
   needs the cluster's **shutdown or a failover recorded inside the window** so there is a writer of `bpServiceToActive`
   (= null) to re-pair against. Model a new `T/server/datanode/TestCausynthRecoveryVsRelinquish` on it: start recovery,
   then over a heartbeat the NN relinquishes ACTIVE (`bpServiceToActive = null`, BPOfferService.java:611), recorded
   *after* the recovery read.
5. **Trigger.** **STATE re-pairing** of the recovery worker's `getActiveNN()` read (`BPOfferService.java:533-543`,
   `bpServiceToActive`) with the relinquish write at :611, so the recovery reads the null. Expected
   `STATE_PAIRING_FLIPPED`, no root moved, depth 0.
6. **Why GraphChecker can detect it.** STATE precedent (slowdisk-zero). The point's unmodified verdict (hdfs-adhoc-28/29/30)
   is `UNSAT_CLOSED` substantive: "the only writers of the BP map and of `bpServiceToActive` are `BlockPoolManager.remove`
   and `shutdownActor` at shutdown; a STATE re-pairing of a recovery read to those writes is a real race" (HDFS.md D.1
   item 6) -- the checks doc explicitly calls this a `B-` (detectable if the shutdown is in the window). The control
   (unmodified tree, this workload) is UNSAT because the correct code re-reads the active NN.
7. **Risks.** `bpServiceToActive` is written at the handshake (before the window) and at shutdown; the workload must put
   a relinquish/shutdown writer *inside* the window and before the recovery read's occurrence closes, or the only writer
   is out of window (NO_ROOT, as the unmodified verdict). Same 14311 CONFIRM-hold risk as hdfs-inj-d. Needs a new
   workload. **Confidence MEDIUM-LOW** (realistic but the window placement of the relinquish is delicate).

### hdfs-inj-f: a hot-swapped volume trusts a block pool that unregistered (P5, STATE re-pairing, hdfs-adhoc-33)

1. **Id and point.** `hdfs-inj-f`, point **hdfs-adhoc-33**, throw `H/server/datanode/DataStorage.java:262`
   (`VolumeBuilder.build`, `if (bpStorage == null) throw new @CausynthExceptionTarget("hdfs-adhoc-33") AssertionError()`).
2. **Pattern.** **P5** (a race between a reconfiguration and the block-pool registration, stale view). Analogue: the
   hot-swap-vs-BP-registration race the assert guards.
3. **Mutation** (`H/server/datanode/DataStorage.java:252-268`, `VolumeBuilder.build`): drop the null check so the build
   proceeds on a missing BP storage -- no, that removes the throw. Instead inject that `prepareVolume` snapshots the BP
   set once (P1 stale cache) so a BP removed between `prepareVolume` and `build` is still in the builder's
   `bpStorageDirMap` but gone from `storage.bpStorageMap` at `build` -> `bpStorage == null` at :262. **Healthy run
   passes:** in the recording the BP stays registered between prepare and build, so the map lookup succeeds.
4. **Workload.** `TestDataNodeHotSwapVolumes#testAddOneNewVolume` (hdfs-adhoc-33's study workload) adds a volume; it
   needs a recorded BP change between prepare and build. This is **lower-confidence**: the hot-swap window and a BP
   removal co-occurring is awkward to record cleanly. Offered mainly for breadth.
5. **Trigger.** STATE re-pairing of `build`'s `bpStorageMap.get(bpid)` read with a BP-removal write, or the CONTAINER
   read paired with its pre-removal state. Expected `STATE_PAIRING_FLIPPED` or a CONTAINER re-pairing, depth 0.
6. **Why GraphChecker can detect it.** STATE precedent (slowdisk-zero). Unmodified verdict (hdfs-adhoc-33):
   `UNSAT_CLOSED` substantive ("the builder's block pool ids are the keys the same DataStorage registered under its
   lock").
7. **Risks.** The BP lifecycle sits largely at start-up/shutdown (out of window), as 28-31 note; getting a BP
   registration/removal and a hot-swap into one recorded window is the hard part, and a CONTAINER re-pairing of a
   node-map read is a known engine limit (EXPLORE does not flip container reads at depth > 0). **Confidence LOW.**

### hdfs-inj-g: a lost key-update heartbeat is treated as success (P2, IPC door, hdfs-adhoc-11)

1. **Id and point.** `hdfs-inj-g`, point **hdfs-adhoc-11**, throw `BlockTokenSecretManager.java:584` (as hdfs-inj-c).
2. **Pattern.** **P2** (a remote error handled as a generic failure / not retried with fresh state). Analogue:
   HDFS-12931/5766/10609 (the client-side generic handling of a lost key). This is the **IPC-door** sibling of the
   CLOCK candidate hdfs-inj-c, at the same point but a different root and pattern (allowed: "the same point with a
   clearly different pattern and root").
3. **Mutation** (`H/server/datanode/BPServiceActor.java`, the offer-service loop, or
   `CausynthCluster.refreshKeysFromNameNode`'s production analogue): make the DataNode mark its key-update as *done*
   before the KeyUpdateCommand is applied (swallow the transport error and clear the pending flag), e.g. in
   `BPOfferService.processCommandFromActor`'s DNA_ACCESSKEYUPDATE (`:793-800`) wrap the `addKeys` in a
   `try { ... } catch (Exception e) { LOG.warn(...); }` that swallows -- so a world where the key export is absent
   (lost response) leaves the DN without the new key but the actor proceeds. **Healthy run passes:** the response
   carries the export, `addKeys` runs, the key is held.
4. **Workload.** hdfs-adhoc-12's own `T/server/datanode/TestCausynthDataTransferRpcFailure` with **encryption on**
   (the :584 DEK check path), rotating nn0 twice and refreshing the consumer DataNode over its own heartbeat, then a
   read/transfer presenting the current DEK to that DataNode.
5. **Trigger.** **IPC door RESPONSE fault** on the consumer DataNode's key-update heartbeat (as hdfs-buggy-12931's
   moved root: `ipc.Client.getRpcResponse` of `DatanodeProtocol.sendHeartbeat`). Expected `MARKER_FLIPPED`, depth 0.
6. **Why GraphChecker can detect it.** Precedent: hdfs-buggy-12931/5766/10609 at this exact throw via a lost
   heartbeat, SAT, CONFIRM, native 10/10, 368-556 s. Unmodified verdict (hdfs-adhoc-11): `UNSAT_CLOSED` NO_ROOT (no
   rotation in the study window). Control (unmodified, this workload): the DataNode retries/holds the key correctly so
   the loss is survived -> UNSAT.
7. **Risks.** Overlaps hdfs-inj-c's point; keep only one of c/g in the final five unless a second block-key root is
   wanted. The throw at :584 fires in the lost-key world with or without the swallow (as the 12931 caveat notes), so
   the *control* must use a workload where the correct code recovers; otherwise the injection does not discriminate.
   **Confidence MEDIUM-HIGH** (fast, proven door; the discrimination caveat is the only subtlety).

### hdfs-inj-h: ordered snapshot deletion mishandled on a config flip (P6, CONFIG, hdfs-adhoc-52)

1. **Id and point.** `hdfs-inj-h`, point **hdfs-adhoc-52**, throw `H/server/namenode/snapshot/FSImageFormatPBSnapshot.java:468`
   (`Saver.serializeSnapshotSection`, the rewritten `if (i != sm.getNumSnapshots()) throw new
   @CausynthExceptionTarget("hdfs-17960,hdfs-adhoc-52") ...`).
2. **Pattern.** **P6** (an unhandled configuration-dependent path). Analogue: HDFS-17960 (`ordered=false`), the exact
   point. The injection is a *distinct* P6 mutation of the counter/tolerance coordination.
3. **Mutation** (`H/server/namenode/snapshot/DirectorySnapshottableFeature.java:261-263`): widen the tolerance so it
   also swallows a missing snapshot when ordered deletion is **on**, while `SnapshotManager.deleteSnapshot` still
   decrements `numSnapshots` unconditionally (:552):
   ```diff
   -      if (!snapshotManager.isSnapshotDeletionOrdered() &&
   -          !snapshotManager.isImageLoaded()) {
   +      if (!snapshotManager.isImageLoaded()) {   // tolerate a missing snapshot during replay regardless of ordering
            return null;
          }
   ```
   **Healthy run passes:** the recorded deletions each remove a real snapshot (the tolerance path is not taken on the
   recorded arm), so counter and list agree and :468 is false.
4. **Workload.** hdfs-17960's `T/server/namenode/snapshot/TestOrderedSnapshotDeletion#testOrderedDeletionWithRestart`
   (records duplicate snapshot-deletion edits, restarts the NameNode, checkpoints), scope as hdfs-17960's case.sh
   (loop bounds 16).
5. **Trigger.** **CONFIG** root `HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED` (field-backed; the hook mints it, else
   `CONFIG:dfs.namenode.snapshot.deletion.ordered`). With this mutation the mishandled path is reached when the restart
   replays a duplicate deletion and `isImageLoaded()` is false, and the CONFIG flip exercises the config-dependent
   path; counter and list diverge -> :468 throw. Expected `MARKER_FLIPPED` moving the config value, depth 0.
6. **Why GraphChecker can detect it.** Precedent: hdfs-17960 at this exact point, CONFIG `MARKER_FLIPPED`, SAT, native
   10/10, 501 s. The CONFIG root is proven here. Unmodified verdict (hdfs-adhoc-52): `RUN_DEFECT`/UNSAT on the study
   workload (its study test has no deletion or replay).
7. **Risks.** HDFS-17960's own bug (the unconditional decrement at :552) is already present on r7, so the point is
   already SAT via the ordered=false path; this mutation adds a *second* config-dependent mishandle and the injected
   case must be shown to discriminate from the pre-existing 17960 path (the control must pin the counter decrement to
   the fixed behaviour, or choose the num-committed-allowed append point 39 instead). This is the least-clean injection
   of the set. **Confidence MEDIUM-LOW.**

## 2. Points considered and not proposed

- **hdfs-adhoc-10** (Journal checkWriteRequest epoch): already SAT on the unmodified tree as a designed QJM tolerance
  (a door fault on `startLogSegment` leaves `lastWriterEpoch`=0); no injection needed, so not an injection site. It is
  the reliable QJM door precedent but not a clean fresh case.
- **hdfs-adhoc-05/06** (QuorumOutputStream double-buffer asserts): local to one thread under the stream lock, no
  coordination (UNSAT vacuous); an injection would be vacuous.
- **hdfs-adhoc-08/09** (Journal fencing / committed-txid backward): UNSAT substantive; the IPC-serial and single-thread
  executor keep requests ordered, so no single flip lowers the value -- hard to inject cleanly.
- **hdfs-adhoc-14** (BTSM 6-arg password mismatch): needs two different key bytes under one id; key bytes come from
  `KeyGenerator`, not a root.
- **hdfs-adhoc-49/50** (snapshot quota / duplicate name): per-directory constants; no root flips them.
- **hdfs-adhoc-22-27/34/35/37** (storage VERSION compares): read from disk (IO rule class C); not coordination.
- **hdfs-14311 shape** (concurrent-initialization race on shared state, the reader's own writer created after the
  read): GraphChecker's known capability limit (P10) -- excluded as the brief asks for detectable only.

## 3. Ranked recommendation (5 detectable, spread over 5 points and 5 root kinds)

1. **hdfs-inj-a** (hdfs-adhoc-45, **LOCAL_IO**, P4). Highest confidence: the exact point, workload, root and mechanism
   of hdfs-buggy-14075 (SAT/CONFIRM/10-10, 463-490 s), a clean UNSAT->SAT, a one-hunk mutation distinct from 14075's.
2. **hdfs-inj-b** (hdfs-adhoc-12, **IPC door**, P9). Proven heartbeat/key-update door and the 17383 HA workload; a
   plausible caller-side copy-paste mistake; control cleanly UNSAT. Fast (530-572 s).
3. **hdfs-inj-d** (hdfs-adhoc-20, **STATE re-pairing**, P7). Brings in a new point and the STATE root (slowdisk-zero
   precedent); a clean monotonic shared field with INITIAL/high/low writes. Needs a new HA workload; the 14311 CONFIRM-
   hold risk is the main doubt.
4. **hdfs-inj-h** (hdfs-adhoc-52, **CONFIG**, P6). Covers the config root (17960 precedent) at a proven fast point;
   ranked below a/b/d because it overlaps the pre-existing 17960 bug and must be shown to discriminate (swap-in:
   point 39 num-committed-allowed if a cleaner CONFIG site is wanted).
5. **hdfs-inj-c** (hdfs-adhoc-11, **CLOCK**, P8). Covers the clock root (11741 precedent) for maximum spread. The
   biggest doubt: CLOCK is the slowest/least reliable root (11741 was 1123 s and its native plant needed the serial-no
   hook that is a TODO), so if a reliable five is preferred over full root-kind spread, swap in **hdfs-inj-g**
   (hdfs-adhoc-11, IPC door, P2 -- a second fast block-key door case) or **hdfs-inj-e** (recovery STATE).

### Doubts (surface to the lead)

- **a, b are safe**; the rest carry one risk each.
- **CLOCK (c):** detectable but slow and the native reproduction is a known follow-up (serial-no hook). If the five
  must all be "proven fast and reliable," drop c for g.
- **STATE (d, e, f):** the 14311 lesson -- a re-pairing is detected only if the differing writer is recorded before the
  reader's occurrence closes and CONFIRM can hold the pairing after the deciding reads. d (a single monotonic field) is
  the safest STATE; e and f need a BP-lifecycle writer dragged into the window and are MEDIUM-LOW / LOW.
- **CONFIG (h):** the point already SATs via the pre-existing 17960 bug, so the injected mutation must be shown to add a
  *distinct* discriminating path; the num-committed-allowed append (point 39) is the alternative CONFIG site.
- **New workloads:** a, b, c, g, h reuse an existing (bd or study) workload directory to copy; d, e, f need a new
  `TestCausynth*` HA/recovery test (sketched), which is implementation work and a risk to the "fast" preference.
- **Discrimination vs the control** is the recurring subtlety for the block-key points (b, c, g): because the DN throw
  is upstream of the client code, the control must use a workload on which the *correct* code survives the same
  fault/skew, exactly as hdfs-buggy-12931/17383 do. All three candidates above specify such a control.

## 4. Additional candidates (after the lead's review, 2026-10-31)

The lead dropped **c** (its mutation is the HDFS-11741 put-back, a55f17c918), **h** (the base tree already has the 17960
path, so the control is SAT) and **g** (the DataNode throws at :584 on the correct code in the same lost-key world, the
12931 caveat). Kept: **a** (45, LOCAL_IO), **b** (12, IPC), **d** (20, STATE). The ranking in §3 is superseded by §4.4.

Three more detectable candidates follow. Each one meets the lead's four constraints:
1. it is not any `hdfs-bug-*` put-back, nor a named bug in the tree;
2. its control is UNSAT, with the reason stated;
3. its trigger is inside the window and has an HDFS precedent;
4. it sits on a point other than a/b/d, and it copies a proven-fast workload.

**Why the block-key family can still give a discriminating case.** The base tree reaches :542/:584 only when the
DataNode misses **two** rotations (the named 17899/17967 cases and hdfs-adhoc-12 rotate twice). With **one** rotation
the correct code is safe, because the NameNode publishes its *next* key ahead of time:
- `generateKeys` puts `nextKey` into `allKeys` at BlockTokenSecretManager.java:207, and `updateKeys` does the same at :302.
- `exportKeys` then ships every key in `allKeys`, so each DataNode already holds the key that becomes current at the
  next rotation (the design comment at :180-191).
- hdfs-buggy-11741's README states the consequence: "No fault world reaches the target: target-dn holds S+2 since the
  pin, before the window, so a lost heartbeat cannot take it away."

A one-rotation workload is therefore UNSAT on the correct code. Candidates i and j each break that look-ahead
differently.

### hdfs-inj-i: the NameNode stops publishing its next block key (P1, IPC door, hdfs-adhoc-11)

1. **Id and point.** `hdfs-inj-i`, point **hdfs-adhoc-11**, throw `H/security/token/block/BlockTokenSecretManager.java:584`
   (`retrieveDataEncryptionKey`, `if (key == null)` at :583).
2. **Pattern.** **P1**, stale cached coordination state. The DataNode's key cache is no longer primed ahead of a
   rotation, so one missed refresh leaves it stale.
   - Analogue: the HDFS-11741 / HDFS-17899 class (a DataNode without the NameNode's current key), here caused by losing
     the look-ahead rather than by a second rotation.
   - The plausible mistake: "allKeys holds the keys tokens can carry now; the next key is published when it becomes
     current".
3. **Mutation** (two deletions):
   ```diff
   @@ BlockTokenSecretManager.java:205-207 (generateKeys)
        allKeys.put(currentKey.getKeyId(), currentKey);
   -    allKeys.put(nextKey.getKeyId(), nextKey);
   @@ BlockTokenSecretManager.java:301-302 (updateKeys)
            + "DelegationKey: long expiryDate>");
   -    allKeys.put(nextKey.getKeyId(), nextKey);
        return true;
   ```
   - The key still enters `allKeys` when it becomes current (:291), and `exportKeys` (:211-218) is unchanged.
   - Nothing on the NameNode looks a token up under its next key: `createPassword` and `generateDataEncryptionKey` use
     `currentKey`.

   **The healthy run passes and reaches the guard.** After the in-window rotation the master's export is {S+1 retiring,
   S+2 current}. Each DataNode takes it over its own heartbeat. The source's current key becomes S+2, and the target
   holds S+2, so the target's `retrieveDataEncryptionKey(S+2)` finds the key and does not throw.
4. **Workload.** Copy hdfs-17899-bug3's encrypted workload,
   `T/server/datanode/TestCausynthDataTransferRpcFailure#testReplicationAfterModeledKeyRefreshRpcFailure` (PASS, 371 s
   alone), as a new method `testReplicationAfterOneRotation`. The changes:
   - Rotate **once**: `rotation < 2` (:143) becomes `< 1`, and the precondition `initialKeyId + 2` (:156) becomes `+ 1`.
   - Make the pin tree-agnostic, because the control runs the same test on the unmodified tree. Replace
     `assertEquals(pinned, keyIds(master))` (:258) and `hasKey(SERIAL_NO + 1) && hasKey(SERIAL_NO + 2)` (:268) with
     "the keys are a subset of `pinned`, contain S+1, and S+1 is current".
   - Set `dfs.heartbeat.interval` to 6 h (hdfs-buggy-12931/5766/17383's lesson: a daemon heartbeat must not take the
     key-update mark).
5. **Trigger.** An **IPC door** fault on the *target* DataNode's key-update heartbeat: the REQUEST half, or the
   RESPONSE half (`ipc.Client#getRpcResponse` of `DatanodeProtocol.sendHeartbeat` under the workload's `heartbeat`
   request), after nn0 cleared the target's mark (BlockManager.java:1675-1677).
   - With the mutation the target holds only {S+1}. The source presents a DEK under S+2, and :584 throws.
   - The trigger is inside the window: the refresh is the workload's own recorded request.
   - Expected `MARKER_FLIPPED` (the RPC_FAILURE row), world depth 0.
6. **Why GraphChecker can detect it.**
   - Precedent: the same door, workload frame and throw as hdfs-17899-bug3 (SAT, native 10/10) and
     hdfs-buggy-12931/5766/10609 (SAT, native 10/10, 368-556 s).
   - The point's unmodified study verdict is `UNSAT_CLOSED` (NO_ROOT).
   - **Control UNSAT, and why.** On the correct code the target holds S+2 from the pin, before the window.
     - A lost target refresh leaves S+2 in place.
     - A lost source refresh makes the source present S+1, which the target holds.
     - A forward skew of the target's `removeExpiredKeys` clock acts only inside a *delivered* `addKeys`, and the
       received keys are re-put right after it (:244, then :249-251).
     - A skew of nn0's `removeExpiredKeys` clock runs before `updateKeys` puts the new current key (:276, then :291).
     - So no fault, clock or combination of them removes the key the source presents.
7. **Risks.**
   - The workload change is small but needed; the existing asserts at :258/:268 would fail on the mutated tree.
   - This is not the base tree's named 17899 bug: that one needs two rotations and no code change. Here the mutation is
     what makes one rotation unsafe.
   - **Confidence HIGH.** It is the most-proven door in HDFS, and the control's safety rests on a design invariant
     already recorded in hdfs-buggy-11741's README.

### hdfs-inj-j: expired keys are pruned after the merge (P8, CLOCK, hdfs-adhoc-11)

1. **Id and point.** `hdfs-inj-j`, point **hdfs-adhoc-11**, throw BlockTokenSecretManager.java:584 (as i).
   - Same point as i, but a different root (CLOCK) and pattern (P8). Pick **one of i/j** if the five must sit on five
     distinct points.
   - The encrypted :584 path is required. On the unencrypted :542 path, `retrievePassword` checks the token's expiry
     first (`isExpired`, `Time.now()`, :534-537). A forward skew on the same node would fire the "expired" throw
     instead. `SaslDataTransferServer` reads no clock before :584 (grep: no `expiryDate`/`Time.now` there).
2. **Pattern.** **P8**, a time or expiry assumption across nodes: the DataNode judges keys the NameNode has just
   declared valid by its own clock.
   - Analogue: HDFS-11741, which turns on the same clock read.
   - The mutation is a reorder of two statements, not the 11741 put-back (that one is in KeyManager).
3. **Mutation** (`addKeys`, BlockTokenSecretManager.java:238-254):
   ```diff
        LOG.info("Setting block keys. BlockPool = {} .", blockPoolId);
   -    removeExpiredKeys();
        if (updateCurrentKey || currentKey == null) {
          this.currentKey = exportedKeys.getCurrentKey();
        }
        BlockKey[] receivedKeys = exportedKeys.getAllKeys();
        for (int i = 0; i < receivedKeys.length; i++) {
          if (receivedKeys[i] != null) {
            this.allKeys.put(receivedKeys[i].getKeyId(), receivedKeys[i]);
          }
        }
   +    removeExpiredKeys();   // prune after merging, so expired received keys go too
      }
   ```
   **The healthy run passes.** The workload sets a 60 min interval and 1 min lifetime, so S+2's expiry is now + 2 h 1 min,
   and nothing is pruned at the recorded clock.
4. **Workload.** The same one-rotation encrypted variant as i: copy `testReplicationAfterModeledKeyRefreshRpcFailure`,
   rotate once, and set the heartbeat interval to 6 h.
   - The pin asserts need no change, because the look-ahead is intact on this tree.
   - Zero in-window rotations would also do: one refresh, then the transfer.
5. **Trigger.** A **CLOCK** skew of the target DataNode's `removeExpiredKeys` read (`timer.now()`, :221), inside its
   in-window `addKeys` (the workload's `heartbeat` refresh).
   - That site is a `ROOT_SITE` (`removeExpiredKeys()>#u2`) in the static scope maps of both H1-adhoc-12 and
     H1-17899-bug3.
   - A skew past S+2's expiry prunes the S+2 the target has just received. The source presents a DEK under S+2, and
     :584 throws.
   - Expected `CLOCK_SKEW` with the target-dn clock in `movedRoots`, one clock, world depth 0.
6. **Why GraphChecker can detect it.**
   - Precedent: hdfs-buggy-11741 moved exactly this read ("target-dn's clock at its key update's `removeExpiredKeys`"):
     SAT, CONFIRM, native 10/10, control 0/10.
   - **Control UNSAT, and why.** The correct code prunes *before* the merge (:244), so any skew at :221 is undone by
     the re-put at :249-251.
     - Lost refreshes are harmless with one rotation (the look-ahead, as in i).
     - nn0-side skews cannot remove the key the source presents (see i).
7. **Risks.**
   - CLOCK is HDFS's slowest root: 11741 took 1123 s alone, against about 400 s for the block-key door cases.
   - Native CLOCK plants on `removeExpiredKeys` failed (0/10) when daemon heartbeats raced the plant (CloudLab
     hdfs-11741). The 6 h heartbeat interval is what gave hdfs-buggy-11741 10/10.
   - **Confidence MEDIUM.** It is the only remaining CLOCK option, and it has one clock, depth 0, and the exact
     precedent site.

### hdfs-inj-k: a JournalNode that rejected a batch keeps getting batches (P2, IPC door or LOCAL_IO, hdfs-adhoc-10)

1. **Id and point.** `hdfs-inj-k`, point **hdfs-adhoc-10**, throw `H/qjournal/server/Journal.java:521`
   (`checkWriteRequest`: `reqInfo.getEpoch() != lastWriterEpoch.get()`, :520).
   - The **declared occurrence is the faulted JournalNode's *second* `journal()` in segment 1**, not the first.
   - hdfs-adhoc-10 is SAT on the unmodified tree only at the first `journal()` (QJM's designed tolerance). The second
     one is never sent on the correct code.
2. **Pattern.** **P2**, a remote error handled as a transient failure: the writer does not resync with the node that
   rejected its write.
   - Analogue: the QJM design (HDFS-3077). A logger that missed a write is disabled until the next roll, as the
     comment at IPCLoggerChannel.java:364-365 says ("Will try to write to this JN again after the next log roll").
   - The plausible mistake: "a failed batch is just logged; the quorum covers it".
3. **Mutation** (`H/qjournal/client/IPCLoggerChannel.java:363-370`, `sendEdits`):
   ```diff
            } catch (IOException e) {
              QuorumJournalManager.LOG.warn("Remote journal {} failed to write txns {}-{}."
                      + " Will try to write to this JN again after the next log roll.",
                  IPCLoggerChannel.this, firstTxnId, (firstTxnId + numTxns - 1), e);
   -          synchronized (IPCLoggerChannel.this) {
   -            outOfSync = true;
   -          }
              throw e;
   ```
   **The healthy run passes.** No `journal()` fails, so `outOfSync` is never needed. Every JournalNode's
   `lastWriterEpoch` is 1 after `startLogSegment` (Journal.java:615), and the guard at :520 is false at both flushes.
4. **Workload.** hdfs-adhoc-10's study workload, `TestQuorumJournalManager#testSingleWriter` (566 s alone, SAT,
   native 10/10, with the MiniJournalCluster adapter already in r7), extended so that segment 1 is written in **two
   flushes**. `QJMTestUtil.writeTxns` flushes once per call (QJMTestUtil.java:105-112), so `testSingleWriter` sends one
   `journal()` per segment. A new method in the same class, using only QJMTestUtil calls:
   ```java
   @Test
   public void testSingleWriterTwoFlushes() throws Exception {
     EditLogOutputStream stm = writeSegment(cluster, qjm, 1, 3, false); // start + flush 1 (txids 1-3)
     writeTxns(stm, 4, 2);                                              // flush 2 (txids 4-5): the target
     stm.close();
     qjm.finalizeLogSegment(1, 5);
     checkRecovery(cluster, 1, 5);                                      // holds on a quorum
   }
   ```
   - In `case.sh`, give hdfs-adhoc-10's scope, world depth 0, and as `target_occurrence` the resolved address of jnK's
     `journal()` under flush 2. Read that address off a `STOP_AFTER=SEED` run, as hdfs-buggy-14075 resolved roll-2's.
5. **Trigger.** The precedent's root for jnK's segment-1 start, either of:
   - an **IPC door** REQUEST fault on `QJournalProtocol.startLogSegment` to jnK;
   - the **LOCAL_IO** SYNC fault at jnK's `lastWriterEpoch` persist (`PersistentLongFile.set`, then
     `AtomicFileOutputStream` close and `FileChannel.force`). This is H1-adhoc-10's moved root, and it is in that run's
     `io_doors.jsonl`.

   What follows:
   - jnK keeps `lastWriterEpoch` = 0, and the quorum of the other two goes on.
   - Flush 1's `journal()` to jnK throws at :521. This is the designed tolerance, not the declared occurrence.
   - With the mutation the logger is not marked out of sync. Flush 2's `journal()` is sent to jnK and passes
     `throwIfOutOfSync` (:358). `checkRequest` passes, and :520 compares 1 with 0, so the throw fires at the declared
     occurrence.
   - Inside the window: the adapter opens the window after `waitActive`, before `format` and `startLogSegment`.
   - Expected `MARKER_FLIPPED`, world depth 0.
6. **Why GraphChecker can detect it.**
   - Precedent: H1-adhoc-10 (the same workload family, root and throw): SAT, CONFIRM, native 10/10, 566 s.
   - **Control UNSAT, and why.** On the correct code, flush 1's failure at jnK sets `outOfSync` (:368). Flush 2's
     `sendEdits` then stops at `throwIfOutOfSync` (:358). It sends at most a `heartbeat()`, which runs `checkRequest`
     only and is not the `journal()` region. So jnK never receives flush 2's `journal()`, and the declared occurrence
     is unreachable.
     - Faulting flush 1's RESPONSE instead (jnK wrote the batch) leaves `lastWriterEpoch` = 1, so nothing throws even
       on the mutated tree.
     - A fault on jnK's segment-file creation after `lastWriterEpoch` was set fails at `checkSync(curSegment != null)`,
       a different throw.
   - Why not 08/09, the siblings the lead suggested:
     - Both are UNSAT substantive, and a single writer cannot reach them.
     - For 09, the IPC-serial `checkSync` comes before the committed-txid check in `checkRequest` (:499-502 before
       :505-507). Any reorder hits `JournalOutOfSyncException` first, and the single-thread executor plus the
       quorum-then-`setCommittedTxId` order (QuorumOutputStream) keep the committed txid monotone per logger.
     - 08 needs a second writer to raise the promise.
7. **Risks.**
   - Identity: the declared occurrence (jnK, flush 2) must not be "answered by shape" by flush 1's occurrence in the
     control's fault world. They differ in the client step's count, so this should hold, but check it on the control
     run.
   - Semantics: the throw at the declared occurrence is the same check as the designed tolerance at flush 1. The bug is
     that the writer keeps feeding a JournalNode that has fallen out of sync, which a reader may find a weaker "bug"
     than a, b or i.
   - The workload needs a new test method; it is small, and the case directory is otherwise hdfs-adhoc-10's.
   - **Confidence MEDIUM.**

### 4.1 Coordinator ideas checked and not proposed

- **15/16 (BlockInfo commit/complete).** These are NameNode-local checks under the FSNamesystem write lock;
  HDFS.md §0.5 says CONFIRM refutes a re-pairing there.
  - The only way to get a retried `complete`/`addBlock` is a lost IPC reply, and a non-HA client does not retry
    (`dfs.client.retry.policy.enabled` is false by default).
  - The addBlock retry protection (`analyzeFileState`'s "this is a retry" branch) is reached only with an HA failover
    proxy, and even then its throws are not points 15/16.
- **38/39/40 (append guards).** 39 needs a last block that is COMMITTED at append time, which requires
  `num-committed-allowed` > 0 *and* the IBR losing a race.
  - A mutation that accepts COMMITTED at close makes the healthy run racy, because the client's `complete()` often
    beats the DataNode's IBR.
  - A lost IBR is re-queued and resent (`IncrementalBlockReportManager`), and the RetriableException at 39 is itself
    the designed retry signal.
  - 40 needs a COMPLETE block with too few live replicas, which no in-window root produces.
- **19 (DNA_FINALIZE bpid).** The block-pool id strings are fixed at format, and the workload has one NameNode, so no
  root or mutation makes the command's id differ without a federation workload.
- **48 (rename undo).** It is an identity compare of references the renaming thread took itself, which states no term
  (VM.md §5.2; the results README reads it as vacuous by construction).

### 4.2 Revised recommendation (5 detectable, 5 distinct points)

1. **hdfs-inj-a** (45, LOCAL_IO, P4). Unchanged: the exact hdfs-buggy-14075 frame. HIGH.
2. **hdfs-inj-b** (12, IPC door, P9). Unchanged: the 17383 HA frame with a caller-side mutation. HIGH.
3. **hdfs-inj-i** (11, IPC door, P1). The most-proven door. The one-rotation workload makes the correct code safe by
   design (the look-ahead), so the control is cleanly UNSAT. HIGH.
4. **hdfs-inj-d** (20, STATE, P7). Unchanged: a new point and the STATE root. MEDIUM.
5. **hdfs-inj-k** (10, IPC door or LOCAL_IO, P2). The QJM family on its proven root and workload, declared at the
   second `journal()` so the control is UNSAT. MEDIUM.

This set covers three root kinds (LOCAL_IO, IPC door, STATE) and five patterns (P1, P2, P4, P7, P9). If a CLOCK case is
wanted, **hdfs-inj-j** replaces i (same point, P8, MEDIUM).
