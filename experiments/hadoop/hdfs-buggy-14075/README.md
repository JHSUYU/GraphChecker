# HDFS-14075 (hdfs-buggy-14075)

## The bug

[HDFS-14075](https://issues.apache.org/jira/browse/HDFS-14075), fixed by 042c8ef593c (2018, "Terminate the namenode when
failed to start log segment"). `FSEditLog.rollEditLog` ends the current segment, then starts the next
(`startLogSegment`). When `journalSet.startLogSegment` throws -- too few journals started -- the pre-fix catch re-threw the
IOException to the roll caller: `curSegmentTxId` and `state = State.IN_SEGMENT` were skipped, so the NameNode kept serving
in BETWEEN_LOG_SEGMENTS with `editLogStream` null. The next roll's `endCurrentLogSegment` then trips its precondition,
`if (!isSegmentOpen()) throw new IllegalStateException("Bad state: ...")` -- the throw of the ad hoc point hdfs-adhoc-45
(`docs/checks/HDFS.md` row 45, FSEditLog.java:1466-1467 in this tree). The fix logs, closes the journals and
`terminate(1, msg)`.

## The tree: the bug put back, the workload

Tree `$GC_TREES/hadoop-hdfs-bug-14075`, the fork's `graphchecker/hdfs-bug-14075` = `graphchecker/hdfs-checks` (899c200cc8e)
plus three commits:

- **b958422e2bb, HDFS-14075 put back.** In the private `FSEditLog#startLogSegment` the catch around
  `journalSet.startLogSegment` re-throws `new IOException("Unable to start log segment ...: too few journals successfully
  started.", ex)` again, as before the fix, instead of LOG.error + cleanup + `terminate(1, msg)` (FSEditLog.java:1438-1446).
  The two `terminate` calls of `logSync` are another feature and stay.
- **a80f582fe6b, the workload and the target.** `TestCausynthRollSegmentFailure#testNextRollAfterFailedStartLogSegment`
  (`hadoop-hdfs/src/test/.../server/namenode`): a NameNode with ONE edit journal, redundant (not in
  `dfs.namenode.edits.dir.required`, no shared edits) with `dfs.namenode.edits.dir.minimum` 1, synchronous edit logging;
  the window (`registerCluster` + `startRecording`) holds two rolls, each its own request (`roll-1`, `roll-2`); the first
  roll is wrapped so its IOException does not end the workload. `endCurrentLogSegment`'s throw names `hdfs-buggy-14075`
  beside `hdfs-adhoc-45`. Why a redundant journal: a REQUIRED journal's failure is shut down by
  `JournalSet.mapJournalsAndReportErrors` itself (`terminate`, JournalSet.java:395) before FSEditLog's catch; a redundant
  one is disabled, `areResourcesAvailable` (1 redundant, 1 disabled, minimum 1) is false and JournalSet throws "failed for
  too many journals" (JournalSet.java:418) into the catch the bug changed.
- **7e8681a724d, the second roll rolls at once.** In round B14075b the fault replay went on to roll 2, whose own edit
  logged before `rollEditLog` dereferenced the null `editLogStream` (NullPointerException in
  `FSEditLog.doEditTransaction`) and ended the run before the check. The standby's roll RPC calls `rollEditLog` directly;
  roll 2 now does the same, roll 1 keeps its edit and sync.

Checked natively (a scratch run outside the tree, the journal's `startLogSegment` made to throw at roll 1 with a Mockito
spy, as the fix's own test does): on this tree roll 1 throws "Unable to start log segment 4: too few journals successfully
started." and roll 2 throws `IllegalStateException: Bad state: BETWEEN_LOG_SEGMENTS` at `endCurrentLogSegment`; on the
fixed code (`graphchecker/hdfs-checks`) roll 1 terminates the NameNode. The workload itself passes natively.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hdfs-adhoc-45,hdfs-buggy-14075")` on `endCurrentLogSegment`'s `throw new IllegalStateException` |
| the occurrence | `target_occurrence` in `case.sh` | the recording's roll-2 occurrence of `endCurrentLogSegment`'s region, by its resolved address (`ctx:Root:CLIENT/roll-2#1/idx:...rollEditLog@0/...endCurrentLogSegment@0`). `first` resolved to roll 1's (round B14075a), whose segment is always open: only the second roll can see the state the first roll's failed start leaves |
| scope | `case.sh` | FSEditLog (the point's) plus the classes the roll failure flows through: JournalSet, NameNodeResourcePolicy, FileJournalManager, EditLogFileOutputStream, and the IPC client |
| roots | the engine's catalog | the demanded LOCAL_IO doors the root demand chose (`io_doors.jsonl`): the edits_inprogress opens in `EditLogFileOutputStream.<init>` (reach ESCAPE) among them; no hook, no `root-domains.jsonl` |
| world depth, tasks | `case.sh` | 0 (one counterfactual), 128 |
| loop bounds, workflow | `loop-bounds.jsonl`, `workflow.properties` | the ad hoc family's (none declared; default 8), no comments |

## Result: SAT, confirmed, reproduced 10/10 natively, report.py PASS (round B14075c)

On liftlab, round B1 (2026-10-28, `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-buggy-14075`, snapshot
`/u/vnr3ne/gc-run/bd-hdfs-1`, tree set `/bigtemp/vnr3ne/wt/bd-trees-1`): B1: SAT, CONFIRM, native 10/10, control 0/10, report.py PASS, 463 s (B1-buggy-14075). The rounds below ran on
CloudLab (their `/bulk` paths are that cluster's, no longer used); they stay as the record.

Round B14075c (2026-10-26, `/bulk/gc-out/hdfs-buggy/14075/accept-B14075c-buggy-14075`; snapshot `/bulk/gc-run/hb14075-2` =
8936331be, tree set `/bulk/trees/b14075-2` = fork 7e8681a724d): `SAT_CANDIDATE`, `FINAL_READY`, 743 s; EXPLORE 2 rounds, 12
obligation verdicts, WITNESSED by the replay of obligation e1bcef8f8fb99839. round-verify: `end=(WITNESSED) z3=sat
moved=1 polarityDecides=True leaves=3 confirmed`, no UNBOUND, HOLD or BLOCKING gap, no defect, no refuted claim. BOUNDED by
the depth-0 bound (4 task rounds cut) and `ordered_map_unmodeled` at `NameNode.initReconfigurableBackoffKey` (start-up
configuration, off the chain).

- **Claim:** `MARKER_FLIPPED` at valuation 1, one moved root: the LOCAL_IO fault marker of the edits_inprogress open in
  roll 1's `startLogSegment` occurrence (`REGION.da7b10a5...in.2304262e...` = true; the open is
  `new RandomAccessFile(name, "rw")`, EditLogFileOutputStream.java:89).
- **CONFIRM:** the witness session itself is the run (it ran the moved root at the model's value and observed the fatal at
  the anchor; `targets.jsonl.gz` `observedFatal` true). **REPRODUCE:** natively 10/10 planted and fatal at the anchor,
  the control 0/10.
- **The chain** (claimed path 1, `candidate.smt2` `path_fatal__1`, the witness session e1bcef8f8fb99839-abaf72f1): the
  fault fails roll 1's journal open (`FileNotFoundException`, EditLogFileOutputStream.java:89) -> FileJournalManager and
  `JournalAndStream.startLogSegment` throw -> `JournalSet.mapJournalsAndReportErrors` disables the redundant journal and
  throws "starting log segment 4 failed for too many journals" (JournalSet.java:415-418) -> `FSEditLog.startLogSegment`
  re-throws it (the bug, :1442) and skips `state = State.IN_SEGMENT` (:1446), so `state` stays the BETWEEN_LOG_SEGMENTS
  roll 1's own `endCurrentLogSegment` wrote -> roll 2's `rollEditLog` (:1372) -> `endCurrentLogSegment`'s
  `isSegmentOpen()` compares `BETWEEN_LOG_SEGMENTS` with `IN_SEGMENT` -> false -> the throw (:1466-1467). Paths 0 and 2
  (the seed and roll 2's own fault) have the marker false and compare `IN_SEGMENT` with itself: no fatal.
- **Necessity:** one root moved; at the recorded valuation (the marker false) every path's fatal arm is false, so the file is
  unsat there (the polarity).
- **report.py:** PASS (row `hdfs-buggy-14075`: MARKER_FLIPPED, no clock).

Rounds before: B14075a anchored on roll 1 (`first`), UNSAT (the wrong question); B14075b anchored on roll 2, UNSAT
(NOT_FLIPPABLE at `isSegmentOpen()#u3#1`): its roll-1 fault replay ended at roll 2's own edit (the NullPointerException
above) before reaching the anchor -- the workload, fixed by 7e8681a724d.
