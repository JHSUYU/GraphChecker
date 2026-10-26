# HDFS-14311 (hdfs-buggy-14311)

## The bug

[HDFS-14311](https://issues.apache.org/jira/browse/HDFS-14311), fixed by 4cb22cd867a (2019, "Multi-threading conflict at
layoutVersion when loading block pool storage"). A DataNode loads its volumes into ONE `BlockPoolSliceStorage` (one
`StorageInfo`: `layoutVersion`, `cTime`, ...). Before the fix, `DataStorage#loadBlockPoolSliceStorage` submitted a volume's
upgrade callables to the parallel-load executor inside the loop over the volumes, so volume k's upgrade task
(`BlockPoolSliceStorage#doUpgrade(String, ...)`: `this.layoutVersion = current`, `this.cTime = nsInfo.getCTime()`) ran while
the loader thread read volume k+1's VERSION into the same fields (`readProperties`) and checked them in `doTransition`. When
the task's `layoutVersion = current` lands between the next volume's VERSION read and its layout check, that volume -- at an
older layout, so it should upgrade -- reads the current layout, skips the layout upgrade and reaches the cTime check; with
a cTime not below the NameNode's it falls through to `throw new IOException("Datanode state: LV = ... CTime = ... is newer
than the namespace state ...")` -- the throw of the ad hoc point hdfs-adhoc-24 (`docs/checks/HDFS.md` row 24,
BlockPoolSliceStorage.java:425). The issue's report is this throw after a 2.7 -> 2.9 DataNode upgrade (layout -56 -> -57).
The fix collects the callables and submits them only after every volume is loaded.

## The tree: the bug put back, the workload

Tree `$GC_TREES/hadoop-hdfs-bug-14311`, the fork's `graphchecker/hdfs-bug-14311` = `graphchecker/hdfs-checks` (899c200cc8e)
plus:

- **be42a6803b1, HDFS-14311 put back.** `DataStorage#loadBlockPoolSliceStorage` submits each volume's callables in the
  loop again (`tasks.add(new UpgradeTask(dataDir, executor.submit(c)))`), as before the fix; the fix's
  `upgradeCallableMap` and its deferred submission loop are gone. Nothing else changes.
- **0d7ab791afa, 92501dc122f, c3f0661bedc, the workload and the target.** `TestDFSUpgrade#testParallelVolumeUpgrade`
  (the class of hdfs-adhoc-24's own workload, `testUpgrade`), the "Normal DataNode upgrade" step with three volumes: the
  NameNode starts with -upgrade (a new cTime), the DataNode's volumes come from the master storage. Volumes 1 and 2 are
  at the previous DataNode layout (-56): each upgrades for its layout, decided on `layoutVersion > current` alone, so
  neither evaluates the cTime check; volume 1's upgrade task then writes the current layout. Volume 2 also has a future
  cTime. Volume 3 keeps the master layout and old cTime and upgrades for its cTime: it is the recording's one evaluation of
  the target guard in the occurrence. The recording passes with all three volumes upgraded (natively 5/5). Block scanner
  off, a six-hour heartbeat interval (no daemon heartbeat in the window after the DataNode's first).
  `doTransition`'s throw names `hdfs-buggy-14311` beside `hdfs-adhoc-24`. (0d7ab791afa had two volumes at the old cTime,
  where the throw's `cTime > namespace` can never hold; 92501dc122f had volume 1 at the current layout, so its own cTime
  check was the occurrence's first evaluation of the guard and took the anchor; c3f0661bedc is the three-volume design.)
- **1bc07a3e76a, a GraphChecker workaround: the upgrade tasks wait natively.** Without it the three-volume workload raced
  natively about 1 run in 10 (B14311d's native control hit the throw 1/10). A test-only static,
  `BlockPoolSliceStorage#upgradeTaskDelayMs` (0 unless a test sets it; the test sets 10 s and resets it), makes each upgrade
  task sleep before its upgrade, so natively every volume's VERSION is read before any task writes the shared layout. It
  adds no happens-before and never decides the throw. Natively 20/20 passes.

## The engine support it needed (system/hdfs-buggy-detect branches only; independently reviewed)

The DataNode's whole volume load is ONE occurrence (the handshake's `BPOfferService.verifyAndSetNamespaceInfo`, a
STATE_WRITER_ENTRY region), and volume 1's upgrade task is a TASK occurrence that carries the handshake's IPC anchor. On
the round with the bug and the old engine (B14311a, below) the write the bug needs -- volume 1's task's
`layoutVersion = current` -- was never offered to volume 2's layout read:

- **ba6580331, Arms#eligible: an earlier concurrent writer may overtake a write the reader cannot pass.** The task's
  write is EARLIER (in the recording) than volume 2's own `readProperties` write, which is in the reader's own occurrence;
  the old rule let an earlier alternative stand only when every write between it and the observed version could move past
  the read. Now the alternative may also overtake such a write when the two occurrences are concurrent.
- **131bf16d9, FlipQuery: one write choice per reader occurrence, location and observed version.** A flip query's write
  choice bound every read of the location in the occurrence; choosing the task's write for volume 2 would also have moved
  volume 1's earlier reads to it. Reads that observed different writes are now proposed apart.
- **7f562ef37, ConfirmMain: an overtaken write the reader cannot pass is held before the writer.** CONFIRM's and EXPLORE's
  holds now order volume 2's `readProperties` write before the task's write (it was ordered nowhere).
- **252ed18da, ConfirmMain: an overtaking read is held after the write its writer overtakes.** The re-review found that
  volume 2 was still held at `readProperties`' entry, the frame that holds that write: a cycle until the order's timeout.
  Volume 2 is now held at its first activation after the write (`setNamespaceID`), so the task writes `layoutVersion` and
  `cTime` there and volume 2's `setcTime` still follows. "The reader cannot pass it" and "the writer overtakes it" are
  decided with `Arms`' one concurrency rule, fed from the session's rows.
- **6a7c74e61, ConfirmMain: an overtaking read's hold starts after the overtaken write's activation exits.** A hold nested
  in the overtaken write's frame (or before the occurrence's close it waits on) cycles as well; it is now refused. This
  case is unchanged: `setLayoutVersion`'s frame holds only the write, and the holds on the seed are identical, so the round
  on 252ed18da stands.
- **838b0c888, Arms/ConfirmMain: a later concurrent writer may move ahead of a write the reader cannot pass.** The mirror
  of ba6580331. In the three-volume recordings every task writes after all three `readProperties`, so volume 1's task
  write is a LATER alternative for volume 2's reads, behind volume 3's `readProperties` (the reader occurrence's own write).
  Such a write now stays after the read while the writer moves ahead of it; the reader's hold is bounded by every write
  ordered before the writer that it cannot pass (here volume 2's own `setLayoutVersion`).

Rationale, tests and the review: `/bulk/analysis/buggy-detect-2026-10-26/14311-notes.md`.

## What this case declares

| Declaration | Where | What it says |
| --- | --- | --- |
| the failure | the tree's marker | `@CausynthExceptionTarget("hdfs-adhoc-24,hdfs-buggy-14311")` on `doTransition`'s "is newer than the namespace state" `throw new` |
| the occurrence | `target_occurrence=first` in `case.sh` | the first occurrence of the target the recording observes: the DataNode's volume load (`auto1/dn0 ... verifyAndSetNamespaceInfo@0`); its first evaluation of the guard (`doTransition#u117`, `cTime < namespace cTime`) is volume 3's in the recording and volume 2's in the re-paired world |
| scope | `case.sh` | hdfs-adhoc-24's: DataStorage, BlockPoolSliceStorage, Storage, StorageInfo |
| world depth, tasks, replay bound | `case.sh` | 0 (one counterfactual), 128, `CAUSYNTH_REPLAY_TIMEOUT_S=7200` as the family's 24 |
| loop bounds, workflow | `loop-bounds.jsonl`, `workflow.properties` | the ad hoc family's (none declared; default 8), no comments |
| report.py | `EXPECTED_MECHANISM` | `STATE_PAIRING_FLIPPED`, no clock |

## Result

**Not detected; not accepted.** GraphChecker's only witness was the race happening by timing in one replay.

| Round | Engine | Tree | Outcome |
| --- | --- | --- | --- |
| B14311a | eb2015bea (case only) | 92501dc122f (two volumes) | UNSAT_CLOSED: volume 1's task write was never an eligible writer of volume 2's layout read (it led to ba6580331 and 131bf16d9) |
| B14311b, B14311c | 131bf16d9, 7f562ef37 | c3f0661bedc | stopped before any obligation: superseded by the reviews (the hold cycled) |
| B14311d | 252ed18da | c3f0661bedc | SAT_CANDIDATE, `MARKER_FLIPPED` on a `Storage$StorageDirectory#tryLock` marker (#u31#3): under the flipped lock the third volume was not loaded, and volume 1's task wrote `layoutVersion = cur` between volume 2's reads **by timing**. CONFIRM saw the throw in that session; REPRODUCE planted the marker 10 times with 0 fatal (control 1/10); report.py FAIL (`MARKER_FLIPPED != STATE_PAIRING_FLIPPED`). The intended flip (volume 2's `#u112#2`) was NOT_ADMITTED: `ADMISSION_GAP`, no variable of its own, because the task write was a later alternative (now 838b0c888). |
| B14311e | 838b0c888 | 1bc07a3e76a (native delay) | stopped at the seed: volume 2's OWN task still wrote `layoutVersion` before volume 1's task (blocker 1) |

What the engine now supports (independently reviewed): an earlier (ba6580331) or later (838b0c888) concurrent writer
re-paired past a write the reader cannot pass, one write choice per observed version (131bf16d9), and CONFIRM/EXPLORE holds
that order the passed write before the writer and hold the reader after it without a cycle (7f562ef37, 252ed18da,
6a7c74e61, 838b0c888).

The two blockers that remain, both confirmed by the review:

1. **The carried-anchor over-approximation.** Each upgrade task's context carries the handshake's IPC anchor, not an anchor
   to its submit, so `Arms#concurrent` counts volume 2's own task -- submitted by the reader occurrence after volume 2's
   doTransition -- as concurrent with volume 2's reads. In both three-volume seeds volume 2's task wrote `layoutVersion`
   before volume 1's task (B14311d: 20186 < 20197; B14311e: 20743 < 20766). That write is then ordered before the chosen
   writer, which cannot happen, so every alternative cycles until the order's 300 s timeout.
2. **An order that times out after the fatal refutes.** In the fatal world, volume 2's IOException is caught per volume, so
   volume 3 still loads, and the loader waits for volume 3's task inside the occurrence. The pairing's block-mode order
   "reader occurrence close before volume 3's task" then times out after the fatal. `Confirmation` turns that into a
   `CONFIRM_MISMATCH` that refutes the claim. Confirmation is the false-positive filter and is not changed without the
   owner.

The native workload races about 1/10 without the workaround, and passes 20/20 with it.
