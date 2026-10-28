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
- **be29cd3c074, the same workaround: the tasks wait in load order.** With one wait for every task, every VERSION was read
  first, but the tasks still raced one another: in B14311e's recording volume 2's own task wrote the layout before volume
  1's (blocker 1 below). `BlockPoolSliceStorage#upgradeTaskStaggerMs` (test-only, 0 unless a test sets it; the test sets
  5 s and resets it) makes the n-th task to start (counted in `UPGRADE_TASKS_STARTED`, which the test resets) wait n times
  5 s longer, so volume 1's task writes first (10 s), then volume 2's (15 s), then volume 3's (20 s). The code is in the
  task's `call()`, under the existing `upgradeTaskDelayMs > 0` guard, so the loader (the reader occurrence) gains no read or
  branch. It adds no happens-before and never decides the throw. Natively 20/20 passes, each run in that order and with no
  "is newer" throw (`/bulk/gc-out/hdfs-buggy/14311/native-b14311-4/summary.txt`).

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

On liftlab, round B1 (2026-10-28, `/bigtemp/vnr3ne/gc-out/buggy-detect/accept-B1-buggy-14311`, snapshot
`/u/vnr3ne/gc-run/bd-hdfs-1`, tree set `/bigtemp/vnr3ne/wt/bd-trees-1`): B1: not detected again (UNSAT_CLOSED, substantive: 9 paths, 8 free; 2333 s). The rounds below ran on
CloudLab (their `/bulk` paths are that cluster's, no longer used); they stay as the record.

**Not detected; recorded as a capability limit** (the owner, 2026-10-26: a check truly beyond GraphChecker is not
forced). GraphChecker's only witness was the race happening by timing in one replay (B14311d). The last round, B14311f,
hit blocker 1 below and was stopped there.

| Round | Engine | Tree | Outcome |
| --- | --- | --- | --- |
| B14311a | eb2015bea (case only) | 92501dc122f (two volumes) | UNSAT_CLOSED: volume 1's task write was never an eligible writer of volume 2's layout read (it led to ba6580331 and 131bf16d9) |
| B14311b, B14311c | 131bf16d9, 7f562ef37 | c3f0661bedc | stopped before any obligation: superseded by the reviews (the hold cycled) |
| B14311d | 252ed18da | c3f0661bedc | SAT_CANDIDATE, `MARKER_FLIPPED` on a `Storage$StorageDirectory#tryLock` marker (#u31#3): under the flipped lock the third volume was not loaded, and volume 1's task wrote `layoutVersion = cur` between volume 2's reads **by timing**. CONFIRM saw the throw in that session; REPRODUCE planted the marker 10 times with 0 fatal (control 1/10); report.py FAIL (`MARKER_FLIPPED != STATE_PAIRING_FLIPPED`). The intended flip (volume 2's `#u112#2`) was NOT_ADMITTED: `ADMISSION_GAP`, no variable of its own, because the task write was a later alternative (now 838b0c888). |
| B14311e | 838b0c888 | 1bc07a3e76a (native delay) | stopped at the seed: volume 2's OWN task still wrote `layoutVersion` before volume 1's task (blocker 1) |
| B14311f | 4e1c228aa (838b0c888 merged) | be29cd3c074 (delay in load order) | seed as intended: the three `readProperties` (19554, 19788, 20013), then the task writes 20650 (submit `#u36@0`, volume 1's), 21049 (`#u36@1`, volume 2's own), 21429 (`#u36@2`). Volume 2's `#u112#2` flip is now UNSAT: the flip query keeps volume 2's earlier decisions on the same value as recorded (`layoutVersion == current` false, `layoutVersion > current` true). The first decision on that value, `#u96#2`, is SAT with one planted pairing, but z3 chose version 21049, the write of volume 2's OWN task (blocker 1). The replay was NOT_ADMITTED ("wrong decision at `#u96#2` ... took true"), and the re-solve asked the same world. Stopped with stop-run.sh at 14:19, per the lead. No verdict. |

What the engine now supports (independently reviewed): an earlier (ba6580331) or later (838b0c888) concurrent writer
re-paired past a write the reader cannot pass, one write choice per observed version (131bf16d9), and CONFIRM/EXPLORE holds
that order the passed write before the writer and hold the reader after it without a cycle (7f562ef37, 252ed18da,
6a7c74e61, 838b0c888).

The two blockers that remain, both confirmed by the review:

1. **The carried-anchor over-approximation.** Each upgrade task's context carries the handshake's IPC anchor, not an anchor
   to its submit, so `Arms#concurrent` counts volume 2's own task -- submitted by the reader occurrence after volume 2's
   doTransition -- as concurrent with volume 2's reads. It bites in two ways:
   - **as an intervening write.** In both earlier three-volume seeds, volume 2's task wrote `layoutVersion` before volume
     1's task (B14311d: 20186 < 20197; B14311e: 20743 < 20766). That write is then ordered before the chosen writer, which
     cannot happen, so every alternative cycles until the order's 300 s timeout. be29cd3c074 removes this form.
   - **as the chosen writer itself (B14311f).** With the tasks in load order, all three task writes of the current layout
     are later alternatives of volume 2's reads, all "concurrent", and the flip query lets the solver pick any of them.
     In obligation 06735091127740cf (`doTransition#u96#2`; three of its four write choices give `-57`), the model chose
     version 21049, written by volume 2's own task (`4dbd6035`, submit `#u36@1`). In that world the reader waits for a
     writer it has not created yet. The STATE edge reads `"writer":"9a0bac52e3b04a85","version":21049`,
     with ORDER `4dbd6035 doUpgrade exit -> 11fb7b34 .../doUpgrade@0/getLayoutVersion@0`. The replay took the recorded
     arm at `#u96#2` and was refused before it reached that hold (the decision's own reads are not held; see below). The re-solve (`obligations-0010`) asked the identical world, because nothing
     excludes a writer whose world failed, so volume 1's task write (20650) was never tried.
2. **An order that times out after the fatal refutes.** In the fatal world, volume 2's IOException is caught per volume, so
   volume 3 still loads, and the loader waits for volume 3's task inside the occurrence. The pairing's block-mode order
   "reader occurrence close before volume 3's task" then times out after the fatal. `Confirmation` turns that into a
   `CONFIRM_MISMATCH` that refutes the claim. Confirmation is the false-positive filter and is not changed without the
   owner.

Also seen in B14311f (not a named blocker, and inferred rather than run): the planted pairing names one read, the
representative of the value symbol `st_32_e8d8b03f6387941b`: `doUpgrade`'s `getLayoutVersion` (seq 19826), the last of
volume 2's reads of version 19788. The decisions it feeds (`#u96`, `#u112`) read the same value earlier, in
`doTransition` (19805-19818), and they are neither paired nor held. So the reader's hold point falls after those
decisions. By the hold rule, the same would hold with volume 1's task as the writer.

The native workload races about 1/10 without the workaround, and passes 20/20 with it (1bc07a3e76a, and be29cd3c074 in
load order).
